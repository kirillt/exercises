package controllers

import java.time.{LocalDate, Period}
import javax.inject._

import domain.{Deposit, Operation, OperationException, Withdrawal}
import models.AccountRepository
import models.Account.accountFormat
import org.apache.commons.lang3.exception.ExceptionUtils
import org.h2.jdbc.JdbcSQLException
import org.slf4j.LoggerFactory
import play.api.libs.json.{JsNumber, Json}
import play.api.mvc._

import scala.concurrent.{ExecutionContext, Future}

@Singleton
class AccountController @Inject()(accounts: AccountRepository,
                                  cc: ControllerComponents)
                                 (implicit ec: ExecutionContext)
  extends AbstractController(cc) {

  def create(name: String): Action[AnyContent] = Action.async { fromFuture {
    accounts.create(name).map(account => Created(Json.toJson(account)))
      .recover {
        case e: JdbcSQLException =>
          log.error(s"User creation failed: $e")
          Forbidden(s"User $name can't be created")
      }
    }
  }

  def balance(name: String): Action[AnyContent] = Action.async { fromFuture {
    accounts.get(name).map(account => Ok(JsNumber(account.balance)))
      .recover {
        case e: NoSuchElementException =>
          log.error(s"Balance retrieval failed: $e")
          NotFound(s"Can't find user $name")
      }
    }
  }

  case class OperationParameters(name: String, amount: BigDecimal)

  private implicit val opParamsFormat = Json.format[OperationParameters]

  def deposit: Action[OperationParameters] =
    perform(Deposit)

  def withdrawal: Action[OperationParameters] =
    perform(Withdrawal)

  private def perform(op: Operation): Action[OperationParameters] = asyncOp {
    case OperationParameters(name: String, amount: BigDecimal) =>
      require(op.MaxTransactionAmount <= op.MaxDailyAmount)
      require(op.MaxTransactionsPerDay > 0)

      def isToday(date: LocalDate): Boolean =
        Period.between(date, LocalDate.now())
          .minusDays(1).isNegative

      if (amount > op.MaxTransactionAmount)
        Future.successful {
          Forbidden(s"Amount $amount is too big (the limit is ${op.MaxTransactionAmount})")
        }
      else accounts
        .get(name)
        .flatMap { account =>
          val wasPerformedToday = isToday(op.lastPerformed(account))

          def withChecks(f: => Future[Result]) =
            if (wasPerformedToday) {
              val frequency = op.frequency(account)
              if (frequency >= op.MaxTransactionsPerDay) {
                Future.successful {
                  Forbidden(s"Operation was performed $frequency times today (limit is ${op.MaxTransactionsPerDay})")
                }
              } else {
                val left = op.MaxDailyAmount - op.dailyAmount(account)
                if (amount > left)
                  Future.successful {
                    Forbidden(s"Amount $amount is too big (you have $left limit left)")
                  }
                else f
              }
            } else f

          withChecks {
            Future.fromTry(op.perform(account, amount, wasPerformedToday))
              .flatMap { modified =>
                accounts
                  .update(modified)
                  .map { result =>
                    Ok(Json.toJson(result))
                  }
              }
          }
        } recover {
            case _: NoSuchElementException => NotFound(s"Can't find user $name")
        }
  }

  private def asyncOp(f: OperationParameters => Future[Result]) =
    Action.async(parse.json[OperationParameters]) { request =>
      fromFuture(f(request.body))
    }

  private def fromFuture(f: => Future[Result]) =
    f.recover {
      case e: OperationException =>
        Forbidden(e.getMessage)
      case e: Throwable =>
        log.error(ExceptionUtils.getStackTrace(e))
        InternalServerError("Error occurred")
    }

  private val log = LoggerFactory.getLogger(getClass)

}