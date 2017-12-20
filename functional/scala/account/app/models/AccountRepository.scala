package models

import java.sql.Date
import java.time.LocalDate
import javax.inject.{Inject, Singleton}

import play.api.db.slick.DatabaseConfigProvider
import slick.jdbc.JdbcProfile

import scala.concurrent.{ExecutionContext, Future}

@Singleton
class AccountRepository @Inject()(dbConfigProvider: DatabaseConfigProvider)(implicit ec: ExecutionContext) {
  private val dbConfig = dbConfigProvider.get[JdbcProfile]

  import dbConfig._
  import profile.api._

  private implicit val localDateToDate = MappedColumnType.base[LocalDate, Date](Date.valueOf, _.toLocalDate)

  private class AccountTable(tag: Tag) extends Table[Account](tag, "account") {

    def name = column[String]("name", O.PrimaryKey)
    def balance = column[BigDecimal]("balance")

    def deposited = column[BigDecimal]("deposited")
    def deposits = column[Int]("deposits")
    def lastDeposit = column[LocalDate]("lastDeposit")

    def withdrawn = column[BigDecimal]("withdrawn")
    def withdrawals = column[Int]("withdrawals")
    def lastWithdrawal = column[LocalDate]("lastWithdrawal")

    def * = (name, balance,
        deposited, deposits, lastDeposit,
        withdrawn, withdrawals, lastWithdrawal) <>
      ((Account.apply _).tupled, Account.unapply)

  }

  private val accounts = TableQuery[AccountTable]

  def get(name: String): Future[Account] = db.run {
    accounts.filter(_.name === name)
      .take(1).result.head
  }

  def list(): Future[Seq[Account]] = db.run {
    accounts.result
  }

  def create(name: String): Future[Account] = db.run {
    val fresh = Account.fresh(name)

    (accounts += fresh)
      .andThen(DBIO.successful(fresh))
  }

  def update(account: Account): Future[Account] = db.run {
    accounts
      .filter(_.name === account.name)
      .update(account)
      .andThen(DBIO.successful(account))
  }

}
