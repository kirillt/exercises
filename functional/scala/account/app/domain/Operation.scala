package domain

import java.time.LocalDate

import models.Account

import scala.util.{Failure, Try}

trait Operation {
  def MaxDailyAmount: BigDecimal
  def MaxTransactionAmount: BigDecimal
  def MaxTransactionsPerDay: BigDecimal

  def lastPerformed(account: Account): LocalDate
  def dailyAmount(account: Account): BigDecimal
  def frequency(account: Account): Int

  def perform(account: Account, amount: BigDecimal,
              wasPerformedToday: Boolean): Try[Account]
}

object Deposit extends Operation {
  val MaxDailyAmount: BigDecimal = 150000
  val MaxTransactionAmount: BigDecimal = 40000
  val MaxTransactionsPerDay: BigDecimal = 4

  override def lastPerformed(account: Account): LocalDate = account.lastDeposit
  override def dailyAmount(account: Account): BigDecimal = account.deposited
  override def frequency(account: Account): Int = account.deposits

  override def perform(account: Account, amount: BigDecimal,
                       wasPerformedToday: Boolean): Try[Account] =
    Try(account.deposit(amount, wasPerformedToday))
}

object Withdrawal extends Operation {
  val MaxDailyAmount: BigDecimal = 50000
  val MaxTransactionAmount: BigDecimal = 20000
  val MaxTransactionsPerDay: BigDecimal = 3

  override def lastPerformed(account: Account): LocalDate = account.lastWithdrawal
  override def dailyAmount(account: Account): BigDecimal = account.withdrawn
  override def frequency(account: Account): Int = account.withdrawals

  override def perform(account: Account, amount: BigDecimal,
                       wasPerformedToday: Boolean): Try[Account] =
    if (account.balance < amount) Failure {
      new OperationException("Not enough money")
    } else Try {
      account.withdrawal(amount, wasPerformedToday)
    }
}

class OperationException(msg: String) extends RuntimeException(msg)