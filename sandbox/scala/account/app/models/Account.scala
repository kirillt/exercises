package models

import java.time.LocalDate

import play.api.libs.json.{Format, Json}

case class Account(name: String, balance: BigDecimal,
                   deposited: BigDecimal, deposits: Int, lastDeposit: LocalDate,
                   withdrawn: BigDecimal, withdrawals: Int, lastWithdrawal: LocalDate) {

  def deposit(amount: BigDecimal, wasDepositedToday: Boolean): Account = {
    val limits: (BigDecimal, Int) =
      if (wasDepositedToday) (deposited, deposits)
      else (0, 0)

    Account(name, balance + amount,
      limits._1 + amount, limits._2 + 1, LocalDate.now(),
      withdrawn, withdrawals, lastWithdrawal)
  }

  def withdrawal(amount: BigDecimal, wasWithdrawnToday: Boolean): Account = {
    val limits: (BigDecimal, Int) =
      if (wasWithdrawnToday) (withdrawn, withdrawals)
      else (0, 0)

    Account(name, balance - amount,
      deposited, deposits, lastDeposit,
      limits._1 + amount, limits._2 + 1, LocalDate.now())
  }

}

object Account {

  def fresh(name: String): Account =
    Account(name, 0,
      0, 0, LocalDate.now(),
      0, 0, LocalDate.now())

  implicit val accountFormat: Format[Account] = Json.format[Account]

}