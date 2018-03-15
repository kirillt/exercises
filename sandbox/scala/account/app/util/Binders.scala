package util

import play.api.mvc.PathBindable

import scala.util.Try

object Binders {

  implicit def bigDecimalBinder: PathBindable[BigDecimal] = new PathBindable[BigDecimal] {

    override def bind(key: String, value: String): Either[String, BigDecimal] =
      Try(BigDecimal(value)).toEither.left.map(_.toString)

    override def unbind(key: String, value: BigDecimal): String =
      value.toString()

  }

}
