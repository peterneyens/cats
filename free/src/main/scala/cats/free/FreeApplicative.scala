package cats
package free

import cats.arrow.FunctionK
import cats.data.Const

import scala.annotation.tailrec

/**
  * Applicative Functor for Free,
  * implementation inspired by https://github.com/safareli/free/pull/31/
  */
sealed abstract class FreeApplicative[F[_], A] extends Product with Serializable {
  self =>
  // ap => apply alias needed so we can refer to both
  // FreeApplicative.ap and FreeApplicative#ap
  import FreeApplicative.{FA, Pure, Ap, lift}

  final def ap[B](b: FA[F, A => B]): FA[F, B] = {
    b match {
      case Pure(f) =>
        this.map(f)
      case _ =>
        Ap(b, this)
    }
  }

  final def map[B](f: A => B): FA[F, B] = {
    this match {
      case Pure(a) => Pure(f(a))
      case _ => Ap(Pure(f), this)
    }
  }

  /** Interprets/Runs the sequence of operations using the semantics of `Applicative` G[_].
    * Tail recursive.
    */
  // scalastyle:off method.length
  final def foldMapOld[G[_]](f: F ~> G)(implicit G: Applicative[G]): G[A] = {
    import FreeApplicative._
    // the remaining arguments to G[A => B]'s
    var argsF: List[FA[F, Any]] = this.asInstanceOf[FA[F, Any]] :: Nil
    var argsFLength: Int = 1
    // the remaining stack of G[A => B]'s to be applied to the arguments
    var fns: List[Fn[G, Any, Any]] = Nil
    var fnsLength: Int = 0

    @tailrec
    def loop(): G[Any] = {
      var argF: FA[F, Any] = argsF.head
      argsF = argsF.tail
      argsFLength -= 1

      // rip off every `Ap` in `argF`, peeling off left-associated prefixes
      if (argF.isInstanceOf[Ap[F, _, _]]) {
        val lengthInitial = argsFLength
        // reassociate the functions into a single fn,
        // and move the arguments into argsF
        do {
          val ap = argF.asInstanceOf[Ap[F, Any, Any]]
          argsF ::= ap.fp
          argsFLength += 1
          argF = ap.fn.asInstanceOf[FA[F, Any]]
        } while (argF.isInstanceOf[Ap[F, _, _]])
        // consecutive `ap` calls have been queued as operations;
        // argF is no longer an `Ap` node, so the entire topmost left-associated
        // function application branch has been looped through and we've
        // moved (`argsFLength` - `lengthInitial`) arguments to the stack, through
        // (`argsFLength` - `lengthInitial`) `Ap` nodes, so the function on the right
        // which consumes them all must have (`argsFLength` - `lengthInitial`) arguments
        val argc = argsFLength - lengthInitial
        fns ::= Fn[G, Any, Any](foldArg(argF.asInstanceOf[FA[F, Any => Any]], f), argc)
        fnsLength += 1
        loop()
      } else {
        val argT: G[Any] = foldArg(argF, f)
        if (fns ne Nil) {
          // single right-associated function application
          var fn = fns.head
          fns = fns.tail
          fnsLength -= 1
          var res = G.ap(fn.gab)(argT)
          if (fn.argc > 1) {
            // this function has more than 1 argument,
            // bail out of nested right-associated function application
            fns ::= Fn(res.asInstanceOf[G[Any => Any]], fn.argc - 1)
            fnsLength += 1
            loop()
          } else {
            if (fnsLength > 0) {
              // we've got a nested right-associated `Ap` tree,
              // so apply as many functions as possible
              @tailrec
              def innerLoop(): Unit = {
                fn = fns.head
                fns = fns.tail
                fnsLength -= 1
                res = G.ap(fn.gab)(res)
                if (fn.argc > 1) {
                  fns ::= Fn(res.asInstanceOf[G[Any => Any]], fn.argc - 1)
                  fnsLength += 1
                }
                // we have to bail out if fn has more than one argument,
                // because it means we may have more left-associated trees
                // deeper to the right in the application tree
                if (fn.argc == 1 && fnsLength > 0) innerLoop()
              }

              innerLoop()
            }
            if (fnsLength == 0) res
            else loop()
          }
        } else argT
      }
    }

    loop().asInstanceOf[G[A]]
  }
  // scalastyle:on method.length

  final def foldMap[G[_]](fk: F ~> G)(implicit G: Applicative[G]): G[A] = {
    import FreeApplicative._

    @tailrec
    def reassociateApToFn(ap: Ap[F, Any, Any], args: List[FA[F, Any]], argsLength: Int): (List[FA[F, Any]], Fn[G, Any, Any]) = {
      val args2 = ap.fp :: args
      val argsLength2 = argsLength + 1
      ap.fn match {
        case apx @ Ap(_, _) => reassociateApToFn(apx.asInstanceOf[Ap[F, Any, Any]], args2, argsLength2)
        case _              => (args2, Fn[G, Any, Any](foldArg(ap.fn, fk), argsLength2))
      }
    }

    @tailrec
    def applyFunctions(res: G[Any], fns: List[Fn[G, Any, Any]]): Either[List[Fn[G, Any, Any]], G[Any]] =
      fns match {
        case Fn(f, numArgs) :: fns =>
          val res2 = G.ap(f)(res)
          // bail out -> more left-associated trees
          if (numArgs > 1)
            Left(Fn(res2.asInstanceOf[G[Any => Any]], numArgs - 1) :: fns)
          else applyFunctions(res2, fns)
        case Nil =>
          Right(res)
      }

    @tailrec
    def loop(apArgs: List[FA[F, Any]], fns: List[Fn[G, Any, Any]]): G[Any] =
      apArgs.head match {
        case ap @ Ap(_, _) =>
          val (extraArgs, fn) = reassociateApToFn(ap, Nil, 0)
          loop(extraArgs ::: apArgs.tail, fn :: fns)
        case other =>
          applyFunctions(foldArg(other, fk), fns) match {
            case Left(fns) => loop(apArgs.tail, fns)
            case Right(x) => x
          }
      }

    loop(this.asInstanceOf[FA[F, Any]] :: Nil, Nil).asInstanceOf[G[A]]
  }

  /**
    * Interpret/run the operations using the semantics of `Applicative[F]`.
    * Stack-safe.
    */
  final def fold(implicit F: Applicative[F]): F[A] =
    foldMap(FunctionK.id[F])

  /**
    * Interpret this algebra into another algebra.
    * Stack-safe.
    */
  final def compile[G[_]](f: F ~> G): FA[G, A] =
    foldMap[FA[G, ?]] {
      λ[FunctionK[F, FA[G, ?]]](fa => lift(f(fa)))
    }

  /**
    * Interpret this algebra into a FreeApplicative over another algebra.
    * Stack-safe.
    */
  def flatCompile[G[_]](f: F ~> FA[G, ?]): FA[G, A] =
    foldMap(f)

  /**
    * Interpret this algebra into a Monoid
    */
  final def analyze[M: Monoid](f: FunctionK[F, λ[α => M]]): M =
    foldMap[Const[M, ?]](
      λ[FunctionK[F, Const[M, ?]]](x => Const(f(x)))
    ).getConst

  /** Compile this FreeApplicative algebra into a Free algebra. */
  final def monad: Free[F, A] =
    foldMap[Free[F, ?]] {
      λ[FunctionK[F, Free[F, ?]]](fa => Free.liftF(fa))
    }

  override def toString: String = "FreeApplicative(...)"
}

object FreeApplicative {
  type FA[F[_], A] = FreeApplicative[F, A]

  // Internal helper function for foldMap, it folds only Pure and Lift nodes
  private[free] def foldArg[F[_], G[_], A](node: FA[F, A], f: F ~> G)(implicit G: Applicative[G]): G[A] =
    if (node.isInstanceOf[Pure[F, A]]) {
      val Pure(x) = node
      G.pure(x)
    } else {
      val Lift(fa) = node
      f(fa)
    }

  /** Represents a curried function `F[A => B => C => ...]`
   * that has been constructed with chained `ap` calls.
   * Fn#argc denotes the amount of curried params remaining.
   */
  private final case class Fn[G[_], A, B](gab: G[A => B], argc: Int)

  private final case class Pure[F[_], A](a: A) extends FA[F, A]

  private final case class Lift[F[_], A](fa: F[A]) extends FA[F, A]

  private final case class Ap[F[_], P, A](fn: FA[F, P => A], fp: FA[F, P]) extends FA[F, A]

  final def pure[F[_], A](a: A): FA[F, A] =
    Pure(a)

  final def ap[F[_], P, A](fp: F[P])(f: FA[F, P => A]): FA[F, A] =
    Ap(f, Lift(fp))

  final def lift[F[_], A](fa: F[A]): FA[F, A] =
    Lift(fa)

  implicit final def freeApplicative[S[_]]: Applicative[FA[S, ?]] = {
    new Applicative[FA[S, ?]] {
      override def product[A, B](fa: FA[S, A], fb: FA[S, B]): FA[S, (A, B)] = ap(fa.map((a: A) => (b: B) => (a, b)))(fb)

      override def map[A, B](fa: FA[S, A])(f: A => B): FA[S, B] = fa.map(f)

      override def ap[A, B](f: FA[S, A => B])(fa: FA[S, A]): FA[S, B] = fa.ap(f)

      def pure[A](a: A): FA[S, A] = Pure(a)
    }
  }
}
