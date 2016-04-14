object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

} /* object Fun */

object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => HOL.eq[A](x1, y1) && HOL.eq[B](x2, y2)
}

implicit def equal_prod[A : HOL.equal, B : HOL.equal]: HOL.equal[(A, B)] = new
  HOL.equal[(A, B)] {
  val `HOL.equal` = (a: (A, B), b: (A, B)) => equal_proda[A, B](a, b)
}

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

} /* object Product_Type */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)

trait preorder[A] extends ord[A] {
}

trait order[A] extends preorder[A] {
}

trait linorder[A] extends order[A] {
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

} /* object Orderings */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def integer_of_nat(x0: nat): BigInt = x0 match {
  case Nata(x) => x
}

def equal_nata(m: nat, n: nat): Boolean = integer_of_nat(m) == integer_of_nat(n)

implicit def equal_nat: HOL.equal[nat] = new HOL.equal[nat] {
  val `HOL.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def less_eq_nat(m: nat, n: nat): Boolean =
  integer_of_nat(m) <= integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean = integer_of_nat(m) < integer_of_nat(n)

implicit def ord_nat: Orderings.ord[nat] = new Orderings.ord[nat] {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def preorder_nat: Orderings.preorder[nat] = new Orderings.preorder[nat]
  {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def order_nat: Orderings.order[nat] = new Orderings.order[nat] {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def linorder_nat: Orderings.linorder[nat] = new Orderings.linorder[nat]
  {
  val `Orderings.less_eq` = (a: nat, b: nat) => less_eq_nat(a, b)
  val `Orderings.less` = (a: nat, b: nat) => less_nat(a, b)
}

implicit def ord_integer: Orderings.ord[BigInt] = new Orderings.ord[BigInt] {
  val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
}

def plus_nat(m: nat, n: nat): nat = Nata(integer_of_nat(m) + integer_of_nat(n))

def one_nat: nat = Nata(BigInt(1))

def Suc(n: nat): nat = plus_nat(n, one_nat)

def zero_nat: nat = Nata(BigInt(0))

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(-1) else BigInt(1)))

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (Fun.comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                           BigInt](Fun.comp[BigInt => BigInt,
     ((BigInt, BigInt)) => (BigInt, BigInt),
     BigInt](((a: BigInt => BigInt) => (b: (BigInt, BigInt)) =>
               Product_Type.apsnd[BigInt, BigInt, BigInt](a, b)),
              ((a: BigInt) => (b: BigInt) => a * b)),
                                    ((a: BigInt) =>
                                      sgn_integer(a)))).apply(l).apply((if (sgn_integer(k) ==
                                      sgn_integer(l))
                                 ((k: BigInt) => (l: BigInt) => if (l == 0)
                                   (BigInt(0), k) else
                                   (k.abs /% l.abs)).apply(k).apply(l)
                                 else {
val (r, s): (BigInt, BigInt) =
  ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
    (k.abs /% l.abs)).apply(k).apply(l);
(if (s == BigInt(0)) ((- r), BigInt(0)) else ((- r) - BigInt(1), l.abs - s))
                                      }))))

def nat_of_integer(k: BigInt): nat = Nata(Orderings.max[BigInt](BigInt(0), k))

def minus_nat(m: nat, n: nat): nat =
  Nata(Orderings.max[BigInt](BigInt(0), integer_of_nat(m) - integer_of_nat(n)))

def times_nat(m: nat, n: nat): nat = Nata(integer_of_nat(m) * integer_of_nat(n))

def mod_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.snd[BigInt, BigInt](divmod_integer(k, l))

} /* object Nat */

object Set {

def equal_lista[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) =>
    HOL.eq[A](x21, y21) && equal_lista[A](x22, y22)
  case (Nil, Nil) => true
}

implicit def equal_list[A : HOL.equal]: HOL.equal[List[A]] = new
  HOL.equal[List[A]] {
  val `HOL.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
}

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def nth[A](x0: List[A], n: Nat.nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (Nat.equal_nata(n, Nat.zero_nat)) x
      else nth[A](xs, Nat.minus_nat(n, Nat.one_nat)))
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def rev[A](xs: List[A]): List[A] =
  fold[A, List[A]](((a: A) => (b: List[A]) => a :: b), xs, Nil)

def upt(i: Nat.nat, j: Nat.nat): List[Nat.nat] =
  (if (Nat.less_nat(i, j)) i :: upt(Nat.Suc(i), j) else Nil)

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](map[A, B](f, xs))
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x :: xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def membera[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => HOL.eq[A](x, y) || membera[A](xs, y)
}

def inserta[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (membera[A](xs, x)) xs else x :: xs)

def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](inserta[A](x, xs))
}

def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (membera[A](xs, x))
  case (x, seta(xs)) => membera[A](xs, x)
}

def remove[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](inserta[A](x, xs))
  case (x, seta(xs)) => seta[A](removeAll[A](x, xs))
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def hd[A](x0: List[A]): A = x0 match {
  case x21 :: x22 => x21
}

def remdups[A : HOL.equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (membera[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def remove1[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) => (if (HOL.eq[A](x, y)) xs else y :: remove1[A](x, xs))
}

def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
  case (n, Nil) => n
}

def bot_set[A]: set[A] = seta[A](Nil)

def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](filter[A](((x: A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
}

def top_set[A]: set[A] = coset[A](Nil)

def minus_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) => seta[A](filter[A](((x: A) => member[A](x, a)), xs))
  case (a, seta(xs)) =>
    fold[A, set[A]](((aa: A) => (b: set[A]) => remove[A](aa, b)), xs, a)
}

def size_list[A]: (List[A]) => Nat.nat =
  ((a: List[A]) => gen_length[A](Nat.zero_nat, a))

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def insort_insert_key[A, B : HOL.equal : Orderings.linorder](f: A => B, x: A,
                      xs: List[A]):
      List[A]
  =
  (if (member[B](f(x), image[A, B](f, seta[A](xs)))) xs
    else insort_key[A, B](f, x, xs))

} /* object Set */

object String {

abstract sealed class nibble
final case class Nibble0() extends nibble
final case class Nibble1() extends nibble
final case class Nibble2() extends nibble
final case class Nibble3() extends nibble
final case class Nibble4() extends nibble
final case class Nibble5() extends nibble
final case class Nibble6() extends nibble
final case class Nibble7() extends nibble
final case class Nibble8() extends nibble
final case class Nibble9() extends nibble
final case class NibbleA() extends nibble
final case class NibbleB() extends nibble
final case class NibbleC() extends nibble
final case class NibbleD() extends nibble
final case class NibbleE() extends nibble
final case class NibbleF() extends nibble

abstract sealed class char
final case class Char(a: nibble, b: nibble) extends char

} /* object String */

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.coset(xs) =>
    { sys.error("card (List.coset _) requires type class instance card_UNIV");
      (((_: Unit) => card[A](Set.coset[A](xs)))).apply(()) }
  case Set.seta(xs) => Set.size_list[A].apply(Set.remdups[A](xs))
}

} /* object Finite_Set */

object FSet {

abstract sealed class fset[A]
final case class Abs_fset[A](a: Set.set[A]) extends fset[A]

def fset[A](x0: fset[A]): Set.set[A] = x0 match {
  case Abs_fset(x) => x
}

def fcard[A : HOL.equal](xa: fset[A]): Nat.nat = Finite_Set.card[A](fset[A](xa))

def fimage[B, A](xb: B => A, xc: fset[B]): fset[A] =
  Abs_fset[A](Set.image[B, A](xb, fset[B](xc)))

def finsert[A : HOL.equal](xb: A, xc: fset[A]): fset[A] =
  Abs_fset[A](Set.insert[A](xb, fset[A](xc)))

def bot_fset[A]: fset[A] = Abs_fset[A](Set.bot_set[A])

def sup_fset[A : HOL.equal](xb: fset[A], xc: fset[A]): fset[A] =
  Abs_fset[A](Set.sup_set[A](fset[A](xb), fset[A](xc)))

def minus_fset[A : HOL.equal](xb: fset[A], xc: fset[A]): fset[A] =
  Abs_fset[A](Set.minus_set[A](fset[A](xb), fset[A](xc)))

} /* object FSet */

object Phantom_Type {

abstract sealed class phantom[A, B]
final case class phantoma[B, A](a: B) extends phantom[A, B]

def of_phantom[A, B](x0: phantom[A, B]): B = x0 match {
  case phantoma(x) => x
}

} /* object Phantom_Type */

object Cardinality {

def finite_UNIV_nata: Phantom_Type.phantom[Nat.nat, Boolean] =
  Phantom_Type.phantoma[Boolean, Nat.nat](false)

def card_UNIV_nata: Phantom_Type.phantom[Nat.nat, Nat.nat] =
  Phantom_Type.phantoma[Nat.nat, Nat.nat](Nat.zero_nat)

trait finite_UNIV[A] {
  val `Cardinality.finite_UNIV`: Phantom_Type.phantom[A, Boolean]
}
def finite_UNIV[A](implicit A: finite_UNIV[A]): Phantom_Type.phantom[A, Boolean]
  = A.`Cardinality.finite_UNIV`

trait card_UNIV[A] extends finite_UNIV[A] {
  val `Cardinality.card_UNIVa`: Phantom_Type.phantom[A, Nat.nat]
}
def card_UNIVa[A](implicit A: card_UNIV[A]): Phantom_Type.phantom[A, Nat.nat] =
  A.`Cardinality.card_UNIVa`

implicit def finite_UNIV_nat: finite_UNIV[Nat.nat] = new finite_UNIV[Nat.nat] {
  val `Cardinality.finite_UNIV` = finite_UNIV_nata
}

implicit def card_UNIV_nat: card_UNIV[Nat.nat] = new card_UNIV[Nat.nat] {
  val `Cardinality.card_UNIVa` = card_UNIV_nata
  val `Cardinality.finite_UNIV` = finite_UNIV_nata
}

def card[A : card_UNIV : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.coset(xs) =>
    Nat.minus_nat(Phantom_Type.of_phantom[A, Nat.nat](card_UNIVa[A]),
                   Set.size_list[A].apply(Set.remdups[A](xs)))
  case Set.seta(xs) => Set.size_list[A].apply(Set.remdups[A](xs))
}

def card_UNIV[A : card_UNIV]: Phantom_Type.phantom[A, Nat.nat] = card_UNIVa[A]

def is_list_UNIV[A : card_UNIV : HOL.equal](xs: List[A]): Boolean =
  {
    val c: Nat.nat = Phantom_Type.of_phantom[A, Nat.nat](card_UNIV[A]);
    (if (Nat.equal_nata(c, Nat.zero_nat)) false
      else Nat.equal_nata(Set.size_list[A].apply(Set.remdups[A](xs)), c))
  }

} /* object Cardinality */

object FinFun {

import /*implicits*/ Product_Type.equal_prod

abstract sealed class finfun[A, B]
final case class finfun_const[B, A](a: B) extends finfun[A, B]
final case class finfun_update_code[A, B](a: finfun[A, B], b: A, c: B) extends
  finfun[A, B]

def finfun_comp[A, B, C](g: A => B, x1: finfun[C, A]): finfun[C, B] = (g, x1)
  match {
  case (g, finfun_update_code(f, a, b)) =>
    finfun_update_code[C, B](finfun_comp[A, B, C](g, f), a, g(b))
  case (g, finfun_const(c)) => finfun_const[B, C](g(c))
}

def finfun_update[A : HOL.equal, B : HOL.equal](x0: finfun[A, B], a: A, b: B):
      finfun[A, B]
  =
  (x0, a, b) match {
  case (finfun_update_code(f, aa, ba), a, b) =>
    (if (HOL.eq[A](aa, a)) finfun_update[A, B](f, aa, b)
      else finfun_update_code[A, B](finfun_update[A, B](f, a, b), aa, ba))
  case (finfun_const(ba), a, b) =>
    (if (HOL.eq[B](ba, b)) finfun_const[B, A](ba)
      else finfun_update_code[A, B](finfun_const[B, A](ba), a, b))
}

def finfun_apply[A : HOL.equal, B](x0: finfun[A, B], a: A): B = (x0, a) match {
  case (finfun_const(b), a) => b
  case (finfun_update_code(f, aa, b), a) =>
    (if (HOL.eq[A](aa, a)) b else finfun_apply[A, B](f, a))
}

def finfun_Diag[A : HOL.equal, B : HOL.equal,
                 C : HOL.equal](x0: finfun[A, B], g: finfun[A, C]):
      finfun[A, (B, C)]
  =
  (x0, g) match {
  case (finfun_update_code(f, a, b), g) =>
    finfun_update[A, (B, C)](finfun_Diag[A, B, C](f, g), a,
                              (b, finfun_apply[A, C](g, a)))
  case (finfun_const(b), finfun_update_code(g, a, c)) =>
    finfun_update_code[A, (B, C)](finfun_Diag[A, B,
       C](finfun_const[B, A](b), g),
                                   a, (b, c))
  case (finfun_const(b), finfun_const(c)) => finfun_const[(B, C), A]((b, c))
}

def finfun_All_except[A : Cardinality.card_UNIV : HOL.equal](aa: List[A],
                      x1: finfun[A, Boolean]):
      Boolean
  =
  (aa, x1) match {
  case (aa, finfun_update_code(f, a, b)) =>
    (Set.membera[A](aa, a) || b) && finfun_All_except[A](a :: aa, f)
  case (a, finfun_const(b)) => b || Cardinality.is_list_UNIV[A](a)
}

def finfun_All[A : Cardinality.card_UNIV : HOL.equal]:
      (finfun[A, Boolean]) => Boolean
  =
  ((a: finfun[A, Boolean]) => finfun_All_except[A](Nil, a))

def equal_finfuna[A : Cardinality.card_UNIV : HOL.equal,
                   B : HOL.equal](f: finfun[A, B], g: finfun[A, B]):
      Boolean
  =
  finfun_All[A].apply(finfun_comp[(B, B), Boolean,
                                   A](((a: (B, B)) =>
{
  val (aa, b): (B, B) = a;
  HOL.eq[B](aa, b)
}),
                                       finfun_Diag[A, B, B](f, g)))

implicit def
  equal_finfun[A : Cardinality.card_UNIV : HOL.equal, B : HOL.equal]:
    HOL.equal[finfun[A, B]]
  = new HOL.equal[finfun[A, B]] {
  val `HOL.equal` = (a: finfun[A, B], b: finfun[A, B]) =>
    equal_finfuna[A, B](a, b)
}

def finfun_default[A : Cardinality.card_UNIV : HOL.equal, B](x0: finfun[A, B]):
      B
  =
  x0 match {
  case finfun_update_code(f, a, b) => finfun_default[A, B](f)
  case finfun_const(c) =>
    (if (Nat.equal_nata(Cardinality.card[A](Set.top_set[A]), Nat.zero_nat)) c
      else sys.error("undefined"))
}

def finfun_to_list[A : Cardinality.card_UNIV : HOL.equal : Orderings.linorder,
                    B : HOL.equal](x0: finfun[A, B]):
      List[A]
  =
  x0 match {
  case finfun_update_code(f, a, b) =>
    (if (HOL.eq[B](b, finfun_default[A, B](f)))
      Set.remove1[A](a, finfun_to_list[A, B](f))
      else Set.insort_insert_key[A, A](((x: A) => x), a,
finfun_to_list[A, B](f)))
  case finfun_const(c) =>
    (if (Nat.equal_nata(Cardinality.card[A](Set.top_set[A]), Nat.zero_nat)) Nil
      else { sys.error("finfun_to_list called on finite type");
             (((_: Unit) =>
                finfun_to_list[A, B](finfun_const[B, A](c)))).apply(())
             })
}

} /* object FinFun */

object Divides {

def mod_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Nat.mod_integer(Nat.integer_of_nat(m), Nat.integer_of_nat(n)))

} /* object Divides */

object Optiona {

def equal_optiona[A : HOL.equal](x0: Option[A], x1: Option[A]): Boolean =
  (x0, x1) match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => HOL.eq[A](x2, y2)
  case (None, None) => true
}

implicit def equal_option[A : HOL.equal]: HOL.equal[Option[A]] = new
  HOL.equal[Option[A]] {
  val `HOL.equal` = (a: Option[A], b: Option[A]) => equal_optiona[A](a, b)
}

def bind[A, B](x0: Option[A], f: A => Option[B]): Option[B] = (x0, f) match {
  case (None, f) => None
  case (Some(x), f) => f(x)
}

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def the[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

} /* object Optiona */

object LinorderOption {

def less_eq_o[A : Orderings.ord](x0: Option[A], uu: Option[A]): Boolean =
  (x0, uu) match {
  case (None, uu) => true
  case (Some(x), None) => false
  case (Some(x), Some(y)) => Orderings.less_eq[A](x, y)
}

def less_eq_option[A : Orderings.preorder](o1: Option[A], o2: Option[A]):
      Boolean
  =
  less_eq_o[A](o1, o2)

def less_o[A : Orderings.ord](x0: Option[A], x1: Option[A]): Boolean = (x0, x1)
  match {
  case (None, None) => false
  case (None, Some(v)) => true
  case (Some(x), None) => false
  case (Some(x), Some(y)) => Orderings.less[A](x, y)
}

def less_option[A : Orderings.preorder](o1: Option[A], o2: Option[A]): Boolean =
  less_o[A](o1, o2)

implicit def ord_option[A : Orderings.preorder]: Orderings.ord[Option[A]] = new
  Orderings.ord[Option[A]] {
  val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
    less_eq_option[A](a, b)
  val `Orderings.less` = (a: Option[A], b: Option[A]) => less_option[A](a, b)
}

} /* object LinorderOption */

object MultiPaxos4 {

import /*implicits*/ LinorderOption.ord_option, Nat.order_nat,
  FinFun.equal_finfun, Product_Type.equal_prod, Cardinality.card_UNIV_nat,
  Nat.linorder_nat, Optiona.equal_option, Set.equal_list, Nat.equal_nat

abstract sealed class cmd[A]
final case class Cmd[A](a: A) extends cmd[A]
final case class NoOp[A]() extends cmd[A]

def equal_cmda[A : HOL.equal](x0: cmd[A], x1: cmd[A]): Boolean = (x0, x1) match
  {
  case (Cmd(x1), NoOp()) => false
  case (NoOp(), Cmd(x1)) => false
  case (Cmd(x1), Cmd(y1)) => HOL.eq[A](x1, y1)
  case (NoOp(), NoOp()) => true
}

implicit def equal_cmd[A : HOL.equal]: HOL.equal[cmd[A]] = new HOL.equal[cmd[A]]
  {
  val `HOL.equal` = (a: cmd[A], b: cmd[A]) => equal_cmda[A](a, b)
}

def less_eq_pair[A, B : Orderings.ord, C](x0: (A, B), x1: (C, B)): Boolean =
  (x0, x1) match {
  case ((x, y), (u, v)) => Orderings.less_eq[B](y, v)
}

def less_eq_prod[A, B : Orderings.order](x: (A, B), y: (A, B)): Boolean =
  less_eq_pair[A, B, A](x, y)

def less_pair[A, B : Orderings.ord, C](x0: (A, B), x1: (C, B)): Boolean =
  (x0, x1) match {
  case ((x, y), (u, v)) => Orderings.less[B](y, v)
}

def less_prod[A, B : Orderings.order](x: (A, B), y: (A, B)): Boolean =
  less_pair[A, B, A](x, y)

implicit def ord_prod[A, B : Orderings.order]: Orderings.ord[(A, B)] = new
  Orderings.ord[(A, B)] {
  val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
  val `Orderings.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
}

implicit def preorder_prod[A, B : Orderings.order]: Orderings.preorder[(A, B)] =
  new Orderings.preorder[(A, B)] {
  val `Orderings.less_eq` = (a: (A, B), b: (A, B)) => less_eq_prod[A, B](a, b)
  val `Orderings.less` = (a: (A, B), b: (A, B)) => less_prod[A, B](a, b)
}

abstract sealed class msg[A]
final case class Phase1a[A](a: Nat.nat, b: Nat.nat) extends msg[A]
final case class
  Phase1b[A](a: FinFun.finfun[Nat.nat, Option[(cmd[A], Nat.nat)]], b: Nat.nat,
              c: Nat.nat)
  extends msg[A]
final case class Phase2a[A](a: Nat.nat, b: Nat.nat, c: cmd[A], d: Nat.nat)
  extends msg[A]
final case class Phase2b[A](a: Nat.nat, b: Nat.nat, c: Nat.nat, d: cmd[A])
  extends msg[A]
final case class Vote[A](a: Nat.nat, b: cmd[A]) extends msg[A]
final case class Fwd[A](a: A) extends msg[A]

def equal_msg[A : HOL.equal](x0: msg[A], x1: msg[A]): Boolean = (x0, x1) match {
  case (Vote(x51, x52), Fwd(x6)) => false
  case (Fwd(x6), Vote(x51, x52)) => false
  case (Phase2b(x41, x42, x43, x44), Fwd(x6)) => false
  case (Fwd(x6), Phase2b(x41, x42, x43, x44)) => false
  case (Phase2b(x41, x42, x43, x44), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase2b(x41, x42, x43, x44)) => false
  case (Phase2a(x31, x32, x33, x34), Fwd(x6)) => false
  case (Fwd(x6), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase2b(x41, x42, x43, x44)) => false
  case (Phase2b(x41, x42, x43, x44), Phase2a(x31, x32, x33, x34)) => false
  case (Phase1b(x21, x22, x23), Fwd(x6)) => false
  case (Fwd(x6), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase2b(x41, x42, x43, x44)) => false
  case (Phase2b(x41, x42, x43, x44), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase1b(x21, x22, x23)) => false
  case (Phase1a(x11, x12), Fwd(x6)) => false
  case (Fwd(x6), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase2b(x41, x42, x43, x44)) => false
  case (Phase2b(x41, x42, x43, x44), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase1a(x11, x12)) => false
  case (Fwd(x6), Fwd(y6)) => HOL.eq[A](x6, y6)
  case (Vote(x51, x52), Vote(y51, y52)) =>
    Nat.equal_nata(x51, y51) && equal_cmda[A](x52, y52)
  case (Phase2b(x41, x42, x43, x44), Phase2b(y41, y42, y43, y44)) =>
    Nat.equal_nata(x41, y41) &&
      (Nat.equal_nata(x42, y42) &&
        (Nat.equal_nata(x43, y43) && equal_cmda[A](x44, y44)))
  case (Phase2a(x31, x32, x33, x34), Phase2a(y31, y32, y33, y34)) =>
    Nat.equal_nata(x31, y31) &&
      (Nat.equal_nata(x32, y32) &&
        (equal_cmda[A](x33, y33) && Nat.equal_nata(x34, y34)))
  case (Phase1b(x21, x22, x23), Phase1b(y21, y22, y23)) =>
    FinFun.equal_finfuna[Nat.nat, Option[(cmd[A], Nat.nat)]](x21, y21) &&
      (Nat.equal_nata(x22, y22) && Nat.equal_nata(x23, y23))
  case (Phase1a(x11, x12), Phase1a(y11, y12)) =>
    Nat.equal_nata(x11, y11) && Nat.equal_nata(x12, y12)
}

abstract sealed class packet[A]
final case class Packet[A](a: Nat.nat, b: Nat.nat, c: msg[A]) extends packet[A]

def equal_packeta[A : HOL.equal](x0: packet[A], x1: packet[A]): Boolean =
  (x0, x1) match {
  case (Packet(x1, x2, x3), Packet(y1, y2, y3)) =>
    Nat.equal_nata(x1, y1) && (Nat.equal_nata(x2, y2) && equal_msg[A](x3, y3))
}

implicit def equal_packet[A : HOL.equal]: HOL.equal[packet[A]] = new
  HOL.equal[packet[A]] {
  val `HOL.equal` = (a: packet[A], b: packet[A]) => equal_packeta[A](a, b)
}

abstract sealed class acc_state_ext[A, B]
final case class
  acc_state_exta[A, B](a: Nat.nat, b: FSet.fset[Nat.nat], c: Option[Nat.nat],
                        d: FinFun.finfun[Nat.nat, Option[cmd[A]]],
                        e: FinFun.finfun[Nat.nat, Option[Nat.nat]],
                        f: FinFun.finfun[Nat.nat,
  FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]],
                        g: FinFun.finfun[Nat.nat,
  FinFun.finfun[Nat.nat, List[Nat.nat]]],
                        h: FinFun.finfun[Nat.nat, Option[cmd[A]]], i: Nat.nat,
                        j: FinFun.finfun[Nat.nat, Option[cmd[A]]], k: Boolean,
                        l: Option[Nat.nat], m: B)
  extends acc_state_ext[A, B]

def acceptors[A, B](x0: acc_state_ext[A, B]): FSet.fset[Nat.nat] = x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => acceptors
}

def nr[A, B](s: acc_state_ext[A, B]): Nat.nat =
  FSet.fcard[Nat.nat](acceptors[A, B](s))

def accs(n: Nat.nat): FSet.fset[Nat.nat] =
  (if (Nat.equal_nata(n, Nat.zero_nat)) FSet.bot_fset[Nat.nat]
    else FSet.sup_fset[Nat.nat](accs(Nat.minus_nat(n, Nat.one_nat)),
                                 FSet.finsert[Nat.nat](Nat.minus_nat(n,
                              Nat.one_nat),
                FSet.bot_fset[Nat.nat])))

def next_inst_update[A, B](next_insta: Nat.nat => Nat.nat,
                            x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (next_insta, x1) match {
  case (next_insta,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobs, decided, next_insta(next_inst), pending,
                             leader, last_decision, more)
}

def pending_update[A, B](pendinga:
                           (FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
                             FinFun.finfun[Nat.nat, Option[cmd[A]]],
                          x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (pendinga, x1) match {
  case (pendinga,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobs, decided, next_inst, pendinga(pending),
                             leader, last_decision, more)
}

def twobs_update[A, B](twobsa:
                         (FinFun.finfun[Nat.nat,
 FinFun.finfun[Nat.nat, List[Nat.nat]]]) =>
                           FinFun.finfun[Nat.nat,
  FinFun.finfun[Nat.nat, List[Nat.nat]]],
                        x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (twobsa, x1) match {
  case (twobsa,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobsa(twobs), decided, next_inst, pending, leader,
                             last_decision, more)
}

def next_inst[A, B](x0: acc_state_ext[A, B]): Nat.nat = x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => next_inst
}

def pending[A, B](x0: acc_state_ext[A, B]):
      FinFun.finfun[Nat.nat, Option[cmd[A]]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => pending
}

def ballot[A, B](x0: acc_state_ext[A, B]): Option[Nat.nat] = x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => ballot
}

def twobs[A, B](x0: acc_state_ext[A, B]):
      FinFun.finfun[Nat.nat, FinFun.finfun[Nat.nat, List[Nat.nat]]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => twobs
}

def id[A, B](x0: acc_state_ext[A, B]): Nat.nat = x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => id
}

def send_all[A, B, C](s: acc_state_ext[A, B], a: Nat.nat, m: msg[C]):
      FSet.fset[packet[C]]
  =
  FSet.fimage[Nat.nat,
               packet[C]](((a2: Nat.nat) => Packet[C](id[A, B](s), a2, m)),
                           FSet.minus_fset[Nat.nat](acceptors[A, B](s),
             FSet.finsert[Nat.nat](a, FSet.bot_fset[Nat.nat])))

def do_2a[A, B](s: acc_state_ext[A, B], v: cmd[A]):
      (acc_state_ext[A, B], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, B](s)
    val inst: Nat.nat = next_inst[A, B](s)
    val b: Nat.nat = Optiona.the[Nat.nat](ballot[A, B](s))
    val msg: msg[A] = Phase2a[A](inst, b, v, a)
    val new_state: acc_state_ext[A, B] =
      twobs_update[A, B](((_: FinFun.finfun[Nat.nat,
     FinFun.finfun[Nat.nat, List[Nat.nat]]])
                            =>
                           FinFun.finfun_update_code[Nat.nat,
              FinFun.finfun[Nat.nat,
                             List[Nat.nat]]](twobs[A, B](s), inst,
      FinFun.finfun_update[Nat.nat,
                            List[Nat.nat]](FinFun.finfun_const[List[Nat.nat],
                        Nat.nat](Nil),
    b, List(a)))),
                          pending_update[A,
  B](((_: FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
       FinFun.finfun_update_code[Nat.nat,
                                  Option[cmd[A]]](pending[A, B](s), inst,
           Some[cmd[A]](v))),
      next_inst_update[A, B](((_: Nat.nat) => Nat.plus_nat(inst, Nat.one_nat)),
                              s)));
    (new_state, send_all[A, B, A](s, a, msg))
  }

def decided[A, B](x0: acc_state_ext[A, B]):
      FinFun.finfun[Nat.nat, Option[cmd[A]]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => decided
}

def learn[A : HOL.equal](i: Nat.nat, v: A, s: acc_state_ext[A, Unit]):
      Option[(acc_state_ext[A, Unit], FSet.fset[packet[A]])]
  =
  (FinFun.finfun_apply[Nat.nat, Option[cmd[A]]](decided[A, Unit](s), i) match {
     case None => None
     case Some(Cmd(c)) =>
       (if (HOL.eq[A](v, c))
         Some[(acc_state_ext[A, Unit],
                FSet.fset[packet[A]])]((s, FSet.bot_fset[packet[A]]))
         else None)
     case Some(NoOp()) => None
   })

def getOwnedBallot(a: Nat.nat, b: Nat.nat, n: Nat.nat): Nat.nat =
  (if (Nat.equal_nata(b, Nat.zero_nat)) Nat.zero_nat
    else (if (Nat.equal_nata(Divides.mod_nat(Nat.Suc(Nat.minus_nat(b,
                            Nat.one_nat)),
      n),
                              a))
           Nat.Suc(Nat.minus_nat(b, Nat.one_nat))
           else getOwnedBallot(a, Nat.minus_nat(b, Nat.one_nat), n)))

def suc_bal(a: Nat.nat, b: Nat.nat, n: Nat.nat): Nat.nat =
  getOwnedBallot(a, Nat.plus_nat(b, n), n)

def nx_bal(a: Nat.nat, x1: Option[Nat.nat], n: Nat.nat): Nat.nat = (a, x1, n)
  match {
  case (a, None, n) => suc_bal(a, Nat.zero_nat, n)
  case (a, Some(b), n) => suc_bal(a, b, n)
}

def leader[A, B](x0: acc_state_ext[A, B]): Boolean = x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => leader
}

def leader_of_bal[A, B](s: acc_state_ext[A, B], b: Option[Nat.nat]): Nat.nat =
  (b match {
     case None => Nat.zero_nat
     case Some(ba) => Divides.mod_nat(ba, nr[A, B](s))
   })

def propose[A : HOL.equal](v: A, s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, Unit](s);
    (if (Nat.equal_nata(leader_of_bal[A, Unit](s, ballot[A, Unit](s)), a) &&
           leader[A, Unit](s))
      do_2a[A, Unit](s, Cmd[A](v))
      else (if (Nat.equal_nata(leader_of_bal[A, Unit](s, ballot[A, Unit](s)),
                                a))
             (s, FSet.bot_fset[packet[A]])
             else (s, FSet.finsert[packet[A]](Packet[A](a,
                 leader_of_bal[A, Unit](s, ballot[A, Unit](s)), Fwd[A](v)),
       FSet.bot_fset[packet[A]]))))
  }

def ballot_update[A, B](ballota: Option[Nat.nat] => Option[Nat.nat],
                         x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (ballota, x1) match {
  case (ballota,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballota(ballot), vote, last_ballot,
                             onebs, twobs, decided, next_inst, pending, leader,
                             last_decision, more)
}

def send_1a[A](s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, Unit](s)
    val b: Nat.nat = nx_bal(a, ballot[A, Unit](s), nr[A, Unit](s))
    val msg_1a: msg[A] = Phase1a[A](a, b);
    (ballot_update[A, Unit](((_: Option[Nat.nat]) => Some[Nat.nat](b)), s),
      FSet.fimage[Nat.nat,
                   packet[A]](((a2: Nat.nat) => Packet[A](a, a2, msg_1a)),
                               acceptors[A, Unit](s)))
  }

def is_leader[A, B](s: acc_state_ext[A, B]): Boolean = leader[A, B](s)

def new_twobs[A, B](s: acc_state_ext[A, B], i: Nat.nat, b: Nat.nat, a: Nat.nat):
      List[Nat.nat]
  =
  a :: FinFun.finfun_apply[Nat.nat,
                            List[Nat.nat]](FinFun.finfun_apply[Nat.nat,
                        FinFun.finfun[Nat.nat,
                                       List[Nat.nat]]](twobs[A, B](s), i),
    b)

def get_ballot[A, B](s: acc_state_ext[A, B]): Option[Nat.nat] = ballot[A, B](s)

def get_leader[A, B](s: acc_state_ext[A, B]): Option[Nat.nat] =
  (ballot[A, B](s) match {
     case None => None
     case Some(b) => Some[Nat.nat](Divides.mod_nat(b, nr[A, B](s)))
   })

def last_ballot[A, B](x0: acc_state_ext[A, B]):
      FinFun.finfun[Nat.nat, Option[Nat.nat]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => last_ballot
}

def vote[A, B](x0: acc_state_ext[A, B]): FinFun.finfun[Nat.nat, Option[cmd[A]]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => vote
}

def receive_1a[A : HOL.equal](l: Nat.nat, b: Nat.nat,
                               s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val bal: Option[Nat.nat] = ballot[A, Unit](s)
    val a: Nat.nat = id[A, Unit](s);
    (if (Optiona.is_none[Nat.nat](bal) ||
           Nat.less_nat(Optiona.the[Nat.nat](bal), b))
      {
        val combiner:
              ((Option[cmd[A]], Option[Nat.nat])) => Option[(cmd[A], Nat.nat)]
          = ((aa: (Option[cmd[A]], Option[Nat.nat])) =>
              {
                val (vo, bo): (Option[cmd[A]], Option[Nat.nat]) = aa;
                Optiona.bind[cmd[A],
                              (cmd[A],
                                Nat.nat)](vo,
   ((v: cmd[A]) =>
     Optiona.bind[Nat.nat,
                   (cmd[A],
                     Nat.nat)](bo, ((ba: Nat.nat) =>
                                     Some[(cmd[A], Nat.nat)]((v, ba))))))
              })
        val last_votes: FinFun.finfun[Nat.nat, Option[(cmd[A], Nat.nat)]] =
          FinFun.finfun_comp[(Option[cmd[A]], Option[Nat.nat]),
                              Option[(cmd[A], Nat.nat)],
                              Nat.nat](combiner,
FinFun.finfun_Diag[Nat.nat, Option[cmd[A]],
                    Option[Nat.nat]](vote[A, Unit](s), last_ballot[A, Unit](s)))
        val msg_1b: msg[A] = Phase1b[A](last_votes, b, a)
        val packet: packet[A] = Packet[A](a, l, msg_1b)
        val state: acc_state_ext[A, Unit] =
          ballot_update[A, Unit](((_: Option[Nat.nat]) => Some[Nat.nat](b)), s);
        (state, FSet.finsert[packet[A]](packet, FSet.bot_fset[packet[A]]))
      }
      else (s, FSet.bot_fset[packet[A]]))
  }

def leader_update[A, B](leadera: Boolean => Boolean, x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (leadera, x1) match {
  case (leadera,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobs, decided, next_inst, pending,
                             leadera(leader), last_decision, more)
}

def onebs[A, B](x0: acc_state_ext[A, B]):
      FinFun.finfun[Nat.nat,
                     FinFun.finfun[Nat.nat,
                                    List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]]
  =
  x0 match {
  case acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                       decided, next_inst, pending, leader, last_decision, more)
    => onebs
}

def one_b_quorum_received[A, B](b: Nat.nat, s: acc_state_ext[A, B]): Boolean =
  {
    val at_b: FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]
      = FinFun.finfun_apply[Nat.nat,
                             FinFun.finfun[Nat.nat,
    List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]](onebs[A, B](s), b)
    val at_b_i: List[(Nat.nat, Option[(cmd[A], Nat.nat)])] =
      FinFun.finfun_apply[Nat.nat,
                           List[(Nat.nat,
                                  Option[(cmd[A],
   Nat.nat)])]](at_b, Nat.zero_nat);
    Nat.less_nat(nr[A, B](s),
                  Nat.times_nat(Nat.nat_of_integer(BigInt(2)),
                                 Set.size_list[(Nat.nat,
         Option[(cmd[A], Nat.nat)])].apply(at_b_i)))
  }

def highest_voted[A](m: FinFun.finfun[Nat.nat,
                                       List[(Nat.nat,
      Option[(cmd[A], Nat.nat)])]]):
      FinFun.finfun[Nat.nat, Option[cmd[A]]]
  =
  {
    val votes: FinFun.finfun[Nat.nat, List[Option[(cmd[A], Nat.nat)]]] =
      FinFun.finfun_comp[List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                          List[Option[(cmd[A], Nat.nat)]],
                          Nat.nat](((a: List[(Nat.nat,
       Option[(cmd[A], Nat.nat)])])
                                      =>
                                     Set.map[(Nat.nat,
       Option[(cmd[A], Nat.nat)]),
      Option[(cmd[A],
               Nat.nat)]](((aa: (Nat.nat, Option[(cmd[A], Nat.nat)])) =>
                            Product_Type.snd[Nat.nat,
      Option[(cmd[A], Nat.nat)]](aa)),
                           a)),
                                    m)
    val highest: (List[Option[(cmd[A], Nat.nat)]]) => Option[cmd[A]] =
      ((l: List[Option[(cmd[A], Nat.nat)]]) =>
        (if (Set.nulla[Option[(cmd[A], Nat.nat)]](l)) None
          else Optiona.bind[(cmd[A], Nat.nat),
                             cmd[A]](Set.fold[Option[(cmd[A], Nat.nat)],
       Option[(cmd[A],
                Nat.nat)]](((a: Option[(cmd[A], Nat.nat)]) =>
                             (b: Option[(cmd[A], Nat.nat)]) =>
                             Orderings.max[Option[(cmd[A], Nat.nat)]](a, b)),
                            l, Set.nth[Option[(cmd[A],
        Nat.nat)]](l, Nat.zero_nat)),
                                      ((vb: (cmd[A], Nat.nat)) =>
Some[cmd[A]](Product_Type.fst[cmd[A], Nat.nat](vb))))));
    FinFun.finfun_comp[List[Option[(cmd[A], Nat.nat)]], Option[cmd[A]],
                        Nat.nat](highest, votes)
  }

def onebs_update[A, B](onebsa:
                         (FinFun.finfun[Nat.nat,
 FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]]) =>
                           FinFun.finfun[Nat.nat,
  FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]],
                        x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (onebsa, x1) match {
  case (onebsa,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot,
                             onebsa(onebs), twobs, decided, next_inst, pending,
                             leader, last_decision, more)
}

def update_onebs[A : HOL.equal](s: acc_state_ext[A, Unit], bal: Nat.nat,
                                 a2: Nat.nat,
                                 last_vs:
                                   FinFun.finfun[Nat.nat,
          Option[(cmd[A], Nat.nat)]]):
      acc_state_ext[A, Unit]
  =
  {
    id[A, Unit](s)
    val combiner:
          ((List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
            Option[(cmd[A], Nat.nat)])) =>
            List[(Nat.nat, Option[(cmd[A], Nat.nat)])]
      = ((a: (List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
               Option[(cmd[A], Nat.nat)]))
           =>
          (a match {
             case (xs, None) => (a2, None) :: xs
             case (xs, Some(z)) => (a2, Some[(cmd[A], Nat.nat)](z)) :: xs
           }))
    val pair_map:
          FinFun.finfun[Nat.nat,
                         (List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                           Option[(cmd[A], Nat.nat)])]
      = FinFun.finfun_Diag[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                            Option[(cmd[A],
                                     Nat.nat)]](FinFun.finfun_apply[Nat.nat,
                             FinFun.finfun[Nat.nat,
    List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]](onebs[A, Unit](s), bal),
         last_vs)
    val at_bal:
          FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]
      = FinFun.finfun_comp[(List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                             Option[(cmd[A], Nat.nat)]),
                            List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                            Nat.nat](combiner, pair_map);
    onebs_update[A, Unit](((_: FinFun.finfun[Nat.nat,
      FinFun.finfun[Nat.nat, List[(Nat.nat, Option[(cmd[A], Nat.nat)])]]])
                             =>
                            FinFun.finfun_update[Nat.nat,
          FinFun.finfun[Nat.nat,
                         List[(Nat.nat,
                                Option[(cmd[A],
 Nat.nat)])]]](onebs[A, Unit](s), bal, at_bal)),
                           s)
  }

def receive_1b[A : HOL.equal](last_vs:
                                FinFun.finfun[Nat.nat,
       Option[(cmd[A], Nat.nat)]],
                               bal: Nat.nat, a2: Nat.nat,
                               s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, Unit](s);
    (if (Optiona.equal_optiona[Nat.nat](Some[Nat.nat](bal), ballot[A, Unit](s)))
      {
        val s1: acc_state_ext[A, Unit] = update_onebs[A](s, bal, a2, last_vs);
        (if (one_b_quorum_received[A, Unit](bal, s1))
          {
            val h: FinFun.finfun[Nat.nat, Option[cmd[A]]] =
              highest_voted[A](FinFun.finfun_apply[Nat.nat,
            FinFun.finfun[Nat.nat,
                           List[(Nat.nat,
                                  Option[(cmd[A],
   Nat.nat)])]]](onebs[A, Unit](s1), bal))
            val max_i: Nat.nat =
              {
                val l: List[Nat.nat] =
                  FinFun.finfun_to_list[Nat.nat,
 List[(Nat.nat,
        Option[(cmd[A],
                 Nat.nat)])]](FinFun.finfun_apply[Nat.nat,
           FinFun.finfun[Nat.nat,
                          List[(Nat.nat,
                                 Option[(cmd[A],
  Nat.nat)])]]](onebs[A, Unit](s1), bal));
                (if (Set.nulla[Nat.nat](l)) Nat.zero_nat
                  else Set.hd[Nat.nat](Set.rev[Nat.nat](l)))
              }
            val s2: acc_state_ext[A, Unit] =
              leader_update[A, Unit](((_: Boolean) => true), s1)
            val s3: acc_state_ext[A, Unit] =
              next_inst_update[A, Unit](((_: Nat.nat) =>
  Nat.plus_nat(max_i, Nat.one_nat)),
 s2)
            val twoa_is: List[Nat.nat] =
              Set.upt(Nat.one_nat, Nat.plus_nat(max_i, Nat.one_nat))
            val s4: acc_state_ext[A, Unit] =
              Set.fold[Nat.nat,
                        acc_state_ext[A, Unit]](((i: Nat.nat) =>
          (sa: acc_state_ext[A, Unit]) =>
          twobs_update[A, Unit](((_: FinFun.finfun[Nat.nat,
            FinFun.finfun[Nat.nat, List[Nat.nat]]])
                                   =>
                                  FinFun.finfun_update_code[Nat.nat,
                     FinFun.finfun[Nat.nat,
                                    List[Nat.nat]]](twobs[A, Unit](sa), i,
             FinFun.finfun_update[Nat.nat,
                                   List[Nat.nat]](FinFun.finfun_apply[Nat.nat,
                               FinFun.finfun[Nat.nat,
      List[Nat.nat]]](twobs[A, Unit](sa), i),
           bal, List(a)))),
                                 sa)),
         twoa_is, s3)
            val msgs: List[msg[A]] =
              Set.map[Nat.nat,
                       msg[A]](((i: Nat.nat) =>
                                 (FinFun.finfun_apply[Nat.nat,
               Option[cmd[A]]](h, i)
                                    match {
                                    case None =>
                                      Phase2a[A](i, bal, NoOp[A](), a)
                                    case Some(v) => Phase2a[A](i, bal, v, a)
                                  })),
                                twoa_is)
            val pckts: List[FSet.fset[packet[A]]] =
              Set.map[msg[A],
                       FSet.fset[packet[A]]](((b: msg[A]) =>
       send_all[A, Unit, A](s, a, b)),
      msgs);
            (s4, Set.fold[FSet.fset[packet[A]],
                           FSet.fset[packet[A]]](((aa: FSet.fset[packet[A]]) =>
           (b: FSet.fset[packet[A]]) => FSet.sup_fset[packet[A]](aa, b)),
          pckts, FSet.bot_fset[packet[A]]))
          }
          else (s1, FSet.bot_fset[packet[A]]))
      }
      else (s, FSet.bot_fset[packet[A]]))
  }

def vote_update[A, B](votea:
                        (FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
                          FinFun.finfun[Nat.nat, Option[cmd[A]]],
                       x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (votea, x1) match {
  case (votea,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, votea(vote), last_ballot,
                             onebs, twobs, decided, next_inst, pending, leader,
                             last_decision, more)
}

def receive_2a[A](i: Nat.nat, b: Nat.nat, v: cmd[A], l: Nat.nat,
                   s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, Unit](s)
    val bal: Option[Nat.nat] = ballot[A, Unit](s);
    (if (Optiona.equal_optiona[Nat.nat](bal, Some[Nat.nat](b)))
      (twobs_update[A, Unit](((_: FinFun.finfun[Nat.nat,
         FinFun.finfun[Nat.nat, List[Nat.nat]]])
                                =>
                               FinFun.finfun_update_code[Nat.nat,
                  FinFun.finfun[Nat.nat,
                                 List[Nat.nat]]](twobs[A, Unit](s), i,
          FinFun.finfun_update[Nat.nat,
                                List[Nat.nat]](FinFun.finfun_const[List[Nat.nat],
                            Nat.nat](Nil),
        Optiona.the[Nat.nat](bal), List(a)))),
                              vote_update[A,
   Unit](((_: FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
           FinFun.finfun_update_code[Nat.nat,
                                      Option[cmd[A]]](vote[A, Unit](s), i,
               Some[cmd[A]](v))),
          s)),
        send_all[A, Unit, A](s, a, Phase2b[A](i, b, a, v)))
      else (s, FSet.bot_fset[packet[A]]))
  }

def last_decision_update[A, B](last_decisiona:
                                 Option[Nat.nat] => Option[Nat.nat],
                                x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (last_decisiona, x1) match {
  case (last_decisiona,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobs, decided, next_inst, pending, leader,
                             last_decisiona(last_decision), more)
}

def decided_update[A, B](decideda:
                           (FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
                             FinFun.finfun[Nat.nat, Option[cmd[A]]],
                          x1: acc_state_ext[A, B]):
      acc_state_ext[A, B]
  =
  (decideda, x1) match {
  case (decideda,
         acc_state_exta(id, acceptors, ballot, vote, last_ballot, onebs, twobs,
                         decided, next_inst, pending, leader, last_decision,
                         more))
    => acc_state_exta[A, B](id, acceptors, ballot, vote, last_ballot, onebs,
                             twobs, decideda(decided), next_inst, pending,
                             leader, last_decision, more)
}

def update_decided[A, B](s: acc_state_ext[A, B], i: Nat.nat, v: cmd[A]):
      acc_state_ext[A, B]
  =
  last_decision_update[A, B](((_: Option[Nat.nat]) => Some[Nat.nat](i)),
                              decided_update[A,
      B](((_: FinFun.finfun[Nat.nat, Option[cmd[A]]]) =>
           FinFun.finfun_update_code[Nat.nat,
                                      Option[cmd[A]]](decided[A, B](s), i,
               Some[cmd[A]](v))),
          s))

def update_twobs[A, B](s: acc_state_ext[A, B], i: Nat.nat, b: Nat.nat,
                        newa: List[Nat.nat]):
      acc_state_ext[A, B]
  =
  twobs_update[A, B](((_: FinFun.finfun[Nat.nat,
 FinFun.finfun[Nat.nat, List[Nat.nat]]])
                        =>
                       FinFun.finfun_update_code[Nat.nat,
          FinFun.finfun[Nat.nat,
                         List[Nat.nat]]](twobs[A, B](s), i,
  FinFun.finfun_update[Nat.nat,
                        List[Nat.nat]](FinFun.finfun_apply[Nat.nat,
                    FinFun.finfun[Nat.nat, List[Nat.nat]]](twobs[A, B](s), i),
b, newa))),
                      s)

def receive_2b[A](i: Nat.nat, b: Nat.nat, a2: Nat.nat, v: cmd[A],
                   s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    id[A, Unit](s);
    (if (true)
      {
        val new_twobsa: List[Nat.nat] = new_twobs[A, Unit](s, i, b, a2)
        val s2: acc_state_ext[A, Unit] =
          update_twobs[A, Unit](s, i, b, new_twobsa);
        (if (Nat.less_nat(nr[A, Unit](s),
                           Nat.times_nat(Nat.nat_of_integer(BigInt(2)),
  Set.size_list[Nat.nat].apply(new_twobsa))))
          (update_decided[A, Unit](s2, i, v), FSet.bot_fset[packet[A]])
          else (s2, FSet.bot_fset[packet[A]]))
      }
      else (s, FSet.bot_fset[packet[A]]))
  }

def receive_fwd[A](v: A, s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  {
    val a: Nat.nat = id[A, Unit](s);
    (if (Nat.equal_nata(leader_of_bal[A, Unit](s, ballot[A, Unit](s)), a))
      do_2a[A, Unit](s, Cmd[A](v)) else (s, FSet.bot_fset[packet[A]]))
  }

def process_msg[A : HOL.equal](x0: msg[A], s: acc_state_ext[A, Unit]):
      (acc_state_ext[A, Unit], FSet.fset[packet[A]])
  =
  (x0, s) match {
  case (Phase1a(l, b), s) => receive_1a[A](l, b, s)
  case (Phase1b(lvs, b, a), s) => receive_1b[A](lvs, b, a, s)
  case (Phase2a(i, b, cm, l), s) => receive_2a[A](i, b, cm, l, s)
  case (Phase2b(i, b, a, cm), s) => receive_2b[A](i, b, a, cm, s)
  case (Vote(i, cm), s) => sys.error("undefined")
  case (Fwd(v), s) => receive_fwd[A](v, s)
}

def init_acc_state[A](n: Nat.nat, a: Nat.nat): acc_state_ext[A, Unit] =
  acc_state_exta[A, Unit](a, accs(n), None,
                           FinFun.finfun_const[Option[cmd[A]], Nat.nat](None),
                           FinFun.finfun_const[Option[Nat.nat], Nat.nat](None),
                           FinFun.finfun_const[FinFun.finfun[Nat.nat,
                      List[(Nat.nat, Option[(cmd[A], Nat.nat)])]],
        Nat.nat](FinFun.finfun_const[List[(Nat.nat, Option[(cmd[A], Nat.nat)])],
                                      Nat.nat](Nil)),
                           FinFun.finfun_const[FinFun.finfun[Nat.nat,
                      List[Nat.nat]],
        Nat.nat](FinFun.finfun_const[List[Nat.nat], Nat.nat](Nil)),
                           FinFun.finfun_const[Option[cmd[A]], Nat.nat](None),
                           Nat.one_nat,
                           FinFun.finfun_const[Option[cmd[A]], Nat.nat](None),
                           false, None, ())

def serialize_finfun[A : Cardinality.card_UNIV : HOL.equal : Orderings.linorder,
                      B : HOL.equal](ff: FinFun.finfun[A, B]):
      List[(A, B)]
  =
  Set.fold[A, List[(A, B)]](((k: A) =>
                              ((a: List[(A, B)]) =>
                                (k, FinFun.finfun_apply[A, B](ff, k)) :: a)),
                             FinFun.finfun_to_list[A, B](ff), Nil)

def get_next_instance[A, B](s: acc_state_ext[A, B]): Nat.nat =
  next_inst[A, B](s)

def deserialize_finfun[A, B](l: List[(A, Option[B])]):
      FinFun.finfun[A, Option[B]]
  =
  (Set.foldr[(A, Option[B]),
              FinFun.finfun[A, Option[B]]](((kv: (A, Option[B])) =>
     (r: FinFun.finfun[A, Option[B]]) =>
     FinFun.finfun_update_code[A, Option[B]](r,
      Product_Type.fst[A, Option[B]](kv), Product_Type.snd[A, Option[B]](kv))),
    l)).apply(FinFun.finfun_const[Option[B], A](None))

} /* object MultiPaxos4 */
