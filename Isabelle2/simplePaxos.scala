object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def fun_upd[A : HOL.equal, B](f: A => B, a: A, b: B): A => B =
  ((x: A) => (if (HOL.eq[A](x, a)) b else f(x)))

} /* object Fun */

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

object Groups {

trait one[A] {
  val `Groups.one`: A
}
def one[A](implicit A: one[A]): A = A.`Groups.one`

trait minus[A] {
  val `Groups.minus`: (A, A) => A
}
def minus[A](a: A, b: A)(implicit A: minus[A]): A = A.`Groups.minus`(a, b)

} /* object Groups */

object Code_Numeral {

implicit def ord_integer: Orderings.ord[BigInt] = new Orderings.ord[BigInt] {
  val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
  val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
}

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

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

def mod_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.snd[BigInt, BigInt](divmod_integer(k, l))

def divide_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.fst[BigInt, BigInt](divmod_integer(k, l))

} /* object Code_Numeral */

object Nat {

import /*implicits*/ Code_Numeral.ord_integer

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

implicit def equal_nat: HOL.equal[nat] = new HOL.equal[nat] {
  val `HOL.equal` = (a: nat, b: nat) => equal_nata(a, b)
}

def one_nata: nat = Nata(BigInt(1))

implicit def one_nat: Groups.one[nat] = new Groups.one[nat] {
  val `Groups.one` = one_nata
}

def minus_nata(m: nat, n: nat): nat =
  Nata(Orderings.max[BigInt](BigInt(0),
                              Code_Numeral.integer_of_nat(m) -
                                Code_Numeral.integer_of_nat(n)))

implicit def minus_nat: Groups.minus[nat] = new Groups.minus[nat] {
  val `Groups.minus` = (a: nat, b: nat) => minus_nata(a, b)
}

def less_eq_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

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

def plus_nat(m: nat, n: nat): nat =
  Nata(Code_Numeral.integer_of_nat(m) + Code_Numeral.integer_of_nat(n))

def Suc(n: nat): nat = plus_nat(n, one_nata)

def zero_nat: nat = Nata(BigInt(0))

def times_nat(m: nat, n: nat): nat =
  Nata(Code_Numeral.integer_of_nat(m) * Code_Numeral.integer_of_nat(n))

} /* object Nat */

object Lista {

def nth[A](x0: List[A], n: Nat.nat): A = (x0, n) match {
  case (x :: xs, n) =>
    (if (Nat.equal_nata(n, Nat.zero_nat)) x
      else nth[A](xs, Nat.minus_nata(n, Nat.one_nata)))
}

def upt(i: Nat.nat, j: Nat.nat): List[Nat.nat] =
  (if (Nat.less_nat(i, j)) i :: upt(Nat.Suc(i), j) else Nil)

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x :: xs => false
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x :: xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => HOL.eq[A](x, y) || member[A](xs, y)
}

def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (member[A](xs, x)) xs else x :: xs)

def hd[A](x0: List[A]): A = x0 match {
  case x21 :: x22 => x21
}

def remdups[A : HOL.equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (member[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
  case (n, Nil) => n
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)),
                      xs)).apply(Nil)

def size_list[A]: (List[A]) => Nat.nat =
  ((a: List[A]) => gen_length[A](Nat.zero_nat, a))

def equal_list[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) =>
    HOL.eq[A](x21, y21) && equal_list[A](x22, y22)
  case (Nil, Nil) => true
}

} /* object Lista */

object Log {

import /*implicits*/ Product_Type.equal_prod, Nat.linorder_nat, Nat.equal_nat

def largestinseq_carry[A](x: Nat.nat, xa1: List[(Nat.nat, A)]): Nat.nat =
  (x, xa1) match {
  case (x, Nil) => x
  case (x, (y, z) :: xs) =>
    (if (Nat.equal_nata(y, Nat.plus_nat(x, Nat.one_nata)))
      largestinseq_carry[A](y, xs) else x)
}

def largestinseq[A](xs: List[(Nat.nat, A)]): Nat.nat =
  largestinseq_carry[A](Nat.zero_nat, xs)

def largestprefix[A](xs: List[(Nat.nat, A)]): List[(Nat.nat, A)] =
  Lista.filter[(Nat.nat,
                 A)](((a: (Nat.nat, A)) =>
                       {
                         val (y, _): (Nat.nat, A) = a;
                         Nat.less_eq_nat(y, largestinseq[A](xs))
                       }),
                      xs)

def distinct_Sorted_Insert[A : HOL.equal](x: (Nat.nat, A),
   xs: List[(Nat.nat, A)]):
      List[(Nat.nat, A)]
  =
  (if (! (Lista.member[(Nat.nat, A)](xs, x)))
    Lista.sort_key[(Nat.nat, A),
                    Nat.nat](((a: (Nat.nat, A)) =>
                               {
                                 val (xa, _): (Nat.nat, A) = a;
                                 xa
                               }),
                              x :: xs)
    else xs)

} /* object Log */

object Set {

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
}

def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](Lista.removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](Lista.insert[A](x, xs))
}

def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (Lista.member[A](xs, x))
  case (x, seta(xs)) => Lista.member[A](xs, x)
}

def bot_set[A]: set[A] = seta[A](Nil)

def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](Lista.filter[A](((x: A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
}

} /* object Set */

object Divides {

def mod_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.mod_integer(Code_Numeral.integer_of_nat(m),
                                     Code_Numeral.integer_of_nat(n)))

def divide_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.divide_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

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

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.seta(xs) => Lista.size_list[A].apply(Lista.remdups[A](xs))
}

} /* object Finite_Set */

object Lattices_Big {

def Max[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta(x :: xs) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
}

} /* object Lattices_Big */

object MultiPaxos {

import /*implicits*/ Product_Type.equal_prod, Optiona.equal_option,
  Nat.linorder_nat, Nat.minus_nat, Nat.one_nat, Nat.equal_nat

abstract sealed class msg[A, B, C]
final case class Phase1a[B, C, A](a: B, b: C) extends msg[A, B, C]
final case class Phase1b[A, C, B](a: List[Option[(A, C)]], b: C, c: B) extends
  msg[A, B, C]
final case class Phase2a[C, A, B](a: Nat.nat, b: C, c: A, d: B) extends
  msg[A, B, C]
final case class Phase2b[C, B, A](a: Nat.nat, b: C, c: B) extends msg[A, B, C]
final case class Vote[A, B, C](a: Nat.nat, b: A) extends msg[A, B, C]
final case class Fwd[A, B, C](a: A) extends msg[A, B, C]

def equal_msg[A : HOL.equal, B : HOL.equal,
               C : HOL.equal](x0: msg[A, B, C], x1: msg[A, B, C]):
      Boolean
  =
  (x0, x1) match {
  case (Vote(x51, x52), Fwd(x6)) => false
  case (Fwd(x6), Vote(x51, x52)) => false
  case (Phase2b(x41, x42, x43), Fwd(x6)) => false
  case (Fwd(x6), Phase2b(x41, x42, x43)) => false
  case (Phase2b(x41, x42, x43), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase2b(x41, x42, x43)) => false
  case (Phase2a(x31, x32, x33, x34), Fwd(x6)) => false
  case (Fwd(x6), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase2b(x41, x42, x43)) => false
  case (Phase2b(x41, x42, x43), Phase2a(x31, x32, x33, x34)) => false
  case (Phase1b(x21, x22, x23), Fwd(x6)) => false
  case (Fwd(x6), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase2b(x41, x42, x43)) => false
  case (Phase2b(x41, x42, x43), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase1b(x21, x22, x23)) => false
  case (Phase1a(x11, x12), Fwd(x6)) => false
  case (Fwd(x6), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Vote(x51, x52)) => false
  case (Vote(x51, x52), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase2b(x41, x42, x43)) => false
  case (Phase2b(x41, x42, x43), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase2a(x31, x32, x33, x34)) => false
  case (Phase2a(x31, x32, x33, x34), Phase1a(x11, x12)) => false
  case (Phase1a(x11, x12), Phase1b(x21, x22, x23)) => false
  case (Phase1b(x21, x22, x23), Phase1a(x11, x12)) => false
  case (Fwd(x6), Fwd(y6)) => HOL.eq[A](x6, y6)
  case (Vote(x51, x52), Vote(y51, y52)) =>
    Nat.equal_nata(x51, y51) && HOL.eq[A](x52, y52)
  case (Phase2b(x41, x42, x43), Phase2b(y41, y42, y43)) =>
    Nat.equal_nata(x41, y41) && (HOL.eq[C](x42, y42) && HOL.eq[B](x43, y43))
  case (Phase2a(x31, x32, x33, x34), Phase2a(y31, y32, y33, y34)) =>
    Nat.equal_nata(x31, y31) &&
      (HOL.eq[C](x32, y32) && (HOL.eq[A](x33, y33) && HOL.eq[B](x34, y34)))
  case (Phase1b(x21, x22, x23), Phase1b(y21, y22, y23)) =>
    Lista.equal_list[Option[(A, C)]](x21, y21) &&
      (HOL.eq[C](x22, y22) && HOL.eq[B](x23, y23))
  case (Phase1a(x11, x12), Phase1a(y11, y12)) =>
    HOL.eq[B](x11, y11) && HOL.eq[C](x12, y12)
}

abstract sealed class packet[A, B, C]
final case class Packet[B, A, C](a: B, b: B, c: msg[A, B, C]) extends
  packet[A, B, C]

def equal_packeta[A : HOL.equal, B : HOL.equal,
                   C : HOL.equal](x0: packet[A, B, C], x1: packet[A, B, C]):
      Boolean
  =
  (x0, x1) match {
  case (Packet(x1, x2, x3), Packet(y1, y2, y3)) =>
    HOL.eq[B](x1, y1) && (HOL.eq[B](x2, y2) && equal_msg[A, B, C](x3, y3))
}

implicit def
  equal_packet[A : HOL.equal, B : HOL.equal, C : HOL.equal]:
    HOL.equal[packet[A, B, C]]
  = new HOL.equal[packet[A, B, C]] {
  val `HOL.equal` = (a: packet[A, B, C], b: packet[A, B, C]) =>
    equal_packeta[A, B, C](a, b)
}

abstract sealed class mp_state_ext[A, B, C, D]
final case class
  mp_state_exta[B, C, A,
                 D](a: Set.set[B], b: B => Option[C],
                     c: B => Nat.nat => Option[A], d: B => Nat.nat => Option[C],
                     e: B => C => List[List[(B, Option[(A, C)])]],
                     f: B => Nat.nat => C => List[B],
                     g: B => Nat.nat => Option[A], h: B => Nat.nat,
                     i: B => Nat.nat => Option[A], j: B => List[(Nat.nat, A)],
                     k: D)
  extends mp_state_ext[A, B, C, D]

def acceptors[A, B, C, D](x0: mp_state_ext[A, B, C, D]): Set.set[B] = x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => acceptors
}

def nr[A, B : HOL.equal, C, D](s: mp_state_ext[A, B, C, D]): Nat.nat =
  Finite_Set.card[B](acceptors[A, B, C, D](s))

def highest_instance_update[A, B, C,
                             D](highest_instancea:
                                  (A => Nat.nat) => A => Nat.nat,
                                 x1: mp_state_ext[B, A, C, D]):
      mp_state_ext[B, A, C, D]
  =
  (highest_instancea, x1) match {
  case (highest_instancea,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, C, B,
                      D](acceptors, ballot, vote, last_ballot, onebs, twobs,
                          decided, highest_instancea(highest_instance), pending,
                          log, more)
}

def highest_instance[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => Nat.nat =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => highest_instance
}

def pending_update[A, B, C,
                    D](pendinga:
                         (A => Nat.nat => Option[B]) =>
                           A => Nat.nat => Option[B],
                        x1: mp_state_ext[B, A, C, D]):
      mp_state_ext[B, A, C, D]
  =
  (pendinga, x1) match {
  case (pendinga,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, C, B,
                      D](acceptors, ballot, vote, last_ballot, onebs, twobs,
                          decided, highest_instance, pendinga(pending), log,
                          more)
}

def pending[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => Nat.nat => Option[A]
  =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => pending
}

def ballot[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => Option[C] = x0 match
  {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => ballot
}

def send_all[A, B, C, D, E,
              F](s: mp_state_ext[A, B, C, D], sendr: B, m: msg[E, B, F]):
      Set.set[packet[E, B, F]]
  =
  Set.image[B, packet[E, B,
                       F]](((a2: B) => Packet[B, E, F](sendr, a2, m)),
                            acceptors[A, B, C, D](s))

def do_2a[A, B : HOL.equal, C, D](s: mp_state_ext[A, B, C, D], a: B, v: A):
      (mp_state_ext[A, B, C, D], Set.set[packet[A, B, C]])
  =
  {
    val inst: Nat.nat =
      Nat.plus_nat((highest_instance[A, B, C, D](s)).apply(a), Nat.one_nata)
    val msg: msg[A, B, C] =
      Phase2a[C, A,
               B](inst, Optiona.the[C]((ballot[A, B, C, D](s)).apply(a)), v, a)
    val new_state: mp_state_ext[A, B, C, D] =
      pending_update[B, A, C,
                      D](((_: B => Nat.nat => Option[A]) =>
                           Fun.fun_upd[B,
Nat.nat =>
  Option[A]](pending[A, B, C, D](s), a,
              Fun.fun_upd[Nat.nat,
                           Option[A]]((pending[A, B, C, D](s)).apply(a), inst,
                                       Some[A](v)))),
                          highest_instance_update[B, A, C,
           D](((_: B => Nat.nat) =>
                Fun.fun_upd[B, Nat.nat](highest_instance[A, B, C, D](s), a,
 inst)),
               s));
    (new_state, send_all[A, B, C, D, A, C](s, a, msg))
  }

def leader[A, B : HOL.equal, C,
            D](s: mp_state_ext[A, B, C, D], b: Option[Nat.nat]):
      Nat.nat
  =
  (b match {
     case None => Nat.zero_nat
     case Some(ba) => Divides.mod_nat(ba, nr[A, B, C, D](s))
   })

def suc_bal(a: Nat.nat, b: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.plus_nat(Nat.times_nat(Nat.plus_nat(Divides.divide_nat(b, n),
   Nat.one_nata),
                              n),
                a)

def nx_bal(a: Nat.nat, x1: Option[Nat.nat], n: Nat.nat): Nat.nat = (a, x1, n)
  match {
  case (a, None, n) => suc_bal(a, Nat.zero_nat, n)
  case (a, Some(b), n) => suc_bal(a, b, n)
}

def max_opt[A](ao: Option[A], bo: Option[A], f: A => A => A): Option[A] =
  (ao match {
     case None => (bo match {
                     case None => None
                     case Some(a) => Some[A](a)
                   })
     case Some(a) => (bo match {
                        case None => Some[A](a)
                        case Some(b) => Some[A]((f(a))(b))
                      })
   })

def propose[A : HOL.equal,
             B](a: Nat.nat, v: A, s: mp_state_ext[A, Nat.nat, Nat.nat, B]):
      (mp_state_ext[A, Nat.nat, Nat.nat, B],
        Set.set[packet[A, Nat.nat, Nat.nat]])
  =
  (if (Nat.equal_nata(leader[A, Nat.nat, Nat.nat,
                              B](s, (ballot[A, Nat.nat, Nat.nat,
     B](s)).apply(a)),
                       a))
    do_2a[A, Nat.nat, Nat.nat, B](s, a, v)
    else (s, Set.insert[packet[A, Nat.nat,
                                Nat.nat]](Packet[Nat.nat, A,
          Nat.nat](a, leader[A, Nat.nat, Nat.nat,
                              B](s, (ballot[A, Nat.nat, Nat.nat,
     B](s)).apply(a)),
                    Fwd[A, Nat.nat, Nat.nat](v)),
   Set.bot_set[packet[A, Nat.nat, Nat.nat]])))

def send_1a[A, B, C](a: Nat.nat, s: mp_state_ext[A, Nat.nat, Nat.nat, B]):
      (mp_state_ext[A, Nat.nat, Nat.nat, B],
        Set.set[packet[C, Nat.nat, Nat.nat]])
  =
  {
    val b: Nat.nat =
      nx_bal(a, (ballot[A, Nat.nat, Nat.nat, B](s)).apply(a),
              Finite_Set.card[Nat.nat](acceptors[A, Nat.nat, Nat.nat, B](s)))
    val msg_1a: msg[C, Nat.nat, Nat.nat] = Phase1a[Nat.nat, Nat.nat, C](a, b);
    (s, Set.image[Nat.nat,
                   packet[C, Nat.nat,
                           Nat.nat]](((a2: Nat.nat) =>
                                       Packet[Nat.nat, C,
       Nat.nat](a, a2, msg_1a)),
                                      acceptors[A, Nat.nat, Nat.nat, B](s)))
  }

def add_index[A, B : Groups.minus : Groups.one](x0: List[A], uu: B):
      List[(A, B)]
  =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (x :: xs, n) =>
    (x, n) :: add_index[A, B](xs, Groups.minus[B](n, Groups.one[B]))
}

def fold_union[A : HOL.equal](l: List[Set.set[A]]): Set.set[A] =
  Lista.fold[Set.set[A],
              Set.set[A]](((a: Set.set[A]) => (b: Set.set[A]) =>
                            Set.sup_set[A](a, b)),
                           l, Set.bot_set[A])

def init_state[A, B, C](accs: Set.set[A]): mp_state_ext[B, A, C, Unit] =
  mp_state_exta[A, C, B,
                 Unit](accs, ((_: A) => None), ((_: A) => (_: Nat.nat) => None),
                        ((_: A) => (_: Nat.nat) => None),
                        ((_: A) => (_: C) => Nil),
                        ((_: A) => (_: Nat.nat) => (_: C) => Nil),
                        ((_: A) => (_: Nat.nat) => None),
                        ((_: A) => Nat.zero_nat),
                        ((_: A) => (_: Nat.nat) => None), ((_: A) => Nil), ())

def ballot_update[A, B, C,
                   D](ballota: (A => Option[B]) => A => Option[B],
                       x1: mp_state_ext[C, A, B, D]):
      mp_state_ext[C, A, B, D]
  =
  (ballota, x1) match {
  case (ballota,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, B, C,
                      D](acceptors, ballota(ballot), vote, last_ballot, onebs,
                          twobs, decided, highest_instance, pending, log, more)
}

def last_ballot[A, B, C, D](x0: mp_state_ext[A, B, C, D]):
      B => Nat.nat => Option[C]
  =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => last_ballot
}

def vote[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => Nat.nat => Option[A] =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => vote
}

def receive_1a[A, B : HOL.equal,
                C](a: Nat.nat, x1: msg[A, Nat.nat, Nat.nat],
                    s: mp_state_ext[B, Nat.nat, Nat.nat, C]):
      (mp_state_ext[B, Nat.nat, Nat.nat, C],
        Set.set[packet[B, Nat.nat, Nat.nat]])
  =
  (a, x1, s) match {
  case (a, Phase1a(l, b), s) =>
    {
      val bal: Option[Nat.nat] = (ballot[B, Nat.nat, Nat.nat, C](s)).apply(a);
      (if (Optiona.is_none[Nat.nat](bal) ||
             Nat.less_nat(Optiona.the[Nat.nat](bal), b))
        {
          val is: List[Nat.nat] =
            (bal match {
               case None => Nil
               case Some(ba) => Lista.upt(Nat.zero_nat, Nat.Suc(ba))
             })
          val get_vote: Nat.nat => Option[(B, Nat.nat)] =
            ((i: Nat.nat) =>
              Optiona.bind[B, (B, Nat.nat)]((vote[B, Nat.nat, Nat.nat,
           C](s)).apply(i).apply(a),
     ((v: B) =>
       Optiona.bind[Nat.nat,
                     (B, Nat.nat)]((last_ballot[B, Nat.nat, Nat.nat,
         C](s)).apply(a).apply(i),
                                    ((ba: Nat.nat) =>
                                      Some[(B, Nat.nat)]((v, ba)))))))
          val votes: List[Option[(B, Nat.nat)]] =
            Lista.map[Nat.nat, Option[(B, Nat.nat)]](get_vote, is)
          val msg_1b: msg[B, Nat.nat, Nat.nat] =
            Phase1b[B, Nat.nat, Nat.nat](votes, b, a)
          val packet: packet[B, Nat.nat, Nat.nat] =
            Packet[Nat.nat, B, Nat.nat](a, l, msg_1b)
          val state: mp_state_ext[B, Nat.nat, Nat.nat, C] =
            ballot_update[Nat.nat, Nat.nat, B,
                           C](((_: Nat.nat => Option[Nat.nat]) =>
                                Fun.fun_upd[Nat.nat,
     Option[Nat.nat]](ballot[B, Nat.nat, Nat.nat, C](s), a, Some[Nat.nat](b))),
                               s);
          (state,
            Set.insert[packet[B, Nat.nat,
                               Nat.nat]](packet,
  Set.bot_set[packet[B, Nat.nat, Nat.nat]]))
        }
        else (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]]))
    }
  case (a, Phase1b(v, va, vb), s) =>
    (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]])
  case (a, Phase2a(v, va, vb, vc), s) =>
    (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]])
  case (a, Phase2b(v, va, vb), s) =>
    (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]])
  case (a, Vote(v, va), s) => (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]])
  case (a, Fwd(v), s) => (s, Set.bot_set[packet[B, Nat.nat, Nat.nat]])
}

def onebs[A, B, C, D](x0: mp_state_ext[A, B, C, D]):
      B => C => List[List[(B, Option[(A, C)])]]
  =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => onebs
}

def highest_voted[A, B, C : Orderings.ord](l: List[(A, Option[(B, C)])]):
      Option[B]
  =
  {
    val filtered: List[Option[(B, C)]] =
      Lista.map[(A, Option[(B, C)]),
                 Option[(B, C)]](((a: (A, Option[(B, C)])) =>
                                   Product_Type.snd[A, Option[(B, C)]](a)),
                                  l)
    val max_pair: ((B, C)) => ((B, C)) => (B, C) =
      ((x: (B, C)) => (y: (B, C)) =>
        (if (Orderings.less[C](Product_Type.snd[B, C](y),
                                Product_Type.snd[B, C](x)))
          x else y))
    val max_option: Option[(B, C)] => Option[(B, C)] => Option[(B, C)] =
      ((x: Option[(B, C)]) => (y: Option[(B, C)]) =>
        max_opt[(B, C)](x, y, max_pair))
    val init_val: Option[(B, C)] =
      (if (Lista.nulla[Option[(B, C)]](filtered)) None
        else Lista.hd[Option[(B, C)]](filtered));
    (Lista.fold[Option[(B, C)], Option[(B, C)]](max_option, filtered, init_val)
       match {
       case None => None
       case Some((v, _)) => Some[B](v)
     })
  }

def onebs_update[A, B, C,
                  D](onebsa:
                       (A => B => List[List[(A, Option[(C, B)])]]) =>
                         A => B => List[List[(A, Option[(C, B)])]],
                      x1: mp_state_ext[C, A, B, D]):
      mp_state_ext[C, A, B, D]
  =
  (onebsa, x1) match {
  case (onebsa,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, B, C,
                      D](acceptors, ballot, vote, last_ballot, onebsa(onebs),
                          twobs, decided, highest_instance, pending, log, more)
}

def update_onebs[A, B : HOL.equal, C : HOL.equal, D,
                  E](s: mp_state_ext[A, B, C, D], a: B, bal: C, a2: E,
                      last_vs: List[Option[(A, C)]]):
      mp_state_ext[A, B, C, D]
  =
  {
    val max_is: Nat.nat =
      Lattices_Big.Max[Nat.nat](Set.insert[Nat.nat](Lista.size_list[Option[(A,
                                     C)]].apply(last_vs),
             Set.insert[Nat.nat](Lista.size_list[List[(B,
                Option[(A, C)])]].apply((onebs[A, B, C,
        D](s)).apply(a).apply(bal)),
                                  Set.bot_set[Nat.nat])))
    val is: List[Nat.nat] = Lista.upt(Nat.one_nata, Nat.Suc(max_is))
    val curr_onebs: List[List[(B, Option[(A, C)])]] =
      (onebs[A, B, C, D](s)).apply(a).apply(bal)
    val at_i: Nat.nat => List[(B, Option[(A, C)])] =
      ((i: Nat.nat) =>
        (if (Nat.less_eq_nat(i, Lista.size_list[List[(B,
               Option[(A, C)])]].apply(curr_onebs)))
          (if (Nat.less_eq_nat(i, Lista.size_list[Option[(A,
                   C)]].apply(last_vs)))
            (a, Lista.nth[Option[(A, C)]](last_vs,
   Nat.minus_nata(i, Nat.one_nata))) ::
              Lista.nth[List[(B, Option[(A,
  C)])]](curr_onebs, Nat.minus_nata(i, Nat.one_nata))
            else Lista.nth[List[(B, Option[(A,
     C)])]](curr_onebs, Nat.minus_nata(i, Nat.one_nata)))
          else List((a, Lista.nth[Option[(A,
   C)]](last_vs, Nat.minus_nata(i, Nat.one_nata))))))
    val newa: List[List[(B, Option[(A, C)])]] =
      Lista.map[Nat.nat, List[(B, Option[(A, C)])]](at_i, is);
    onebs_update[B, C, A,
                  D](((_: B => C => List[List[(B, Option[(A, C)])]]) =>
                       Fun.fun_upd[B, C =>
List[List[(B, Option[(A, C)])]]](onebs[A, B, C, D](s), a,
                                  Fun.fun_upd[C,
       List[List[(B, Option[(A, C)])]]]((onebs[A, B, C, D](s)).apply(a), bal,
 newa))),
                      s)
  }

def receive_1b[A : HOL.equal, B : HOL.equal, C, D : HOL.equal : Orderings.ord,
                E](a: A, x1: msg[B, C, D], s: mp_state_ext[B, A, D, E]):
      (mp_state_ext[B, A, D, E], Set.set[packet[B, A, D]])
  =
  (a, x1, s) match {
  case (a, Phase1b(last_vs, new_bal, a2), s) =>
    (if (HOL.eq[D](new_bal, Optiona.the[D]((ballot[B, A, D, E](s)).apply(a))))
      {
        val new_state: mp_state_ext[B, A, D, E] =
          update_onebs[B, A, D, E, C](s, a, new_bal, a2, last_vs)
        val onebsa: List[List[(A, Option[(B, D)])]] =
          (onebs[B, A, D, E](new_state)).apply(a).apply(new_bal)
        val quorum_received: Boolean =
          Nat.less_nat(nr[B, A, D, E](s),
                        Nat.times_nat(Code_Numeral.nat_of_integer(BigInt(2)),
                                       Lista.size_list[List[(A,
                      Option[(B, D)])]].apply(onebsa)))
        val aa: Set.set[packet[B, A, D]] =
          (if (quorum_received)
            {
              val received: List[List[(A, Option[(B, D)])]] =
                (onebs[B, A, D, E](new_state)).apply(a).apply(new_bal)
              val safe: List[(Option[B], Nat.nat)] =
                add_index[Option[B],
                           Nat.nat](Lista.map[List[(A, Option[(B, D)])],
       Option[B]](((aa: List[(A, Option[(B, D)])]) =>
                    highest_voted[A, B, D](aa)),
                   received),
                                     Nat.one_nata)
              val msg: ((Option[B], Nat.nat)) => Option[msg[B, A, D]] =
                ((b: (Option[B], Nat.nat)) =>
                  (b match {
                     case (None, _) => None
                     case (Some(v), i) =>
                       Some[msg[B, A, D]](Phase2a[D, B, A](i, new_bal, v, a))
                   }))
              val aa: List[Set.set[packet[B, A, D]]] =
                Lista.map[(Option[B], Nat.nat),
                           Set.set[packet[B, A,
   D]]](((x: (Option[B], Nat.nat)) =>
          (msg(x) match {
             case None => Set.bot_set[packet[B, A, D]]
             case Some(b) => send_all[B, A, D, E, B, D](s, a, b)
           })),
         safe);
              fold_union[packet[B, A, D]](aa)
            }
            else Set.bot_set[packet[B, A, D]]);
        (new_state, aa)
      }
      else (s, Set.bot_set[packet[B, A, D]]))
  case (a, Phase1a(v, va), s) => (s, Set.bot_set[packet[B, A, D]])
  case (a, Phase2a(v, va, vb, vc), s) => (s, Set.bot_set[packet[B, A, D]])
  case (a, Phase2b(v, va, vb), s) => (s, Set.bot_set[packet[B, A, D]])
  case (a, Vote(v, va), s) => (s, Set.bot_set[packet[B, A, D]])
  case (a, Fwd(v), s) => (s, Set.bot_set[packet[B, A, D]])
}

def vote_update[A, B, C,
                 D](votea:
                      (A => Nat.nat => Option[B]) => A => Nat.nat => Option[B],
                     x1: mp_state_ext[B, A, C, D]):
      mp_state_ext[B, A, C, D]
  =
  (votea, x1) match {
  case (votea,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, C, B,
                      D](acceptors, ballot, votea(vote), last_ballot, onebs,
                          twobs, decided, highest_instance, pending, log, more)
}

def receive_2a[A : HOL.equal, B, C : HOL.equal, D,
                E : HOL.equal](a: A, x1: msg[B, A, C],
                                s: mp_state_ext[B, A, C, D]):
      (mp_state_ext[B, A, C, D], Set.set[packet[E, A, C]])
  =
  (a, x1, s) match {
  case (a, Phase2a(i, b, v, l), s) =>
    {
      val bal: Option[C] = (ballot[B, A, C, D](s)).apply(a);
      (if (Optiona.equal_optiona[C](bal, Some[C](b)))
        (vote_update[A, B, C,
                      D](((_: A => Nat.nat => Option[B]) =>
                           Fun.fun_upd[A,
Nat.nat =>
  Option[B]](vote[B, A, C, D](s), a,
              Fun.fun_upd[Nat.nat,
                           Option[B]]((vote[B, A, C, D](s)).apply(a), i,
                                       Some[B](v)))),
                          s),
          Set.insert[packet[E, A,
                             C]](Packet[A, E,
 C](a, l, Phase2b[C, A, E](i, b, a)),
                                  Set.bot_set[packet[E, A, C]]))
        else (s, Set.bot_set[packet[E, A, C]]))
    }
  case (a, Phase1a(v, va), s) => (s, Set.bot_set[packet[E, A, C]])
  case (a, Phase1b(v, va, vb), s) => (s, Set.bot_set[packet[E, A, C]])
  case (a, Phase2b(v, va, vb), s) => (s, Set.bot_set[packet[E, A, C]])
  case (a, Vote(v, va), s) => (s, Set.bot_set[packet[E, A, C]])
  case (a, Fwd(v), s) => (s, Set.bot_set[packet[E, A, C]])
}

def decided_update[A, B, C,
                    D](decideda:
                         (A => Nat.nat => Option[B]) =>
                           A => Nat.nat => Option[B],
                        x1: mp_state_ext[B, A, C, D]):
      mp_state_ext[B, A, C, D]
  =
  (decideda, x1) match {
  case (decideda,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, C, B,
                      D](acceptors, ballot, vote, last_ballot, onebs, twobs,
                          decideda(decided), highest_instance, pending, log,
                          more)
}

def twobs_update[A, B, C,
                  D](twobsa:
                       (A => Nat.nat => B => List[A]) =>
                         A => Nat.nat => B => List[A],
                      x1: mp_state_ext[C, A, B, D]):
      mp_state_ext[C, A, B, D]
  =
  (twobsa, x1) match {
  case (twobsa,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, B, C,
                      D](acceptors, ballot, vote, last_ballot, onebs,
                          twobsa(twobs), decided, highest_instance, pending,
                          log, more)
}

def log_update[A, B, C,
                D](loga: (A => List[(Nat.nat, B)]) => A => List[(Nat.nat, B)],
                    x1: mp_state_ext[B, A, C, D]):
      mp_state_ext[B, A, C, D]
  =
  (loga, x1) match {
  case (loga,
         mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                        decided, highest_instance, pending, log, more))
    => mp_state_exta[A, C, B,
                      D](acceptors, ballot, vote, last_ballot, onebs, twobs,
                          decided, highest_instance, pending, loga(log), more)
}

def decided[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => Nat.nat => Option[A]
  =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => decided
}

def twobs[A, B, C, D](x0: mp_state_ext[A, B, C, D]):
      B => Nat.nat => C => List[B]
  =
  x0 match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => twobs
}

def log[A, B, C, D](x0: mp_state_ext[A, B, C, D]): B => List[(Nat.nat, A)] = x0
  match {
  case mp_state_exta(acceptors, ballot, vote, last_ballot, onebs, twobs,
                      decided, highest_instance, pending, log, more)
    => log
}

def receive_2b[A : HOL.equal, B, C : HOL.equal, D : HOL.equal, E,
                F](a: A, x1: msg[B, A, C], s: mp_state_ext[D, A, C, E]):
      (mp_state_ext[D, A, C, E], Set.set[F])
  =
  (a, x1, s) match {
  case (a, Phase2b(i, b, a2), s) =>
    {
      val sa: mp_state_ext[D, A, C, E] =
        (if (Optiona.is_none[D]((decided[D, A, C, E](s)).apply(a).apply(i)))
          {
            val new_twobs: List[A] =
              a2 :: (twobs[D, A, C, E](s)).apply(a).apply(i).apply(b);
            (if (Nat.less_nat(Finite_Set.card[A](acceptors[D, A, C, E](s)),
                               Nat.times_nat(Code_Numeral.nat_of_integer(BigInt(2)),
      Lista.size_list[A].apply(new_twobs))))
              log_update[A, D, C,
                          E](((_: A => List[(Nat.nat, D)]) =>
                               Fun.fun_upd[A,
    List[(Nat.nat,
           D)]](log[D, A, C, E](s), a,
                 Log.distinct_Sorted_Insert[D]((i,
         Optiona.the[D]((pending[D, A, C, E](s)).apply(a).apply(i))),
        (log[D, A, C, E](s)).apply(a)))),
                              decided_update[A, D, C,
      E](((_: A => Nat.nat => Option[D]) =>
           Fun.fun_upd[A, Nat.nat =>
                            Option[D]](decided[D, A, C, E](s), a,
Fun.fun_upd[Nat.nat,
             Option[D]]((decided[D, A, C, E](s)).apply(a), i,
                         (pending[D, A, C, E](s)).apply(a).apply(i)))),
          twobs_update[A, C, D,
                        E](((_: A => Nat.nat => C => List[A]) =>
                             Fun.fun_upd[A,
  Nat.nat =>
    C => List[A]](twobs[D, A, C, E](s), a,
                   Fun.fun_upd[Nat.nat,
                                C => List[A]]((twobs[D, A, C, E](s)).apply(a),
       i, Fun.fun_upd[C, List[A]]((twobs[D, A, C, E](s)).apply(a).apply(i), b,
                                   new_twobs)))),
                            s)))
              else twobs_update[A, C, D,
                                 E](((_: A => Nat.nat => C => List[A]) =>
                                      Fun.fun_upd[A,
           Nat.nat =>
             C => List[A]](twobs[D, A, C, E](s), a,
                            Fun.fun_upd[Nat.nat,
 C => List[A]]((twobs[D, A, C, E](s)).apply(a), i,
                Fun.fun_upd[C, List[A]]((twobs[D, A, C,
        E](s)).apply(a).apply(i),
 b, new_twobs)))),
                                     s))
          }
          else s);
      (sa, Set.bot_set[F])
    }
  case (a, Phase1a(v, va), s) => (s, Set.bot_set[F])
  case (a, Phase1b(v, va, vb), s) => (s, Set.bot_set[F])
  case (a, Phase2a(v, va, vb, vc), s) => (s, Set.bot_set[F])
  case (a, Vote(v, va), s) => (s, Set.bot_set[F])
  case (a, Fwd(v), s) => (s, Set.bot_set[F])
}

def receive_fwd[A, B, C,
                 D](a: Nat.nat, x1: msg[A, B, C],
                     s: mp_state_ext[A, Nat.nat, Nat.nat, D]):
      (mp_state_ext[A, Nat.nat, Nat.nat, D],
        Set.set[packet[A, Nat.nat, Nat.nat]])
  =
  (a, x1, s) match {
  case (a, Fwd(v), s) =>
    (if (Nat.equal_nata(leader[A, Nat.nat, Nat.nat,
                                D](s, (ballot[A, Nat.nat, Nat.nat,
       D](s)).apply(a)),
                         a))
      do_2a[A, Nat.nat, Nat.nat, D](s, a, v)
      else (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]]))
  case (a, Phase1a(v, va), s) => (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]])
  case (a, Phase1b(v, va, vb), s) =>
    (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]])
  case (a, Phase2a(v, va, vb, vc), s) =>
    (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]])
  case (a, Phase2b(v, va, vb), s) =>
    (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]])
  case (a, Vote(v, va), s) => (s, Set.bot_set[packet[A, Nat.nat, Nat.nat]])
}

} /* object MultiPaxos */
