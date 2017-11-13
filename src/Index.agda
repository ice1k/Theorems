module Index where

import Nats.Add.Assoc
  using (nat-add-assoc) -- associative law for addition on natrual numbers
import Nats.Add.Comm
  using (nat-add-comm) -- commutative law for addition on natural numbers

import Ints.Add.Comm
  using (int-add-comm) -- commutative law for addition on integer

import Logics.And
  using (and-comm) -- commutative law for the "and" relation
  using (and-assoc) -- associative law for the "and" relation
import Logics.Or
  using (or-comm) -- commutative law for the "or" relation
  using (or-assoc) -- associative law for the "or" relation
  using (or-elim) -- elimination rule for the "or" relation
import Logics.Not
  using (not-not) -- law that negatives make a positive

import Vecs.Reverse
  using (vec-rev-rev) -- law that reverse twice returns the original list

import Lists.Reverse
  using (list-rev-rev) -- law that reverse twice returns the original vector

import Isos.NatLike
  using (iso-nat-vec) -- isomorphism between natrual numbers and vector
  using (iso-nat-list) -- isomorphism between natrual numbers and list
