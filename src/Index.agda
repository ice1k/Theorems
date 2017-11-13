module Index where

-- on natural numbers
--- for addition
import Nats.Add.Assoc
  using (nat-add-assoc) -- associative law
  using (nat-add-assoc-flip) -- exchanged left and right
import Nats.Add.Comm
  using (nat-add-comm) -- commutative law for addition

--- for multiplication
import Nats.Multiply.Comm
  using (nat-multiply-comm) -- commutative law

-- on integer
--- for addition
import Ints.Add.Comm
  using (int-add-comm) -- commutative law

-- import Ints.Add.Assoc

--- for the "and" relations
import Logics.And
  using (and-comm) -- commutative law
  using (and-assoc) -- associative law

--- for the "or" relation
import Logics.Or
  using (or-comm) -- commutative law
  using (or-assoc) -- associative law
  using (or-elim) -- elimination rule

--- for nagatives
import Logics.Not
  using (not-not) -- law that negatives make a positive

import Vecs.Reverse
  using (vec-rev-rev) -- law that reverse twice returns the original list

import Lists.Reverse
  using (list-rev-rev) -- law that reverse twice returns the original vector

-- isomorphisms between natrual numbers and others
import Isos.NatLike
  using (iso-nat-vec) -- with vector
  using (iso-nat-list) -- with list
