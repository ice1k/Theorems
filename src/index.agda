module index where

-- natural numbers
--- additions
import Nats.Add.Assoc
  using (nat-add-assoc) -- associative law
  using (nat-add-assoc-flip) -- exchanged
import Nats.Add.Comm
  using (nat-add-comm) -- commutative law

--- multiplications
import Nats.Multiply.Comm
  using (nat-multiply-comm) -- commutative law
import Nats.Multiply.Distrib
  using (nat-multiply-distrib) -- distributive law
  using (nat-multiply-distrib-flip) -- exchanged
import Nats.Multiply.Assoc
  using (nat-multiply-assoc) -- associative law
  using (nat-multiply-assoc-flip) -- exchanged

-- integers
--- additions
import Ints.Add.Comm
  using (int-add-comm) -- commutative law

-- logics
--- the "and" relations
import Logics.And
  using (and-comm) -- commutative law
  using (and-assoc) -- associative law

--- the "or" relations
import Logics.Or
  using (or-comm) -- commutative law
  using (or-assoc) -- associative law
  using (or-elim) -- elimination rule

--- negations
import Logics.Not
  using (not-not) -- law that negatives make a positive

-- vectors
import Vecs.Reverse
  using (vec-rev-rev) -- law that reverse twice returns the original list

-- lists
import Lists.Reverse
  using (list-rev-rev) -- law that reverse twice returns the original vector

-- isomorphisms
--- natrual numbers and others
import Isos.NatLike
  using (iso-nat-vec) -- with vector
  using (iso-nat-list) -- with list
