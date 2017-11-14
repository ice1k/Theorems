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
--- law that reverse twice returns the original vector
import Vecs.Reverse
  using (vec-rev-rev)

-- lists
--- law that reverse twice returns the original vector
import Lists.Reverse
  using (list-rev-rev)

-- isomorphisms
--- natrual numbers and others
import Isos.NatLike
  using (iso-nat-vec) -- with vector
  using (iso-nat-list) -- with list

-- groups
--- s3 group
import Groups.Symm.S3
  using (s3-property-1) -- given xxx=e, yy=e, yx=xxy, prove aba≡b
