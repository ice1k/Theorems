module index where

-- natural numbers
--- additions
import Nats.Add.Assoc
  using (nat-add-assoc) -- associative law
import Nats.Add.Comm
  using (nat-add-comm) -- commutative law
import Nats.Add.Invert
  using (nat-add-invert) -- a + a == b + b implies a == b
  using (nat-add-invert-1) -- a + 1 == b + 1 implies a == b

--- multiplications
import Nats.Multiply.Comm
  using (nat-multiply-comm) -- commutative law
import Nats.Multiply.Distrib
  using (nat-multiply-distrib) -- distributive law
import Nats.Multiply.Assoc
  using (nat-multiply-assoc) -- associative law

-- integers
--- some properties
import Ints.Properties
  using (eq-int-to-nat) -- for natrual number a, + a == + a implis a == a
  using (eq-neg-int-to-nat) -- for natrual number a, - a == - a implis a == a
  using (eq-nat-to-int) -- for natrual number a, a == a implis + a == + a
  using (eq-neg-nat-to-int) -- for natrual number a, a == a implis - a == - a

--- additions
import Ints.Add.Comm
  using (int-add-comm) -- commutative law
import Ints.Add.Assoc
  using (int-add-assoc) -- associative law
import Ints.Add.Invert
  using (int-add-invert) -- a + a == b + b implis a == b

-- non-negative rationals
--- some properties
import Rationals.Properties
  -- if b is not zero, n times b div b is the original number
  using (times-div-id)

-- additions
import Rationals.Add.Comm
  using (rational-add-comm) -- commutative law
import Rationals.Add.Assoc
  using (rational-add-assoc) -- associative law

-- multiplications
import Rationals.Multiply.Comm
  using (rational-multiply-comm) -- commutative law

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
  -- law that negative twice will make a positive
  using (not-not)
  using (contrapositive) -- contrapositive

-- vectors
--- reverse twice gives the original vector
import Vecs.Reverse
  using (vec-rev-rev-id)

-- lists
--- reverse twice gives the original vector
import Lists.Reverse
  using (list-rev-rev-id)

-- isomorphisms
--- natrual numbers and others
import Isos.NatLike
  using (iso-nat-vec) -- with vector
  using (iso-nat-list) -- with list

-- groups
--- s3 group, xxx=e, yy=e, yx=xxy
import Groups.Symm.S3
  using (s3-property-1) -- given s3, prove xyx≡y
