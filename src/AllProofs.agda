module AllProofs where

import Nats.Plus.Assoc
  using (nat-plus-assoc)
import Nats.Plus.Comm
  using (nat-plus-comm)

import Ints.Plus.Comm
  using (int-plus-comm)

import Logics.And
  using (and-comm; and-assoc)
import Logics.Or
  using (or-comm; or-assoc; or-elim)
import Logics.Not
  using (not-not)

import Lists.Reverse
  using (rev-rev)

import Isos.NatLike
  using (iso-nat-vec; iso-nat-list)
