module Isos.TreeLike where

open import Isos.Isomorphism

open import Trees
open import Tuples
open import Equality

open import Data.Product
open import Data.Unit

------------------------------------------------------------------------
-- internal stuffs

private

  pattern ∅ = Empty tt
  ∅′ : BareBinTree
  ∅′ = Empty tt
  _,,_ : BareBinTree → BareBinTree → BareBinTree
  _,,_ = Node tt
  infixl 4 _,,_
  pattern [_,_] a b = Node tt a b

  tree⁷->tree : BareBinTree ⁷ → BareBinTree
  tree⁷->tree (∅ , ∅ , ∅ , ∅ , ∅ , ∅ , [ [ [ [ a , b ] , c ] , d ] , e ])
              = ∅′ ,, a ,, b ,, c ,, d ,, e
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , ∅  , ∅  , ∅′) = ∅′
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , ∅  , t5 , t6)
              = t5 ,, t6 ,, ∅′ ,, ∅′ ,, ∅′ ,, ∅′ ,, ∅′
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , [ a , b ] , t5 , t6)
              = ∅′ ,, t6 ,, t5 ,, a ,, b
  tree⁷->tree (t0 , t1 , t2 , t3 , t4 , t5 , t6)
              = t6 ,, t5 ,, t4 ,, t3 ,, t2 ,, t1 ,, t0

  tree->tree⁷ : BareBinTree → BareBinTree ⁷
  tree->tree⁷ [ [ [ [ [ ∅ , a ] , b ] , c ] , d ] , e ]
              = ∅ , ∅ , ∅ , ∅ , ∅ , ∅ , (a ,, b ,, c ,, d ,, e)
  tree->tree⁷ [ [ [ [ [ t6 , t5 ] , ∅ ] , ∅ ] , ∅ ] , ∅ ]
              = ∅ , ∅ , ∅ , ∅ , ∅ , t5 , t6
  tree->tree⁷ [ [ [ [ ∅ , t6 ] , t5 ] , a ] , b ]
              = ∅ , ∅ , ∅ , ∅ , (a ,, b) , t5 , t6
  tree->tree⁷ [ [ [ [ [ [ t6 , t5 ] , t4 ] , t3 ] , t2 ] , t1 ] , t0 ]
              = t0 , t1 , t2 , t3 , t4 , t5 , t6
  tree->tree⁷ _ = ∅ , ∅ , ∅ , ∅ , ∅ , ∅ , ∅

  tree⁷<=>tree : BareBinTree ⁷ ⇔ BareBinTree
  tree⁷<=>tree = ∧-intro tree⁷->tree tree->tree⁷

  -- too hard
  -- proofL : ∀ tree → tree⁷->tree (tree->tree⁷ tree) ≡ tree
  -- proofL [ [ [ [ [ ∅ , a ] , b ] , c ] , d ] , e ]
  --        = refl
  -- proofL [ [ [ [ [ Node x t6 t7 , t5 ] , ∅ ] , ∅ ] , ∅ ] , ∅ ]
  --        = {!!}
  -- proofL [ [ [ [ ∅ , t6 ] , t5 ] , a ] , b ]
  --        = refl
  -- proofL [ [ [ [ [ [ t6 , t5 ] , t4 ] , t3 ] , t2 ] , t1 ] , t0 ]
  --        = {!!}
  -- proofL _ = {!!}

------------------------------------------------------------------------
-- public aliases

iso-seven-tree-in-one : BareBinTree ⁷ ⇔ BareBinTree
iso-seven-tree-in-one = tree⁷<=>tree

