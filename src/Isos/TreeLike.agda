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
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , ∅  , ∅  , a) = a
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , ∅  , t₅ , t₆)
              = t₅ ,, t₆ ,, ∅′ ,, ∅′ ,, ∅′ ,, ∅′ ,, ∅′
  tree⁷->tree (∅  , ∅  , ∅  , ∅  , [ a , b ] , t₅ , t₆)
              = ∅′ ,, t₆ ,, t₅ ,, a ,, b
  tree⁷->tree (t₀ , t₁ , t₂ , t₃ , t₄ , t₅ , t₆)
              = t₆ ,, t₅ ,, t₄ ,, t₃ ,, t₂ ,, t₁ ,, t₀

  tree->tree⁷ : BareBinTree → BareBinTree ⁷
  tree->tree⁷ [ [ [ [ [ ∅ , a ] , b ] , c ] , d ] , e ]
              = ∅ , ∅ , ∅ , ∅ , ∅ , ∅ , (a ,, b ,, c ,, d ,, e)
  tree->tree⁷ [ [ [ [ [ t₆ , t₅ ] , ∅ ] , ∅ ] , ∅ ] , ∅ ]
              = ∅ , ∅ , ∅ , ∅ , ∅ , t₅ , t₆
  tree->tree⁷ [ [ [ [ ∅ , t₆ ] , t₅ ] , a ] , b ]
              = ∅ , ∅ , ∅ , ∅ , (a ,, b) , t₅ , t₆
  tree->tree⁷ [ [ [ [ [ [ t₆ , t₅ ] , t₄ ] , t₃ ] , t₂ ] , t₁ ] , t₀ ]
              = t₀ , t₁ , t₂ , t₃ , t₄ , t₅ , t₆
  tree->tree⁷ a = ∅ , ∅ , ∅ , ∅ , ∅ , ∅ , a

  tree⁷<=>tree : BareBinTree ⁷ ⇔ BareBinTree
  tree⁷<=>tree = ∧-intro tree⁷->tree tree->tree⁷

  -- too hard
  -- proofL : ∀ tree → tree⁷->tree (tree->tree⁷ tree) ≡ tree
  -- proofL [ [ [ [ [ ∅ , a ] , b ] , c ] , d ] , e ]
  --        = refl
  -- proofL [ [ [ [ [ Node x t₆ t7 , t₅ ] , ∅ ] , ∅ ] , ∅ ] , ∅ ]
  --        = {!!}
  -- proofL [ [ [ [ ∅ , t₆ ] , t₅ ] , a ] , b ]
  --        = refl
  -- proofL [ [ [ [ [ [ t₆ , t₅ ] , t₄ ] , t₃ ] , t₂ ] , t₁ ] , t₀ ]
  --        = {!!}
  -- proofL _ = {!!}

------------------------------------------------------------------------
-- public aliases

iso-seven-tree-in-one : BareBinTree ⁷ ⇔ BareBinTree
iso-seven-tree-in-one = tree⁷<=>tree

