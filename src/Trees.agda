module Trees where

open import Data.Unit using (⊤)

data BinTree {a} (A : Set a) : Set a where
  Empty : A → BinTree A
  Node  : A → BinTree A → BinTree A → BinTree A

BareBinTree : Set
BareBinTree = BinTree ⊤

