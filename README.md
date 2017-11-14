# Theorems

<!-- [![Build Status](https://travis-ci.org/ice1000/Theorems.svg?branch=master)](https://travis-ci.org/ice1000/Theorems) -->
[![CircleCI](https://circleci.com/gh/ice1000/Theorems.svg?style=svg)](https://circleci.com/gh/ice1000/Theorems)

Theorems proving codes, written in Agda.

Each proof is put into separate files, except those very very short ones.

This library depends on [the Agda standard library](https://github.com/agda/agda-stdlib/).

## All Proofs

You can either:

+ View all proves [online](http://ice1000.coding.me/Theorems/Index.html)

+ See [Index.agda](./src/Index.agda)

## File structure

```agda
module Meow where -- module definition

open import Data.Meow -- imports

------------------------------------------------------------------------
-- definitions

meow~ : Meow -- some basic function definitions here

------------------------------------------------------------------------
-- internal stuffs

private

  ⌈meow≶meow⌉ : Meow ≡ Meow -- proofs here, with strange but readable naming
                            -- you'll never know how I type those characters

------------------------------------------------------------------------
-- public aliases

meow-meow : Meow ≡ Meow
meow-meow = ⌈meow≶meow⌉ -- regulated aliases, using ascii characters
```
