{-# OPTIONS --safe --cubical #-}
------------------------------------------------------------------------
-- FlagTable.agda —— 哪些 flag 是 infective、哪些是 coinfective
--   由 agda-code-gen 从 Agda 源码（Interaction.Options.Base.infectiveCoinfectiveOptions）生成，不要手改。
--   infective：子开了父必须开（父没开的子不能开）；coinfective：父开了子必须开（子关不掉）。
------------------------------------------------------------------------
module FlagTable where

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Agda.Builtin.String using (String; primStringEquality)

data FlagKind : Type where
  infective coinfective plain : FlagKind

flagKind : String → FlagKind
flagKind s =
  if primStringEquality s "--safe" then coinfective else
  if primStringEquality s "--without-K" then coinfective else
  if primStringEquality s "--cubical=compatible" then coinfective else
  if primStringEquality s "--no-universe-polymorphism" then coinfective else
  if primStringEquality s "--no-cumulativity" then coinfective else
  if primStringEquality s "--level-universe" then coinfective else
  if primStringEquality s "--cubical" then infective else
  if primStringEquality s "--cubical=full" then infective else
  if primStringEquality s "--cubical=erased" then infective else
  if primStringEquality s "--cubical=no-glue" then infective else
  if primStringEquality s "--guarded" then infective else
  if primStringEquality s "--irrelevance" then infective else
  if primStringEquality s "--prop" then infective else
  if primStringEquality s "--two-level" then infective else
  if primStringEquality s "--rewriting" then infective else
  if primStringEquality s "--local-rewriting" then infective else
  if primStringEquality s "--sized-types" then infective else
  if primStringEquality s "--guardedness" then infective else
  if primStringEquality s "--flat-split" then infective else
  if primStringEquality s "--polarity" then infective else
  if primStringEquality s "--cohesion" then infective else
  if primStringEquality s "--erasure" then infective else
  if primStringEquality s "--erased-matches" then infective else
  plain
