module
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
## `Set` facts
-/

open Set

variable {α : Type}

public lemma Set.diff_union {s u v : Set α} : s \ (u ∪ v) = (s \ u) \ v :=
  Set.sdiff_sdiff.symm
