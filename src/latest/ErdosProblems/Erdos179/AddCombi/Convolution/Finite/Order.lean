/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import ErdosProblems.Erdos179.AddCombi.Convolution.Finite.Defs

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Rat.Star

public section

open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise

variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
variable [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] {f g : G → K}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  fun _a ↦ expect_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

lemma conv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ∗ g) a := conv_nonneg hf hg _

@[simp] lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g := by
  refine (support_conv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, conv_apply_add]
  exact ne_of_gt <| expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩

lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing K] [StarOrderedRing K]

omit [IsStrictOrderedRing K] in
lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _a ↦ expect_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _

omit [IsStrictOrderedRing K] in
lemma dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ g) a := dconv_nonneg hf hg _

@[simp]
lemma support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [← conv_conjneg]; exact conv_pos hf (conjneg_pos.2 hg)
