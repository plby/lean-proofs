/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMarking

/-! # Product weights for two-colour quasi-moment coordinates -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiWeight {V : Type*} [DecidableEq V]
    (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0) : SourceQuasiCoordinate V → ℝ≥0 :=
  Sum.elim (Sum.elim f₀ f₁) (fun _ ↦ p)

theorem sourceQuasiWeight_factor
    {V : Type*} [DecidableEq V] (f₀ f₁ : TripleOn V → ℝ≥0) (p : ℝ≥0)
    (H : Finset (SourceQuasiCoordinate V)) :
    setWeight (sourceQuasiWeight f₀ f₁ p) H =
      setWeight f₀ H.toLeft.toLeft * setWeight f₁ H.toLeft.toRight * p ^ H.toRight.card := by
  unfold setWeight
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight, prod_sum_eq_prod_toLeft_mul_prod_toRight H.toLeft]
  simp only [sourceQuasiWeight, Sum.elim_inl, Sum.elim_inr, prod_const]

theorem SourceQuasiMarking.remainder_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    (f₀ f₁ π : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ π T) (h₁ : ∀ T, f₁ T ≤ π T)
    {H : Finset (SourceQuasiCoordinate V)} (hH : H ⊆ x.coordinates B) :
    setWeight (sourceQuasiWeight f₀ f₁ p) (x.coordinates B \ H) ≤
      setWeight π ((x.system \ {x.root}) \ sourceQuasiUnderlyingRoot H) := by
  have hh : H.toLeft.toLeft ⊆ x.initial ∧ H.toLeft.toRight ⊆ x.later :=
    subset_disjSum.mp (subset_disjSum.mp hH).1
  have hd := hx.disjoint.mono (sdiff_subset : x.initial \ H.toLeft.toLeft ⊆ x.initial)
    (sdiff_subset : x.later \ H.toLeft.toRight ⊆ x.later)
  rw [sourceQuasiWeight_factor]
  simp only [toLeft_sdiff, toRight_sdiff, coordinates, toLeft_disjSum, toRight_disjSum]
  calc
    _ ≤ setWeight π (x.initial \ H.toLeft.toLeft) * setWeight π (x.later \ H.toLeft.toRight) * 1 :=
      mul_le_mul (mul_le_mul (prod_le_prod' (fun T _ ↦ h₀ T))
        (prod_le_prod' (fun T _ ↦ h₁ T)) zero_le zero_le) (pow_le_one₀ zero_le hp) zero_le zero_le
    _ = _ := by
      rw [mul_one, SourceQuasiMarking.remainder_eq hx, sourceQuasiUnderlyingRoot,
        ← disjoint_colored_sdiff_union hx.disjoint hh.1 hh.2]
      exact (prod_union hd).symm

theorem SourceQuasiMarking.full_weight_le_density
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {S B : Finset V}
    {x : SourceQuasiMarking V} (hx : IsSourceQuasiMarking W F e S B x)
    (f₀ f₁ π : TripleOn V → ℝ≥0) (p : ℝ≥0) (hp : p ≤ 1)
    (h₀ : ∀ T, f₀ T ≤ π T) (h₁ : ∀ T, f₁ T ≤ p * π T) :
    setWeight (sourceQuasiWeight f₀ f₁ p) (x.coordinates B) ≤
      p ^ (B.card + 1) * setWeight π (x.system \ {x.root}) := by
  have hpD : p ^ x.later.card ≤ p :=
    pow_le_of_le_one zero_le hp (Nat.ne_of_gt (card_pos.mpr hx.later_nonempty))
  rw [sourceQuasiWeight_factor]
  simp only [coordinates, toLeft_disjSum, toRight_disjSum, sourceQuasiSpokes_card]
  calc
    _ ≤ setWeight π x.initial * setWeight (fun T ↦ p * π T) x.later * p ^ B.card := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact mul_le_mul (prod_le_prod' (fun T _ ↦ h₀ T)) (prod_le_prod' (fun T _ ↦ h₁ T)) zero_le zero_le
    _ = p ^ x.later.card * p ^ B.card * setWeight π (x.system \ {x.root}) := by
      rw [SourceQuasiMarking.remainder_eq hx]
      simp only [setWeight, prod_mul_distrib, prod_const, prod_union hx.disjoint]
      ring
    _ ≤ p * p ^ B.card * setWeight π (x.system \ {x.root}) := by gcongr
    _ = _ := by rw [pow_succ]; ring

end

end Erdos207
