/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientSourceThickness

/-!
# Weighted functional-slab thickness

This version of the separating-hyperplane argument does not discard small
coefficients.  Instead, it bounds the total coefficient mass lost in the CFP
complement and in a narrow slab by their cardinalities times the uniform
coefficient cap.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A bounded weight function has at most `card * cap` mass on any finite
set on which the pointwise cap is valid. -/
theorem sum_le_card_mul_of_le
    {α : Type*} [DecidableEq α]
    (S : Finset α) (q : α → ℝ) (cap : ℝ)
    (hq : ∀ x ∈ S, q x ≤ cap) :
    (∑ x ∈ S, q x) ≤ (S.card : ℝ) * cap := by
  calc
    (∑ x ∈ S, q x) ≤ ∑ _x ∈ S, cap := by
      exact Finset.sum_le_sum fun x hx ↦ hq x hx
    _ = (S.card : ℝ) * cap := by simp

/-- If `core` omits at most `missing` input points and its thin part has at
most `slab` points, then the mass outside the thin part is at least total
input mass minus `(missing + slab) * cap`. -/
theorem weightedOutsideMass_lower
    {α : Type*} [DecidableEq α]
    (input core : Finset α) (hcore : core ⊆ input)
    (q : α → ℝ) (cap massLower : ℝ)
    (hcap : 0 ≤ cap)
    (hqcap : ∀ x ∈ input, q x ≤ cap)
    (htotal : massLower ≤ ∑ x ∈ input, q x)
    (p : α → Prop) [DecidablePred p]
    (missing slab : ℕ)
    (hmissing : (input \ core).card ≤ missing)
    (hslab : (core.filter fun x ↦ ¬p x).card ≤ slab) :
    massLower - ((missing + slab : ℕ) : ℝ) * cap ≤
      ∑ x ∈ core.filter p, q x := by
  let outside := core.filter p
  have houtside : outside ⊆ input :=
    (Finset.filter_subset _ _).trans hcore
  have homit : input \ outside ⊆
      (input \ core) ∪ (core.filter fun x ↦ ¬p x) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hxc : x ∈ core
    · apply Finset.mem_union_right
      rw [Finset.mem_filter]
      refine ⟨hxc, ?_⟩
      intro hpx
      exact hx.2 (Finset.mem_filter.mpr ⟨hxc, hpx⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hxc⟩)
  have hcard : (input \ outside).card ≤ missing + slab := by
    calc
      (input \ outside).card ≤
          ((input \ core) ∪ (core.filter fun x ↦ ¬p x)).card :=
        Finset.card_le_card homit
      _ ≤ (input \ core).card +
          (core.filter fun x ↦ ¬p x).card := Finset.card_union_le _ _
      _ ≤ missing + slab := Nat.add_le_add hmissing hslab
  have hsumOmit : (∑ x ∈ input \ outside, q x) ≤
      ((missing + slab : ℕ) : ℝ) * cap := by
    calc
      (∑ x ∈ input \ outside, q x) ≤
          ((input \ outside).card : ℝ) * cap := by
        apply sum_le_card_mul_of_le
        intro x hx
        exact hqcap x (Finset.mem_sdiff.mp hx).1
      _ ≤ ((missing + slab : ℕ) : ℝ) * cap := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · exact hcap
  have hdecomp : (∑ x ∈ input, q x) - ∑ x ∈ outside, q x =
      ∑ x ∈ input \ outside, q x := by
    rw [← Finset.sum_sdiff_eq_sub houtside]
  dsimp only [outside] at hdecomp ⊢
  linarith

/-- Real-valued version of `weightedOutsideMass_lower`.  This loses no
integer ceiling in the slab estimate and is therefore the sharp form needed
to diagnose the source parameter budget. -/
theorem weightedOutsideMass_lower_realSlab
    {α : Type*} [DecidableEq α]
    (input core : Finset α) (hcore : core ⊆ input)
    (q : α → ℝ) (cap massLower : ℝ)
    (hcap : 0 ≤ cap)
    (hqcap : ∀ x ∈ input, q x ≤ cap)
    (htotal : massLower ≤ ∑ x ∈ input, q x)
    (p : α → Prop) [DecidablePred p]
    (missing : ℕ) (slabBound : ℝ)
    (hmissing : (input \ core).card ≤ missing)
    (hslab : ((core.filter fun x ↦ ¬p x).card : ℕ) ≤ slabBound) :
    massLower - ((missing : ℝ) + slabBound) * cap ≤
      ∑ x ∈ core.filter p, q x := by
  let outside := core.filter p
  have houtside : outside ⊆ input :=
    (Finset.filter_subset _ _).trans hcore
  have homit : input \ outside ⊆
      (input \ core) ∪ (core.filter fun x ↦ ¬p x) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hxc : x ∈ core
    · apply Finset.mem_union_right
      rw [Finset.mem_filter]
      refine ⟨hxc, ?_⟩
      intro hpx
      exact hx.2 (Finset.mem_filter.mpr ⟨hxc, hpx⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hxc⟩)
  have hcardNat : (input \ outside).card ≤
      (input \ core).card + (core.filter fun x ↦ ¬p x).card := by
    exact (Finset.card_le_card homit).trans (Finset.card_union_le _ _)
  have hcard : ((input \ outside).card : ℝ) ≤
      (missing : ℝ) + slabBound := by
    have hcardReal : ((input \ outside).card : ℝ) ≤
        ((input \ core).card : ℝ) +
          ((core.filter fun x ↦ ¬p x).card : ℝ) := by
      exact_mod_cast hcardNat
    have hmissingReal : (((input \ core).card : ℕ) : ℝ) ≤ missing := by
      exact_mod_cast hmissing
    linarith
  have hsumOmit : (∑ x ∈ input \ outside, q x) ≤
      ((missing : ℝ) + slabBound) * cap := by
    calc
      (∑ x ∈ input \ outside, q x) ≤
          ((input \ outside).card : ℝ) * cap := by
        apply sum_le_card_mul_of_le
        intro x hx
        exact hqcap x (Finset.mem_sdiff.mp hx).1
      _ ≤ ((missing : ℝ) + slabBound) * cap :=
        mul_le_mul_of_nonneg_right hcard hcap
  have hdecomp : (∑ x ∈ input, q x) - ∑ x ∈ outside, q x =
      ∑ x ∈ input \ outside, q x := by
    rw [← Finset.sum_sdiff_eq_sub houtside]
  dsimp only [outside] at hdecomp ⊢
  linarith

/-- Weighted analogue of the high-coefficient slab criterion.  No positive
pointwise lower bound on `q` is assumed. -/
theorem cube_subset_centeredZonotope_of_weighted_slabCard
    {d : ℕ} (input core : Finset (LatticePoint d))
    (hcore : core ⊆ input) (q : LatticePoint d → ℝ)
    (hqnonneg : ∀ x ∈ core, 0 ≤ q x)
    (cap massLower radius t : ℝ)
    (hcap : 0 ≤ cap)
    (hqcap : ∀ x ∈ input, q x ≤ cap)
    (htotal : massLower ≤ ∑ x ∈ input, q x)
    (missing slab : ℕ)
    (hmissing : (input \ core).card ≤ missing)
    (ht : 0 < t)
    (hslab : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      (core.filter fun x ↦
        |f (realVector x)| < t * coefficientMass f).card ≤ slab)
    (hradius : radius ≤
      t * (massLower - ((missing + slab : ℕ) : ℝ) * cap)) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope core q := by
  apply cube_subset_centeredZonotope_of_outsideSlabMass
    core q hqnonneg radius (fun f ↦ t * coefficientMass f)
  intro f
  by_cases hf : f = 0
  · subst f
    simp only [zero_apply, abs_zero, Finset.sum_const_zero, mul_zero]
    exact mul_nonneg (mul_nonneg ht.le (coefficientMass_nonneg 0))
      (Finset.sum_nonneg fun x hx ↦ hqnonneg x (Finset.mem_filter.mp hx).1)
  have hmassPos : 0 < coefficientMass f := coefficientMass_pos f hf
  have houtside := weightedOutsideMass_lower input core hcore q cap massLower
    hcap hqcap htotal (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|)
    missing slab hmissing (by simpa only [not_le] using hslab f hf)
  calc
    radius * ∑ i, |f (Pi.single i 1)| =
        radius * coefficientMass f := by rfl
    _ ≤ (t * (massLower - ((missing + slab : ℕ) : ℝ) * cap)) *
          coefficientMass f :=
      mul_le_mul_of_nonneg_right hradius hmassPos.le
    _ ≤ (t * (∑ x ∈ core.filter
          (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|), q x)) *
          coefficientMass f := by
      apply mul_le_mul_of_nonneg_right _ hmassPos.le
      exact mul_le_mul_of_nonneg_left houtside ht.le
    _ = (t * coefficientMass f) *
          (∑ x ∈ core.filter
            (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|), q x) := by
      ring

/-- Sharp real-slab analogue of
`cube_subset_centeredZonotope_of_weighted_slabCard`. -/
theorem cube_subset_centeredZonotope_of_weighted_realSlabCard
    {d : ℕ} (input core : Finset (LatticePoint d))
    (hcore : core ⊆ input) (q : LatticePoint d → ℝ)
    (hqnonneg : ∀ x ∈ core, 0 ≤ q x)
    (cap massLower radius t : ℝ)
    (hcap : 0 ≤ cap)
    (hqcap : ∀ x ∈ input, q x ≤ cap)
    (htotal : massLower ≤ ∑ x ∈ input, q x)
    (missing : ℕ) (slabBound : ℝ)
    (hmissing : (input \ core).card ≤ missing)
    (ht : 0 < t)
    (hslab : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      ((core.filter fun x ↦
        |f (realVector x)| < t * coefficientMass f).card : ℝ) ≤ slabBound)
    (hradius : radius ≤
      t * (massLower - ((missing : ℝ) + slabBound) * cap)) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope core q := by
  apply cube_subset_centeredZonotope_of_outsideSlabMass
    core q hqnonneg radius (fun f ↦ t * coefficientMass f)
  intro f
  by_cases hf : f = 0
  · subst f
    simp only [zero_apply, abs_zero, Finset.sum_const_zero, mul_zero]
    exact mul_nonneg (mul_nonneg ht.le (coefficientMass_nonneg 0))
      (Finset.sum_nonneg fun x hx ↦ hqnonneg x (Finset.mem_filter.mp hx).1)
  have hmassPos : 0 < coefficientMass f := coefficientMass_pos f hf
  have houtside := weightedOutsideMass_lower_realSlab input core hcore q cap
    massLower hcap hqcap htotal
    (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|)
    missing slabBound hmissing (by simpa only [not_le] using hslab f hf)
  calc
    radius * ∑ i, |f (Pi.single i 1)| =
        radius * coefficientMass f := by rfl
    _ ≤ (t * (massLower - ((missing : ℝ) + slabBound) * cap)) *
          coefficientMass f :=
      mul_le_mul_of_nonneg_right hradius hmassPos.le
    _ ≤ (t * (∑ x ∈ core.filter
          (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|), q x)) *
          coefficientMass f := by
      apply mul_le_mul_of_nonneg_right _ hmassPos.le
      exact mul_le_mul_of_nonneg_left houtside ht.le
    _ = (t * coefficientMass f) *
          (∑ x ∈ core.filter
            (fun x ↦ t * coefficientMass f ≤ |f (realVector x)|), q x) := by
      ring

end

end Erdos186.PZ.Intersection
