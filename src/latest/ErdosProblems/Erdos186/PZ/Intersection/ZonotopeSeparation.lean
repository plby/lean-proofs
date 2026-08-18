/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ZonotopeThickness
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separation for finite centered zonotopes

The Pham--Zakharov thickness argument separates a point from a centered
zonotope.  This file supplies the finite-dimensional topological and support
lemmas for the literal zonotope definition used in the formalization.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A finite centered zonotope with nonnegative radii is compact. -/
theorem isCompact_centeredZonotope {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (_hq : ∀ x ∈ A, 0 ≤ q x) :
    IsCompact (centeredZonotope A q) := by
  let K : Set (A → ℝ) :=
    Set.univ.pi fun x ↦ Set.Icc (-q x.1) (q x.1)
  let F : (A → ℝ) → (Fin d → ℝ) := fun t i ↦
    ∑ x : A, t x * realVector x.1 i
  have hK : IsCompact K := by
    dsimp only [K]
    exact isCompact_univ_pi fun _x ↦ isCompact_Icc
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hEq : centeredZonotope A q = F '' K := by
    ext y
    constructor
    · rintro ⟨t, ht, hy⟩
      let c : A → ℝ := fun x ↦ t x.1
      have hc : c ∈ K := by
        intro x _hx
        exact (abs_le.mp (ht x.1 x.2))
      refine ⟨c, hc, ?_⟩
      funext i
      dsimp only [F, c]
      simpa only [← A.sum_attach, Finset.attach_eq_univ] using (hy i).symm
    · rintro ⟨c, hc, rfl⟩
      let t : (Fin d → ℤ) → ℝ := fun x ↦
        if hx : x ∈ A then c ⟨x, hx⟩ else 0
      refine ⟨t, ?_, ?_⟩
      · intro x hx
        have hcx : c ⟨x, hx⟩ ∈ Set.Icc (-q x) (q x) := hc ⟨x, hx⟩ trivial
        rw [abs_le]
        simpa [t, hx] using hcx
      · intro i
        dsimp only [F]
        simpa +contextual [← A.sum_attach, t]
  rw [hEq]
  exact hK.image hF

/-- A finite centered zonotope with nonnegative radii is closed. -/
theorem isClosed_centeredZonotope {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x) :
    IsClosed (centeredZonotope A q) :=
  (isCompact_centeredZonotope A q hq).isClosed

/-- Every linear functional attains the expected signed support value on a
finite centered zonotope. -/
theorem exists_mem_centeredZonotope_apply_eq_sum_abs {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∃ z ∈ centeredZonotope A q,
      f z = ∑ x ∈ A, q x * |f (realVector x)| := by
  let t : (Fin d → ℤ) → ℝ := fun x ↦
    if 0 ≤ f (realVector x) then q x else -q x
  let z : Fin d → ℝ := fun i ↦ ∑ x ∈ A, t x * realVector x i
  have hz : z ∈ centeredZonotope A q := by
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      by_cases hfx : 0 ≤ f (realVector x)
      · simp [t, hfx, abs_of_nonneg (hq x hx)]
      · simp [t, hfx, abs_of_nonneg (hq x hx)]
    · intro i
      rfl
  refine ⟨z, hz, ?_⟩
  have hzsum : z = ∑ x ∈ A, t x • realVector x := by
    funext i
    simp only [z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hzsum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [map_smul, smul_eq_mul]
  by_cases hfx : 0 ≤ f (realVector x)
  · simp [t, hfx, abs_of_nonneg hfx]
  · have hfx' : f (realVector x) ≤ 0 := le_of_not_ge hfx
    simp [t, hfx, abs_of_nonpos hfx']

/-- The coordinate cube has the expected support function. -/
theorem apply_le_cubeSupport {d : ℕ}
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (radius : ℝ)
    {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ radius) :
    f y ≤ radius * ∑ i, |f (Pi.single i 1)| := by
  have hybasis : y = ∑ i, y i • (Pi.single i 1 : Fin d → ℝ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simp [Pi.single_apply, hij]
    · simp
  calc
    f y ≤ |f y| := le_abs_self _
    _ = |∑ i, y i * f (Pi.single i 1)| := by
      apply congrArg abs
      calc
        f y = f (∑ i, y i • (Pi.single i 1 : Fin d → ℝ)) :=
          congrArg f hybasis
        _ = ∑ i, y i * f (Pi.single i 1) := by
          rw [map_sum]
          simp only [map_smul, smul_eq_mul]
    _ ≤ ∑ i, |y i * f (Pi.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |y i| * |f (Pi.single i 1)| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i, radius * |f (Pi.single i 1)| := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
    _ = radius * ∑ i, |f (Pi.single i 1)| := by
      rw [Finset.mul_sum]

/-- A support-function lower bound implies containment of a coordinate cube
in a finite centered zonotope.  This is the separation-theorem form used by
the source proof of PZ Lemma 14. -/
theorem cube_subset_centeredZonotope_of_support {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x) (radius : ℝ)
    (hSupport : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ,
      radius * ∑ i, |f (Pi.single i 1)| ≤
        ∑ x ∈ A, q x * |f (realVector x)|) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope A q := by
  intro y hy
  by_contra hnot
  obtain ⟨f, u, hzu, huy⟩ := geometric_hahn_banach_closed_point
    (convex_centeredZonotope A q) (isClosed_centeredZonotope A q hq) hnot
  obtain ⟨z, hz, hfz⟩ :=
    exists_mem_centeredZonotope_apply_eq_sum_abs A q hq f
  have hfy : f y ≤ radius * ∑ i, |f (Pi.single i 1)| :=
    apply_le_cubeSupport f radius hy
  have hzs :
      ∑ x ∈ A, q x * |f (realVector x)| < u := by
    rw [← hfz]
    exact hzu z hz
  exact (not_lt_of_ge (hfy.trans (hSupport f))) (hzs.trans huy)

/-- The contribution from generators outside a functional slab bounds the
support sum from below. -/
theorem threshold_mul_massOutside_le_support {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (threshold : ℝ) :
    threshold *
        (∑ x ∈ A.filter fun x ↦ threshold ≤ |f (realVector x)|, q x) ≤
      ∑ x ∈ A, q x * |f (realVector x)| := by
  let outside := A.filter fun x ↦ threshold ≤ |f (realVector x)|
  calc
    threshold * (∑ x ∈ outside, q x) =
        ∑ x ∈ outside, threshold * q x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ outside, q x * |f (realVector x)| := by
      apply Finset.sum_le_sum
      intro x hx
      have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
      have hxout : threshold ≤ |f (realVector x)| :=
        (Finset.mem_filter.mp hx).2
      nlinarith [hq x hxA]
    _ ≤ ∑ x ∈ A, q x * |f (realVector x)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x hxA _hxout
      exact mul_nonneg (hq x hxA) (abs_nonneg _)

/-- Source-shaped slab criterion for zonotope thickness: it is enough that,
for every functional, the weighted mass outside one centered slab pays for
the support of the desired coordinate cube. -/
theorem cube_subset_centeredZonotope_of_outsideSlabMass {d : ℕ}
    (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (hq : ∀ x ∈ A, 0 ≤ q x) (radius : ℝ)
    (threshold : ((Fin d → ℝ) →L[ℝ] ℝ) → ℝ)
    (hOutside : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ,
      radius * ∑ i, |f (Pi.single i 1)| ≤
        threshold f *
          (∑ x ∈ A.filter
            (fun x ↦ threshold f ≤ |f (realVector x)|), q x)) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope A q := by
  apply cube_subset_centeredZonotope_of_support A q hq radius
  intro f
  exact (hOutside f).trans
    (threshold_mul_massOutside_le_support A q hq f (threshold f))

end

end Erdos186.PZ.Intersection
