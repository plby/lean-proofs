/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnPositiveVolume
import ErdosProblems.Erdos186.PZ.Intersection.ActualStepInverse
import ErdosProblems.Erdos186.PZ.Intersection.CenteredZonotope

/-!
# Thickness supplied by a high-coefficient CFP progression

This is the geometric heart of the post-CFP intersection argument.  CFP is
applied to the part of a coefficient-balanced side on which every convex
coefficient is at least `theta`.  Taking the difference of the covered
subset sum for a progression point and the covered subset sum for zero puts
`theta` times that progression point in the centered zonotope.  Convexity
and central symmetry then put the full displayed crosspolytope in the
centered zonotope.

The construction is finite and explicit.  In particular, it does not assume
a separating-hyperplane or thickness conclusion as additional data.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MinkowskiSecond

noncomputable section

set_option autoImplicit false

/-- A centered zonotope is convex. -/
theorem convex_centeredZonotope {d : ℕ}
    (A : Finset (LatticePoint d)) (q : LatticePoint d → ℝ) :
    Convex ℝ (centeredZonotope A q) := by
  rintro y₁ ⟨t₁, ht₁, hy₁⟩ y₂ ⟨t₂, ht₂, hy₂⟩ a b ha hb hab
  refine ⟨fun x ↦ a * t₁ x + b * t₂ x, ?_, ?_⟩
  · intro x hx
    calc
      |a * t₁ x + b * t₂ x| ≤
          |a * t₁ x| + |b * t₂ x| := abs_add_le _ _
      _ = a * |t₁ x| + b * |t₂ x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * q x + b * q x :=
        add_le_add (mul_le_mul_of_nonneg_left (ht₁ x hx) ha)
          (mul_le_mul_of_nonneg_left (ht₂ x hx) hb)
      _ = q x := by rw [← add_mul, hab, one_mul]
  · intro i
    change
      a * y₁ i + b * y₂ i =
        ∑ x ∈ A, (a * t₁ x + b * t₂ x) * realVector x i
    rw [hy₁ i, hy₂ i]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring

/-- A centered zonotope is closed under negation. -/
theorem neg_mem_centeredZonotope {d : ℕ}
    {A : Finset (LatticePoint d)} {q : LatticePoint d → ℝ}
    {y : Fin d → ℝ} (hy : y ∈ centeredZonotope A q) :
    -y ∈ centeredZonotope A q := by
  obtain ⟨t, ht, hyt⟩ := hy
  refine ⟨-t, ?_, ?_⟩
  · intro x hx
    simpa using ht x hx
  · intro i
    change -y i = ∑ x ∈ A, (-t x) * realVector x i
    rw [hyt i]
    simp only [Finset.sum_neg_distrib, neg_mul]

/-- A centered zonotope is balanced.  Convexity plus central symmetry is the
form needed by the crosspolytope lemma. -/
theorem balanced_centeredZonotope {d : ℕ}
    (A : Finset (LatticePoint d)) (q : LatticePoint d → ℝ) :
    Balanced ℝ (centeredZonotope A q) := by
  apply (balanced_iff_neg_mem (convex_centeredZonotope A q)).2
  intro y hy
  exact neg_mem_centeredZonotope hy

/-- The scaled difference of two subset sums belongs to the centered
zonotope whenever every available coefficient is at least the scale. -/
theorem scaled_difference_subsetSums_mem_centeredZonotope
    {d : ℕ} (A : Finset (LatticePoint d))
    (q : LatticePoint d → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta) (hq : ∀ x ∈ A, theta ≤ q x)
    {u v : LatticePoint d}
    (hu : u ∈ GAP.subsetSums A) (hv : v ∈ GAP.subsetSums A) :
    (fun i ↦ theta * ((u i : ℝ) - (v i : ℝ))) ∈
      centeredZonotope A q := by
  obtain ⟨U, hUA, hUsum⟩ := GAP.mem_subsetSums_iff.mp hu
  obtain ⟨V, hVA, hVsum⟩ := GAP.mem_subsetSums_iff.mp hv
  let indicator : Finset (LatticePoint d) → LatticePoint d → ℝ :=
    fun T x ↦ if x ∈ T then 1 else 0
  let t : LatticePoint d → ℝ :=
    fun x ↦ theta * (indicator U x - indicator V x)
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    have hxq := hq x hx
    have hxq0 : 0 ≤ q x := htheta.trans hxq
    simp only [t, indicator]
    by_cases hxU : x ∈ U <;> by_cases hxV : x ∈ V <;>
      simp [hxU, hxV, abs_of_nonneg htheta, hxq, hxq0]
  · intro i
    have hsumIndicator (T : Finset (LatticePoint d)) (hTA : T ⊆ A) :
        (∑ x ∈ A, indicator T x * realVector x i) =
          ∑ x ∈ T, realVector x i := by
      symm
      calc
        (∑ x ∈ T, realVector x i) =
            ∑ x ∈ T, indicator T x * realVector x i := by
          apply Finset.sum_congr rfl
          intro x hxT
          simp [indicator, hxT]
        _ = ∑ x ∈ A, indicator T x * realVector x i := by
          apply Finset.sum_subset hTA
          intro x hxA hxT
          simp [indicator, hxT]
    have hUcoord : (∑ x ∈ U, realVector x i) = (u i : ℝ) := by
      have hi := congrFun hUsum i
      change (∑ x ∈ U, (x i : ℝ)) = (u i : ℝ)
      simp only [Finset.sum_apply] at hi
      exact_mod_cast hi
    have hVcoord : (∑ x ∈ V, realVector x i) = (v i : ℝ) := by
      have hi := congrFun hVsum i
      change (∑ x ∈ V, (x i : ℝ)) = (v i : ℝ)
      simp only [Finset.sum_apply] at hi
      exact_mod_cast hi
    calc
      theta * ((u i : ℝ) - (v i : ℝ)) =
          theta * ((∑ x ∈ U, realVector x i) -
            ∑ x ∈ V, realVector x i) := by rw [hUcoord, hVcoord]
      _ = theta * ((∑ x ∈ A, indicator U x * realVector x i) -
            ∑ x ∈ A, indicator V x * realVector x i) := by
          rw [hsumIndicator U hUA, hsumIndicator V hVA]
      _ = ∑ x ∈ A, t x * realVector x i := by
          simp only [t]
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _hx
          ring

/-- Difference the covered translate of a progression point with the
covered translate of zero. -/
theorem scaled_dilate_point_mem_centeredZonotope
    {d r k : ℕ} (A : Finset (LatticePoint d))
    (P : GAP d r) (t : LatticePoint d)
    (q : LatticePoint d → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta) (hq : ∀ x ∈ A, theta ≤ q x)
    (hP : P.Symmetric)
    (hcovered : CFP.translate t (P.dilate k).carrier ⊆ GAP.subsetSums A)
    {p : LatticePoint d} (hp : p ∈ (P.dilate k).carrier) :
    theta • realVector p ∈ centeredZonotope A q := by
  have htp : t + p ∈ GAP.subsetSums A := by
    apply hcovered
    exact CFP.mem_translate_iff.mpr ⟨p, hp, rfl⟩
  have ht : t ∈ GAP.subsetSums A := by
    apply hcovered
    apply CFP.mem_translate_iff.mpr
    exact ⟨0, (hP.dilate k).zero_mem_carrier, by simp⟩
  have hdiff := scaled_difference_subsetSums_mem_centeredZonotope
    A q theta htheta hq htp ht
  convert hdiff using 1
  funext i
  simp [realVector]

/-- The positive extreme in one displayed direction belongs to the centered
dilate. -/
theorem centered_stepExtreme_mem_dilate
    {d k : ℕ} (P : GAP d d) {radii : Fin d → ℕ}
    (hP : P.Centered radii) (i : Fin d) :
    (k * radii i : ℤ) • P.steps i ∈ (P.dilate k).carrier := by
  let a : Fin d → ℤ := Pi.single i (k * radii i : ℤ)
  have ha : ∀ j, |a j| ≤ (k * radii j : ℕ) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [a]
    · simp [a, hji]
      positivity
  have hsum : (k * radii i : ℤ) • P.steps i =
      ∑ j, a j • P.steps j := by
    rw [Finset.sum_eq_single i]
    · simp [a]
    · intro j _hj hji
      simp [a, Pi.single_apply, hji]
    · simp
  exact mem_dilate_of_stepCoefficients_le P hP a hsum ha

/-- The crosspolytope generated by the displayed radii of a covered square
progression is contained in the high-coefficient centered zonotope. -/
theorem covered_dilate_crosspolytope_subset_centeredZonotope
    {d k : ℕ} (hd : 0 < d) (A : Finset (LatticePoint d))
    (P : GAP d d) {radii : Fin d → ℕ} (hP : P.Centered radii)
    (t : LatticePoint d) (q : LatticePoint d → ℝ) (theta : ℝ)
    (htheta : 0 ≤ theta) (hq : ∀ x ∈ A, theta ≤ q x)
    (hcovered : CFP.translate t (P.dilate k).carrier ⊆ GAP.subsetSums A) :
    (Matrix.toLin' (scaledRealColumns
      (fun i ↦ theta * (k * radii i : ℕ)) P.steps)) '' l1UnitBall d ⊆
        centeredZonotope A q := by
  apply Erdos186.DiscreteJohn.scaledCrosspolytope_subset_balancedConvex
    (fun i ↦ theta * (k * radii i : ℕ)) P.steps
    (balanced_centeredZonotope A q) (convex_centeredZonotope A q) _ hd
  intro i
  have hextreme := scaled_dilate_point_mem_centeredZonotope A P t q theta
    htheta hq ⟨radii, hP⟩ hcovered (centered_stepExtreme_mem_dilate P hP i)
  simpa [realVector, integralEmbed, smul_smul, mul_assoc] using hextreme

end

end Erdos186.PZ.Intersection
