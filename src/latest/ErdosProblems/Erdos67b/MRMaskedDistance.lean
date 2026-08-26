import ErdosProblems.Erdos67b.MRHalaszBandDistance
import Mathlib.Analysis.PSeries

/-!
# Pretentious distance retained by prime deletion

The deleted primes themselves pay a positive distance cost. Retaining
this cost is useful when summing inclusion-exclusion terms; this file
does not assert a pointwise cofactor Halász theorem.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

def mrRemovedPrimeMass (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X, if P p then 0 else 1 / (p : ℝ)

theorem mrPretentiousTerm_mask_lower
    {f g : ℕ → ℂ} (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime)
    (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 2) :
    lam * pretentiousTerm f g p + (1 - 2 * lam) * (if P p then 0 else 1 / (p : ℝ)) ≤
      pretentiousTerm (primeBandCoefficient f P) g p := by
  rw [pretentiousTerm_primeBandCoefficient f g P hp]
  by_cases hP : P p
  · simp only [hP, ↓reduceIte, mul_zero, add_zero]
    have hh := pretentiousTerm_nonneg hf hg
    nlinarith
  · simp only [hP, ↓reduceIte]
    have hh := mul_le_mul_of_nonneg_left (pretentiousTerm_le_two_div hf hg) hlam0
    have hratio : 2 / (p : ℝ) = 2 * (1 / (p : ℝ)) := by ring
    rw [hratio] at hh
    nlinarith

theorem mrPretentiousDistSq_mask_lower
    {f g : ℕ → ℂ} (P : ℕ → Prop) [DecidablePred P] (X : ℕ)
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 2) :
    lam * pretentiousDistSq f g X + (1 - 2 * lam) * mrRemovedPrimeMass P X ≤
      pretentiousDistSq (primeBandCoefficient f P) g X := by
  unfold pretentiousDistSq mrRemovedPrimeMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_primesUpTo.mp hp).1
  exact mrPretentiousTerm_mask_lower P hprime (hf p hprime) (hg p hprime) hlam0 hlam1

theorem mrRemovedPrimeMass_outside_finset (A : Finset ℕ) {X : ℕ}
    (hA : A ⊆ primesUpTo X) :
    mrRemovedPrimeMass (fun p ↦ p ∉ A) X = ∑ p ∈ A, 1 / (p : ℝ) := by
  classical
  unfold mrRemovedPrimeMass
  simp only [ite_not]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun hp ↦ ⟨hA hp, hp⟩⟩

theorem mrRemovedPrimeMass_outside_biUnion {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ) {X : ℕ}
    (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ι) B) :
    mrRemovedPrimeMass (fun p ↦ p ∉ J.biUnion B) X =
      ∑ j ∈ J, ∑ p ∈ B j, 1 / (p : ℝ) := by
  rw [mrRemovedPrimeMass_outside_finset (J.biUnion B) (by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hB j hj hpj)]
  exact Finset.sum_biUnion hdisj

theorem mrSum_exp_neg_le_of_subset_cost {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (D : Finset ι → ℝ) (m : ι → ℝ)
    {M lam kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hD : ∀ S ⊆ J, lam * M + (1 - 2 * lam) * (∑ j ∈ S, m j) ≤ D S) :
    (∑ S ∈ J.powerset, Real.exp (-kappa * D S)) ≤
      Real.exp (-kappa * lam * M) *
        ∏ j ∈ J, (1 + Real.exp (-kappa * (1 - 2 * lam) * m j)) := by
  calc
    _ ≤ ∑ S ∈ J.powerset, Real.exp (-kappa * lam * M) *
        ∏ j ∈ S, Real.exp (-kappa * (1 - 2 * lam) * m j) := by
      apply Finset.sum_le_sum
      intro S hS
      rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (hD S (Finset.mem_powerset.mp hS)) hkappa
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, Finset.prod_one_add]

/-- The finite inclusion-exclusion sum retains each deleted block's
prime mass. No pointwise mean-value estimate is assumed or concluded. -/
theorem mrSum_exp_neg_mask_distance_le {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ) {X : ℕ}
    (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ι) B)
    {f g : ℕ → ℂ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {lam kappa : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 2) (hkappa : 0 ≤ kappa) :
    (∑ S ∈ J.powerset, Real.exp (-kappa *
      pretentiousDistSq (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) g X)) ≤
      Real.exp (-kappa * lam * pretentiousDistSq f g X) *
        ∏ j ∈ J, (1 + Real.exp (-kappa * (1 - 2 * lam) *
          (∑ p ∈ B j, 1 / (p : ℝ)))) := by
  apply mrSum_exp_neg_le_of_subset_cost J _ _ hkappa
  intro S hS
  have hh := mrPretentiousDistSq_mask_lower (fun p ↦ p ∉ S.biUnion B) X hf hg hlam0 hlam1
  have hdisjS : Set.PairwiseDisjoint (↑S : Set ι) B := by
    intro i hi j hj hij
    exact hdisj (hS hi) (hS hj) hij
  rw [mrRemovedPrimeMass_outside_biUnion S B
    (fun j hj ↦ hB j (hS hj)) hdisjS] at hh
  exact hh

def mrMaskProductSeries : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))

theorem mrMaskProduct_le_series (J : Finset ℕ) (cost : ℕ → ℝ)
    (hJ : ∀ j ∈ J, 1 ≤ j)
    (hcost : ∀ j ∈ J, (3 / 2 : ℝ) * Real.log (j : ℝ) ≤ cost j) :
    (∏ j ∈ J, (1 + Real.exp (-cost j))) ≤ Real.exp mrMaskProductSeries := by
  have hsum : (∑ j ∈ J, Real.exp (-cost j)) ≤ mrMaskProductSeries := by
    calc
      _ ≤ ∑ j ∈ J, (j : ℝ) ^ (-(3 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (hJ j hj)
        rw [Real.rpow_def_of_pos hj0]
        apply Real.exp_le_exp.mpr
        linarith [hcost j hj]
      _ ≤ _ := (Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2 : ℝ)) < -1)).sum_le_tsum J
        (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact (Real.prod_one_add_le_exp_sum J (fun n ↦ (Real.exp_pos (-cost n)).le)).trans
    (Real.exp_le_exp.mpr hsum)

theorem mrSum_exp_neg_mask_distance_le_uniform
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X : ℕ}
    (hJ : ∀ j ∈ J, 1 ≤ j)
    (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    {f g : ℕ → ℂ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {lam kappa : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 2) (hkappa : 0 ≤ kappa)
    (hmass : ∀ j ∈ J, (3 / 2 : ℝ) * Real.log (j : ℝ) ≤
      kappa * (1 - 2 * lam) * (∑ p ∈ B j, 1 / (p : ℝ))) :
    (∑ S ∈ J.powerset, Real.exp (-kappa *
      pretentiousDistSq (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) g X)) ≤
      Real.exp (mrMaskProductSeries - kappa * lam * pretentiousDistSq f g X) := by
  have hprod := mrMaskProduct_le_series J
    (fun j ↦ kappa * (1 - 2 * lam) * (∑ p ∈ B j, 1 / (p : ℝ))) hJ hmass
  have hh := mrSum_exp_neg_mask_distance_le J B hB hdisj hf hg hlam0 hlam1 hkappa
  calc
    _ ≤ Real.exp (-kappa * lam * pretentiousDistSq f g X) *
        Real.exp mrMaskProductSeries := by
      apply hh.trans
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have heq (j : ℕ) : -kappa * (1 - 2 * lam) * (∑ p ∈ B j, 1 / (p : ℝ)) =
          -(kappa * (1 - 2 * lam) * (∑ p ∈ B j, 1 / (p : ℝ))) := by ring
      simpa only [heq] using hprod
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end

end Erdos67b
