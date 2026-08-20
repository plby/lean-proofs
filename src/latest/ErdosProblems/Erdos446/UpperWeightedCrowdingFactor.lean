/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedQuantileBridge
import ErdosProblems.Erdos446.UpperCrowdingMass

/-!
# Erdős Problem 446: weighted four-factor crowding split

Ford's rank code splits a crowded occupancy vector into four pointwise
summands.  The reciprocal-factorial inequality was proved in
`UpperCrowdingMass`.  Here we retain an arbitrary nonnegative cell weight:
the occupancy monomial factors exactly, so the same injective rank code
bounds weighted mass by the product of the four weighted segment masses.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem weightedCompositionMass_le_four_of_pointwise_add
    {v : ℕ} (lam : Fin v → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (a b e d c : Fin v → ℕ)
    (hc : ∀ i, a i + b i + e i + d i = c i) :
    weightedCompositionMass lam c ≤
      weightedCompositionMass lam a *
        weightedCompositionMass lam b *
        weightedCompositionMass lam e *
        weightedCompositionMass lam d := by
  have hmono :
      (∏ i : Fin v, lam i ^ c i) =
        (∏ i : Fin v, lam i ^ a i) *
          (∏ i : Fin v, lam i ^ b i) *
          (∏ i : Fin v, lam i ^ e i) *
          (∏ i : Fin v, lam i ^ d i) := by
    calc
      (∏ i : Fin v, lam i ^ c i) =
          ∏ i : Fin v, lam i ^ (a i + b i + e i + d i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hc i]
      _ = _ := by
        simp only [pow_add, Finset.prod_mul_distrib]
  have hinv := inv_compositionFactorial_le_four_of_pointwise_add
    a b e d c hc
  have hprod : 0 ≤ ∏ i : Fin v, lam i ^ c i :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hlam i) _
  rw [weightedCompositionMass, weightedCompositionMass,
    weightedCompositionMass, weightedCompositionMass,
    weightedCompositionMass, div_eq_mul_inv, div_eq_mul_inv,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ← one_div, ← one_div, ← one_div, ← one_div, ← one_div]
  calc
    (∏ i : Fin v, lam i ^ c i) * (1 / compositionFactorial c) ≤
        (∏ i : Fin v, lam i ^ c i) *
          ((1 / compositionFactorial a) *
            (1 / compositionFactorial b) *
            (1 / compositionFactorial e) *
            (1 / compositionFactorial d)) :=
      mul_le_mul_of_nonneg_left hinv hprod
    _ = ((∏ i : Fin v, lam i ^ a i) *
          (1 / compositionFactorial a)) *
        ((∏ i : Fin v, lam i ^ b i) *
          (1 / compositionFactorial b)) *
        ((∏ i : Fin v, lam i ^ e i) *
          (1 / compositionFactorial e)) *
        ((∏ i : Fin v, lam i ^ d i) *
          (1 / compositionFactorial d)) := by
      rw [hmono]
      ring

/-- Weighted version of Ford's injective four-family rank split. -/
theorem weightedOccupancyMassOver_le_fourFamilies
    {v g l : ℕ} (lam : Fin v → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hgl : g + 1 ≤ l)
    (I A B E D : Finset (Fin v → ℕ))
    (hcode : ∀ c ∈ I,
      (crowdingRankCode c g l).1 ∈ A ∧
      (crowdingRankCode c g l).2.1 ∈ B ∧
      (crowdingRankCode c g l).2.2.1 ∈ E ∧
      (crowdingRankCode c g l).2.2.2 ∈ D) :
    weightedOccupancyMassOver lam I ≤
      weightedOccupancyMassOver lam A *
        weightedOccupancyMassOver lam B *
        weightedOccupancyMassOver lam E *
        weightedOccupancyMassOver lam D := by
  classical
  let J := I.image (fun c ↦ crowdingRankCode c g l)
  let Cert := A.product (B.product (E.product D))
  let W : (Fin v → ℕ) × (Fin v → ℕ) ×
      (Fin v → ℕ) × (Fin v → ℕ) → ℝ := fun z ↦
    weightedCompositionMass lam z.1 *
      weightedCompositionMass lam z.2.1 *
      weightedCompositionMass lam z.2.2.1 *
      weightedCompositionMass lam z.2.2.2
  have hJCert : J ⊆ Cert := by
    intro z hz
    change z ∈ I.image (fun c ↦ crowdingRankCode c g l) at hz
    obtain ⟨c, hcI, rfl⟩ := Finset.mem_image.mp hz
    have hm := hcode c hcI
    change crowdingRankCode c g l ∈ A.product (B.product (E.product D))
    exact Finset.mem_product.mpr ⟨hm.1,
      Finset.mem_product.mpr ⟨hm.2.1,
        Finset.mem_product.mpr ⟨hm.2.2.1, hm.2.2.2⟩⟩⟩
  have hcompNonneg : ∀ x : Fin v → ℕ,
      0 ≤ weightedCompositionMass lam x := by
    intro x
    exact div_nonneg
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hlam i) _)
      (by dsimp [compositionFactorial]; positivity)
  have hWNonneg : ∀ z, 0 ≤ W z := by
    intro z
    dsimp [W]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hcompNonneg z.1) (hcompNonneg z.2.1))
        (hcompNonneg z.2.2.1)) (hcompNonneg z.2.2.2)
  calc
    weightedOccupancyMassOver lam I ≤
        ∑ c ∈ I, W (crowdingRankCode c g l) := by
      rw [weightedOccupancyMassOver]
      apply Finset.sum_le_sum
      intro c hcI
      exact weightedCompositionMass_le_four_of_pointwise_add lam hlam
        _ _ _ _ c (crowdingRankCode_reassembles c hgl)
    _ = ∑ z ∈ J, W z := by
      change (∑ c ∈ I, W (crowdingRankCode c g l)) =
        ∑ z ∈ I.image (fun c ↦ crowdingRankCode c g l), W z
      symm
      apply Finset.sum_image
      intro c hc d hd hcd
      exact crowdingRankCode_injective_on hgl (Set.mem_univ c)
        (Set.mem_univ d) hcd
    _ ≤ ∑ z ∈ Cert, W z :=
      Finset.sum_le_sum_of_subset_of_nonneg hJCert
        (fun z hz hnot ↦ hWNonneg z)
    _ = weightedOccupancyMassOver lam A *
        weightedOccupancyMassOver lam B *
        weightedOccupancyMassOver lam E *
        weightedOccupancyMassOver lam D := by
      change (A.product (B.product (E.product D))).sum W = _
      rw [weightedOccupancyMassOver, weightedOccupancyMassOver,
        weightedOccupancyMassOver, weightedOccupancyMassOver]
      have hprod := Finset.sum_product A (B.product (E.product D)) W
      have hprod' : (A.product (B.product (E.product D))).sum W =
          ∑ x ∈ A, ∑ y ∈ B.product (E.product D), W (x, y) := by
        exact hprod
      rw [hprod']
      have hprodB (a : Fin v → ℕ) :
          (B.product (E.product D)).sum (fun y ↦ W (a, y)) =
            ∑ b ∈ B, ∑ z ∈ E.product D, W (a, b, z) := by
        exact Finset.sum_product B (E.product D) (fun y ↦ W (a, y))
      simp_rw [hprodB]
      have hprodE (a b : Fin v → ℕ) :
          (E.product D).sum (fun z ↦ W (a, b, z)) =
            ∑ e ∈ E, ∑ d ∈ D, W (a, b, e, d) := by
        exact Finset.sum_product E D (fun z ↦ W (a, b, z))
      simp_rw [hprodE]
      dsimp only [W]
      symm
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum B
        (fun b ↦ weightedCompositionMass lam b)
        (weightedCompositionMass lam a)]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum E
        (fun e ↦ weightedCompositionMass lam e)
        (weightedCompositionMass lam a * weightedCompositionMass lam b)]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum D
        (fun d ↦ weightedCompositionMass lam d)
        (weightedCompositionMass lam a * weightedCompositionMass lam b *
          weightedCompositionMass lam e)]

end Erdos446
