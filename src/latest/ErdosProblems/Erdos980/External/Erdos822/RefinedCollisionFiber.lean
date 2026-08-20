/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.CollisionFiber
import ErdosProblems.Erdos980.External.Erdos822.CollisionDeterminant
import ErdosProblems.Erdos980.External.Erdos822.SlopeAwarePrimePairs

/-!
# Scale-sensitive analytic bound for one collision fiber

The least collision supplies large prime constants.  The parameterization
uses the actual quotient ceilings, and the slope-aware beta sieve then gives
the determinant Euler product with its explicit slope-prime loss.
-/

namespace Erdos822

theorem exists_outerCollisionPairs_slopeAware_pair_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ x m m' z y S : ℕ,
        0 < m → 0 < m' →
        (∀ p ∈ outerPrimes x m, m < p) →
        (∀ p ∈ outerPrimes x m', m' < p) →
        (∀ p ∈ outerPrimes x m, y < p) →
        (∀ p ∈ outerPrimes x m', y < p) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (outerCollisionPairs x m m').Nonempty →
        ∃ q q' : ℕ,
          (q, q') ∈ outerCollisionPairs x m m' ∧
          let B := reducedCollisionRight m m'
          let Acoef := reducedCollisionLeft m m'
          let U := max (x / m) (x / m')
          let X := U / B + 1
          let V := Erdos851.localEulerProduct
            (Erdos851.pairShiftDensity (affineDetNat B q Acoef q')) z y
          let L := slopePrimeLoss (affineDetNat B q Acoef q') B Acoef z y
          let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
          ((outerCollisionPairs x m m').card : ℝ) ≤
            (X : ℝ) * ((1 + eta) * (V * L)) +
              ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hpair⟩ :=
    exists_twoAffinePrimeCandidates_slopeAware_pair_bound
  refine ⟨A, hA, ?_⟩
  intro x m m' z y S hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hne
  obtain ⟨q, q', hbase, hcard⟩ :=
    outerCollisionPairs_card_le_primeCandidates_div_of_nonempty
      hm hm' hlarge hlarge' hy hy' hne
  refine ⟨q, q', hbase, ?_⟩
  dsimp only at hcard ⊢
  have hq : q.Prime :=
    (mem_outerPrimes_iff.mp (mem_outerCollisionPairs_iff.mp hbase).1).2.2
  have hq' : q'.Prime :=
    (mem_outerPrimes_iff.mp (mem_outerCollisionPairs_iff.mp hbase).2.1).2.2
  have hyq : y < q := hy q (mem_outerCollisionPairs_iff.mp hbase).1
  have hyq' : y < q' := hy' q' (mem_outerCollisionPairs_iff.mp hbase).2.1
  have hcardR :
      ((outerCollisionPairs x m m').card : ℝ) ≤
        ((twoAffinePrimeCandidates
          (reducedCollisionRight m m') q
          (reducedCollisionLeft m m') q'
          (max (x / m) (x / m') / reducedCollisionRight m m' + 1) y).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (hpair (reducedCollisionRight m m') (reducedCollisionLeft m m')
      q q'
      (max (x / m) (x / m') / reducedCollisionRight m m' + 1)
      z y S hq hq' hyq hyq' hz hzy hyTwo hS hlog)

/-- Rewriting the determinant by the collision equation removes all
dependence of the analytic majorant on the chosen least base primes. -/
theorem outerCollisionPairs_slopeAware_reducedDet_bound_of_nonempty :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ x m m' z y S : ℕ,
        0 < m → 0 < m' →
        (∀ p ∈ outerPrimes x m, m < p) →
        (∀ p ∈ outerPrimes x m', m' < p) →
        (∀ p ∈ outerPrimes x m, y < p) →
        (∀ p ∈ outerPrimes x m', y < p) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        (outerCollisionPairs x m m').Nonempty →
        let B := reducedCollisionRight m m'
        let Acoef := reducedCollisionLeft m m'
        let U := max (x / m) (x / m')
        let X := U / B + 1
        let V := Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (reducedTotientDet m m')) z y
        let L := slopePrimeLoss (reducedTotientDet m m') B Acoef z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((outerCollisionPairs x m m').card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * (V * L)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbaseBound⟩ :=
    exists_outerCollisionPairs_slopeAware_pair_bound
  refine ⟨A, hA, ?_⟩
  intro x m m' z y S hm hm' hlarge hlarge' hy hy'
    hz hzy hyTwo hS hlog hne
  obtain ⟨q, q', hbase, hbound⟩ :=
    hbaseBound x m m' z y S hm hm' hlarge hlarge' hy hy'
      hz hzy hyTwo hS hlog hne
  dsimp only at hbound ⊢
  have hdet :=
    affineDetNat_reducedCollision_eq_reducedTotientDet_of_collision
      (mem_outerCollisionPairs_iff.mp hbase).1
      (mem_outerCollisionPairs_iff.mp hbase).2.1
      hm hm'
      (hlarge q (mem_outerCollisionPairs_iff.mp hbase).1)
      (hlarge' q' (mem_outerCollisionPairs_iff.mp hbase).2.1)
      (mem_outerCollisionPairs_iff.mp hbase).2.2
  rw [hdet] at hbound
  exact hbound

end Erdos822
