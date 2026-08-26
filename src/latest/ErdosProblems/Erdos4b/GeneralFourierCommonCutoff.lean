/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientSupport
import ErdosProblems.Erdos4b.GeneralFourierCanonicalCutoff

/-!
# A denominator-independent compact-profile cutoff

This cutoff bounds every positive coordinate of a nonzero profile
tensor and stabilizes both the ordinary and totient sums. It depends
only on the profiles and scales, not on either arithmetic graph.
The older ordinary canonical sum is preserved exactly.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def compactProfileTensorCommonBound {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℕ := by
  classical
  exact if h : (∀ ib, HasCompactSupport (F ib)) ∧ (∀ i b, 0 < L i b) then
    (exists_common_profileTensor_cutoff_stabilization F h.1 L h.2).choose
  else 0

theorem compactProfileTensorCommonBound_capture {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : ∀ i b, 0 < d i b)
    (hne : doubledSelbergProfileTensor F L d ≠ 0) :
    ∀ i b, d i b ≤ compactProfileTensorCommonBound F L := by
  classical
  unfold compactProfileTensorCommonBound
  rw [dif_pos ⟨hF, hL⟩]
  exact (exists_common_profileTensor_cutoff_stabilization F hF L hL).choose_spec.1 d hd hne

theorem compactProfileTensorCommonBound_spec {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) :
    cutoffSelbergProfileTensorSum (P.filter (· ≤ compactProfileTensorCommonBound F L))
        edges companion F L = cutoffSelbergProfileTensorSum P edges companion F L ∧
    cutoffTotientSelbergProfileTensorSum (P.filter (· ≤ compactProfileTensorCommonBound F L))
        edges companion F L = cutoffTotientSelbergProfileTensorSum P edges companion F L := by
  classical
  unfold compactProfileTensorCommonBound
  rw [dif_pos ⟨hF, hL⟩]
  exact (exists_common_profileTensor_cutoff_stabilization F hF L hL).choose_spec.2
    P hP edges companion

def compactTotientSelbergProfileSum {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℂ :=
  cutoffTotientSelbergProfileTensorSum
    (selectedFourierPrimeCutoff select
      (boundedFourierPrimes (compactProfileTensorCommonBound F L))) edges companion F L

theorem cutoffSelbergProfileTensorSum_commonBound_eq_cutoff_of_le
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    {B : ℕ} (hB : compactProfileTensorCommonBound F L ≤ B) :
    cutoffSelbergProfileTensorSum
        (selectedFourierPrimeCutoff select
          (boundedFourierPrimes (compactProfileTensorCommonBound F L))) edges companion F L =
      cutoffSelbergProfileTensorSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion F L := by
  have hsub : boundedFourierPrimes (compactProfileTensorCommonBound F L) ⊆
      boundedFourierPrimes B := by
    intro p hp
    exact (mem_boundedFourierPrimes B p).mpr
      (((mem_boundedFourierPrimes _ p).mp hp).trans hB)
  have h := (compactProfileTensorCommonBound_spec F hF L hL
    (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
    (selectedFourierPrimeCutoff_prime select _) edges companion).1
  rw [selectedFourierPrimeCutoff_filter_eq select _ hsub] at h
  exact h

theorem compactTotientSelbergProfileSum_eq_cutoff_of_le
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    {B : ℕ} (hB : compactProfileTensorCommonBound F L ≤ B) :
    compactTotientSelbergProfileSum select edges companion F L =
      cutoffTotientSelbergProfileTensorSum
        (selectedFourierPrimeCutoff select (boundedFourierPrimes B)) edges companion F L := by
  have hsub : boundedFourierPrimes (compactProfileTensorCommonBound F L) ⊆
      boundedFourierPrimes B := by
    intro p hp
    exact (mem_boundedFourierPrimes B p).mpr
      (((mem_boundedFourierPrimes _ p).mp hp).trans hB)
  have h := (compactProfileTensorCommonBound_spec F hF L hL
    (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
    (selectedFourierPrimeCutoff_prime select _) edges companion).2
  rw [selectedFourierPrimeCutoff_filter_eq select _ hsub] at h
  exact h

theorem compactSelbergProfileSum_eq_commonBound
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    compactSelbergProfileSum select edges companion F L =
      cutoffSelbergProfileTensorSum
        (selectedFourierPrimeCutoff select
          (boundedFourierPrimes (compactProfileTensorCommonBound F L))) edges companion F L := by
  let B := max (compactSelbergPrimeBound F L) (compactProfileTensorCommonBound F L)
  exact (compactSelbergProfileSum_eq_cutoff_of_le select edges companion F hF L hL
    (B := B) (le_max_left _ _)).trans
      (cutoffSelbergProfileTensorSum_commonBound_eq_cutoff_of_le select edges companion
        F hF L hL (le_max_right _ _)).symm

end

end Erdos4b
