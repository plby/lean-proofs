/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFullIntegral

/-!
# A canonical finite prime cutoff for compact profiles

The chosen cutoff depends only on the profiles and their logarithmic
scales, not on the affine graph or auxiliary prime. Every larger cutoff
gives exactly the same coefficient sum.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def compactSelbergPrimeBound {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℕ := by
  classical
  exact if h : (∀ ib, HasCompactSupport (F ib)) ∧ (∀ i b, 0 < L i b) then
    (exists_cutoffSelbergProfileTensorSum_stabilization F h.1 L h.2).choose
  else 0

theorem compactSelbergPrimeBound_spec {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) :
    cutoffSelbergProfileTensorSum (P.filter (· ≤ compactSelbergPrimeBound F L))
        edges companion F L = cutoffSelbergProfileTensorSum P edges companion F L := by
  classical
  unfold compactSelbergPrimeBound
  rw [dif_pos ⟨hF, hL⟩]
  exact (exists_cutoffSelbergProfileTensorSum_stabilization F hF L hL).choose_spec
    P hP edges companion

def compactSelbergProfileSum {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ) : ℂ :=
  cutoffSelbergProfileTensorSum
    (selectedFourierPrimeCutoff select (boundedFourierPrimes (compactSelbergPrimeBound F L)))
    edges companion F L

theorem compactSelbergProfileSum_eq_cutoff_of_le
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (hF : ∀ ib, HasCompactSupport (F ib))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    {B : ℕ} (hB : compactSelbergPrimeBound F L ≤ B) :
    compactSelbergProfileSum select edges companion F L =
      cutoffSelbergProfileTensorSum (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion F L := by
  have hsub : boundedFourierPrimes (compactSelbergPrimeBound F L) ⊆ boundedFourierPrimes B := by
    intro p hp
    exact (mem_boundedFourierPrimes B p).mpr
      (((mem_boundedFourierPrimes _ p).mp hp).trans hB)
  have h := compactSelbergPrimeBound_spec F hF L hL
    (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
    (selectedFourierPrimeCutoff_prime select _) edges companion
  rw [selectedFourierPrimeCutoff_filter_eq select _ hsub] at h
  exact h

theorem compactSelbergProfileSum_eq_fullEuler_integral
    {ι : Type*} [Fintype ι]
    (select : ℕ → Bool) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b) :
    compactSelbergProfileSum select edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏' p : Nat.Primes, selectedDoubledFourierPrimeFactor select edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ := by
  classical
  let F := fun ib ↦ laplaceFourierProfile (f ib)
  let B := compactSelbergPrimeBound F L
  obtain ⟨σ, hσ, hσL⟩ := exists_doubledFourierTensor_halfPlane L hL
  have hlimit := tendsto_integral_selectedDoubledFourierPrimeProducts volume select edges companion
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ
    (fun ξ i b ↦ by rw [doubledFourierTensorExponents_re]; exact hσL i b)
  have heventual : ∀ᶠ Q : Finset Nat.Primes in atTop,
      (∫ ξ, (∏ p ∈ Q, selectedDoubledFourierPrimeFactor select edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ) =
      compactSelbergProfileSum select edges companion F L := by
    filter_upwards [eventually_ge_atTop (boundedFourierPrimes B)] with Q hQ
    have hP := selectedFourierPrimeCutoff_prime select Q
    have hE : ∀ p ∈ selectedFourierPrimeCutoff select Q, ∀ ij ∈ edges p, companion p = true :=
      fun p hp ↦ hedges ⟨p, hP p hp⟩
    have hfinite := cutoffSelbergProfileTensorSum_eq_integral_finiteEulerProduct
      (selectedFourierPrimeCutoff select Q) hP edges companion hE f L hL
    simp_rw [prod_selectedFourierPrimeCutoff select edges companion] at hfinite
    rw [← hfinite, ← compactSelbergPrimeBound_spec F hcompact L hL
      (selectedFourierPrimeCutoff select Q) hP edges companion,
      selectedFourierPrimeCutoff_filter_eq select B hQ]
    rfl
  have hconstant := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heventual)
  exact (tendsto_nhds_unique hlimit hconstant).symm

end

end Erdos4b
