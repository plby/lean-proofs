/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientSupport
import ErdosProblems.Erdos4b.GeneralFourierTotientCutoffLimit
import ErdosProblems.Erdos4b.GeneralFourierFullIntegral

/-!
# Full Euler-integral representation of the compact totient sum

Dominated convergence removes the prime cutoff, and compact support
identifies the result with a finite arithmetic sum. The chosen cutoff
also has the explicit coordinate-capture property.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

theorem prod_selectedFourierPrimeCutoff_totient
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (Q : Finset Nat.Primes) :
    (∏ p ∈ selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) Q,
      totientDoubledFourierPrimeFactor edges companion s p) =
        ∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion s p := by
  classical
  calc
    _ = ∏ p ∈ Q.filter (fun p : Nat.Primes ↦ decide (w < p.val)),
        totientDoubledFourierPrimeFactor edges companion s p :=
      Finset.prod_image (fun p hp q hq h ↦ Subtype.ext h)
    _ = _ := by
      rw [Finset.prod_filter]
      simp only [roughTotientDoubledFourierPrimeFactor, decide_eq_true_eq]

theorem exists_compactProfileTensor_fullTotientEuler_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ p : Nat.Primes, ∀ ij ∈ edges p, companion p = true)
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w) :
    ∃ B : ℕ,
      (∀ d : (ι ⊕ ι) → Bool → ℕ, (∀ i b, 0 < d i b) →
        doubledSelbergProfileTensor (fun ib ↦ laplaceFourierProfile (f ib)) L d ≠ 0 →
          ∀ i b, d i b ≤ B) ∧
      cutoffTotientSelbergProfileTensorSum
        (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes B))
        edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏' p : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ := by
  classical
  let select (p : ℕ) := decide (w < p)
  obtain ⟨B, hcapture, hB⟩ := exists_common_profileTensor_cutoff_stabilization
    (fun ib ↦ laplaceFourierProfile (f ib)) hcompact L hL
  obtain ⟨σ, hσ, hσL⟩ := exists_doubledFourierTensor_halfPlane L hL
  refine ⟨B, hcapture, ?_⟩
  have hlimit := tendsto_integral_roughTotientDoubledFourierPrimeProducts volume w edges companion
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ hw0 hw
    (fun ξ i b ↦ by rw [doubledFourierTensorExponents_re]; exact hσL i b)
  have heventual : ∀ᶠ Q : Finset Nat.Primes in atTop,
      (∫ ξ, (∏ p ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion
        (doubledFourierTensorExponents L ξ) p) * doubledFourierTensor f ξ) =
      cutoffTotientSelbergProfileTensorSum
        (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion (fun ib ↦ laplaceFourierProfile (f ib)) L := by
    filter_upwards [eventually_ge_atTop (boundedFourierPrimes B)] with Q hQ
    have hP := selectedFourierPrimeCutoff_prime select Q
    have hE : ∀ p ∈ selectedFourierPrimeCutoff select Q, ∀ ij ∈ edges p, companion p = true :=
      fun p hp ↦ hedges ⟨p, hP p hp⟩
    have hfinite := cutoffTotientSelbergProfileTensorSum_eq_integral_finiteEulerProduct
      (selectedFourierPrimeCutoff select Q) hP edges companion hE f L hL
    simp only [select] at hfinite
    simp_rw [prod_selectedFourierPrimeCutoff_totient w edges companion] at hfinite
    rw [← hfinite, ← (hB (selectedFourierPrimeCutoff select Q) hP edges companion).2,
      selectedFourierPrimeCutoff_filter_eq select B hQ]
  have hconstant := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heventual)
  exact (tendsto_nhds_unique hlimit hconstant).symm

end

end Erdos4b
