/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedSupport
import ErdosProblems.Erdos4b.GeneralFourierForcedProduct

/-!
# The stabilized forced profile sum as a full Euler integral

The original common profile cutoff suffices. The intermediate prime
cutoffs also contain the forced prime, and compact support then removes
all excess coefficient coordinates exactly.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

open Classical in
theorem prod_subtype_replace_eq_nat (P : Finset ℕ) (p : P) (f : ℕ → ℂ) (b : ℂ) :
    (∏ r : P, if r = p then b else f r) =
      ∏ r ∈ P, if r = p.val then b else f r := by
  simpa only [Subtype.val_inj] using Finset.prod_coe_sort P
    (fun r : ℕ ↦ if r = p.val then b else f r)

open Classical in
theorem prod_selectedFourierPrimeCutoff_forced
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : Nat.Primes) (hwp : w < p.val)
    (b : ℂ) (Q : Finset Nat.Primes) :
    (∏ r ∈ selectedFourierPrimeCutoff (fun r ↦ decide (w < r)) Q,
      if r = p.val then b else totientDoubledFourierPrimeFactor edges companion s r) =
      ∏ r ∈ Q, if r = p then b else
        roughTotientDoubledFourierPrimeFactor w edges companion s r := by
  classical
  calc
    _ = ∏ r ∈ Q.filter (fun r : Nat.Primes ↦ decide (w < r.val)),
        if r.val = p.val then b else totientDoubledFourierPrimeFactor edges companion s r :=
      Finset.prod_image (fun r hr t ht heq ↦ Subtype.ext heq)
    _ = _ := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro r hr
      by_cases heq : r = p
      · subst r
        simp only [hwp, decide_true, if_true]
      · have hv : r.val ≠ p.val := fun h ↦ heq (Subtype.ext h)
        simp only [decide_eq_true_eq, if_neg heq, if_neg hv, roughTotientDoubledFourierPrimeFactor]

theorem cutoffForcedSelbergProfileTensorSum_eq_fullEuler_integral
    {ι : Type*} [Fintype ι] (w : ℕ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (hedges : ∀ r : Nat.Primes, ∀ ij ∈ edges r, companion r = true)
    (p : Nat.Primes) (hwp : w < p.val)
    (R : ((ι ⊕ ι) → Bool → ℕ) → Prop) (force : DoubledPrimeChoice ι → Prop)
    (hR : ∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) → ∀ hpP : p.val ∈ P,
      ∀ c : P → DoubledPrimeChoice ι,
        R (doubledPrimeChoiceDivisor P c) ↔ force (c ⟨p.val, hpP⟩))
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (hcompact : ∀ ib, HasCompactSupport (laplaceFourierProfile (f ib)))
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ w)
    {B : ℕ} (hB : compactProfileTensorCommonBound (fun ib ↦ laplaceFourierProfile (f ib)) L ≤ B) :
    cutoffForcedSelbergProfileTensorSum
      (selectedFourierPrimeCutoff (fun r ↦ decide (w < r)) (boundedFourierPrimes B))
      edges companion p R (fun ib ↦ laplaceFourierProfile (f ib)) L =
      ∫ ξ, (∏' r : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion
        (doubledFourierTensorExponents L ξ) r) *
        (forcedTotientFourierPrimeFactor
          (fun c ↦ DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c)
          (doubledFourierTensorExponents L ξ) p /
          totientDoubledFourierPrimeFactor edges companion (doubledFourierTensorExponents L ξ) p *
            doubledFourierTensor f ξ) := by
  classical
  let select (r : ℕ) := decide (w < r)
  let allow (c : DoubledPrimeChoice ι) :=
    DoubledPrimeChoiceAllowed (edges p) (companion p) c ∧ force c
  obtain ⟨σ, hσ, hσL⟩ := exists_doubledFourierTensor_halfPlane L hL
  have hlim := tendsto_integral_oneForcedTotientPrimeProducts volume w edges companion allow p hwp
    (doubledFourierTensorExponents L) (continuous_doubledFourierTensorExponents L)
    (doubledFourierTensor f) (integrable_doubledFourierTensor f) hσ hw0 hw
    (fun ξ i b ↦ by rw [doubledFourierTensorExponents_re]; exact hσL i b)
  have heventual : ∀ᶠ Q : Finset Nat.Primes in atTop,
      (∫ ξ, (∏ r ∈ Q, if r = p then
        forcedTotientFourierPrimeFactor allow (doubledFourierTensorExponents L ξ) p
        else roughTotientDoubledFourierPrimeFactor w edges companion
          (doubledFourierTensorExponents L ξ) r) * doubledFourierTensor f ξ) =
      cutoffForcedSelbergProfileTensorSum
        (selectedFourierPrimeCutoff select (boundedFourierPrimes B))
        edges companion p R (fun ib ↦ laplaceFourierProfile (f ib)) L := by
    filter_upwards [eventually_ge_atTop (boundedFourierPrimes B),
      eventually_ge_atTop ({p} : Finset Nat.Primes)] with Q hQ hQp
    let P := selectedFourierPrimeCutoff select Q
    have hP : ∀ r ∈ P, r.Prime := selectedFourierPrimeCutoff_prime select Q
    have hpP : p.val ∈ P := Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hQp (Finset.mem_singleton_self p), by simpa [select]⟩, rfl⟩
    have hE : ∀ r ∈ P, ∀ ij ∈ edges r, companion r = true := fun r hr ↦ hedges ⟨r, hP r hr⟩
    have hfinite := cutoffForcedSelbergProfileTensorSum_eq_integral_finiteEulerProduct
      P hP edges companion hE ⟨p.val, hpP⟩ R force (hR P hP hpP) f L hL
    simp_rw [prod_subtype_replace_eq_nat] at hfinite
    simp_rw [show P = selectedFourierPrimeCutoff (fun r ↦ decide (w < r)) Q from rfl,
      prod_selectedFourierPrimeCutoff_forced w edges companion _ p hwp] at hfinite
    rw [← hfinite, ← cutoffForcedSelbergProfileTensorSum_filtered_eq
      P hP edges companion p R (fun ib ↦ laplaceFourierProfile (f ib)) hcompact L hL hB,
      selectedFourierPrimeCutoff_filter_eq select B hQ]
  have hc := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heventual)
  exact (tendsto_nhds_unique hlim hc).symm

end

end Erdos4b
