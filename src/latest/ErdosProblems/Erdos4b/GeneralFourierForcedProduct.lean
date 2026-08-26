/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierForcedPrimeFactor
import ErdosProblems.Erdos4b.GeneralFourierTotientCutoffLimit

/-!
# Replacing one Euler factor and passing to the full integral

The forced/unforced quotient is bounded uniformly at all frequencies.
It can therefore be absorbed into the integrable tensor before applying
the proved dominated-convergence theorem for the unforced product.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

open Classical in
theorem prod_replace_one_eq_div_mul {ι : Type*} (Q : Finset ι)
    (f : ι → ℂ) {p : ι} (hp : p ∈ Q) (hfp : f p ≠ 0) (b : ℂ) :
    (∏ r ∈ Q, if r = p then b else f r) = b / f p * ∏ r ∈ Q, f r := by
  rw [← Finset.mul_prod_erase Q (fun r ↦ if r = p then b else f r) hp,
    ← Finset.mul_prod_erase Q f hp, if_pos rfl, ← mul_assoc, div_mul_cancel₀ _ hfp]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  exact if_neg (Finset.mem_erase.mp hr).1

theorem continuous_forcedTotientFourierPrimeFactor
    {ι : Type*} [Fintype ι] (allow : DoubledPrimeChoice ι → Prop) (p : ℕ) :
    Continuous (fun s : (ι ⊕ ι) → Bool → ℂ ↦ forcedTotientFourierPrimeFactor allow s p) := by
  classical
  unfold forcedTotientFourierPrimeFactor forcedTotientLocalFactor doubledPrimeChoiceNumerator
  apply continuous_finsetSum
  intro c hc
  by_cases ha : allow c
  · simp only [if_pos ha]
    apply Continuous.div_const
    apply continuous_finsetProd
    intro i hi
    apply continuous_finsetProd
    intro b hb
    by_cases hinc : doubledPrimeChoiceIncidence c i b
    · simp only [if_pos hinc, primeFourierPower]
      fun_prop
    · simp only [if_neg hinc]
      exact continuous_const
  · simp only [if_neg ha]
    exact continuous_const

theorem continuous_forcedTotientFourierQuotient_comp
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (allow : DoubledPrimeChoice ι → Prop)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : Nat.Primes)
    (S : X → (ι ⊕ ι) → Bool → ℂ) (hS : Continuous S)
    (hs : ∀ x i b, 0 ≤ (S x i b).re)
    (hp : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ (p : ℝ)) :
    Continuous (fun x ↦ forcedTotientFourierPrimeFactor allow (S x) p /
      totientDoubledFourierPrimeFactor edges companion (S x) p) := by
  have hden : Continuous (fun x ↦ totientDoubledFourierPrimeFactor edges companion (S x) p) := by
    have hc := (continuous_roughTotientDoubledFourierPrimeFactor 0 edges companion p).comp hS
    simpa only [roughTotientDoubledFourierPrimeFactor, if_pos p.property.pos,
      Function.comp_def] using hc
  apply ((continuous_forcedTotientFourierPrimeFactor allow p).comp hS).div hden
  intro x
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (half_le_norm_totientDoubledFourierPrimeFactor edges companion (S x) (hs x) p hp))

open Classical in
theorem tendsto_integral_oneForcedTotientPrimeProducts
    {ι X : Type*} [Fintype ι] [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (allow : DoubledPrimeChoice ι → Prop) (p : Nat.Primes) (hwp : w < p.val)
    (S : X → (ι ⊕ ι) → Bool → ℂ) (hS : Continuous S)
    (G : X → ℂ) (hG : Integrable G μ) {σ : ℝ} (hσ : 1 < σ)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ w)
    (hRe : ∀ x i b, σ - 1 ≤ (S x i b).re) :
    Tendsto (fun Q : Finset Nat.Primes ↦ ∫ x,
      (∏ r ∈ Q, if r = p then forcedTotientFourierPrimeFactor allow (S x) p
        else roughTotientDoubledFourierPrimeFactor w edges companion (S x) r) * G x ∂μ)
      atTop (𝓝 (∫ x,
        (∏' r : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion (S x) r) *
          (forcedTotientFourierPrimeFactor allow (S x) p /
            totientDoubledFourierPrimeFactor edges companion (S x) p * G x) ∂μ)) := by
  have hs : ∀ x i b, 0 ≤ (S x i b).re := fun x i b ↦ (by linarith : 0 ≤ σ - 1).trans (hRe x i b)
  have hp : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ (p : ℝ) :=
    hw.trans (by exact_mod_cast hwp.le)
  let H (x : X) : ℂ := forcedTotientFourierPrimeFactor allow (S x) p /
    totientDoubledFourierPrimeFactor edges companion (S x) p
  have hH : Continuous H := continuous_forcedTotientFourierQuotient_comp
    allow edges companion p S hS hs hp
  have hHG : Integrable (fun x ↦ H x * G x) μ := by
    apply (hG.norm.const_mul (4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ))).mono'
      (hH.aestronglyMeasurable.mul hG.aestronglyMeasurable)
    apply ae_of_all
    intro x
    change ‖H x * G x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_forcedTotientFourierPrimeFactor_div_le allow edges companion (S x) (hs x) p hp)
      (norm_nonneg _)
  have hbase := tendsto_integral_roughTotientDoubledFourierPrimeProducts μ w edges companion
    S hS (fun x ↦ H x * G x) hHG hσ hw0 (by linarith) hRe
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop ({p} : Finset Nat.Primes)] with Q hQ
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hmem : p ∈ Q := hQ (Finset.mem_singleton_self p)
  have hne : roughTotientDoubledFourierPrimeFactor w edges companion (S x) p ≠ 0 := by
    rw [roughTotientDoubledFourierPrimeFactor, if_pos hwp]
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (half_le_norm_totientDoubledFourierPrimeFactor edges companion (S x) (hs x) p hp))
  dsimp only
  have hid := prod_replace_one_eq_div_mul Q
    (fun r : Nat.Primes ↦ roughTotientDoubledFourierPrimeFactor w edges companion (S x) r)
    hmem hne (forcedTotientFourierPrimeFactor allow (S x) p)
  have hid' := congrArg (fun z : ℂ ↦ z * G x) hid
  have hfp : roughTotientDoubledFourierPrimeFactor w edges companion (S x) p =
      totientDoubledFourierPrimeFactor edges companion (S x) p := if_pos hwp
  rw [hfp] at hid'
  calc
    _ = (forcedTotientFourierPrimeFactor allow (S x) p /
        totientDoubledFourierPrimeFactor edges companion (S x) p *
          ∏ r ∈ Q, roughTotientDoubledFourierPrimeFactor w edges companion (S x) r) * G x := by
      dsimp only [H]
      ring
    _ = _ := by
      refine hid'.symm.trans ?_
      congr 1
      apply Finset.prod_congr rfl
      intro r hr
      by_cases hrp : r = p
      · simp only [if_pos hrp]
      · simp only [if_neg hrp]

end

end Erdos4b
