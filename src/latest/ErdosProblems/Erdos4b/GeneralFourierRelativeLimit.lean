/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRelativeProduct

/-!
# The full rough-prime relative Fourier product

The cutoff-independent bound on finite sums of norm errors gives absolute
convergence of the relative product. Its distance from one is bounded by
the same explicit generic and exceptional-prime error envelope.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def roughDoubledFourierRelativeFactor {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  if w < p then doubledFourierRelativeFactor edges companion s p else 1

def doubledFourierRelativeErrorBound (ι : Type*) [Fintype ι] (M w : ℕ) (σ : ℝ) : ℝ :=
  2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
    (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) * (2 / (w : ℝ)) +
      (10 * (Fintype.card ι : ℝ) * σ) * roughPrimeLogDivisorMass M w)

theorem sum_norm_roughDoubledFourierRelativeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} {σ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ)
    (Q : Finset Nat.Primes) :
    (∑ p ∈ Q, ‖roughDoubledFourierRelativeFactor w edges companion s p - 1‖) ≤
      doubledFourierRelativeErrorBound ι M w σ := by
  classical
  let R := Q.filter fun p : Nat.Primes ↦ w < p.val
  let P := R.image (fun p : Nat.Primes ↦ p.val)
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have hrough : ∀ p ∈ P, w < p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  have hcardP : ∀ p ∈ P, 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p := by
    intro p hp
    exact hcard.trans (by exact_mod_cast (hrough p hp).le)
  have hedgeP : ∀ p ∈ P, (edges p).card ≤ Fintype.card ι :=
    fun p hp ↦ hedgeCard ⟨p, hP p hp⟩ (hrough p hp)
  have hgenericP : ∀ p ∈ P, ¬p ∣ M → edges p = ∅ ∧ companion p = true :=
    fun p hp ↦ hgeneric ⟨p, hP p hp⟩ (hrough p hp)
  calc
    _ = ∑ p ∈ R, ‖doubledFourierRelativeFactor edges companion s p - 1‖ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hwp : w < p.val <;> simp [roughDoubledFourierRelativeFactor, hwp]
    _ = ∑ p ∈ P, ‖doubledFourierRelativeFactor edges companion s p - 1‖ := by
      exact (Finset.sum_image (s := R) (g := fun p : Nat.Primes ↦ p.val)
        (f := fun p ↦ ‖doubledFourierRelativeFactor edges companion s p - 1‖)
        (fun p hp q hq h ↦ Subtype.ext h)).symm
    _ ≤ _ := sum_norm_doubledFourierRelativeFactor_sub_one_le edges companion s P hP
      hM hw hσ hrough hcardP hedgeP hgenericP hRe hNorm

theorem summable_norm_roughDoubledFourierRelativeFactor_sub_one
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} {σ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    Summable (fun p : Nat.Primes ↦
      ‖roughDoubledFourierRelativeFactor w edges companion s p - 1‖) := by
  exact summable_of_sum_le (fun p ↦ norm_nonneg _)
    (sum_norm_roughDoubledFourierRelativeFactor_sub_one_le edges companion s
      hM hw hσ hcard hedgeCard hgeneric hRe hNorm)

theorem multipliable_roughDoubledFourierRelativeFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} {σ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    Multipliable (fun p : Nat.Primes ↦
      roughDoubledFourierRelativeFactor w edges companion s p) := by
  have hsum := summable_norm_roughDoubledFourierRelativeFactor_sub_one edges companion s
    hM hw hσ hcard hedgeCard hgeneric hRe hNorm
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsum

theorem norm_tprod_roughDoubledFourierRelativeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) {M w : ℕ} {σ : ℝ}
    (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    ‖(∏' p : Nat.Primes, roughDoubledFourierRelativeFactor w edges companion s p) - 1‖ ≤
      Real.exp (doubledFourierRelativeErrorBound ι M w σ) - 1 := by
  have hlim : Tendsto (fun Q : Finset Nat.Primes ↦
      ∏ p ∈ Q, roughDoubledFourierRelativeFactor w edges companion s p) atTop
      (𝓝 (∏' p : Nat.Primes, roughDoubledFourierRelativeFactor w edges companion s p)) :=
    (multipliable_roughDoubledFourierRelativeFactor edges companion s
      hM hw hσ hcard hedgeCard hgeneric hRe hNorm).hasProd
  apply le_of_tendsto (hlim.sub_const 1).norm
  apply Eventually.of_forall
  intro Q
  have hsum := sum_norm_roughDoubledFourierRelativeFactor_sub_one_le edges companion s
    hM hw hσ hcard hedgeCard hgeneric hRe hNorm Q
  have hprod := norm_prod_one_add_error_le Q
    (fun p : Nat.Primes ↦ roughDoubledFourierRelativeFactor w edges companion s p - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem tendsto_doubledFourierRelativeErrorBound_zero
    (ι : Type*) [Fintype ι] {α : Type*} {l : Filter α}
    (M w : α → ℕ) (σ : α → ℝ)
    (hw : Tendsto w l atTop)
    (hmass : Tendsto (fun x ↦ σ x * roughPrimeLogDivisorMass (M x) (w x)) l (𝓝 0)) :
    Tendsto (fun x ↦ doubledFourierRelativeErrorBound ι (M x) (w x) (σ x)) l (𝓝 0) := by
  have hwr : Tendsto (fun x ↦ (w x : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hw
  have hrec : Tendsto (fun x ↦ (2 : ℝ) / (w x : ℝ)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hwr
  have h := ((hrec.const_mul (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)))).add
    (hmass.const_mul (10 * (Fintype.card ι : ℝ)))).const_mul
      (2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι))
  simpa only [doubledFourierRelativeErrorBound, mul_assoc, mul_zero, add_zero] using h

theorem exists_uniform_doubledFourierRelativeErrorBound_log_bound
    (ι : Type*) [Fintype ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M w : ℕ} {B L σ : ℝ},
      0 < M → 0 ≤ B → 1 ≤ L → 0 ≤ σ → Real.log M ≤ B * L →
        doubledFourierRelativeErrorBound ι M w σ ≤
          2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
            (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) * (2 / (w : ℝ)) +
              (10 * (Fintype.card ι : ℝ) * σ) * (Real.log (L + 1) + C + B)) := by
  obtain ⟨C, hC, hmass⟩ := exists_uniform_roughPrimeLogDivisorMass_log_bound
  refine ⟨C, hC, ?_⟩
  intro M w B L σ hM hB hL hσ hlog
  unfold doubledFourierRelativeErrorBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hmass hM hB hL hlog w) (by positivity))

end

end Erdos4b
