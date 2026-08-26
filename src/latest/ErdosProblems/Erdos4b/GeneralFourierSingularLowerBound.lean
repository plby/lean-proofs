/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSingularProduct
import ErdosProblems.Erdos4b.GeneralFourierRelativeProduct

/-!
# A uniform lower bound for the full singular normalization

The exceptional prime factors only increase the norms of the positive
real singular factors. The generic product is uniformly close to one
once the pre-sieve cutoff is large. This gives a lower bound independent
of the size and prime factors of the exceptional integer.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

def genericFourierSingularErrorBound (n w : ℕ) : ℝ :=
  (2 : ℝ) ^ n * pairProductErrorConstant n * (2 / (w : ℝ))

theorem norm_genericFourierSingularFactor_sub_one_le (n : ℕ) {p : ℕ}
    (hp : 2 ≤ (p : ℝ)) (hcard : 7 * (n : ℝ) ≤ p) :
    ‖genericFourierSingularFactor n p - 1‖ ≤
      (2 : ℝ) ^ n * (pairProductErrorConstant n / (p : ℝ) ^ 2) := by
  simpa only [Complex.ofReal_natCast, sub_zero, norm_zero, zero_div, add_zero,
    genericFourierSingularFactor] using norm_zeroExponentSingularFactor_sub_one_le n hp hcard 0

theorem norm_prod_genericFourierSingularFactor_sub_one_le
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {w : ℕ} (hw : 0 < w)
    (hrough : ∀ p ∈ P, w < p) (hcard : 7 * (n : ℝ) ≤ w) :
    ‖(∏ p ∈ P, genericFourierSingularFactor n p) - 1‖ ≤
      Real.exp (genericFourierSingularErrorBound n w) - 1 := by
  have hsum : (∑ p ∈ P, ‖genericFourierSingularFactor n p - 1‖) ≤
      genericFourierSingularErrorBound n w := by
    calc
      _ ≤ ∑ p ∈ P, (2 : ℝ) ^ n * (pairProductErrorConstant n / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        exact norm_genericFourierSingularFactor_sub_one_le n
          (by exact_mod_cast (hP p hp).two_le)
          (hcard.trans (by exact_mod_cast (hrough p hp).le))
      _ = (2 : ℝ) ^ n * pairProductErrorConstant n *
          (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) := by
        simp only [Finset.mul_sum, mul_one_div, mul_div_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (finite_rough_reciprocalSquare_sum_le P hw hrough)
        (mul_nonneg (by positivity) (pairProductErrorConstant_nonneg n))
  have hprod := norm_prod_one_add_error_le P (fun p ↦ genericFourierSingularFactor n p - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem generic_bound_le_norm_prod_doubledFourierSingularFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {w : ℕ} (hw : 0 < w)
    (hrough : ∀ p ∈ P, w < p) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w) :
    2 - Real.exp (genericFourierSingularErrorBound (Fintype.card (ι ⊕ ι)) w) ≤
      ‖∏ p ∈ P, doubledFourierSingularFactor edges companion p‖ := by
  have hclose := norm_prod_genericFourierSingularFactor_sub_one_le
    (Fintype.card (ι ⊕ ι)) P hP hw hrough hcard
  have htri := norm_sub_norm_le (1 : ℂ)
    (∏ p ∈ P, genericFourierSingularFactor (Fintype.card (ι ⊕ ι)) p)
  rw [norm_one, norm_sub_rev] at htri
  have hle : ‖∏ p ∈ P, genericFourierSingularFactor (Fintype.card (ι ⊕ ι)) p‖ ≤
      ‖∏ p ∈ P, doubledFourierSingularFactor edges companion p‖ := by
    simp only [norm_prod]
    apply Finset.prod_le_prod (fun p hp ↦ norm_nonneg _)
    intro p hp
    have hpw : (w : ℝ) ≤ p := by exact_mod_cast (hrough p hp).le
    have hn : (0 : ℝ) ≤ Fintype.card (ι ⊕ ι) := Nat.cast_nonneg _
    exact norm_genericFourierSingularFactor_le edges companion
      (by exact_mod_cast (hP p hp).two_le) (by linarith)
  linarith

theorem generic_bound_le_norm_prod_roughDoubledFourierSingularFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {w : ℕ} (hw : 0 < w) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (Q : Finset Nat.Primes) :
    2 - Real.exp (genericFourierSingularErrorBound (Fintype.card (ι ⊕ ι)) w) ≤
      ‖∏ p ∈ Q, roughDoubledFourierSingularFactor w edges companion p‖ := by
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
  have heq : (∏ p ∈ P, doubledFourierSingularFactor edges companion p) =
      ∏ p ∈ Q, roughDoubledFourierSingularFactor w edges companion p := by
    calc
      _ = ∏ p ∈ R, doubledFourierSingularFactor edges companion p :=
        Finset.prod_image (fun p hp q hq h ↦ Subtype.ext h)
      _ = _ := by rw [Finset.prod_filter]; rfl
  have h := generic_bound_le_norm_prod_doubledFourierSingularFactor
    edges companion P hP hw hrough hcard
  exact heq ▸ h

theorem generic_bound_le_norm_tprod_roughDoubledFourierSingularFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {M w : ℕ} (hM : 0 < M) (hw : 0 < w) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ w)
    (hedgeCard : ∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) :
    2 - Real.exp (genericFourierSingularErrorBound (Fintype.card (ι ⊕ ι)) w) ≤
      ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖ := by
  have h := multipliable_roughDoubledFourierSingularFactor
    edges companion hM hcard hedgeCard hgeneric
  apply ge_of_tendsto h.hasProd.norm
  apply Eventually.of_forall
  intro Q
  simpa only [norm_prod] using
    generic_bound_le_norm_prod_roughDoubledFourierSingularFactor edges companion hw hcard Q

theorem tendsto_genericFourierSingularErrorBound_zero (n : ℕ) :
    Tendsto (genericFourierSingularErrorBound n) atTop (𝓝 0) := by
  have hrec : Tendsto (fun w : ℕ ↦ (2 : ℝ) / (w : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  change Tendsto (fun w : ℕ ↦
    (2 : ℝ) ^ n * pairProductErrorConstant n * (2 / (w : ℝ))) atTop (𝓝 0)
  simpa only [mul_zero] using
    hrec.const_mul ((2 : ℝ) ^ n * pairProductErrorConstant n)

theorem exists_genericFourierSingularErrorBound_cutoff (n : ℕ) :
    ∃ W : ℕ, ∀ w ≥ W, 0 < w ∧ 7 * (n : ℝ) ≤ w ∧
      Real.exp (genericFourierSingularErrorBound n w) ≤ 3 / 2 := by
  have hlim : Tendsto (fun w ↦ Real.exp (genericFourierSingularErrorBound n w))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp
        (tendsto_genericFourierSingularErrorBound_zero n)
  obtain ⟨W, hW⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num :
    (1 : ℝ) < 3 / 2)))
  refine ⟨max (7 * n + 1) W, fun w hw ↦ ?_⟩
  have hnw : 7 * n + 1 ≤ w := (le_max_left _ _).trans hw
  refine ⟨by omega, ?_, (hW w ((le_max_right _ _).trans hw)).le⟩
  exact_mod_cast (show 7 * n ≤ w by omega)

theorem exists_uniform_half_le_norm_tprod_roughDoubledFourierSingularFactor
    (ι : Type*) [Fintype ι] :
    ∃ W : ℕ, ∀ {M w : ℕ} (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool),
      W ≤ w → 0 < M →
      (∀ p : Nat.Primes, w < p → (edges p).card ≤ Fintype.card ι) →
      (∀ p : Nat.Primes, w < p → ¬p.val ∣ M → edges p = ∅ ∧ companion p = true) →
      (1 : ℝ) / 2 ≤
        ‖∏' p : Nat.Primes, roughDoubledFourierSingularFactor w edges companion p‖ := by
  obtain ⟨W, hW⟩ := exists_genericFourierSingularErrorBound_cutoff (Fintype.card (ι ⊕ ι))
  refine ⟨W, fun {M w} edges companion hw hM hedgeCard hgeneric ↦ ?_⟩
  obtain ⟨hwpos, hcard, hbound⟩ := hW w hw
  have h := generic_bound_le_norm_tprod_roughDoubledFourierSingularFactor
    edges companion hM hwpos hcard hedgeCard hgeneric
  linarith

end

end Erdos4b
