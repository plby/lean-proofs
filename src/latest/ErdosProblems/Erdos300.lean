/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 300.
https://www.erdosproblems.com/forum/thread/300

Informal authors:
- Yang P. Liu
- Mehtaab Sawhney

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos300.md
-/
/-
This is a Lean formalization of the solution to Erdős Problem 300.
https://www.erdosproblems.com/300

Informal authors:
- Yang P. Liu
- Mehtaab Sawhney

Reference:
- Y. P. Liu and M. Sawhney, "On further questions regarding unit fractions",
  arXiv:2404.07113 (2024), Theorem 1.3.
-/
import ErdosProblems.Erdos299
import ErdosProblems.Erdos297.FiniteHoeffding
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos300

open Filter Real
open scoped ArithmeticFunction.omega BigOperators Topology
open UnitFractions

/-- A finite set of denominators is admissible for Erdős Problem 300 when none
of its subsets has reciprocal sum exactly one. -/
def AvoidsOne (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → rec_sum B ≠ 1

/-- The finite family over which the extremal function is maximized. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter AvoidsOne

/-- `erdos300Max N` is the exact maximum cardinality in Erdős Problem 300. -/
noncomputable def erdos300Max (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/-- Every admissible set has cardinality at most the extremal function. -/
theorem card_le_erdos300Max {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) (hA : AvoidsOne A) :
    A.card ≤ erdos300Max N := by
  classical
  exact Finset.le_sup (by simpa [candidateSets] using ⟨hAN, hA⟩)

/-- The finite maximum is attained. -/
theorem exists_extremizer (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ AvoidsOne A ∧
      A.card = erdos300Max N := by
  classical
  have hne : (candidateSets N).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidateSets, AvoidsOne]
  obtain ⟨A, hmem, hsup⟩ :=
    Finset.exists_mem_eq_sup (candidateSets N) hne Finset.card
  refine ⟨A, ?_, ?_, hsup.symm⟩
  · exact Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1
  · exact (Finset.mem_filter.mp hmem).2

/-- The explicit interval used for the lower bound.  Its left endpoint is one
integer beyond `ceil (N / e)`, which makes its total reciprocal mass strictly
less than one. -/
noncomputable def lowerCutoff (N : ℕ) : ℕ :=
  ⌈(N : ℝ) / Real.exp 1⌉₊ + 1

noncomputable def lowerSet (N : ℕ) : Finset ℕ :=
  Finset.Ioc (lowerCutoff N) N

private lemma sum_Ico_inv_succ_le_log_ratio
    {m U : ℕ} (hm : 1 ≤ m) (hmU : m ≤ U) :
    (∑ k ∈ Finset.Ico m U, (((k + 1 : ℕ) : ℝ))⁻¹) ≤
      Real.log ((U : ℝ) / (m : ℝ)) := by
  calc
    (∑ k ∈ Finset.Ico m U, (((k + 1 : ℕ) : ℝ))⁻¹) ≤
        ∑ k ∈ Finset.Ico m U,
          (Real.log (k + 1 : ℕ) - Real.log k) := by
            apply Finset.sum_le_sum
            intro k hk
            have hkData := Finset.mem_Ico.mp hk
            have hkPos : (0 : ℝ) < k := by
              exact_mod_cast hm.trans hkData.1
            have hksPos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
            have hratioPos :
                0 < ((k + 1 : ℕ) : ℝ) / (k : ℝ) :=
              div_pos hksPos hkPos
            have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
            rw [Real.log_div hksPos.ne' hkPos.ne'] at hlog
            have hinv :
                ((((k + 1 : ℕ) : ℝ) / (k : ℝ))⁻¹) =
                  (k : ℝ) / (k + 1 : ℕ) := by
              field_simp
            rw [hinv] at hlog
            have hid :
                (((k + 1 : ℕ) : ℝ))⁻¹ =
                  1 - (k : ℝ) / (k + 1 : ℕ) := by
              push_cast
              field_simp
              ring
            rw [hid]
            exact hlog
    _ = Real.log U - Real.log m := by
          exact Finset.sum_Ico_sub (fun k : ℕ => Real.log k) hmU
    _ = Real.log ((U : ℝ) / (m : ℝ)) := by
          rw [Real.log_div
            (by exact_mod_cast (show U ≠ 0 by omega))
            (by exact_mod_cast (show m ≠ 0 by omega))]

private lemma cast_rec_sum_Ioc (a N : ℕ) :
    (rec_sum (Finset.Ioc a N) : ℝ) =
      ∑ k ∈ Finset.Ico a N, (((k + 1 : ℕ) : ℝ))⁻¹ := by
  rw [rec_sum, Rat.cast_sum]
  simp_rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, one_div]
  apply Finset.sum_bij (fun n _ => n - 1)
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    omega
  · intro k hk
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc, Finset.mem_Ico] at hk ⊢
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [Nat.sub_add_cancel (by omega)]

/-- The interval `(ceil (N/e) + 1, N]` has total reciprocal mass below one. -/
theorem lowerSet_rec_sum_lt_one (N : ℕ) :
    (rec_sum (lowerSet N) : ℝ) < 1 := by
  classical
  let m : ℕ := lowerCutoff N
  by_cases hmN : m ≤ N
  · have hm : 1 ≤ m := by simp [m, lowerCutoff]
    have hsum :
        (rec_sum (lowerSet N) : ℝ) ≤
          Real.log ((N : ℝ) / (m : ℝ)) := by
      rw [lowerSet, show lowerCutoff N = m by rfl, cast_rec_sum_Ioc]
      exact sum_Ico_inv_succ_le_log_ratio hm hmN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < m) hmN
    have hmgt : (N : ℝ) / Real.exp 1 < (m : ℝ) := by
      dsimp [m, lowerCutoff]
      have hceil : (N : ℝ) / Real.exp 1 ≤ (⌈(N : ℝ) / Real.exp 1⌉₊ : ℕ) :=
        Nat.le_ceil _
      push_cast at hceil ⊢
      linarith
    have hratio : (N : ℝ) / (m : ℝ) < Real.exp 1 := by
      have hmpos : (0 : ℝ) < m := by positivity
      rw [div_lt_iff₀ hmpos]
      have h := (div_lt_iff₀ (Real.exp_pos 1)).mp hmgt
      simpa [mul_comm] using h
    have hlog : Real.log ((N : ℝ) / (m : ℝ)) < 1 := by
      have hratioPos : 0 < (N : ℝ) / (m : ℝ) := by positivity
      calc
        Real.log ((N : ℝ) / (m : ℝ)) < Real.log (Real.exp 1) :=
          Real.strictMonoOn_log hratioPos (Real.exp_pos 1) hratio
        _ = 1 := Real.log_exp 1
    exact hsum.trans_lt hlog
  · have hempty : lowerSet N = ∅ := by
      rw [lowerSet, Finset.Ioc_eq_empty]
      simpa [m] using le_of_not_ge hmN
    simp [hempty]

/-- The lower-bound interval is admissible. -/
theorem lowerSet_avoidsOne (N : ℕ) : AvoidsOne (lowerSet N) := by
  intro B hB hrec
  have hmono : (rec_sum B : ℝ) ≤ rec_sum (lowerSet N) := by
    exact_mod_cast rec_sum_mono hB
  have hone : (rec_sum B : ℝ) = 1 := by exact_mod_cast hrec
  linarith [lowerSet_rec_sum_lt_one N]

/-- The explicit lower-bound set really lies in `[1,N]`. -/
theorem lowerSet_subset_Icc (N : ℕ) :
    lowerSet N ⊆ Finset.Icc 1 N := by
  intro n hn
  simp only [lowerSet, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
  exact ⟨by omega, hn.2⟩

private theorem lowerCutoff_ratio_tendsto :
    Tendsto (fun N : ℕ => (lowerCutoff N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 / Real.exp 1)) := by
  have hc : 0 ≤ (Real.exp 1)⁻¹ := inv_nonneg.mpr (Real.exp_pos 1).le
  have hceil :
      Tendsto
        (fun N : ℕ =>
          ((⌈(Real.exp 1)⁻¹ * (N : ℝ)⌉₊ : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 (Real.exp 1)⁻¹) :=
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc).comp
      tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hadd := hceil.add hone
  rw [add_zero] at hadd
  rw [one_div]
  apply hadd.congr'
  filter_upwards with N
  simp only [lowerCutoff, Nat.cast_add, Nat.cast_one, add_div]
  rw [show (N : ℝ) / Real.exp 1 = (Real.exp 1)⁻¹ * (N : ℝ) by
    rw [div_eq_mul_inv, mul_comm]]

private theorem eventually_lowerCutoff_le :
    ∀ᶠ N : ℕ in atTop, lowerCutoff N ≤ N := by
  have hc_lt : (1 / Real.exp 1 : ℝ) < 1 := by
    rw [one_div, inv_lt_one₀ (Real.exp_pos 1)]
    exact Real.one_lt_exp_iff.mpr zero_lt_one
  have hev :=
    lowerCutoff_ratio_tendsto.eventually (eventually_lt_nhds hc_lt)
  filter_upwards [hev, eventually_ge_atTop 1] with N hratio hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcast : (lowerCutoff N : ℝ) < N :=
    (div_lt_one hNpos).mp hratio
  exact_mod_cast hcast.le

/-- The cardinality of the explicit construction has the conjectured limiting
density `1 - 1/e`. -/
theorem lowerSet_card_ratio_tendsto :
    Tendsto (fun N : ℕ => ((lowerSet N).card : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 - 1 / Real.exp 1)) := by
  have hself : Tendsto (fun N : ℕ => (N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    exact tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp [show N ≠ 0 by omega])
  have hlim := hself.sub lowerCutoff_ratio_tendsto
  apply hlim.congr'
  filter_upwards [eventually_lowerCutoff_le] with N hcut
  rw [lowerSet, Nat.card_Ioc, Nat.cast_sub hcut]
  ring

/-- The elementary construction supplies the lower half of the asymptotic
formula for the extremal function. -/
theorem eventually_erdos300Max_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      1 - 1 / Real.exp 1 - ε < (erdos300Max N : ℝ) / (N : ℝ) := by
  have hclose := lowerSet_card_ratio_tendsto.eventually
    (Ioi_mem_nhds (sub_lt_self (1 - 1 / Real.exp 1) hε))
  filter_upwards [hclose, eventually_ge_atTop 1] with N hlower hN
  have hcard : (lowerSet N).card ≤ erdos300Max N :=
    card_le_erdos300Max (lowerSet_subset_Icc N) (lowerSet_avoidsOne N)
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hratio : ((lowerSet N).card : ℝ) / (N : ℝ) ≤
      (erdos300Max N : ℝ) / (N : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hNnonneg
  exact hlower.trans_le hratio

/-! ## Weighted Fourier factors

The sharp upper bound uses Bernoulli sampling with a variable parameter,
rather than the probability `1/2` used by the older local unit-fraction
development.  The next lemmas establish the exact factor and its basic
minor-arc decay estimate. -/

/-- The characteristic-function factor for retaining a denominator with
probability `τ`. -/
noncomputable def bernoulliFactor (τ x : ℝ) : ℂ :=
  (1 - τ : ℝ) + τ * e x

private lemma bernoulliFactor_normSq (τ x : ℝ) :
    Complex.normSq (bernoulliFactor τ x) =
      1 - 2 * τ * (1 - τ) * (1 - Real.cos (2 * Real.pi * x)) := by
  have hre : (e x).re = Real.cos (2 * Real.pi * x) := by
    have harg :
        (x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
          ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, harg, Complex.exp_ofReal_mul_I_re]
  have him : (e x).im = Real.sin (2 * Real.pi * x) := by
    have harg :
        (x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
          ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e, harg, Complex.exp_ofReal_mul_I_im]
  rw [Complex.normSq_apply]
  simp only [bernoulliFactor, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
  rw [hre, him]
  have htrig := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  ring_nf
  ring_nf at htrig
  nlinarith

/-- Uniform quadratic decay of a weighted Bernoulli factor on the centered
fundamental interval. -/
lemma norm_bernoulliFactor_le
    {τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |x| ≤ 1 / 2) :
    ‖bernoulliFactor τ x‖ ≤ 1 - 8 * τ * (1 - τ) * x ^ 2 := by
  have hτcomp : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
  have hτquarter : τ * (1 - τ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (τ - 1 / 2)]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hsin := jordan_apply hx0 hx
  have hpix : |Real.pi * x| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have habssin : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * |x|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpix]
    congr 2
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hsinsq : 4 * x ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
    have hsinnonneg : 0 ≤ Real.sin (Real.pi * |x|) :=
      le_trans (mul_nonneg zero_le_two hx0) hsin
    have hsquare := mul_self_le_mul_self (mul_nonneg zero_le_two hx0) hsin
    calc
      4 * x ^ 2 = (2 * |x|) ^ 2 := by nlinarith [sq_abs x]
      _ ≤ Real.sin (Real.pi * |x|) ^ 2 := by
        simpa [pow_two] using hsquare
      _ = |Real.sin (Real.pi * x)| ^ 2 := by rw [habssin]
      _ = Real.sin (Real.pi * x) ^ 2 := sq_abs _
  have htrig :
      1 - Real.cos (2 * Real.pi * x) =
        2 * Real.sin (Real.pi * x) ^ 2 := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
  have hnormsq :
      Complex.normSq (bernoulliFactor τ x) ≤
        1 - 16 * (τ * (1 - τ)) * x ^ 2 := by
    rw [bernoulliFactor_normSq, htrig]
    nlinarith
  have hxsq : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa using hx
  have hrhs : 0 ≤ 1 - 8 * τ * (1 - τ) * x ^ 2 := by
    nlinarith [sq_nonneg x]
  apply le_of_sq_le_sq _ hrhs
  rw [← Complex.normSq_eq_norm_sq]
  calc
    Complex.normSq (bernoulliFactor τ x)
        ≤ 1 - 16 * (τ * (1 - τ)) * x ^ 2 := hnormsq
    _ ≤ (1 - 8 * τ * (1 - τ) * x ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (8 * (τ * (1 - τ)) * x ^ 2)]

private lemma norm_bernoulliFactor_le_one
    {τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    ‖bernoulliFactor τ x‖ ≤ 1 := by
  calc
    ‖bernoulliFactor τ x‖
        ≤ ‖((1 - τ : ℝ) : ℂ)‖ + ‖((τ : ℝ) : ℂ) * e x‖ :=
      norm_add_le _ _
    _ = (1 - τ) + τ := by
      rw [norm_mul, norm_e]
      simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hτ0, abs_of_nonneg (sub_nonneg.mpr hτ1)]
    _ = 1 := by ring

private lemma bernoulliFactor_period
    (τ : ℝ) {x y n : ℤ} (h : x % n = y % n) :
    bernoulliFactor τ ((x : ℝ) / (n : ℝ)) =
      bernoulliFactor τ ((y : ℝ) / (n : ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hdiv : n ∣ x - y := by
    rwa [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  obtain ⟨k, hk⟩ := hdiv
  rw [sub_eq_iff_eq_add'] at hk
  have he : e ((x : ℝ) / (n : ℝ)) = e ((y : ℝ) / (n : ℝ)) := by
    rw [hk, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_left₀]
    · rw [e_add, e_int, mul_one]
    · exact_mod_cast hn
  rw [bernoulliFactor, bernoulliFactor, he]

/-- Product of the absolute values of the weighted Fourier factors. -/
noncomputable def bernoulliNormProd (A : Finset ℕ) (τ : ℝ) (t : ℤ) : ℝ :=
  A.prod fun n => ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖

private lemma bernoulliNormProd_nonneg {A : Finset ℕ} {τ : ℝ} {t : ℤ} :
    0 ≤ bernoulliNormProd A τ t := by
  exact Finset.prod_nonneg fun _ _ => norm_nonneg _

private lemma bernoulliNormProd_le_one
    {A : Finset ℕ} {τ : ℝ} {t : ℤ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    bernoulliNormProd A τ t ≤ 1 := by
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) ?_
  intro n hn
  exact norm_bernoulliFactor_le_one hτ0 hτ1

private lemma bernoulliNormProd_bound
    {A : Finset ℕ} {N : ℕ} {τ : ℝ} (t : ℤ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA0 : 0 ∉ A)
    (hAN : ∀ n ∈ A, n ≤ N) (r : ℕ → ℤ)
    (hrmod : ∀ n ∈ A, r n % n = t % n)
    (hrsize : ∀ n ∈ A, (|r n| : ℝ) ≤ n / 2) :
    bernoulliNormProd A τ t ≤
      Real.exp
        (-(8 * τ * (1 - τ) / (N : ℝ) ^ 2) *
          A.sum (fun n => (r n : ℝ) ^ 2)) := by
  have hrhs :
      Real.exp
          (-(8 * τ * (1 - τ) / (N : ℝ) ^ 2) *
            A.sum (fun n => (r n : ℝ) ^ 2)) =
        A.prod (fun n =>
          Real.exp
            (-(8 * τ * (1 - τ) / (N : ℝ) ^ 2) * (r n : ℝ) ^ 2)) := by
    rw [show
      -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) *
          A.sum (fun n => (r n : ℝ) ^ 2) =
        A.sum (fun n =>
          -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) * (r n : ℝ) ^ 2) by
      rw [Finset.mul_sum]]
    exact Real.exp_sum _ _
  rw [bernoulliNormProd, hrhs]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
  intro n hn
  have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hNpos : (0 : ℝ) < N := hnpos.trans_le (by exact_mod_cast hAN n hn)
  have hperiod :
      ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖ =
        ‖bernoulliFactor τ ((r n : ℝ) / (n : ℝ))‖ := by
    have hp := bernoulliFactor_period τ (x := t) (y := r n) (n := (n : ℤ))
      (hrmod n hn).symm
    simpa using congrArg norm hp
  rw [hperiod]
  have hcenter : |(r n : ℝ) / (n : ℝ)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
    have hrs := hrsize n hn
    nlinarith
  calc
    ‖bernoulliFactor τ ((r n : ℝ) / (n : ℝ))‖
        ≤ 1 - 8 * τ * (1 - τ) * ((r n : ℝ) / (n : ℝ)) ^ 2 :=
      norm_bernoulliFactor_le hτ0 hτ1 hcenter
    _ ≤ Real.exp (-8 * τ * (1 - τ) * ((r n : ℝ) / (n : ℝ)) ^ 2) := by
      have hexp := Real.add_one_le_exp
        (-8 * τ * (1 - τ) * ((r n : ℝ) / (n : ℝ)) ^ 2)
      linarith
    _ ≤ Real.exp
          (-(8 * τ * (1 - τ) / (N : ℝ) ^ 2) * (r n : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hτcomp : 0 ≤ τ * (1 - τ) :=
        mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
      have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith [show (n : ℝ) ≤ N by exact_mod_cast hAN n hn]
      have hinv : ((N : ℝ) ^ 2)⁻¹ ≤ ((n : ℝ) ^ 2)⁻¹ :=
        (inv_le_inv₀ (sq_pos_of_pos hNpos) (sq_pos_of_pos hnpos)).2 hsq
      have hc : 0 ≤ 8 * (τ * (1 - τ)) * (r n : ℝ) ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hinv hc
      calc
        -8 * τ * (1 - τ) * ((r n : ℝ) / (n : ℝ)) ^ 2 =
            -(8 * (τ * (1 - τ)) * (r n : ℝ) ^ 2) * ((n : ℝ) ^ 2)⁻¹ := by
          field_simp [hnpos.ne']
        _ ≤ -(8 * (τ * (1 - τ)) * (r n : ℝ) ^ 2) * ((N : ℝ) ^ 2)⁻¹ :=
          by simpa only [neg_mul] using neg_le_neg hmul
        _ = -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) * (r n : ℝ) ^ 2 := by
          rw [div_eq_mul_inv]
          ring

private lemma weighted_missing_bridge
    (A : Finset ℕ) {N : ℕ} {τ : ℝ} {t : ℤ} {K M : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA0 : 0 ∉ A)
    (hAN : ∀ n ∈ A, n ≤ N) {I : Finset ℤ} (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hbad : M ≤ ((A.filter fun n : ℕ =>
      ∀ x ∈ I, ¬((n : ℤ) ∣ x)).card : ℝ)) :
    bernoulliNormProd A τ t ≤
      Real.exp (-(2 * τ * (1 - τ) * M * K ^ 2 / (N : ℝ) ^ 2)) := by
  have hrepr : ∀ n : ℕ, ∃ rn : ℤ,
      n ∈ A → rn % n = t % n ∧ |rn| ≤ n / 2 := by
    intro n
    by_cases hn : n ∈ A
    · have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA0
      obtain ⟨rn, hrmod, hrsize⟩ := exists_representative t hn0
      exact ⟨rn, fun _ => ⟨hrmod, hrsize⟩⟩
    · exact ⟨0, by simp [hn]⟩
  choose r hrmod hrsize using hrepr
  refine (bernoulliNormProd_bound t hτ0 hτ1 hA0 hAN r
    hrmod ?_).trans ?_
  · intro n hn
    have hrs := hrsize n hn
    have hrsInt : (((r n).natAbs : ℕ) : ℤ) ≤ (n / 2 : ℕ) := by
      rw [Int.abs_eq_natAbs] at hrs
      exact hrs
    have hrsReal : (((r n).natAbs : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hrsInt
    have hrsReal' : |((r n : ℤ) : ℝ)| ≤ ((n / 2 : ℕ) : ℝ) := by
      simpa [Int.cast_abs] using hrsReal
    exact hrsReal'.trans Nat.cast_div_le
  · have hsum :
        M * (K ^ 2 / 4) ≤ A.sum (fun n => (r n : ℝ) ^ 2) :=
      missing_bridge_sum hK hI hrmod hbad
    have hτcomp : 0 ≤ τ * (1 - τ) :=
      mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
    apply Real.exp_le_exp.mpr
    have hcoef : -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) ≤ 0 := by
      exact neg_nonpos.mpr <|
        div_nonneg (by positivity) (sq_nonneg (N : ℝ))
    calc
      -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) *
          A.sum (fun n => (r n : ℝ) ^ 2)
          ≤ -(8 * τ * (1 - τ) / (N : ℝ) ^ 2) * (M * (K ^ 2 / 4)) :=
        mul_le_mul_of_nonpos_left hsum hcoef
      _ = -(2 * τ * (1 - τ) * M * K ^ 2 / (N : ℝ) ^ 2) := by ring

private lemma weighted_minor2_part_one
    {N : ℕ} {A : Finset ℕ} {τ : ℝ} {t : ℤ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hA0 : 0 ∉ A)
    (hAN : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N) :
    bernoulliNormProd A τ t ≤
      (ppowers_in_set A).prod (fun q =>
        (bernoulliNormProd (local_part A q) τ t) ^ (2 * Real.log N)⁻¹) := by
  let Qn : ℕ → Finset ℕ := fun n =>
    (ppowers_in_set A).filter (fun q => n ∈ local_part A q)
  have hqcard : ∀ n ∈ A, ((Qn n).card : ℝ) ≤ 2 * Real.log N := by
    intro n hn
    have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlogn : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
    have htriv : ((Qn n).card : ℝ) ≤ Real.log n / Real.log 2 := by
      simpa [Qn] using (triv_q_bound hA0 n)
    refine htriv.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul ?_
      (Real.log_le_log hnpos (by exact_mod_cast hAN n hn)) hlogn zero_le_two
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 :=
      le_trans (by norm_num) Real.log_two_gt_d9.le
    simpa [one_div] using
      ((one_div_le (Real.log_pos one_lt_two) zero_lt_two).2 hhalf)
  simp only [bernoulliNormProd]
  have hrewrite :
      (ppowers_in_set A).prod (fun q =>
          (∏ n ∈ local_part A q,
            ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖) ^
              (2 * Real.log N)⁻¹) =
        (ppowers_in_set A).prod (fun q =>
          ∏ n ∈ local_part A q,
            ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖ ^
              (2 * Real.log N)⁻¹) := by
    refine Finset.prod_congr rfl ?_
    intro q hq
    symm
    exact Real.finsetProd_rpow _ _ (fun n hn => norm_nonneg _) _
  rw [hrewrite, ← prod_swapping]
  change
    ∏ n ∈ A, ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖ ≤
      ∏ n ∈ A, ∏ _q ∈ Qn n,
        ‖bernoulliFactor τ ((t : ℝ) / (n : ℝ))‖ ^
          (2 * Real.log N)⁻¹
  simp_rw [Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
  intro n hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  refine Real.self_le_rpow_of_le_one (norm_nonneg _)
    (norm_bernoulliFactor_le_one hτ0 hτ1) ?_
  rw [← div_eq_inv_mul]
  refine (div_le_one ?_).2 (hqcard n hn)
  exact mul_pos zero_lt_two
    (Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN))

private lemma weighted_minor2_ind_bound
    {N : ℕ} {A : Finset ℕ} {τ : ℝ} {t : ℤ} {K L : ℝ}
    (I : Finset ℤ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA0 : 0 ∉ A) (hK : 0 < K) (hAN : ∀ n ∈ A, n ≤ N)
    (hN : 2 ≤ N)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hq : ∀ q ∈ ppowers_in_set A,
      (q : ℝ) ≤ τ * (1 - τ) * L * K ^ 2 /
        (4 * (N : ℝ) ^ 2 * Real.log N ^ 2)) :
    bernoulliNormProd A τ t ≤
      (N : ℝ) ^
        (-4 * (ppowers_in_set A \ interval_rare_ppowers I A L).card : ℝ) := by
  refine (weighted_minor2_part_one hτ0 hτ1 hA0 hAN hN).trans ?_
  rw [← Finset.prod_sdiff (interval_rare_ppowers_subset I L)]
  have hlocal : ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
      bernoulliNormProd (local_part A q) τ t ≤
        (N : ℝ) ^ (-8 * Real.log N) := by
    intro q hqdiff
    have hqmem : q ∈ ppowers_in_set A := (Finset.mem_sdiff.mp hqdiff).1
    have hqnot : q ∉ interval_rare_ppowers I A L :=
      (Finset.mem_sdiff.mp hqdiff).2
    have hqcount :
        L / q ≤ (((local_part A q).filter fun n : ℕ =>
          ∀ x ∈ I, ¬((n : ℤ) ∣ x)).card : ℝ) := by
      let : DecidableEq ℤ := Classical.decEq ℤ
      let sZ : Finset ℤ := (local_part A q).image (fun n : ℕ => (n : ℤ))
      have hcardeq :
          ((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬n ∣ x).card : ℝ) =
            (((local_part A q).filter fun n : ℕ =>
              ∀ x ∈ I, ¬((n : ℤ) ∣ x)).card : ℝ) := by
        dsimp [sZ]
        rw [Finset.filter_image,
          Finset.card_image_of_injective _ Nat.cast_injective]
      by_contra hlt
      apply hqnot
      rw [interval_rare_ppowers, Finset.mem_filter]
      have hlt' :
          ((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬n ∣ x).card : ℝ) < L / q := by
        rw [hcardeq]
        exact not_le.mp hlt
      simpa [sZ, Finset.bind_def, Finset.pure_def,
        Finset.biUnion_singleton] using
        (show q ∈ ppowers_in_set A ∧
          ((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬n ∣ x).card : ℝ) < L / q
          from ⟨hqmem, hlt'⟩)
    refine (weighted_missing_bridge (local_part A q) hτ0 hτ1
      (zero_mem_local_part_iff hA0)
      (fun n hn => hAN n (Finset.filter_subset _ _ hn)) hK hI hqcount).trans ?_
    have hNpos : (0 : ℝ) < N := by exact_mod_cast zero_lt_two.trans_le hN
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
    rw [← Real.le_log_iff_exp_le (Real.rpow_pos_of_pos hNpos _),
      Real.log_rpow hNpos]
    have hqpos : 0 < (q : ℝ) := by
      rw [Nat.cast_pos]
      rw [mem_ppowers_in_set] at hqmem
      exact hqmem.1.pos
    have hqbound := hq q hqmem
    have hdenpos : 0 < 4 * (N : ℝ) ^ 2 * Real.log N ^ 2 := by positivity
    have hqbound' :
        4 * (N : ℝ) ^ 2 * Real.log N ^ 2 * q ≤
          τ * (1 - τ) * L * K ^ 2 := by
      have := (_root_.le_div_iff₀ hdenpos).1 hqbound
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hmain' :
        8 * Real.log N * Real.log N ≤
          (2 * τ * (1 - τ) * L * K ^ 2) / ((N : ℝ) ^ 2 * q) := by
      have hden : 0 < (N : ℝ) ^ 2 * q := by positivity
      refine (_root_.le_div_iff₀ hden).2 ?_
      nlinarith [hqbound', sq_nonneg (Real.log N)]
    have hdiv :
        2 * τ * (1 - τ) * (L / q) * K ^ 2 / (N : ℝ) ^ 2 =
          (2 * τ * (1 - τ) * L * K ^ 2) / ((N : ℝ) ^ 2 * q) := by
      field_simp [hqpos.ne']
    rw [hdiv]
    have hmain := hmain'
    nlinarith
  have hlocalPow :
      ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
        bernoulliNormProd (local_part A q) τ t ^ (2 * Real.log N)⁻¹ ≤
          (N : ℝ) ^ (-4 : ℝ) := by
    intro q hqdiff
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
    calc
      bernoulliNormProd (local_part A q) τ t ^ (2 * Real.log N)⁻¹
          ≤ ((N : ℝ) ^ (-8 * Real.log N)) ^ (2 * Real.log N)⁻¹ :=
        Real.rpow_le_rpow bernoulliNormProd_nonneg (hlocal q hqdiff)
          (inv_nonneg.mpr (mul_nonneg zero_le_two hlogpos.le))
      _ = (N : ℝ) ^ (-4 : ℝ) := by
        rw [← Real.rpow_mul (show 0 ≤ (N : ℝ) by positivity)]
        congr 2
        field_simp [hlogpos.ne']
        ring
  have hrare : ∀ q ∈ interval_rare_ppowers I A L,
      bernoulliNormProd (local_part A q) τ t ^ (2 * Real.log N)⁻¹ ≤ 1 := by
    intro q hqrare
    apply Real.rpow_le_one bernoulliNormProd_nonneg
      (bernoulliNormProd_le_one hτ0 hτ1)
    exact inv_nonneg.mpr (mul_nonneg zero_le_two
      (Real.log_nonneg (by exact_mod_cast one_le_two.trans hN)))
  have hprod1 :
      ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
          bernoulliNormProd (local_part A q) τ t ^ (2 * Real.log N)⁻¹ ≤
        ∏ _q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
          (N : ℝ) ^ (-4 : ℝ) := by
    exact Finset.prod_le_prod
      (fun _ _ => Real.rpow_nonneg bernoulliNormProd_nonneg _) hlocalPow
  have hprod2 :
      ∏ q ∈ interval_rare_ppowers I A L,
          bernoulliNormProd (local_part A q) τ t ^ (2 * Real.log N)⁻¹ ≤
        ∏ _q ∈ interval_rare_ppowers I A L, (1 : ℝ) := by
    exact Finset.prod_le_prod
      (fun _ _ => Real.rpow_nonneg bernoulliNormProd_nonneg _) hrare
  refine (mul_le_mul hprod1 hprod2 ?_ ?_).trans ?_
  · exact Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg bernoulliNormProd_nonneg _
  · exact Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _
  · rw [Finset.prod_const, Finset.prod_const_one, mul_one,
      ← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ (N : ℝ) by positivity)]

private lemma weighted_minor2_bound :
    ∀ᶠ N : ℕ in atTop,
      ∀ {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {τ : ℝ},
      0 ≤ τ → τ ≤ 1 → 0 ∉ A → 1 ≤ K → 0 < L → k ≠ 0 → k ≤ N / 192 → K ≤ N →
      (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤ τ * (1 - τ) * L * K ^ 2 /
          (4 * (N : ℝ) ^ 2 * Real.log N ^ 2)) →
      good_condition A K T L →
      (minor_arc₂ A k K T).sum
        (fun h => bernoulliNormProd A τ (h * k)) ≤ 8⁻¹ := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with
    N hN K L T k A τ hτ0 hτ1 hA0 hK hL hk hkN hKN hAN hq hgood
  have ha : τ * (1 - τ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (τ - 1 / 2)]
  have hqCandidate :
      ∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤ L * K ^ 2 / (16 * (N : ℝ) ^ 2 * Real.log N ^ 2) := by
    intro q hqmem
    refine (hq q hqmem).trans ?_
    have hLK : 0 ≤ L * K ^ 2 := mul_nonneg hL.le (sq_nonneg K)
    have hden : 0 < 16 * (N : ℝ) ^ 2 * Real.log N ^ 2 := by
      have hlog : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
      positivity
    have hnum : 4 * τ * (1 - τ) * (L * K ^ 2) ≤ L * K ^ 2 := by
      nlinarith
    have hden4 : 0 < 4 * (N : ℝ) ^ 2 * Real.log N ^ 2 := by
      have hlog : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
      positivity
    refine (div_le_div_iff₀ hden4 hden).2 ?_
    calc
      τ * (1 - τ) * L * K ^ 2 *
            (16 * (N : ℝ) ^ 2 * Real.log N ^ 2) =
          (4 * τ * (1 - τ) * (L * K ^ 2)) *
            (4 * (N : ℝ) ^ 2 * Real.log N ^ 2) := by ring
      _ ≤ (L * K ^ 2) * (4 * (N : ℝ) ^ 2 * Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_right hnum hden4.le
      _ = L * K ^ 2 * (4 * (N : ℝ) ^ 2 * Real.log N ^ 2) := rfl
  have hdivisible :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k,
          ∀ q ∈ interval_rare_ppowers (I h K k) A L, (q : ℤ) ∣ x := by
    intro h hh
    refine (hgood (h * k : ℝ) (I h K k) ?_).resolve_left ?_
    · simp [I, integer_range]
    · rw [minor_arc₂_eq, Finset.mem_filter] at hh
      let : DecidableEq ℤ := Classical.decEq ℤ
      let sZ : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))
      have hcardeq :
          ((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬n ∣ z).card : ℝ) =
            ((A.filter fun n : ℕ => ∀ z ∈ I h K k,
              ¬((n : ℤ) ∣ z)).card : ℝ) := by
        dsimp [sZ]
        rw [Finset.filter_image,
          Finset.card_image_of_injective _ Nat.cast_injective]
      have hh' :
          ((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬n ∣ z).card : ℝ) < T := by
        rw [hcardeq]
        exact hh.2
      simpa [sZ] using not_le.mpr hh'
  have hz :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k,
          ((↑((interval_rare_ppowers (I h K k) A L).lcm id : ℕ) : ℤ) ∣ x) := by
    intro h hh
    obtain ⟨x, hxI, hx⟩ := hdivisible h hh
    exact ⟨x, hxI, cast_lcm_dvd hx⟩
  have hcard :
      ∀ D ∈ (ppowers_in_set A).ssubsets,
        (((minor_arc₂ A k K T).filter
          fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
            6 * (k : ℝ) * (N : ℝ) ^
              (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    intro D hD
    exact candidate_count hN hA0 hK hL hk hKN hAN hqCandidate hz hD
  have hsumD :
      ∀ D ∈ (ppowers_in_set A).ssubsets,
        Finset.sum
            ((minor_arc₂ A k K T).filter
              (fun h => interval_rare_ppowers (I h K k) A L = D))
            (fun h => bernoulliNormProd A τ (h * k)) ≤
          6 * (k : ℝ) * (N : ℝ)⁻¹ *
            ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card := by
    intro D hD
    refine (Finset.sum_le_card_nsmul _ _
      ((N : ℝ) ^ (-4 * (ppowers_in_set A \ D).card : ℝ)) ?_).trans ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      rw [← hh.2]
      refine weighted_minor2_ind_bound (I h K k) hτ0 hτ1 hA0
        (by linarith) hAN hN ?_ hq
      simp [I, integer_range]
    · rw [nsmul_eq_mul]
      refine (mul_le_mul_of_nonneg_right (hcard D hD)
        (Real.rpow_nonneg (by positivity) _)).trans ?_
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast zero_lt_two.trans_le hN
      rw [mul_assoc, ← Real.rpow_add hNpos, mul_assoc (6 * (k : ℝ)),
        ← Real.rpow_neg_one, ← Real.rpow_natCast,
        ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (by positivity))
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_two.trans hN) ?_
      have hcard1 : (1 : ℝ) ≤ (ppowers_in_set A \ D).card := by
        rw [Nat.one_le_cast, Nat.succ_le_iff, Finset.card_pos,
          Finset.sdiff_nonempty, Finset.mem_ssubsets] at *
        exact hD.2
      linarith
  have hsum :
      Finset.sum (ppowers_in_set A).ssubsets
          (fun D => Finset.sum
            ((minor_arc₂ A k K T).filter
              (fun h => interval_rare_ppowers (I h K k) A L = D))
            (fun h => bernoulliNormProd A τ (h * k))) ≤
        Finset.sum (ppowers_in_set A).ssubsets
          (fun D => 6 * (k : ℝ) * (N : ℝ)⁻¹ *
            ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card) := by
    exact Finset.sum_le_sum hsumD
  simp only [Finset.sum_filter] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_ssubsets] at hsum
  rw [← Finset.sum_filter, d_strict_subset hA0 hk hz,
    ← Finset.mul_sum] at hsum
  exact hsum.trans (minor2_bound_end N hN hkN hAN)

private lemma weighted_minor1_bound :
    ∀ᶠ N : ℕ in atTop,
      ∀ {K M T : ℝ} (k : ℕ) {A : Finset ℕ} {τ : ℝ},
      0 < τ → τ < 1 → 8 ≤ M → A.Nonempty →
      (∀ n ∈ A, M ≤ (n : ℝ)) → 0 < K → 0 < T →
      (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤
          (4 * τ * (1 - τ) * T * K ^ 2) /
            ((N : ℝ) ^ 2 * Real.log N)) →
      (minor_arc₁ A k K T).sum
        (fun h => bernoulliNormProd A τ (h * k)) ≤ 8⁻¹ := by
  filter_upwards [minor1_bound_aux] with
    N haux K M T k A τ hτ0 hτ1 hM hAne hLower hK hT hUpper hSmooth
  have hτ0' : 0 ≤ τ := hτ0.le
  have hτ1' : τ ≤ 1 := hτ1.le
  have ha : 0 < τ * (1 - τ) := mul_pos hτ0 (sub_pos.mpr hτ1)
  have hA0 : 0 ∉ A := by
    intro h0
    have : M ≤ 0 := by simpa using hLower 0 h0
    linarith
  have hlcm :
      (lcmA A : ℝ) ≤
        Real.exp (τ * (1 - τ) * T * K ^ 2 / (N : ℝ) ^ 2) := by
    have hT' : 0 < 4 * τ * (1 - τ) * T := by positivity
    have hsmooth' :
        ∀ q ∈ ppowers_in_set A,
          (q : ℝ) ≤
            ((4 * τ * (1 - τ) * T) * K ^ 2) /
              ((N : ℝ) ^ 2 * Real.log N) := by
      intro q hq
      simpa [mul_assoc] using hSmooth q hq
    refine (haux hM hA0 hT' hsmooth').trans_eq ?_
    congr 1
    ring
  suffices hpoint :
      ∀ h ∈ minor_arc₁ A k K T,
        bernoulliNormProd A τ (h * k) ≤ ((lcmA A : ℝ) ^ 2)⁻¹ by
    have hsum :
        (minor_arc₁ A k K T).sum
            (fun h => bernoulliNormProd A τ (h * k)) ≤
          ((minor_arc₁ A k K T).card : ℝ) *
            (((lcmA A : ℝ) ^ 2)⁻¹) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (minor_arc₁ A k K T)
          (fun h => bernoulliNormProd A τ (h * k))
          (((lcmA A : ℝ) ^ 2)⁻¹) hpoint)
    refine hsum.trans ?_
    have hjsubset : j A ⊆ valid_sum_range (lcmA A) := by
      intro x hx
      rw [j, Finset.mem_erase] at hx
      exact hx.2
    have hcard : ((minor_arc₁ A k K T).card : ℝ) ≤ lcmA A := by
      exact_mod_cast
        (Finset.card_le_card ((Finset.filter_subset _ _).trans
          Finset.sdiff_subset)).trans
          ((Finset.card_le_card hjsubset).trans_eq (card_valid_sum_range _))
    have hlcmge : (8 : ℝ) ≤ lcmA A := by
      obtain ⟨n, hn⟩ := hAne
      have hnle : (8 : ℝ) ≤ n := hM.trans (hLower n hn)
      exact hnle.trans (by
        exact_mod_cast Nat.le_of_dvd
          (Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0))
          (Finset.dvd_lcm hn))
    have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
    calc
      ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹) =
          ((minor_arc₁ A k K T).card : ℝ) / (lcmA A : ℝ) ^ 2 := by
            rw [div_eq_mul_inv]
      _ ≤ (lcmA A : ℝ) / (lcmA A : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcard (sq_nonneg _)
      _ = 1 / (lcmA A : ℝ) := by field_simp [hlcm0]
      _ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hlcmge
      _ = (8 : ℝ)⁻¹ := by norm_num
  intro h hh
  rw [minor_arc₁, Finset.mem_filter] at hh
  have hI : I h K k =
      Finset.Icc ⌈((h * k : ℤ) : ℝ) - K / 2⌉
        ⌊((h * k : ℤ) : ℝ) + K / 2⌋ := by
    simp [I, integer_range]
  refine (weighted_missing_bridge A hτ0' hτ1' hA0 hUpper hK hI hh.2).trans ?_
  have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
  have hlcmpos : 0 < (lcmA A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0)
  rw [Real.exp_neg]
  refine (inv_le_inv₀ (Real.exp_pos _) (sq_pos_iff.mpr hlcm0)).2 ?_
  refine (pow_le_pow_left₀ hlcmpos.le hlcm 2).trans ?_
  rw [sq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  apply le_of_eq
  ring

private lemma norm_finsetProd_le_exp_card_mul
    {s : Finset ℕ} {z : ℕ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hz : ∀ i ∈ s, ‖z i - 1‖ ≤ d) :
    ‖s.prod z‖ ≤ Real.exp (s.card * d) := by
  rw [norm_prod]
  calc
    ∏ i ∈ s, ‖z i‖ ≤ ∏ _i ∈ s, (1 + d) := by
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
      intro i hi
      calc
        ‖z i‖ = ‖(z i - 1) + 1‖ := by ring_nf
        _ ≤ ‖z i - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + d := by simpa [add_comm] using add_le_add_right (hz i hi) 1
    _ ≤ Real.exp (∑ _i ∈ s, d) :=
      Real.prod_one_add_le_exp_sum s (fun _ => hd)
    _ = Real.exp (s.card * d) := by simp [nsmul_eq_mul]

private lemma norm_finsetProd_sub_one_le_exp_card_mul
    {s : Finset ℕ} {z : ℕ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hz : ∀ i ∈ s, ‖z i - 1‖ ≤ d) :
    ‖s.prod z - 1‖ ≤ Real.exp (s.card * d) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hza : ‖z a - 1‖ ≤ d := hz a (by simp)
      have hzs : ∀ i ∈ s, ‖z i - 1‖ ≤ d := by
        intro i hi
        exact hz i (by simp [hi])
      have hprod := norm_finsetProd_le_exp_card_mul hd hzs
      have hih := ih hzs
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      calc
        ‖z a * ∏ i ∈ s, z i - 1‖ =
            ‖(∏ i ∈ s, z i) * (z a - 1) +
              ((∏ i ∈ s, z i) - 1)‖ := by
                congr 1
                ring
        _ ≤ ‖∏ i ∈ s, z i‖ * ‖z a - 1‖ +
              ‖(∏ i ∈ s, z i) - 1‖ := by
                exact (norm_add_le _ _).trans_eq (by rw [norm_mul])
        _ ≤ Real.exp (s.card * d) * d +
              (Real.exp (s.card * d) - 1) := by
                gcongr
        _ ≤ Real.exp (s.card * d + d) - 1 := by
          have hexpnonneg : 0 ≤ Real.exp (s.card * d) := Real.exp_nonneg _
          have hone : 1 + d ≤ Real.exp d := by
            simpa [add_comm] using Real.add_one_le_exp d
          rw [Real.exp_add]
          nlinarith

private lemma complex_exp_quadratic_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ ≤ ‖z‖ ^ 3 := by
  have h := Complex.exp_bound (x := z) hz (n := 3) (by norm_num)
  have hcoef :
      (4 : ℝ) * (((Nat.factorial 3 : ℕ) * 3 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    norm_num
  calc
    ‖Complex.exp z - (1 + z + z ^ 2 / 2)‖ =
        ‖Complex.exp z - ∑ m ∈ Finset.range 3, z ^ m / m.factorial‖ := by
          norm_num [Finset.sum_range_succ]
    _ ≤ ‖z‖ ^ 3 *
        ((4 : ℝ) * (((Nat.factorial 3 : ℕ) * 3 : ℕ) : ℝ)⁻¹) := by
      simpa using h
    _ ≤ ‖z‖ ^ 3 := by
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) 3) hcoef

private noncomputable def gaussianScalar (τ x : ℝ) : ℝ :=
  1 - τ * (1 - τ) * (2 * Real.pi * x) ^ 2 / 2

private lemma gaussianScalar_bounds {x τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |2 * Real.pi * x| ≤ 1) :
    (1 / 2 : ℝ) ≤ gaussianScalar τ x ∧ gaussianScalar τ x ≤ 1 := by
  have ha0 : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
  have ha4 : τ * (1 - τ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (τ - 1 / 2)]
  have hx0 : 0 ≤ |2 * Real.pi * x| := abs_nonneg _
  have hx2 : (2 * Real.pi * x) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith
  have hprod :
      τ * (1 - τ) * (2 * Real.pi * x) ^ 2 ≤ 1 / 4 := by
    calc
      τ * (1 - τ) * (2 * Real.pi * x) ^ 2 ≤
          (1 / 4 : ℝ) * (2 * Real.pi * x) ^ 2 :=
        mul_le_mul_of_nonneg_right ha4 (sq_nonneg _)
      _ ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 / 4 := by ring
  dsimp [gaussianScalar]
  constructor
  · nlinarith
  · have := mul_nonneg ha0 (sq_nonneg (2 * Real.pi * x))
    nlinarith

private lemma phaseZ_norm (x : ℝ) :
    ‖((2 * Real.pi * x : ℝ) : ℂ) * Complex.I‖ = |2 * Real.pi * x| := by
  simp

private lemma e_eq_exp_phaseZ (x : ℝ) :
    e x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  simp [e]
  congr 1
  ring

private lemma bernoulliFactor_taylor {x τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |2 * Real.pi * x| ≤ 1) :
    ‖bernoulliFactor τ x -
        e (τ * x) * (gaussianScalar τ x : ℂ)‖ ≤
      4 * |2 * Real.pi * x| ^ 3 := by
  let θ : ℝ := 2 * Real.pi * x
  let z : ℂ := (θ : ℂ) * Complex.I
  let a : ℝ := τ * (1 - τ)
  let g : ℝ := gaussianScalar τ x
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
  have ha4 : a ≤ 1 / 4 := by
    dsimp [a]
    nlinarith [sq_nonneg (τ - 1 / 2)]
  have ha1 : a ≤ 1 := ha4.trans (by norm_num)
  have hθnorm : ‖z‖ = |θ| := by simp [z]
  have hzle : ‖z‖ ≤ 1 := by rw [hθnorm]; simpa [θ] using hx
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hτzle : ‖(τ : ℂ) * z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact (mul_le_of_le_one_left hz0 hτ1).trans hzle
  have hremz := complex_exp_quadratic_error hzle
  have hremτz := complex_exp_quadratic_error hτzle
  have hg := gaussianScalar_bounds hτ0 hτ1 hx
  have hg0 : 0 ≤ g := (by dsimp [g]; linarith [hg.1])
  have hg1 : g ≤ 1 := by simpa [g] using hg.2
  have hgnorm : ‖(g : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
  have hphasex :
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) = z := by rfl
  have hphase :
      (((2 * Real.pi * (τ * x) : ℝ) : ℂ) * Complex.I) =
        (τ : ℂ) * z := by
    dsimp [z, θ]
    push_cast
    ring
  have hzsq : z ^ 2 = -(θ : ℂ) ^ 2 := by
    dsimp [z]
    rw [mul_pow, Complex.I_sq]
    ring
  have hgc : (g : ℂ) = 1 + (a : ℂ) * z ^ 2 / 2 := by
    rw [hzsq]
    dsimp [g, gaussianScalar, a, θ]
    push_cast
    ring
  let P : ℂ := 1 + z + z ^ 2 / 2
  let Pτ : ℂ := 1 + (τ : ℂ) * z + ((τ : ℂ) * z) ^ 2 / 2
  have hdecomp :
      bernoulliFactor τ x - e (τ * x) * (g : ℂ) =
        (τ : ℂ) * (Complex.exp z - P) +
          ((1 - (τ : ℂ)) + (τ : ℂ) * P - Pτ * (g : ℂ)) +
          (Pτ - Complex.exp ((τ : ℂ) * z)) * (g : ℂ) := by
    rw [bernoulliFactor, e_eq_exp_phaseZ, e_eq_exp_phaseZ, hphasex, hphase]
    dsimp [P, Pτ]
    push_cast
    ring
  have hfirst :
      ‖(τ : ℂ) * (Complex.exp z - P)‖ ≤ ‖z‖ ^ 3 := by
    calc
      ‖(τ : ℂ) * (Complex.exp z - P)‖ =
          τ * ‖Complex.exp z - P‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
      _ ≤ τ * ‖z‖ ^ 3 := mul_le_mul_of_nonneg_left
        (by simpa [P] using hremz) hτ0
      _ ≤ ‖z‖ ^ 3 := mul_le_of_le_one_left (pow_nonneg hz0 3) hτ1
  have hthird :
      ‖(Pτ - Complex.exp ((τ : ℂ) * z)) * (g : ℂ)‖ ≤ ‖z‖ ^ 3 := by
    calc
      ‖(Pτ - Complex.exp ((τ : ℂ) * z)) * (g : ℂ)‖ ≤
          ‖Pτ - Complex.exp ((τ : ℂ) * z)‖ := by
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) hgnorm
      _ = ‖Complex.exp ((τ : ℂ) * z) - Pτ‖ := norm_sub_rev _ _
      _ ≤ ‖(τ : ℂ) * z‖ ^ 3 := by simpa [Pτ] using hremτz
      _ ≤ ‖z‖ ^ 3 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
        gcongr
        exact mul_le_of_le_one_left hz0 hτ1
  have hmiddleEq :
      (1 - (τ : ℂ)) + (τ : ℂ) * P - Pτ * (g : ℂ) =
        -((a : ℂ) * (τ : ℂ) * z ^ 3 / 2 +
          (a : ℂ) * (τ : ℂ) ^ 2 * z ^ 4 / 4) := by
    rw [hgc]
    dsimp [P, Pτ, a]
    push_cast
    ring
  have hterm1 :
      ‖(a : ℂ) * (τ : ℂ) * z ^ 3 / 2‖ ≤ ‖z‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha0, abs_of_nonneg hτ0]
    norm_num
    have hat : a * τ ≤ 1 := mul_le_one₀ ha1 hτ0 hτ1
    nlinarith [pow_nonneg hz0 3]
  have hterm2 :
      ‖(a : ℂ) * (τ : ℂ) ^ 2 * z ^ 4 / 4‖ ≤ ‖z‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha0, abs_of_nonneg hτ0]
    norm_num
    have hτsq : τ ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
    have hat : a * τ ^ 2 ≤ 1 := mul_le_one₀ ha1 (sq_nonneg τ) hτsq
    have hz4 : ‖z‖ ^ 4 ≤ ‖z‖ ^ 3 := by
      rw [show ‖z‖ ^ 4 = ‖z‖ ^ 3 * ‖z‖ by ring]
      exact mul_le_of_le_one_right (pow_nonneg hz0 3) hzle
    nlinarith [pow_nonneg hz0 3, pow_nonneg hz0 4]
  have hmiddle :
      ‖(1 - (τ : ℂ)) + (τ : ℂ) * P - Pτ * (g : ℂ)‖ ≤
        2 * ‖z‖ ^ 3 := by
    rw [hmiddleEq, norm_neg]
    exact (norm_add_le _ _).trans (by linarith)
  rw [hdecomp]
  calc
    ‖(τ : ℂ) * (Complex.exp z - P) +
          ((1 - (τ : ℂ)) + (τ : ℂ) * P - Pτ * (g : ℂ)) +
          (Pτ - Complex.exp ((τ : ℂ) * z)) * (g : ℂ)‖ ≤
        ‖(τ : ℂ) * (Complex.exp z - P)‖ +
          ‖(1 - (τ : ℂ)) + (τ : ℂ) * P - Pτ * (g : ℂ)‖ +
          ‖(Pτ - Complex.exp ((τ : ℂ) * z)) * (g : ℂ)‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 * ‖z‖ ^ 3 := by linarith
    _ = 4 * |2 * Real.pi * x| ^ 3 := by rw [hθnorm]

private noncomputable def normalizedBernoulliFactor (τ x : ℝ) : ℂ :=
  bernoulliFactor τ x / (e (τ * x) * (gaussianScalar τ x : ℂ))

private lemma normalizedBernoulliFactor_error {x τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hx : |2 * Real.pi * x| ≤ 1) :
    ‖normalizedBernoulliFactor τ x - 1‖ ≤
      8 * |2 * Real.pi * x| ^ 3 := by
  have hg := gaussianScalar_bounds hτ0 hτ1 hx
  have hgpos : 0 < gaussianScalar τ x := lt_of_lt_of_le (by norm_num) hg.1
  have he0 : e (τ * x) ≠ 0 := by
    intro he
    have hn := norm_e (x := τ * x)
    rw [he] at hn
    norm_num at hn
  have hden : e (τ * x) * (gaussianScalar τ x : ℂ) ≠ 0 := by
    exact mul_ne_zero he0 (by exact_mod_cast hgpos.ne')
  rw [normalizedBernoulliFactor, div_sub_one hden, norm_div]
  have hdennorm :
      ‖e (τ * x) * (gaussianScalar τ x : ℂ)‖ = gaussianScalar τ x := by
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hgpos]
  rw [hdennorm]
  refine (div_le_iff₀ hgpos).2 ?_
  have htaylor := bernoulliFactor_taylor hτ0 hτ1 hx
  calc
    ‖bernoulliFactor τ x - e (τ * x) * (gaussianScalar τ x : ℂ)‖ ≤
        4 * |2 * Real.pi * x| ^ 3 := htaylor
    _ ≤ 8 * |2 * Real.pi * x| ^ 3 * gaussianScalar τ x := by
      have hpow : 0 ≤ |2 * Real.pi * x| ^ 3 := pow_nonneg (abs_nonneg _) 3
      nlinarith [hg.1]

private noncomputable def bernoulliProd (A : Finset ℕ) (τ : ℝ) (h : ℤ) : ℂ :=
  A.prod fun n => bernoulliFactor τ ((h : ℝ) / (n : ℝ))

private lemma bernoulliProd_norm (A : Finset ℕ) (τ : ℝ) (h : ℤ) :
    ‖bernoulliProd A τ h‖ = bernoulliNormProd A τ h := by
  simp [bernoulliProd, bernoulliNormProd, norm_prod]

private lemma bernoulliProd_eq_of_mod
    {A : Finset ℕ} {τ : ℝ} {x y : ℤ}
    (hmod : ∀ n ∈ A, x % (n : ℤ) = y % (n : ℤ)) :
    bernoulliProd A τ x = bernoulliProd A τ y := by
  rw [bernoulliProd, bernoulliProd]
  refine Finset.prod_congr rfl ?_
  intro n hn
  exact bernoulliFactor_period τ (hmod n hn)

private lemma bernoulliProd_sub_lcm_mul
    {A : Finset ℕ} {τ : ℝ} (x t : ℤ) :
    bernoulliProd A τ (x - t * (lcmA A : ℤ)) = bernoulliProd A τ x := by
  apply bernoulliProd_eq_of_mod
  intro n hn
  have hnQ : (n : ℤ) ∣ (lcmA A : ℤ) := by
    exact Int.natCast_dvd_natCast.mpr (Finset.dvd_lcm hn)
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  rw [show (x - t * (lcmA A : ℤ)) - x = -(t * (lcmA A : ℤ)) by ring]
  exact Int.emod_eq_zero_of_dvd (dvd_neg.mpr (dvd_mul_of_dvd_right hnQ t))

private lemma rec_sum_cast_real (A : Finset ℕ) :
    (rec_sum A : ℝ) = A.sum (fun n => (1 : ℝ) / n) := by
  simp [rec_sum, Rat.cast_sum]

private lemma bernoulliProd_re_nonneg_of_small
    {A : Finset ℕ} {τ d : ℝ} {h : ℤ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmeanPhase : e ((h : ℝ) * (τ * (rec_sum A : ℝ))) = 1)
    (hphase : ∀ n ∈ A, |2 * Real.pi * ((h : ℝ) / (n : ℝ))| ≤ 1)
    (hd0 : 0 ≤ d)
    (hdev : ∀ n ∈ A,
      ‖normalizedBernoulliFactor τ ((h : ℝ) / (n : ℝ)) - 1‖ ≤ d)
    (hexp : Real.exp (A.card * d) - 1 ≤ 1) :
    0 ≤ (bernoulliProd A τ h).re := by
  let z : ℕ → ℂ := fun n =>
    normalizedBernoulliFactor τ ((h : ℝ) / (n : ℝ))
  let g : ℕ → ℝ := fun n =>
    gaussianScalar τ ((h : ℝ) / (n : ℝ))
  have hzdev : ‖A.prod z - 1‖ ≤ 1 :=
    (norm_finsetProd_sub_one_le_exp_card_mul hd0 hdev).trans hexp
  have hzre : 0 ≤ (A.prod z).re := by
    have hre : |(A.prod z - 1).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans hzdev
    change |(A.prod z).re - 1| ≤ 1 at hre
    have hlower := (abs_le.mp hre).1
    linarith
  have hg : ∀ n ∈ A, (1 / 2 : ℝ) ≤ g n ∧ g n ≤ 1 := by
    intro n hn
    exact gaussianScalar_bounds hτ0 hτ1 (hphase n hn)
  have hgprod : 0 ≤ A.prod g :=
    Finset.prod_nonneg fun n hn =>
      (show (0 : ℝ) ≤ 1 / 2 by norm_num).trans (hg n hn).1
  have heprod :
      A.prod (fun n => e (τ * ((h : ℝ) / (n : ℝ)))) = 1 := by
    rw [← e_sum]
    have hsum :
        A.sum (fun n => τ * ((h : ℝ) / (n : ℝ))) =
          (h : ℝ) * (τ * (rec_sum A : ℝ)) := by
      calc
        A.sum (fun n => τ * ((h : ℝ) / (n : ℝ))) =
            τ * (h : ℝ) * A.sum (fun n => (1 : ℝ) / n) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro n hn
              ring
        _ = (h : ℝ) * (τ * (rec_sum A : ℝ)) := by
          rw [← rec_sum_cast_real]
          ring
    rw [hsum]
    exact hmeanPhase
  have hfactor : ∀ n ∈ A,
      bernoulliFactor τ ((h : ℝ) / (n : ℝ)) =
        z n * (e (τ * ((h : ℝ) / (n : ℝ))) * (g n : ℂ)) := by
    intro n hn
    have hgn := hg n hn
    have hgpos : 0 < g n := lt_of_lt_of_le (by norm_num) hgn.1
    have he0 : e (τ * ((h : ℝ) / (n : ℝ))) ≠ 0 := by
      intro he
      have hnorm := norm_e (x := τ * ((h : ℝ) / (n : ℝ)))
      rw [he] at hnorm
      norm_num at hnorm
    have hden :
        e (τ * ((h : ℝ) / (n : ℝ))) * (g n : ℂ) ≠ 0 :=
      mul_ne_zero he0 (by exact_mod_cast hgpos.ne')
    dsimp [z, g, normalizedBernoulliFactor]
    exact (div_mul_cancel₀ _ hden).symm
  rw [bernoulliProd]
  have hprodFactor :
      A.prod (fun n => bernoulliFactor τ ((h : ℝ) / (n : ℝ))) =
        (A.prod z) *
          (A.prod (fun n => e (τ * ((h : ℝ) / (n : ℝ)))) *
            ((A.prod g : ℝ) : ℂ)) := by
    calc
      A.prod (fun n => bernoulliFactor τ ((h : ℝ) / (n : ℝ))) =
          A.prod (fun n => z n *
            (e (τ * ((h : ℝ) / (n : ℝ))) * (g n : ℂ))) :=
        Finset.prod_congr rfl hfactor
      _ = (A.prod z) *
          (A.prod (fun n => e (τ * ((h : ℝ) / (n : ℝ)))) *
            ((A.prod g : ℝ) : ℂ)) := by
        simp_rw [Finset.prod_mul_distrib]
        push_cast
        ring
  rw [hprodFactor, heprod, one_mul, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg hzre hgprod

private lemma abs_le_half_of_mem_major_arc_one
    {A : Finset ℕ} {K : ℝ} {h : ℤ}
    (hA0 : 0 ∉ A) (_hK : 0 ≤ K) (hKlcm : K < (lcmA A : ℝ))
    (hh : h ∈ major_arc A 1 K) : |(h : ℝ)| ≤ K / 2 := by
  classical
  rw [major_arc, Finset.mem_filter] at hh
  obtain ⟨t, ht⟩ := hh.2
  rw [mem_major_arc_at] at ht
  have hhbound : |(h : ℝ)| ≤ (lcmA A : ℝ) / 2 := bound_of_mem_j A h hh.1
  have hQpos : 0 < (lcmA A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0)
  have ht0 : t = 0 := by
    by_contra htne
    have htAbsNat : (1 : ℕ) ≤ t.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr htne)
    have htAbs' : (1 : ℝ) ≤ (t.natAbs : ℝ) := by exact_mod_cast htAbsNat
    have htAbs : (1 : ℝ) ≤ |(t : ℝ)| := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using htAbs'
    have hleft : (lcmA A : ℝ) ≤ |(t : ℝ) * (lcmA A : ℝ)| := by
      rw [abs_mul, abs_of_pos hQpos]
      exact le_mul_of_one_le_left hQpos.le htAbs
    have htri :
        |(t : ℝ) * (lcmA A : ℝ)| ≤
          |(h : ℝ) - (t : ℝ) * (lcmA A : ℝ)| + |(h : ℝ)| := by
      calc
        |(t : ℝ) * (lcmA A : ℝ)| =
            |((t : ℝ) * (lcmA A : ℝ) - (h : ℝ)) + (h : ℝ)| := by ring_nf
        _ ≤ |(t : ℝ) * (lcmA A : ℝ) - (h : ℝ)| + |(h : ℝ)| :=
          abs_add_le _ _
        _ = |(h : ℝ) - (t : ℝ) * (lcmA A : ℝ)| + |(h : ℝ)| := by
          rw [abs_sub_comm]
    have hdist :
        |(h : ℝ) - (t : ℝ) * (lcmA A : ℝ)| ≤ K / 2 := by
      simpa using ht.2
    have hstrict : K / 2 + (lcmA A : ℝ) / 2 < (lcmA A : ℝ) := by
      linarith
    linarith [hleft, htri, hdist, hhbound]
  subst t
  simpa using ht.2

private lemma bernoulliNormProd_const_residue
    {A : Finset ℕ} {N : ℕ} {τ M : ℝ} {h : ℤ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hM : 0 < M)
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (hh : |(h : ℝ)| ≤ M / 2) :
    bernoulliNormProd A τ h ≤
      Real.exp (-(8 * τ * (1 - τ) * A.card * (h : ℝ) ^ 2 /
        (N : ℝ) ^ 2)) := by
  have hA0 : 0 ∉ A := by
    intro hzero
    have := hLower 0 hzero
    norm_num at this
    linarith
  refine (bernoulliNormProd_bound h hτ0 hτ1 hA0 hUpper
    (fun _ => h) (fun _ _ => rfl) ?_).trans_eq ?_
  · intro n hn
    have hn : M / 2 ≤ (n : ℝ) / 2 := by linarith [hLower n hn]
    exact hh.trans hn
  · congr 1
    simp [nsmul_eq_mul]
    ring

private lemma bernoulliProd_re_nonneg_small_bound_of_phase
    {A : Finset ℕ} {τ M H : ℝ} {h : ℤ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmeanPhase : e ((h : ℝ) * (τ * (rec_sum A : ℝ))) = 1)
    (hM : 0 < M) (hH : 0 ≤ H)
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hh : |(h : ℝ)| ≤ H)
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hexp :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1) :
    0 ≤ (bernoulliProd A τ h).re := by
  let d : ℝ := 8 * (2 * Real.pi * H / M) ^ 3
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hratio : ∀ n ∈ A,
      |(h : ℝ)| / (n : ℝ) ≤ H / M := by
    intro n hn
    have hnpos : 0 < (n : ℝ) := hM.trans_le (hLower n hn)
    rw [div_le_div_iff₀ hnpos hM]
    calc
      |(h : ℝ)| * M ≤ H * M :=
        mul_le_mul_of_nonneg_right hh hM.le
      _ ≤ H * (n : ℝ) :=
        mul_le_mul_of_nonneg_left (hLower n hn) hH
  have hphaseN : ∀ n ∈ A,
      |2 * Real.pi * ((h : ℝ) / (n : ℝ))| ≤ 1 := by
    intro n hn
    have hnpos : 0 < (n : ℝ) := hM.trans_le (hLower n hn)
    calc
      |2 * Real.pi * ((h : ℝ) / (n : ℝ))| =
          2 * Real.pi * (|(h : ℝ)| / (n : ℝ)) := by
            rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
              abs_of_pos Real.pi_pos, abs_of_pos hnpos]
      _ ≤ 2 * Real.pi * (H / M) :=
        mul_le_mul_of_nonneg_left (hratio n hn)
          (mul_nonneg (by norm_num) Real.pi_pos.le)
      _ = 2 * Real.pi * H / M := by ring
      _ ≤ 1 := hphase
  have hdev : ∀ n ∈ A,
      ‖normalizedBernoulliFactor τ ((h : ℝ) / (n : ℝ)) - 1‖ ≤ d := by
    intro n hn
    refine (normalizedBernoulliFactor_error hτ0 hτ1 (hphaseN n hn)).trans ?_
    have habs :
        |2 * Real.pi * ((h : ℝ) / (n : ℝ))| ≤ 2 * Real.pi * H / M := by
      have hnpos : 0 < (n : ℝ) := hM.trans_le (hLower n hn)
      calc
        |2 * Real.pi * ((h : ℝ) / (n : ℝ))| =
            2 * Real.pi * (|(h : ℝ)| / (n : ℝ)) := by
              rw [abs_mul, abs_mul, abs_div,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                abs_of_pos Real.pi_pos, abs_of_pos hnpos]
        _ ≤ 2 * Real.pi * (H / M) :=
          mul_le_mul_of_nonneg_left (hratio n hn)
            (mul_nonneg (by norm_num) Real.pi_pos.le)
        _ = 2 * Real.pi * H / M := by ring
    dsimp [d]
    gcongr
  exact bernoulliProd_re_nonneg_of_small hτ0 hτ1 hmeanPhase hphaseN hd0 hdev
    (by simpa [d] using hexp)

private lemma bernoulliProd_re_nonneg_small_bound
    {A : Finset ℕ} {τ M H : ℝ} {h : ℤ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hM : 0 < M) (hH : 0 ≤ H)
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hh : |(h : ℝ)| ≤ H)
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hexp :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1) :
    0 ≤ (bernoulliProd A τ h).re := by
  refine bernoulliProd_re_nonneg_small_bound_of_phase hτ0 hτ1 ?_
    hM hH hLower hh hphase hexp
  rw [hmean, mul_one]
  exact e_int h

private lemma bernoulliProd_re_nonneg_small_bound_recip
    {A : Finset ℕ} {k : ℕ} {τ M H : ℝ} {h : ℤ}
    (hk : k ≠ 0) (hkh : (k : ℤ) ∣ h)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1 / (k : ℝ))
    (hM : 0 < M) (hH : 0 ≤ H)
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hh : |(h : ℝ)| ≤ H)
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hexp :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1) :
    0 ≤ (bernoulliProd A τ h).re := by
  refine bernoulliProd_re_nonneg_small_bound_of_phase hτ0 hτ1 ?_
    hM hH hLower hh hphase hexp
  obtain ⟨r, rfl⟩ := hkh
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [hmean]
  have harg :
      ((((k : ℤ) * r : ℤ) : ℝ) * (1 / (k : ℝ))) = (r : ℝ) := by
    push_cast
    field_simp [hkR]
  rw [harg]
  exact e_int r

private lemma weighted_major_arc_bound
    {A : Finset ℕ} {N : ℕ} {τ M K H ρ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (_hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (K + 1) * Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8) :
    -(1 / 8 : ℝ) ≤
      (major_arc A 1 K).sum (fun h => (bernoulliProd A τ h).re) := by
  classical
  let small : Finset ℤ := (major_arc A 1 K).filter fun h => |(h : ℝ)| ≤ H
  let medium : Finset ℤ := (major_arc A 1 K).filter fun h => ¬|(h : ℝ)| ≤ H
  have hsmallSum : 0 ≤ small.sum (fun h => (bernoulliProd A τ h).re) := by
    exact Finset.sum_nonneg fun h hh =>
      bernoulliProd_re_nonneg_small_bound hτ0 hτ1 hmean hM hH hLower
        (Finset.mem_filter.mp hh).2 hphase hsmall
  let E : ℝ := Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2))
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hmediumPoint : ∀ h ∈ medium, -E ≤ (bernoulliProd A τ h).re := by
    intro h hh
    have hhMajor : h ∈ major_arc A 1 K := (Finset.mem_filter.mp hh).1
    have hhLarge : H < |(h : ℝ)| := lt_of_not_ge (Finset.mem_filter.mp hh).2
    have hhK := abs_le_half_of_mem_major_arc_one hA0 hK hKlcm hhMajor
    have hhM : |(h : ℝ)| ≤ M / 2 := hhK.trans (by linarith)
    have hnorm := bernoulliNormProd_const_residue hτ0 hτ1 hM hLower hUpper hhM
    have hsq : H ^ 2 ≤ (h : ℝ) ^ 2 := by
      calc
        H ^ 2 ≤ |(h : ℝ)| ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hhLarge.le)
            (add_nonneg (abs_nonneg (h : ℝ)) hH)]
        _ = (h : ℝ) ^ 2 := sq_abs (h : ℝ)
    have ha0 : 0 ≤ τ * (1 - τ) := mul_nonneg hτ0 (sub_nonneg.mpr hτ1)
    have hcoef :
        ρ * A.card * H ^ 2 ≤
          τ * (1 - τ) * A.card * (h : ℝ) ^ 2 := by
      have hcard0 : (0 : ℝ) ≤ A.card := by positivity
      calc
        ρ * A.card * H ^ 2 ≤
            τ * (1 - τ) * A.card * H ^ 2 := by
              gcongr
        _ ≤ τ * (1 - τ) * A.card * (h : ℝ) ^ 2 := by
              gcongr
    have hexpPoint :
        Real.exp (-(8 * τ * (1 - τ) * A.card * (h : ℝ) ^ 2 /
            (N : ℝ) ^ 2)) ≤ E := by
      change Real.exp (-(8 * τ * (1 - τ) * A.card * (h : ℝ) ^ 2 /
          (N : ℝ) ^ 2)) ≤
        Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2))
      apply Real.exp_le_exp.mpr
      have hN2 : 0 < (N : ℝ) ^ 2 := by exact_mod_cast (pow_pos hN 2)
      have hdiv := div_le_div_of_nonneg_right hcoef hN2.le
      calc
        -(8 * τ * (1 - τ) * A.card * (h : ℝ) ^ 2 / (N : ℝ) ^ 2) =
            -8 * (τ * (1 - τ) * A.card * (h : ℝ) ^ 2 / (N : ℝ) ^ 2) := by ring
        _ ≤ -8 * (ρ * A.card * H ^ 2 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonpos_left hdiv (by norm_num)
        _ = -(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2) := by ring
    have hnormE : ‖bernoulliProd A τ h‖ ≤ E := by
      rw [bernoulliProd_norm]
      exact hnorm.trans hexpPoint
    have hre : -‖bernoulliProd A τ h‖ ≤ (bernoulliProd A τ h).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    linarith
  have hmediumCard : (medium.card : ℝ) ≤ K + 1 := by
    have hsubset : medium ⊆ integer_range 0 (K / 2) := by
      intro h hh
      rw [mem_integer_range_iff]
      simpa using abs_le_half_of_mem_major_arc_one hA0 hK hKlcm
        (Finset.mem_filter.mp hh).1
    calc
      (medium.card : ℝ) ≤ ((integer_range 0 (K / 2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ 2 * (K / 2) + 1 :=
        card_integer_range_le (div_nonneg hK (by norm_num)) (x := (0 : ℝ))
      _ = K + 1 := by ring
  have hmediumSum : -(1 / 8 : ℝ) ≤
      medium.sum (fun h => (bernoulliProd A τ h).re) := by
    have hconst : -(1 / 8 : ℝ) ≤ -(K + 1) * E := by
      change -(1 / 8 : ℝ) ≤
        -(K + 1) * Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2))
      nlinarith
    have hcardE : -(K + 1) * E ≤ -(medium.card : ℝ) * E := by
      have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hmediumCard hE0)
      simpa only [neg_mul] using hneg
    have hsumConst :
        medium.sum (fun _ => -E) ≤
          medium.sum (fun h => (bernoulliProd A τ h).re) :=
      Finset.sum_le_sum hmediumPoint
    have heq : medium.sum (fun _ => -E) = -(medium.card : ℝ) * E := by
      simp [nsmul_eq_mul]
    rw [heq] at hsumConst
    exact le_trans (le_trans hconst hcardE) hsumConst
  have hpartition :
      (major_arc A 1 K).sum (fun h => (bernoulliProd A τ h).re) =
        small.sum (fun h => (bernoulliProd A τ h).re) +
          medium.sum (fun h => (bernoulliProd A τ h).re) := by
    simpa [small, medium] using
      (Finset.sum_filter_add_sum_filter_not (major_arc A 1 K)
        (fun h : ℤ => |(h : ℝ)| ≤ H)
        (fun h => (bernoulliProd A τ h).re)).symm
  rw [hpartition]
  linarith

private lemma major_arc_at_card_le
    {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hk : k ≠ 0) (hK : 0 ≤ K) (t : ℤ) :
    ((major_arc_at A k K t).card : ℝ) ≤ K + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hsub : major_arc_at A k K t ⊆
      integer_range ((t : ℝ) * (lcmA A : ℝ) / k) (K / (2 * k)) := by
    intro h hh
    rw [mem_integer_range_iff]
    simpa [abs_sub_comm] using ((mem_major_arc_at h).mp hh).2
  calc
    ((major_arc_at A k K t).card : ℝ) ≤
        ((integer_range ((t : ℝ) * (lcmA A : ℝ) / k)
          (K / (2 * k))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ 2 * (K / (2 * (k : ℝ))) + 1 :=
      card_integer_range_le (div_nonneg hK (by positivity))
    _ = K / k + 1 := by field_simp [hkR.ne']
    _ ≤ K + 1 := by
      gcongr
      exact div_le_self hK (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)

private lemma my_range'_card_le
    {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hA0 : 0 ∉ A) (hk : k ≠ 0) (hK : 0 ≤ K)
    (hKlcm : K < (lcmA A : ℝ)) :
    ((my_range' A k K).card : ℝ) ≤ 2 * (k : ℝ) + 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hQ : (0 : ℝ) < lcmA A := by
    exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0)
  let radius : ℝ :=
    (K / (2 * (k : ℝ)) + (lcmA A : ℝ) / 2) /
      |(lcmA A : ℝ) / k|
  have hden : |(lcmA A : ℝ) / k| = (lcmA A : ℝ) / k := by
    rw [abs_of_pos (div_pos hQ hkR)]
  have hrad0 : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hrad : radius ≤ (k : ℝ) := by
    dsimp [radius]
    rw [hden]
    apply (div_le_iff₀ (div_pos hQ hkR)).2
    have hKQ : K ≤ (lcmA A : ℝ) := hKlcm.le
    have hdivK : K / (2 * (k : ℝ)) ≤ (lcmA A : ℝ) / 2 := by
      calc
        K / (2 * (k : ℝ)) ≤ (lcmA A : ℝ) / (2 * (k : ℝ)) := by
          gcongr
        _ ≤ (lcmA A : ℝ) / 2 := by
          apply div_le_div_of_nonneg_left hQ.le (by norm_num)
          nlinarith
    calc
      K / (2 * (k : ℝ)) + (lcmA A : ℝ) / 2 ≤
          (lcmA A : ℝ) := by linarith
      _ = (k : ℝ) * ((lcmA A : ℝ) / k) := by field_simp [hkR.ne']
  calc
    ((my_range' A k K).card : ℝ) = ((my_range radius).card : ℝ) := by
      rfl
    _ ≤ 2 * radius + 1 := by
      simpa [my_range] using card_integer_range_le (x := (0 : ℝ)) hrad0
    _ ≤ 2 * (k : ℝ) + 1 := by linarith

private lemma major_arc_card_le
    {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hA0 : 0 ∉ A) (hk : k ≠ 0) (hK : 0 ≤ K)
    (hKlcm : K < (lcmA A : ℝ)) :
    ((major_arc A k K).card : ℝ) ≤
      (2 * (k : ℝ) + 1) * (K + 1) := by
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ)
      (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hKlcm) (by simp)
  rw [major_arc_eq_union hA0 hk, Finset.card_biUnion hdisj]
  push_cast
  calc
    ∑ t ∈ my_range' A k K, ((major_arc_at A k K t).card : ℝ) ≤
        ∑ _t ∈ my_range' A k K, (K + 1) := by
      exact Finset.sum_le_sum fun t _ => major_arc_at_card_le hk hK t
    _ = ((my_range' A k K).card : ℝ) * (K + 1) := by
      simp [nsmul_eq_mul]
      ring
    _ ≤ (2 * (k : ℝ) + 1) * (K + 1) := by
      gcongr
      exact my_range'_card_le hA0 hk hK hKlcm

private lemma weighted_major_arc_bound_recip
    {A : Finset ℕ} {N k : ℕ} {τ M K H ρ : ℝ}
    (hk : k ≠ 0) (hklcm : k ∣ lcmA A)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1 / (k : ℝ))
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (_hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (2 * (k : ℝ) + 1) * (K + 1) *
        Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8) :
    -(1 / 8 : ℝ) ≤
      (major_arc A k K).sum
        (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) := by
  classical
  let residual : ℤ → ℤ → ℤ := fun h t => h * (k : ℤ) - t * (lcmA A : ℤ)
  let small : Finset ℤ := (major_arc A k K).filter fun h =>
    ∃ t : ℤ, h ∈ major_arc_at A k K t ∧ |(residual h t : ℝ)| ≤ H
  let medium : Finset ℤ := (major_arc A k K).filter fun h =>
    ¬ ∃ t : ℤ, h ∈ major_arc_at A k K t ∧ |(residual h t : ℝ)| ≤ H
  have hperiod : ∀ h t : ℤ,
      bernoulliProd A τ (residual h t) = bernoulliProd A τ (h * (k : ℤ)) := by
    intro h t
    exact bernoulliProd_sub_lcm_mul (h * (k : ℤ)) t
  have hresDvd : ∀ h t : ℤ, (k : ℤ) ∣ residual h t := by
    intro h t
    dsimp [residual]
    exact dvd_sub (dvd_mul_left (k : ℤ) h)
      (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hklcm) t)
  have hsmallSum : 0 ≤ small.sum
      (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) := by
    refine Finset.sum_nonneg fun h hh => ?_
    obtain ⟨t, ht, hres⟩ := (Finset.mem_filter.mp hh).2
    rw [← hperiod h t]
    exact bernoulliProd_re_nonneg_small_bound_recip hk (hresDvd h t)
      hτ0 hτ1 hmean hM hH hLower hres hphase hsmall
  let E : ℝ := Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2))
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hmediumPoint : ∀ h ∈ medium,
      -E ≤ (bernoulliProd A τ (h * (k : ℤ))).re := by
    intro h hh
    have hhMajor : h ∈ major_arc A k K := (Finset.mem_filter.mp hh).1
    rw [major_arc, Finset.mem_filter] at hhMajor
    obtain ⟨t, ht⟩ := hhMajor.2
    have hresK : |(residual h t : ℝ)| ≤ K / 2 := by
      simpa [residual] using
        ((mem_major_arc_at' (A := A) (k := k) (K := K) (t := t) hk h).mp ht).2
    have hresLarge : H < |(residual h t : ℝ)| := by
      apply lt_of_not_ge
      intro hle
      exact (Finset.mem_filter.mp hh).2 ⟨t, ht, hle⟩
    have hresM : |(residual h t : ℝ)| ≤ M / 2 := hresK.trans (by linarith)
    have hnorm := bernoulliNormProd_const_residue hτ0 hτ1 hM hLower hUpper hresM
    have hsq : H ^ 2 ≤ (residual h t : ℝ) ^ 2 := by
      calc
        H ^ 2 ≤ |(residual h t : ℝ)| ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hresLarge.le)
            (add_nonneg (abs_nonneg (residual h t : ℝ)) hH)]
        _ = (residual h t : ℝ) ^ 2 := sq_abs _
    have hcoef :
        ρ * A.card * H ^ 2 ≤
          τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 := by
      calc
        ρ * A.card * H ^ 2 ≤
            τ * (1 - τ) * A.card * H ^ 2 := by gcongr
        _ ≤ τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 := by
          gcongr
    have hexpPoint :
        Real.exp (-(8 * τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 /
            (N : ℝ) ^ 2)) ≤ E := by
      change Real.exp (-(8 * τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 /
          (N : ℝ) ^ 2)) ≤
        Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2))
      apply Real.exp_le_exp.mpr
      have hN2 : 0 < (N : ℝ) ^ 2 := by exact_mod_cast (pow_pos hN 2)
      have hdiv := div_le_div_of_nonneg_right hcoef hN2.le
      calc
        -(8 * τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 /
            (N : ℝ) ^ 2) =
            -8 * (τ * (1 - τ) * A.card * (residual h t : ℝ) ^ 2 /
              (N : ℝ) ^ 2) := by ring
        _ ≤ -8 * (ρ * A.card * H ^ 2 / (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonpos_left hdiv (by norm_num)
        _ = -(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2) := by ring
    have hnormE : ‖bernoulliProd A τ (residual h t)‖ ≤ E := by
      rw [bernoulliProd_norm]
      exact hnorm.trans hexpPoint
    have hre : -‖bernoulliProd A τ (residual h t)‖ ≤
        (bernoulliProd A τ (residual h t)).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    rw [← hperiod h t]
    linarith
  have hmediumCard : (medium.card : ℝ) ≤
      (2 * (k : ℝ) + 1) * (K + 1) := by
    have hsub : medium ⊆ major_arc A k K := Finset.filter_subset _ _
    have hcast : (medium.card : ℝ) ≤ (major_arc A k K).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcast.trans (major_arc_card_le hA0 hk hK hKlcm)
  have hmediumSum : -(1 / 8 : ℝ) ≤
      medium.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) := by
    have hconst : -(1 / 8 : ℝ) ≤
        -((2 * (k : ℝ) + 1) * (K + 1)) * E := by
      dsimp [E]
      nlinarith
    have hcardE : -((2 * (k : ℝ) + 1) * (K + 1)) * E ≤
        -(medium.card : ℝ) * E := by
      have hneg := neg_le_neg (mul_le_mul_of_nonneg_right hmediumCard hE0)
      simpa only [neg_mul] using hneg
    have hsumConst : medium.sum (fun _ => -E) ≤
        medium.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) :=
      Finset.sum_le_sum hmediumPoint
    have heq : medium.sum (fun _ => -E) = -(medium.card : ℝ) * E := by
      simp [nsmul_eq_mul]
    rw [heq] at hsumConst
    exact le_trans (le_trans hconst hcardE) hsumConst
  have hpartition :
      (major_arc A k K).sum
          (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) =
        small.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) +
          medium.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) := by
    simpa [small, medium] using
      (Finset.sum_filter_add_sum_filter_not (major_arc A k K)
        (fun h : ℤ => ∃ t : ℤ,
          h ∈ major_arc_at A k K t ∧ |(residual h t : ℝ)| ≤ H)
        (fun h => (bernoulliProd A τ (h * (k : ℤ))).re)).symm
  rw [hpartition]
  linarith

private noncomputable def subsetWeight (A : Finset ℕ) (τ : ℝ)
    (B : Finset ℕ) : ℝ :=
  τ ^ B.card * (1 - τ) ^ (A \ B).card

private lemma bernoulliProd_powerset (A : Finset ℕ) (τ : ℝ) (h : ℤ) :
    bernoulliProd A τ h =
      A.powerset.sum (fun B =>
        (subsetWeight A τ B : ℂ) * e ((h : ℝ) * (rec_sum B : ℝ))) := by
  classical
  have heprod : ∀ B ⊆ A,
      B.prod (fun n => e ((h : ℝ) / (n : ℝ))) =
        e ((h : ℝ) * (rec_sum B : ℝ)) := by
    intro B hBA
    rw [← e_sum]
    congr 1
    rw [rec_sum_cast_real, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    ring
  calc
    bernoulliProd A τ h =
        A.prod (fun n =>
          ((τ : ℂ) * e ((h : ℝ) / (n : ℝ))) + (1 - τ : ℝ)) := by
      rw [bernoulliProd]
      refine Finset.prod_congr rfl ?_
      intro n hn
      rw [bernoulliFactor]
      push_cast
      ring
    _ = A.powerset.sum (fun B =>
        (B.prod (fun n => (τ : ℂ) * e ((h : ℝ) / (n : ℝ)))) *
          ((A \ B).prod (fun _ => ((1 - τ : ℝ) : ℂ)))) := by
      exact Finset.prod_add _ _ A
    _ = A.powerset.sum (fun B =>
        (subsetWeight A τ B : ℂ) * e ((h : ℝ) * (rec_sum B : ℝ))) := by
      refine Finset.sum_congr rfl ?_
      intro B hB
      have hBA := Finset.mem_powerset.mp hB
      rw [Finset.prod_mul_distrib, heprod B hBA]
      simp only [Finset.prod_const]
      dsimp [subsetWeight]
      push_cast
      ring

private lemma rec_sum_eq_lcm_numerator
    {A B : Finset ℕ} (hA0 : 0 ∉ A) (hBA : B ⊆ A) :
    rec_sum B =
      ((B.sum (fun n => lcmA A / n) : ℕ) : ℚ) / (lcmA A : ℚ) := by
  have hQ0 : (lcmA A : ℚ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
  apply (eq_div_iff hQ0).2
  rw [rec_sum, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn0 : n ≠ 0 := by
    intro hnzero
    exact hA0 (hBA (hnzero ▸ hn))
  calc
    (1 : ℚ) / n * (lcmA A : ℚ) = (lcmA A : ℚ) / n := by ring
    _ = ((lcmA A / n : ℕ) : ℚ) := by
      symm
      exact Nat.cast_div (Finset.dvd_lcm (hBA hn)) (Nat.cast_ne_zero.mpr hn0)

private noncomputable def integerReciprocalMass
    (A : Finset ℕ) (τ : ℝ) : ℝ :=
  A.powerset.sum fun B =>
    if lcmA A ∣ B.sum (fun n => lcmA A / n) then
      subsetWeight A τ B
    else 0

private noncomputable def integerReciprocalMassC
    (A : Finset ℕ) (τ : ℝ) : ℂ :=
  A.powerset.sum fun B =>
    if lcmA A ∣ B.sum (fun n => lcmA A / n) then
      (subsetWeight A τ B : ℂ)
    else 0

private lemma integerReciprocalMassC_eq
    (A : Finset ℕ) (τ : ℝ) :
    integerReciprocalMassC A τ = (integerReciprocalMass A τ : ℂ) := by
  classical
  simp only [integerReciprocalMassC, integerReciprocalMass]
  push_cast
  apply Finset.sum_congr rfl
  intro B hB
  split_ifs <;> rfl

private lemma subsetWeight_eq_finiteHoeffding
    {A B : Finset ℕ} {τ : ℝ} (_hBA : B ⊆ A) :
    subsetWeight A τ B =
      Erdos297.WeightedFourier.subsetWeight A (fun _ => τ) B := by
  simp [subsetWeight, Erdos297.WeightedFourier.subsetWeight,
    Finset.prod_const]

private lemma character_sum_eq_lcm_indicator
    {A B : Finset ℕ} (hA0 : 0 ∉ A) (hBA : B ⊆ A) :
    (valid_sum_range (lcmA A)).sum
        (fun h => e ((h : ℝ) * (rec_sum B : ℝ))) =
      if lcmA A ∣ B.sum (fun n => lcmA A / n) then
        (lcmA A : ℂ)
      else 0 := by
  let Q : ℕ := lcmA A
  let u : ℕ := B.sum (fun n => Q / n)
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact lcm_ne_zero_of_zero_not_mem hA0
  have hrec : rec_sum B = (u : ℚ) / (Q : ℚ) := by
    simpa [Q, u] using rec_sum_eq_lcm_numerator hA0 hBA
  have ht : (-((Q : ℕ) : ℤ) / 2 : ℤ) < (Q : ℤ) / 2 := by
    apply Int.ediv_lt_of_lt_mul zero_lt_two
    apply lt_of_lt_of_le
    · rw [Right.neg_neg_iff, Int.natCast_pos]
      exact Nat.pos_iff_ne_zero.mpr hQ0
    · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
  have horth := orthogonality (n := u) (m := Q) hQ0
    (I := valid_sum_range Q) rfl ht (card_valid_sum_range Q)
  have hphase : ∀ h : ℤ,
      e ((h : ℝ) * (rec_sum B : ℝ)) =
        e ((h : ℝ) * (u : ℝ) / (Q : ℝ)) := by
    intro h
    congr 1
    have hrecR : (rec_sum B : ℝ) = (u : ℝ) / (Q : ℝ) := by
      rw [hrec]
      norm_num [Rat.cast_div]
    rw [hrecR]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hphase h)]
  by_cases hdiv : Q ∣ u
  · rw [if_pos hdiv] at horth
    rw [if_pos (by simpa [Q, u] using hdiv)]
    change (valid_sum_range Q).sum
      (fun h => e ((h : ℝ) * (u : ℝ) / (Q : ℝ))) = (Q : ℂ)
    have hQcomplex : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0
    calc
      (valid_sum_range Q).sum
          (fun h => e ((h : ℝ) * (u : ℝ) / (Q : ℝ))) =
          ((valid_sum_range Q).sum
            (fun h => e ((h : ℝ) * (u : ℝ) / (Q : ℝ))) *
              (1 / (Q : ℂ))) * Q := by
                field_simp
                apply Finset.sum_congr rfl
                intro h hh
                congr 1
                ring
      _ = (Q : ℂ) := by rw [horth, one_mul]
  · rw [if_neg hdiv] at horth
    rw [if_neg (by simpa [Q, u] using hdiv)]
    change (valid_sum_range Q).sum
      (fun h => e ((h : ℝ) * (u : ℝ) / (Q : ℝ))) = 0
    have hQinv : (1 / (Q : ℂ)) ≠ 0 := one_div_ne_zero (by exact_mod_cast hQ0)
    exact (mul_eq_zero.mp horth).resolve_right hQinv

private lemma weighted_fourier_eq_integer_mass
    {A : Finset ℕ} {τ : ℝ} (hA0 : 0 ∉ A) :
    (valid_sum_range (lcmA A)).sum (fun h => bernoulliProd A τ h) =
      (lcmA A : ℂ) * integerReciprocalMassC A τ := by
  classical
  rw [Finset.sum_congr rfl (fun h _ => bernoulliProd_powerset A τ h),
    Finset.sum_comm]
  have hterms : ∀ B ∈ A.powerset,
      (valid_sum_range (lcmA A)).sum
          (fun h => (subsetWeight A τ B : ℂ) *
            e ((h : ℝ) * (rec_sum B : ℝ))) =
        (lcmA A : ℂ) *
          (if lcmA A ∣ B.sum (fun n => lcmA A / n) then
            (subsetWeight A τ B : ℂ)
          else 0) := by
    intro B hB
    rw [← Finset.mul_sum,
      character_sum_eq_lcm_indicator hA0 (Finset.mem_powerset.mp hB)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterms, integerReciprocalMassC, Finset.mul_sum]

private lemma integerReciprocalMass_le_hoeffdingTail_of_avoids
    {A : Finset ℕ} {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hA0 : 0 ∉ A) (hAvoid : AvoidsOne A) :
    integerReciprocalMass A τ ≤
      Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
        1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
              (fun n : ℕ => (n : ℝ)⁻¹) -
            Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
              (fun n : ℕ => (n : ℝ)⁻¹)|) := by
  classical
  have hmeanFH :
      Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
          (fun n : ℕ => (n : ℝ)⁻¹) = 1 := by
    rw [Erdos297.FiniteHoeffding.subsetMean, ← Finset.mul_sum]
    calc
      τ * ∑ i ∈ A, (i : ℝ)⁻¹ = τ * (rec_sum A : ℝ) := by
        congr 1
        simpa [one_div] using (rec_sum_cast_real A).symm
      _ = 1 := hmean
  rw [integerReciprocalMass, Erdos297.FiniteHoeffding.eventMass]
  apply Finset.sum_le_sum
  intro B hB
  have hBA : B ⊆ A := Finset.mem_powerset.mp hB
  have hweight0 : 0 ≤ subsetWeight A τ B := by
    rw [subsetWeight_eq_finiteHoeffding hBA]
    exact Erdos297.WeightedFourier.subsetWeight_nonneg A (fun _ => τ)
      (fun _ _ => hτ0) (fun _ _ => hτ1) hB
  have hweight0FH :
      0 ≤ Erdos297.WeightedFourier.subsetWeight A (fun _ => τ) B := by
    simpa [← subsetWeight_eq_finiteHoeffding hBA] using hweight0
  by_cases hdiv : lcmA A ∣ B.sum (fun n => lcmA A / n)
  · obtain ⟨d, hd⟩ := hdiv
    have hQ0 : (lcmA A : ℚ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
    have hrecD : rec_sum B = (d : ℚ) := by
      rw [rec_sum_eq_lcm_numerator hA0 hBA, hd, Nat.cast_mul]
      field_simp
    have hd1 : d ≠ 1 := by
      intro hdOne
      apply hAvoid B hBA
      simpa [hdOne] using hrecD
    have hfarD : (1 : ℝ) ≤ |(d : ℝ) - 1| := by
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · norm_num
      · have hdTwo : 2 ≤ d := by omega
        have hdTwoR : (2 : ℝ) ≤ d := by exact_mod_cast hdTwo
        rw [abs_of_nonneg]
        · linarith
        · linarith
    have hsubset :
        Erdos297.FiniteHoeffding.subsetSum B
            (fun n : ℕ => (n : ℝ)⁻¹) = (d : ℝ) := by
      have hrecReal : (rec_sum B : ℝ) = (d : ℝ) := by exact_mod_cast hrecD
      calc
        Erdos297.FiniteHoeffding.subsetSum B
            (fun n : ℕ => (n : ℝ)⁻¹) =
            ∑ n ∈ B, (n : ℝ)⁻¹ := rfl
        _ = (rec_sum B : ℝ) := by
          simpa [one_div] using (rec_sum_cast_real B).symm
        _ = (d : ℝ) := hrecReal
    have htail :
        1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
              (fun n : ℕ => (n : ℝ)⁻¹) -
            Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
              (fun n : ℕ => (n : ℝ)⁻¹)| := by
      simpa [hsubset, hmeanFH] using hfarD
    rw [if_pos ⟨d, hd⟩, if_pos htail, subsetWeight_eq_finiteHoeffding hBA]
  · rw [if_neg hdiv]
    split_ifs
    · exact hweight0FH
    · exact le_rfl

private lemma character_sum_eq_zero_of_avoids
    {A B : Finset ℕ} (hA0 : 0 ∉ A) (hBA : B ⊆ A)
    (hBne : B.Nonempty) (hAvoid : AvoidsOne A)
    (hAtwo : (rec_sum A : ℝ) < 2) :
    (valid_sum_range (lcmA A)).sum
      (fun h => e ((h : ℝ) * (rec_sum B : ℝ))) = 0 := by
  let Q : ℕ := lcmA A
  let u : ℕ := B.sum (fun n => Q / n)
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact lcm_ne_zero_of_zero_not_mem hA0
  have hrec : rec_sum B = (u : ℚ) / (Q : ℚ) := by
    simpa [Q, u] using rec_sum_eq_lcm_numerator hA0 hBA
  have hnotdvd : ¬Q ∣ u := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    have hrecK : rec_sum B = (k : ℚ) := by
      rw [hrec, hk, Nat.cast_mul]
      field_simp [show (Q : ℚ) ≠ 0 by exact_mod_cast hQ0]
    have hB0 : 0 ∉ B := fun hzero => hA0 (hBA hzero)
    have hrecpos : (0 : ℚ) < rec_sum B := by
      have hne : rec_sum B ≠ 0 := (rec_sum_eq_zero_iff hB0).not.mpr hBne.ne_empty
      exact lt_of_le_of_ne rec_sum_nonneg hne.symm
    have hkpos : 0 < k := by
      rw [hrecK] at hrecpos
      exact_mod_cast hrecpos
    have hmono : (rec_sum B : ℝ) ≤ (rec_sum A : ℝ) := by
      exact_mod_cast rec_sum_mono hBA
    have hrecLt : (rec_sum B : ℝ) < 2 := hmono.trans_lt hAtwo
    have hklt : k < 2 := by
      have hcast : ((k : ℚ) : ℝ) < 2 := by simpa [hrecK] using hrecLt
      exact_mod_cast hcast
    have hk1 : k = 1 := by omega
    subst k
    exact hAvoid B hBA (by simpa using hrecK)
  have ht : (-((Q : ℕ) : ℤ) / 2 : ℤ) < (Q : ℤ) / 2 := by
    apply Int.ediv_lt_of_lt_mul zero_lt_two
    apply lt_of_lt_of_le
    · rw [Right.neg_neg_iff, Int.natCast_pos]
      exact Nat.pos_iff_ne_zero.mpr hQ0
    · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
  have horth := orthogonality (n := u) (m := Q) hQ0
    (I := valid_sum_range Q) rfl ht (card_valid_sum_range Q)
  rw [if_neg hnotdvd] at horth
  have hphase : ∀ h : ℤ,
      e ((h : ℝ) * (rec_sum B : ℝ)) = e ((h : ℝ) * (u : ℝ) / (Q : ℝ)) := by
    intro h
    congr 1
    have hrecR : (rec_sum B : ℝ) = (u : ℝ) / (Q : ℝ) := by
      rw [hrec]
      norm_num [Rat.cast_div]
    rw [hrecR]
    ring
  have hsum :
      (valid_sum_range Q).sum
        (fun h => e ((h : ℝ) * (rec_sum B : ℝ))) * (1 / (Q : ℂ)) = 0 := by
    rw [Finset.sum_congr rfl (fun h _ => hphase h)]
    exact horth
  have hQinv : (1 / (Q : ℂ)) ≠ 0 := by
    exact one_div_ne_zero (by exact_mod_cast hQ0)
  have hzero := (mul_eq_zero.mp hsum).resolve_right hQinv
  simpa [Q] using hzero

private lemma character_sum_eq_zero_of_avoids_recip
    {A B : Finset ℕ} {k : ℕ}
    (hk : k ≠ 0) (hA0 : 0 ∉ A) (hBA : B ⊆ A)
    (hBne : B.Nonempty)
    (hAvoid : ∀ S ⊆ A, rec_sum S ≠ 1 / k)
    (hAtwo : (rec_sum A : ℝ) < 2 / (k : ℝ)) :
    (valid_sum_range (lcmA A)).sum
      (fun h => e ((h : ℝ) * (k : ℝ) * (rec_sum B : ℝ))) = 0 := by
  let Q : ℕ := lcmA A
  let u : ℕ := B.sum (fun n => Q / n)
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact lcm_ne_zero_of_zero_not_mem hA0
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hkQpos : (0 : ℚ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hrec : rec_sum B = (u : ℚ) / (Q : ℚ) := by
    simpa [Q, u] using rec_sum_eq_lcm_numerator hA0 hBA
  have hnotdvd : ¬Q ∣ k * u := by
    intro hdiv
    obtain ⟨d, hd⟩ := hdiv
    have hscaled : rec_sum B * (k : ℚ) = (d : ℚ) := by
      rw [hrec]
      field_simp [show (Q : ℚ) ≠ 0 by exact_mod_cast hQ0]
      exact_mod_cast (by simpa [Nat.mul_comm] using hd)
    have hB0 : 0 ∉ B := fun hzero => hA0 (hBA hzero)
    have hrecpos : (0 : ℚ) < rec_sum B := by
      have hne : rec_sum B ≠ 0 := (rec_sum_eq_zero_iff hB0).not.mpr hBne.ne_empty
      exact lt_of_le_of_ne rec_sum_nonneg hne.symm
    have hdposQ : (0 : ℚ) < d := by
      rw [← hscaled]
      exact mul_pos hrecpos hkQpos
    have hdpos : 0 < d := by exact_mod_cast hdposQ
    have hmono : (rec_sum B : ℝ) ≤ (rec_sum A : ℝ) := by
      exact_mod_cast rec_sum_mono hBA
    have hscaledLt : ((d : ℚ) : ℝ) < 2 := by
      have hrecLt : (rec_sum B : ℝ) < 2 / (k : ℝ) := hmono.trans_lt hAtwo
      have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have hmul := (lt_div_iff₀ hkR).mp hrecLt
      have hscaledR : (rec_sum B : ℝ) * (k : ℝ) = (d : ℝ) := by
        exact_mod_cast hscaled
      rw [hscaledR] at hmul
      exact hmul
    have hdltR : (d : ℝ) < 2 := by simpa using hscaledLt
    have hdlt : d < 2 := by exact_mod_cast hdltR
    have hd1 : d = 1 := by omega
    apply hAvoid B hBA
    apply (eq_div_iff hkQ).2
    simpa [hd1] using hscaled
  have ht : (-((Q : ℕ) : ℤ) / 2 : ℤ) < (Q : ℤ) / 2 := by
    apply Int.ediv_lt_of_lt_mul zero_lt_two
    apply lt_of_lt_of_le
    · rw [Right.neg_neg_iff, Int.natCast_pos]
      exact Nat.pos_iff_ne_zero.mpr hQ0
    · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
  have horth := orthogonality (n := k * u) (m := Q) hQ0
    (I := valid_sum_range Q) rfl ht (card_valid_sum_range Q)
  rw [if_neg hnotdvd] at horth
  have hphase : ∀ h : ℤ,
      e ((h : ℝ) * (k : ℝ) * (rec_sum B : ℝ)) =
        e ((h : ℝ) * ((k * u : ℕ) : ℝ) / (Q : ℝ)) := by
    intro h
    congr 1
    have hrecR : (rec_sum B : ℝ) = (u : ℝ) / (Q : ℝ) := by
      rw [hrec]
      norm_num [Rat.cast_div]
    rw [hrecR]
    push_cast
    ring
  have hsum :
      (valid_sum_range Q).sum
        (fun h => e ((h : ℝ) * (k : ℝ) * (rec_sum B : ℝ))) *
          (1 / (Q : ℂ)) = 0 := by
    rw [Finset.sum_congr rfl (fun h _ => hphase h)]
    exact horth
  have hQinv : (1 / (Q : ℂ)) ≠ 0 := by
    exact one_div_ne_zero (by exact_mod_cast hQ0)
  have hzero := (mul_eq_zero.mp hsum).resolve_right hQinv
  simpa [Q] using hzero

private lemma weighted_fourier_eq_empty
    {A : Finset ℕ} {τ : ℝ} (hA0 : 0 ∉ A)
    (hAvoid : AvoidsOne A) (hAtwo : (rec_sum A : ℝ) < 2) :
    (valid_sum_range (lcmA A)).sum (fun h => bernoulliProd A τ h) =
      (lcmA A : ℂ) * (((1 - τ) ^ A.card : ℝ) : ℂ) := by
  classical
  rw [Finset.sum_congr rfl (fun h _ => bernoulliProd_powerset A τ h),
    Finset.sum_comm]
  have hterms : ∀ B ∈ A.powerset,
      (valid_sum_range (lcmA A)).sum
          (fun h => (subsetWeight A τ B : ℂ) *
            e ((h : ℝ) * (rec_sum B : ℝ))) =
        if B = ∅ then
          (lcmA A : ℂ) * (((1 - τ) ^ A.card : ℝ) : ℂ)
        else 0 := by
    intro B hB
    have hBA := Finset.mem_powerset.mp hB
    by_cases hB0 : B = ∅
    · subst B
      simp [subsetWeight, card_valid_sum_range]
    · rw [if_neg hB0, ← Finset.mul_sum]
      have hchar := character_sum_eq_zero_of_avoids hA0 hBA
        (Finset.nonempty_iff_ne_empty.mpr hB0) hAvoid hAtwo
      rw [hchar, mul_zero]
  rw [Finset.sum_congr rfl hterms]
  simp

private lemma weighted_fourier_eq_empty_recip
    {A : Finset ℕ} {k : ℕ} {τ : ℝ}
    (hk : k ≠ 0) (hA0 : 0 ∉ A)
    (hAvoid : ∀ S ⊆ A, rec_sum S ≠ 1 / k)
    (hAtwo : (rec_sum A : ℝ) < 2 / (k : ℝ)) :
    (valid_sum_range (lcmA A)).sum
        (fun h => bernoulliProd A τ (h * (k : ℤ))) =
      (lcmA A : ℂ) * (((1 - τ) ^ A.card : ℝ) : ℂ) := by
  classical
  rw [Finset.sum_congr rfl
      (fun h _ => bernoulliProd_powerset A τ (h * (k : ℤ))),
    Finset.sum_comm]
  have hterms : ∀ B ∈ A.powerset,
      (valid_sum_range (lcmA A)).sum
          (fun h => (subsetWeight A τ B : ℂ) *
            e (((h * (k : ℤ) : ℤ) : ℝ) * (rec_sum B : ℝ))) =
        if B = ∅ then
          (lcmA A : ℂ) * (((1 - τ) ^ A.card : ℝ) : ℂ)
        else 0 := by
    intro B hB
    have hBA := Finset.mem_powerset.mp hB
    by_cases hB0 : B = ∅
    · subst B
      simp [subsetWeight, card_valid_sum_range]
    · rw [if_neg hB0, ← Finset.mul_sum]
      have hchar := character_sum_eq_zero_of_avoids_recip hk hA0 hBA
        (Finset.nonempty_iff_ne_empty.mpr hB0) hAvoid hAtwo
      have hsame : ∀ h : ℤ,
          e (((h * (k : ℤ) : ℤ) : ℝ) * (rec_sum B : ℝ)) =
            e ((h : ℝ) * (k : ℝ) * (rec_sum B : ℝ)) := by
        intro h
        congr 1
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun h _ => hsame h), hchar, mul_zero]
  rw [Finset.sum_congr rfl hterms]
  simp

private lemma weighted_circle_core
    {A : Finset ℕ} {N : ℕ} {τ M K H ρ T : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hAtwo : (rec_sum A : ℝ) < 2)
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (K + 1) * Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8)
    (hminor1 :
      (minor_arc₁ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8)
    (hminor2 :
      (minor_arc₂ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8)
    (hempty :
      (lcmA A : ℝ) * (1 - τ) ^ A.card < 5 / 8) :
    ∃ B : Finset ℕ, B ⊆ A ∧ rec_sum B = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hAvoid : AvoidsOne A := fun B hBA hsum => hnone B hBA hsum
  have hmajor : -(1 / 8 : ℝ) ≤
      (major_arc A 1 K).sum (fun h => (bernoulliProd A τ h).re) :=
    weighted_major_arc_bound hτ0 hτ1 hmean hA0 hN hM hH hK hKM hKlcm
      hLower hUpper hρ hρa hphase hsmall hmedium
  have minor_re_bound : ∀ s : Finset ℤ,
      s.sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8 →
      -(1 / 8 : ℝ) ≤ s.sum (fun h => (bernoulliProd A τ h).re) := by
    intro s hs
    have hpoint : ∀ h ∈ s,
        -bernoulliNormProd A τ h ≤ (bernoulliProd A τ h).re := by
      intro h hh
      rw [← bernoulliProd_norm]
      exact (abs_le.mp (Complex.abs_re_le_norm _)).1
    calc
      -(1 / 8 : ℝ) ≤ -s.sum (fun h => bernoulliNormProd A τ h) :=
        neg_le_neg hs
      _ = s.sum (fun h => -bernoulliNormProd A τ h) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ s.sum (fun h => (bernoulliProd A τ h).re) :=
        Finset.sum_le_sum hpoint
  have hminor1re := minor_re_bound (minor_arc₁ A 1 K T) hminor1
  have hminor2re := minor_re_bound (minor_arc₂ A 1 K T) hminor2
  let f : ℤ → ℝ := fun h => (bernoulliProd A τ h).re
  have hmajorSub : major_arc A 1 K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hminor1Sub : minor_arc₁ A 1 K T ⊆ j A \ major_arc A 1 K :=
    Finset.filter_subset _ _
  have hsplitOuter :
      (j A \ major_arc A 1 K).sum f + (major_arc A 1 K).sum f = (j A).sum f :=
    Finset.sum_sdiff hmajorSub
  have hsplitInner :
      (minor_arc₂ A 1 K T).sum f + (minor_arc₁ A 1 K T).sum f =
        (j A \ major_arc A 1 K).sum f := by
    simpa [minor_arc₂] using Finset.sum_sdiff hminor1Sub (f := f)
  have hjlower : -(3 / 8 : ℝ) ≤ (j A).sum f := by
    dsimp [f] at hmajor hminor1re hminor2re ⊢
    rw [← hsplitOuter, ← hsplitInner]
    linarith
  have hQ0 := lcm_ne_zero_of_zero_not_mem hA0
  have hzeroMem : (0 : ℤ) ∈ valid_sum_range (lcmA A) := zero_mem_valid_sum_range hQ0
  have hzeroProd : (bernoulliProd A τ 0).re = 1 := by
    simp [bernoulliProd, bernoulliFactor]
  have hvalidSplit :
      (valid_sum_range (lcmA A)).sum f = 1 + (j A).sum f := by
    rw [j, Finset.sum_erase_eq_sub hzeroMem]
    dsimp [f]
    rw [hzeroProd]
    ring
  have htotalLower : (5 / 8 : ℝ) ≤
      (valid_sum_range (lcmA A)).sum f := by
    rw [hvalidSplit]
    linarith
  have hfourier := weighted_fourier_eq_empty (A := A) (τ := τ) hA0 hAvoid hAtwo
  have hfourierRe := congrArg Complex.re hfourier
  have htotalEq :
      (valid_sum_range (lcmA A)).sum f =
        (lcmA A : ℝ) * (1 - τ) ^ A.card := by
    simpa only [f, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      using hfourierRe
  rw [htotalEq] at htotalLower
  linarith

private lemma weighted_fourier_real_lower
    {A : Finset ℕ} {N : ℕ} {τ M K H ρ T : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (K + 1) * Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8)
    (hminor1 :
      (minor_arc₁ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8)
    (hminor2 :
      (minor_arc₂ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8) :
    (5 / 8 : ℝ) ≤
      (valid_sum_range (lcmA A)).sum
        (fun h => (bernoulliProd A τ h).re) := by
  classical
  have hmajor : -(1 / 8 : ℝ) ≤
      (major_arc A 1 K).sum (fun h => (bernoulliProd A τ h).re) :=
    weighted_major_arc_bound hτ0 hτ1 hmean hA0 hN hM hH hK hKM hKlcm
      hLower hUpper hρ hρa hphase hsmall hmedium
  have minor_re_bound : ∀ s : Finset ℤ,
      s.sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8 →
      -(1 / 8 : ℝ) ≤ s.sum (fun h => (bernoulliProd A τ h).re) := by
    intro s hs
    have hpoint : ∀ h ∈ s,
        -bernoulliNormProd A τ h ≤ (bernoulliProd A τ h).re := by
      intro h hh
      rw [← bernoulliProd_norm]
      exact (abs_le.mp (Complex.abs_re_le_norm _)).1
    calc
      -(1 / 8 : ℝ) ≤ -s.sum (fun h => bernoulliNormProd A τ h) :=
        neg_le_neg hs
      _ = s.sum (fun h => -bernoulliNormProd A τ h) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ s.sum (fun h => (bernoulliProd A τ h).re) :=
        Finset.sum_le_sum hpoint
  have hminor1re := minor_re_bound (minor_arc₁ A 1 K T) hminor1
  have hminor2re := minor_re_bound (minor_arc₂ A 1 K T) hminor2
  let f : ℤ → ℝ := fun h => (bernoulliProd A τ h).re
  have hmajorSub : major_arc A 1 K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hminor1Sub : minor_arc₁ A 1 K T ⊆ j A \ major_arc A 1 K :=
    Finset.filter_subset _ _
  have hsplitOuter :
      (j A \ major_arc A 1 K).sum f + (major_arc A 1 K).sum f = (j A).sum f :=
    Finset.sum_sdiff hmajorSub
  have hsplitInner :
      (minor_arc₂ A 1 K T).sum f + (minor_arc₁ A 1 K T).sum f =
        (j A \ major_arc A 1 K).sum f := by
    simpa [minor_arc₂] using Finset.sum_sdiff hminor1Sub (f := f)
  have hjlower : -(3 / 8 : ℝ) ≤ (j A).sum f := by
    dsimp [f] at hmajor hminor1re hminor2re ⊢
    rw [← hsplitOuter, ← hsplitInner]
    linarith
  have hQ0 := lcm_ne_zero_of_zero_not_mem hA0
  have hzeroMem : (0 : ℤ) ∈ valid_sum_range (lcmA A) :=
    zero_mem_valid_sum_range hQ0
  have hzeroProd : (bernoulliProd A τ 0).re = 1 := by
    simp [bernoulliProd, bernoulliFactor]
  have hvalidSplit :
      (valid_sum_range (lcmA A)).sum f = 1 + (j A).sum f := by
    rw [j, Finset.sum_erase_eq_sub hzeroMem]
    dsimp [f]
    rw [hzeroProd]
    ring
  rw [hvalidSplit]
  linarith

private lemma weighted_circle_core_hoeffding
    {A : Finset ℕ} {N : ℕ} {τ M K H ρ T : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1)
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (K + 1) * Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8)
    (hminor1 :
      (minor_arc₁ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8)
    (hminor2 :
      (minor_arc₂ A 1 K T).sum (fun h => bernoulliNormProd A τ h) ≤ 1 / 8)
    (htail :
      (lcmA A : ℝ) *
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) < 5 / 8) :
    ∃ B : Finset ℕ, B ⊆ A ∧ rec_sum B = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hAvoid : AvoidsOne A := fun B hBA hsum => hnone B hBA hsum
  have htotalLower := weighted_fourier_real_lower hτ0 hτ1 hmean hA0 hN hM hH
    hK hKM hKlcm hLower hUpper hρ hρa hphase hsmall hmedium hminor1 hminor2
  have hfourier := weighted_fourier_eq_integer_mass (A := A) (τ := τ) hA0
  rw [integerReciprocalMassC_eq] at hfourier
  have hfourierRe := congrArg Complex.re hfourier
  have htotalEq :
      (valid_sum_range (lcmA A)).sum
          (fun h => (bernoulliProd A τ h).re) =
        (lcmA A : ℝ) * integerReciprocalMass A τ := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      using hfourierRe
  rw [htotalEq] at htotalLower
  have hmassTail := integerReciprocalMass_le_hoeffdingTail_of_avoids
    hτ0 hτ1 hmean hA0 hAvoid
  have hQnonneg : (0 : ℝ) ≤ lcmA A := by positivity
  have hscaledTail := mul_le_mul_of_nonneg_left hmassTail hQnonneg
  linarith

private lemma scaled_hoeffding_tail_lt
    {A : Finset ℕ} {N M S : ℕ} {τ : ℝ}
    (hM : 1 ≤ M) (hMN : M ≤ N) (hS : 1 ≤ S)
    (hA : A ⊆ Erdos297.GoodFactorization.goodDenominators N M S)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hscale : (24 : ℝ) * (N : ℝ) * (S : ℝ) ≤ (M : ℝ) ^ 2)
    (hQ : (Erdos297.GoodFactorization.smoothLcm S : ℝ) ≤
      Real.exp (5 * (S : ℝ))) :
    (lcmA A : ℝ) *
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) < 5 / 8 := by
  have htail :=
    Erdos297.FiniteHoeffding.abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm
      (fun _ => τ) (Nat.lt_of_lt_of_le Nat.zero_lt_one hM) hMN hS
      (hA.trans (Erdos297.GoodFactorization.goodDenominators_subset_Icc N M S))
      (fun _ _ => hτ0) (fun _ _ => hτ1) hscale hQ
  have hQdvd : lcmA A ∣ Erdos297.GoodFactorization.smoothLcm S :=
    Erdos297.GoodFactorization.lcm_dvd_smoothLcm hM hA
  have hsmoothPos : 0 < Erdos297.GoodFactorization.smoothLcm S :=
    Nat.lcmUpto_pos S
  have hQle : (lcmA A : ℝ) ≤
      Erdos297.GoodFactorization.smoothLcm S := by
    exact_mod_cast Nat.le_of_dvd hsmoothPos hQdvd
  have hQnonneg : (0 : ℝ) ≤ lcmA A := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htail hQnonneg
  calc
    (lcmA A : ℝ) *
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) ≤
        (lcmA A : ℝ) *
          (1 / (4 *
            (Erdos297.GoodFactorization.smoothLcm S : ℝ))) := hscaled
    _ ≤ 1 / 4 := by
      rw [mul_one_div]
      exact (div_le_iff₀ (mul_pos (by norm_num)
        (by exact_mod_cast hsmoothPos))).2 (by nlinarith)
    _ < 5 / 8 := by norm_num

private lemma weighted_circle_core_recip
    {A : Finset ℕ} {N k : ℕ} {τ M K H ρ T : ℝ}
    (hk : k ≠ 0) (hklcm : k ∣ lcmA A)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hmean : τ * (rec_sum A : ℝ) = 1 / (k : ℝ))
    (hAtwo : (rec_sum A : ℝ) < 2 / (k : ℝ))
    (hA0 : 0 ∉ A) (hN : 0 < N) (hM : 0 < M) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hKM : K ≤ M) (hKlcm : K < (lcmA A : ℝ))
    (hLower : ∀ n ∈ A, M ≤ (n : ℝ))
    (hUpper : ∀ n ∈ A, n ≤ N)
    (hρ : 0 ≤ ρ) (hρa : ρ ≤ τ * (1 - τ))
    (hphase : 2 * Real.pi * H / M ≤ 1)
    (hsmall :
      Real.exp (A.card * (8 * (2 * Real.pi * H / M) ^ 3)) - 1 ≤ 1)
    (hmedium :
      (2 * (k : ℝ) + 1) * (K + 1) *
        Real.exp (-(8 * ρ * A.card * H ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8)
    (hminor1 :
      (minor_arc₁ A k K T).sum
        (fun h => bernoulliNormProd A τ (h * (k : ℤ))) ≤ 1 / 8)
    (hminor2 :
      (minor_arc₂ A k K T).sum
        (fun h => bernoulliNormProd A τ (h * (k : ℤ))) ≤ 1 / 8)
    (hempty :
      (lcmA A : ℝ) * (1 - τ) ^ A.card < 5 / 8) :
    ∃ B : Finset ℕ, B ⊆ A ∧ rec_sum B = 1 / k := by
  classical
  by_contra hnone
  push Not at hnone
  have hAvoid : ∀ B ⊆ A, rec_sum B ≠ 1 / k :=
    fun B hBA hsum => hnone B hBA hsum
  have hmajor : -(1 / 8 : ℝ) ≤
      (major_arc A k K).sum
        (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) :=
    weighted_major_arc_bound_recip hk hklcm hτ0 hτ1 hmean hA0 hN hM hH
      hK hKM hKlcm hLower hUpper hρ hρa hphase hsmall hmedium
  have minor_re_bound : ∀ s : Finset ℤ,
      s.sum (fun h => bernoulliNormProd A τ (h * (k : ℤ))) ≤ 1 / 8 →
      -(1 / 8 : ℝ) ≤
        s.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) := by
    intro s hs
    have hpoint : ∀ h ∈ s,
        -bernoulliNormProd A τ (h * (k : ℤ)) ≤
          (bernoulliProd A τ (h * (k : ℤ))).re := by
      intro h hh
      rw [← bernoulliProd_norm]
      exact (abs_le.mp (Complex.abs_re_le_norm _)).1
    calc
      -(1 / 8 : ℝ) ≤
          -s.sum (fun h => bernoulliNormProd A τ (h * (k : ℤ))) :=
        neg_le_neg hs
      _ = s.sum (fun h => -bernoulliNormProd A τ (h * (k : ℤ))) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ s.sum (fun h => (bernoulliProd A τ (h * (k : ℤ))).re) :=
        Finset.sum_le_sum hpoint
  have hminor1re := minor_re_bound (minor_arc₁ A k K T) hminor1
  have hminor2re := minor_re_bound (minor_arc₂ A k K T) hminor2
  let f : ℤ → ℝ := fun h => (bernoulliProd A τ (h * (k : ℤ))).re
  have hmajorSub : major_arc A k K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hminor1Sub : minor_arc₁ A k K T ⊆ j A \ major_arc A k K :=
    Finset.filter_subset _ _
  have hsplitOuter :
      (j A \ major_arc A k K).sum f + (major_arc A k K).sum f = (j A).sum f :=
    Finset.sum_sdiff hmajorSub
  have hsplitInner :
      (minor_arc₂ A k K T).sum f + (minor_arc₁ A k K T).sum f =
        (j A \ major_arc A k K).sum f := by
    simpa [minor_arc₂] using Finset.sum_sdiff hminor1Sub (f := f)
  have hjlower : -(3 / 8 : ℝ) ≤ (j A).sum f := by
    dsimp [f] at hmajor hminor1re hminor2re ⊢
    rw [← hsplitOuter, ← hsplitInner]
    linarith
  have hQ0 := lcm_ne_zero_of_zero_not_mem hA0
  have hzeroMem : (0 : ℤ) ∈ valid_sum_range (lcmA A) :=
    zero_mem_valid_sum_range hQ0
  have hzeroProd : (bernoulliProd A τ (0 * (k : ℤ))).re = 1 := by
    simp [bernoulliProd, bernoulliFactor]
  have hvalidSplit :
      (valid_sum_range (lcmA A)).sum f = 1 + (j A).sum f := by
    rw [j, Finset.sum_erase_eq_sub hzeroMem]
    dsimp [f]
    rw [hzeroProd]
    ring
  have htotalLower : (5 / 8 : ℝ) ≤
      (valid_sum_range (lcmA A)).sum f := by
    rw [hvalidSplit]
    linarith
  have hfourier := weighted_fourier_eq_empty_recip
    (A := A) (k := k) (τ := τ) hk hA0 hAvoid hAtwo
  have hfourierRe := congrArg Complex.re hfourier
  have htotalEq :
      (valid_sum_range (lcmA A)).sum f =
        (lcmA A : ℝ) * (1 - τ) ^ A.card := by
    simpa only [f, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      using hfourierRe
  rw [htotalEq] at htotalLower
  linarith

/-! ## The density input

The inverse theorem in `UnitFractions.force_good_properties` has one
alternative which says that a substantial subset has unusually small
prime-power reciprocal support.  For a dense set this alternative is
impossible.  The following elementary Rankin bound is the needed bridge.

For `n`, `UnitFractions.my_function n` is the finset of the maximal prime
powers in the factorisation of `n`.  Expanding `2 ^ omega(n)` as the number
of subsets of that finset and then interchanging the two finite sums gives
an Euler product over `ppowers_in_set A`. -/

private lemma my_function_subset_ppowers_in_set {A : Finset ℕ} {n : ℕ}
    (hn : n ∈ A) : my_function n ⊆ ppowers_in_set A := by
  intro q hq
  simp only [my_function, Multiset.mem_toFinset, Finsupp.sum,
    Multiset.mem_sum, Multiset.mem_singleton] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact mem_ppowers_in_set'' hn (Finsupp.mem_support_iff.mp hp)

private lemma prod_my_function_subset_dvd {n : ℕ} (hn : n ≠ 0)
    {T : Finset ℕ} (hT : T ⊆ my_function n) : T.prod id ∣ n := by
  rw [← prod_my_function hn]
  exact Finset.prod_dvd_prod_of_subset T (my_function n) id hT

/-- A finite Euler-product moment estimate.  This is the quantitative
reason that a set with many prime factors but small prime-power reciprocal
support has density tending to zero. -/
private lemma sum_two_pow_omega_le
    {A : Finset ℕ} {N : ℕ} (hAN : A ⊆ Finset.Icc 1 N) :
    ∑ n ∈ A, (2 : ℝ) ^ ω n ≤
      (N : ℝ) * Real.exp (ppower_rec_sum A : ℝ) := by
  classical
  let Q := ppowers_in_set A
  have hA0 : 0 ∉ A := by
    intro h0
    have := (Finset.mem_Icc.mp (hAN h0)).1
    omega
  have hexpand :
      ∑ n ∈ A, (2 : ℝ) ^ ω n =
        ∑ n ∈ A, ∑ T ∈ Q.powerset,
          if T ⊆ my_function n then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    have hsub : my_function n ⊆ Q :=
      my_function_subset_ppowers_in_set hn
    have hfilter :
        Q.powerset.filter (fun T ↦ T ⊆ my_function n) =
          (my_function n).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨h.trans hsub, h⟩
    calc
      (2 : ℝ) ^ ω n = ((2 ^ ω n : ℕ) : ℝ) := by norm_num
      _ = (((my_function n).powerset.card : ℕ) : ℝ) := by
        rw [Finset.card_powerset, card_my_function]
      _ = ((Q.powerset.filter (fun T ↦ T ⊆ my_function n)).card : ℝ) := by
        rw [hfilter]
      _ = ∑ T ∈ Q.powerset,
          if T ⊆ my_function n then (1 : ℝ) else 0 := by simp
  rw [hexpand, Finset.sum_comm]
  have hterm : ∀ T ∈ Q.powerset,
      ∑ n ∈ A, (if T ⊆ my_function n then (1 : ℝ) else 0) ≤
        (N : ℝ) / (T.prod id : ℕ) := by
    intro T hTQ
    let E := A.filter (fun n ↦ T ⊆ my_function n)
    have hsum :
        ∑ n ∈ A, (if T ⊆ my_function n then (1 : ℝ) else 0) =
          (E.card : ℝ) := by simp [E]
    rw [hsum]
    have hprod0 : T.prod id ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      have hqQ : q ∈ Q := (Finset.mem_powerset.mp hTQ) hq
      exact ne_of_mem_of_not_mem hqQ zero_not_mem_ppowers_in_set
    have hprod1 : 1 ≤ T.prod id := Nat.one_le_iff_ne_zero.mpr hprod0
    have hEsub : E ⊆ (Finset.Icc 1 N).filter (fun n ↦ T.prod id ∣ n) := by
      intro n hn
      change n ∈ A.filter (fun n ↦ T ⊆ my_function n) at hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      refine ⟨hAN hn.1, ?_⟩
      exact prod_my_function_subset_dvd
        (Nat.ne_of_gt (Finset.mem_Icc.mp (hAN hn.1)).1) hn.2
    have hcard : (E.card : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n ↦ T.prod id ∣ n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hEsub
    exact hcard.trans (count_multiples''' hprod1)
  calc
    ∑ T ∈ Q.powerset,
        ∑ n ∈ A, (if T ⊆ my_function n then (1 : ℝ) else 0) ≤
        ∑ T ∈ Q.powerset, (N : ℝ) / (T.prod id : ℕ) :=
      Finset.sum_le_sum hterm
    _ = (N : ℝ) * ∏ q ∈ Q, (1 + (1 : ℝ) / q) := by
      rw [Finset.prod_one_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const_one, div_eq_mul_inv, Nat.cast_prod, id_eq]
      ring
    _ ≤ (N : ℝ) * Real.exp (∑ q ∈ Q, (1 : ℝ) / q) := by
      gcongr
      exact Real.prod_one_add_le_exp_sum Q (fun q ↦ by positivity)
    _ = (N : ℝ) * Real.exp (ppower_rec_sum A : ℝ) := by
      congr 2
      rw [ppower_rec_sum]
      push_cast
      rfl

private lemma card_le_exp_neg_loglog_of_low_ppower
    {A : Finset ℕ} {N : ℕ}
    (hAN : A ⊆ Finset.Icc 1 N)
    (hloglog : 0 ≤ Real.log (Real.log (N : ℝ)))
    (hreg : arith_regular N A)
    (hpp : (ppower_rec_sum A : ℝ) ≤
      (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ))) :
    (A.card : ℝ) ≤
      (N : ℝ) * Real.exp (-(1 / 75 : ℝ) *
        Real.log (Real.log (N : ℝ))) := by
  let L := Real.log (Real.log (N : ℝ))
  have hpoint : ∀ n ∈ A,
      Real.exp ((17 / 25 : ℝ) * L) ≤ (2 : ℝ) ^ ω n := by
    intro n hn
    have homega := (hreg n hn).1
    have hlog2 : (69 / 100 : ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      norm_num at h ⊢
      linarith
    have hcoef : (17 / 25 : ℝ) ≤ (69 / 100) * (99 / 100) := by norm_num
    have hfirst : (17 / 25 : ℝ) * L ≤
        ((69 / 100 : ℝ) * (99 / 100)) * L :=
      mul_le_mul_of_nonneg_right hcoef (by simpa [L] using hloglog)
    have hsecond : ((69 / 100 : ℝ) * (99 / 100)) * L ≤
        Real.log 2 * (ω n : ℝ) := by
      calc
        ((69 / 100 : ℝ) * (99 / 100)) * L =
            (69 / 100 : ℝ) * ((99 / 100) * L) := by ring
        _ ≤ (69 / 100 : ℝ) * (ω n : ℝ) := by
          gcongr
        _ ≤ Real.log 2 * (ω n : ℝ) := by
          gcongr
    calc
      Real.exp ((17 / 25 : ℝ) * L) ≤
          Real.exp (Real.log 2 * (ω n : ℝ)) :=
        Real.exp_le_exp.mpr (hfirst.trans hsecond)
      _ = (2 : ℝ) ^ ω n := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlower :
      (A.card : ℝ) * Real.exp ((17 / 25 : ℝ) * L) ≤
        ∑ n ∈ A, (2 : ℝ) ^ ω n := by
    calc
      (A.card : ℝ) * Real.exp ((17 / 25 : ℝ) * L) =
          ∑ _n ∈ A, Real.exp ((17 / 25 : ℝ) * L) := by simp
      _ ≤ ∑ n ∈ A, (2 : ℝ) ^ ω n := Finset.sum_le_sum hpoint
  have hmiddle := hlower.trans (sum_two_pow_omega_le hAN)
  have huppExp : Real.exp (ppower_rec_sum A : ℝ) ≤
      Real.exp ((2 / 3 : ℝ) * L) := by
    exact Real.exp_le_exp.mpr (by simpa [L] using hpp)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hcombined :
      (A.card : ℝ) * Real.exp ((17 / 25 : ℝ) * L) ≤
        (N : ℝ) * Real.exp ((2 / 3 : ℝ) * L) :=
    hmiddle.trans (mul_le_mul_of_nonneg_left huppExp hN0)
  apply le_of_mul_le_mul_right _ (Real.exp_pos ((17 / 25 : ℝ) * L))
  calc
    (A.card : ℝ) * Real.exp ((17 / 25 : ℝ) * L) ≤
        (N : ℝ) * Real.exp ((2 / 3 : ℝ) * L) := hcombined
    _ = ((N : ℝ) * Real.exp (-(1 / 75 : ℝ) * L)) *
        Real.exp ((17 / 25 : ℝ) * L) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private lemma top_interval_rec_sum_succ {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (rec_sum (Finset.Ioc (N - m) N) : ℝ) =
      1 / (N : ℝ) +
        (rec_sum (Finset.Ioc ((N - 1) - (m - 1)) (N - 1)) : ℝ) := by
  have hN : 0 < N := lt_of_lt_of_le hm hmN
  have hcut : (N - 1) - (m - 1) = N - m := by omega
  have hset : Finset.Ioc (N - m) N =
      insert N (Finset.Ioc (N - m) (N - 1)) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hnot : N ∉ Finset.Ioc (N - m) (N - 1) := by
    intro h
    have := (Finset.mem_Ioc.mp h).2
    omega
  rw [hcut, hset]
  simp only [rec_sum, Rat.cast_sum, one_div]
  rw [Finset.sum_insert hnot]
  all_goals simp_all

/-- Of all `m`-element subsets of `[1,N]`, the final interval has the
smallest reciprocal sum. -/
private lemma top_interval_minimizes_rec_sum {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) :
    (rec_sum (Finset.Ioc (N - A.card) N) : ℝ) ≤ (rec_sum A : ℝ) := by
  classical
  induction N using Nat.strong_induction_on generalizing A with
  | h N ih =>
      by_cases hAempty : A = ∅
      · simp [hAempty]
      have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAempty
      have hNpos : 0 < N := by
        obtain ⟨n, hn⟩ := hAne
        exact lt_of_lt_of_le (Finset.mem_Icc.mp (hAN hn)).1
          (Finset.mem_Icc.mp (hAN hn)).2
      let a := A.max' hAne
      let A' := A.erase a
      have haA : a ∈ A := Finset.max'_mem A hAne
      have haBounds := Finset.mem_Icc.mp (hAN haA)
      have hA'sub : A' ⊆ Finset.Icc 1 (N - 1) := by
        intro n hn
        have hnData := Finset.mem_erase.mp hn
        have hnBounds := Finset.mem_Icc.mp (hAN hnData.2)
        have hna : n < a := by
          exact A.lt_max'_of_mem_erase_max' hAne
            (by simpa [A', a] using hn)
        exact Finset.mem_Icc.mpr ⟨hnBounds.1, by omega⟩
      have hcardA' : A'.card = A.card - 1 := by
        simp [A', haA]
      have hcardAN : A.card ≤ N := by
        have hcard := Finset.card_le_card hAN
        simpa [Nat.card_Icc, hNpos] using hcard
      have hrec' := ih (N - 1) (by omega) hA'sub
      have htop := top_interval_rec_sum_succ
        (N := N) (m := A.card) (Finset.card_pos.mpr hAne) hcardAN
      have haPos : (0 : ℝ) < a := by exact_mod_cast haBounds.1
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hinv : 1 / (N : ℝ) ≤ 1 / (a : ℝ) :=
        one_div_le_one_div_of_le haPos (by exact_mod_cast haBounds.2)
      have hrecA : (rec_sum A : ℝ) =
          1 / (a : ℝ) + (rec_sum A' : ℝ) := by
        rw [← Finset.insert_erase haA]
        simp [rec_sum, A']
      rw [hcardA'] at hrec'
      rw [htop, hrecA]
      exact add_le_add hinv hrec'

private lemma log_ratio_succ_le_top_rec_sum {a N : ℕ}
    (ha : 1 ≤ a) (haN : a ≤ N) :
    Real.log (((N + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) ≤
      (rec_sum (Finset.Ioc a N) : ℝ) := by
  rw [cast_rec_sum_Ioc]
  calc
    Real.log (((N + 1 : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)) =
        Real.log (N + 1 : ℕ) - Real.log (a + 1 : ℕ) := by
      rw [Real.log_div] <;> positivity
    _ = ∑ k ∈ Finset.Ico a N,
        (Real.log (k + 2 : ℕ) - Real.log (k + 1 : ℕ)) := by
      convert (Finset.sum_Ico_sub (fun k : ℕ ↦ Real.log (k + 1)) haN).symm using 1
      all_goals norm_num
      all_goals ring_nf
    _ ≤ ∑ k ∈ Finset.Ico a N, (((k + 1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hratioPos : 0 < (((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ)) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hratioPos
      rw [Real.log_div (by positivity) (by positivity)] at hlog
      have hid :
          (((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ)) - 1 =
            (((k + 1 : ℕ) : ℝ))⁻¹ := by
        push_cast
        field_simp
        ring_nf
      rw [hid] at hlog
      exact hlog

private noncomputable def denseCutoff (eta : ℝ) (N : ℕ) : ℕ :=
  ⌈(1 / Real.exp 1 - eta / 2) * (N : ℝ)⌉₊

private lemma dense_log_ratio_tendsto {eta : ℝ}
    (hc : 0 < 1 / Real.exp 1 - eta / 2) :
    Tendsto
      (fun N : ℕ ↦ Real.log (((N + 1 : ℕ) : ℝ) /
        ((denseCutoff eta N + 1 : ℕ) : ℝ))) atTop
      (nhds (Real.log (1 / (1 / Real.exp 1 - eta / 2)))) := by
  let c : ℝ := 1 / Real.exp 1 - eta / 2
  have hc' : 0 ≤ c := hc.le
  have hceil :
      Tendsto
        (fun N : ℕ ↦ ((⌈c * (N : ℝ)⌉₊ : ℕ) : ℝ) / (N : ℝ))
        atTop (nhds c) :=
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc').comp
      tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hden0 := hceil.add hone
  rw [add_zero] at hden0
  have hden : Tendsto
      (fun N : ℕ ↦ ((denseCutoff eta N + 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds c) := by
    apply hden0.congr'
    filter_upwards with N
    simp only [denseCutoff, c, Nat.cast_add, Nat.cast_one, add_div]
  have hself : Tendsto (fun N : ℕ ↦ (N : ℝ) / (N : ℝ)) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]
  have hnum0 := hself.add hone
  rw [add_zero] at hnum0
  have hnum : Tendsto
      (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) / (N : ℝ))) atTop (nhds 1) := by
    apply hnum0.congr'
    filter_upwards with N
    simp [Nat.cast_add, add_div]
  have hratio := hnum.div hden hc.ne'
  have hratio' : Tendsto
      (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) /
        ((denseCutoff eta N + 1 : ℕ) : ℝ))) atTop
      (nhds (1 / c)) := by
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hcutPos : (0 : ℝ) < denseCutoff eta N + 1 := by positivity
    change ((((N + 1 : ℕ) : ℝ) / (N : ℝ)) /
      (((denseCutoff eta N + 1 : ℕ) : ℝ) / (N : ℝ))) =
        ((N + 1 : ℕ) : ℝ) / ((denseCutoff eta N + 1 : ℕ) : ℝ)
    field_simp [hNR, hcutPos.ne']
  change Tendsto
    (Real.log ∘ (fun N : ℕ ↦ (((N + 1 : ℕ) : ℝ) /
      ((denseCutoff eta N + 1 : ℕ) : ℝ)))) atTop
    (nhds (Real.log (1 / c)))
  exact (Real.continuousAt_log (one_div_ne_zero hc.ne')).tendsto.comp hratio'

private noncomputable def densityMassMargin (eta : ℝ) : ℝ :=
  (Real.log (1 / (1 / Real.exp 1 - eta / 2)) - 1) / 4

private lemma densityMassMargin_pos {eta : ℝ} (heta : 0 < eta)
    (hc : 0 < 1 / Real.exp 1 - eta / 2) :
    0 < densityMassMargin eta := by
  have hcoeff : 1 / Real.exp 1 - eta / 2 < 1 / Real.exp 1 := by linarith
  have hinv : Real.exp 1 < 1 / (1 / Real.exp 1 - eta / 2) := by
    have h := one_div_lt_one_div_of_lt hc hcoeff
    simpa [one_div_div] using h
  have hlog : 1 < Real.log (1 / (1 / Real.exp 1 - eta / 2)) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (1 / (1 / Real.exp 1 - eta / 2)) :=
        Real.log_lt_log (Real.exp_pos 1) hinv
  simp only [densityMassMargin]
  linarith

private lemma eventually_denseCutoff_mass {eta : ℝ} (heta : 0 < eta)
    (hc : 0 < 1 / Real.exp 1 - eta / 2) :
    ∀ᶠ N : ℕ in atTop,
      1 + 3 * densityMassMargin eta ≤
        (rec_sum (Finset.Ioc (denseCutoff eta N) N) : ℝ) := by
  have hmargin := densityMassMargin_pos heta hc
  have hlimit :
      1 + 3 * densityMassMargin eta <
        Real.log (1 / (1 / Real.exp 1 - eta / 2)) := by
    dsimp [densityMassMargin] at hmargin ⊢
    linarith
  have hlogEv := (dense_log_ratio_tendsto hc).eventually
    (eventually_gt_nhds hlimit)
  have hcutRatio := (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
    tendsto_natCast_atTop_atTop
  have hcLtOne : 1 / Real.exp 1 - eta / 2 < 1 := by
    have he : 1 / Real.exp 1 < 1 := by
      rw [one_div, inv_lt_one₀ (Real.exp_pos 1)]
      exact Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hcutLeEv := hcutRatio.eventually (eventually_lt_nhds hcLtOne)
  filter_upwards [hlogEv, hcutLeEv, eventually_ge_atTop 1] with N hlog hcutRatioN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcutLe : denseCutoff eta N ≤ N := by
    have hlt : (denseCutoff eta N : ℝ) < N := by
      exact (div_lt_one hNpos).mp (by simpa [denseCutoff] using hcutRatioN)
    exact_mod_cast hlt.le
  have hcutOne : 1 ≤ denseCutoff eta N := by
    have hceil := Nat.le_ceil ((1 / Real.exp 1 - eta / 2) * (N : ℝ))
    have hpos : 0 < (1 / Real.exp 1 - eta / 2) * (N : ℝ) := mul_pos hc hNpos
    have : (0 : ℝ) < denseCutoff eta N := by
      simpa [denseCutoff] using hpos.trans_le hceil
    exact_mod_cast this
  exact hlog.le.trans (log_ratio_succ_le_top_rec_sum hcutOne hcutLe)

private lemma card_sdiff_lower_real (A D : Finset ℕ) :
    (A.card : ℝ) - (D.card : ℝ) ≤ ((A \ D).card : ℝ) := by
  have hsub : A ⊆ (A \ D) ∪ D := by
    intro n hn
    by_cases hnD : n ∈ D
    · simp [hnD]
    · simp [hn, hnD]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (A \ D) D
  have hcast : (A.card : ℝ) ≤ ((A \ D).card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast (by omega : A.card ≤ (A \ D).card + D.card)
  linarith

/-- Uniform density preprocessing.  From any set whose density exceeds the
critical value by `eta`, remove small denominators, arithmetically irregular
integers, and integers having a prime-power factor above the smoothness
cutoff.  The remaining set still has reciprocal mass uniformly above one. -/
private lemma eventually_dense_regular_smooth_core {eta : ℝ}
    (heta : 0 < eta) (hc : 0 < 1 / Real.exp 1 - eta / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      (1 - 1 / Real.exp 1 + eta) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ C : Finset ℕ, C ⊆ A ∧
        (∀ n ∈ C, eta * (N : ℝ) / 32 ≤ (n : ℝ)) ∧
        arith_regular N C ∧
        (∀ n ∈ C,
          is_smooth ((N : ℝ) ^
            (1 - 8 / Real.log (Real.log (N : ℝ)))) n) ∧
        1 + 3 * densityMassMargin eta ≤ (rec_sum C : ℝ) := by
  let D : ℝ := 128 / eta
  have hD : 0 < D := div_pos (by norm_num) heta
  filter_upwards
      [filter_regular D hD, filter_smooth D hD,
        eventually_denseCutoff_mass heta hc,
        tendsto_natCast_atTop_atTop.eventually
          (eventually_ge_atTop (16 / eta : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with
      N hreg hsmooth hmass hNlarge hN A hAN hAcard
  classical
  let A₀ : Finset ℕ := A.erase N
  let R : Finset ℕ := A₀.filter fun n : ℕ =>
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * Real.log (Real.log (N : ℝ)) ≤ ω n ∧
      (ω n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ)))
  let S : Finset ℕ := A₀.filter fun n : ℕ =>
    ∃ q : ℕ, IsPrimePow q ∧
      ((N : ℝ) ^ (1 - 8 / Real.log (Real.log (N : ℝ))) < (q : ℝ) ∧ q ∣ n)
  let E : Finset ℕ := A₀.filter fun n : ℕ => (n : ℝ) < eta * (N : ℝ) / 32
  let C : Finset ℕ := A₀ \ (E ∪ R ∪ S)
  have hA₀A : A₀ ⊆ A := Finset.erase_subset _ _
  have hA₀range : A₀ ⊆ Finset.range N := by
    intro n hn
    have hnA := hA₀A hn
    have hnN := (Finset.mem_Icc.mp (hAN hnA)).2
    have hnNe : n ≠ N := (Finset.mem_erase.mp hn).1
    exact Finset.mem_range.mpr (lt_of_le_of_ne hnN hnNe)
  have hRcard : (R.card : ℝ) ≤ (N : ℝ) / D := by
    simpa [R] using hreg A₀ hA₀range
  have hScard : (S.card : ℝ) ≤ (N : ℝ) / D := by
    simpa [S] using hsmooth A₀ hA₀range
  have hEsub : E ⊆ Finset.range ⌈eta * (N : ℝ) / 32⌉₊ := by
    intro n hn
    have hnlt : (n : ℝ) < eta * (N : ℝ) / 32 := (Finset.mem_filter.mp hn).2
    exact Finset.mem_range.mpr ((Nat.lt_ceil).2 hnlt)
  have hEcardNat : E.card ≤ ⌈eta * (N : ℝ) / 32⌉₊ := by
    simpa using Finset.card_le_card hEsub
  have hceil : (⌈eta * (N : ℝ) / 32⌉₊ : ℝ) <
      eta * (N : ℝ) / 32 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg heta.le (by positivity)) (by norm_num))
  have hEcard : (E.card : ℝ) ≤ eta * (N : ℝ) / 32 + 1 := by
    have hcast : (E.card : ℝ) ≤ (⌈eta * (N : ℝ) / 32⌉₊ : ℝ) := by
      exact_mod_cast hEcardNat
    exact hcast.trans hceil.le
  have hbadCard : (((E ∪ R ∪ S).card : ℕ) : ℝ) ≤
      eta * (N : ℝ) / 32 + 1 +
        (N : ℝ) / D + (N : ℝ) / D := by
    have hcardNat := (Finset.card_union_le (E ∪ R) S).trans
      (Nat.add_le_add_right (Finset.card_union_le E R) S.card)
    have hcast : (((E ∪ R ∪ S).card : ℕ) : ℝ) ≤
        (E.card : ℝ) + (R.card : ℝ) + (S.card : ℝ) := by
      exact_mod_cast hcardNat
    exact hcast.trans (add_le_add (add_le_add hEcard hRcard) hScard)
  have hlargeEta : (16 : ℝ) ≤ eta * (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hNlarge heta.le
    field_simp [heta.ne'] at this
    simpa [mul_comm] using this
  have hbadSmall : (((E ∪ R ∪ S).card : ℕ) : ℝ) ≤
      eta * (N : ℝ) / 4 := by
    apply hbadCard.trans
    dsimp [D]
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    have hetaN : 0 ≤ eta * (N : ℝ) := mul_nonneg heta.le hNnonneg
    field_simp [heta.ne']
    nlinarith
  have hA₀card : (A.card : ℝ) - 1 ≤ (A₀.card : ℝ) := by
    dsimp [A₀]
    by_cases hNA : N ∈ A
    · have hpos : 1 ≤ A.card := Finset.one_le_card.mpr ⟨N, hNA⟩
      rw [Finset.card_erase_of_mem hNA, Nat.cast_sub hpos]
      norm_num
    · simp [hNA]
  have hCcard0 := card_sdiff_lower_real A₀ (E ∪ R ∪ S)
  have hCcard :
      (1 - 1 / Real.exp 1 + eta / 2) * (N : ℝ) ≤ (C.card : ℝ) := by
    dsimp [C]
    nlinarith [hlargeEta]
  have hCA₀ : C ⊆ A₀ := Finset.sdiff_subset
  have hCA : C ⊆ A := hCA₀.trans hA₀A
  have hCcardN : C.card ≤ N := by
    have := Finset.card_le_card (hCA.trans hAN)
    simpa [Nat.card_Icc, hN] using this
  have hcut : N - C.card ≤ denseCutoff eta N := by
    have hsubCast : ((N - C.card : ℕ) : ℝ) = (N : ℝ) - (C.card : ℝ) := by
      rw [Nat.cast_sub hCcardN]
    have hreal : (N : ℝ) - (C.card : ℝ) ≤
        (1 / Real.exp 1 - eta / 2) * (N : ℝ) := by
      linarith
    have hceil := Nat.le_ceil ((1 / Real.exp 1 - eta / 2) * (N : ℝ))
    exact_mod_cast (hsubCast ▸ hreal.trans hceil)
  have hintervalSub : Finset.Ioc (denseCutoff eta N) N ⊆
      Finset.Ioc (N - C.card) N := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨lt_of_le_of_lt hcut hn.1, hn.2⟩
  have hmassC : 1 + 3 * densityMassMargin eta ≤ (rec_sum C : ℝ) := by
    calc
      1 + 3 * densityMassMargin eta ≤
          (rec_sum (Finset.Ioc (denseCutoff eta N) N) : ℝ) := hmass
      _ ≤ (rec_sum (Finset.Ioc (N - C.card) N) : ℝ) := by
        exact_mod_cast rec_sum_mono hintervalSub
      _ ≤ (rec_sum C : ℝ) := top_interval_minimizes_rec_sum (hCA.trans hAN)
  refine ⟨C, hCA, ?_, ?_, ?_, hmassC⟩
  · intro n hn
    have hnE : n ∉ E := by
      intro hnE
      exact (Finset.mem_sdiff.mp hn).2 (by simp [hnE])
    have := not_lt.mp (fun hlt => hnE (Finset.mem_filter.mpr ⟨hCA₀ hn, hlt⟩))
    simpa [E] using this
  · intro n hn
    have hnR : n ∉ R := by
      intro hnR
      exact (Finset.mem_sdiff.mp hn).2 (by simp [hnR])
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp (hAN (hCA hn))).1
    by_contra hbad
    exact hnR (Finset.mem_filter.mpr ⟨hCA₀ hn, hn0, hbad⟩)
  · intro n hn q hq hqn
    by_contra hqbig
    have hnS : n ∈ S := by
      simp only [S, Finset.mem_filter]
      exact ⟨hCA₀ hn, ⟨q, hq, lt_of_not_ge hqbig, hqn⟩⟩
    exact (Finset.mem_sdiff.mp hn).2 (by simp [hnS])

private lemma eventually_pruning_loss_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop,
      2 * (Real.log (N : ℝ)) ^ (-(1 / 100 : ℝ)) *
          Real.log (Real.log (N : ℝ)) ≤ d := by
  have hlarge := large_enough_N 1 (by norm_num : (0 : ℝ) < 1)
  have hp := tendsto_coe_log_pow_at_top (1 / 200 : ℝ) (by norm_num)
  filter_upwards
      [hlarge, hp.eventually (eventually_ge_atTop (1 / d : ℝ))] with
      N hN hpow
  rcases hN with
    ⟨-, -, -, -, -, hlog, -, -, -, -, -, -, -, -, -, hthreshold,
      -, -, -, -, -⟩
  have hPpos : 0 < (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hsmall : (Real.log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ d := by
    rw [Real.rpow_neg hlog.le]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hPpos).2
    have hd0 : 0 ≤ d := hd.le
    calc
      (1 : ℝ) = d * (1 / d) := by field_simp [hd.ne']
      _ ≤ d * (Real.log (N : ℝ)) ^ (1 / 200 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hd0
  exact hthreshold.trans hsmall

private lemma eventually_low_ppower_reciprocal_small {eta : ℝ}
    (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ,
      B ⊆ Finset.Icc 1 N →
      (∀ n ∈ B, eta * (N : ℝ) / 32 ≤ (n : ℝ)) →
      arith_regular N B →
      (ppower_rec_sum B : ℝ) ≤
        (2 / 3 : ℝ) * Real.log (Real.log (N : ℝ)) →
      (rec_sum B : ℝ) < 1 / 3 := by
  let c : ℝ := 1 / 75
  have hc : 0 < c := by norm_num
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecayPow : Tendsto
      (fun N : ℕ ↦ (Real.log (N : ℝ)) ^ (-c)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hc).comp hlogTop
  have hlogPos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_gt_atTop 0)
  have hdecay : Tendsto
      (fun N : ℕ ↦ Real.exp (-c * Real.log (Real.log (N : ℝ))))
      atTop (nhds 0) := by
    apply hdecayPow.congr'
    filter_upwards [hlogPos] with N hlog
    rw [Real.rpow_def_of_pos hlog]
    ring_nf
  have hscaled : Tendsto
      (fun N : ℕ ↦ (32 / eta) *
        Real.exp (-c * Real.log (Real.log (N : ℝ))))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hdecay :
      Tendsto
        (fun N : ℕ ↦ (32 / eta) *
          Real.exp (-c * Real.log (Real.log (N : ℝ))))
        atTop (nhds ((32 / eta) * 0)))
  have hsmall := hscaled.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 3 by norm_num))
  have hloglogPos : ∀ᶠ N : ℕ in atTop,
      0 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp hlogTop).eventually (eventually_ge_atTop 0)
  filter_upwards [hsmall, hloglogPos, eventually_ge_atTop (1 : ℕ)] with
      N hsmallN hloglog hN B hBN hLower hreg hpp
  have hcard := card_le_exp_neg_loglog_of_low_ppower hBN hloglog hreg hpp
  have hM : 0 < eta * (N : ℝ) / 32 := by
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    positivity
  have hrec := rec_sum_le_card_div hM hLower
  calc
    (rec_sum B : ℝ) ≤ (B.card : ℝ) / (eta * (N : ℝ) / 32) := hrec
    _ ≤ ((N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)))) /
        (eta * (N : ℝ) / 32) := by
      apply div_le_div_of_nonneg_right _ hM.le
      simpa [c] using hcard
    _ = (32 / eta) * Real.exp (-c * Real.log (Real.log (N : ℝ))) := by
      have hNne : (N : ℝ) ≠ 0 := by positivity
      field_simp [heta.ne', hNne]
    _ < 1 / 3 := by simpa using hsmallN

/-- The inverse-theorem input extracted from a dense set.  The first
alternative of `force_good_properties` is excluded by the preceding Euler
moment estimate. -/
private lemma eventually_dense_inverse_good {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hc : 0 < 1 / Real.exp 1 - eta / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      (1 - 1 / Real.exp 1 + eta) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ P : Finset ℕ, P ⊆ A ∧
        (∀ n ∈ P, eta * (N : ℝ) / 32 ≤ (n : ℝ)) ∧
        (∀ n ∈ P,
          is_smooth ((N : ℝ) ^
            (1 - 8 / Real.log (Real.log (N : ℝ)))) n) ∧
        1 + 2 * densityMassMargin eta ≤ (rec_sum P : ℝ) ∧
        (∀ q ∈ ppowers_in_set P,
          (Real.log (N : ℝ)) ^ (-(1 / 100 : ℝ)) ≤
            (rec_sum_local P q : ℝ)) ∧
        good_condition P
          ((eta * (N : ℝ) / 32) *
            (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))))
          ((eta * (N : ℝ) / 32) / Real.log (N : ℝ))
          ((eta * (N : ℝ) / 32) /
            (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))) := by
  let δ := densityMassMargin eta
  have hδ : 0 < δ := densityMassMargin_pos heta hc
  have hcore := eventually_dense_regular_smooth_core heta hc
  have hloss := eventually_pruning_loss_le hδ
  have hlow := eventually_low_ppower_reciprocal_small heta
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hcore, hloss, hlow, pruning_lemma_one, force_good_properties,
        tendsto_natCast_atTop_atTop.eventually
          (eventually_ge_atTop ((32 / eta) ^ 2 : ℝ)),
        hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with
      N hcoreN hlossN hlowN hprune hforce hNlarge hlog hN A hAN hAcard
  obtain ⟨C, hCA, hClower, hCreg, hCsmooth, hCmass⟩ := hcoreN A hAN hAcard
  have hCrange : C ⊆ Finset.range (N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp (hAN (hCA hn))).2)
  have heps : 0 < (Real.log (N : ℝ)) ^ (-(1 / 100 : ℝ)) := by
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) _
  obtain ⟨P, hPC, hPmass0, hPlocal0⟩ :=
    hprune C hCrange ((Real.log (N : ℝ)) ^ (-(1 / 100 : ℝ))) heps
  have hPA : P ⊆ A := hPC.trans hCA
  have hPrange : P ⊆ Finset.range (N + 1) := hPC.trans hCrange
  have hP0 : 0 ∉ P := by
    intro hzero
    have := (Finset.mem_Icc.mp (hAN (hPA hzero))).1
    omega
  have hPlower : ∀ n ∈ P, eta * (N : ℝ) / 32 ≤ (n : ℝ) :=
    fun n hn ↦ hClower n (hPC hn)
  have hPreg : arith_regular N P := hCreg.subset hPC
  have hPsmooth : ∀ n ∈ P,
      is_smooth ((N : ℝ) ^
        (1 - 8 / Real.log (Real.log (N : ℝ)))) n :=
    fun n hn ↦ hCsmooth n (hPC hn)
  have hPmass : 1 + 2 * δ ≤ (rec_sum P : ℝ) := by
    linarith
  have hMpos : 0 < eta * (N : ℝ) / 32 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    positivity
  have hMN : eta * (N : ℝ) / 32 ≤ (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hNM2 : (N : ℝ) ≤ (eta * (N : ℝ) / 32) ^ 2 := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hquot : 32 / eta ≤ Real.sqrt (N : ℝ) := by
      have hsqrt := Real.sqrt_le_sqrt hNlarge
      rw [Real.sqrt_sq (by positivity : 0 ≤ 32 / eta)] at hsqrt
      simpa using hsqrt
    have hmul : 32 ≤ eta * Real.sqrt (N : ℝ) := by
      rw [div_le_iff₀ heta] at hquot
      simpa [mul_comm] using hquot
    have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    rw [← Real.sq_sqrt hNpos.le]
    nlinarith [sq_nonneg (eta * Real.sqrt (N : ℝ) / 32 - 1)]
  have hrecThreshold :
      (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ (rec_sum P : ℝ) := by
    have hpow : (Real.log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
    exact hpow.trans (by linarith [hδ])
  have hPlocal : ∀ q ∈ ppowers_in_set P,
      (Real.log (N : ℝ)) ^ (-(1 / 100 : ℝ)) ≤
        (rec_sum_local P q : ℝ) := by
    intro q hq
    exact le_of_lt (hPlocal0 q hq)
  have hforceP := hforce (eta * (N : ℝ) / 32) P hPrange hMpos hMN hNM2
    hP0 hPlower hPreg hrecThreshold hPlocal
  rcases hforceP with hbad | hgood
  · obtain ⟨B, hBP, hPBmass, hBpp⟩ := hbad
    have hBsmall := hlowN B (hBP.trans (hPA.trans hAN))
      (fun n hn ↦ hPlower n (hBP hn)) (hPreg.subset hBP) hBpp
    have hPBmass' : (rec_sum P : ℝ) ≤ 3 * (rec_sum B : ℝ) := by
      exact_mod_cast hPBmass
    exfalso
    nlinarith [hPmass, hδ]
  · refine ⟨P, hPA, hPlower, hPsmooth, ?_, hPlocal, ?_⟩
    · simpa [δ] using hPmass
    · simpa using hgood

/-- Any fixed power of `log N` is dominated by the subpower
`N^(c/log log N)`.  This is the common asymptotic comparison behind the
minor-arc, major-arc, and smooth-lcm numerical estimates below. -/
private lemma tendsto_subpower_div_log_rpow (c k : ℝ) (hc : 0 < c) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) /
          (Real.log (N : ℝ)) ^ k)
      atTop atTop := by
  have hx : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hratio : Tendsto
      (fun N : ℕ ↦ c * Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ)) ^ (2 : ℕ)) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_mul_add_div_pow_log_at_top c 0 2 hc).comp hx
  have hratioSub : Tendsto
      (fun N : ℕ ↦ c * Real.log (N : ℝ) /
        Real.log (Real.log (N : ℝ)) ^ (2 : ℕ) - k) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-k) hratio
  have hprod : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ)) *
        (c * Real.log (N : ℝ) /
          Real.log (Real.log (N : ℝ)) ^ (2 : ℕ) - k)) atTop atTop :=
    hll.atTop_mul_atTop₀ hratioSub
  have hexponent : Tendsto
      (fun N : ℕ ↦ c * Real.log (N : ℝ) /
          Real.log (Real.log (N : ℝ)) -
        k * Real.log (Real.log (N : ℝ))) atTop atTop := by
    apply hprod.congr'
    filter_upwards [hll.eventually (eventually_gt_atTop 0)] with N hllN
    field_simp [hllN.ne']
  have hexp := Real.tendsto_exp_atTop.comp hexponent
  apply hexp.congr'
  filter_upwards
      [hx.eventually (eventually_gt_atTop 0),
        hll.eventually (eventually_gt_atTop 0),
        eventually_ge_atTop (1 : ℕ)] with N hlog hllN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  change Real.exp (c * Real.log (N : ℝ) /
      Real.log (Real.log (N : ℝ)) -
        k * Real.log (Real.log (N : ℝ))) =
    (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) /
      Real.log (N : ℝ) ^ k
  rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos hlog, Real.exp_sub]
  congr 1
  · field_simp [hllN.ne']
  · ring_nf

private noncomputable def circleM (eta : ℝ) (N : ℕ) : ℝ :=
  eta * (N : ℝ) / 32

private noncomputable def circleK (eta : ℝ) (N : ℕ) : ℝ :=
  circleM eta N *
    (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))

private noncomputable def circleT (eta : ℝ) (N : ℕ) : ℝ :=
  circleM eta N / Real.log (N : ℝ)

private noncomputable def circleL (eta : ℝ) (N : ℕ) : ℝ :=
  circleM eta N /
    (2 * (Real.log (N : ℝ)) ^ (1 / 100 : ℝ))

private noncomputable def smoothScale (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - 8 / Real.log (Real.log (N : ℝ)))

private noncomputable def majorScale (N : ℕ) : ℝ :=
  (N : ℝ) ^ (3 / 5 : ℝ)

private noncomputable def varianceFloor (delta : ℝ) (N : ℕ) : ℝ :=
  delta / ((1 + 2 * delta) * (Real.log (N : ℝ) + 1))

private lemma eventually_minor_scale_bounds {eta delta : ℝ}
    (heta : 0 < eta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      smoothScale N ≤
          4 * varianceFloor delta N * circleT eta N * circleK eta N ^ 2 /
            ((N : ℝ) ^ 2 * Real.log (N : ℝ)) ∧
      smoothScale N ≤
          varianceFloor delta N * circleL eta N * circleK eta N ^ 2 /
            (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) := by
  have hlarge := large_enough_N 1 (by norm_num : (0 : ℝ) < 1)
  have hgap := tendsto_subpower_div_log_rpow 3 1 (by norm_num : (0 : ℝ) < 3)
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let C : ℝ := (2 * (1 + 2 * delta)) /
    (delta * (eta / 32) ^ 3)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  filter_upwards
      [hlarge, hgap.eventually (eventually_ge_atTop C),
        hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
        (Real.tendsto_log_atTop.comp hlogTop).eventually
          (eventually_gt_atTop 0),
        eventually_ge_atTop (2 : ℕ)] with
      N hlargeN hgapN hlog hll hN
  rcases hlargeN with
    ⟨-, -, -, -, hM0pos, hlogpos, -, -, -, -, -, -, -, -, -, -, -,
      hbaseL, hbaseT, -, -⟩
  let M₀ : ℝ := (N : ℝ) ^
    (1 - 1 / Real.log (Real.log (N : ℝ)))
  let K₀ : ℝ := (N : ℝ) ^
    (1 - 3 / Real.log (Real.log (N : ℝ)))
  let L₀ : ℝ := M₀ / (2 * Real.log (N : ℝ) ^ (1 / 100 : ℝ))
  let T₀ : ℝ := M₀ / Real.log (N : ℝ)
  let r : ℝ := (eta / 32) *
    (N : ℝ) ^ (1 / Real.log (Real.log (N : ℝ)))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hvarpos : 0 < varianceFloor delta N := by
    dsimp [varianceFloor]
    positivity
  have hlogTwo : Real.log (N : ℝ) + 1 ≤ 2 * Real.log (N : ℝ) := by linarith
  have hgapRewrite : C ≤
      (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) /
        Real.log (N : ℝ) := by simpa using hgapN
  have hratio : (1 / 4 : ℝ) ≤ varianceFloor delta N * r ^ 3 := by
    dsimp [varianceFloor, r, C] at hvarpos hgapRewrite ⊢
    have hpow3 :
        ((N : ℝ) ^ (1 / Real.log (Real.log (N : ℝ)))) ^ (3 : ℕ) =
          (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      apply congrArg (fun x : ℝ ↦ (N : ℝ) ^ x)
      field_simp [hll.ne']
      ring
    rw [mul_pow, hpow3]
    have hden1 : 0 < (1 + 2 * delta) * (Real.log (N : ℝ) + 1) := by positivity
    have hden2 : 0 < Real.log (N : ℝ) := hlogpos
    have heta3 : 0 < (eta / 32) ^ 3 := by positivity
    have hdenC : 0 < delta * (eta / 32) ^ 3 := mul_pos hdelta heta3
    have hg : C * Real.log (N : ℝ) ≤
        (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) := by
      calc
        C * Real.log (N : ℝ) ≤
            ((N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) /
              Real.log (N : ℝ)) * Real.log (N : ℝ) :=
          mul_le_mul_of_nonneg_right hgapRewrite hden2.le
        _ = (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) := by
          field_simp [hden2.ne']
    have hg' :
        2 * (1 + 2 * delta) * Real.log (N : ℝ) ≤
          delta * (eta / 32) ^ 3 *
            (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) := by
      dsimp [C] at hg
      rw [div_mul_eq_mul_div] at hg
      have hh := (div_le_iff₀ hdenC).mp (by simpa [mul_assoc] using hg)
      calc
        2 * (1 + 2 * delta) * Real.log (N : ℝ) =
            2 * ((1 + 2 * delta) * Real.log (N : ℝ)) := by ring
        _ ≤ (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) *
            (delta * (eta / 32) ^ 3) := hh
        _ = delta * (eta / 32) ^ 3 *
            (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))) := by ring
    rw [show delta / ((1 + 2 * delta) * (Real.log (N : ℝ) + 1)) *
        ((eta / 32) ^ 3 *
          (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ)))) =
      (delta * ((eta / 32) ^ 3 *
          (N : ℝ) ^ (3 / Real.log (Real.log (N : ℝ))))) /
        ((1 + 2 * delta) * (Real.log (N : ℝ) + 1)) by ring]
    rw [le_div_iff₀ hden1]
    nlinarith [hg', mul_pos hdelta heta3]
  have hM : circleM eta N = M₀ * r := by
    have hp : M₀ * (N : ℝ) ^
        (1 / Real.log (Real.log (N : ℝ))) = (N : ℝ) := by
      dsimp [M₀]
      rw [← Real.rpow_add hNpos]
      convert Real.rpow_one (N : ℝ) using 2
      field_simp [hll.ne']
      ring
    calc
      circleM eta N = (eta / 32) * (N : ℝ) := by
        dsimp [circleM]
        ring
      _ = (eta / 32) *
          (M₀ * (N : ℝ) ^ (1 / Real.log (Real.log (N : ℝ)))) := by rw [hp]
      _ = M₀ * r := by dsimp [r]; ring
  have hK : circleK eta N = K₀ * r := by
    have hp : M₀ * (N : ℝ) ^
        (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) = K₀ := by
      dsimp [M₀, K₀]
      rw [← Real.rpow_add hNpos]
      apply congrArg (fun x : ℝ ↦ (N : ℝ) ^ x)
      field_simp [hll.ne']
      ring
    rw [circleK, hM]
    calc
      M₀ * r * (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) =
          (M₀ * (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))) * r := by ring
      _ = K₀ * r := by rw [hp]
  have hL : circleL eta N = L₀ * r := by
    rw [circleL, hM]
    dsimp [L₀]
    ring
  have hT : circleT eta N = T₀ * r := by
    rw [circleT, hM]
    dsimp [T₀]
    ring
  have hbaseL' : smoothScale N ≤
      L₀ * K₀ ^ 2 / (16 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) := by
    simpa [smoothScale, M₀, K₀, L₀] using hbaseL
  have hbaseT' : smoothScale N ≤
      T₀ * K₀ ^ 2 / ((N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
    simpa [smoothScale, M₀, K₀, T₀] using hbaseT
  constructor
  · apply hbaseT'.trans
    rw [hT, hK]
    have hden : 0 < (N : ℝ) ^ 2 * Real.log (N : ℝ) := by positivity
    have hbaseNonneg : 0 ≤ T₀ * K₀ ^ 2 := by
      dsimp [T₀, K₀, M₀]
      positivity
    have hfactor : 1 ≤ 4 * varianceFloor delta N * r ^ 3 := by nlinarith
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      T₀ * K₀ ^ 2 ≤ (T₀ * K₀ ^ 2) *
          (4 * varianceFloor delta N * r ^ 3) :=
        le_mul_of_one_le_right hbaseNonneg hfactor
      _ = 4 * varianceFloor delta N * (T₀ * r) * (K₀ * r) ^ 2 := by ring
  · apply hbaseL'.trans
    rw [hL, hK]
    have hden : 0 < (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2 := by positivity
    have hbaseNonneg : 0 ≤ L₀ * K₀ ^ 2 := by
      dsimp [L₀, K₀, M₀]
      positivity
    have hfactor : 1 ≤ 4 * varianceFloor delta N * r ^ 3 := by nlinarith
    rw [show varianceFloor delta N * (L₀ * r) * (K₀ * r) ^ 2 /
        (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) =
      (4 * varianceFloor delta N * (L₀ * r) * (K₀ * r) ^ 2) /
        (16 * ((N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2)) by ring]
    rw [show (L₀ * K₀ ^ 2) /
        (16 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) =
      (L₀ * K₀ ^ 2) /
        (16 * ((N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2)) by ring]
    change (L₀ * K₀ ^ 2) /
        (16 * ((N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2)) ≤
      (4 * varianceFloor delta N * (L₀ * r) * (K₀ * r) ^ 2) /
        (16 * ((N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2))
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (by norm_num) hden.le)
    calc
      L₀ * K₀ ^ 2 ≤ (L₀ * K₀ ^ 2) *
          (4 * varianceFloor delta N * r ^ 3) :=
        le_mul_of_one_le_right hbaseNonneg hfactor
      _ = 4 * varianceFloor delta N * (L₀ * r) * (K₀ * r) ^ 2 := by ring

private lemma eventually_major_scale_bounds {eta delta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      2 * Real.pi * majorScale N / circleM eta N ≤ 1 ∧
      (N : ℝ) * (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) ≤
        Real.log 2 ∧
      (circleK eta N + 1) *
          Real.exp (-(8 * varianceFloor delta N * circleM eta N *
            majorScale N ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8 := by
  let a : ℝ := 64 * Real.pi / eta
  let b : ℝ := delta * eta / (4 * (1 + 2 * delta))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp25 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (2 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hp15 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hp110 : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hp25.eventually (eventually_ge_atTop a),
        hp15.eventually (eventually_ge_atTop (8 * a ^ 3 / Real.log 2)),
        hp110.eventually (eventually_ge_atTop (2400 / b)),
        hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
        (Real.tendsto_log_atTop.comp hlogTop).eventually (eventually_gt_atTop 0),
        eventually_ge_atTop (4 : ℕ)] with
      N hp25N hp15N hp110N hlog hll hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 4) hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by omega : 1 ≤ 4) hN)
  have hlogpos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hMpos : 0 < circleM eta N := by dsimp [circleM]; positivity
  have hpow25pos : 0 < (N : ℝ) ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hpow15pos : 0 < (N : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hH25 : majorScale N * (N : ℝ) ^ (2 / 5 : ℝ) = (N : ℝ) := by
    dsimp [majorScale]
    rw [← Real.rpow_add hNpos]
    convert Real.rpow_one (N : ℝ) using 2
    all_goals norm_num
  have hphase : 2 * Real.pi * majorScale N / circleM eta N ≤ 1 := by
    rw [div_le_one hMpos]
    have haH : a * majorScale N ≤ (N : ℝ) := by
      calc
        a * majorScale N ≤ (N : ℝ) ^ (2 / 5 : ℝ) * majorScale N :=
          mul_le_mul_of_nonneg_right hp25N (le_of_lt (by dsimp [majorScale]; positivity))
        _ = (N : ℝ) := by rw [mul_comm, hH25]
    dsimp [a, circleM] at haH ⊢
    have heta0 : 0 ≤ eta := heta.le
    field_simp [heta.ne'] at haH ⊢
    nlinarith [Real.pi_pos]
  have hphaseEq :
      2 * Real.pi * majorScale N / circleM eta N =
        a / (N : ℝ) ^ (2 / 5 : ℝ) := by
    dsimp [a, circleM]
    field_simp [hpow25pos.ne']
    nlinarith [hH25]
  have hcube : ((N : ℝ) ^ (2 / 5 : ℝ)) ^ (3 : ℕ) =
      (N : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    calc
      (N : ℝ) ^ ((2 / 5 : ℝ) * (3 : ℕ)) =
          (N : ℝ) ^ (1 + 1 / 5 : ℝ) := by
            congr 1
            all_goals norm_num
      _ = (N : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) := by
        rw [Real.rpow_add hNpos, Real.rpow_one]
  have hsmallBase :
      (N : ℝ) * (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) =
        8 * a ^ 3 / (N : ℝ) ^ (1 / 5 : ℝ) := by
    rw [hphaseEq]
    field_simp [hpow25pos.ne', hpow15pos.ne']
    nlinarith [hcube]
  have hsmall :
      (N : ℝ) * (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) ≤
        Real.log 2 := by
    rw [hsmallBase]
    exact (div_le_iff₀ hpow15pos).2 (by
      simpa [mul_comm] using (div_le_iff₀ hlog2).mp hp15N)
  have hlogBound : Real.log (N : ℝ) ≤
      20 * (N : ℝ) ^ (1 / 20 : ℝ) := by
    have h := Real.log_le_rpow_div hNpos.le (by norm_num : (0 : ℝ) < 1 / 20)
    norm_num at h ⊢
    simpa [div_eq_mul_inv, mul_comm] using h
  have hpowSquare : ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 2 =
      (N : ℝ) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    all_goals norm_num
  have hlogSq : Real.log (N : ℝ) ^ 2 ≤
      400 * (N : ℝ) ^ (1 / 10 : ℝ) := by
    nlinarith [sq_nonneg (20 * (N : ℝ) ^ (1 / 20 : ℝ) - Real.log (N : ℝ)),
      show ((N : ℝ) ^ (1 / 20 : ℝ)) ^ 2 = (N : ℝ) ^ (1 / 10 : ℝ) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        congr 1
        all_goals norm_num]
  have hgrowth : 6 * Real.log (N : ℝ) ^ 2 ≤
      b * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have hbpow : 2400 ≤ b * (N : ℝ) ^ (1 / 10 : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hb).mp hp110N
    have hx0 : 0 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hNpos.le _
    calc
      6 * Real.log (N : ℝ) ^ 2 ≤
          2400 * (N : ℝ) ^ (1 / 10 : ℝ) := by nlinarith [hlogSq]
      _ ≤ (b * (N : ℝ) ^ (1 / 10 : ℝ)) *
          (N : ℝ) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hbpow hx0
      _ = b * (N : ℝ) ^ (1 / 5 : ℝ) := by rw [← hpowSquare]; ring
  have hlogTwo : Real.log (N : ℝ) + 1 ≤ 2 * Real.log (N : ℝ) := by linarith
  have hexponentEq :
      8 * varianceFloor delta N * circleM eta N * majorScale N ^ 2 /
          (N : ℝ) ^ 2 =
        b * (N : ℝ) ^ (1 / 5 : ℝ) / (Real.log (N : ℝ) + 1) := by
    dsimp [varianceFloor, circleM, majorScale, b]
    have hHsq : ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 =
        (N : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      calc
        (N : ℝ) ^ ((3 / 5 : ℝ) * (2 : ℕ)) =
            (N : ℝ) ^ (1 + 1 / 5 : ℝ) := by
              congr 1
              all_goals norm_num
        _ = (N : ℝ) * (N : ℝ) ^ (1 / 5 : ℝ) := by
          rw [Real.rpow_add hNpos, Real.rpow_one]
    rw [hHsq]
    field_simp [hNpos.ne', hlogpos.ne', heta.ne']
    ring
  have hexponent : 3 * Real.log (N : ℝ) ≤
      8 * varianceFloor delta N * circleM eta N * majorScale N ^ 2 /
        (N : ℝ) ^ 2 := by
    rw [hexponentEq]
    apply (le_div_iff₀ (by linarith : 0 < Real.log (N : ℝ) + 1)).2
    calc
      3 * Real.log (N : ℝ) * (Real.log (N : ℝ) + 1) ≤
          3 * Real.log (N : ℝ) * (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogTwo (mul_nonneg (by norm_num) hlogpos.le)
      _ = 6 * Real.log (N : ℝ) ^ 2 := by ring
      _ ≤ b * (N : ℝ) ^ (1 / 5 : ℝ) := hgrowth
  have hKleM : circleK eta N ≤ circleM eta N := by
    dsimp [circleK]
    have hpow : (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hN1
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hll.le)
    exact mul_le_of_le_one_right hMpos.le hpow
  have hMleN : circleM eta N ≤ (N : ℝ) := by
    have hcoef : eta / 32 ≤ 1 :=
      (div_le_self heta.le (by norm_num : (1 : ℝ) ≤ 32)).trans heta1
    calc
      circleM eta N = (eta / 32) * (N : ℝ) := by dsimp [circleM]; ring
      _ ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hcoef hNpos.le
      _ = (N : ℝ) := one_mul _
  have hKone : circleK eta N + 1 ≤ 2 * (N : ℝ) := by
    calc
      circleK eta N + 1 ≤ (N : ℝ) + 1 := by
        simpa [add_comm] using add_le_add_right (hKleM.trans hMleN) 1
      _ ≤ (N : ℝ) + (N : ℝ) := by
        simpa [add_comm] using add_le_add_left hN1 (N : ℝ)
      _ = 2 * (N : ℝ) := by ring
  have hexpMono : Real.exp (-(8 * varianceFloor delta N * circleM eta N *
      majorScale N ^ 2 / (N : ℝ) ^ 2)) ≤
      Real.exp (-(3 * Real.log (N : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hmedium : (circleK eta N + 1) *
      Real.exp (-(8 * varianceFloor delta N * circleM eta N *
        majorScale N ^ 2 / (N : ℝ) ^ 2)) ≤ 1 / 8 := by
    calc
      _ ≤ (2 * (N : ℝ)) * Real.exp (-(3 * Real.log (N : ℝ))) :=
        mul_le_mul hKone hexpMono (Real.exp_nonneg _) (by positivity)
      _ = 2 / (N : ℝ) ^ 2 := by
        rw [show -(3 * Real.log (N : ℝ)) =
            Real.log (((N : ℝ) ^ 3)⁻¹) by
          rw [Real.log_inv, Real.log_pow]; ring]
        rw [Real.exp_log (by positivity : 0 < ((N : ℝ) ^ 3)⁻¹)]
        field_simp [hNpos.ne']
      _ ≤ 1 / 8 := by
        have hNsq : (16 : ℝ) ≤ (N : ℝ) ^ 2 := by
          exact_mod_cast (show 16 ≤ N ^ 2 by nlinarith)
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
        nlinarith
  exact ⟨hphase, hsmall, hmedium⟩

private lemma tendsto_smoothScale_div_nat :
    Tendsto (fun N : ℕ ↦ smoothScale N / (N : ℝ)) atTop (nhds 0) := by
  have htop : Tendsto
      (fun N : ℕ ↦ (N : ℝ) ^
        (8 / Real.log (Real.log (N : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_pow_rec_log_log_at_top (by norm_num : (0 : ℝ) < 8)).comp
        tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp htop
  apply hinv.congr'
  filter_upwards
      [(Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
          (eventually_gt_atTop 0),
        eventually_ge_atTop (1 : ℕ)] with N hll hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  symm
  calc
    smoothScale N / (N : ℝ) =
        (N : ℝ) ^ (1 - 8 / Real.log (Real.log (N : ℝ))) /
          (N : ℝ) ^ (1 : ℝ) := by simp [smoothScale]
    _ = (N : ℝ) ^
        ((1 - 8 / Real.log (Real.log (N : ℝ))) - 1) :=
      (Real.rpow_sub hNpos _ _).symm
    _ = (N : ℝ) ^ (-(8 / Real.log (Real.log (N : ℝ)))) := by
      congr 1
      ring
    _ = ((N : ℝ) ^ (8 / Real.log (Real.log (N : ℝ))))⁻¹ :=
      Real.rpow_neg hNpos.le _

/-- Smoothness makes the common denominator subexponential, while the
linear lower cutoff makes the reciprocal Hoeffding tail exponentially small
in `N`. -/
private lemma eventually_scaled_hoeffding_tail {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, ∀ τ : ℝ,
      A ⊆ Finset.Icc 1 N →
      (∀ n ∈ A, circleM eta N ≤ (n : ℝ)) →
      (∀ n ∈ A, is_smooth (smoothScale N) n) →
      0 ≤ τ → τ ≤ 1 →
      (lcmA A : ℝ) *
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) < 5 / 8 := by
  obtain ⟨C, hC, hClcm⟩ := smooth_lcm
  have hinvN : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hscaled0 : Tendsto
      (fun N : ℕ ↦ C * (smoothScale N / (N : ℝ)) +
        Real.log (16 / 5 : ℝ) * (1 / (N : ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_smoothScale_div_nat).add
      (tendsto_const_nhds.mul hinvN)
  have htarget : 0 < eta ^ 2 / 8192 := by positivity
  have hsmall := hscaled0.eventually (eventually_lt_nhds htarget)
  filter_upwards [hsmall,
      tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (64 / eta : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with
      N hsmallN hNlarge hN A τ hAN hLower hSmooth hτ0 hτ1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hMpos : 0 < circleM eta N := by dsimp [circleM]; positivity
  let m : ℕ := ⌈circleM eta N / 2⌉₊
  have hmCastLower : circleM eta N / 2 ≤ (m : ℝ) := by
    exact Nat.le_ceil _
  have hMlarge : (2 : ℝ) ≤ circleM eta N := by
    dsimp [circleM]
    have hmul := mul_le_mul_of_nonneg_left hNlarge heta.le
    field_simp [heta.ne'] at hmul ⊢
    linarith
  have hm : 0 < m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hMpos) hmCastLower
    exact_mod_cast this
  have hmN : m ≤ N := by
    rw [Nat.ceil_le]
    have hMleN : circleM eta N ≤ (N : ℝ) := by
      have hcoef : eta / 32 ≤ 1 :=
        (div_le_self heta.le (by norm_num : (1 : ℝ) ≤ 32)).trans heta1
      calc
        circleM eta N = (eta / 32) * (N : ℝ) := by dsimp [circleM]; ring
        _ ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hcoef hNpos.le
        _ = (N : ℝ) := one_mul _
    exact (half_le_self hMpos.le).trans hMleN
  have hAIcc : A ⊆ Finset.Icc m N := by
    intro n hn
    have hnBounds := Finset.mem_Icc.mp (hAN hn)
    refine Finset.mem_Icc.mpr ⟨?_, hnBounds.2⟩
    dsimp [m]
    rw [Nat.ceil_le]
    exact (half_le_self hMpos.le).trans (hLower n hn)
  have hA0 : 0 ∉ A := by
    intro hzero
    have := (Finset.mem_Icc.mp (hAN hzero)).1
    omega
  have hpp : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ smoothScale N := by
    intro q hq
    rcases mem_ppowers_in_set.mp hq with ⟨hqpp, n, hnlocal⟩
    have hnA : n ∈ A := local_part_subset hnlocal
    have hqdiv : q ∣ n := (mem_local_part n).mp hnlocal |>.2.1
    exact hSmooth n hnA q hqpp hqdiv
  have hlcm := hClcm (smoothScale N) (Real.rpow_nonneg hNpos.le _) A hA0 hpp
  have htail := Erdos297.FiniteHoeffding.abs_reciprocal_sum_sub_mean_tail
    (fun _ => τ) hm hmN hAIcc (fun _ _ => hτ0) (fun _ _ => hτ1)
  have hmSq : (circleM eta N / 2) ^ 2 ≤ (m : ℝ) ^ 2 :=
    (sq_le_sq₀ (div_nonneg hMpos.le (by norm_num)) (by positivity)).2 hmCastLower
  have hexponentLower : eta ^ 2 * (N : ℝ) / 8192 ≤
      (m : ℝ) ^ 2 / (2 * (N : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hNpos)).2
    dsimp [circleM] at hmSq
    field_simp [hNpos.ne'] at hmSq ⊢
    nlinarith
  have hlog165 : 0 < Real.log (16 / 5 : ℝ) :=
    Real.log_pos (by norm_num)
  have hnumeric : C * smoothScale N + Real.log (16 / 5 : ℝ) <
      eta ^ 2 * (N : ℝ) / 8192 := by
    have hsmall' :
        (C * smoothScale N + Real.log (16 / 5 : ℝ)) / (N : ℝ) <
          eta ^ 2 / 8192 := by
      calc
        _ = C * (smoothScale N / (N : ℝ)) +
            Real.log (16 / 5 : ℝ) * (1 / (N : ℝ)) := by
          field_simp [hNpos.ne']
        _ < eta ^ 2 / 8192 := hsmallN
    calc
      C * smoothScale N + Real.log (16 / 5 : ℝ) <
          (eta ^ 2 / 8192) * (N : ℝ) := (div_lt_iff₀ hNpos).mp hsmall'
      _ = eta ^ 2 * (N : ℝ) / 8192 := by ring
  have hexpGap : C * smoothScale N - (m : ℝ) ^ 2 / (2 * (N : ℝ)) <
      -Real.log (16 / 5 : ℝ) := by linarith
  have hscaledTail :
      (lcmA A : ℝ) *
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) ≤
        2 * Real.exp (C * smoothScale N -
          (m : ℝ) ^ 2 / (2 * (N : ℝ))) := by
    have hevent0 : 0 ≤
        Erdos297.FiniteHoeffding.eventMass A (fun _ => τ) (fun B =>
          1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
                (fun n : ℕ => (n : ℝ)⁻¹) -
              Erdos297.FiniteHoeffding.subsetMean A (fun _ => τ)
                (fun n : ℕ => (n : ℝ)⁻¹)|) := by
      rw [Erdos297.FiniteHoeffding.eventMass]
      apply Finset.sum_nonneg
      intro B hB
      split_ifs
      · exact Erdos297.WeightedFourier.subsetWeight_nonneg A
          (fun _ => τ) (fun _ _ => hτ0) (fun _ _ => hτ1) hB
      · exact le_rfl
    calc
      _ ≤ Real.exp (C * smoothScale N) *
          (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * (N : ℝ)))) :=
        mul_le_mul hlcm htail
          hevent0 (by positivity)
      _ = 2 * Real.exp (C * smoothScale N -
          (m : ℝ) ^ 2 / (2 * (N : ℝ))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring_nf
  calc
    _ ≤ 2 * Real.exp (C * smoothScale N -
        (m : ℝ) ^ 2 / (2 * (N : ℝ))) := hscaledTail
    _ < 2 * Real.exp (-Real.log (16 / 5 : ℝ)) := by
      gcongr
    _ = 5 / 8 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16 / 5)]
      norm_num

private lemma cast_rec_sum_le_one_add_log {A : Finset ℕ} {N : ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) :
    (rec_sum A : ℝ) ≤ Real.log (N : ℝ) + 1 := by
  calc
    (rec_sum A : ℝ) = ∑ n ∈ A, ((n : ℝ))⁻¹ := by
      rw [rec_sum, Rat.cast_sum]
      push_cast
      simp only [one_div]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hAN
      intro n hnIcc hnA
      positivity
    _ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
    _ = Real.log (N : ℝ) + 1 := add_comm _ _

/-- Elementary eventual facts about the four circle-method scales. -/
private lemma eventually_circle_basic_bounds {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ᶠ N : ℕ in atTop,
      192 ≤ N ∧
      8 ≤ circleM eta N ∧
      1 ≤ circleK eta N ∧
      circleK eta N < circleM eta N ∧
      circleK eta N ≤ (N : ℝ) ∧
      0 < circleT eta N ∧
      0 < circleL eta N ∧
      0 < majorScale N ∧
      0 < Real.log (N : ℝ) := by
  have hlarge := large_enough_N 1 (by norm_num : (0 : ℝ) < 1)
  have hpow : Tendsto
      (fun N : ℕ ↦ (N : ℝ) ^
        (1 / Real.log (Real.log (N : ℝ)))) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_pow_rec_log_log_at_top (by norm_num : (0 : ℝ) < 1)).comp
        tendsto_natCast_atTop_atTop
  filter_upwards
      [hlarge, hpow.eventually (eventually_ge_atTop (32 / eta : ℝ)),
        eventually_ge_atTop (192 : ℕ)] with N hlargeN hpowN hN
  rcases hlargeN with
    ⟨-, -, -, -, hM₀pos, hlogpos, hK₀eight, hK₀M, -, -, -, -, -, -, -, -, -,
      -, -, -, -⟩
  let M₀ : ℝ := (N : ℝ) ^
    (1 - 1 / Real.log (Real.log (N : ℝ)))
  let K₀ : ℝ := (N : ℝ) ^
    (1 - 3 / Real.log (Real.log (N : ℝ)))
  let r : ℝ := (eta / 32) *
    (N : ℝ) ^ (1 / Real.log (Real.log (N : ℝ)))
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 192) hN)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrone : 1 ≤ r := by
    calc
      (1 : ℝ) = (eta / 32) * (32 / eta) := by field_simp [heta.ne']
      _ ≤ (eta / 32) *
          (N : ℝ) ^ (1 / Real.log (Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hpowN (by positivity)
      _ = r := rfl
  have hllne : Real.log (Real.log (N : ℝ)) ≠ 0 := by
    intro hz
    have hpowN' := hpowN
    simp [hz] at hpowN'
    have hgt : (1 : ℝ) < 32 / eta := by
      apply (lt_div_iff₀ heta).2
      nlinarith
    linarith
  have hM : circleM eta N = M₀ * r := by
    have hp : M₀ * (N : ℝ) ^
        (1 / Real.log (Real.log (N : ℝ))) = (N : ℝ) := by
      dsimp [M₀]
      rw [← Real.rpow_add hNpos]
      convert Real.rpow_one (N : ℝ) using 2
      field_simp [hllne]
      ring
    calc
      circleM eta N = (eta / 32) * (N : ℝ) := by
        dsimp [circleM]
        ring
      _ = (eta / 32) *
          (M₀ * (N : ℝ) ^
            (1 / Real.log (Real.log (N : ℝ)))) := by rw [hp]
      _ = M₀ * r := by dsimp [r]; ring
  have hK : circleK eta N = K₀ * r := by
    have hp : M₀ * (N : ℝ) ^
        (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) = K₀ := by
      dsimp [M₀, K₀]
      rw [← Real.rpow_add hNpos]
      apply congrArg (fun x : ℝ ↦ (N : ℝ) ^ x)
      field_simp [hllne]
      ring
    rw [circleK, hM]
    calc
      M₀ * r * (N : ℝ) ^
          (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) =
          (M₀ * (N : ℝ) ^
            (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))) * r := by ring
      _ = K₀ * r := by rw [hp]
  have hM₀eight : 8 < M₀ := hK₀eight.trans_lt hK₀M
  have hMeight : 8 ≤ circleM eta N := by
    rw [hM]
    calc
      (8 : ℝ) ≤ M₀ := hM₀eight.le
      _ ≤ M₀ * r := le_mul_of_one_le_right hM₀pos.le hrone
  have hKone : 1 ≤ circleK eta N := by
    rw [hK]
    calc
      (1 : ℝ) ≤ 8 := by norm_num
      _ ≤ K₀ := hK₀eight
      _ ≤ K₀ * r := le_mul_of_one_le_right (by positivity) hrone
  have hKM : circleK eta N < circleM eta N := by
    rw [hK, hM]
    exact mul_lt_mul_of_pos_right hK₀M hrpos
  have hMleN : circleM eta N ≤ (N : ℝ) := by
    have hcoef : eta / 32 ≤ 1 :=
      (div_le_self heta.le (by norm_num : (1 : ℝ) ≤ 32)).trans heta1
    calc
      circleM eta N = (eta / 32) * (N : ℝ) := by dsimp [circleM]; ring
      _ ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hcoef hNpos.le
      _ = (N : ℝ) := one_mul _
  have hTpos : 0 < circleT eta N := by
    dsimp [circleT, circleM]
    positivity
  have hLpos : 0 < circleL eta N := by
    dsimp [circleL, circleM]
    positivity
  exact ⟨hN, hMeight, hKone, hKM, hKM.le.trans hMleN,
    hTpos, hLpos, by dsimp [majorScale]; positivity, hlogpos⟩

/-- The exact finite-density assertion proved by Liu and Sawhney.  Keeping
this proposition as a named interface separates their arithmetic/Fourier
theorem from the elementary passage to the extremal asymptotic. -/
def DenseContainsOne : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 2 →
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      (1 - 1 / Real.exp 1 + ξ) * (N : ℝ) ≤ (A.card : ℝ) →
      ∃ B : Finset ℕ, B ⊆ A ∧ rec_sum B = 1

/-- Liu and Sawhney's sharp finite-density theorem. -/
theorem dense_contains_one : DenseContainsOne := by
  intro ξ hξ hξhalf
  let eta : ℝ := min ξ (1 / Real.exp 1)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min hξ (by positivity)
  have hetaξ : eta ≤ ξ := min_le_left _ _
  have hetaExp : eta ≤ 1 / Real.exp 1 := min_le_right _ _
  have hexpOne : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr zero_lt_one
  have hinvOne : 1 / Real.exp 1 < (1 : ℝ) := by
    simpa [one_div] using inv_lt_one_of_one_lt₀ hexpOne
  have heta1 : eta ≤ 1 := hetaExp.trans hinvOne.le
  have hc : 0 < 1 / Real.exp 1 - eta / 2 := by
    have hinvpos : 0 < 1 / Real.exp 1 := by positivity
    nlinarith
  let delta : ℝ := densityMassMargin eta
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact densityMassMargin_pos heta hc
  have hinverse := eventually_dense_inverse_good heta heta1 hc
  have hminorScale := eventually_minor_scale_bounds heta hdelta
  have hmajorScale := eventually_major_scale_bounds heta heta1 hdelta
  have htail := eventually_scaled_hoeffding_tail heta heta1
  have hbasic := eventually_circle_basic_bounds heta heta1
  filter_upwards
      [hinverse, hminorScale, hmajorScale, htail, hbasic,
        weighted_minor1_bound, weighted_minor2_bound] with
      N hinverseN hminorScaleN hmajorScaleN htailN hbasicN
        hminor1N hminor2N
  intro A hAN hAdense
  rcases hbasicN with
    ⟨hNlarge, hMeight, hKone, hKM, hKN, hTpos, hLpos, hHpos, hlogpos⟩
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 192) hNlarge)
  have hAdenseEta :
      (1 - 1 / Real.exp 1 + eta) * (N : ℝ) ≤ (A.card : ℝ) := by
    have hcoef : 1 - 1 / Real.exp 1 + eta ≤
        1 - 1 / Real.exp 1 + ξ := by linarith
    exact (mul_le_mul_of_nonneg_right hcoef hNpos.le).trans hAdense
  obtain ⟨P, hPA, hLower, hSmooth, hMass, hLocal, hGood⟩ :=
    hinverseN A hAN hAdenseEta
  have hPN : P ⊆ Finset.Icc 1 N := hPA.trans hAN
  have hUpper : ∀ n ∈ P, n ≤ N := fun n hn ↦
    (Finset.mem_Icc.mp (hPN hn)).2
  have hP0 : 0 ∉ P := by
    intro hzero
    have := (Finset.mem_Icc.mp (hPN hzero)).1
    omega
  let R : ℝ := (rec_sum P : ℝ)
  let tau : ℝ := R⁻¹
  let rho : ℝ := varianceFloor delta N
  change 1 + 2 * delta ≤ R at hMass
  have hRgt : 1 < R := by nlinarith
  have hRpos : 0 < R := zero_lt_one.trans hRgt
  have hRone : 1 ≤ R := hRgt.le
  have hRupper : R ≤ Real.log (N : ℝ) + 1 := by
    simpa [R] using cast_rec_sum_le_one_add_log hPN
  have hUpos : 0 < Real.log (N : ℝ) + 1 := by linarith
  have htaupos : 0 < tau := by dsimp [tau]; positivity
  have htaubound : tau < 1 := by
    dsimp [tau]
    exact inv_lt_one_of_one_lt₀ hRgt
  have htau0 : 0 ≤ tau := htaupos.le
  have htau1 : tau ≤ 1 := htaubound.le
  have hmean : tau * (rec_sum P : ℝ) = 1 := by
    change R⁻¹ * R = 1
    exact inv_mul_cancel₀ hRpos.ne'
  have hrhopos : 0 < rho := by
    dsimp [rho, varianceFloor]
    positivity
  have hrho0 : 0 ≤ rho := hrhopos.le
  have hfrac : 2 * delta / (1 + 2 * delta) ≤ (R - 1) / R := by
    rw [div_le_div_iff₀ (by positivity : 0 < 1 + 2 * delta) hRpos]
    nlinarith
  have hinv : 1 / (Real.log (N : ℝ) + 1) ≤ 1 / R :=
    one_div_le_one_div_of_le hRpos hRupper
  have hfrac0 : 0 ≤ 2 * delta / (1 + 2 * delta) := by positivity
  have hfracRight0 : 0 ≤ (R - 1) / R := hfrac0.trans hfrac
  have hinv0 : 0 ≤ 1 / (Real.log (N : ℝ) + 1) := by positivity
  have hrhoa : rho ≤ tau * (1 - tau) := by
    have htwice : rho ≤ 2 * rho := by nlinarith
    calc
      rho ≤ 2 * rho := htwice
      _ = (2 * delta / (1 + 2 * delta)) *
          (1 / (Real.log (N : ℝ) + 1)) := by
        dsimp [rho, varianceFloor]
        field_simp [hUpos.ne', (by positivity : (1 + 2 * delta) ≠ 0)]
      _ ≤ ((R - 1) / R) * (1 / R) :=
        mul_le_mul hfrac hinv hinv0 hfracRight0
      _ = tau * (1 - tau) := by
        dsimp [tau]
        field_simp [hRpos.ne']
  have hMpos : 0 < circleM eta N := (by linarith : 0 < circleM eta N)
  have hrecCard := rec_sum_le_card_div hMpos hLower
  change R ≤ (P.card : ℝ) / circleM eta N at hrecCard
  have hMcard : circleM eta N ≤ (P.card : ℝ) := by
    have honeCard : (1 : ℝ) ≤ (P.card : ℝ) / circleM eta N :=
      hRone.trans hrecCard
    have := (le_div_iff₀ hMpos).mp honeCard
    simpa using this
  have hPcardN : (P.card : ℝ) ≤ (N : ℝ) := by
    have hcard := Finset.card_le_card hPN
    simpa using hcard
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8)
      (hMeight.trans hMcard))
  have hQpos : 0 < lcmA P := Nat.pos_of_ne_zero
    (lcm_ne_zero_of_zero_not_mem hP0)
  obtain ⟨n, hnP⟩ := hPne
  have hndvd : n ∣ lcmA P := by
    simpa [lcmA] using (Finset.dvd_lcm (f := id) hnP)
  have hnlcm : n ≤ lcmA P := Nat.le_of_dvd hQpos hndvd
  have hKlcm : circleK eta N < (lcmA P : ℝ) := by
    calc
      circleK eta N < circleM eta N := hKM
      _ ≤ (n : ℝ) := hLower n hnP
      _ ≤ (lcmA P : ℝ) := by exact_mod_cast hnlcm
  have hphase :
      2 * Real.pi * majorScale N / circleM eta N ≤ 1 := hmajorScaleN.1
  have hsmallExponent :
      (P.card : ℝ) *
          (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) ≤
        Real.log 2 := by
    have hfactor : 0 ≤
        8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3 := by
      positivity
    calc
      (P.card : ℝ) *
          (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) ≤
          (N : ℝ) *
            (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3) :=
        mul_le_mul_of_nonneg_right hPcardN hfactor
      _ ≤ Real.log 2 := hmajorScaleN.2.1
  have hsmall :
      Real.exp (P.card *
          (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3)) - 1 ≤ 1 := by
    calc
      Real.exp (P.card *
          (8 * (2 * Real.pi * majorScale N / circleM eta N) ^ 3)) - 1 ≤
          Real.exp (Real.log 2) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.mpr hsmallExponent) 1
      _ = 1 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hmedium :
      (circleK eta N + 1) *
          Real.exp (-(8 * rho * P.card * majorScale N ^ 2 /
            (N : ℝ) ^ 2)) ≤ 1 / 8 := by
    calc
      _ ≤ (circleK eta N + 1) *
          Real.exp (-(8 * rho * circleM eta N * majorScale N ^ 2 /
            (N : ℝ) ^ 2)) := by
        gcongr
      _ ≤ 1 / 8 := by simpa [rho] using hmajorScaleN.2.2
  have hqMinor1 : ∀ q ∈ ppowers_in_set P,
      (q : ℝ) ≤
        (4 * tau * (1 - tau) * circleT eta N * circleK eta N ^ 2) /
          ((N : ℝ) ^ 2 * Real.log N) := by
    intro q hq
    have hqSmooth : (q : ℝ) ≤ smoothScale N := by
      rcases mem_ppowers_in_set.mp hq with ⟨hqpp, n, hnlocal⟩
      have hnP : n ∈ P := local_part_subset hnlocal
      have hqdiv : q ∣ n := (mem_local_part n).mp hnlocal |>.2.1
      simpa [smoothScale] using hSmooth n hnP q hqpp hqdiv
    calc
      (q : ℝ) ≤ smoothScale N := hqSmooth
      _ ≤ 4 * rho * circleT eta N * circleK eta N ^ 2 /
          ((N : ℝ) ^ 2 * Real.log (N : ℝ)) := hminorScaleN.1
      _ ≤ (4 * tau * (1 - tau) * circleT eta N * circleK eta N ^ 2) /
          ((N : ℝ) ^ 2 * Real.log (N : ℝ)) := by
        have hden : 0 < (N : ℝ) ^ 2 * Real.log (N : ℝ) := by positivity
        apply div_le_div_of_nonneg_right _ hden.le
        have hfactor : 0 ≤ 4 * circleT eta N * circleK eta N ^ 2 := by
          positivity
        calc
          4 * rho * circleT eta N * circleK eta N ^ 2 =
              rho * (4 * circleT eta N * circleK eta N ^ 2) := by ring
          _ ≤ (tau * (1 - tau)) *
              (4 * circleT eta N * circleK eta N ^ 2) :=
            mul_le_mul_of_nonneg_right hrhoa hfactor
          _ = 4 * tau * (1 - tau) * circleT eta N *
              circleK eta N ^ 2 := by ring
  have hqMinor2 : ∀ q ∈ ppowers_in_set P,
      (q : ℝ) ≤ tau * (1 - tau) * circleL eta N * circleK eta N ^ 2 /
        (4 * (N : ℝ) ^ 2 * Real.log N ^ 2) := by
    intro q hq
    have hqSmooth : (q : ℝ) ≤ smoothScale N := by
      rcases mem_ppowers_in_set.mp hq with ⟨hqpp, n, hnlocal⟩
      have hnP : n ∈ P := local_part_subset hnlocal
      have hqdiv : q ∣ n := (mem_local_part n).mp hnlocal |>.2.1
      simpa [smoothScale] using hSmooth n hnP q hqpp hqdiv
    calc
      (q : ℝ) ≤ smoothScale N := hqSmooth
      _ ≤ rho * circleL eta N * circleK eta N ^ 2 /
          (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) := hminorScaleN.2
      _ ≤ tau * (1 - tau) * circleL eta N * circleK eta N ^ 2 /
          (4 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2) := by
        have hden : 0 < 4 * (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ 2 := by positivity
        apply div_le_div_of_nonneg_right _ hden.le
        have hfactor : 0 ≤ circleL eta N * circleK eta N ^ 2 := by
          positivity
        calc
          rho * circleL eta N * circleK eta N ^ 2 =
              rho * (circleL eta N * circleK eta N ^ 2) := by ring
          _ ≤ (tau * (1 - tau)) *
              (circleL eta N * circleK eta N ^ 2) :=
            mul_le_mul_of_nonneg_right hrhoa hfactor
          _ = tau * (1 - tau) * circleL eta N * circleK eta N ^ 2 := by ring
  have hminor1 :
      (minor_arc₁ P 1 (circleK eta N) (circleT eta N)).sum
        (fun h => bernoulliNormProd P tau h) ≤ 1 / 8 := by
    simpa using hminor1N (K := circleK eta N) (M := circleM eta N)
      (T := circleT eta N) 1 (A := P) (τ := tau) htaupos htaubound
      hMeight ⟨n, hnP⟩ hLower (lt_of_lt_of_le zero_lt_one hKone) hTpos hUpper
      hqMinor1
  have hminor2 :
      (minor_arc₂ P 1 (circleK eta N) (circleT eta N)).sum
        (fun h => bernoulliNormProd P tau h) ≤ 1 / 8 := by
    rw [circleK, circleT, circleM]
    have hKone' : 1 ≤ (eta * (N : ℝ) / 32) *
        (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) := by
      simpa only [circleK, circleM] using hKone
    have hLpos' : 0 < (eta * (N : ℝ) / 32) /
        (2 * Real.log (N : ℝ) ^ (1 / 100 : ℝ)) := by
      simpa only [circleL, circleM] using hLpos
    have hKN' : (eta * (N : ℝ) / 32) *
        (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))) ≤ (N : ℝ) := by
      simpa only [circleK, circleM] using hKN
    have hqMinor2' : ∀ q ∈ ppowers_in_set P,
        (q : ℝ) ≤ tau * (1 - tau) *
          ((eta * (N : ℝ) / 32) /
            (2 * Real.log (N : ℝ) ^ (1 / 100 : ℝ))) *
          ((eta * (N : ℝ) / 32) *
            (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ)))) ^ 2 /
          (4 * (N : ℝ) ^ 2 * Real.log N ^ 2) := by
      simpa only [circleK, circleL, circleM] using hqMinor2
    have hraw := hminor2N
        (K := (eta * (N : ℝ) / 32) *
          (N : ℝ) ^ (-(2 : ℝ) / Real.log (Real.log (N : ℝ))))
        (L := (eta * (N : ℝ) / 32) /
          (2 * Real.log (N : ℝ) ^ (1 / 100 : ℝ)))
        (T := (eta * (N : ℝ) / 32) / Real.log (N : ℝ))
        (k := 1) (A := P) (τ := tau)
        htau0 htau1 hP0 hKone' hLpos' one_ne_zero (by omega)
        hKN' hUpper hqMinor2' hGood
    simpa using hraw
  have hscaledTail := htailN P tau hPN hLower
    (by simpa [smoothScale] using hSmooth) htau0 htau1
  obtain ⟨B, hBP, hBsum⟩ := weighted_circle_core_hoeffding
    htau0 htau1 hmean hP0 (by omega : 0 < N) hMpos hHpos.le
    (zero_le_one.trans hKone) hKM.le hKlcm hLower hUpper hrho0 hrhoa hphase
    hsmall hmedium
    hminor1 hminor2 hscaledTail
  exact ⟨B, hBP.trans hPA, hBsum⟩

/-- The Liu--Sawhney finite theorem gives the matching eventual upper bound
for the extremal function. -/
theorem eventually_erdos300Max_upper_of_dense
    (hLS : DenseContainsOne) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (erdos300Max N : ℝ) / (N : ℝ) < 1 - 1 / Real.exp 1 + ε := by
  let ξ : ℝ := min (ε / 2) (1 / 4)
  have hξpos : 0 < ξ := by
    dsimp [ξ]
    exact lt_min (half_pos hε) (by norm_num)
  have hξhalf : ξ < 1 / 2 := by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hξε : ξ < ε := by
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hfinite := hLS ξ hξpos hξhalf
  filter_upwards [hfinite, eventually_ge_atTop 1] with N hfiniteN hN
  obtain ⟨A, hAN, hAvoid, hAcard⟩ := exists_extremizer N
  have hnotdense :
      ¬(1 - 1 / Real.exp 1 + ξ) * (N : ℝ) ≤ (A.card : ℝ) := by
    intro hdense
    obtain ⟨B, hBA, hBsum⟩ := hfiniteN A hAN hdense
    exact hAvoid B hBA hBsum
  have hcardlt :
      (A.card : ℝ) < (1 - 1 / Real.exp 1 + ξ) * (N : ℝ) :=
    lt_of_not_ge hnotdense
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoef :
      1 - 1 / Real.exp 1 + ξ < 1 - 1 / Real.exp 1 + ε := by
    linarith
  rw [div_lt_iff₀ hNpos, ← hAcard]
  exact hcardlt.trans
    (mul_lt_mul_of_pos_right hcoef hNpos)

/-- Once the exact finite Liu--Sawhney theorem is established, the lower and
upper estimates combine to the claimed asymptotic formula. -/
theorem erdos300_of_dense (hLS : DenseContainsOne) :
    Tendsto (fun N : ℕ => (erdos300Max N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 - 1 / Real.exp 1)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards
    [eventually_erdos300Max_lower hε,
      eventually_erdos300Max_upper_of_dense hLS hε] with N hlower hupper
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Erdős Problem 300: the largest subset of `{1, ..., N}` having no
unit-sum reciprocal subcollection has asymptotic density `1 - 1 / e`. -/
theorem erdos_300 :
    Tendsto (fun N : ℕ => (erdos300Max N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 - 1 / Real.exp 1)) :=
  erdos300_of_dense dense_contains_one

#print axioms erdos_300

end Erdos300

alias _root_.Erdos300.erdos300 := _root_.Erdos300.erdos_300
