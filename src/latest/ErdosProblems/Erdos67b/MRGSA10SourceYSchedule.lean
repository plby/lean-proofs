import ErdosProblems.Erdos67b.EulerSubpower
import ErdosProblems.Erdos67b.MRTFiniteThreshold
import ErdosProblems.Erdos67b.PrimeEstimates

/-!
# An explicit source cutoff for GS A.10

The source proof of GS Lemma A.10 needs a natural cutoff which grows faster
than every fixed power of `log X`, but remains subpolynomial in `X`.  We use

`y(X) = ceil (exp (sqrt (log X)))`.

Keeping the ceiling in the definition is useful downstream: its lower bound
is exact, while its additive upper error costs only `log 2` after taking a
logarithm.  This file records both the structural inequalities and the
vanishing scalar errors used by the A.10 parameter schedule.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The logarithmic square-root scale underlying the A.10 source cutoff. -/
def gsA10SourceRoot (X : ℕ) : ℝ :=
  Real.sqrt (Real.log (X : ℝ))

/-- The natural source cutoff used in GS A.10. -/
def gsA10SourceCutoff (X : ℕ) : ℕ :=
  Nat.ceil (Real.exp (gsA10SourceRoot X))

theorem gsA10SourceRoot_nonneg (X : ℕ) :
    0 ≤ gsA10SourceRoot X :=
  Real.sqrt_nonneg _

theorem tendsto_gsA10SourceRoot_atTop :
    Tendsto gsA10SourceRoot atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    Erdos67b.EulerSubpower.tendsto_log_nat_atTop

theorem tendsto_gsA10SourceCutoff_atTop :
    Tendsto gsA10SourceCutoff atTop atTop := by
  have hexp : Tendsto (fun X : ℕ ↦ Real.exp (gsA10SourceRoot X))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_gsA10SourceRoot_atTop
  apply tendsto_atTop.2
  intro N
  filter_upwards [hexp.eventually (eventually_ge_atTop (N : ℝ))]
      with X hX
  have hceil : Real.exp (gsA10SourceRoot X) ≤
      (gsA10SourceCutoff X : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hX.trans hceil

/-- The ceiling never loses the exact exponential lower bound. -/
theorem exp_gsA10SourceRoot_le_cutoff (X : ℕ) :
    Real.exp (gsA10SourceRoot X) ≤ (gsA10SourceCutoff X : ℝ) := by
  exact Nat.le_ceil _

theorem gsA10SourceCutoff_pos (X : ℕ) :
    0 < gsA10SourceCutoff X := by
  unfold gsA10SourceCutoff
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

/-- The logarithm of the integral cutoff is bounded below by the intended
square-root scale, without any threshold. -/
theorem gsA10SourceRoot_le_log_cutoff (X : ℕ) :
    gsA10SourceRoot X ≤ Real.log (gsA10SourceCutoff X : ℝ) := by
  calc
    gsA10SourceRoot X = Real.log (Real.exp (gsA10SourceRoot X)) := by
      rw [Real.log_exp]
    _ ≤ Real.log (gsA10SourceCutoff X : ℝ) :=
      Real.log_le_log (Real.exp_pos _)
        (exp_gsA10SourceRoot_le_cutoff X)

/-- The ceiling costs at most an additive `log 2` after taking logarithms. -/
theorem log_gsA10SourceCutoff_le (X : ℕ) :
    Real.log (gsA10SourceCutoff X : ℝ) ≤
      gsA10SourceRoot X + Real.log 2 := by
  have hceil : (gsA10SourceCutoff X : ℝ) <
      Real.exp (gsA10SourceRoot X) + 1 := by
    unfold gsA10SourceCutoff
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hone : 1 ≤ Real.exp (gsA10SourceRoot X) := by
    simpa only [Real.exp_zero] using
      Real.exp_monotone (gsA10SourceRoot_nonneg X)
  have htwo : (gsA10SourceCutoff X : ℝ) ≤
      2 * Real.exp (gsA10SourceRoot X) := by
    linarith
  calc
    Real.log (gsA10SourceCutoff X : ℝ) ≤
        Real.log (2 * Real.exp (gsA10SourceRoot X)) :=
      Real.log_le_log (by exact_mod_cast gsA10SourceCutoff_pos X) htwo
    _ = gsA10SourceRoot X + Real.log 2 := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
      ring

theorem eventually_log_gsA10SourceCutoff_le_two_mul_root :
    ∀ᶠ X : ℕ in atTop,
      Real.log (gsA10SourceCutoff X : ℝ) ≤
        2 * gsA10SourceRoot X := by
  filter_upwards
    [tendsto_gsA10SourceRoot_atTop.eventually
      (eventually_ge_atTop (Real.log 2))] with X hX
  exact (log_gsA10SourceCutoff_le X).trans (by linarith)

/-- The source cutoff is eventually below the ambient scale. -/
theorem eventually_gsA10SourceCutoff_le_self :
    ∀ᶠ X : ℕ in atTop, gsA10SourceCutoff X ≤ X := by
  have hsmall :
      (fun X : ℕ ↦ Real.exp (gsA10SourceRoot X)) =o[atTop]
        (fun X : ℕ ↦ (X : ℝ)) := by
    change (fun X : ℕ ↦
        Real.exp (Real.sqrt (Real.log (X : ℝ)))) =o[atTop]
          (fun X : ℕ ↦ (X : ℝ))
    simpa only [Function.comp_apply, Function.comp_def, one_mul] using
      (Erdos67b.EulerSubpower.subpower_real_isLittleO 1).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hhalf := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hhalf, eventually_ge_atTop 2] with X hX hXtwo
  have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hExp : Real.exp (gsA10SourceRoot X) ≤ (X : ℝ) / 2 := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hXR, div_eq_mul_inv, mul_comm, one_mul] using hX
  have hceil : (gsA10SourceCutoff X : ℝ) <
      Real.exp (gsA10SourceRoot X) + 1 := by
    unfold gsA10SourceCutoff
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hXtwoR : (2 : ℝ) ≤ X := by exact_mod_cast hXtwo
  have hltR : (gsA10SourceCutoff X : ℝ) < (X : ℝ) :=
    hceil.trans_le (by linarith :
      Real.exp (gsA10SourceRoot X) + 1 ≤ (X : ℝ))
  have hlt : gsA10SourceCutoff X < X := by exact_mod_cast hltR
  exact hlt.le

/-- The fourth logarithmic power is eventually swallowed by the exponential
square-root cutoff. -/
theorem eventually_log_pow_four_le_gsA10SourceCutoff :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ 4 ≤ (gsA10SourceCutoff X : ℝ) := by
  have hpoly : (fun r : ℝ ↦ r ^ (8 : ℝ)) =o[atTop]
      (fun r : ℝ ↦ Real.exp (1 * r)) :=
    isLittleO_rpow_exp_pos_mul_atTop 8 (by norm_num)
  have hbound :=
    (hpoly.comp_tendsto tendsto_gsA10SourceRoot_atTop).bound
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards
    [hbound,
      Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 0)] with X hX hlog
  have hsquare : gsA10SourceRoot X ^ 2 = Real.log (X : ℝ) := by
    exact Real.sq_sqrt hlog
  have hpow : Real.log (X : ℝ) ^ 4 ≤
      Real.exp (gsA10SourceRoot X) := by
    have hrootpow : 0 ≤ gsA10SourceRoot X ^ 8 :=
      pow_nonneg (gsA10SourceRoot_nonneg X) _
    have hrpow : |gsA10SourceRoot X ^ (8 : ℝ)| ≤
        Real.exp (gsA10SourceRoot X) := by
      simpa only [Function.comp_apply, Function.comp_def,
        Real.norm_eq_abs, one_mul, abs_of_pos (Real.exp_pos _)] using hX
    have hxnorm : |gsA10SourceRoot X ^ (8 : ℕ)| ≤
        Real.exp (gsA10SourceRoot X) := by
      rw [← Real.rpow_natCast]
      exact hrpow
    have hx' : gsA10SourceRoot X ^ 8 ≤
        Real.exp (gsA10SourceRoot X) :=
      (le_abs_self _).trans hxnorm
    rw [← hsquare]
    nlinarith
  exact hpow.trans (exp_gsA10SourceRoot_le_cutoff X)

/-- All fixed structural hypotheses used at the source of A.10 hold
simultaneously. -/
theorem eventually_gsA10SourceCutoff_structural :
    ∀ᶠ X : ℕ in atTop,
      23 ≤ gsA10SourceCutoff X ∧
      gsA10SourceCutoff X ≤ X ∧
      6 ≤ Real.log (gsA10SourceCutoff X : ℝ) ∧
      Real.log (X : ℝ) ^ 4 ≤ (gsA10SourceCutoff X : ℝ) := by
  filter_upwards
    [tendsto_gsA10SourceCutoff_atTop.eventually (eventually_ge_atTop 23),
      eventually_gsA10SourceCutoff_le_self,
      tendsto_gsA10SourceRoot_atTop.eventually (eventually_ge_atTop 6),
      eventually_log_pow_four_le_gsA10SourceCutoff] with X hy hyX hroot hpow
  exact ⟨hy, hyX, hroot.trans (gsA10SourceRoot_le_log_cutoff X), hpow⟩

/-- `log y / log X` vanishes for the explicit source cutoff. -/
theorem tendsto_log_gsA10SourceCutoff_div_log :
    Tendsto (fun X : ℕ ↦
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ))
      atTop (𝓝 0) := by
  have hmajor : Tendsto (fun X : ℕ ↦
      2 / gsA10SourceRoot X) atTop (𝓝 0) :=
    tendsto_gsA10SourceRoot_atTop.const_div_atTop 2
  apply squeeze_zero'
  · filter_upwards
      [Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1)] with X hlog
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast gsA10SourceCutoff_pos X))
      (zero_le_one.trans hlog)
  · filter_upwards
      [eventually_log_gsA10SourceCutoff_le_two_mul_root,
       Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1)] with X hupper hlog
    have hrootpos : 0 < gsA10SourceRoot X :=
      Real.sqrt_pos.2 (zero_lt_one.trans_le hlog)
    have hsquare : gsA10SourceRoot X ^ 2 = Real.log (X : ℝ) :=
      Real.sq_sqrt (zero_le_one.trans hlog)
    calc
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ) ≤
          (2 * gsA10SourceRoot X) / Real.log (X : ℝ) :=
        div_le_div_of_nonneg_right hupper (zero_le_one.trans hlog)
      _ = 2 / gsA10SourceRoot X := by
        rw [← hsquare]
        field_simp
  · exact hmajor

/-- The reciprocal logarithmic window width also vanishes. -/
theorem tendsto_inv_log_gsA10SourceCutoff :
    Tendsto (fun X : ℕ ↦
      (Real.log (gsA10SourceCutoff X : ℝ))⁻¹) atTop (𝓝 0) := by
  have hlogTop : Tendsto (fun X : ℕ ↦
      Real.log (gsA10SourceCutoff X : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_gsA10SourceRoot_atTop
    exact Filter.Eventually.of_forall gsA10SourceRoot_le_log_cutoff
  exact hlogTop.inv_tendsto_atTop

/-- Every fixed polylogarithmic endpoint divided by `X` vanishes. -/
theorem tendsto_log_pow_div_self (k : ℕ) :
    Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) ^ k / (X : ℝ)) atTop (𝓝 0) := by
  have hlittle :
      (fun X : ℕ ↦ Real.log (X : ℝ) ^ k) =o[atTop]
        (fun X : ℕ ↦ (X : ℝ)) := by
    simpa only [Function.comp_apply, Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto
        tendsto_natCast_atTop_atTop
  exact hlittle.tendsto_div_nhds_zero

private theorem tendsto_two_mul_log_sq_div_exp_sourceRoot :
    Tendsto (fun X : ℕ ↦
      2 * Real.log (X : ℝ) ^ 2 /
        Real.exp (gsA10SourceRoot X)) atTop (𝓝 0) := by
  have hpoly : (fun r : ℝ ↦ r ^ (4 : ℝ)) =o[atTop]
      (fun r : ℝ ↦ Real.exp (1 * r)) :=
    isLittleO_rpow_exp_pos_mul_atTop 4 (by norm_num)
  have hpolyNat : (fun r : ℝ ↦ r ^ (4 : ℕ)) =o[atTop]
      (fun r : ℝ ↦ Real.exp r) := by
    convert hpoly using 1
    · funext r
      exact (Real.rpow_natCast r 4).symm
    · funext r
      rw [one_mul]
  have hlim :=
    (hpolyNat.comp_tendsto
      tendsto_gsA10SourceRoot_atTop).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun X : ℕ ↦
      2 * (((fun r : ℝ ↦ r ^ (4 : ℕ)) ∘ gsA10SourceRoot) X /
        ((fun r : ℝ ↦ Real.exp r) ∘ gsA10SourceRoot) X))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2 : ℝ)
  apply hscaled.congr'
  filter_upwards
    [Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
      (eventually_ge_atTop 0)] with X hlog
  have hsquare : gsA10SourceRoot X ^ 2 = Real.log (X : ℝ) :=
    Real.sq_sqrt hlog
  simp only [Function.comp_apply]
  rw [← hsquare]
  ring

/-- The higher-prime-power scalar cost in A.10 vanishes for the explicit
source cutoff. -/
theorem tendsto_log_div_gsA10SourceCutoff_mul_primeReciprocals :
    Tendsto (fun X : ℕ ↦
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
        Erdos67b.PrimeEstimates.primeReciprocals X) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards
      [Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 0)] with X hlog
    exact mul_nonneg
      (div_nonneg hlog (Nat.cast_nonneg _))
      (Erdos67b.PrimeEstimates.primeReciprocals_nonneg X)
  · filter_upwards
      [Erdos67b.PrimeEstimates.eventually_primeReciprocals_le_139,
       Erdos67b.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 1)] with X hprime hlog
    let L := Real.log (X : ℝ)
    have hLpos : 0 < L := zero_lt_one.trans_le hlog
    have hloglog : Real.log L ≤ L := by
      have h := Real.log_le_sub_one_of_pos hLpos
      linarith
    have hprime' : Erdos67b.PrimeEstimates.primeReciprocals X ≤ 2 * L := by
      change Erdos67b.PrimeEstimates.primeReciprocals X ≤
        (139 / 100 : ℝ) * Real.log L at hprime
      calc
        Erdos67b.PrimeEstimates.primeReciprocals X ≤
            (139 / 100 : ℝ) * Real.log L := hprime
        _ ≤ 2 * L := by nlinarith
    have hquot : L / (gsA10SourceCutoff X : ℝ) ≤
        L / Real.exp (gsA10SourceRoot X) :=
      div_le_div_of_nonneg_left (zero_le_one.trans hlog) (Real.exp_pos _)
        (exp_gsA10SourceRoot_le_cutoff X)
    calc
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
          Erdos67b.PrimeEstimates.primeReciprocals X ≤
          (L / Real.exp (gsA10SourceRoot X)) * (2 * L) := by
        dsimp only [L]
        exact mul_le_mul hquot hprime'
          (Erdos67b.PrimeEstimates.primeReciprocals_nonneg X)
          (div_nonneg (zero_le_one.trans hlog) (Real.exp_pos _).le)
      _ = 2 * Real.log (X : ℝ) ^ 2 /
          Real.exp (gsA10SourceRoot X) := by
        dsimp only [L]
        ring
  · exact tendsto_two_mul_log_sq_div_exp_sourceRoot

theorem eventually_log_gsA10SourceCutoff_div_log_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ) ≤ ε := by
  filter_upwards
    [(tendsto_order.1 tendsto_log_gsA10SourceCutoff_div_log).2 ε hε]
      with X hX
  exact hX.le

theorem eventually_inv_log_gsA10SourceCutoff_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (gsA10SourceCutoff X : ℝ))⁻¹ ≤ ε := by
  filter_upwards
    [(tendsto_order.1 tendsto_inv_log_gsA10SourceCutoff).2 ε hε]
      with X hX
  exact hX.le

theorem eventually_log_div_gsA10SourceCutoff_mul_primeReciprocals_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
        Erdos67b.PrimeEstimates.primeReciprocals X ≤ ε := by
  filter_upwards
    [(tendsto_order.1
      tendsto_log_div_gsA10SourceCutoff_mul_primeReciprocals).2 ε hε]
      with X hX
  exact hX.le

theorem eventually_log_pow_div_self_le (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (X : ℝ) ^ k / (X : ℝ) ≤ ε := by
  filter_upwards
    [(tendsto_order.1 (tendsto_log_pow_div_self k)).2 ε hε]
      with X hX
  exact hX.le

/-- One source threshold supplies all structural hypotheses and all four
vanishing scalar budgets, for a prescribed polylogarithmic power. -/
theorem exists_gsA10SourceCutoff_threshold (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      23 ≤ gsA10SourceCutoff X ∧
      gsA10SourceCutoff X ≤ X ∧
      6 ≤ Real.log (gsA10SourceCutoff X : ℝ) ∧
      Real.log (X : ℝ) ^ 4 ≤ (gsA10SourceCutoff X : ℝ) ∧
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ) ≤ ε ∧
      (Real.log (gsA10SourceCutoff X : ℝ))⁻¹ ≤ ε ∧
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
        Erdos67b.PrimeEstimates.primeReciprocals X ≤ ε ∧
      Real.log (X : ℝ) ^ k / (X : ℝ) ≤ ε := by
  have hall : ∀ᶠ X : ℕ in atTop,
      23 ≤ gsA10SourceCutoff X ∧
      gsA10SourceCutoff X ≤ X ∧
      6 ≤ Real.log (gsA10SourceCutoff X : ℝ) ∧
      Real.log (X : ℝ) ^ 4 ≤ (gsA10SourceCutoff X : ℝ) ∧
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ) ≤ ε ∧
      (Real.log (gsA10SourceCutoff X : ℝ))⁻¹ ≤ ε ∧
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
        Erdos67b.PrimeEstimates.primeReciprocals X ≤ ε ∧
      Real.log (X : ℝ) ^ k / (X : ℝ) ≤ ε := by
    filter_upwards
      [eventually_gsA10SourceCutoff_structural,
       eventually_log_gsA10SourceCutoff_div_log_le hε,
       eventually_inv_log_gsA10SourceCutoff_le hε,
       eventually_log_div_gsA10SourceCutoff_mul_primeReciprocals_le hε,
       eventually_log_pow_div_self_le k hε] with X hstruct hratio hinv hhpp hpoly
    exact ⟨hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2,
      hratio, hinv, hhpp, hpoly⟩
  exact Filter.Eventually.exists_forall_of_atTop hall

/-- Finitely many endpoint polylogarithmic powers can be supplied by one
uniform source threshold. -/
theorem exists_gsA10SourceCutoff_uniform_threshold_on_finset
    (s : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ k ∈ s, ∀ X : ℕ, X₀ ≤ X →
      23 ≤ gsA10SourceCutoff X ∧
      gsA10SourceCutoff X ≤ X ∧
      6 ≤ Real.log (gsA10SourceCutoff X : ℝ) ∧
      Real.log (X : ℝ) ^ 4 ≤ (gsA10SourceCutoff X : ℝ) ∧
      Real.log (gsA10SourceCutoff X : ℝ) / Real.log (X : ℝ) ≤ ε ∧
      (Real.log (gsA10SourceCutoff X : ℝ))⁻¹ ≤ ε ∧
      Real.log (X : ℝ) / (gsA10SourceCutoff X : ℝ) *
        Erdos67b.PrimeEstimates.primeReciprocals X ≤ ε ∧
      Real.log (X : ℝ) ^ k / (X : ℝ) ≤ ε := by
  apply Erdos67b.exists_uniform_nat_threshold_on_finset s
  intro k hk
  exact exists_gsA10SourceCutoff_threshold k hε

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.eventually_gsA10SourceCutoff_structural
#print axioms Erdos67b.MRHalaszBands.tendsto_log_gsA10SourceCutoff_div_log
#print axioms Erdos67b.MRHalaszBands.tendsto_inv_log_gsA10SourceCutoff
#print axioms Erdos67b.MRHalaszBands.tendsto_log_div_gsA10SourceCutoff_mul_primeReciprocals
#print axioms Erdos67b.MRHalaszBands.exists_gsA10SourceCutoff_uniform_threshold_on_finset
