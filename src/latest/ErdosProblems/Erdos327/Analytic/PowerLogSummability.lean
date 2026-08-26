import ErdosProblems.Erdos327.Analytic.LogPowerAsymptotics
import Mathlib.Analysis.PSeries

/-!
# Summability of power-log schedule profiles

Every logarithmic loss may be absorbed by an arbitrarily small positive
power.  Consequently `(n+1)^p log(n+1)^m` is summable whenever `p < -1`.
The tail form below is the interface used by the scheduled bulk sums.
-/

namespace Erdos327.Analytic

open Filter Finset Real Asymptotics

noncomputable section

/-- A negative power beyond `-1` remains summable after multiplication by
any nonnegative real power of a logarithm. -/
theorem summable_nat_add_one_rpow_mul_log_rpow
    {p m : ℝ} (hp : p < -1) (hm : 0 ≤ m) :
    Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ p) *
        log (((n + 1 : ℕ) : ℝ)) ^ m) := by
  let δ : ℝ := (-1 - p) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hpexp : p + δ < -1 := by
    dsimp [δ]
    linarith
  have hg0 :
      Summable (fun n : ℕ ↦ ((n : ℝ) ^ (p + δ))) :=
    Real.summable_nat_rpow.2 hpexp
  have hg :
      Summable (fun n : ℕ ↦
        (((n + 1 : ℕ) : ℝ) ^ (p + δ))) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm] using
      ((summable_nat_add_iff 1).2 hg0)
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop m hδ).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hcast :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlittleNat :
      ∀ᶠ n : ℕ in atTop,
        ‖log (((n + 1 : ℕ) : ℝ)) ^ m‖ ≤
          ‖(((n + 1 : ℕ) : ℝ) ^ δ)‖ :=
    by simpa using hcast.eventually hlittle
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [hlittleNat] with n hn
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog0 :
      0 ≤ log (((n + 1 : ℕ) : ℝ)) := by
    exact log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hleft0 :
      0 ≤ (((n + 1 : ℕ) : ℝ) ^ p) := Real.rpow_nonneg hx.le _
  have hlogpow0 :
      0 ≤ log (((n + 1 : ℕ) : ℝ)) ^ m :=
    Real.rpow_nonneg hlog0 _
  have hδpow0 :
      0 ≤ (((n + 1 : ℕ) : ℝ) ^ δ) :=
    Real.rpow_nonneg hx.le _
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hleft0,
    abs_of_nonneg hlogpow0, abs_of_nonneg hδpow0] at hn ⊢
  calc
    ((n + 1 : ℕ) : ℝ) ^ p *
          log (((n + 1 : ℕ) : ℝ)) ^ m
        ≤ ((n + 1 : ℕ) : ℝ) ^ p *
            ((n + 1 : ℕ) : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_left hn hleft0
    _ = ((n + 1 : ℕ) : ℝ) ^ (p + δ) := by
      rw [← Real.rpow_add hx]

/-- Any fixed logarithmic power is eventually bounded by an arbitrarily
small positive power of `n+1`. -/
theorem eventually_log_add_one_rpow_le_rpow
    (m : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      log (((n + 1 : ℕ) : ℝ)) ^ m ≤
        (((n + 1 : ℕ) : ℝ) ^ δ) := by
  have hlittle :=
    (isLittleO_log_rpow_rpow_atTop m hδ).bound
      (show (0 : ℝ) < 1 by norm_num)
  have hcast :
      Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ)))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hbound := hcast.eventually hlittle
  filter_upwards [hbound] with n hn
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog0 :
      0 ≤ log (((n + 1 : ℕ) : ℝ)) :=
    log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hx.le _)] using hn

/-- Every sufficiently late finite segment of a summable power-log
profile has arbitrarily small mass. -/
theorem exists_powerLogProfile_tail_lt
    {p m ε : ℝ} (hp : p < -1) (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ J' ≥ J, ∀ M : ℕ,
      (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ p) *
          log (((j + 1 : ℕ) : ℝ)) ^ m) < ε := by
  let f : ℕ → ℝ := fun j ↦
    (((j + 1 : ℕ) : ℝ) ^ p) *
      log (((j + 1 : ℕ) : ℝ)) ^ m
  have hf : Summable f :=
    summable_nat_add_one_rpow_mul_log_rpow hp hm
  have htail :
      ∀ᶠ J : ℕ in atTop, (∑' k : ℕ, f (k + J)) < ε :=
    (tendsto_order.1 (tendsto_sum_nat_add f)).2 ε hε
  rcases (eventually_atTop.1 htail) with ⟨J, hJ⟩
  refine ⟨J, fun J' hJJ M ↦ ?_⟩
  have hshift : Summable (fun k : ℕ ↦ f (k + J')) :=
    (summable_nat_add_iff J').2 hf
  have hfinite :
      (∑ k ∈ range (M - J'), f (k + J')) ≤
        ∑' k : ℕ, f (k + J') := by
    exact hshift.sum_le_tsum (range (M - J'))
      (fun k hk ↦ by
        dsimp [f]
        positivity)
  calc
    (∑ j ∈ Ico J' M,
        (((j + 1 : ℕ) : ℝ) ^ p) *
          log (((j + 1 : ℕ) : ℝ)) ^ m) =
        ∑ k ∈ range (M - J'), f (k + J') := by
      rw [Finset.sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro k hk
      dsimp [f]
      rw [show J' + k + 1 = k + J' + 1 by omega]
    _ ≤ ∑' k : ℕ, f (k + J') := hfinite
    _ < ε := hJ J' hJJ

end

end Erdos327.Analytic
