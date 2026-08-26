/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure endpoint estimates along dyadic degree blocks.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointProbability

namespace Erdos521

open MeasureTheory Filter

theorem summable_dyadic_neg_rpow {p : ℝ} (hp : 0 < p) :
    Summable (fun j : ℕ ↦ ((2 ^ j : ℕ) : ℝ) ^ (-p)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Summable (fun j : ℕ ↦ Real.exp (-p * Real.log 2) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hlog))
  apply hs.congr
  intro j
  rw [Nat.cast_pow, Nat.cast_ofNat,
    Real.rpow_def_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j), Real.log_pow,
    ← Real.exp_nat_mul]
  congr 1
  ring

theorem ae_eventually_notMem_of_summable_real {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (h : Summable (fun j ↦ μ.real (E j))) :
    ∀ᵐ ω ∂μ, ∀ᶠ j : ℕ in atTop, ω ∉ E j := by
  apply ae_eventually_notMem
  have hsum := h.tsum_ofReal_ne_top
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using hsum

theorem ae_dyadic_notMem_of_power_decay {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω) {p C : ℝ} (hp : 0 < p)
    (h : ∀ᶠ n : ℕ in atTop, μ.real (E n) ≤ C * (n : ℝ) ^ (-p)) :
    ∀ᵐ ω ∂μ, ∀ᶠ j : ℕ in atTop, ω ∉ E (2 ^ j) := by
  have ht : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hs : Summable (fun j : ℕ ↦ μ.real (E (2 ^ j))) := by
    apply ((summable_dyadic_neg_rpow hp).mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [ht.eventually h] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hj
  exact ae_eventually_notMem_of_summable_real μ (fun j ↦ E (2 ^ j)) hs

/-- One interval with fixed center/radius constants is controlled simultaneously
for all degrees in each sufficiently late dyadic block. -/
theorem ae_endpoint_local_dyadic_bound {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hgeometry : 4 * max (4 * b - a) 0 < τ * Real.log 4) :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, 2 ^ j ≤ m → m ≤ 2 * 2 ^ j →
      (localRootCount ε m (endpointCenter a (2 ^ j)) (endpointRadius b (2 ^ j)) : ℝ) <
        τ * Real.log (2 ^ j : ℕ) := by
  obtain ⟨p, hp, hdecay⟩ := endpoint_local_probability_decay ha hb hgeometry
  let E := fun n : ℕ ↦ {ε | ∃ m, n ≤ m ∧ m ≤ 2 * n ∧
    endpointThreshold τ n ≤ localRootCount ε m (endpointCenter a n) (endpointRadius b n)}
  have h := ae_dyadic_notMem_of_power_decay sequenceLaw E hp hdecay
  filter_upwards [h] with ε hε
  filter_upwards [hε] with j hj
  intro m hm hm'
  have hlt : localRootCount ε m (endpointCenter a (2 ^ j)) (endpointRadius b (2 ^ j)) <
      endpointThreshold τ (2 ^ j) := by
    by_contra hh
    exact hj ⟨m, hm, hm', Nat.le_of_not_gt hh⟩
  exact Nat.lt_ceil.mp hlt

end Erdos521
