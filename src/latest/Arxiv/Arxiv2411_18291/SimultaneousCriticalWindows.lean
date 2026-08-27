import Arxiv.Arxiv2411_18291.CriticalWindowConcentration

/-!
# Simultaneous control from critical-interval estimates

All drift and variance estimates are allowed to depend on the same good
events. Taking the first failure justifies using those estimates. A finite
union bound gives both an explicit failure probability and an existence
criterion for a trajectory on which every good event holds.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure CriticalWindowControl (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (T : Type*) (n : ℕ) where
  process : T → ℕ → Ω → ℝ
  good : ℕ → Set Ω
  lower : T → ℝ
  upper : T → ℝ
  step : T → ℝ
  variance : T → ℝ
  step_pos : ∀ t, 0 < step t
  variance_nonneg : ∀ t, 0 ≤ variance t
  gap : ∀ t, lower t + step t < upper t
  adapted : ∀ t i, i ≤ n → StronglyMeasurable[ℱ i] (process t i)
  initial : ∀ t, ∀ᵐ ω ∂P, process t 0 ω < lower t
  bounded : ∀ t i, i < n → ∀ᵐ ω ∂P, |process t (i + 1) ω - process t i ω| ≤ step t
  measurable_good : ∀ i < n, MeasurableSet[ℱ i] (good i)
  trend : ∀ t i, i < n → ∀ᵐ ω ∂P, ω ∈ good i → lower t ≤ process t i ω →
    P[fun ω => process t (i + 1) ω - process t i ω | ℱ i] ω ≤ 0
  variance_budget : ∀ t j, j ≤ n → ∀ᵐ ω ∂P, (∀ k < j, ω ∈ good k) →
    (∑ i ∈ range j, Var[fun ω => process t (i + 1) ω - process t i ω; P | ℱ i] ω) ≤
      variance t
  failure : ∀ j ≤ n, ∀ ω, ω ∉ good j → ∃ t, upper t ≤ process t j ω

namespace CriticalWindowControl

variable {ℱ : Filtration ℕ mΩ} {P : Measure Ω} [IsProbabilityMeasure P]
variable {T : Type*} [Fintype T] {n : ℕ} (C : CriticalWindowControl ℱ P T n)

def failureBound : ℝ :=
  ∑ t, n * Real.exp (-((C.upper t - C.lower t - C.step t) ^ 2 /
    (2 * (C.variance t + (C.upper t - C.lower t - C.step t) * C.step t))))

theorem failure_probability_le : P.real {ω | ∃ j ≤ n, ω ∉ C.good j} ≤ C.failureBound := by
  classical
  let E := fun t => {ω | ∃ j ≤ n, C.upper t ≤ C.process t j ω ∧
    (∀ k < j, ω ∈ C.good k) ∧
    (∑ i ∈ range j,
      Var[fun ω => C.process t (i + 1) ω - C.process t i ω; P | ℱ i] ω) ≤ C.variance t}
  have hbudget : ∀ t j, ∀ᵐ ω ∂P, j ≤ n → (∀ k < j, ω ∈ C.good k) →
      (∑ i ∈ range j,
        Var[fun ω => C.process t (i + 1) ω - C.process t i ω; P | ℱ i] ω) ≤ C.variance t := by
    intro t j
    by_cases hj : j ≤ n
    · exact (C.variance_budget t j hj).mono fun _ h _ => h
    · exact ae_of_all _ fun _ h => (hj h).elim
  have hsub : {ω | ∃ j ≤ n, ω ∉ C.good j} ≤ᵐ[P] ⋃ t, E t := by
    filter_upwards [ae_all_iff.mpr (fun t => ae_all_iff.mpr (hbudget t))] with ω hω
    intro hbad
    let j := Nat.find hbad
    have hj : j ≤ n ∧ ω ∉ C.good j := Nat.find_spec hbad
    have hpast : ∀ k < j, ω ∈ C.good k := by
      intro k hk
      by_contra h
      have hle : j ≤ k := Nat.find_min' hbad ⟨hk.le.trans hj.1, h⟩
      omega
    obtain ⟨t, ht⟩ := C.failure j hj.1 ω hj.2
    exact Set.mem_iUnion.mpr ⟨t, j, hj.1, ht, hpast, hω t j hj.1 hpast⟩
  calc
    _ ≤ P.real (⋃ t, E t) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ ∑ t, P.real (E t) := measureReal_iUnion_fintype_le _
    _ ≤ C.failureBound := by
      apply sum_le_sum
      intro t _
      exact critical_window_upper_bound (C.step_pos t) (C.variance_nonneg t) (C.gap t)
        (C.adapted t) (C.initial t) (C.bounded t) C.measurable_good (C.trend t)

theorem exists_good_trajectory (hsmall : C.failureBound < 1) :
    ∃ ω, ∀ j ≤ n, ω ∈ C.good j := by
  classical
  by_contra h
  push Not at h
  have heq : {ω | ∃ j ≤ n, ω ∉ C.good j} = Set.univ := Set.eq_univ_of_forall h
  have hprob := C.failure_probability_le
  rw [heq, probReal_univ] at hprob
  linarith only [hprob, hsmall]

end CriticalWindowControl

end Arxiv2411_18291
