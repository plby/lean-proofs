import ErdosProblems.Erdos520.Doob
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem520

/-!
# Doob maximal inequalities localized at the initial sigma-algebra

Caich's small-energy event is measurable before the later prime blocks are
revealed.  Multiplying a martingale by its indicator therefore preserves the
martingale property.  This file records that standard localization directly,
without treating conditioning on an event as a new probability primitive.
-/

section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒜 : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- A martingale remains a martingale after it is killed off the complement
of an event visible at time zero. -/
theorem Martingale.indicator_initial [IsFiniteMeasure μ]
    (hX : Martingale X 𝒜 μ) {A : Set Ω}
    (hA : MeasurableSet[𝒜 0] A) :
    Martingale (fun n => A.indicator (X n)) 𝒜 μ := by
  let gate : Ω → ℝ := A.indicator (fun _ => 1)
  have hgate (n : ℕ) : StronglyMeasurable[𝒜 n] gate := by
    apply StronglyMeasurable.indicator stronglyMeasurable_const
    exact (𝒜.mono (Nat.zero_le n)) A hA
  have hpoint (n : ℕ) : A.indicator (X n) = gate * X n := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [gate, hω]
  have hint (n : ℕ) : Integrable (A.indicator (X n)) μ := by
    exact (hX.integrable n).indicator ((𝒜.le 0) A hA)
  apply martingale_nat
  · intro n
    change StronglyMeasurable[𝒜 n] (A.indicator (X n))
    rw [hpoint]
    exact (hgate n).mul (hX.stronglyAdapted n)
  · exact hint
  · intro n
    rw [hpoint n, hpoint (n + 1)]
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (hgate n) (by simpa [← hpoint (n + 1)] using! hint (n + 1))
      (hX.integrable (n + 1))
    filter_upwards [hX.condExp_ae_eq (Nat.le_succ n), hpull] with ω hmart hpullω
    rw [hpullω]
    change gate ω * X n ω = gate ω * μ[X (n + 1) | 𝒜 n] ω
    rw [hmart]

/-- Localized weak Doob inequality.  On an event visible at time zero, an
upper bound for the initial value controls the probability that a
nonnegative martingale crosses a later threshold. -/
theorem Martingale.measure_initial_inter_maximal_le [IsProbabilityMeasure μ]
    (hX : Martingale X 𝒜 μ) (hXnonneg : ∀ n ω, 0 ≤ X n ω)
    {A : Set Ω} (hA : MeasurableSet[𝒜 0] A)
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u)
    (hinitial : ∀ ω ∈ A, X 0 ω ≤ a) (n : ℕ) :
    ENNReal.ofReal u * μ (A ∩ {ω | u ≤ finiteRunningMax X n ω}) ≤
      ENNReal.ofReal a := by
  let G : ℕ → Ω → ℝ := fun k => A.indicator (X k)
  have hG : Martingale G 𝒜 μ := Martingale.indicator_initial hX hA
  have hGnonneg : 0 ≤ G := by
    intro k ω
    by_cases hω : ω ∈ A <;> simp [G, hω, hXnonneg]
  let E : Set Ω := {ω | u ≤ finiteRunningMax G n ω}
  have hE : E = A ∩ {ω | u ≤ finiteRunningMax X n ω} := by
    ext ω
    by_cases hω : ω ∈ A
    · have hpath : (fun k => G k ω) = fun k => X k ω := by
        funext k
        simp [G, hω]
      simp only [E, Set.mem_setOf_eq, Set.mem_inter_iff, hω, true_and]
      unfold finiteRunningMax
      simp_rw [hpath]
    · have hpath : (fun k => G k ω) = fun _k => 0 := by
        funext k
        simp [G, hω]
      simp only [E, Set.mem_setOf_eq, Set.mem_inter_iff, hω, false_and,
        iff_false]
      unfold finiteRunningMax
      simp_rw [hpath]
      simpa using! (not_le_of_gt hu)
  have hmax := maximal_ineq hG.submartingale hGnonneg
    (ε := ⟨u, hu.le⟩) n
  have htotal : ∫ ω, G n ω ∂μ ≤ a := by
    calc
      (∫ ω, G n ω ∂μ) = ∫ ω, G 0 ω ∂μ := by
        symm
        simpa only [setIntegral_univ] using!
          hG.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
      _ ≤ ∫ _ω, a ∂μ := by
        exact integral_mono (f := G 0) (g := fun _ω : Ω => a)
          (hG.integrable 0) (integrable_const a) (fun ω => by
          by_cases hω : ω ∈ A
          · simpa [G, hω] using! hinitial ω hω
          · simp [G, hω, ha])
      _ = a := by simp
  have hset : ∫ ω in E, G n ω ∂μ ≤ a := by
    exact (setIntegral_le_integral (hG.integrable n)
      (ae_of_all μ fun ω => hGnonneg n ω)).trans htotal
  have hmaxE : ENNReal.ofReal u * μ E ≤
      ENNReal.ofReal (∫ ω in E, G n ω ∂μ) := by
    simpa only [E, finiteRunningMax, ENNReal.coe_nnreal_eq,
      ENNReal.coe_toNNReal, ENNReal.ofReal_eq_coe_nnreal hu.le] using! hmax
  rw [hE] at hmaxE hset
  calc
    ENNReal.ofReal u * μ (A ∩ {ω | u ≤ finiteRunningMax X n ω}) ≤
        ENNReal.ofReal
          (∫ ω in A ∩ {ω | u ≤ finiteRunningMax X n ω}, G n ω ∂μ) := hmaxE
    _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal hset

/-- Real-valued form of the localized weak Doob inequality. -/
theorem Martingale.measureReal_initial_inter_maximal_le [IsProbabilityMeasure μ]
    (hX : Martingale X 𝒜 μ) (hXnonneg : ∀ n ω, 0 ≤ X n ω)
    {A : Set Ω} (hA : MeasurableSet[𝒜 0] A)
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u)
    (hinitial : ∀ ω ∈ A, X 0 ω ≤ a) (n : ℕ) :
    μ.real (A ∩ {ω | u ≤ finiteRunningMax X n ω}) ≤ a / u := by
  have h := Martingale.measure_initial_inter_maximal_le
    hX hXnonneg hA ha hu hinitial n
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le,
    ENNReal.toReal_ofReal ha] at hreal
  change u * μ.real (A ∩ {ω | u ≤ finiteRunningMax X n ω}) ≤ a at hreal
  exact (le_div_iff₀ hu).2 (by simpa [mul_comm] using! hreal)

end

end Problem520
end Erdos
