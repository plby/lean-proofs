import ErdosProblems.Erdos67b.LogControlledWeyl

/-!
# Eventual fixed-depth logarithmic Weyl bounds

At a fixed height-band index `r`, both auxiliary scale restrictions in the
finite controlled-Weyl theorem are eventually automatic.  This is the form
needed by the epsilon proof: one first chooses a finite depth cutoff and only
then sends the main height to infinity.
-/

open scoped BigOperators
open Filter

namespace Erdos67b.LogFixedDepth

noncomputable section

open Erdos1149
open Erdos67b.LogWeylParameters
open Erdos67b.LogPhaseHigherDerivative
open Erdos67b.LogControlledWeyl

/-- For one fixed band `X^r ≤ a < X^(r+1)`, the clean power-saving
estimate holds at every sufficiently large scale, uniformly in every prefix
of the dyadic block. -/
theorem exists_fixedDepth_threshold (r : ℕ) (hr : 2 ≤ r) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ P ≤ X, ∀ a : ℝ,
      0 < a → (X : ℝ) ^ r ≤ a → a < (X : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
        AnalyticParameters.envelopeConstant
            10 (terminalConstant r) (depth r) *
          (X : ℝ) ^ (1 - savingExponent r) := by
  obtain ⟨Xlarge, hlarge⟩ :=
    Filter.eventually_atTop.1 (eventually_isLargeLogWeylScale r)
  obtain ⟨Xwindow, hwindow⟩ := exists_window_threshold (depth r)
  refine ⟨max 1 (max Xlarge Xwindow), ?_⟩
  intro X hX P hP a ha halower haupper
  have hXone : 1 ≤ X := (Nat.le_max_left 1 _).trans hX
  have hlargeX : IsLargeLogWeylScale r X :=
    hlarge X ((Nat.le_max_left Xlarge Xwindow).trans
      ((Nat.le_max_right 1 (max Xlarge Xwindow)).trans hX))
  have hwindowX :
      (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X :=
    hwindow X ((Nat.le_max_right Xlarge Xwindow).trans
      ((Nat.le_max_right 1 (max Xlarge Xwindow)).trans hX))
  have hp := parameters hr hXone ha halower haupper hlargeX
  dsimp only at hp
  have hKd : (shiftCount r X : ℝ) * stepSize r X a ≤
      (X : ℝ) ^ (3 / 4 : ℝ) := hp.2.2.2.2.2.2.2.1
  have hPcast : (P : ℝ) ≤ X := by exact_mod_cast hP
  have hfullWindow :
      (P : ℝ) + (depth r : ℝ) * shiftCount r X *
          stepSize r X a + 1 ≤ 2 * X := by
    have hsnonneg : (0 : ℝ) ≤ depth r := by positivity
    have hshift : (depth r : ℝ) *
          ((shiftCount r X : ℝ) * stepSize r X a) ≤
        (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hKd hsnonneg
    calc
      (P : ℝ) + (depth r : ℝ) * shiftCount r X *
          stepSize r X a + 1 ≤
          (X : ℝ) +
            ((depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1) := by
        nlinarith
      _ ≤ (X : ℝ) + X := by
        simpa [add_comm] using add_le_add_left hwindowX (X : ℝ)
      _ = 2 * X := by ring
  exact norm_sum_shiftedLogPhase_le hr hXone hP ha halower haupper
    hlargeX hfullWindow

/-- A named threshold selected from `exists_fixedDepth_threshold`. -/
def fixedDepthThreshold (r : ℕ) (hr : 2 ≤ r) : ℕ :=
  Classical.choose (exists_fixedDepth_threshold r hr)

theorem fixedDepthThreshold_spec (r : ℕ) (hr : 2 ≤ r) :
    ∀ X ≥ fixedDepthThreshold r hr, ∀ P ≤ X, ∀ a : ℝ,
      0 < a → (X : ℝ) ^ r ≤ a → a < (X : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
        AnalyticParameters.envelopeConstant
            10 (terminalConstant r) (depth r) *
          (X : ℝ) ^ (1 - savingExponent r) :=
  Classical.choose_spec (exists_fixedDepth_threshold r hr)

/-- A single scale threshold works for every depth in a prescribed finite
range.  This is the quantifier order used after the epsilon argument chooses
its maximal depth `R`. -/
theorem exists_depthRange_threshold (R : ℕ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ r ∈ Finset.Icc 2 R, ∀ P ≤ X, ∀ a : ℝ,
      0 < a → (X : ℝ) ^ r ≤ a → a < (X : ℝ) ^ (r + 1) →
      ‖∑ n ∈ Finset.range P,
          HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
        AnalyticParameters.envelopeConstant
            10 (terminalConstant r) (depth r) *
          (X : ℝ) ^ (1 - savingExponent r) := by
  have heach : ∀ r ∈ Finset.Icc 2 R,
      ∀ᶠ X : ℕ in atTop, ∀ P ≤ X, ∀ a : ℝ,
        0 < a → (X : ℝ) ^ r ≤ a → a < (X : ℝ) ^ (r + 1) →
        ‖∑ n ∈ Finset.range P,
            HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
          AnalyticParameters.envelopeConstant
              10 (terminalConstant r) (depth r) *
            (X : ℝ) ^ (1 - savingExponent r) := by
    intro r hrmem
    have hr : 2 ≤ r := (Finset.mem_Icc.mp hrmem).1
    exact Filter.eventually_atTop.2
      ⟨fixedDepthThreshold r hr,
        fun X hX ↦ fixedDepthThreshold_spec r hr X hX⟩
  have hall : ∀ᶠ X : ℕ in atTop, ∀ r ∈ Finset.Icc 2 R, ∀ P ≤ X,
      ∀ a : ℝ, 0 < a → (X : ℝ) ^ r ≤ a →
        a < (X : ℝ) ^ (r + 1) →
        ‖∑ n ∈ Finset.range P,
            HigherDerivative.phase (shiftedLogPhase a X n)‖ ≤
          AnalyticParameters.envelopeConstant
              10 (terminalConstant r) (depth r) *
            (X : ℝ) ^ (1 - savingExponent r) :=
    (Finset.eventually_all (Finset.Icc 2 R)).2 heach
  exact Filter.eventually_atTop.1 hall

end

end Erdos67b.LogFixedDepth
