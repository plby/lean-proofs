import ErdosProblems.Erdos520.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter MeasureTheory

namespace Erdos
namespace Problem520

/-!
# Almost-sure interpolation from a cofinal test sequence

This file isolates the deterministic interpolation step used after estimates
have been proved on a sparse sequence of test points.  In particular, it does
not encode interpolation failure as a sequence of fixed exceptional events.
Both the test-point constant and the interval-increment constant may depend on
the sample.
-/

/-- Almost-sure eventual control on the values of `M` at a sequence of test
points.  The multiplicative constant is allowed to depend on the sample. -/
def AETestPointBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) (scale : ℕ → ℝ)
    (test : ℕ → ℕ) : Prop :=
  ∀ᵐ omega ∂μ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ k : ℕ in atTop,
      |M omega (test k)| ≤ C * scale (test k)

/-- Almost-sure eventual control on every increment between two consecutive
test points.  The right side uses the scale at the upper endpoint; this is the
form naturally produced by maximal interpolation lemmas.  The constant is
allowed to depend on the sample. -/
def AEIntervalIncrementBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℕ → ℝ) (scale : ℕ → ℝ)
    (test : ℕ → ℕ) : Prop :=
  ∀ᵐ omega ∂μ, ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,
      test k ≤ N → N ≤ test (k + 1) →
        |M omega N - M omega (test k)| ≤ D * scale (test (k + 1))

/-- Deterministic local comparability of a scale on each interval between
consecutive test points.  Both endpoint scales are compared with the scale at
the interpolated point. -/
def AdjacentScaleComparable (scale : ℕ → ℝ) (test : ℕ → ℕ)
    (A : ℝ) : Prop :=
  0 ≤ A ∧ ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,
    test k ≤ N → N ≤ test (k + 1) →
      scale (test k) ≤ A * scale N ∧
      scale (test (k + 1)) ≤ A * scale N

/-- A cofinal natural-valued sequence brackets every sufficiently large
natural number between two consecutive values. -/
theorem eventually_exists_testBracket
    {test : ℕ → ℕ} (hcofinal : Tendsto test atTop atTop) :
    ∀ᶠ N : ℕ in atTop, ∃ k : ℕ,
      test k ≤ N ∧ N ≤ test (k + 1) := by
  filter_upwards [eventually_gt_atTop (test 0)] with N hN
  have hex : ∃ j : ℕ, N ≤ test j := by
    have heventually : ∀ᶠ j : ℕ in atTop, N ≤ test j :=
      hcofinal.eventually (eventually_ge_atTop N)
    exact heventually.exists
  let j := Nat.find hex
  have hj : N ≤ test j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro hjzero
    have : N ≤ test 0 := by simpa [hjzero] using! hj
    omega
  obtain ⟨k, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  rw [hjk] at hj
  refine ⟨k, ?_, ?_⟩
  · have hnot : ¬N ≤ test k := by
      intro hNk
      have hfind : Nat.find hex ≤ k := Nat.find_min' hex hNk
      change j ≤ k at hfind
      rw [hjk] at hfind
      omega
    omega
  · simpa [Nat.succ_eq_add_one] using! hj

/-- Strengthening of `eventually_exists_testBracket`: the selected bracket
can be required to satisfy any property that holds eventually in the test
index. -/
theorem eventually_exists_testBracket_and
    {test : ℕ → ℕ} (htest : Monotone test)
    (hcofinal : Tendsto test atTop atTop) {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ N : ℕ in atTop, ∃ k : ℕ,
      test k ≤ N ∧ N ≤ test (k + 1) ∧ P k := by
  rw [eventually_atTop] at hP
  obtain ⟨k₀, hk₀⟩ := hP
  filter_upwards [eventually_exists_testBracket hcofinal,
      eventually_gt_atTop (test k₀)] with N hbracket hN
  obtain ⟨k, hkN, hNk⟩ := hbracket
  refine ⟨k, hkN, hNk, hk₀ k ?_⟩
  by_contra hnot
  have hsucc : k + 1 ≤ k₀ := by omega
  have := htest hsucc
  omega

/-- Interpolation with sample-dependent constants.

An almost-sure eventual bound on a monotone cofinal sequence, together with
an almost-sure eventual maximal-increment bound on adjacent intervals and a
deterministic scale comparison, gives an almost-sure eventual bound at every
natural input. -/
theorem ae_eventually_bound_of_testPoints_and_increments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → ℕ → ℝ} {scale : ℕ → ℝ} {test : ℕ → ℕ} {A : ℝ}
    (htest : Monotone test) (hcofinal : Tendsto test atTop atTop)
    (hscale : AdjacentScaleComparable scale test A)
    (hpoints : AETestPointBound μ M scale test)
    (hincrements : AEIntervalIncrementBound μ M scale test) :
    ∀ᵐ omega ∂μ, ∃ E : ℝ, 0 ≤ E ∧
      ∀ᶠ N : ℕ in atTop, |M omega N| ≤ E * scale N := by
  rcases hscale with ⟨hA, hscale⟩
  filter_upwards [hpoints, hincrements] with omega hpoint hincrement
  obtain ⟨C, hC, hpoint⟩ := hpoint
  obtain ⟨D, hD, hincrement⟩ := hincrement
  refine ⟨A * (C + D), mul_nonneg hA (add_nonneg hC hD), ?_⟩
  have hindex : ∀ᶠ k : ℕ in atTop,
      |M omega (test k)| ≤ C * scale (test k) ∧
      (∀ N : ℕ, test k ≤ N → N ≤ test (k + 1) →
        |M omega N - M omega (test k)| ≤ D * scale (test (k + 1))) ∧
      (∀ N : ℕ, test k ≤ N → N ≤ test (k + 1) →
        scale (test k) ≤ A * scale N ∧
        scale (test (k + 1)) ≤ A * scale N) := by
    filter_upwards [hpoint, hincrement, hscale] with k hkpoint hkincrement hkscale
    exact ⟨hkpoint, hkincrement, hkscale⟩
  filter_upwards [eventually_exists_testBracket_and htest hcofinal hindex] with N hN
  obtain ⟨k, hkN, hNk, hkpoint, hkincrement, hkscale⟩ := hN
  have hbase : |M omega (test k)| ≤ C * (A * scale N) :=
    hkpoint.trans (mul_le_mul_of_nonneg_left (hkscale N hkN hNk).1 hC)
  have hinc : |M omega N - M omega (test k)| ≤ D * (A * scale N) :=
    (hkincrement N hkN hNk).trans
      (mul_le_mul_of_nonneg_left (hkscale N hkN hNk).2 hD)
  calc
    |M omega N| =
        |M omega (test k) + (M omega N - M omega (test k))| := by ring_nf
    _ ≤ |M omega (test k)| + |M omega N - M omega (test k)| := abs_add_le _ _
    _ ≤ C * (A * scale N) + D * (A * scale N) := add_le_add hbase hinc
    _ = A * (C + D) * scale N := by ring

/-- Direct endpoint in the terminology of Erdős #520.  This theorem matches
the almost-sure eventual conclusion of an interpolation lemma: it requires no
summable family of fixed-threshold interpolation-failure events. -/
theorem criticalUpperBound_of_ae_testPoints_and_increments
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → ℕ → ℝ} (test : ℝ → ℕ → ℕ) (A : ℝ → ℝ)
    (htest : ∀ η : ℝ, 0 < η → Monotone (test η))
    (hcofinal : ∀ η : ℝ, 0 < η → Tendsto (test η) atTop atTop)
    (hscale : ∀ η : ℝ, 0 < η →
      AdjacentScaleComparable (criticalScale η) (test η) (A η))
    (hpoints : ∀ η : ℝ, 0 < η →
      AETestPointBound μ M (criticalScale η) (test η))
    (hincrements : ∀ η : ℝ, 0 < η →
      AEIntervalIncrementBound μ M (criticalScale η) (test η)) :
    CriticalUpperBound μ M := by
  intro η hη
  exact ae_eventually_bound_of_testPoints_and_increments
    (htest η hη) (hcofinal η hη) (hscale η hη)
    (hpoints η hη) (hincrements η hη)

end Problem520
end Erdos
