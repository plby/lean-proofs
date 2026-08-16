import Wikipedia.GreenTao.Transference.RelativeCountingInduction
import Wikipedia.GreenTao.Transference.RelativeSzemeredi

/-!
# An explicit error schedule for relative simplex counting

The active-face induction in `RelativeCountingInduction` asks for a scalar
sequence `error`.  Its successor condition is

```text
(1 + ξ) * (3η + 2√(3η) + 2 error(r) + 4ξ)
  ≤ (error(r + 1) - cutError)².
```

This file chooses equality: the next error is `cutError` plus the square
root of the expression on the left.  Nonnegativity of the three input
errors then proves all numerical hypotheses of the active-face induction.
The last section records that every fixed finite stage tends jointly to
zero with the three input errors.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-- The explicit scalar budget used by relative active-face counting.

Stage zero pays for the bounded telescoping base.  Each successor stage
pays one direct face-cut error and the Cauchy--Schwarz square root generated
by the preceding stage. -/
noncomputable def relativeCountingErrorSchedule
    (m : ℕ) (cutError η ξ : ℝ) : ℕ → ℝ
  | 0 => ((m + 2 : ℕ) : ℝ) * cutError
  | r + 1 =>
      cutError +
        Real.sqrt
          ((1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * relativeCountingErrorSchedule m cutError η ξ r +
              4 * ξ))

@[simp]
theorem relativeCountingErrorSchedule_zero
    (m : ℕ) (cutError η ξ : ℝ) :
    relativeCountingErrorSchedule m cutError η ξ 0 =
      ((m + 2 : ℕ) : ℝ) * cutError :=
  rfl

@[simp]
theorem relativeCountingErrorSchedule_succ
    (m r : ℕ) (cutError η ξ : ℝ) :
    relativeCountingErrorSchedule m cutError η ξ (r + 1) =
      cutError +
        Real.sqrt
          ((1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * relativeCountingErrorSchedule
                m cutError η ξ r + 4 * ξ)) :=
  rfl

/-- Every stage of the schedule is nonnegative when the three input
errors are nonnegative. -/
theorem relativeCountingErrorSchedule_nonneg
    (m : ℕ) {cutError η ξ : ℝ}
    (hcut : 0 ≤ cutError) :
    ∀ r : ℕ, 0 ≤ relativeCountingErrorSchedule m cutError η ξ r := by
  intro r
  induction r with
  | zero =>
      exact mul_nonneg (Nat.cast_nonneg _) hcut
  | succ r _ih =>
      rw [relativeCountingErrorSchedule_succ]
      exact add_nonneg hcut (Real.sqrt_nonneg _)

/-- The schedule has exactly the base budget required by relative
counting. -/
theorem relativeCountingErrorSchedule_base
    (m : ℕ) (cutError η ξ : ℝ) :
    ((m + 2 : ℕ) : ℝ) * cutError ≤
      relativeCountingErrorSchedule m cutError η ξ 0 := by
  rw [relativeCountingErrorSchedule_zero]

/-- Every successor budget contains at least the direct face-cut error. -/
theorem relativeCountingErrorSchedule_next
    (m : ℕ) (cutError η ξ : ℝ) :
    ∀ r : ℕ,
      cutError ≤
        relativeCountingErrorSchedule m cutError η ξ (r + 1) := by
  intro r
  rw [relativeCountingErrorSchedule_succ]
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- The successor definition solves the Cauchy--Schwarz root recurrence
with equality. -/
theorem relativeCountingErrorSchedule_root
    (m : ℕ) {cutError η ξ : ℝ}
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    ∀ r : ℕ,
      (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * relativeCountingErrorSchedule m cutError η ξ r +
            4 * ξ) ≤
        (relativeCountingErrorSchedule m cutError η ξ (r + 1) -
          cutError) ^ 2 := by
  intro r
  have hschedule :
      0 ≤ relativeCountingErrorSchedule m cutError η ξ r :=
    relativeCountingErrorSchedule_nonneg m hcut r
  have hfirst : 0 ≤ 1 + ξ := by
    linarith
  have hsecond :
      0 ≤
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * relativeCountingErrorSchedule m cutError η ξ r +
          4 * ξ := by
    positivity
  have hradicand :
      0 ≤
        (1 + ξ) *
          (3 * η + 2 * Real.sqrt (3 * η) +
            2 * relativeCountingErrorSchedule m cutError η ξ r +
            4 * ξ) :=
    mul_nonneg hfirst hsecond
  rw [relativeCountingErrorSchedule_succ]
  have hsub :
      cutError +
            Real.sqrt
              ((1 + ξ) *
                (3 * η + 2 * Real.sqrt (3 * η) +
                  2 * relativeCountingErrorSchedule
                    m cutError η ξ r + 4 * ξ)) -
          cutError =
        Real.sqrt
          ((1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * relativeCountingErrorSchedule
                m cutError η ξ r + 4 * ξ)) := by
    ring
  rw [hsub, Real.sq_sqrt hradicand]

/-- The explicit schedule discharges every scalar hypothesis of fully
decoded relative counting. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_of_errorSchedule
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active cutError
      (relativeCountingErrorSchedule m cutError η ξ
        (activeFaceCount active)) := by
  exact
    hLF.maskedSimplexComparisonLe_of_linearForms
      hν
      (relativeCountingErrorSchedule m cutError η ξ)
      (relativeCountingErrorSchedule_base m cutError η ξ)
      hξ hconvert
      (relativeCountingErrorSchedule_next m cutError η ξ)
      (relativeCountingErrorSchedule_root m hcut hη hξ)
      active

/-- The all-active mask has one active face for each element of its
finite index type. -/
@[simp]
theorem activeFaceCount_allActive (k : ℕ) :
    activeFaceCount (fun _ : Fin k => true) = k := by
  simp [activeFaceCount, activeFaceSet]

/-- Convenient all-active form of the explicit relative-counting
comparison. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_allActive_of_errorSchedule
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1))) :
    MaskedSimplexComparisonLe (m + 1) N ν
      (fun _ => true) cutError
      (relativeCountingErrorSchedule m cutError η ξ (m + 2)) := by
  simpa using
    hLF.maskedSimplexComparisonLe_of_errorSchedule
      hν hcut hη hξ hconvert (fun _ => true)

/-! ## Arithmetic-progression specialization -/

/-- An all-active masked simplex comparison is precisely the relative AP
comparison after translating cut discrepancy to the canonical simplex.

The coprimality hypothesis makes every canonical face coordinate change
invertible.  This is the only extra input needed by the AP specialization. -/
theorem MaskedSimplexComparisonLe.relativeAPComparisonLe_of_allActive
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {cutError countError : ℝ}
    (hcomparison :
      MaskedSimplexComparisonLe (r + 1) N ν
        (fun _ => true) cutError countError)
    (hN : Nat.Coprime N (Nat.factorial (r + 1))) :
    RelativeAPComparisonLe r N ν cutError countError := by
  intro f g hf0 hfν hg hcut
  have hF :
      SimplexEdgeMajorizedBy
        (apSimplexSystem (r + 2) N f)
        (apMaskedSimplexMajorantSystem
          (r + 1) N ν (fun _ => true)) := by
    intro i x
    constructor
    · exact hf0 _
    · change
        f (apSimplexForm (r + 2) N i x) ≤
          apMaskedFaceMajorant ν (fun _ => true) i
            (apSimplexForm (r + 2) N i x)
      rw [apMaskedFaceMajorant_of_active]
      · exact hfν _
      · rfl
  have hG :
      EdgeWeightsInUnitInterval
        (apSimplexSystem (r + 2) N g) := by
    intro i x
    exact ⟨hg.nonneg _, hg.le_one _⟩
  have hsimplex :=
    hcomparison
      (apSimplexSystem (r + 2) N f)
      (apSimplexSystem (r + 2) N g)
      hF hG
      (hcut.edgeFaceCutDiscrepancyLe_apSimplexSystem hN)
  simpa only [
    apSimplexSystem_simplexCount_eq_cyclicAPCount r N f,
    apSimplexSystem_simplexCount_eq_cyclicAPCount r N g] using hsimplex

/-- The explicit schedule therefore gives quantitative relative counting
for cyclic arithmetic progressions of length `r + 2`. -/
theorem HasLinearFormsCondition.relativeAPComparisonLe_of_errorSchedule
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (r + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (r + 2),
        (1 + η) ^ (2 ^ (r + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (r + 2) j) * η) ≤
          ξ ^ (2 ^ (r + 1)))
    (hN : Nat.Coprime N (Nat.factorial (r + 1))) :
    RelativeAPComparisonLe r N ν cutError
      (relativeCountingErrorSchedule r cutError η ξ (r + 2)) := by
  exact
    (hLF.maskedSimplexComparisonLe_allActive_of_errorSchedule
      hν hcut hη hξ hconvert).relativeAPComparisonLe_of_allActive hN

/-! ## Joint smallness at every fixed finite stage -/

/-- At zero input, every finite stage of the schedule is zero. -/
@[simp]
theorem relativeCountingErrorSchedule_zero_inputs
    (m r : ℕ) :
    relativeCountingErrorSchedule m 0 0 0 r = 0 := by
  induction r with
  | zero =>
      simp
  | succ r ihr =>
      simp [relativeCountingErrorSchedule_succ, ihr]

/-- Every fixed stage is a continuous function of the three input
errors. -/
theorem continuous_relativeCountingErrorSchedule
    (m r : ℕ) :
    Continuous
      (fun p : ℝ × (ℝ × ℝ) =>
        relativeCountingErrorSchedule m p.1 p.2.1 p.2.2 r) := by
  induction r with
  | zero =>
      simp only [relativeCountingErrorSchedule_zero]
      fun_prop
  | succ r ihr =>
      simp only [relativeCountingErrorSchedule_succ]
      fun_prop

/-- Consequently, each fixed finite-rank budget tends jointly to zero
when the cut, linear-forms, and cross-correlation errors tend to zero. -/
theorem tendsto_relativeCountingErrorSchedule_zero
    (m r : ℕ) :
    Tendsto
      (fun p : ℝ × (ℝ × ℝ) =>
        relativeCountingErrorSchedule m p.1 p.2.1 p.2.2 r)
      (𝓝 (0, (0, 0))) (𝓝 0) := by
  simpa using
    (continuous_relativeCountingErrorSchedule m r).tendsto
      (0, (0, 0))

end Wikipedia.SzemeredisTheorem
