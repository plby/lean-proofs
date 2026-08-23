/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixADiskSuccess

/-!
# The Appendix-A source estimates at the Proposition-1.3 endpoint

This file is a thin composition layer.  The literal source estimates assembled
in `HLOZAppendixADiskSuccess` first give the Euclidean-disk estimate, the
existing shape bridge gives the square-exit estimate, and the existing
Appendix-A/exit-tail argument gives Proposition 1.3 eventually in time.

`Prop13LowerDeviationBound` is stated for every natural time.  The only new
argument below absorbs the finitely many times before the eventual estimate
into one positive constant.  The resulting bound is then fed unchanged to the
already checked near-critical time-change theorem.
-/

namespace Erdos1166.HLOZAppendixAEndpoint

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

open HLOZAppendixADiskSuccess
open HLOZAppendixAShapeBridge
open HLOZExitTail
open HLOZNearCriticalBridge
open HLOZProp13FromAppendix
open HLOZPropositionA7
open HLOZTimeChange

/-- A convenient reciprocal of the coefficient-free Proposition-1.3 tail
weight.  Multiplying it by that tail weight gives exactly one. -/
noncomputable def prop13TailReciprocal (n : ℕ) : ℝ :=
  Real.exp
    (Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5)))

theorem prop13TailReciprocal_mul_tail (n : ℕ) :
    prop13TailReciprocal n *
        Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5))) = 1 := by
  rw [prop13TailReciprocal, ← Real.exp_add]
  simp

/-- An eventual coefficient-one Proposition-1.3 estimate can be upgraded to
the repository's all-time `Prop13LowerDeviationBound`: a finite sum of
reciprocal tail weights absorbs the exceptional initial segment. -/
theorem prop13LowerDeviationBound_of_eventually
    (d : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) < proposition13Threshold d n} ≤
        ENNReal.ofReal
          (Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5))))) :
    ∃ C : ℝ, 0 < C ∧ Prop13LowerDeviationBound d C := by
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  let C : ℝ := 1 + ∑ n ∈ Finset.range N, prop13TailReciprocal n
  have hC : 0 < C := by
    dsimp [C]
    have hsum_nonneg :
        0 ≤ ∑ n ∈ Finset.range N, prop13TailReciprocal n := by
      exact Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le
    linarith
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · calc
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) < proposition13Threshold d n} ≤
          ENNReal.ofReal
            (Real.exp
              (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5)))) := hN n hn
      _ ≤ ENNReal.ofReal
          (C * Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5)))) := by
        apply ENNReal.ofReal_le_ofReal
        have hCle : 1 ≤ C := by
          dsimp [C]
          have hsum_nonneg :
              0 ≤ ∑ i ∈ Finset.range N, prop13TailReciprocal i := by
            exact Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le
          linarith
        exact (le_mul_iff_one_le_left (Real.exp_pos _)).2 hCle
  · have hnlt : n < N := by omega
    have hreciprocal_le : prop13TailReciprocal n ≤ C := by
      have hsingle : prop13TailReciprocal n ≤
          ∑ i ∈ Finset.range N, prop13TailReciprocal i := by
        apply Finset.single_le_sum
        · intro i hi
          exact (Real.exp_pos _).le
        · exact Finset.mem_range.mpr hnlt
      dsimp [C]
      linarith
    have hone_le : 1 ≤
        C * Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5))) := by
      rw [← prop13TailReciprocal_mul_tail n]
      exact mul_le_mul_of_nonneg_right hreciprocal_le (Real.exp_pos _).le
    calc
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) < proposition13Threshold d n} ≤
          simpleRandomWalkLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal
          (C * Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5)))) :=
        ENNReal.ofReal_le_ofReal hone_le

/-- The Euclidean Appendix-A estimate, after the existing shape and exit-tail
bridges, supplies the precise all-time Proposition-1.3 hypothesis used by the
time-change argument. -/
theorem prop13LowerDeviationBound_of_euclideanAppendixDiskEstimate
    (hsource : EuclideanAppendixDiskEstimate) :
    ∃ C : ℝ, 0 < C ∧
      Prop13LowerDeviationBound lowerTailDelta C := by
  have hdisk : AppendixDiskEstimate :=
    appendixDiskEstimate_of_euclidean hsource
  have heventual := eventually_prop13_lower_deviation_of_disk
    appendixEpsilon_pos appendixEpsilon_lt_two_fifteenths hdisk
  apply prop13LowerDeviationBound_of_eventually lowerTailDelta
  filter_upwards [heventual] with n hn
  have hevent :
      {s | (maxLocalTime s n : ℝ) <
        HLOZTimeChange.proposition13Threshold lowerTailDelta n} =
      {s | (maxLocalTime s n : ℝ) <
        1 / Real.pi * Real.log (n : ℝ) ^ 2 -
          Real.log (n : ℝ) ^ (8 / 5 + 4 * appendixEpsilon : ℝ)} := by
    ext s
    change (maxLocalTime s n : ℝ) <
        HLOZTimeChange.proposition13Threshold lowerTailDelta n ↔
      (maxLocalTime s n : ℝ) <
        1 / Real.pi * Real.log (n : ℝ) ^ 2 -
          Real.log (n : ℝ) ^ (8 / 5 + 4 * appendixEpsilon : ℝ)
    rw [HLOZTimeChange.proposition13Threshold, lowerDeviationExponent,
      four_mul_appendixEpsilon_eq_lowerTailDelta]
    ring
  rw [hevent]
  exact hn

/-- Short source-to-endpoint composition.  The hypothesis is exactly the
eventual `EuclideanDiskSourceEstimates` package: in particular its
`SourceExitWordData` certificates, Gaussian/corridor lower bound, initial and
terminal factors, and final Paley--Zygmund budget remain visible as the only
source-specific inputs. -/
theorem prop13LowerDeviationBound_of_eventually_source_estimates
    {delta : ℝ}
    (atom : (n : ℕ) → Site → NatPath (n - 2) → Set (ℕ → Direction))
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (EuclideanDiskSourceEstimates appendixEpsilon delta n (atom n))) :
    ∃ C : ℝ, 0 < C ∧
      Prop13LowerDeviationBound lowerTailDelta C := by
  exact prop13LowerDeviationBound_of_euclideanAppendixDiskEstimate
    (euclideanAppendixDiskEstimate_of_eventually_source_estimates atom hsource)

/-- The complete checked endpoint needed by the near-critical screening
argument: the source estimates give both a global Proposition-1.3 constant
and the almost-sure eventual fourth-threshold cutoff. -/
theorem prop13_and_nearCritical_cutoff_of_eventually_source_estimates
    {delta : ℝ}
    (atom : (n : ℕ) → Site → NatPath (n - 2) → Set (ℕ → Direction))
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (EuclideanDiskSourceEstimates appendixEpsilon delta n (atom n))) :
    ∃ C : ℝ, 0 < C ∧
      Prop13LowerDeviationBound lowerTailDelta C ∧
      (∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
        s ∈ hlozThresholdTimeEvent m →
          firstKSitesReachLevel m 4 s ≤
            (nearCriticalHorizon m : WithTop ℕ)) := by
  obtain ⟨C, hC, hprop13⟩ :=
    prop13LowerDeviationBound_of_eventually_source_estimates atom hsource
  exact ⟨C, hC, hprop13,
    ae_eventually_fourth_threshold_le_nearCriticalHorizon_of_prop13
      C hC hprop13⟩

end Erdos1166.HLOZAppendixAEndpoint
