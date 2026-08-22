/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZAwayStoppedLazyOverflow
import ErdosProblems.Erdos1165.HLOZShellZeroExternalWindow
import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition

/-!
# Candidate-local lazy cap from the source Theta screen

The upper proof never needs a lazy cap at every visited point.  It needs the
cap only at a selected near-level candidate.  On the literal oriented source,
that point lies in `V₂(I₁)` and the restricted Theta set is empty.  Hence its
endpoint-chain external local time is at least the concrete lower endpoint;
subtracting from its total local time, which is strictly below `m`, gives the
required boundary-plus-lazy cap deterministically.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZCandidateLocalLazyCap

open HLOZAwayStoppedLazyOverflow HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows HLOZSourceOrientedExternalLocalTime
open LazyDecomposition TilingLazyDecomposition
open ScreeningInstantiation
open TilingOrientedShellZeroSourcePartition TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The only lazy cap used by candidate extraction: the complement of the
concrete retained endpoint lower bound inside level `m`. -/
def sourceCandidateLazyCap48 (m : ℕ) : ℕ :=
  m - shellZeroExternalLow48 m

/-- The concrete retained lower endpoint never exceeds the level.  This is
valid even for the finitely many small levels, where `Nat.ceil` truncates a
negative real endpoint to zero. -/
theorem shellZeroExternalLow48_le (m : ℕ) :
    shellZeroExternalLow48 m ≤ m := by
  unfold shellZeroExternalLow48
  apply Nat.ceil_le.mpr
  have hR : 0 ≤ shellZeroCenterRadius m := by
    unfold shellZeroCenterRadius
    exact add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m)
  have hm : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- Pure arithmetic/path decomposition: a below-level point whose phased
external local time is at least the concrete source lower endpoint has its
remaining boundary-plus-lazy contribution below the candidate cap. -/
theorem pathPhasedBoundary_add_lazy_le_sourceCandidateLazyCap48
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n m : ℕ}
    {b : Point}
    (htotal : localTime s n b < m)
    (hexternal : shellZeroExternalLow48 m ≤
      pathPhasedExternalLocalTime t o s n b) :
    pathPhasedBoundaryLocalTime o s n b +
        pathPhasedLazyLocalTime t o s n b ≤
      sourceCandidateLazyCap48 m := by
  have hsplit := localTime_eq_phasedBoundary_add_external_add_lazy
    t o s n b
  unfold sourceCandidateLazyCap48
  have hlow := shellZeroExternalLow48_le m
  omega

/-- Empty restricted Theta turns membership in the literal oriented source
`V₂(I₁)` into the concrete endpoint-chain external lower bound. -/
theorem sourceExternalLow_of_mem_orientedSourceVTwo_theta_good
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n m w high : ℕ}
    {b : Point}
    (hsource : b ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n)
    (htheta : orientedTilingThetaBases t o m w
      (shellZeroExternalLow48 m) high s n = ∅) :
    shellZeroExternalLow48 m ≤
      tilingSourceExternalBaseLocalTime t o s n b := by
  classical
  have hsourceUnion : b ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w ∪
        shellZeroReplacementTotalWindow m w) s n := by
    rw [mem_orientedTilingVTwoBases_iff] at hsource ⊢
    refine ⟨?_, hsource.2⟩
    rw [tilingVTwoBases, Finset.mem_filter] at hsource ⊢
    refine ⟨hsource.1.1, hsource.1.2.1, ?_⟩
    exact Finset.mem_union_left _ hsource.1.2.2
  have hnotTheta : b ∉ orientedTilingThetaBases t o m w
      (shellZeroExternalLow48 m) high s n := by
    rw [htheta]
    simp
  rw [orientedTilingThetaBases, Finset.mem_filter, not_and_or] at hnotTheta
  rcases hnotTheta with hnotSupport | hwindow
  · exact (hnotSupport hsourceUnion).elim
  · exact (not_not.mp hwindow).1

/-- Candidate-local source-correct cap.  No lazy exceptional event and no
probability premise occurs: source membership and Theta-goodness determine
the bound at the selected base. -/
theorem boundary_lazy_le_of_mem_orientedSourceVTwo_theta_good
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n m w high : ℕ}
    {b : Point}
    (hvalid : s ∈ validStepWalk)
    (hsource : b ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n)
    (htheta : orientedTilingThetaBases t o m w
      (shellZeroExternalLow48 m) high s n = ∅) :
    pathPhasedBoundaryLocalTime o s n b +
        pathPhasedLazyLocalTime t o s n b ≤
      sourceCandidateLazyCap48 m := by
  classical
  have hsourceData :=
    (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) s n b).mp hsource
  have htotal : localTime s n b < m := by
    rw [tilingVTwoBases, Finset.mem_filter] at hsourceData
    exact (mem_shellZeroSourceTotalWindow.mp hsourceData.1.2.2).2
  have hsourceExternal :=
    sourceExternalLow_of_mem_orientedSourceVTwo_theta_good
      hsource htheta
  have hpathExternal : shellZeroExternalLow48 m ≤
      pathPhasedExternalLocalTime t o s n b := by
    rw [tilingSourceExternalBaseLocalTime_eq_pathPhased_of_compatible
      t o s n b hvalid hsourceData.2] at hsourceExternal
    exact hsourceExternal
  exact pathPhasedBoundary_add_lazy_le_sourceCandidateLazyCap48
    htotal hpathExternal

/-- Direct realization form: every threshold not exceeding the concrete
source endpoint lower bound is already present in the phased external local
time at the selected candidate. -/
theorem externalThreshold_le_of_mem_orientedSourceVTwo_theta_good
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n m w high : ℕ}
    {b : Point} {externalThreshold : ℕ}
    (hvalid : s ∈ validStepWalk)
    (hthreshold : externalThreshold ≤ shellZeroExternalLow48 m)
    (hsource : b ∈ orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m w) s n)
    (htheta : orientedTilingThetaBases t o m w
      (shellZeroExternalLow48 m) high s n = ∅) :
    externalThreshold ≤ pathPhasedExternalLocalTime t o s n b := by
  have hsourceData :=
    (mem_orientedTilingVTwoBases_iff t o
      (shellZeroSourceTotalWindow m w) s n b).mp hsource
  have hsourceExternal :=
    sourceExternalLow_of_mem_orientedSourceVTwo_theta_good
      hsource htheta
  rw [tilingSourceExternalBaseLocalTime_eq_pathPhased_of_compatible
    t o s n b hvalid hsourceData.2] at hsourceExternal
  exact hthreshold.trans hsourceExternal

end

end Erdos1165.HLOZCandidateLocalLazyCap
