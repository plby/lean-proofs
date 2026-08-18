/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92ProjectedCovolumeCancellation
import ErdosProblems.Erdos186.CFP.Bilu.Section92WeightedRankRepair

/-!
# Uniform Section 9.2 rank repair

The unimodular covolume identity removes the final lattice-dependent
quantity from the projected-volume estimate.  This module feeds that
estimate into the rank-weighted minimal-rank argument and obtains a stopped
presentation with uniform rank and weighted-volume bounds.  No analytic
premise remains.
-/

namespace Erdos186.CFP.Bilu.Section92UniformRankRepair

open MeasureTheory
open Mahler MinkowskiUpper
open Section92BodyPresentationQuotient
open Section92OuterInjectivityBridge
open Section92PresentationDescent
open Section92PresentationQuotientAssembly
open Section92ShortKernel
open Section92WeightedRankRepair
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {n s : ℕ} {T : ℝ}

/-- The ordinary real volume of one primitive quotient costs at most rank
times the collision radius. -/
theorem bodyVolume_quotientRankedBodyPresentation_le_rank_mul
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card) (hT : 0 ≤ T) :
    bodyVolume (quotientRankedBodyPresentation X S hcard) ≤
      (n : ℝ) * T * bodyVolume ⟨n, X⟩ := by
  rw [bodyVolume_quotientRankedBodyPresentation]
  simpa only [bodyVolume, unitBall] using
    S.coordinateProjectedBody_volumeReal_le_rank_mul
      X.rank_pos X.definite hT

/-- Fully unconditional Section 9.2 termination.  The repair factor is a
single finite expression depending only on the dilation parameter and the
uniform rank ceiling. -/
theorem exists_enlargedInjective_of_canonicalQuotient
    (s rankBound : ℕ) (hcard : 1 < A.card)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound) :
    ∃ X : RankedBodyPresentation A,
      EnlargedInjective s X ∧ X.1 ≤ rankBound ∧
        rankWeightedBodyVolume
            (canonicalRankRepairFactor s rankBound) X ≤
          rankWeightedBodyVolume
            (canonicalRankRepairFactor s rankBound) initial := by
  apply exists_enlargedInjective_of_localQuotientVolumeBound
    s rankBound hcard initial hinitialRank
  intro X _hXrank S
  have hT : 0 ≤ outerDilationBound X.1 (2 * s) :=
    outerDilationBound_nonneg X.1 (2 * s)
  have hbase :=
    bodyVolume_quotientRankedBodyPresentation_le_rank_mul
      X.2 S hcard hT
  have hfactor :
      (X.1 : ℝ) * outerDilationBound X.1 (2 * s) ≤
        (X.1 : ℝ) *
          (2 * outerDilationBound X.1 (2 * s)) := by
    nlinarith [hT, (Nat.cast_nonneg X.1 : (0 : ℝ) ≤ X.1)]
  exact hbase.trans <| mul_le_mul_of_nonneg_right hfactor
    (bodyVolume_pos X).le

end

end Erdos186.CFP.Bilu.Section92UniformRankRepair

#print axioms
  Erdos186.CFP.Bilu.Section92UniformRankRepair.exists_enlargedInjective_of_canonicalQuotient
