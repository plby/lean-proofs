import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspLiftedSquare
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspOuterFrames
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspCentralizer

/-!
# The actual cusp tail frame and the final outer-circle lift

The final point of the actual lifted analytic square determines a deck
frame relative to the canonical clockwise outer lift.  Covering uniqueness
identifies the whole real final curve in that same frame.  Its actual
integer endpoint relation and the canonical endpoint relation then force
the frame to commute with the original cusp generator.  The proved cusp
centralizer theorem applies to this geometrically constructed element.

Both quarter-time frames below retain this same actual tail and the
canonical positive first-generator frame of the original slit sections.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle Homology
open BoundaryLoopSquares SingularMayerVietoris

/-- The whole real canonical curve is the periodic extension of the
literal final path of the actual native-to-outer square. -/
theorem outerClockwiseRegularCurve_eq_periodic :
    (outerClockwiseRegularCurve : ℝ → TriangleRegularQuotient) =
      loopPeriodic outerClockwiseRegularMeridian :=
  loopPeriodic_unique outerClockwiseRegularCurve outerClockwiseRegularCurve_periodic
    outerClockwiseRegularCurve_unit

/-- The complete final projected edge is the canonical outer circle,
with the same real parameter at every time. -/
@[simp] theorem nativePeriodicSquare_one (t : ℝ) :
    nativePeriodicSquare (1, t) = outerClockwiseRegularCurve t :=
  (periodicSquare_final nativeOuterSquare t).trans
    (congrFun outerClockwiseRegularCurve_eq_periodic t).symm

@[simp] theorem nativeLiftedSquare_final_projection (t : ℝ) :
    triangleRegularProject (nativeLiftedSquare (1, t)) = outerClockwiseRegularCurve t :=
  (nativeLiftedSquare_projection 1 t).trans (nativePeriodicSquare_one t)

/-- The actual final basepoint lies in one deck translate of the
specified canonical lower-section lift. -/
theorem nativeLiftedSquare_exists_tailFrame :
    ∃ d : TriangleGroup, nativeLiftedSquare (1, 0) = d • outerClockwiseBaseLift := by
  have he : triangleRegularProject (nativeLiftedSquare (1, 0)) =
      triangleRegularProject outerClockwiseBaseLift :=
    (nativeLiftedSquare_final_projection 0).trans
      (outerClockwiseRegularCurve_zero.trans outerClockwiseBaseLift_project.symm)
  obtain ⟨d, hd⟩ := triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp he
  exact ⟨d, hd.symm⟩

/-- The deck frame determined by the actual lifted analytic tail endpoint. -/
def tailFrame : TriangleGroup := nativeLiftedSquare_exists_tailFrame.choose

/-- This chosen frame is tied to the original lifted homotopy, not just
to a conjugacy class or an abstract peripheral label. -/
theorem tailFrame_apply :
    nativeLiftedSquare (1, 0) = tailFrame • outerClockwiseBaseLift :=
  nativeLiftedSquare_exists_tailFrame.choose_spec

/-- Uniqueness of lifts on the whole real line preserves the actual
tail frame throughout the entire final lifted outer circle. -/
theorem nativeLiftedSquare_final (t : ℝ) :
    nativeLiftedSquare (1, t) = tailFrame • outerClockwiseLift t := by
  have hleft : Continuous (fun u : ℝ => nativeLiftedSquare (1, u)) :=
    nativeLiftedSquare.continuous.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun u : ℝ => tailFrame • outerClockwiseLift u) :=
    (triangleRegularProject_covering.continuous_const_smul tailFrame).comp
      outerClockwiseLift.continuous
  have he : triangleRegularProject ∘ (fun u : ℝ => nativeLiftedSquare (1, u)) =
      triangleRegularProject ∘ (fun u : ℝ => tailFrame • outerClockwiseLift u) := by
    funext u
    simp only [Function.comp_apply, nativeLiftedSquare_final_projection,
      triangleRegularProject_covering.map_smul, outerClockwiseLift_projection]
  exact congrFun (triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq
    hleft hright he 0 (by simpa only [outerClockwiseLift_zero] using tailFrame_apply)) t

/-- The original native inverse-cusp convention still gives the actual
endpoint of this final lifted edge. -/
theorem nativeLiftedSquare_final_endpoint :
    nativeLiftedSquare (1, 1) = triangleCuspGenerator⁻¹ • nativeLiftedSquare (1, 0) := by
  simpa only [Int.cast_one, zero_add, zpow_neg_one] using
    nativeLiftedSquare_translate 1 1 0

/-- The two actual endpoint formulas force the same inverse cusp
generator to commute with the geometrically constructed tail frame. -/
theorem tailFrame_inverse_cusp_commute : Commute triangleCuspGenerator⁻¹ tailFrame := by
  let := triangleRegularProject_covering.isCancelSMul
  change triangleCuspGenerator⁻¹ * tailFrame = tailFrame * triangleCuspGenerator⁻¹
  apply IsCancelSMul.right_cancel _ _ outerClockwiseBaseLift
  calc
    (triangleCuspGenerator⁻¹ * tailFrame) • outerClockwiseBaseLift =
        triangleCuspGenerator⁻¹ • nativeLiftedSquare (1, 0) := by
      rw [mul_smul, tailFrame_apply]
    _ = nativeLiftedSquare (1, 1) := nativeLiftedSquare_final_endpoint.symm
    _ = tailFrame • outerClockwiseLift 1 := nativeLiftedSquare_final 1
    _ = (tailFrame * triangleCuspGenerator⁻¹) • outerClockwiseBaseLift := by
      rw [outerClockwiseLift_one, mul_smul]

/-- In particular the actual tail commutes with the original cusp generator itself. -/
theorem tailFrame_commute : Commute triangleCuspGenerator tailFrame := by
  simpa only [inv_inv] using tailFrame_inverse_cusp_commute.inv_left

/-- The actual tail is therefore in the original cyclic cusp subgroup. -/
theorem tailFrame_mem_zpowers : tailFrame ∈ Subgroup.zpowers triangleCuspGenerator :=
  triangleCuspGenerator_commute_mem_zpowers tailFrame tailFrame_commute

/-- Its cyclic description follows from the actual square and free action. -/
theorem tailFrame_eq_zpow : ∃ k : ℤ, tailFrame = triangleCuspGenerator ^ k :=
  triangleCuspGenerator_commute_eq_zpow tailFrame tailFrame_commute

/-- The inverse frame required by fibre-coordinate changes lies in the same subgroup. -/
theorem tailFrame_inv_eq_zpow : ∃ k : ℤ, tailFrame⁻¹ = triangleCuspGenerator ^ k :=
  triangleCuspGenerator_commute_eq_zpow tailFrame⁻¹ tailFrame_commute.inv_right

/-- At the actual left quarter point the combined frame retains both
the original analytic tail and the canonical positive first generator. -/
theorem nativeLiftedSquare_quarter_frame :
    nativeLiftedSquare (1, 1 / 4) = (tailFrame * triangleGenerator₁) •
      upperLiftOnOverlap normalizedSlitBaseLift 0 outerClockwiseQuarterPoint := by
  rw [nativeLiftedSquare_final, outerClockwiseLift_quarter_frame, mul_smul]

/-- The actual right quarter point has precisely the same combined frame. -/
theorem nativeLiftedSquare_threeQuarters_frame :
    nativeLiftedSquare (1, 3 / 4) = (tailFrame * triangleGenerator₁) •
      upperLiftOnOverlap normalizedSlitBaseLift 2 outerClockwiseThreeQuarterPoint := by
  rw [nativeLiftedSquare_final, outerClockwiseLift_threeQuarters_frame, mul_smul]

/-- The now-proved actual tail fixes every original cusp-invariant class
in actual integral singular homology. -/
theorem tailFrame_homology_fixed (n : ℕ) (a : SingularHomology RealTorus₄ n)
    (ha : triangleHomologyEquiv triangleCuspGenerator n a = a) :
    triangleHomologyEquiv tailFrame n a = a :=
  cuspCentralizer_homology_fixed tailFrame tailFrame_commute n a ha

/-- The inverse actual tail fixes these same classes in every degree. -/
theorem tailFrame_inv_homology_fixed (n : ℕ) (a : SingularHomology RealTorus₄ n)
    (ha : triangleHomologyEquiv triangleCuspGenerator n a = a) :
    triangleHomologyEquiv tailFrame⁻¹ n a = a :=
  cuspCentralizer_inv_homology_fixed tailFrame tailFrame_commute n a ha

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
