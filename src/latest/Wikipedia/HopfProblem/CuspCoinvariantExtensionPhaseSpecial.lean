import Wikipedia.HopfProblem.CuspCoinvariantExtensionPhaseCollar

/-!
# The actual cusp phase is smooth on its original outer collar

The proved native quotient-atlas smoothness specializes to the actual
cusp piece.  The existing identity biholomorphism between the native
three-coordinate atlas and the original common threefold atlas gives the
same real-smooth statement in that common model.  Only the scalar field
of differentiation changes; both atlases and their identification are
the original ones.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open SpecialPeriods SpecialPeriods.Threefold

local notation "I₃" => modelWithCornersSelf ℝ (ToricCharts.CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℝ ℂ

/-- The unchanged native cusp quotient atlas gives real smoothness on
the actual open outer collar. -/
theorem specialCapPhase_native_contMDiffOn_outer (bound : ℝ) (hbound : 0 < bound) :
    letI := CuspGeometry.nativeChartedSpace
    ContMDiffOn I₃ I₁ ∞ (specialCapPhase bound hbound)
      (outerCollar CuspAttaching.data bound (specialCollarExtension bound hbound) :
        Set (ThreefoldHomologyFinitenessCusp.FullSpace CuspAttaching.data)) := by
  let := CuspGeometry.nativeChartedSpace
  exact capPhase_contMDiffOn_outer CuspAttaching.data bound
    (specialCollarExtension bound hbound)

/-- The same phase is real smooth in the original common atlas used by
the actual threefold gluing, through its genuine identity biholomorphism. -/
theorem specialCapPhase_contMDiffOn_outer (bound : ℝ) (hbound : 0 < bound) :
    letI := specialCuspPieceChartedSpace
    ContMDiffOn IF I₁ ∞ (specialCapPhase bound hbound)
      (outerCollar CuspAttaching.data bound (specialCollarExtension bound hbound) :
        Set (ThreefoldHomologyFinitenessCusp.FullSpace CuspAttaching.data)) := by
  let := specialCuspPieceChartedSpace
  let := CuspGeometry.nativeChartedSpace
  have hid : ContMDiff IF I₃ ∞ (fun x : SpecialCuspPiece => x) :=
    (CuspCircleNormalTrivialization.contMDiff_real_of_complex
      (CuspPiece.nativeToCommon specialCuspData specialBaseCover
        specialCuspRadius_le).symm.contMDiff).of_le le_top
  exact (specialCapPhase_native_contMDiffOn_outer bound hbound).comp
    hid.contMDiffOn (fun _ hx => hx)

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
