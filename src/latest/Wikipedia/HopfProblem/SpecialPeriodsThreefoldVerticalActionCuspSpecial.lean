import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry

/-!
# The vertical flow on the actual cusp piece of the threefold

The toric quotient construction is specialized to the already constructed
cusp correction and radius.  All analytic hypotheses are discharged by
that actual data.  Native holomorphicity and holomorphicity in the existing
common threefold model are related by the previously proved identity
biholomorphism, not by replacing the atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open ToricCharts

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "CD" => CuspGeometry.data

attribute [local instance] CuspGeometry.nativeChartedSpace
  specialCuspPieceChartedSpace Threefold.chartedSpace

/-- The actual vertical flow on the full cusp piece of the constructed threefold. -/
def specialFlow (s : ℂ) : CuspGeometry.LocalSpace → CuspGeometry.LocalSpace :=
  flow (CD).correction (CD).radius s

@[simp] theorem specialFlow_zero (x : CuspGeometry.LocalSpace) : specialFlow 0 x = x :=
  flow_zero (CD).correction (CD).radius x

theorem specialFlow_add (s t : ℂ) (x : CuspGeometry.LocalSpace) :
    specialFlow (s + t) x = specialFlow s (specialFlow t x) :=
  flow_add (CD).correction (CD).radius s t x

@[simp] theorem specialFlow_int_cast (n : ℤ) (x : CuspGeometry.LocalSpace) :
    specialFlow (n : ℂ) x = x := flow_int_cast (CD).correction (CD).radius n x

@[simp] theorem specialFlow_neg_left (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialFlow (-s) (specialFlow s x) = x :=
  flow_neg_left (CD).correction (CD).radius s x

@[simp] theorem specialFlow_neg_right (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialFlow s (specialFlow (-s) x) = x :=
  flow_neg_right (CD).correction (CD).radius s x

@[simp] theorem parameter_specialFlow (s : ℂ) (x : CuspGeometry.LocalSpace) :
    CuspGeometry.parameter (specialFlow s x) = CuspGeometry.parameter x :=
  projection_flow (CD).correction (CD).radius s x

theorem specialFlow_continuous (s : ℂ) : Continuous (specialFlow s) :=
  flow_continuous (CD).correction (CD).radius s

/-- Joint holomorphicity for the original three-coordinate quotient atlas. -/
theorem specialFlow_joint_holomorphic :
    ContMDiff ((I₃).prod I₁) I₃ ω
      (fun p : CuspGeometry.LocalSpace × ℂ => specialFlow p.2 p.1) :=
  flow_joint_holomorphic (CD).correction (CD).radius (CD).radius_pos (CD).radius_lt_one
    (CD).holomorphic (CD).smallDrift

theorem specialFlow_holomorphic (s : ℂ) : ContMDiff I₃ I₃ ω (specialFlow s) :=
  flow_holomorphic (CD).correction (CD).radius (CD).radius_pos (CD).radius_lt_one
    (CD).holomorphic (CD).smallDrift s

/-- Each actual cusp time map is biholomorphic in the original native atlas. -/
def specialFlowBiholomorph (s : ℂ) :
    Diffeomorph I₃ I₃ CuspGeometry.LocalSpace CuspGeometry.LocalSpace ω :=
  flowBiholomorph (CD).correction (CD).radius (CD).radius_pos (CD).radius_lt_one
    (CD).holomorphic (CD).smallDrift s

@[simp] theorem specialFlowBiholomorph_apply (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialFlowBiholomorph s x = specialFlow s x := rfl

/-- The same actual time map, expressed in the existing common model. -/
def specialFlowCommonBiholomorph (s : ℂ) :
    Diffeomorph IF IF CuspGeometry.LocalSpace CuspGeometry.LocalSpace ω :=
  (CuspPiece.nativeToCommon specialCuspData specialBaseCover specialCuspRadius_le).symm.trans
    ((specialFlowBiholomorph s).trans
      (CuspPiece.nativeToCommon specialCuspData specialBaseCover specialCuspRadius_le))

@[simp] theorem specialFlowCommonBiholomorph_apply (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialFlowCommonBiholomorph s x = specialFlow s x := rfl

theorem specialFlow_common_holomorphic (s : ℂ) : ContMDiff IF IF ω (specialFlow s) :=
  (specialFlowCommonBiholomorph s).contMDiff

/-- Joint holomorphicity also holds in the unchanged common-model cusp atlas. -/
theorem specialFlow_joint_common_holomorphic :
    ContMDiff ((IF).prod I₁) IF ω
      (fun p : CuspGeometry.LocalSpace × ℂ => specialFlow p.2 p.1) := by
  let e : Diffeomorph I₃ IF CuspGeometry.LocalSpace CuspGeometry.LocalSpace ω :=
    CuspPiece.nativeToCommon specialCuspData specialBaseCover specialCuspRadius_le
  have he : ContMDiff ((IF).prod I₁) ((I₃).prod I₁) ω
      (fun p : CuspGeometry.LocalSpace × ℂ => (e.symm p.1, p.2)) :=
    (e.symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact e.contMDiff.comp (specialFlow_joint_holomorphic.comp he)

/-- The native flow followed by the actual inclusion is jointly holomorphic
into the genuine glued threefold. -/
theorem inclusion_specialFlow_joint_holomorphic :
    ContMDiff ((I₃).prod I₁) IF ω
      (fun p : CuspGeometry.LocalSpace × ℂ => CuspGeometry.inclusion (specialFlow p.2 p.1)) :=
  CuspGeometry.inclusion_holomorphic.comp specialFlow_joint_holomorphic

theorem specialCuspPieceProjectionToBase_specialFlow (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialCuspPieceProjectionToBase (specialFlow s x) = specialCuspPieceProjectionToBase x := by
  change CuspPiece.projectionToBase specialCuspData specialBaseCover (specialFlow s x) =
    CuspPiece.projectionToBase specialCuspData specialBaseCover x
  rw [CuspPiece.projectionToBase_apply, CuspPiece.projectionToBase_apply]
  exact congrArg _ (parameter_specialFlow s x)

/-- The global projection is preserved on the actual full cusp patch. -/
theorem projection_inclusion_specialFlow (s : ℂ) (x : CuspGeometry.LocalSpace) :
    Threefold.projection (CuspGeometry.inclusion (specialFlow s x)) =
      Threefold.projection (CuspGeometry.inclusion x) := by
  rw [CuspGeometry.projection_inclusion, CuspGeometry.projection_inclusion]
  exact specialCuspPieceProjectionToBase_specialFlow s x

/-- The literal logarithmic representative formula for the actual cusp data. -/
theorem specialFlow_totalCuspCover (s : ℂ) (p : CuspUniformization.LogCover (CD).radius) :
    specialFlow s (CuspUniformization.totalCuspCover (CD).correction (CD).radius p) =
      CuspUniformization.totalCuspCover (CD).correction (CD).radius (logFlow (CD).radius s p) :=
  flow_totalCuspCover (CD).correction (CD).radius s p

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
