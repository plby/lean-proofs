import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldPieces

/-!
# The actual special cusp overlap and its boundary mapping torus

The small cusp piece used in the global threefold has the same original
toric quotient as the radius-restricted analytic cusp data.  Its overlap
with the regular base is exactly the nonzero parameter locus.  This
literal identification transports the whole-family mapping-torus
equivalence, with no choice of a new marking or a substitute fibre.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp

open SpecialPeriods SpecialPeriods.Threefold CuspUniformization

/-- The actual special cusp germs at the exact chosen filling radius. -/
def specialData : CuspFamily.Data :=
  CuspPiece.restrictedData specialCuspData specialBaseCover specialCuspRadius_le

@[simp] theorem specialData_radius : specialData.radius = specialBaseCover.radius none := rfl

@[simp] theorem specialData_correction : specialData.correction = specialCuspData.correction := rfl

/-- The literal punctured subset of the actual special cusp filling. -/
abbrev SpecialPuncturedPiece :=
  {x : SpecialCuspPiece | specialCuspPieceProjectionToBase x ∈ regularPatch}

/-- The overlap identification is the identity on the original full toric quotient. -/
def specialPuncturedHomeomorph :
    SpecialPuncturedPiece ≃ₜ PuncturedQuotient specialData.correction specialData.radius where
  toFun x := ⟨x.1,
    (CuspPiece.projectionToBase_mem_regular_iff specialCuspData specialBaseCover x.1).mp
      x.property⟩
  invFun x := ⟨x.1,
    (CuspPiece.projectionToBase_mem_regular_iff specialCuspData specialBaseCover x.1).mpr
      x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem specialPuncturedHomeomorph_coe (x : SpecialPuncturedPiece) :
    (specialPuncturedHomeomorph x).val = (x : SpecialCuspPiece) := rfl

@[simp] theorem specialPuncturedHomeomorph_symm_coe
    (x : PuncturedQuotient specialData.correction specialData.radius) :
    (specialPuncturedHomeomorph.symm x : SpecialCuspPiece) = x.val := rfl

/-- The entire special overlap, retaining its logarithmic radial coordinate. -/
def specialPuncturedProductHomeomorph :
    SpecialPuncturedPiece ≃ₜ Height specialData.radius × Boundary :=
  specialPuncturedHomeomorph.trans (puncturedProductHomeomorph specialData)

/-- A specified interior logarithmic height, requiring no extra radius assumptions. -/
def specialHeight : Height specialData.radius :=
  ⟨heightThreshold specialData.radius + 1, by
    change heightThreshold specialData.radius < heightThreshold specialData.radius + 1
    exact lt_add_one _⟩

/-- The actual special overlap at any allowed boundary height. -/
def specialMappingTorusHomotopyEquivAt (h : Height specialData.radius) :
    SpecialPuncturedPiece ≃ₕ Boundary :=
  specialPuncturedHomeomorph.toHomotopyEquiv.trans
    (puncturedMappingTorusHomotopyEquiv specialData h)

/-- The unconditional boundary mapping-torus model for the actual special cusp overlap. -/
def specialMappingTorusHomotopyEquiv : SpecialPuncturedPiece ≃ₕ Boundary :=
  specialMappingTorusHomotopyEquivAt specialHeight

/-- The actual boundary representative in the punctured special cusp piece. -/
def specialBoundaryInclusion : C(Boundary, SpecialPuncturedPiece) :=
  specialMappingTorusHomotopyEquiv.invFun

@[simp] theorem specialBoundaryInclusion_native (x : Boundary) :
    specialPuncturedHomeomorph (specialBoundaryInclusion x) =
      boundaryInclusion specialData specialHeight x := rfl

/-- The same boundary map into the full original cusp filling. -/
def specialBoundaryToPiece : C(Boundary, SpecialCuspPiece) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(SpecialPuncturedPiece, SpecialCuspPiece)).comp
    specialBoundaryInclusion

@[simp] theorem specialBoundaryToPiece_apply (x : Boundary) :
    specialBoundaryToPiece x = (specialBoundaryInclusion x : SpecialCuspPiece) := rfl

/-- The actual special boundary cylinder before its monodromy quotient. -/
def specialBoundaryCylinder : C(ℝ × RealTorus₄, SpecialPuncturedPiece) :=
  specialBoundaryInclusion.comp
    ⟨MappingTorus.mk monodromy, MappingTorus.mk_continuous monodromy⟩

@[simp] theorem specialBoundaryCylinder_native (t : ℝ) (x : RealTorus₄) :
    specialPuncturedHomeomorph (specialBoundaryCylinder (t, x)) =
      boundaryCylinder specialData specialHeight (t, x) := rfl

/-- The special whole-cylinder map uses the original varying real period matrices. -/
theorem specialBoundaryCylinder_realCoordinates (t : ℝ) (x : RealPlane₄) :
    (specialBoundaryCylinder (t, standardLattice.mkQ x) : SpecialCuspPiece) =
      (puncturedCuspCover specialData.correction specialData.radius
        ⟨((logPoint specialData.radius specialData.radius_pos t specialHeight : ℂ),
          specialData.periods.periodEquiv
            (logPoint specialData.radius specialData.radius_pos t specialHeight) x),
          (logPoint specialData.radius specialData.radius_pos t specialHeight).property⟩).val :=
  congrArg (fun q : PuncturedQuotient specialData.correction specialData.radius =>
    q.val)
    (boundaryCylinder_realCoordinates specialData specialHeight t x)

/-- The actual special overlap satisfies the proved `M₀` endpoint identification. -/
theorem specialBoundaryCylinder_endpoint (t : ℝ) (x : RealTorus₄) :
    specialBoundaryCylinder (t + 1, x) = specialBoundaryCylinder (t, monodromy x) :=
  congrArg specialBoundaryInclusion (MappingTorus.mk_add_one monodromy t x)

/-- The literal original cusp parameter along the special boundary cylinder. -/
theorem specialBoundaryCylinder_parameter (t : ℝ) (x : RealTorus₄) :
    CuspQuotient.projection specialCuspData.correction (specialBaseCover.radius none)
      (specialBoundaryCylinder (t, x)) =
      exponential ((t : ℂ) + (specialHeight : ℝ) * Complex.I) :=
  boundaryCylinder_base specialData specialHeight t x

/-- The actual global base projection of the special boundary cylinder. -/
theorem specialBoundaryCylinder_base (t : ℝ) (x : RealTorus₄) :
    specialCuspPieceProjectionToBase (specialBoundaryCylinder (t, x)) =
      (punctureChart none).symm
        (exponential ((t : ℂ) + (specialHeight : ℝ) * Complex.I)) :=
  congrArg (punctureChart none).symm (specialBoundaryCylinder_parameter t x)

/-- The base-circle coordinate of an actual punctured special cusp point. -/
def specialBaseCircle : C(SpecialPuncturedPiece, MappingTorus.Circle) :=
  (puncturedBaseCircle specialData).comp
    ⟨specialPuncturedHomeomorph, specialPuncturedHomeomorph.continuous⟩

theorem specialBaseCircle_boundaryCylinder (t : ℝ) (x : RealTorus₄) :
    specialBaseCircle (specialBoundaryCylinder (t, x)) = (t : MappingTorus.Circle) :=
  puncturedBaseCircle_boundaryCylinder specialData specialHeight t x

theorem specialMappingTorusHomotopyEquiv_base (x : SpecialPuncturedPiece) :
    MappingTorus.base monodromy (specialMappingTorusHomotopyEquiv x) =
      specialBaseCircle x := rfl

/-- The actual original torus fibre map at time zero, into the full cusp filling. -/
def specialFibreToPiece : C(RealTorus₄, SpecialCuspPiece) :=
  specialBoundaryToPiece.comp (MappingTorus.HomologyCover.fibreInclusion monodromy)

@[simp] theorem specialFibreToPiece_apply (x : RealTorus₄) :
    specialFibreToPiece x = (specialBoundaryCylinder (0, x) : SpecialCuspPiece) := rfl

theorem specialFibreToPiece_realCoordinates (x : RealPlane₄) :
    specialFibreToPiece (standardLattice.mkQ x) =
      (puncturedCuspCover specialData.correction specialData.radius
        ⟨((logPoint specialData.radius specialData.radius_pos 0 specialHeight : ℂ),
          specialData.periods.periodEquiv
            (logPoint specialData.radius specialData.radius_pos 0 specialHeight) x),
          (logPoint specialData.radius specialData.radius_pos 0 specialHeight).property⟩).val :=
  specialBoundaryCylinder_realCoordinates 0 x

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp
