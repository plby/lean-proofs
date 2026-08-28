import Wikipedia.HopfProblem.CuspBoundaryToricExtensionTorus
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroMappingTorus
import Wikipedia.HopfProblem.MappingTorusHomologyCoveringMap

/-!
# The literal swept phase torus in the original cusp boundary

The identity mapping torus of the fixed two-torus maps into the actual
cusp mapping torus by the literal fixed-period inclusion.  Precomposing
with the existing degree-one circle-product map gives the continuous
boundary map.  Its real-cylinder formula has unchanged real time and
the original period coordinates `(0,0,w,δ)`.

The degree-one product map is retained explicitly so its already proved
positive-circle Wang normalization can be applied to these actual maps.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open PeriodTorusHigherHomology MappingTorusHomology.Covering

/-- The literal identity-monodromy mapping torus of the two phase circles. -/
abbrev IdentityBoundary := MappingTorus.Torus (Homeomorph.refl (ProductTorus 2))

theorem identityMonodromy_period : (Homeomorph.refl (ProductTorus 2)) ^ (1 : ℕ) = 1 := by
  ext y
  rfl

/-- The original degree-one product map to that actual identity mapping torus. -/
def identityProductMap : C(MappingTorus.Circle × ProductTorus 2, IdentityBoundary) :=
  productCover 1 (Homeomorph.refl (ProductTorus 2)) identityMonodromy_period

/-- Real time is unchanged by the degree-one product map. -/
@[simp] theorem identityProductMap_real (t : ℝ) (y : ProductTorus 2) :
    identityProductMap ((t : MappingTorus.Circle), y) =
      MappingTorus.mk (Homeomorph.refl (ProductTorus 2)) (t, y) := by
  change productCover 1 (Homeomorph.refl (ProductTorus 2))
    identityMonodromy_period ((t : MappingTorus.Circle), y) =
      MappingTorus.mk (Homeomorph.refl (ProductTorus 2)).symm (t, y)
  rw [productCover_real_apply, Nat.cast_one, mul_one]

/-- The actual map of the two original integer-orbit mapping-torus quotients. -/
def mappingTorusInclusion : C(IdentityBoundary, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  CuspBoundaryGammaZero.mappingTorusMap (Homeomorph.refl (ProductTorus 2))
    ThreefoldOverlapMappingTorus.Cusp.monodromy fibreMap fibreMap_monodromy

@[simp] theorem mappingTorusInclusion_mk (t : ℝ) (y : ProductTorus 2) :
    mappingTorusInclusion (MappingTorus.mk (Homeomorph.refl (ProductTorus 2)) (t, y)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, fibreMap y) := rfl

theorem mappingTorusInclusion_injective : Function.Injective mappingTorusInclusion :=
  CuspBoundaryGammaZero.mappingTorusMap_injective (Homeomorph.refl (ProductTorus 2))
    ThreefoldOverlapMappingTorus.Cusp.monodromy fibreMap fibreMap_monodromy fibreMap_injective

/-- The continuous sweep of the two fixed phase periods around the actual cusp boundary. -/
def boundaryMap :
    C(MappingTorus.Circle × ProductTorus 2, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  mappingTorusInclusion.comp identityProductMap

/-- The requested literal real-cylinder formula for the actual boundary map. -/
@[simp] theorem boundaryMap_real (t : ℝ) (y : ProductTorus 2) :
    boundaryMap ((t : MappingTorus.Circle), y) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, fibreMap y) := by
  change mappingTorusInclusion (identityProductMap ((t : MappingTorus.Circle), y)) = _
  rw [identityProductMap_real, mappingTorusInclusion_mk]

/-- In the original real lattice quotient, the first two periods remain exactly zero. -/
theorem boundaryMap_coordinateProjection (t : ℝ) (x : Fin 2 → ℝ) :
    boundaryMap ((t : MappingTorus.Circle), coordinateProjection 2 x) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy
        (t, standardLattice.mkQ ![0, 0, x 0, x 1]) := by
  rw [boundaryMap_real, fibreMap_coordinateProjection]

/-- The boundary map preserves the actual base-circle coordinate. -/
@[simp] theorem boundaryMap_base (p : MappingTorus.Circle × ProductTorus 2) :
    MappingTorus.base ThreefoldOverlapMappingTorus.Cusp.monodromy (boundaryMap p) = p.1 := by
  rcases p with ⟨s, y⟩
  induction s using Quotient.inductionOn with
  | h t =>
    rw [boundaryMap_real]
    rfl

/-- At time zero this is the actual native fibre inclusion composed with the fixed subtorus. -/
@[simp] theorem boundaryMap_zero (y : ProductTorus 2) :
    boundaryMap (0, y) =
      MappingTorus.HomologyCover.fibreInclusion ThreefoldOverlapMappingTorus.Cusp.monodromy
        (fibreMap y) := by
  change boundaryMap (0, y) =
    MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (0, fibreMap y)
  simpa only [AddCircle.coe_zero] using boundaryMap_real 0 y

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
