import Wikipedia.HopfProblem.CuspBoundaryGammaZeroTorus
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroMappingTorus

/-!
# The literal gamma-zero cusp boundary inclusion

The actual restricted cusp homeomorphism and the proved equivariant
zero-coordinate fibre inclusion induce a map of the original mapping
tori. It preserves real time and is injective. In particular this is a
whole geometric boundary map, not merely a selected homology class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open PeriodTorusHigherHomology

/-- The actual mapping torus of the proved restricted native cusp shear. -/
abbrev Boundary := MappingTorus.Torus restrictedMonodromy

/-- The literal inclusion into the original native cusp mapping torus. -/
def boundaryMap : C(Boundary, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  mappingTorusMap restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy

/-- No time or fibre reparametrization occurs in the actual quotient map. -/
@[simp] theorem boundaryMap_mk (t : ℝ) (y : ProductTorus 3) :
    boundaryMap (MappingTorus.mk restrictedMonodromy (t, y)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, fibreMap y) := rfl

/-- Original real period representatives exhibit the literal zero first coordinate. -/
theorem boundaryMap_coordinateProjection (t : ℝ) (x : Fin 3 → ℝ) :
    boundaryMap (MappingTorus.mk restrictedMonodromy (t, coordinateProjection 3 x)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy
        (t, standardLattice.mkQ (Fin.cons 0 x)) := by
  rw [boundaryMap_mk, fibreMap_coordinateProjection]

@[simp] theorem boundaryMap_base (q : Boundary) :
    MappingTorus.base ThreefoldOverlapMappingTorus.Cusp.monodromy (boundaryMap q) =
      MappingTorus.base restrictedMonodromy q :=
  mappingTorusMap_base restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy q

/-- The actual map is an inclusion on the original quotient spaces. -/
theorem boundaryMap_injective : Function.Injective boundaryMap :=
  mappingTorusMap_injective restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy fibreMap_injective

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
