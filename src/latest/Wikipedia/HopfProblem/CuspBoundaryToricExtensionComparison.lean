import Wikipedia.HopfProblem.CuspBoundaryToricExtensionHeight
import Wikipedia.HopfProblem.CuspBoundaryToricExtensionBoundary
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusGlobal
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspRegular

/-!
# The actual toric boundary map is the restriction of the actual disc extension

All comparisons are identities of the original continuous maps.  Real
time, the original logarithmic height, and the original ordered real
period coordinates are unchanged.  The comparison with the regular
family is included pointwise, independently of any Wang or kernel
calculation.  The period coordinates here refer to the source's hatted
dual basis in `Λ`, not its cohomology basis in `V`.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open CuspQuotient CuspUniformization SpecialPeriods.CuspFamily PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus.Cusp

/-- The original whole cusp boundary map into the full cap at any allowed height. -/
def boundaryToFull (D : Data) (h : Height D.radius) :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary, QuotientSpace D.correction D.radius) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(PuncturedQuotient D.correction D.radius, QuotientSpace D.correction D.radius)).comp
      (boundaryInclusion D h)

@[simp] theorem boundaryToFull_mk (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    boundaryToFull D h (MappingTorus.mk monodromy (t, x)) =
      (boundaryCylinder D h (t, x)).val := rfl

/-- The literal swept two-torus map into that same full cusp cap. -/
def toricBoundaryToFull (D : Data) (h : Height D.radius) :
    C(MappingTorus.Circle × ProductTorus 2, QuotientSpace D.correction D.radius) :=
  (boundaryToFull D h).comp boundaryMap

/-- Exact extension identity for the whole boundary product, not only its homology classes. -/
theorem toricBoundaryToFull_eq_extension (D : Data) (h : Height D.radius) :
    toricBoundaryToFull D h =
      (discExtension D.correction D.radius).comp
        ((circleAtHeight D h).prodMap (ContinuousMap.id (ProductTorus 2))) := by
  apply ContinuousMap.ext
  rintro ⟨s, y⟩
  induction s using Quotient.inductionOn with
  | h t =>
    obtain ⟨x, rfl⟩ := coordinateProjection_surjective 2 y
    change boundaryToFull D h (boundaryMap ((t : MappingTorus.Circle), coordinateProjection 2 x)) =
      discExtension D.correction D.radius
        (circleAtHeight D h (t : MappingTorus.Circle), coordinateProjection 2 x)
    rw [boundaryMap_coordinateProjection, boundaryToFull_mk]
    exact boundaryCylinder_toric_real D h t x

/-- The original special gluing coefficient is precisely the same full-cap map. -/
theorem boundaryToFilling_eq_boundaryToFull :
    ThreefoldOverlapMappingTorus.boundaryToFilling none =
      boundaryToFull specialData specialHeight := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  rfl

/-- The actual global cusp attachment on the swept toric subspace extends
over the original full disc times the two compact period circles. -/
theorem boundaryToFilling_toric_eq_extension :
    (ThreefoldOverlapMappingTorus.boundaryToFilling none).comp boundaryMap =
      (discExtension specialData.correction specialData.radius).comp
        ((circleAtHeight specialData specialHeight).prodMap
          (ContinuousMap.id (ProductTorus 2))) := by
  rw [boundaryToFilling_eq_boundaryToFull]
  exact toricBoundaryToFull_eq_extension specialData specialHeight

/-- The actual regular-family coefficient retains exactly the same
original real period vector `(0,0,w,δ)` at every real boundary time.
This comparison precedes and does not use any Wang-coordinate assertion. -/
theorem boundaryToRegularFamily_toric_real (t : ℝ) (x : Fin 2 → ℝ) :
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily none
        (boundaryMap ((t : MappingTorus.Circle), coordinateProjection 2 x)) =
      boundaryRegularData.quotient
        (logBaseToRegular specialData.radius specialRadius_cap
          (logPoint specialData.radius specialData.radius_pos t specialHeight),
          standardLattice.mkQ ![0, 0, x 0, x 1]) := by
  rw [boundaryMap_coordinateProjection]
  exact boundaryToRegularFamily_cusp_realCoordinates t ![0, 0, x 0, x 1]

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
