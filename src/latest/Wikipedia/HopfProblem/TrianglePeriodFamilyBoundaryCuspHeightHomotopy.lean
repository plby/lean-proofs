import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspNative
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreEquivariance
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# Vertical-height homotopies of the actual cusp boundary

The logarithmic height varies along a literal line segment in its allowed
open half-line.  The whole regular-family boundary map deforms with this
height, retaining the original real cylinder parameter and the unchanged
rank-four fibre coordinate.  Its fibre equivariance is deduced from the
original boundary map, not posited as an additional identification.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle SpecialPeriods.CuspFamily CuspUniformization
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Cusp
open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The unchanged fibre coordinate of the original cusp boundary cylinder. -/
def nativeFibreCylinder : C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨Prod.snd, continuous_snd⟩

@[simp] theorem nativeFibreCylinder_apply (p : ℝ × RealTorus₄) :
    nativeFibreCylinder p = p.2 := rfl

/-- The literal original boundary and its base lift force this complete
fibre deck relation in the original period coordinates. -/
theorem nativeFibreCylinder_deck (k : ℤ) (p : ℝ × RealTorus₄) :
    nativeFibreCylinder (MappingTorus.deck monodromy k p) =
      (triangleCuspGenerator ^ (-k)) • nativeFibreCylinder p :=
  fibreMap_deck_of_actual boundaryRegularData monodromy
    (boundaryToRegularFamily none) (baseLift specialHeight) nativeFibreCylinder
    triangleCuspGenerator (fun p => boundaryToRegularFamily_mk p.1 p.2)
    (baseLift_translate specialHeight) k p

/-- The actual cusp boundary map at an arbitrary allowed logarithmic height. -/
def heightBoundaryMap (h : Height specialData.radius) :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary, boundaryRegularData.Space) :=
  familyBoundaryMap boundaryRegularData monodromy (baseLift h) nativeFibreCylinder
    triangleCuspGenerator (baseLift_translate h) nativeFibreCylinder_deck

/-- Every real-cylinder representative retains its exact original fibre coordinate. -/
@[simp] theorem heightBoundaryMap_mk (h : Height specialData.radius) (t : ℝ)
    (x : RealTorus₄) :
    heightBoundaryMap h (MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (baseLift h t, x) := rfl

/-- At the original selected height this is the literal original coefficient map. -/
theorem heightBoundaryMap_specialHeight :
    heightBoundaryMap specialHeight = boundaryToRegularFamily none := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective monodromy q
  exact (boundaryToRegularFamily_mk p.1 p.2).symm

/-- Linear interpolation stays in the actual allowed height half-line. -/
def heightSegment (a b : Height specialData.radius) :
    C(unitInterval, Height specialData.radius) :=
  ⟨fun s => ⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ), by
      exact (convex_Ioi (heightThreshold specialData.radius) :
        Convex ℝ (Ioi (heightThreshold specialData.radius))) a.property b.property
        (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel 1 (s : ℝ))⟩,
    (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)).subtype_mk _⟩

@[simp] theorem heightSegment_coe (a b : Height specialData.radius) (s : unitInterval) :
    (heightSegment a b s : ℝ) = (1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ) := rfl

@[simp] theorem heightSegment_zero (a b : Height specialData.radius) :
    heightSegment a b 0 = a := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * (a : ℝ) + 0 * (b : ℝ) = (a : ℝ)
  simp

@[simp] theorem heightSegment_one (a b : Height specialData.radius) :
    heightSegment a b 1 = b := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * (a : ℝ) + 1 * (b : ℝ) = (b : ℝ)
  simp

/-- The whole upstairs base homotopy varies only the imaginary logarithmic coordinate. -/
def heightBaseHomotopy (a b : Height specialData.radius) :
    C(unitInterval × ℝ, TriangleRegularPoint) :=
  ⟨fun p => baseLift (heightSegment a b p.1) p.2,
    (logBaseToRegular_holomorphic specialData.radius specialRadius_cap).continuous.comp
      ((logBaseHeightHomeomorph specialData.radius specialData.radius_pos).symm.continuous.comp
        (((heightSegment a b).continuous.comp continuous_fst).prodMk continuous_snd))⟩

@[simp] theorem heightBaseHomotopy_apply (a b : Height specialData.radius)
    (s : unitInterval) (t : ℝ) :
    heightBaseHomotopy a b (s, t) = baseLift (heightSegment a b s) t := rfl

@[simp] theorem heightBaseHomotopy_zero (a b : Height specialData.radius) (t : ℝ) :
    heightBaseHomotopy a b (0, t) = baseLift a t := by
  rw [heightBaseHomotopy_apply, heightSegment_zero]

@[simp] theorem heightBaseHomotopy_one (a b : Height specialData.radius) (t : ℝ) :
    heightBaseHomotopy a b (1, t) = baseLift b t := by
  rw [heightBaseHomotopy_apply, heightSegment_one]

/-- Every intermediate height obeys the same original integer deck convention. -/
theorem heightBaseHomotopy_translate (a b : Height specialData.radius)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    heightBaseHomotopy a b (s, t + k) =
      (triangleCuspGenerator ^ (-k)) • heightBaseHomotopy a b (s, t) :=
  baseLift_translate (heightSegment a b s) k t

/-- An actual homotopy of whole mapping-torus boundary maps at any two allowed heights. -/
def heightBoundaryHomotopy (a b : Height specialData.radius) :
    (heightBoundaryMap a).Homotopy (heightBoundaryMap b) :=
  (familyBoundaryHomotopy boundaryRegularData monodromy (heightBaseHomotopy a b)
    nativeFibreCylinder triangleCuspGenerator (heightBaseHomotopy_translate a b)
    nativeFibreCylinder_deck).cast (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective monodromy q
      change boundaryRegularData.quotient (heightBaseHomotopy a b (0, p.1), p.2) =
        boundaryRegularData.quotient (baseLift a p.1, p.2)
      rw [heightBaseHomotopy_zero]) (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective monodromy q
      change boundaryRegularData.quotient (heightBaseHomotopy a b (1, p.1), p.2) =
        boundaryRegularData.quotient (baseLift b p.1, p.2)
      rw [heightBaseHomotopy_one])

/-- Its whole-cylinder formula shows that no fibre translation is introduced or omitted. -/
@[simp] theorem heightBoundaryHomotopy_mk (a b : Height specialData.radius)
    (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    heightBoundaryHomotopy a b (s, MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (baseLift (heightSegment a b s) t, x) := rfl

/-- The original actual boundary inclusion deforms vertically to any allowed height. -/
def boundaryToRegularFamily_heightHomotopy (h : Height specialData.radius) :
    (boundaryToRegularFamily none).Homotopy (heightBoundaryMap h) :=
  (heightBoundaryHomotopy specialHeight h).cast heightBoundaryMap_specialHeight rfl

@[simp] theorem boundaryToRegularFamily_heightHomotopy_mk (h : Height specialData.radius)
    (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    (boundaryToRegularFamily_heightHomotopy h).toFun (s, MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (baseLift (heightSegment specialHeight h s) t, x) := rfl

/-- Hence the literal original cusp-to-regular coefficient is the map at
any such height on actual integral singular homology, in every degree. -/
theorem boundaryRegularHomologyMap_height (h : Height specialData.radius) (n : ℕ) :
    boundaryRegularHomologyMap none n = singularHomologyMap (heightBoundaryMap h) n :=
  homotopy_homologyMap (boundaryToRegularFamily_heightHomotopy h) n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
