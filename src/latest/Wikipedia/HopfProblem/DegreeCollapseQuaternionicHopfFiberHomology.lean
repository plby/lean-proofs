import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiberFactors
import Wikipedia.NoExoticSixSphere.ProductModTwoThirdHomology
import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity

/-!
# Actual mod-two middle coordinates of the original Hopf-square regular fiber

Transport the native coefficient homology through the existing product
diffeomorphism. The original factor sphere maps become the actual product
sections, so their homology classes are precisely the two coordinate vectors.
No basis or intersection pairing is assigned by definition.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberHomology

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors
open SphereHomologyCoefficients

attribute [local instance] modHomologyModule

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

def homeomorphEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ModHomology 2 X 3 ≃ₗ[ZMod 2] ModHomology 2 Y 3 where
  toEquiv := (modHomologyHomeomorphEquiv 2 e 3).toEquiv
  map_add' := (modHomologyHomeomorphEquiv 2 e 3).map_add
  map_smul' c x := by
    change modHomologyHomeomorphEquiv 2 e 3 (c • x) = c • modHomologyHomeomorphEquiv 2 e 3 x
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) c with rfl | rfl
    · simp only [zero_smul, map_zero]
    · simp only [one_smul]

theorem homeomorphEquiv_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : ModHomology 2 X 3) :
    homeomorphEquiv e x = modHomologyMap 2 (e : C(X, Y)) 3 x := rfl

def coordinates : ModHomology 2 Fiber 3 ≃ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  (homeomorphEquiv fiberDiffeomorph.symm.toHomeomorph).trans
    ProductThirdHomology.modSphereLinearEquivalence

theorem coordinates_apply (x : ModHomology 2 Fiber 3) : coordinates x =
    ProductThirdHomology.modSphereLinearEquivalence
      (modHomologyMap 2 (fiberDiffeomorph.symm.toHomeomorph : C(Fiber, Sphere 3 × Sphere 3)) 3 x) :=
  rfl

def leftSphere (r : Sphere 3) : C(Sphere 3, Fiber) := ⟨left r, (contMDiff_left r).continuous⟩

def rightSphere (q : Sphere 3) : C(Sphere 3, Fiber) := ⟨right q, (contMDiff_right q).continuous⟩

theorem inverse_leftSphere (r : Sphere 3) :
    (fiberDiffeomorph.symm.toHomeomorph : C(Fiber, Sphere 3 × Sphere 3)).comp (leftSphere r) =
      ProductThirdHomology.leftSection r := by
  apply ContinuousMap.ext
  intro q
  exact fiberDiffeomorph.symm_apply_apply (q, r)

theorem inverse_rightSphere (q : Sphere 3) :
    (fiberDiffeomorph.symm.toHomeomorph : C(Fiber, Sphere 3 × Sphere 3)).comp (rightSphere q) =
      ProductThirdHomology.rightSection q := by
  apply ContinuousMap.ext
  intro r
  exact fiberDiffeomorph.symm_apply_apply (q, r)

theorem map_sphereClass {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Sphere 3, X)) :
    modHomologyMap 2 f 3 (SixSphereMiddleParity.sphereClass g) =
      SixSphereMiddleParity.sphereClass (f.comp g) := by
  change modHomologyMap 2 f 3 (modHomologyMap 2 g 3 (unitSphereModTopClass 2 2)) =
    modHomologyMap 2 (f.comp g) 3 (unitSphereModTopClass 2 2)
  rw [modHomologyMap_comp]
  rfl

theorem coordinates_left :
    coordinates (SixSphereMiddleParity.sphereClass (leftSphere (spherePole 3))) = (1, 0) := by
  rw [coordinates_apply, map_sphereClass, inverse_leftSphere]
  change ProductThirdHomology.modSphereLinearEquivalence
    (modHomologyMap 2 (ProductThirdHomology.leftSection (spherePole 3)) 3
      (unitSphereModTopClass 2 2)) = _
  rw [ProductThirdHomology.modSphereLinearEquivalence_left,
    unitSphereModHomologyTopEquiv_topClass]

theorem coordinates_right :
    coordinates (SixSphereMiddleParity.sphereClass (rightSphere (spherePole 3))) = (0, 1) := by
  rw [coordinates_apply, map_sphereClass, inverse_rightSphere]
  change ProductThirdHomology.modSphereLinearEquivalence
    (modHomologyMap 2 (ProductThirdHomology.rightSection (spherePole 3)) 3
      (unitSphereModTopClass 2 2)) = _
  rw [ProductThirdHomology.modSphereLinearEquivalence_right,
    unitSphereModHomologyTopEquiv_topClass]

theorem coordinates_symm_left : coordinates.symm (1, 0) =
    SixSphereMiddleParity.sphereClass (leftSphere (spherePole 3)) := by
  apply coordinates.injective
  rw [LinearEquiv.apply_symm_apply, coordinates_left]

theorem coordinates_symm_right : coordinates.symm (0, 1) =
    SixSphereMiddleParity.sphereClass (rightSphere (spherePole 3)) := by
  apply coordinates.injective
  rw [LinearEquiv.apply_symm_apply, coordinates_right]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiberHomology
