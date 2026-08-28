import Wikipedia.HopfProblem.DegreeCollapseSecondStemSuspension
import Wikipedia.NoExoticSixSphere.JamesSphereThreeRetraction

/-!
# The original second stable stem and its marked first-stem square

Quaternionic James evaluation makes the first three-sphere suspension
injective; Freudenthal makes it surjective and gives every later step.
The actual product suspension preserves composition. The transported
nonzero class is therefore a composite of the original two first-stem
generators in every dimension, and every second-stem class has square one.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SecondStemGroup

open NoExoticSixSphere SmoothCube CubicalSphereSuspension SphereLiftFamily JamesSphere

def step : (k : ℕ) → π_ (k + 5) (Sphere (k + 3)) (spherePole (k + 3)) ≃*
    π_ (k + 6) (Sphere (k + 4)) (spherePole (k + 4))
  | 0 => MulEquiv.ofBijective (hom 5 3)
      ⟨ThreeRetraction.suspension_injective 5, hom_surjective (by decide)⟩
  | k + 1 => MulEquiv.ofBijective (hom (k + 6) (k + 4)) (hom_bijective (by omega))

theorem step_apply (k : ℕ) (a : π_ (k + 5) (Sphere (k + 3)) (spherePole (k + 3))) :
    step k a = hom (k + 5) (k + 3) a := by
  cases k <;> rfl

def stages : (k : ℕ) → π_ 5 (Sphere 3) (spherePole 3) ≃*
    π_ (k + 5) (Sphere (k + 3)) (spherePole (k + 3))
  | 0 => MulEquiv.refl _
  | k + 1 => (stages k).trans (step k)

def groupEquiv (k : ℕ) :
    π_ (k + 5) (Sphere (k + 3)) (spherePole (k + 3)) ≃* Multiplicative (ZMod 2) :=
  (stages k).symm.trans SecondStemReduction.groupEquiv

theorem pow_two (k : ℕ) (c : π_ (k + 5) (Sphere (k + 3)) (spherePole (k + 3))) :
    c ^ 2 = 1 := by
  apply (groupEquiv k).injective
  rw [map_pow, map_one]
  exact (show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 from by decide) _

def doubleMap : (k : ℕ) → SphereComposition.Based (k + 5) (k + 3)
  | 0 => SecondStemSuspension.doubleMap
  | k + 1 => productBasedMap (doubleMap k)

theorem doubleMap_class (k : ℕ) :
    sphereClass (doubleMap k) = stages k (sphereClass SecondStemSuspension.doubleMap) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change sphereClass (productBasedMap (doubleMap k)) =
      step k (stages k (sphereClass SecondStemSuspension.doubleMap))
    rw [← hom_sphereClass, ih, step_apply]

theorem doubleMap_ne_one (k : ℕ) : sphereClass (doubleMap k) ≠ 1 := by
  intro h
  apply SecondStemSuspension.doubleMap_ne_one
  apply (stages k).injective
  exact (doubleMap_class k).symm.trans (h.trans (map_one (stages k)).symm)

def leftMap : (k : ℕ) → SphereComposition.Based (k + 4) (k + 3)
  | 0 => productBasedMap BasedCircleHopf.projection
  | k + 1 => productBasedMap (leftMap k)

def rightMap : (k : ℕ) → SphereComposition.Based (k + 5) (k + 4)
  | 0 => productBasedMap SecondStemSuspension.firstMap
  | k + 1 => productBasedMap (rightMap k)

theorem doubleMap_eq_compose (k : ℕ) : doubleMap k = compose (leftMap k) (rightMap k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change productBasedMap (doubleMap k) =
      compose (productBasedMap (leftMap k)) (productBasedMap (rightMap k))
    rw [ih, SecondStemSuspension.product_compose]

theorem leftMap_class (k : ℕ) : sphereClass (leftMap k) = FirstStemGroup.generator k := by
  induction k with
  | zero => exact SecondStemSuspension.projection_suspension_class
  | succ k ih =>
    change sphereClass (productBasedMap (leftMap k)) = FirstStemGroup.generator (k + 1)
    rw [← hom_sphereClass, ih, FirstStemGroup.generator_suspension]

theorem rightMap_class (k : ℕ) :
    sphereClass (rightMap k) = FirstStemGroup.generator (k + 1) := by
  induction k with
  | zero => exact SecondStemSuspension.firstMap_suspension_class
  | succ k ih =>
    change sphereClass (productBasedMap (rightMap k)) = FirstStemGroup.generator (k + 1 + 1)
    rw [← hom_sphereClass, ih, FirstStemGroup.generator_suspension]

theorem firstStem_composite_ne_one (k : ℕ)
    (f : SphereComposition.Based (k + 4) (k + 3))
    (g : SphereComposition.Based (k + 5) (k + 4))
    (hf : sphereClass f = FirstStemGroup.generator k)
    (hg : sphereClass g = FirstStemGroup.generator (k + 1)) :
    sphereClass (compose f g) ≠ 1 := by
  have h₁ : sphereClass (compose f g) = sphereClass (compose (leftMap k) g) :=
    GroupSpherePrecomposition.compose_class_congr (hf.trans (leftMap_class k).symm) g
  have h₂ : sphereClass (compose (leftMap k) g) =
      sphereClass (compose (leftMap k) (rightMap k)) :=
    congrArg (HigherHomotopy.map (leftMap k).val (leftMap k).property)
      (hg.trans (rightMap_class k).symm)
  have he : sphereClass (compose f g) = sphereClass (doubleMap k) :=
    (h₁.trans h₂).trans (congrArg sphereClass (doubleMap_eq_compose k)).symm
  exact fun h ↦ doubleMap_ne_one k (he.symm.trans h)

end Wikipedia.HopfProblem.DegreeCollapse.SecondStemGroup
