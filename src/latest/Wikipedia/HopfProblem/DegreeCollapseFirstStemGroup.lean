import Wikipedia.HopfProblem.DegreeCollapseFirstStemReduction
import Wikipedia.HopfProblem.DegreeCollapseOrthogonalComponents
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The actual first stable sphere groups have order two

The proved reflection-component calculation completes the original-map
Bott reduction. Every native pi_(k+4)(S^(k+3)) is cyclic of order two.
Its unique nonidentity class is compatible with the original suspensions.
No claim about the S5 attaching action is made by this computation.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FirstStemGroup

open NoExoticSixSphere GLOrthonormalization

def orthogonalFourComponents :
    π_ 0 (OrthogonalOperators 4) 1 ≃ Bool :=
  HomotopyGroup.pi0EquivZerothHomotopy.trans
    (OrthogonalComponents.componentsEquiv (spherePole 3))

def threeSphereClasses : π_ 4 (Sphere 3) (spherePole 3) ≃ Bool :=
  FirstStemReduction.threeSphereComparison.toEquiv.trans
    ((FirstStemReduction.orthogonalComparison 4 (by decide)).trans orthogonalFourComponents)

def sphereStages : (k : ℕ) →
    π_ 4 (Sphere 3) (spherePole 3) ≃*
      π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3))
  | 0 => MulEquiv.refl _
  | k + 1 => (sphereStages k).trans (FirstStemReduction.sphereStep k)

def sphereClasses (k : ℕ) :
    π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3)) ≃ Bool :=
  (sphereStages k).symm.toEquiv.trans threeSphereClasses

theorem card (k : ℕ) :
    Nat.card (π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3))) = 2 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_congr (sphereClasses k)

/-- This is an isomorphism of the original Mathlib cubical group. -/
def groupEquiv (k : ℕ) :
    π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3)) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (p := 2) (card k) (by simp)

def generator (k : ℕ) :
    π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3)) :=
  (groupEquiv k).symm (Multiplicative.ofAdd (1 : ZMod 2))

theorem generator_ne_one (k : ℕ) : generator k ≠ 1 := by
  intro h
  have he : Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    simpa only [generator, MulEquiv.apply_symm_apply, map_one] using congrArg (groupEquiv k) h
  exact one_ne_zero (congrArg Multiplicative.toAdd he)

theorem eq_one_or_generator (k : ℕ)
    (c : π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3))) :
    c = 1 ∨ c = generator k := by
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz ((groupEquiv k) c).toAdd with h | h
  · left
    apply (groupEquiv k).injective
    rw [map_one]
    exact congrArg Multiplicative.ofAdd h
  · right
    apply (groupEquiv k).injective
    change groupEquiv k c = groupEquiv k ((groupEquiv k).symm (Multiplicative.ofAdd 1))
    rw [MulEquiv.apply_symm_apply]
    exact congrArg Multiplicative.ofAdd h

theorem pow_two (k : ℕ)
    (c : π_ (k + 4) (Sphere (k + 3)) (spherePole (k + 3))) : c ^ 2 = 1 := by
  apply (groupEquiv k).injective
  rw [map_pow, map_one]
  exact (show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 from by decide) _

theorem generator_suspension (k : ℕ) :
    CubicalSphereSuspension.hom (k + 4) (k + 3) (generator k) = generator (k + 1) := by
  rcases eq_one_or_generator (k + 1)
    (CubicalSphereSuspension.hom (k + 4) (k + 3) (generator k)) with h | h
  · have he : generator k = 1 := (CubicalSphereSuspension.hom_injective (by omega))
      (h.trans (map_one (CubicalSphereSuspension.hom (k + 4) (k + 3))).symm)
    exact False.elim (generator_ne_one k he)
  · exact h

end Wikipedia.HopfProblem.DegreeCollapse.FirstStemGroup
