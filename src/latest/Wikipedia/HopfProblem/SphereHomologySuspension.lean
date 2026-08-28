import Wikipedia.HopfProblem.SphereHomologySuspensionFibres
import Wikipedia.HopfProblem.SphereHomologySuspensionSurjective
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology

/-!
# The actual suspension is the next Euclidean unit sphere

The latitude map descends through precisely the suspension equivalence
relation. Its proved surjectivity and exact fibres give a continuous
bijection from the compact suspension to the original Hausdorff sphere.
This constructs the homeomorphism, without a sphere-recognition hypothesis.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SphereHomology

open CuspCentralHomology

/-- The original latitude formula descended through the actual cylinder quotient. -/
def suspensionSphereMap (n : ℕ) : Suspension (UnitSphere n) → UnitSphere (n + 1) :=
  Quotient.lift (fun p => Latitude.point n p.1 p.2)
    (fun p q h => (Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mpr h)

@[simp] theorem suspensionSphereMap_mk (n : ℕ) (t : unitInterval) (x : UnitSphere n) :
    suspensionSphereMap n (Suspension.mk t x) = Latitude.point n t x := rfl

@[continuity, fun_prop] theorem suspensionSphereMap_continuous (n : ℕ) :
    Continuous (suspensionSphereMap n) :=
  Suspension.isQuotientMap_mk.continuous_iff.mpr (Latitude.point_continuous n)

theorem suspensionSphereMap_injective (n : ℕ) :
    Function.Injective (suspensionSphereMap n) := by
  intro a b
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      intro h
      exact Quotient.sound ((Latitude.point_eq_iff n p.1 q.1 p.2 q.2).mp h)

theorem suspensionSphereMap_surjective (n : ℕ) :
    Function.Surjective (suspensionSphereMap n) := by
  intro y
  obtain ⟨⟨t, x⟩, h⟩ := Latitude.point_surjective n y
  exact ⟨Suspension.mk t x, h⟩

/-- The genuine suspension of the standard `n`-sphere is the standard `(n+1)`-sphere. -/
def suspensionSphereHomeomorph (n : ℕ) :
    Suspension (UnitSphere n) ≃ₜ UnitSphere (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (suspensionSphereMap n)
      ⟨suspensionSphereMap_injective n, suspensionSphereMap_surjective n⟩)
    (suspensionSphereMap_continuous n)

@[simp] theorem suspensionSphereHomeomorph_apply (n : ℕ)
    (a : Suspension (UnitSphere n)) :
    suspensionSphereHomeomorph n a = suspensionSphereMap n a := rfl

@[simp] theorem suspensionSphereHomeomorph_mk (n : ℕ)
    (t : unitInterval) (x : UnitSphere n) :
    suspensionSphereHomeomorph n (Suspension.mk t x) = Latitude.point n t x := rfl

/-- Every positive-dimensional Euclidean unit sphere is path connected. -/
instance unitSphere_pathConnectedSpace (n : ℕ) : PathConnectedSpace (UnitSphere (n + 1)) :=
  (suspensionSphereHomeomorph n).surjective.pathConnectedSpace
    (suspensionSphereHomeomorph n).continuous

end Wikipedia.HopfProblem.SphereHomology
