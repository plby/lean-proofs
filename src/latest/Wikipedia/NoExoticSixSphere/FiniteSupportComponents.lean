import Wikipedia.NoExoticSixSphere.FiniteSupportedCohomology

/-!
# Unique singleton components of an actual finite-supported cohomology class

Choose a decomposition supplied by proved surjectivity of the original
extension sum. Uniqueness on the actual support removes dependence on
that choice there and proves that each component is an original linear
map to singleton-supported cohomology.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- A family of actual singleton classes with the proved original extension sum. -/
def pointPieces (s : Finset X) (p : ℕ) (c : Cohomology (s : Set X) p) :
    ∀ x : X, Cohomology ({x} : Set X) p := (pointSum_surjective s p c).choose

theorem pointSum_pointPieces (s : Finset X) (p : ℕ) (c : Cohomology (s : Set X) p) :
    pointSum s p (pointPieces s p c) = c := (pointSum_surjective s p c).choose_spec

/-- Any actual decomposition gives the same component at a point of the support. -/
theorem pointPieces_eq_of_pointSum (s : Finset X) (p : ℕ) (c : Cohomology (s : Set X) p)
    (a : ∀ x : X, Cohomology ({x} : Set X) p) (ha : pointSum s p a = c)
    (x : X) (hx : x ∈ s) : pointPieces s p c x = a x :=
  pointSum_components_eq s p _ a ((pointSum_pointPieces s p c).trans ha.symm) x hx

/-- Taking an original singleton component is linear on the genuine finite-supported group. -/
def pointComponent (s : Finset X) (p : ℕ) (x : X) (hx : x ∈ s) :
    Cohomology (s : Set X) p →ₗ[ℤ] Cohomology ({x} : Set X) p :=
  Wikipedia.HopfProblem.ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun c := pointPieces s p c x
      map_zero' := pointPieces_eq_of_pointSum s p 0 (fun _ => 0)
        (by simp only [pointSum, map_zero, Finset.sum_const_zero]) x hx
      map_add' c d := pointPieces_eq_of_pointSum s p (c + d)
        (pointPieces s p c + pointPieces s p d)
        ((pointSum_add s p _ _).trans
          (congrArg₂ (fun a b => a + b)
            (pointSum_pointPieces s p c) (pointSum_pointPieces s p d))) x hx }

/-- The component of an actual finite extension sum is its original singleton summand. -/
theorem pointComponent_pointSum (s : Finset X) (p : ℕ) (x : X) (hx : x ∈ s)
    (a : ∀ y : X, Cohomology ({y} : Set X) p) : pointComponent s p x hx (pointSum s p a) = a x :=
  pointPieces_eq_of_pointSum s p (pointSum s p a) a rfl x hx

end NoExoticSixSphere.SupportedModTwoCohomology
