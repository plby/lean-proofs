import Wikipedia.HopfProblem.SphereHomologySuspensionHigher
import Wikipedia.HopfProblem.SphereHomologyCircle

/-!
# The bottom and top integral homology of positive-dimensional spheres

The bottom marking is the actual singular augmentation. The top marking
starts with the original circle generator and iterates the genuine
latitude-homeomorphism and Mayer--Vietoris suspension maps. No orientation
agreement is asserted merely from the existence of this integral marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual degree-zero homology of each positive-dimensional sphere. -/
def unitSphereHomologyZeroEquiv (n : ℕ) :
    SingularHomology (UnitSphere (n + 1)) 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv (UnitSphere (n + 1))

@[simp] theorem unitSphereHomologyZeroEquiv_pointClass (n : ℕ)
    (x : UnitSphere (n + 1)) :
    unitSphereHomologyZeroEquiv n (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

/-- The top homology marking constructed by successive actual suspension maps. -/
def unitSphereHomologyTopEquiv : (n : ℕ) →
    SingularHomology (UnitSphere (n + 1)) (n + 1) ≃ₗ[ℤ] ℤ
  | 0 => sphereCircleHomologyOneEquiv
  | n + 1 => (unitSphereHomologySuspensionEquiv (n + 1) n).trans
      (unitSphereHomologyTopEquiv n)

@[simp] theorem unitSphereHomologyTopEquiv_zero :
    unitSphereHomologyTopEquiv 0 = sphereCircleHomologyOneEquiv := rfl

/-- The recursive marking uses the actual sphere suspension homomorphism. -/
theorem unitSphereHomologyTopEquiv_succ_apply (n : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (n + 2)) :
    unitSphereHomologyTopEquiv (n + 1) a =
      unitSphereHomologyTopEquiv n (unitSphereHomologySuspensionEquiv (n + 1) n a) := rfl

/-- An actual primitive integral top class, with the suspension marking just constructed. -/
def unitSphereTopClass (n : ℕ) : SingularHomology (UnitSphere (n + 1)) (n + 1) :=
  (unitSphereHomologyTopEquiv n).symm 1

@[simp] theorem unitSphereHomologyTopEquiv_topClass (n : ℕ) :
    unitSphereHomologyTopEquiv n (unitSphereTopClass n) = 1 :=
  (unitSphereHomologyTopEquiv n).apply_symm_apply 1

theorem unitSphereTopClass_ne_zero (n : ℕ) : unitSphereTopClass n ≠ 0 := by
  intro h
  have hh := congrArg (unitSphereHomologyTopEquiv n) h
  simp at hh

/-- The top classes are compatible with the literal singular suspension maps. -/
theorem unitSphereTopClass_suspension (n : ℕ) :
    unitSphereHomologySuspensionEquiv (n + 1) n (unitSphereTopClass (n + 1)) =
      unitSphereTopClass n := by
  apply (unitSphereHomologyTopEquiv n).injective
  change unitSphereHomologyTopEquiv (n + 1) (unitSphereTopClass (n + 1)) =
    unitSphereHomologyTopEquiv n (unitSphereTopClass n)
  simp

/-- Every top homology class is an integral multiple of the constructed primitive class. -/
theorem unitSphereTopClass_generates (n : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) (n + 1)) :
    ∃ k : ℤ, k • unitSphereTopClass n = a := by
  refine ⟨unitSphereHomologyTopEquiv n a, ?_⟩
  apply (unitSphereHomologyTopEquiv n).injective
  simp

end Wikipedia.HopfProblem.SphereHomology
