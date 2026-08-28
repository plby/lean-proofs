import Wikipedia.HopfProblem.SphereHomologyCircleComparison
import Wikipedia.HopfProblem.SphereHomologyCircleNative

/-!
# Integral singular homology of the literal Euclidean unit circle

The real linear isometry to `ℂ`, restricted to the actual unit spheres,
induces the native singular-homology comparison used in every degree.
The previously proved circle calculation gives `H₀ = ℤ`, `H₁ = ℤ`, and
zero higher homology for the original sphere in `EuclideanSpace ℝ (Fin 2)`.
No sphere-homology or suspension formula is an assumption.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Native degree-zero homology of the original Euclidean unit sphere. -/
def sphereCircleHomologyZeroEquiv :
    SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 0 ≃ₗ[ℤ] ℤ :=
  (sphereCircleHomologyEquiv 0).trans unitCircleHomologyZeroEquiv

/-- The transported marking is exactly the original singular augmentation. -/
theorem sphereCircleHomologyZeroEquiv_eq_connectedHomologyZeroEquiv :
    sphereCircleHomologyZeroEquiv =
      connectedHomologyZeroEquiv (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
  apply LinearEquiv.ext
  intro a
  exact connectedHomologyZeroEquiv_natural
    (sphereCircleHomeomorph :
      C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, _root_.Circle)) a

/-- Each actual point of the Euclidean unit sphere represents the positive degree-zero generator. -/
@[simp] theorem sphereCircleHomologyZeroEquiv_pointClass
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereCircleHomologyZeroEquiv (pointClass x) = 1 := by
  rw [sphereCircleHomologyZeroEquiv_eq_connectedHomologyZeroEquiv]
  exact connectedHomologyZeroEquiv_pointClass x

/-- The inverse degree-zero marking is the genuine singular class of any actual point. -/
theorem sphereCircleHomologyZeroEquiv_symm_one
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereCircleHomologyZeroEquiv.symm 1 = pointClass x := by
  rw [sphereCircleHomologyZeroEquiv_eq_connectedHomologyZeroEquiv]
  exact connectedHomologyZeroEquiv_symm_one x

/-- Native degree-one homology of the original Euclidean unit sphere. -/
def sphereCircleHomologyOneEquiv :
    SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 ≃ₗ[ℤ] ℤ :=
  (sphereCircleHomologyEquiv 1).trans unitCircleHomologyOneEquiv

theorem sphereCircleHomologyOneEquiv_apply
    (a : SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 1) :
    sphereCircleHomologyOneEquiv a = unitCircleHomologyOneEquiv
      (singularHomologyMap (sphereCircleHomeomorph :
        C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, _root_.Circle)) 1 a) := rfl

/-- The inverse degree-one marking is the actual map induced by the inverse sphere homeomorphism. -/
theorem sphereCircleHomologyOneEquiv_symm_apply (k : ℤ) :
    sphereCircleHomologyOneEquiv.symm k =
      singularHomologyMap (sphereCircleHomeomorph.symm :
        C(_root_.Circle, Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) 1
          (unitCircleHomologyOneEquiv.symm k) := rfl

/-- All actual homology groups of this sphere above degree one vanish. -/
theorem sphereCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (sphereCircleHomologyEquiv (n + 2)).injective.subsingleton

theorem sphereCircle_homology_isZero (n : ℕ) :
    IsZero (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (n + 2)) := by
  let := sphereCircle_homology_subsingleton n
  exact ModuleCat.isZero_of_subsingleton _

/-- The higher native homology groups are explicitly equivalent to the zero free module. -/
def sphereCircleHomologyHigherEquivZero (n : ℕ) :
    SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (n + 2) ≃ₗ[ℤ]
      (Fin 0 → ℤ) :=
  (sphereCircleHomologyEquiv (n + 2)).trans (unitCircleHomologyHigherEquivZero n)

/-- Freeness of every actual integral singular homology group of the literal sphere. -/
instance sphereCircle_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) := by
  let := unitCircle_homology_free n
  exact Module.Free.of_equiv (sphereCircleHomologyEquiv n).symm

/-- Every actual integral singular homology group of the literal sphere is finitely generated. -/
instance sphereCircle_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) := by
  let := unitCircle_homology_finite n
  exact Module.Finite.of_surjective (sphereCircleHomologyEquiv n).symm.toLinearMap
    (sphereCircleHomologyEquiv n).symm.surjective

/-- The all-degree rank is one in degrees zero and one, and zero otherwise. -/
theorem sphereCircle_homology_finrank (n : ℕ) :
    Module.finrank ℤ
      (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) =
        Nat.choose 1 n := by
  cases n with
  | zero => simpa using sphereCircleHomologyZeroEquiv.finrank_eq
  | succ n =>
    cases n with
    | zero => simpa using sphereCircleHomologyOneEquiv.finrank_eq
    | succ n =>
      let := sphereCircle_homology_subsingleton n
      rw [Module.finrank_zero_of_subsingleton,
        Nat.choose_eq_zero_of_lt (by omega : 1 < n + 2)]

/-- The complete native integral homology calculation of the original Euclidean unit circle. -/
theorem sphereCircle_homology :
    Nonempty (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 ≃ₗ[ℤ] ℤ) ∧
      ∀ n, Subsingleton
        (SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (n + 2)) :=
  ⟨⟨sphereCircleHomologyZeroEquiv⟩, ⟨sphereCircleHomologyOneEquiv⟩,
    sphereCircle_homology_subsingleton⟩

end Wikipedia.HopfProblem.SphereHomology
