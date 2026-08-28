import Wikipedia.NoExoticSixSphere.LocalSingularHomology
import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Wikipedia.HopfProblem.SphereHomologyVanishing
import Mathlib.Analysis.Convex.Contractible

/-!
# Local integral homology of a Euclidean model

The actual relative connecting homomorphism, followed by radial deformation
of the punctured vector space, computes local homology in degrees at least
two. In the top degree of a finite-dimensional model of dimension at least
two, the existing sphere calculation gives a primitive local class.
This class uses the chosen sphere parametrization; compatibility under
oriented chart transitions and a global fundamental class are not asserted.
-/

noncomputable section

open CategoryTheory Metric
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X]

/-- The actual connecting map is an isomorphism in positive target degrees
when the ambient space is contractible. -/
def contractibleConnectingEquiv [ContractibleSpace X] (U : Set X) (n : ℕ) (hn : n ≠ 0) :
    Homology U (n + 1) ≃ₗ[ℤ] SingularHomology U n :=
  ((sequence_shortExact U).δIso (n + 1) n (by simp)
    (contractible_homology_isZero X (n + 1) (Nat.succ_ne_zero n))
    (contractible_homology_isZero X n hn)).toLinearEquiv

theorem contractibleConnectingEquiv_toLinearMap [ContractibleSpace X]
    (U : Set X) (n : ℕ) (hn : n ≠ 0) :
    (contractibleConnectingEquiv U n hn).toLinearMap = connecting U n := rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The punctured Euclidean model is replaced by its actual radial deformation. -/
def localZeroSphereEquiv (n : ℕ) (hn : n ≠ 0) :
    LocalHomology (0 : E) (n + 1) ≃ₗ[ℤ] SingularHomology (sphere (0 : E) 1) n :=
  (contractibleConnectingEquiv ({(0 : E)}ᶜ : Set E) n hn).trans
    (homotopyEquivHomologyEquiv
      (PuncturedRadial.sphereHomotopyEquiv (N := E) 1 zero_lt_one).symm n)

/-- The computation retains the original connecting map and radial map. -/
theorem localZeroSphereEquiv_toLinearMap (n : ℕ) (hn : n ≠ 0) :
    (localZeroSphereEquiv E n hn).toLinearMap =
      (singularHomologyMap (PuncturedRadial.toSphere (N := E)) n).comp
        (connecting ({(0 : E)}ᶜ : Set E) n) := rfl

end NoExoticSixSphere.RelativeSingularHomology

namespace NoExoticSixSphere.RelativeSingularHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

/-- The actual top local homology is infinite cyclic, with an explicit sphere-based marking. -/
def localTopEquiv : LocalHomology (0 : E) (n + 2) ≃ₗ[ℤ] ℤ :=
  ((localZeroSphereEquiv E (n + 1) (Nat.succ_ne_zero n)).trans
    (homeomorphHomologyEquiv
      (SphereCoordinates.standardParametrization E (n + 1)).toHomeomorph (n + 1)).symm).trans
    (SphereHomology.unitSphereHomologyTopEquiv n)

/-- A primitive class in the original local singular homology module. -/
def localTopClass : LocalHomology (0 : E) (n + 2) := (localTopEquiv E n).symm 1

theorem localTopEquiv_class : localTopEquiv E n (localTopClass E n) = 1 :=
  (localTopEquiv E n).apply_symm_apply 1

theorem localTopClass_ne_zero : localTopClass E n ≠ 0 := by
  intro h
  have he := congrArg (localTopEquiv E n) h
  rw [localTopEquiv_class, map_zero] at he
  exact one_ne_zero he

theorem localTopClass_generates (a : LocalHomology (0 : E) (n + 2)) :
    ∃ k : ℤ, k • localTopClass E n = a := by
  refine ⟨localTopEquiv E n a, ?_⟩
  apply (localTopEquiv E n).injective
  simp only [map_zsmul, localTopEquiv_class, zsmul_eq_mul, Int.cast_id, mul_one]

/-- Other local homology groups of degree at least two vanish. -/
theorem localHomology_subsingleton (k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n + 1) :
    Subsingleton (LocalHomology (0 : E) (k + 1)) := by
  let := SphereHomology.unitSphere_homology_subsingleton n k hk hkn
  let e := (localZeroSphereEquiv E k hk).trans
    (homeomorphHomologyEquiv
      (SphereCoordinates.standardParametrization E (n + 1)).toHomeomorph k).symm
  exact e.injective.subsingleton

end NoExoticSixSphere.RelativeSingularHomology
