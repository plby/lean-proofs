import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups

/-!
# Integral homology of the native gamma-zero fibre

The literal inclusion of the gamma-zero subtorus is split injective on actual
singular homology in every degree. Its native three-circle homeomorphism also
computes these groups and proves their vanishing above degree three.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open Elliptic SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual integral singular-homology map of the subtorus inclusion. -/
def fibreHomologyInclusion (n : ℕ) :
    SingularHomology Fibre n →ₗ[ℤ] SingularHomology RealTorus₄ n :=
  singularHomologyMap fibreInclusion n

/-- The actual integral singular-homology map of the coordinate retraction. -/
def fibreHomologyRetraction (n : ℕ) :
    SingularHomology RealTorus₄ n →ₗ[ℤ] SingularHomology Fibre n :=
  singularHomologyMap fibreRetraction n

/-- Functoriality carries the literal inclusion-retraction identity to homology. -/
theorem fibreHomologyRetraction_comp_inclusion (n : ℕ) :
    (fibreHomologyRetraction n).comp (fibreHomologyInclusion n) = LinearMap.id := by
  change (singularHomologyMap fibreRetraction n).comp
    (singularHomologyMap fibreInclusion n) = LinearMap.id
  rw [← singularHomologyMap_comp, fibreRetraction_comp_inclusion, singularHomologyMap_id]

@[simp] theorem fibreHomologyRetraction_inclusion (n : ℕ)
    (a : SingularHomology Fibre n) :
    fibreHomologyRetraction n (fibreHomologyInclusion n a) = a :=
  LinearMap.congr_fun (fibreHomologyRetraction_comp_inclusion n) a

/-- The original subtorus inclusion is injective on integral homology in every degree. -/
theorem fibreHomologyInclusion_injective (n : ℕ) :
    Function.Injective (fibreHomologyInclusion n) :=
  (show Function.LeftInverse (fibreHomologyRetraction n) (fibreHomologyInclusion n)
    from fibreHomologyRetraction_inclusion n).injective

/-- Homology equivalence induced by the native three-circle fibre coordinates. -/
def fibreTorusHomologyEquiv (n : ℕ) :
    SingularHomology Fibre n ≃ₗ[ℤ] SingularHomology (ProductTorus 3) n :=
  homeomorphHomologyEquiv fibreHomeomorph n

@[simp] theorem fibreTorusHomologyEquiv_toLinearMap (n : ℕ) :
    (fibreTorusHomologyEquiv n).toLinearMap =
      singularHomologyMap (fibreHomeomorph : C(Fibre, ProductTorus 3)) n := rfl

/-- The genuine integral fibre homology, in the existing binomial torus coordinates. -/
def fibreHomologyEquiv (n : ℕ) :
    SingularHomology Fibre n ≃ₗ[ℤ] binomialModule 3 n :=
  (fibreTorusHomologyEquiv n).trans (productTorusHomologyEquiv 3 n)

theorem fibreHomology_free (n : ℕ) : Module.Free ℤ (SingularHomology Fibre n) :=
  Module.Free.of_equiv (fibreHomologyEquiv n).symm

theorem fibreHomology_finite (n : ℕ) : Module.Finite ℤ (SingularHomology Fibre n) :=
  Module.Finite.of_surjective (fibreHomologyEquiv n).symm.toLinearMap
    (fibreHomologyEquiv n).symm.surjective

theorem fibreHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology Fibre n) = Nat.choose 3 n := by
  rw [(fibreHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 3 n

/-- The actual integral fibre homology vanishes above its three circle factors. -/
theorem fibreHomology_subsingleton_of_lt (n : ℕ) (h : 3 < n) :
    Subsingleton (SingularHomology Fibre n) := by
  let := productTorus_homology_subsingleton_of_lt h
  exact (fibreTorusHomologyEquiv n).injective.subsingleton

/-- In particular the gamma-zero fibre has zero fourth singular homology. -/
theorem fibreH4_subsingleton : Subsingleton (SingularHomology Fibre 4) :=
  fibreHomology_subsingleton_of_lt 4 (by decide)

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
