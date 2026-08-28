import Wikipedia.HopfProblem.ThreefoldSphereCohomologyEquivalenceBasic

/-!
# Native pairings for the actual sphere cohomology equivalence

The cohomology equivalence retains the original contravariant evaluation
square, and its inverse retains the inverse homology transport. The original
cusp-marked top cohomology class pulls back to a class evaluating to one on
the actual quotient-cube class. No identification of that class with a
separately marked or oriented sphere generator is required.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence

open SingularMayerVietoris SingularCohomologyFree
open SphereHomologyEquivalence

/-- The equivalence is exactly the original cohomological pullback under evaluation. -/
theorem cohomologyEquiv_evaluation (x : Space) (n : ℕ)
    (a : SingularCohomology Space n) (b : SingularHomology SixSphere n) :
    singularEvaluation SixSphere n (cohomologyEquiv x n a) b =
      singularEvaluation Space n a (singularHomologyMap (sphereMap x) n b) :=
  singularEvaluation_naturality (sphereMap x) n a b

/-- The original evaluation square commutes as an equality of linear maps. -/
theorem evaluation_comp_pullback (x : Space) (n : ℕ) :
    (singularEvaluation SixSphere n).comp (singularCohomologyPullback (sphereMap x) n) =
      (singularHomologyMap (sphereMap x) n).dualMap.comp (singularEvaluation Space n) := by
  ext a b
  exact singularEvaluation_naturality (sphereMap x) n a b

/-- Native cochain-cycle evaluation is preserved by the mutually inverse transports. -/
theorem cohomologyEquiv_pairing (x : Space) (n : ℕ)
    (a : SingularCohomology Space n) (b : SingularHomology Space n) :
    singularEvaluation SixSphere n (cohomologyEquiv x n a)
        ((homologyEquiv x n).symm b) = singularEvaluation Space n a b := by
  rw [cohomologyEquiv_evaluation]
  change singularEvaluation Space n a ((homologyEquiv x n) ((homologyEquiv x n).symm b)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The inverse equivalence has the explicitly proved inverse evaluation formula. -/
theorem cohomologyEquiv_symm_evaluation (x : Space) (n : ℕ)
    (a : SingularCohomology SixSphere n) (b : SingularHomology Space n) :
    singularEvaluation Space n ((cohomologyEquiv x n).symm a) b =
      singularEvaluation SixSphere n a ((homologyEquiv x n).symm b) :=
  cohomologyInverse_evaluation x n a b

theorem cohomologyEquiv_symm_pairing (x : Space) (n : ℕ)
    (a : SingularCohomology SixSphere n) (b : SingularHomology SixSphere n) :
    singularEvaluation Space n ((cohomologyEquiv x n).symm a)
        (singularHomologyMap (sphereMap x) n b) = singularEvaluation SixSphere n a b := by
  rw [cohomologyEquiv_symm_evaluation]
  change singularEvaluation SixSphere n a ((homologyEquiv x n).symm ((homologyEquiv x n) b)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The original native cohomology objects are isomorphic by the actual pullback. -/
def cohomologyIso (x : Space) (n : ℕ) :
    SingularCohomology Space n ≅ SingularCohomology SixSphere n :=
  (cohomologyEquiv x n).toModuleIso

/-- The categorical isomorphism has the original cochain-complex homology map as its forward map. -/
@[simp] theorem cohomologyIso_hom (x : Space) (n : ℕ) :
    (cohomologyIso x n).hom =
      HomologicalComplex.homologyMap (singularPullback (sphereMap x)) n := rfl

/-- Its inverse is the constructed evaluation-dual inverse, not an unrelated comparison. -/
@[simp] theorem cohomologyIso_inv (x : Space) (n : ℕ) :
    (cohomologyIso x n).inv = ModuleCat.ofHom (cohomologyInverse x n) := rfl

/-- The pullback of the original cusp-marked class pairs positively with the actual sphere cube. -/
@[simp] theorem topCohomologyClass_sourceCubeClass_pairing (x : Space) :
    singularEvaluation SixSphere 6
        (singularCohomologyPullback (sphereMap x) 6 Homology.TopCohomology.topCohomologyClass)
        sourceCubeClass = 1 := by
  rw [singularEvaluation_naturality, sphereMap_sourceCubeClass,
    Homology.TopCohomology.topCohomologyClass_pairing]

/-- One genuine based continuous map induces both original integral (co)homology isomorphisms. -/
theorem exists_based_homology_cohomology_equivalence (x : Space) :
    ∃ f : C(SixSphere, Space), f SixSphereCube.sphereBasePoint = x ∧
      (∀ n : ℕ, Function.Bijective (singularHomologyMap f n)) ∧
      ∀ n : ℕ, Function.Bijective (singularCohomologyPullback f n) :=
  ⟨sphereMap x, sphereMap_basePoint x, homologyMap_bijective x,
    cohomologyPullback_bijective x⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.SphereCohomologyEquivalence
