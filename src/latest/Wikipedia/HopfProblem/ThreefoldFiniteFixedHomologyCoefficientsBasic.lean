import Wikipedia.HopfProblem.ThreefoldFiniteFixedHomologyGeometry
import Wikipedia.HopfProblem.SphereHomologyCoefficientsBasic

/-!
# Native finite-coefficient homology transport for the actual fixed loci

The comparison uses the genuine singular homology functor with coefficient
object `ModuleCat.of ℤ (ZMod p)`, applied to the already proved fixed-locus
homeomorphisms.  Both fixed spaces remain the literal subtypes of the
original threefold.  These are equivalences of the actual homology objects,
not definitions by assigned ranks or abstract comparison groups.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology

open SphereHomologyCoefficients

/-- The actual roots fixed locus and actual Euclidean sphere have the same native
coefficient homology, through their genuine homeomorphism. -/
def rootsFixedModHomologyEquiv (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    ModHomology p (RootsFixedSpace m) k ≃ₗ[ℤ]
      ModHomology p (SphereHomology.UnitSphere 2) k :=
  modHomologyHomeomorphEquiv p (rootsFixedSphereHomeomorph m hm) k

/-- The finite subgroup of the genuine automorphism component uses its actual fixed subtype. -/
def identityRootsFixedModHomologyEquiv (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    ModHomology p (IdentityRootsFixedSpace m) k ≃ₗ[ℤ]
      ModHomology p (SphereHomology.UnitSphere 2) k :=
  modHomologyHomeomorphEquiv p (identityRootsFixedSphereHomeomorph m hm) k

/-- The roots comparison is exactly the native singular-homology map of the actual homeomorphism. -/
@[simp] theorem rootsFixedModHomologyEquiv_toLinearMap (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (rootsFixedModHomologyEquiv p m hm k).toLinearMap =
      modHomologyMap p (rootsFixedSphereHomeomorph m hm : C(_, _)) k := by
  apply LinearMap.ext
  intro a
  rfl

/-- The automorphism-subgroup comparison likewise retains its actual continuous map. -/
@[simp] theorem identityRootsFixedModHomologyEquiv_toLinearMap
    (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) :
    (identityRootsFixedModHomologyEquiv p m hm k).toLinearMap =
      modHomologyMap p (identityRootsFixedSphereHomeomorph m hm : C(_, _)) k := by
  apply LinearMap.ext
  intro a
  rfl

/-- The inverse map is induced by the actual inverse sphere parametrization of the fixed locus. -/
@[simp] theorem rootsFixedModHomologyEquiv_symm_apply
    (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) (a : ModHomology p (SphereHomology.UnitSphere 2) k) :
    (rootsFixedModHomologyEquiv p m hm k).symm a =
      modHomologyMap p ((rootsFixedSphereHomeomorph m hm).symm : C(_, _)) k a := rfl

/-- The inverse for the finite automorphism subgroup is also the native induced map. -/
@[simp] theorem identityRootsFixedModHomologyEquiv_symm_apply
    (p m : ℕ) (hm : 2 ≤ m) (k : ℕ) (a : ModHomology p (SphereHomology.UnitSphere 2) k) :
    (identityRootsFixedModHomologyEquiv p m hm k).symm a =
      modHomologyMap p ((identityRootsFixedSphereHomeomorph m hm).symm : C(_, _)) k a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology
