import Wikipedia.HopfProblem.ThreefoldFiniteFixedHomologyGeometry
import Wikipedia.HopfProblem.SphereHomologyVanishing

/-!
# Actual integral singular homology of the finite-subgroup fixed sets

The proved homeomorphisms of the literal fixed subsets with the Euclidean
two-sphere induce these all-degree integral singular homology equivalences.
In degrees zero and two, compose with the actual sphere augmentation and
the already constructed suspension marking. The latter is an integral
marking only; no additional orientation agreement is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

/-- Integral homology of the actual roots-of-unity fixed subset, transported
by its genuine sphere homeomorphism in every degree. -/
def rootsFixedIntegralHomologyEquiv (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    SingularHomology (RootsFixedSpace n) k ≃ₗ[ℤ] SingularHomology (UnitSphere 2) k :=
  homeomorphHomologyEquiv (rootsFixedSphereHomeomorph n hn) k

/-- The corresponding equivalence for the fixed set of actual identity-component automorphisms. -/
def identityRootsFixedIntegralHomologyEquiv (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    SingularHomology (IdentityRootsFixedSpace n) k ≃ₗ[ℤ]
      SingularHomology (UnitSphere 2) k :=
  homeomorphHomologyEquiv (identityRootsFixedSphereHomeomorph n hn) k

/-- The underlying map is the literal singular homology map of the geometric homeomorphism. -/
@[simp] theorem rootsFixedIntegralHomologyEquiv_toLinearMap (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (rootsFixedIntegralHomologyEquiv n hn k).toLinearMap =
      singularHomologyMap
        (rootsFixedSphereHomeomorph n hn : C(RootsFixedSpace n, UnitSphere 2)) k := rfl

/-- The identity-component marking also retains its literal induced singular map. -/
@[simp] theorem identityRootsFixedIntegralHomologyEquiv_toLinearMap
    (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (identityRootsFixedIntegralHomologyEquiv n hn k).toLinearMap =
      singularHomologyMap
        (identityRootsFixedSphereHomeomorph n hn : C(IdentityRootsFixedSpace n, UnitSphere 2)) k :=
  rfl

/-- Every other actual integral homology group of the roots fixed set vanishes. -/
theorem rootsFixedIntegralHomology_subsingleton (n : ℕ) (hn : 2 ≤ n) (k : ℕ)
    (hk : k ≠ 0) (hk2 : k ≠ 2) :
    Subsingleton (SingularHomology (RootsFixedSpace n) k) := by
  let := unitSphere_homology_subsingleton 1 k hk hk2
  exact (rootsFixedIntegralHomologyEquiv n hn k).injective.subsingleton

/-- The genuine identity-component fixed set has the same all-other-degree vanishing. -/
theorem identityRootsFixedIntegralHomology_subsingleton (n : ℕ) (hn : 2 ≤ n) (k : ℕ)
    (hk : k ≠ 0) (hk2 : k ≠ 2) :
    Subsingleton (SingularHomology (IdentityRootsFixedSpace n) k) := by
  let := unitSphere_homology_subsingleton 1 k hk hk2
  exact (identityRootsFixedIntegralHomologyEquiv n hn k).injective.subsingleton

/-- The actual degree-zero roots fixed-set homology is the integers,
with its positive augmentation. -/
def rootsFixedIntegralHomologyZeroEquiv (n : ℕ) (hn : 2 ≤ n) :
    SingularHomology (RootsFixedSpace n) 0 ≃ₗ[ℤ] ℤ :=
  (rootsFixedIntegralHomologyEquiv n hn 0).trans (unitSphereHomologyZeroEquiv 1)

/-- The actual identity-roots fixed-set degree-zero homology is the integers. -/
def identityRootsFixedIntegralHomologyZeroEquiv (n : ℕ) (hn : 2 ≤ n) :
    SingularHomology (IdentityRootsFixedSpace n) 0 ≃ₗ[ℤ] ℤ :=
  (identityRootsFixedIntegralHomologyEquiv n hn 0).trans (unitSphereHomologyZeroEquiv 1)

/-- An integral degree-two marking obtained through the genuine fixed-set sphere homeomorphism. -/
def rootsFixedIntegralHomologyTwoEquiv (n : ℕ) (hn : 2 ≤ n) :
    SingularHomology (RootsFixedSpace n) 2 ≃ₗ[ℤ] ℤ :=
  (rootsFixedIntegralHomologyEquiv n hn 2).trans (unitSphereHomologyTopEquiv 1)

/-- The corresponding actual degree-two integral marking for the identity-roots fixed set. -/
def identityRootsFixedIntegralHomologyTwoEquiv (n : ℕ) (hn : 2 ≤ n) :
    SingularHomology (IdentityRootsFixedSpace n) 2 ≃ₗ[ℤ] ℤ :=
  (identityRootsFixedIntegralHomologyEquiv n hn 2).trans (unitSphereHomologyTopEquiv 1)

/-- Every actual point of the roots fixed set has positive augmentation one. -/
@[simp] theorem rootsFixedIntegralHomologyZeroEquiv_pointClass
    (n : ℕ) (hn : 2 ≤ n) (x : RootsFixedSpace n) :
    rootsFixedIntegralHomologyZeroEquiv n hn (pointClass x) = 1 := by
  change unitSphereHomologyZeroEquiv 1
    (singularHomologyMap
      (rootsFixedSphereHomeomorph n hn : C(RootsFixedSpace n, UnitSphere 2)) 0
      (pointClass x)) = 1
  rw [singularHomologyMap_pointClass, unitSphereHomologyZeroEquiv_pointClass]

/-- The augmentation is likewise fixed on the actual identity-roots fixed-set points. -/
@[simp] theorem identityRootsFixedIntegralHomologyZeroEquiv_pointClass
    (n : ℕ) (hn : 2 ≤ n) (x : IdentityRootsFixedSpace n) :
    identityRootsFixedIntegralHomologyZeroEquiv n hn (pointClass x) = 1 := by
  change unitSphereHomologyZeroEquiv 1
    (singularHomologyMap
      (identityRootsFixedSphereHomeomorph n hn : C(IdentityRootsFixedSpace n, UnitSphere 2)) 0
      (pointClass x)) = 1
  rw [singularHomologyMap_pointClass, unitSphereHomologyZeroEquiv_pointClass]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology
