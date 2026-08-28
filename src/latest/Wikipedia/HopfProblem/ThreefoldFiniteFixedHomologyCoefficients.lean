import Wikipedia.HopfProblem.ThreefoldFiniteFixedHomologyCoefficientsBasic
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# Finite-coefficient homology of the original finite fixed loci

The genuine fixed-locus homeomorphisms transport the native sphere
coefficient calculation.  The actual homology groups of each original
fixed subtype are `ℤ/p` in degrees zero and two and vanish in every other
degree.  The coefficient modulus need only be nonzero, so these results
in particular apply to every prime modulus.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology

open SphereHomologyCoefficients

/-- Actual degree-zero singular homology of the roots fixed subtype with coefficients `ℤ/p`. -/
def rootsFixedModHomologyZeroEquiv (p : ℕ) (hp : p ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    ModHomology p (RootsFixedSpace m) 0 ≃ₗ[ℤ] ZMod p :=
  (rootsFixedModHomologyEquiv p m hm 0).trans (unitSphereModHomologyZeroEquiv p hp 1)

/-- Actual degree-two singular homology of the roots fixed subtype with coefficients `ℤ/p`. -/
def rootsFixedModHomologyTwoEquiv (p : ℕ) (hp : p ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    ModHomology p (RootsFixedSpace m) 2 ≃ₗ[ℤ] ZMod p :=
  (rootsFixedModHomologyEquiv p m hm 2).trans (unitSphereModHomologyTopEquiv p hp 1)

/-- Every other native coefficient homology group of the original roots fixed set vanishes. -/
theorem rootsFixedModHomology_subsingleton (p : ℕ) (hp : p ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≠ 0) (hk2 : k ≠ 2) :
    Subsingleton (ModHomology p (RootsFixedSpace m) k) := by
  let := unitSphereModHomology_subsingleton p hp 1 k hk hk2
  exact (rootsFixedModHomologyEquiv p m hm k).injective.subsingleton

/-- Vanishing as a zero object of the actual integral-module-valued coefficient functor. -/
theorem rootsFixedModHomology_isZero (p : ℕ) (hp : p ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≠ 0) (hk2 : k ≠ 2) :
    IsZero (ModHomology p (RootsFixedSpace m) k) := by
  let := rootsFixedModHomology_subsingleton p hp m hm k hk hk2
  exact ModuleCat.isZero_of_subsingleton _

/-- Actual degree-zero homology of the fixed set of the genuine finite automorphism subgroup. -/
def identityRootsFixedModHomologyZeroEquiv (p : ℕ) (hp : p ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    ModHomology p (IdentityRootsFixedSpace m) 0 ≃ₗ[ℤ] ZMod p :=
  (identityRootsFixedModHomologyEquiv p m hm 0).trans (unitSphereModHomologyZeroEquiv p hp 1)

/-- Actual degree-two homology of that same original automorphism-subgroup fixed subtype. -/
def identityRootsFixedModHomologyTwoEquiv (p : ℕ) (hp : p ≠ 0) (m : ℕ) (hm : 2 ≤ m) :
    ModHomology p (IdentityRootsFixedSpace m) 2 ≃ₗ[ℤ] ZMod p :=
  (identityRootsFixedModHomologyEquiv p m hm 2).trans (unitSphereModHomologyTopEquiv p hp 1)

/-- All remaining coefficient homology groups of the actual automorphism fixed set vanish. -/
theorem identityRootsFixedModHomology_subsingleton (p : ℕ) (hp : p ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≠ 0) (hk2 : k ≠ 2) :
    Subsingleton (ModHomology p (IdentityRootsFixedSpace m) k) := by
  let := unitSphereModHomology_subsingleton p hp 1 k hk hk2
  exact (identityRootsFixedModHomologyEquiv p m hm k).injective.subsingleton

/-- The native automorphism fixed-set homology object is zero outside degrees zero and two. -/
theorem identityRootsFixedModHomology_isZero (p : ℕ) (hp : p ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≠ 0) (hk2 : k ≠ 2) :
    IsZero (ModHomology p (IdentityRootsFixedSpace m) k) := by
  let := identityRootsFixedModHomology_subsingleton p hp m hm k hk hk2
  exact ModuleCat.isZero_of_subsingleton _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology
