import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixed
import Wikipedia.HopfProblem.SphereHomologyBasic

/-!
# The literal finite fixed loci in the Euclidean sphere homology model

Both fixed spaces below are actual subsets of the original threefold,
with the subspace topology.  The frozen fixed-locus geometry identifies
them with the literal Euclidean unit two-sphere used by the native sphere
homology calculation.  No ambient sphere recognition or fixed-point
homology theorem is used in this transport.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology

open Set

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- The literal fixed subset for the original restricted roots-of-unity action. -/
abbrev RootsFixedSpace (n : ℕ) : Set Space := by
  letI := VerticalAction.action
  exact MulAction.fixedPoints (rootsOfUnity n ℂ) Space

/-- The literal fixed subset for the actual finite subgroup of the automorphism component. -/
abbrev IdentityRootsFixedSpace (n : ℕ) : Set Space :=
  MulAction.fixedPoints (FiniteActionFixed.identityRoots n) Space

/-- The roots fixed space is the previously constructed original double curve. -/
theorem rootsFixedSpace_eq_D₀ (n : ℕ) (hn : 2 ≤ n) :
    RootsFixedSpace n = VerticalAction.D₀ := by
  let := VerticalAction.action
  exact FiniteActionFixed.rootsOfUnity_fixedPoints_eq_D₀ n hn

/-- The genuine automorphism-subgroup fixed space is the same original double curve. -/
theorem identityRootsFixedSpace_eq_D₀ (n : ℕ) (hn : 2 ≤ n) :
    IdentityRootsFixedSpace n = VerticalAction.D₀ :=
  FiniteActionFixed.identityRoots_fixedPoints_eq_D₀ n hn

/-- The original roots fixed subtype is exactly the sphere used in the native homology proof. -/
def rootsFixedSphereHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    RootsFixedSpace n ≃ₜ SphereHomology.UnitSphere 2 := by
  letI := VerticalAction.action
  exact FiniteActionFixed.rootsOfUnityFixedSphereHomeomorph n hn

/-- The actual identity-component finite fixed subtype has that same genuine sphere model. -/
def identityRootsFixedSphereHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    IdentityRootsFixedSpace n ≃ₜ SphereHomology.UnitSphere 2 :=
  FiniteActionFixed.identityRootsFixedSphereHomeomorph n hn

/-- The comparison of the two actual fixed loci is induced by equality of subsets. -/
def rootsFixedIdentityHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    RootsFixedSpace n ≃ₜ IdentityRootsFixedSpace n :=
  Homeomorph.setCongr ((rootsFixedSpace_eq_D₀ n hn).trans
    (identityRootsFixedSpace_eq_D₀ n hn).symm)

/-- This comparison leaves every point of the original ambient threefold unchanged. -/
@[simp] theorem rootsFixedIdentityHomeomorph_val (n : ℕ) (hn : 2 ≤ n)
    (x : RootsFixedSpace n) : (rootsFixedIdentityHomeomorph n hn x : Space) = x.val := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteFixedHomology
