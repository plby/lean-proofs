import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicSpecialDescent

/-!
# Lemma 9.6: genuine meromorphic descent for the constructed threefold

Every genuine locally represented meromorphic function which is constant
on uncountably many regular fibres is the actual pullback of a unique
genuine meromorphic function on the original Riemann sphere. All regular
and special local descents are proved from the native fractions and the
constructed projection; the only hypothesis is the stated fibre constancy.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Source Lemma 9.6 for arbitrary genuine native meromorphic functions.
There is no local-fraction, normal-form, extension, or descent hypothesis. -/
theorem existsUnique_sphere_meromorphic_descent
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable) :
    ∃! s : HolomorphicMeromorphic.Function I₁ RiemannSphere, sphereMeromorphicPullback s = g := by
  apply existsUnique_sphere_descent_of_local g
  intro b
  by_cases hb : b ∈ sphereRegularPatch
  · exact meromorphicallyDescendsNear_regular g hg b hb
  · exact meromorphicallyDescendsNear_special g hg b hb

/-- The uniquely determined genuine meromorphic function on the sphere. -/
def sphereMeromorphicDescent (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable) :
    HolomorphicMeromorphic.Function I₁ RiemannSphere :=
  (existsUnique_sphere_meromorphic_descent g hg).choose

theorem sphereMeromorphicPullback_descent
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable) :
    sphereMeromorphicPullback (sphereMeromorphicDescent g hg) = g :=
  (existsUnique_sphere_meromorphic_descent g hg).choose_spec.1

theorem sphereMeromorphicDescent_unique
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (s : HolomorphicMeromorphic.Function I₁ RiemannSphere)
    (hs : sphereMeromorphicPullback s = g) :
    s = sphereMeromorphicDescent g hg :=
  (existsUnique_sphere_meromorphic_descent g hg).choose_spec.2 s hs

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
