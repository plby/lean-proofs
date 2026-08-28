import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedSphere
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedAut0
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedAut0Roots

/-!
# Remark 9.25 for the original action and genuine automorphism group

For every `n ≥ 2`, the actual subgroup `rootsOfUnity n ℂ`, acting by
restriction of the constructed action, has the same literal fixed set
as the whole group: the original double curve `D₀`. That fixed subspace
is homeomorphic to the standard unit two-sphere. The same statements
hold for its actual image in the genuine automorphism identity component.

The elliptic affine congruence and cusp torsion-free deck arguments
exclude finite isotropy away from `D₀`. No absence of isotropy is inferred
from normal weights, and neither sphere recognition for the ambient
threefold nor Smith theory is an input.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed

open Automorphisms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- Equality of the literal fixed sets inside the genuine automorphism
group, with its existing evaluation action on the original threefold. -/
theorem identityRoots_fixedPoints_eq_component (n : ℕ) (hn : 2 ≤ n) :
    MulAction.fixedPoints (identityRoots n) Space = MulAction.fixedPoints Aut₀ Space :=
  (identityRoots_fixedPoints_eq_D₀ n hn).trans Aut0.fixedPoints_eq_D₀.symm

/-- The finite-subgroup fixed subspace of the original automorphism
component is an actual standard Euclidean two-sphere. -/
def identityRootsFixedSphereHomeomorph (n : ℕ) (hn : 2 ≤ n) :
    MulAction.fixedPoints (identityRoots n) Space ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let := VerticalAction.action
  exact (Homeomorph.setCongr ((identityRoots_fixedPoints_eq_D₀ n hn).trans
    (rootsOfUnity_fixedPoints_eq_D₀ n hn).symm)).trans
      (rootsOfUnityFixedSphereHomeomorph n hn)

/-- The same fixed-locus conclusion with the source's integer indexing. -/
theorem rootsOfUnity_int_fixedPoints_eq_D₀ (n : ℤ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    MulAction.fixedPoints (rootsOfUnity n.toNat ℂ) Space = VerticalAction.D₀ :=
  rootsOfUnity_fixedPoints_eq_D₀ n.toNat (by omega)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed
