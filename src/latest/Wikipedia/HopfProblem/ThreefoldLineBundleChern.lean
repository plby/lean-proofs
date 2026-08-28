import Wikipedia.HopfProblem.ThreefoldLineBundleChernBasic

/-!
# Vanishing of every original holomorphic line-bundle first Chern class on X

The map was constructed before this vanishing result from the actual
native unit cocycle, the original exponential connecting homomorphism,
and the genuine integral constant-sheaf--singular comparison. The proved
integral singular cohomology calculation of the original glued threefold
now annihilates all its values. No sphere-recognition hypothesis is used.

Vanishing of these classes does not itself construct a continuous or
holomorphic trivialization, nor identify this construction with separate
period-torus winding representatives. Those are separate comparisons.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleChern

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

universe u

/-- Every original native holomorphic line bundle on the actual threefold
has zero first Chern class in the original integral singular cohomology. -/
theorem nativeFirstChernClass_eq_zero (V : Space → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IF] :
    nativeFirstChernClass V = 0 :=
  CohomologySphere.cohomology_eq_zero 2 (by decide) (by decide) _

theorem firstChernClass_eq_zero (L : HolomorphicPicard.LineBundle.{u} IF Space) :
    firstChernClass L = 0 := nativeFirstChernClass_eq_zero L.Fiber

theorem firstChernHom_apply_eq_zero (x : PicardExponential.PicardGroup) : firstChernHom x = 0 :=
  CohomologySphere.cohomology_eq_zero 2 (by decide) (by decide) _

/-- The genuinely constructed Chern homomorphism vanishes as a consequence
of the original threefold's computed cohomology, not by definition. -/
theorem firstChernHom_eq_zero : firstChernHom = 0 := by
  ext x
  exact firstChernHom_apply_eq_zero x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleChern
