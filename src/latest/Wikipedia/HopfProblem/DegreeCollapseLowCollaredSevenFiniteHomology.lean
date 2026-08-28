import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenState
import Wikipedia.HopfProblem.DegreeCollapseCompactHomologyFinite
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarSplitting

/-!

# Finite generation before the low-dimensional surgery reductions

Native compact Morse sublevels give finite generation of the original
closed manifold's higher homology. The actual collar inclusion is injective
when the boundary homology in that degree vanishes. Since the integers are
Noetherian, this proves finite generation of the actual positive half.
Simple connectivity and zero half-homology are not hypotheses.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

theorem half_higherHomology_finitely_generated (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology B (k + 1))] :
    Module.Finite ℤ (SingularHomology S.PositiveHalf (k + 1)) := by
  let : Module.Finite ℤ (SingularHomology S.Space (k + 1)) :=
    MorseFiniteness.compactManifold_higherHomology_finite (Vector 7) S.Space k hk
  exact Module.Finite.of_injective (singularHomologyMap (TimeCollar.halfInclusion S.time) (k + 1))
    (S.collar.halfInclusion_homology_injective (k + 1))

theorem half_secondHomology_finitely_generated [Subsingleton (SingularHomology B 2)] :
    Module.Finite ℤ (SingularHomology S.PositiveHalf 2) :=
  S.half_higherHomology_finitely_generated 1 (by decide)

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
