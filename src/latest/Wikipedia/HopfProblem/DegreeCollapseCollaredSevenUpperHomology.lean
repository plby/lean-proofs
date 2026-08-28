import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenTerminalFilling
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarLowCompactCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenManifoldDuality

/-!
# All positive-degree homology vanishes for the actual cleared half

Closed integral duality gives ambient H5 = 0. The actual interior's
compactly supported H1 and H0 give its H6 and H7 by open-manifold duality.
The original collar homotopy equivalence transfers these to the literal
half. Above dimension seven, compact-manifold support bounds and the
actual half inclusion suffice. The six-sphere boundary supplies the
required homology vanishings; its nonzero H6 is never discarded.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization SingularMayerVietoris
open PeriodTorusHigherHomology SingularCohomologyFree

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

theorem closed_fifth_homology : Subsingleton (SingularHomology S.Space 5) := by
  let : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩
  let : Subsingleton (SingularHomology S.Space 1) :=
    IntegralTopClassLift.first_homology_subsingleton S.Space
  let : Finite (SingularHomology S.Space (1 + 1)) :=
    inferInstanceAs (Finite (SingularHomology S.Space 2))
  let : Subsingleton (SingularCohomology S.Space 2) :=
    IntegralSevenDuality.cohomology_succ_subsingleton S.Space 1
  exact (IntegralCompactSupportCap.absoluteDualityMap_bijective
    (E := Vector 7) 4 S.Space 2 5 rfl).surjective.subsingleton

theorem closed_above_homology (k : ℕ) (hk : 7 < k) :
    Subsingleton (SingularHomology S.Space k) := by
  let : Fact (Module.finrank ℝ (Vector 7) = (5 + 1) + 1) := ⟨by simp⟩
  let : Subsingleton (SupportedRelativeHomology.Homology
      (ModuleCat.of ℤ ℤ) (univ : Set S.Space) k) :=
    IntegralCompactSupport.compactManifold_above_subsingleton (E := Vector 7)
      5 univ isCompact_univ k hk
  exact (SupportedRelativeHomology.absoluteEquiv (X := S.Space) (ModuleCat.of ℤ ℤ) k
    ).injective.subsingleton

theorem half_fifth_homology [Subsingleton (SingularHomology B 5)] :
    Subsingleton (SingularHomology S.Half 5) := by
  let := S.closed_fifth_homology
  exact S.collar.half_homology_subsingleton 5

theorem half_sixth_homology [PathConnectedSpace B] :
    Subsingleton (SingularHomology S.Half 6) := by
  let : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩
  let : Subsingleton (IntegralCompactSupportCohomology.Cohomology
      S.collar.positiveInterior 1) := S.collar.interior_compactSupport_low_cohomology 1 (by decide)
  let : Subsingleton (SingularHomology S.collar.positiveInterior 6) :=
    (IntegralOpenFundamentalClass.dualityEquiv (E := Vector 7)
      4 S.collar.positiveInterior 1 6 rfl).surjective.subsingleton
  exact (homotopyEquivHomologyEquiv S.collar.interiorHalfHomotopyEquiv 6).surjective.subsingleton

theorem half_seventh_homology [PathConnectedSpace B] :
    Subsingleton (SingularHomology S.Half 7) := by
  let : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩
  let : Subsingleton (IntegralCompactSupportCohomology.Cohomology
      S.collar.positiveInterior 0) := S.collar.interior_compactSupport_low_cohomology 0 (by decide)
  let : Subsingleton (SingularHomology S.collar.positiveInterior 7) :=
    (IntegralOpenFundamentalClass.dualityEquiv (E := Vector 7)
      4 S.collar.positiveInterior 0 7 rfl).surjective.subsingleton
  exact (homotopyEquivHomologyEquiv S.collar.interiorHalfHomotopyEquiv 7).surjective.subsingleton

theorem half_above_homology (k : ℕ) (hk : 7 < k) [Subsingleton (SingularHomology B k)] :
    Subsingleton (SingularHomology S.Half k) := by
  let := S.closed_above_homology k hk
  exact S.collar.half_homology_subsingleton k

theorem half_positive_homology_of_sphere (eBoundary : B ≃ₜ Sphere 6)
    [Finite (SingularHomology S.Space 3)] [Subsingleton (SingularHomology S.Half 3)]
    (k : ℕ) (hk : k ≠ 0) : Subsingleton (SingularHomology S.Half k) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  have hB (j : ℕ) (hj : j ≠ 0) (h6 : j ≠ 6) : Subsingleton (SingularHomology B j) := by
    let : Subsingleton (SingularHomology (Sphere 6) j) :=
      SphereHomology.unitSphere_homology_subsingleton 5 j hj h6
    exact (homotopyEquivHomologyEquiv eBoundary.toHomotopyEquiv j).injective.subsingleton
  by_cases h7 : 7 < k
  · let := hB k hk (by omega)
    exact S.half_above_homology k h7
  · have hk7 : k ≤ 7 := Nat.le_of_not_gt h7
    interval_cases k
    · exact (hk rfl).elim
    · exact IntegralTopClassLift.first_homology_subsingleton S.Half
    · let := hB 2 (by decide) (by decide)
      exact S.half_second_homology
    · infer_instance
    · let := hB 4 (by decide) (by decide)
      exact S.half_fourth_homology
    · let := hB 5 (by decide) (by decide)
      exact S.half_fifth_homology
    · exact S.half_sixth_homology
    · exact S.half_seventh_homology

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
