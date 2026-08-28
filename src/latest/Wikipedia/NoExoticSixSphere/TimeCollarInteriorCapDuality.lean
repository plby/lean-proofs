import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Wikipedia.NoExoticSixSphere.ModHomologyHomotopyEquiv
import Wikipedia.NoExoticSixSphere.ManifoldCompactSupportDuality

/-!
# Actual interior cap duality for a collared seven-dimensional half

The positive interior has the original open-submanifold atlas. Its
compact-support cap map is followed by the literal interior-to-half
inclusion. The constructed collar homotopy equivalence makes that
inclusion bijective on finite-coefficient homology. This does not yet
identify boundary-relative cohomology or the boundary connecting class.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def interiorModHomologyEquiv (p n : ℕ) :
    ModHomology p C.positiveInterior n ≃ₗ[ℤ] ModHomology p (NonnegativeHalf t) n :=
  modHomologyHomotopyEquiv p C.interiorHalfHomotopyEquiv n

theorem interiorModHomologyEquiv_toLinearMap (p n : ℕ) :
    (interiorModHomologyEquiv C p n).toLinearMap = modHomologyMap p C.interiorToHalf n := rfl

theorem interiorToHalf_modHomology_bijective (p n : ℕ) :
    Bijective (modHomologyMap p C.interiorToHalf n) := (interiorModHomologyEquiv C p n).bijective

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M]

local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩

def interiorCapMap (p q : ℕ) (h : p + q = 7) :
    CompactSupportCohomology.Cohomology C.positiveInterior p →ₗ[ℤ]
      ModHomology 2 (NonnegativeHalf t) q :=
  (modHomologyMap 2 C.interiorToHalf q).comp
    (CompactSupportCapMap.dualityMap (E := Vector 7) 4 C.positiveInterior p q h)

theorem interiorCapMap_bijective (p q : ℕ) (h : p + q = 7) :
    Bijective (interiorCapMap C p q h) :=
  (interiorToHalf_modHomology_bijective C 2 q).comp
    (CompactSupportCapMap.manifold_bijective (E := Vector 7) 4 C.positiveInterior p q h)

def interiorCapEquiv (p q : ℕ) (h : p + q = 7) :
    CompactSupportCohomology.Cohomology C.positiveInterior p ≃ₗ[ℤ]
      ModHomology 2 (NonnegativeHalf t) q :=
  LinearEquiv.ofBijective (interiorCapMap C p q h) (interiorCapMap_bijective C p q h)

theorem interiorCapEquiv_toLinearMap (p q : ℕ) (h : p + q = 7) :
    (interiorCapEquiv C p q h).toLinearMap = interiorCapMap C p q h := rfl

end NoExoticSixSphere.TimeCollarDuality
