/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.FiniteSupport
import ErdosProblems.Erdos254.TorusCharacters

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- A thick portion of a nonempty finite-dimensional Bohr set. -/
def ContainsPiecewiseBohr (S : Set ℕ) : Prop :=
  ∃ (d : ℕ) (θ : UnitAddTorus (Fin d)) (U : Set (UnitAddTorus (Fin d))) (J : Set ℕ),
    IsOpen U ∧ IsThick J ∧ (∃ n : ℕ, n ∈ J ∧ n • θ ∈ U) ∧
      ∀ n ∈ J, n • θ ∈ U → n ∈ S

/-- Fan's finite-support refinement, once a piecewise Bohr subset has been
extracted. All compact-group and character inputs are proved in the imports. -/
theorem finite_support_thick_of_piecewiseBohr {B C : Set ℕ}
    (hBC : Disjoint B C) (hB : ContainsPiecewiseBohr (subsetSums B)) (hC : PhaseDivergent C) :
    ∃ E : Finset ℕ, (E : Set ℕ) ⊆ C ∧ IsThick (subsetSums (B ∪ (E : Set ℕ))) := by
  obtain ⟨d, θ, U, J, hU, hJ, ⟨n, _, hn⟩, hBohr⟩ := hB
  obtain ⟨E, hEC, hcover⟩ := finite_orbit_cover C θ U hU ⟨n, hn⟩
    (generator_mem_tailSubgroup hC θ)
  refine ⟨E, hEC, ?_⟩
  exact thick_subsetSums_of_finite_cover E (hBC.mono_right hEC) θ U J hJ hBohr hcover

end Erdos254
