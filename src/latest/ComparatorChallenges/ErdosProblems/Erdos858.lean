import Mathlib

open scoped BigOperators Topology
open Filter Finset Set

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos858

def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

end Erdos858

namespace Erdos858

def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, 1 < t → b = a * t → t.minFac ≤ a

end Erdos858

namespace Erdos858

noncomputable def candidateFamilies (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (interval N).powerset.filter Admissible

end Erdos858

namespace Erdos858

noncomputable def harmonicMass (A : Finset ℕ) : ℝ := ∑ n ∈ A, (n : ℝ)⁻¹

end Erdos858

namespace Erdos858

noncomputable def candidateMasses (N : ℕ) : Finset ℝ := by
  classical
  exact (candidateFamilies N).image harmonicMass

lemma empty_mem_candidateFamilies (N : ℕ) : ∅ ∈ candidateFamilies N := by
  classical
  simp [candidateFamilies, Admissible]

lemma candidateMasses_nonempty (N : ℕ) : (candidateMasses N).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  exact Finset.mem_image.mpr ⟨∅, empty_mem_candidateFamilies N, by simp [harmonicMass]⟩

end Erdos858

namespace Erdos858

noncomputable def extremalMass (N : ℕ) : ℝ :=
  (candidateMasses N).max' (candidateMasses_nonempty N)

end Erdos858

namespace Erdos858

noncomputable def twoPrimeProfile (u : ℝ) : ℝ :=
  if u < (1 : ℝ) / 3 then
    ∫ x in u..(1 - u) / 2, x⁻¹ * Real.log ((1 - u - x) / x)
  else 0

end Erdos858

namespace Erdos858

noncomputable def profile (u : ℝ) : ℝ :=
  Real.log ((1 - u) / u) + twoPrimeProfile u

end Erdos858

namespace Erdos858

noncomputable def alphaTwo : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) ∧ profile u ≤ 1}

end Erdos858

namespace Erdos858

noncomputable def constant : ℝ :=
  (1 : ℝ) / 2 + ∫ u in alphaTwo..(1 : ℝ) / 2, 1 - profile u

end Erdos858

namespace Erdos858

theorem erdos_858 :
    Tendsto (fun N : ℕ ↦ extremalMass N / Real.log (N : ℝ))
      atTop (nhds constant) := by
  sorry

end Erdos858

end
