import Mathlib

open Filter
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1024

abbrev TripleSystem (n : ℕ) := Finset (Finset (Fin n))

end Erdos1024

namespace Erdos1024

def allTriples (n : ℕ) : TripleSystem n :=
  Finset.univ.powersetCard 3

end Erdos1024

namespace Erdos1024

def IsLinear {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

instance isLinearDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsLinear H) := by
  unfold IsLinear
  infer_instance

end Erdos1024

namespace Erdos1024

noncomputable def linearSystems (n : ℕ) : Finset (TripleSystem n) :=
  (allTriples n).powerset.filter IsLinear

end Erdos1024

namespace Erdos1024

def IsIndependent {n : ℕ} (H : TripleSystem n) (I : Finset (Fin n)) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬e ⊆ I

instance isIndependentDecidable {n : ℕ} (H : TripleSystem n)
    (I : Finset (Fin n)) : Decidable (IsIndependent H I) := by
  unfold IsIndependent
  infer_instance

end Erdos1024

namespace Erdos1024

noncomputable def independenceNumber {n : ℕ} (H : TripleSystem n) : ℕ :=
  (Finset.univ.powerset.filter (IsIndependent H)).sup Finset.card

end Erdos1024

namespace Erdos1024

theorem linearSystems_nonempty (n : ℕ) : (linearSystems n).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [linearSystems, IsLinear]

noncomputable def guaranteedIndependence (n : ℕ) : ℕ :=
  (linearSystems n).inf' (linearSystems_nonempty n) independenceNumber

end Erdos1024

namespace Erdos1024

noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

end Erdos1024

namespace Erdos1024

theorem erdos_problem_1024 :
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) =Θ[atTop]
      resolutionScale := by
  sorry

end Erdos1024

end
