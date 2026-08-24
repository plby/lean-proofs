/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos1024

abbrev TripleSystem (n : ℕ) := Finset (Finset (Fin n))

def allTriples (n : ℕ) : TripleSystem n :=
  Finset.univ.powersetCard 3

def IsLinear {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

instance isLinearDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsLinear H) := by
  unfold IsLinear
  infer_instance

noncomputable def linearSystems (n : ℕ) : Finset (TripleSystem n) :=
  (allTriples n).powerset.filter IsLinear

def IsIndependent {n : ℕ} (H : TripleSystem n) (I : Finset (Fin n)) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬e ⊆ I

instance isIndependentDecidable {n : ℕ} (H : TripleSystem n)
    (I : Finset (Fin n)) : Decidable (IsIndependent H I) := by
  unfold IsIndependent
  infer_instance

noncomputable def independenceNumber {n : ℕ} (H : TripleSystem n) : ℕ :=
  (Finset.univ.powerset.filter (IsIndependent H)).sup Finset.card

theorem linearSystems_nonempty (n : ℕ) : (linearSystems n).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [linearSystems, IsLinear]

noncomputable def guaranteedIndependence (n : ℕ) : ℕ :=
  (linearSystems n).inf' (linearSystems_nonempty n) independenceNumber

noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

theorem erdos_1024 :
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) =Θ[atTop]
      resolutionScale := by
  sorry

end Erdos1024
