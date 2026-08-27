/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteConcentration

/-! # Finite edge families and their genuine product probability law -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

structure FiniteEdgeFamily (I Ω α : Type*) [Fintype I] [Fintype Ω] [DecidableEq α] where
  vertices : Finset α
  rank : ℕ
  edge : I → Ω → Finset α
  mass : I → Ω → ℝ
  mass_nonneg : ∀ i w, 0 ≤ mass i w
  mass_sum_one : ∀ i, ∑ w, mass i w = 1
  edge_subset : ∀ i w, edge i w ⊆ vertices
  edge_card_le : ∀ i w, (edge i w).card ≤ rank

namespace FiniteEdgeFamily

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def vertexMass (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) : ℝ :=
  ∑ w, if v ∈ F.edge i w then F.mass i w else 0

def pairMass (F : FiniteEdgeFamily I Ω α) (i : I) (v u : α) : ℝ :=
  ∑ w, if v ∈ F.edge i w ∧ u ∈ F.edge i w then F.mass i w else 0

def degree (F : FiniteEdgeFamily I Ω α) (v : α) : ℝ := ∑ i, F.vertexMass i v

def codegree (F : FiniteEdgeFamily I Ω α) (v u : α) : ℝ := ∑ i, F.pairMass i v u

def choiceMass (F : FiniteEdgeFamily I Ω α) (ξ : I → Ω) : ℝ := ∏ i, F.mass i (ξ i)

theorem vertexMass_nonneg (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) :
    0 ≤ F.vertexMass i v := by
  apply Finset.sum_nonneg
  intro w _hw
  split_ifs
  · exact F.mass_nonneg i w
  · exact le_rfl

theorem vertexMass_le_one (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) :
    F.vertexMass i v ≤ 1 := by
  calc
    _ ≤ ∑ w, F.mass i w := by
      apply Finset.sum_le_sum
      intro w _hw
      split_ifs
      · exact le_rfl
      · exact F.mass_nonneg i w
    _ = 1 := F.mass_sum_one i

theorem pairMass_nonneg (F : FiniteEdgeFamily I Ω α) (i : I) (v u : α) :
    0 ≤ F.pairMass i v u := by
  apply Finset.sum_nonneg
  intro w _hw
  split_ifs
  · exact F.mass_nonneg i w
  · exact le_rfl

theorem pairMass_le_vertexMass (F : FiniteEdgeFamily I Ω α) (i : I) (v u : α) :
    F.pairMass i v u ≤ F.vertexMass i v := by
  apply Finset.sum_le_sum
  intro w _hw
  by_cases hv : v ∈ F.edge i w <;> by_cases hu : u ∈ F.edge i w <;>
    simp [hv, hu, F.mass_nonneg]

theorem choiceMass_nonneg (F : FiniteEdgeFamily I Ω α) (ξ : I → Ω) :
    0 ≤ F.choiceMass ξ := assignmentWeight_nonneg F.mass F.mass_nonneg ξ

variable [DecidableEq I]

theorem choiceMass_sum_one (F : FiniteEdgeFamily I Ω α) : ∑ ξ : I → Ω, F.choiceMass ξ = 1 := by
  classical
  exact assignmentWeight_sum F.mass F.mass_sum_one

theorem independent_events (F : FiniteEdgeFamily I Ω α) (P : I → Ω → Prop)
    [∀ i w, Decidable (P i w)] :
    (∑ ξ : I → Ω, if ∀ i, P i (ξ i) then F.choiceMass ξ else 0) =
      ∏ i, ∑ w, if P i w then F.mass i w else 0 := by
  classical
  exact independent_assignment_miss_mass F.mass P

theorem coordinate_event (F : FiniteEdgeFamily I Ω α) (i : I) (P : Ω → Prop)
    [DecidablePred P] :
    (∑ ξ : I → Ω, if P (ξ i) then F.choiceMass ξ else 0) =
      ∑ w, if P w then F.mass i w else 0 := by
  classical
  have h := F.independent_events (fun j w => j = i → P w)
  have hevent (ξ : I → Ω) : (∀ j, j = i → P (ξ j)) ↔ P (ξ i) := by
    constructor
    · intro h
      exact h i rfl
    · intro h j hj
      subst j
      exact h
  simp_rw [hevent] at h
  refine h.trans ?_
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _hj hji
    simpa [hji] using F.mass_sum_one j
  · simp

theorem vertexMass_eq_choice_marginal (F : FiniteEdgeFamily I Ω α) (i : I) (v : α) :
    F.vertexMass i v =
      ∑ ξ : I → Ω, if v ∈ F.edge i (ξ i) then F.choiceMass ξ else 0 :=
  (F.coordinate_event i (fun w => v ∈ F.edge i w)).symm

theorem pairMass_eq_choice_marginal (F : FiniteEdgeFamily I Ω α) (i : I) (v u : α) :
    F.pairMass i v u =
      ∑ ξ : I → Ω, if v ∈ F.edge i (ξ i) ∧ u ∈ F.edge i (ξ i)
        then F.choiceMass ξ else 0 := (F.coordinate_event i (fun w =>
          v ∈ F.edge i w ∧ u ∈ F.edge i w)).symm

end FiniteEdgeFamily

end

end Erdos4b.FGKMT
