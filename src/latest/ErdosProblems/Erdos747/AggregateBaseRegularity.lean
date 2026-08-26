import ErdosProblems.Erdos747.AggregateTopFiber

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## A concrete random-regularity base for aggregate layers -/

/-- The standard sparse-layer certificate: open constant-factor degree
bounds, a codegree cap, and aggregate degree regularity. -/
def AggregateLayerRegular
    (n M codegCap : ℕ) (a B q etaDeg Bdeg : ℝ)
    (H : Finset (Edge n)) : Prop :=
  (∀ v : Vertex n,
      a * ((M : ℝ) / n) < vertexDegree H v) ∧
  (∀ v : Vertex n,
      (vertexDegree H v : ℝ) < B * ((M : ℝ) / n)) ∧
  (∀ u v : Vertex n, u ≠ v →
      vertexCodegree H u v ≤ codegCap) ∧
  DegreeAggregateRegular n M q etaDeg Bdeg H

/-- The arbitrary-factor lower degree union bound transported from ordered
sampling to the fixed-edge sample. -/
lemma sampled_exists_degree_lower_factor_sample_le
    (n M : ℕ) (a : ℝ) (hn : 0 < n) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hM : 2 * M * M ≤ (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ ∃ v : Vertex n,
          (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)) ≤
      (3 * n : ℝ) *
        (2 * Real.exp
          (((M : ℝ) / n) * (a - 1 - a * Real.log a))) := by
  have hMcard : M ≤ (allEdges n).card := by
    have hself : M ≤ 2 * M * M := by
      by_cases hM0 : M = 0
      · simp [hM0]
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
        calc
          M ≤ M * M := Nat.le_mul_of_pos_right M hMpos
          _ ≤ 2 * (M * M) := Nat.le_mul_of_pos_left _ (by omega)
          _ = 2 * M * M := by ac_rfl
    exact hself.trans hM
  calc
    finsetProbability (sample n M)
        (fun H ↦ ∃ v : Vertex n,
          (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)) =
        @finsetProbability _ (sample n M)
          (fun H ↦ ∃ v : Vertex n,
            (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n))
          (Classical.decPred _) :=
      finsetProbability_decidable_irrel (sample n M) _ _ _
    _ = @finsetProbability _
        (Finset.univ : Finset (DeletionHistory (allEdges n) M))
        (fun e ↦ ∃ v : Vertex n,
          (vertexDegree (historyEdges e) v : ℝ) ≤ a * ((M : ℝ) / n))
        (Classical.decPred _) :=
      (historyEdges_probability_eq_sample (allEdges n) hMcard
        (fun H ↦ ∃ v : Vertex n,
          (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n))).symm
    _ = finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) M))
        (fun e ↦ ∃ v : Vertex n,
          (vertexDegree (historyEdges e) v : ℝ) ≤ a * ((M : ℝ) / n)) :=
      finsetProbability_decidable_irrel Finset.univ _ _ _
    _ ≤ _ := sampled_exists_degree_lower_factor_le n M a hn ha0 ha1 hM

/-- The all-pairs codegree-six union bound transported to the fixed-edge
sample. -/
lemma sampled_exists_codegree_six_sample_le
    (n M : ℕ) (hn : 0 < n)
    (hM : 2 * M * M ≤ (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree H u v) ≤
      ((3 * n : ℝ)^2) *
        (2 * Real.exp
          ((M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
              ((n : ℝ) - 1) -
            Real.log (n : ℝ) * 6)) := by
  have hMcard : M ≤ (allEdges n).card := by
    have hself : M ≤ 2 * M * M := by
      by_cases hM0 : M = 0
      · simp [hM0]
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
        calc
          M ≤ M * M := Nat.le_mul_of_pos_right M hMpos
          _ ≤ 2 * (M * M) := Nat.le_mul_of_pos_left _ (by omega)
          _ = 2 * M * M := by ac_rfl
    exact hself.trans hM
  calc
    finsetProbability (sample n M)
        (fun H ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree H u v) =
      @finsetProbability _ (sample n M)
        (fun H ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree H u v) (Classical.decPred _) :=
        finsetProbability_decidable_irrel (sample n M) _ _ _
    _ = @finsetProbability _
        (Finset.univ : Finset (DeletionHistory (allEdges n) M))
        (fun e ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree (historyEdges e) u v)
        (Classical.decPred _) :=
      (historyEdges_probability_eq_sample (allEdges n) hMcard
        (fun H ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree H u v)).symm
    _ = finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) M))
        (fun e ↦ ∃ u v : Vertex n, u ≠ v ∧
          6 ≤ vertexCodegree (historyEdges e) u v) :=
      finsetProbability_decidable_irrel Finset.univ _ _ _
    _ =
      finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) M))
        (fun e ↦ e ∈ sampledCodegreeFailureSet n M) := by
          apply finsetProbability_congr_event
          intro e he
          rw [mem_sampledCodegreeFailureSet_iff]
          constructor
          · rintro ⟨u, v, huv, hcodeg⟩
            exact ⟨⟨(u, v), huv⟩, by exact_mod_cast hcodeg⟩
          · rintro ⟨p, hp⟩
            exact ⟨p.1.1, p.1.2, p.2, by exact_mod_cast hp⟩
    _ ≤ _ := sampledCodegreeFailureSet_le n M hn hM

/-- The concrete base fails only through the four standard degree,
codegree, or aggregate-degree events. -/
lemma aggregateLayerRegular_compl_le
    (n M : ℕ) (a B q etaDeg Bdeg : ℝ)
    (hn : 0 < n) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hB : 1 ≤ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hetaDeg : 0 < etaDeg) (hBdeg : 1 ≤ Bdeg)
    (hM : 2 * M * M ≤ (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ ¬ AggregateLayerRegular n M 5
          a B q etaDeg Bdeg H) ≤
      (3 * n : ℝ) *
          (2 * Real.exp
            (((M : ℝ) / n) * (a - 1 - a * Real.log a))) +
      (3 * n : ℝ) *
          (2 * Real.exp
            (((M : ℝ) / n) * (B - 1 - B * Real.log B))) +
      ((3 * n : ℝ)^2) *
          (2 * Real.exp
            ((M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) *
                ((n : ℝ) - 1) - Real.log (n : ℝ) * 6)) +
      ((4 / etaDeg) * Real.exp (-(q^2 * ((M : ℝ) / n)) / 4) +
        (3 * n : ℝ) *
          (2 * Real.exp (((M : ℝ) / n) *
            (Bdeg - 1 - Bdeg * Real.log Bdeg)))) := by
  let P₀ : Finset (Edge n) → Prop := fun H ↦ ∃ v : Vertex n,
    (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)
  let P₁ : Finset (Edge n) → Prop := fun H ↦ ∃ v : Vertex n,
    B * ((M : ℝ) / n) ≤ vertexDegree H v
  let P₂ : Finset (Edge n) → Prop := fun H ↦ ∃ u v : Vertex n,
    u ≠ v ∧ 6 ≤ vertexCodegree H u v
  let P₃ : Finset (Edge n) → Prop := fun H ↦
    ¬ DegreeAggregateRegular n M q etaDeg Bdeg H
  calc
    finsetProbability (sample n M)
        (fun H ↦ ¬ AggregateLayerRegular n M 5
          a B q etaDeg Bdeg H) ≤
      finsetProbability (sample n M)
        (fun H ↦ P₀ H ∨ P₁ H ∨ P₂ H ∨ P₃ H) := by
          apply finsetProbability_mono_event
          intro H hHs hfail
          by_cases hlow : ∀ v : Vertex n,
              a * ((M : ℝ) / n) < vertexDegree H v
          · by_cases hupper : ∀ v : Vertex n,
                (vertexDegree H v : ℝ) < B * ((M : ℝ) / n)
            · by_cases hcodeg : ∀ u v : Vertex n, u ≠ v →
                  vertexCodegree H u v ≤ 5
              · apply Or.inr (Or.inr (Or.inr ?_))
                intro haggregate
                exact hfail ⟨hlow, hupper, hcodeg, haggregate⟩
              · apply Or.inr (Or.inr (Or.inl ?_))
                push Not at hcodeg
                rcases hcodeg with ⟨u, v, huv, hcap⟩
                exact ⟨u, v, huv, by omega⟩
            · apply Or.inr (Or.inl ?_)
              push Not at hupper
              exact hupper
          · apply Or.inl
            push Not at hlow
            exact hlow
    _ ≤ finsetProbability (sample n M) P₀ +
          finsetProbability (sample n M) P₁ +
          finsetProbability (sample n M) P₂ +
          finsetProbability (sample n M) P₃ := by
      calc
        _ ≤ finsetProbability (sample n M) P₀ +
            finsetProbability (sample n M)
              (fun H ↦ P₁ H ∨ P₂ H ∨ P₃ H) :=
          finsetProbability_or_le_add _ _ _
        _ ≤ finsetProbability (sample n M) P₀ +
            (finsetProbability (sample n M) P₁ +
              finsetProbability (sample n M)
                (fun H ↦ P₂ H ∨ P₃ H)) :=
          add_le_add le_rfl (finsetProbability_or_le_add _ _ _)
        _ ≤ finsetProbability (sample n M) P₀ +
            (finsetProbability (sample n M) P₁ +
              (finsetProbability (sample n M) P₂ +
                finsetProbability (sample n M) P₃)) :=
          add_le_add le_rfl (add_le_add le_rfl
            (finsetProbability_or_le_add _ _ _))
        _ = _ := by ring
    _ ≤ _ := by
      have h₀ := sampled_exists_degree_lower_factor_sample_le
        n M a hn ha0 ha1 hM
      have h₁ := sampled_exists_degree_upper_factor_sample_le
        n M B hn hB hM
      have h₂ := sampled_exists_codegree_six_sample_le n M hn hM
      have h₃ := degreeAggregateRegular_compl_le n M q etaDeg Bdeg
        hn hq0 hq1 hetaDeg hBdeg hM
      have h₁' : finsetProbability (sample n M) P₁ ≤
          (3 * n : ℝ) *
            (2 * Real.exp
              (((M : ℝ) / n) * (B - 1 - B * Real.log B))) := by
        calc
          finsetProbability (sample n M) P₁ =
              finsetProbability (sample n M)
                (DegreeUpperFailure n M B) := by
            apply finsetProbability_congr_event
            intro H hH
            rfl
          _ ≤ _ := h₁
      exact add_le_add (add_le_add (add_le_add h₀ h₁') h₂) h₃

end

end Erdos747
