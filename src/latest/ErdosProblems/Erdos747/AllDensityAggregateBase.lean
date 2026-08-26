import ErdosProblems.Erdos747.AggregateSubsetConcentration
import ErdosProblems.Erdos747.AggregateBaseRegularity

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Aggregate base regularity at every sampling density -/

lemma degreeAggregateRegular_compl_le_allDensity
    (n M : ℕ) (q eta B : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heta0 : 0 ≤ eta)
    (hB : 1 ≤ B) :
    finsetProbability (sample n M)
        (fun H ↦ ¬ DegreeAggregateRegular n M q eta B H) ≤
      (2 : ℝ)^(3 * n) *
          (8 * (((allEdges n).card + 1 : ℝ) *
            Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) +
        (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
          Real.exp (((M : ℝ) / n) *
            (B - 1 - B * Real.log B))) := by
  let P : Finset (Edge n) → Prop := fun H ↦
    eta * (3 * n : ℝ) <
      (degreeRelativeBadVertices n M q H).card
  let Q : Finset (Edge n) → Prop := fun H ↦
    H ∈ allDensityDegreeUpperFailureSet n M B
  have hcontain : finsetProbability (sample n M)
      (fun H ↦ ¬ DegreeAggregateRegular n M q eta B H) ≤
      finsetProbability (sample n M) (fun H ↦ P H ∨ Q H) := by
    apply finsetProbability_mono_event
    intro H hHs hfail
    unfold DegreeAggregateRegular at hfail
    push Not at hfail
    by_cases hbad : ((degreeRelativeBadVertices n M q H).card : ℝ) ≤
        eta * (3 * n : ℝ)
    · apply Or.inr
      dsimp only [Q]
      rw [mem_allDensityDegreeUpperFailureSet_iff]
      obtain ⟨v, hv⟩ := hfail hbad
      exact ⟨hHs, v, hv.le⟩
    · exact Or.inl (lt_of_not_ge hbad)
  calc
    finsetProbability (sample n M)
        (fun H ↦ ¬ DegreeAggregateRegular n M q eta B H) ≤
      finsetProbability (sample n M) (fun H ↦ P H ∨ Q H) := hcontain
    _ ≤ finsetProbability (sample n M) P +
        finsetProbability (sample n M) Q :=
      finsetProbability_or_le_add _ _ _
    _ ≤ (2 : ℝ)^(3 * n) *
          (8 * (((allEdges n).card + 1 : ℝ) *
            Real.exp (-(q^2 * eta^2 * (M : ℝ) / 64)))) +
        (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
          Real.exp (((M : ℝ) / n) *
            (B - 1 - B * Real.log B))) := by
      exact add_le_add
        (degreeRelativeBadVertices_large_probability_le_allDensity
          n M q eta hn hM0 hM hq0 hq1 heta0)
        (allDensityDegreeUpperFailureSet_probability_le
          n M B hn hM hB)

/-- A materialized failure set for a general integral codegree cutoff. -/
noncomputable def allDensityCodegreeCapFailureSet
    (n M codegCap : ℕ) : Finset (Finset (Edge n)) :=
  ((Finset.univ : Finset (Vertex n)).product
      (Finset.univ : Finset (Vertex n))).biUnion fun p ↦
    (sample n M).filter fun H ↦
      p.1 ≠ p.2 ∧ codegCap + 1 ≤ vertexCodegree H p.1 p.2

lemma mem_allDensityCodegreeCapFailureSet_iff
    (n M codegCap : ℕ) (H : Finset (Edge n)) :
    H ∈ allDensityCodegreeCapFailureSet n M codegCap ↔
      H ∈ sample n M ∧ ∃ u v : Vertex n, u ≠ v ∧
        codegCap < vertexCodegree H u v := by
  classical
  simp only [allDensityCodegreeCapFailureSet, Finset.mem_biUnion,
    Finset.mem_product, Finset.mem_univ, and_self,
    Finset.mem_filter, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, -, hHs, huv, hcodeg⟩
    change codegCap + 1 ≤ vertexCodegree H u v at hcodeg
    exact ⟨hHs, u, v, huv, by omega⟩
  · rintro ⟨hHs, u, v, huv, hcodeg⟩
    refine ⟨(u, v), by simp, hHs, huv, ?_⟩
    change codegCap + 1 ≤ vertexCodegree H u v
    omega

def CodegreeCapPairFailure (n codegCap : ℕ)
    (p : Vertex n × Vertex n) (H : Finset (Edge n)) : Prop :=
  p.1 ≠ p.2 ∧ codegCap + 1 ≤ vertexCodegree H p.1 p.2

lemma codegreeCapPairFailure_probability_le
    (n M codegCap : ℕ) (theta : ℝ) (p : Vertex n × Vertex n)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (CodegreeCapPairFailure n codegCap p) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) *
              (Real.exp theta - 1) - theta * (codegCap + 1)) := by
  by_cases huv : p.1 = p.2
  · have hzero : finsetProbability (sample n M)
        (CodegreeCapPairFailure n codegCap p) = 0 := by
      unfold finsetProbability
      have hempty : (sample n M).filter
          (CodegreeCapPairFailure n codegCap p) = ∅ := by
        ext H
        simp [CodegreeCapPairFailure, huv]
      rw [hempty]
      simp
    rw [hzero]
    positivity
  · calc
      finsetProbability (sample n M)
          (CodegreeCapPairFailure n codegCap p) =
        finsetProbability (sample n M)
          (fun H ↦ (codegCap : ℝ) + 1 ≤
            vertexCodegree H p.1 p.2) := by
        apply finsetProbability_congr_event
        intro H hHs
        simp only [CodegreeCapPairFailure, huv, ne_eq, not_false_eq_true,
          true_and]
        exact_mod_cast Iff.rfl
      _ ≤ _ := sampledVertexCodegree_upper_tail_exp_le
        n M p.1 p.2 theta ((codegCap : ℝ) + 1) huv hn hM htheta

lemma allDensityCodegreeCapFailureSet_probability_le
    (n M codegCap : ℕ) (theta : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityCodegreeCapFailureSet n M codegCap) ≤
      ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) *
              (Real.exp theta - 1) - theta * (codegCap + 1))) := by
  let I := (Finset.univ : Finset (Vertex n)).product
    (Finset.univ : Finset (Vertex n))
  let F : Vertex n × Vertex n → Finset (Finset (Edge n)) := fun p ↦
    (sample n M).filter (CodegreeCapPairFailure n codegCap p)
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) I F (fun p _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  have hdef : I.biUnion F =
      allDensityCodegreeCapFailureSet n M codegCap := by
    ext H
    simp [I, F, allDensityCodegreeCapFailureSet, CodegreeCapPairFailure]
  have hIcard : I.card = (3 * n)^2 := by simp [I, pow_two]
  have hbase' : finsetProbability (sample n M)
      (fun H ↦ H ∈ allDensityCodegreeCapFailureSet n M codegCap) ≤
        ∑ p ∈ I, finsetProbability (sample n M)
          (fun H ↦ H ∈ F p) := by
    simpa only [hdef.symm] using hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityCodegreeCapFailureSet n M codegCap) ≤
      ∑ p ∈ I, finsetProbability (sample n M)
        (fun H ↦ H ∈ F p) := hbase'
    _ ≤ ∑ _p ∈ I, (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) *
              (Real.exp theta - 1) - theta * (codegCap + 1))) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        finsetProbability (sample n M) (fun H ↦ H ∈ F p) =
            finsetProbability (sample n M)
              (CodegreeCapPairFailure n codegCap p) := by
          apply finsetProbability_congr_event
          intro H hHs
          simp [F, hHs]
        _ ≤ _ := codegreeCapPairFailure_probability_le
          n M codegCap theta p hn hM htheta
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hIcard]
      norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]

def allDensityAggregateLayerFailureBound
    (n M codegCap : ℕ) (a B q etaDeg Bdeg theta : ℝ) : ℝ :=
  (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
      Real.exp (((M : ℝ) / n) *
        (a - 1 - a * Real.log a))) +
  (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
      Real.exp (((M : ℝ) / n) *
        (B - 1 - B * Real.log B))) +
  ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
      Real.exp ((M : ℝ) *
        (2 / ((n : ℝ) * (3 * n - 1))) *
          (Real.exp theta - 1) - theta * (codegCap + 1))) +
  ((2 : ℝ)^(3 * n) *
      (8 * (((allEdges n).card + 1 : ℝ) *
        Real.exp (-(q^2 * etaDeg^2 * (M : ℝ) / 64)))) +
    (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
      Real.exp (((M : ℝ) / n) *
        (Bdeg - 1 - Bdeg * Real.log Bdeg))))

/-- The full aggregate layer certificate has an explicit failure bound on
every nonempty fixed-size layer, with no sparse-collision hypothesis. -/
lemma aggregateLayerRegular_compl_le_allDensity
    (n M codegCap : ℕ) (a B q etaDeg Bdeg theta : ℝ)
    (hn : 0 < n) (hM0 : 0 < M) (hM : M ≤ (allEdges n).card)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hetaDeg0 : 0 ≤ etaDeg)
    (hBdeg : 1 ≤ Bdeg) (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ ¬ AggregateLayerRegular n M codegCap
          a B q etaDeg Bdeg H) ≤
      allDensityAggregateLayerFailureBound
        n M codegCap a B q etaDeg Bdeg theta := by
  let P₀ : Finset (Edge n) → Prop := fun H ↦
    H ∈ allDensityDegreeLowerFailureSet n M a
  let P₁ : Finset (Edge n) → Prop := fun H ↦
    H ∈ allDensityDegreeUpperFailureSet n M B
  let P₂ : Finset (Edge n) → Prop := fun H ↦
    H ∈ allDensityCodegreeCapFailureSet n M codegCap
  let P₃ : Finset (Edge n) → Prop := fun H ↦
    ¬ DegreeAggregateRegular n M q etaDeg Bdeg H
  have hcontain : finsetProbability (sample n M)
      (fun H ↦ ¬ AggregateLayerRegular n M codegCap
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
            vertexCodegree H u v ≤ codegCap
        · exact Or.inr (Or.inr (Or.inr (fun hagg ↦
            hfail ⟨hlow, hupper, hcodeg, hagg⟩)))
        · have hp2 : P₂ H := by
            push Not at hcodeg
            obtain ⟨u, v, huv, hcap⟩ := hcodeg
            dsimp only [P₂]
            rw [mem_allDensityCodegreeCapFailureSet_iff]
            exact ⟨hHs, u, v, huv, hcap⟩
          exact Or.inr (Or.inr (Or.inl hp2))
      · have hp1 : P₁ H := by
          push Not at hupper
          dsimp only [P₁]
          rw [mem_allDensityDegreeUpperFailureSet_iff]
          exact ⟨hHs, hupper⟩
        exact Or.inr (Or.inl hp1)
    · have hp0 : P₀ H := by
        push Not at hlow
        dsimp only [P₀]
        rw [mem_allDensityDegreeLowerFailureSet_iff]
        exact ⟨hHs, hlow⟩
      exact Or.inl hp0
  calc
    finsetProbability (sample n M)
        (fun H ↦ ¬ AggregateLayerRegular n M codegCap
          a B q etaDeg Bdeg H) ≤
      finsetProbability (sample n M)
        (fun H ↦ P₀ H ∨ P₁ H ∨ P₂ H ∨ P₃ H) := hcontain
    _ ≤ finsetProbability (sample n M) P₀ +
        finsetProbability (sample n M)
          (fun H ↦ P₁ H ∨ P₂ H ∨ P₃ H) :=
      finsetProbability_or_le_add _ _ _
    _ ≤ finsetProbability (sample n M) P₀ +
        (finsetProbability (sample n M) P₁ +
          finsetProbability (sample n M) (fun H ↦ P₂ H ∨ P₃ H)) :=
      add_le_add le_rfl (finsetProbability_or_le_add _ _ _)
    _ ≤ finsetProbability (sample n M) P₀ +
        (finsetProbability (sample n M) P₁ +
          (finsetProbability (sample n M) P₂ +
            finsetProbability (sample n M) P₃)) :=
      add_le_add le_rfl (add_le_add le_rfl
        (finsetProbability_or_le_add _ _ _))
    _ = finsetProbability (sample n M) P₀ +
        finsetProbability (sample n M) P₁ +
        finsetProbability (sample n M) P₂ +
        finsetProbability (sample n M) P₃ := by
      ring
    _ ≤ allDensityAggregateLayerFailureBound
        n M codegCap a B q etaDeg Bdeg theta := by
      unfold allDensityAggregateLayerFailureBound
      exact add_le_add
        (add_le_add
          (add_le_add
            (allDensityDegreeLowerFailureSet_probability_le
              n M a hn hM ha0 ha1)
            (allDensityDegreeUpperFailureSet_probability_le
              n M B hn hM hB))
          (allDensityCodegreeCapFailureSet_probability_le
            n M codegCap theta hn hM htheta))
        (degreeAggregateRegular_compl_le_allDensity
          n M q etaDeg Bdeg hn hM0 hM hq0 hq1 hetaDeg0 hBdeg)

end

end Erdos747
