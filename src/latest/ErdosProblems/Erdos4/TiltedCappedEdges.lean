import ErdosProblems.Erdos4.TiltedCappedLaw
import ErdosProblems.Erdos4.FGKMTSupport
import ErdosProblems.Erdos4.FGKMTIncidence

/-! Capped exact reweighting produces legal edge laws with explicit marginal bounds. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cappedEdgeLaw (ν μ : FiniteLaw (Finset V)) (W : Finset V) :
    FiniteLaw (Finset V) :=
  (cappedLabelLaw ν μ (fun E W => E ⊆ W) W).map (fun e => e.elim ∅ id)

omit [DecidableEq V] in
open Classical in
theorem cappedEdgeLaw_event (ν μ : FiniteLaw (Finset V)) (W : Finset V)
    (P : Finset V → Prop) (hP : ¬P ∅) :
    (cappedEdgeLaw ν μ W).prob P =
      if eventNormalizer ν μ (fun E W => E ⊆ W) W ≤ 2 then
        μ.mean (fun E => if P E then eventWeight ν (fun W => E ⊆ W) W else 0) / 2 else 0 := by
  by_cases hcap : eventNormalizer ν μ (fun E W => E ⊆ W) W ≤ 2
  · rw [if_pos hcap, cappedEdgeLaw, FiniteLaw.prob_map, FiniteLaw.prob_eq_mean]
    simp only [FiniteLaw.mean, cappedLabelLaw, dif_pos hcap, Fintype.sum_option,
      fillSubprob, Option.elim_none, Option.elim_some, id_eq]
    simp only [hP, if_false, mul_zero, zero_add]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro E _
    by_cases hE : P E <;> simp [hE]
  · rw [if_neg hcap, cappedEdgeLaw, FiniteLaw.prob_map]
    simp only [cappedLabelLaw, dif_neg hcap]
    rw [FiniteLaw.prob_eq_mean, FiniteLaw.mean_dirac]
    simp only [Option.elim_none]
    simp only [hP, if_false]

omit [DecidableEq V] in
theorem cappedEdgeLaw_support (ν μ : FiniteLaw (Finset V)) (W E : Finset V)
    (hE : 0 < (cappedEdgeLaw ν μ W).weight E) : E = ∅ ∨ 0 < μ.weight E ∧ E ⊆ W := by
  classical
  obtain ⟨e, he, heq⟩ := FiniteLaw.map_support
    (cappedLabelLaw ν μ (fun E W => E ⊆ W) W) (fun e => e.elim ∅ id) E hE
  cases e with
  | none => exact Or.inl heq.symm
  | some e =>
    have heq' : e = E := heq
    subst e
    refine Or.inr ⟨?_, cappedLabelLaw_support ν μ _ W E he⟩
    by_contra hμ
    have hz : μ.weight E = 0 := le_antisymm (le_of_not_gt hμ) (μ.nonneg E)
    rw [← prob_eq_weight, cappedLabelLaw_some] at he
    simp only [hz, zero_mul, zero_div, ite_self, lt_self_iff_false] at he

theorem cappedEdgeLaw_event_le (ν μ : FiniteLaw (Finset V)) (W : Finset V)
    (P : Finset V → Prop) (hP : ¬P ∅) {B : ℝ} (hB : 0 ≤ B)
    (hinv : ∀ E, 0 < μ.weight E → 1 / survival ν E ≤ B) :
    (cappedEdgeLaw ν μ W).prob P ≤ (B / 2) * μ.prob P := by
  classical
  rw [cappedEdgeLaw_event ν μ W P hP]
  split_ifs
  · calc
      _ ≤ μ.mean (fun E => if P E then B else 0) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply μ.mean_mono_support
        intro E hE
        by_cases hPE : P E
        · simp only [if_pos hPE]
          unfold eventWeight
          split_ifs
          · exact hinv E hE
          · exact hB
        · simp only [if_neg hPE]
          exact le_rfl
      _ = _ := by rw [mean_indicator_const]; ring
  · exact mul_nonneg (div_nonneg hB (by norm_num)) (μ.prob_nonneg P)

noncomputable def edgeRawIncidence (ν μ : FiniteLaw (Finset V)) (v : V) (W : Finset V) : ℝ :=
  μ.mean (fun E => if v ∈ E then eventWeight ν (fun W => E ⊆ W) W else 0)

open Classical in
noncomputable def edgeLostIncidence (ν μ : FiniteLaw (Finset V)) (v : V) (W : Finset V) : ℝ :=
  if 2 < eventNormalizer ν μ (fun E W => E ⊆ W) W then edgeRawIncidence ν μ v W else 0

theorem edgeRawIncidence_nonneg (ν μ : FiniteLaw (Finset V)) (v : V) (W : Finset V) :
    0 ≤ edgeRawIncidence ν μ v W := by
  apply μ.mean_nonneg
  intro E
  split_ifs
  · exact eventWeight_nonneg ν _ W
  · exact le_rfl

theorem edgeLostIncidence_nonneg (ν μ : FiniteLaw (Finset V)) (v : V) (W : Finset V) :
    0 ≤ edgeLostIncidence ν μ v W := by
  unfold edgeLostIncidence
  split_ifs
  · exact edgeRawIncidence_nonneg ν μ v W
  · exact le_rfl

theorem cappedEdgeLaw_vertex (ν μ : FiniteLaw (Finset V)) (W : Finset V) (v : V) :
    (cappedEdgeLaw ν μ W).prob (fun E => v ∈ E) =
      (edgeRawIncidence ν μ v W - edgeLostIncidence ν μ v W) / 2 := by
  classical
  rw [cappedEdgeLaw_event ν μ W (fun E => v ∈ E) (by simp)]
  unfold edgeLostIncidence edgeRawIncidence
  by_cases h : eventNormalizer ν μ (fun E W => E ⊆ W) W ≤ 2
  · simp only [if_pos h, if_neg (not_lt.mpr h), sub_zero]
    congr 1
    apply μ.mean_congr
    intro E
    by_cases hv : v ∈ E <;> simp only [hv, if_true, if_false]
  · simp only [if_neg h, if_pos (lt_of_not_ge h), sub_self, zero_div]

variable {I : Type*} [Fintype I]

noncomputable def exactRawDegree (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (v : V) (W : Finset V) : ℝ := ∑ i, edgeRawIncidence ν (μ i) v W

noncomputable def exactLostDegree (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (v : V) (W : Finset V) : ℝ := ∑ i, edgeLostIncidence ν (μ i) v W

theorem cappedEdgeLaw_degree (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (v : V) (W : Finset V) :
    vertexDegree (fun i => cappedEdgeLaw ν (μ i) W) v =
      (exactRawDegree ν μ v W - exactLostDegree ν μ v W) / 2 := by
  simp only [vertexDegree, cappedEdgeLaw_vertex, exactRawDegree, exactLostDegree,
    ← Finset.sum_div, Finset.sum_sub_distrib]

theorem cappedEdgeLaw_pairDegree_le (ν : FiniteLaw (Finset V)) (μ : I → FiniteLaw (Finset V))
    (W : Finset V) (v w : V) {B : ℝ} (hB : 0 ≤ B)
    (hinv : ∀ i E, 0 < (μ i).weight E → 1 / survival ν E ≤ B) :
    pairDegree (fun i => cappedEdgeLaw ν (μ i) W) v w ≤ (B / 2) * pairDegree μ v w := by
  classical
  unfold pairDegree
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => cappedEdgeLaw_event_le ν (μ i) W
    (fun E => v ∈ E ∧ w ∈ E) (by simp) hB (hinv i))

end Erdos4.Tilted
