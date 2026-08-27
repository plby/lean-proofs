import ErdosProblems.Erdos4.FGKMTAssignedRounds

/-! Finite covering with one legal choice per source, from lower degree bounds. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

theorem neg_log_half_le_one : -Real.log (1 / 2 : ℝ) ≤ 1 := by
  rw [one_div, Real.log_inv, neg_neg]
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hh
  exact hh

variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

theorem source_covering (μ : I → FiniteLaw (Finset V)) {m r : ℕ}
    (hr : 1 ≤ r) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hεδ : ε ≤ δ)
    (hdegree : ∀ v, 4 ≤ vertexDegree μ v)
    (hsize : ∀ i e, 0 < (μ i).weight e → e.card ≤ r)
    (hmarginal : ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ ε)
    (hsquare : (Fintype.card I : ℝ) * ε ^ 2 ≤ δ ^ 2)
    (hpair : ∀ v w, v ≠ w → pairDegree μ v w ≤ δ)
    (hpartition : (m : ℝ) * Fintype.card V *
      Real.exp (-((1 / 2 : ℝ) ^ m) / (6 * ε)) < 1)
    (hsparse : δ ≤ coveringThreshold r (2 * r) ((1 / 2 : ℝ) ^ m)
      (-Real.log (1 / 2 : ℝ)) ^ (4 * 8 ^ m)) :
    ∃ choice : I → Finset V,
      (∀ i, choice i = ∅ ∨ ∃ e, 0 < (μ i).weight e ∧ choice i ⊆ e) ∧
      ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) ≤
        2 * (Fintype.card V : ℝ) * (1 / 2 : ℝ) ^ m := by
  let ν := equalizedFamily μ 4 (by norm_num) hdegree
  have hνdegree : ∀ v, vertexDegree ν v = 4 :=
    equalizedFamily_degree μ 4 (by norm_num) hdegree
  have hνmarginal : ∀ i v, (ν i).prob (fun e => v ∈ e) ≤ ε :=
    fun i v => (equalizedFamily_marginal_le μ 4 (by norm_num) hdegree i v).trans
      (hmarginal i v)
  have hνsupport : ∀ i f, 0 < (ν i).weight f →
      ∃ e, 0 < (μ i).weight e ∧ f ⊆ e :=
    equalizedFamily_support μ 4 (by norm_num) hdegree
  obtain ⟨a, ha⟩ := exists_dyadic_source_partition ν m hε hνdegree hνmarginal hpartition
  let rounds := assignedRounds ν a
  have hroundDegree : ∀ j < m, ∀ v,
      (-Real.log (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ j ≤ vertexDegree (rounds j) v := by
    intro j hj v
    calc
      _ ≤ (1 : ℝ) * (1 / 2 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right neg_log_half_le_one (by positivity)
      _ = (1 / 2 : ℝ) ^ j := one_mul _
      _ ≤ vertexDegree (rounds j) v := by
        rw [show vertexDegree (rounds j) v =
          ∑ i, if a i = some ⟨j, hj⟩ then (ν i).prob (fun e => v ∈ e) else 0 from
            assignedRounds_degree ν a ⟨j, hj⟩ v]
        exact ha ⟨j, hj⟩ v
  have hroundSize : ∀ j < m, ∀ i e, 0 < (rounds j i).weight e → e.card ≤ r := by
    intro j _ i e he
    rcases assignedRounds_support ν a j i e he with hzero | ⟨_, he⟩
    · simp [hzero]
    · obtain ⟨f, hf, hsub⟩ := hνsupport i e he
      exact (Finset.card_le_card hsub).trans (hsize i f hf)
  have hroundMarginal : ∀ j < m, ∀ i v, (rounds j i).prob (fun e => v ∈ e) ≤ ε := by
    intro j _ i v
    exact (assignedRounds_prob_le ν a j i _ (by simp)).trans (hνmarginal i v)
  have hroundPair : ∀ j < m, ∀ v w, v ≠ w → pairDegree (rounds j) v w ≤ δ := by
    intro j _ v w hvw
    exact (assignedRounds_pair_le ν a j v w).trans
      ((equalizedFamily_pairDegree_le μ 4 (by norm_num) hdegree v w).trans (hpair v w hvw))
  have hroundSquare : ∀ j < m, (∑ _i : I, ε ^ 2) ≤ δ ^ 2 := by
    intro j _
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsquare
  obtain ⟨roundChoice, hlegal, hcard⟩ := lower_degree_covering rounds hr
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hδ
    hroundDegree (fun _ _ => ε) hroundSize hroundMarginal
    (fun _ _ _ => hεδ) hroundSquare hroundPair hsparse
  let choice := assignedChoice a roundChoice
  have hcover : coveredThrough roundChoice m ⊆ Finset.univ.biUnion choice :=
    assignedChoice_covers ν a roundChoice hlegal
  refine ⟨choice, ?_, ?_⟩
  · intro i
    rcases assignedChoice_legal ν a roundChoice hlegal i with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr (hνsupport i (choice i) hpos)
  · have hsub : Finset.univ \ Finset.univ.biUnion choice ⊆
        Finset.univ \ coveredThrough roundChoice m := by
      intro v hv
      obtain ⟨hvu, hvnot⟩ := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨hvu, fun hh => hvnot (hcover hh)⟩
    have hcount : ((Finset.univ \ Finset.univ.biUnion choice).card : ℝ) ≤
        ((Finset.univ \ coveredThrough roundChoice m).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcount.trans hcard

end Erdos4.FGKMT
