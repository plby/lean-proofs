import Arxiv.Arxiv2411_18291.LocalTypicalityProbability
import Arxiv.Arxiv2411_18291.RankOneVertices

/-! # The local typicality lemma, including deterministic rank-one graphs

Every rank-one graph is exactly typical at every neighborhood order. Combining
this with the first local probability estimate covers `R*h ≥ 15`.
`FullLocalTypicality` subsequently proves the local threshold in all ranks.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem commonNeighbors_singleton_rankOne (G : Hypergraph V 1) (S : Block V 0) :
    commonNeighbors G {S} = vertexSupport G := by
  have hS : S.val = ∅ := card_eq_zero.mp S.property
  ext v
  simp only [mem_commonNeighbors, mem_singleton, forall_eq]
  constructor
  · intro hv
    obtain ⟨hnot, he⟩ := (mem_neighbors G S v).mp hv
    exact subset_vertexSupport he (by simp only [extendBlock, mem_insert, true_or])
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    have hnot : v ∉ S.val := by simp [hS]
    refine (mem_neighbors G S v).mpr ⟨hnot, ?_⟩
    have heq : extendBlock S v hnot = e := by
      apply Subtype.ext
      simp only [extendBlock, hS, insert_empty_eq, one_block_eq_singleton hve]
    exact heq.symm ▸ he

theorem rankOne_isTypical (G : Hypergraph V 1) (h : ℕ) : IsTypical G 0 h := by
  intro A _
  by_cases hA : A = ∅
  · simp [hA, commonNeighbors]
  · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hA
    have hcard : A.card ≤ 1 := by
      simpa only [Block, Fintype.card_finset_len, Nat.choose_zero_right] using card_le_univ A
    have hAs : A = {S} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr hS)
      (by simpa only [card_singleton] using hcard)).symm
    rw [hAs, commonNeighbors_singleton_rankOne, card_vertexSupport_rankOne]
    simp only [card_singleton, pow_one, zero_mul]
    by_cases hn : Fintype.card V = 0
    · have hG : G.card = 0 := Nat.eq_zero_of_le_zero (hn ▸ card_rankOne_le G)
      simp [density, hn, hG]
    · have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
      simp only [density, Nat.zero_add, Nat.choose_one_right,
        mul_div_cancel₀ _ hnR, sub_self, abs_zero, le_refl]

theorem rankOne_typical_probability {n h : ℕ} {c : ℝ} (hc : 0 ≤ c) (p : unitInterval) :
    (BernoulliSubset.probability (Block (Fin n) 1) p).real
      {ω | IsTypical (sampleGraph ω) c h} = 1 := by
  have hevent : {ω : BernoulliSubset.Sample (Block (Fin n) 1) |
      IsTypical (sampleGraph ω) c h} = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro ω
    exact (rankOne_isTypical (sampleGraph ω) h).mono hc le_rfl
  rw [hevent, probReal_univ]

theorem typical_local_threshold_of_covered_parameters {r h n : ℕ}
    (hh : 1 ≤ h) (hcovered : r = 0 ∨ 15 ≤ (r + 1) * h)
    (hn : 2 ^ (9 * ((r + 1) * h)) ≤ n)
    (p : unitInterval) (hp : (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | IsTypical (sampleGraph ω) ((n : ℝ) ^ (-(1 / 10 : ℝ))) h} := by
  by_cases hr : r = 0
  · subst r
    rw [rankOne_typical_probability (Real.rpow_nonneg (Nat.cast_nonneg n) _) p]
    linarith only [Real.exp_pos (-((n : ℝ) ^ (1 / 10 : ℝ)))]
  · have hk : 15 ≤ (r + 1) * h := hcovered.resolve_left hr
    have hf := typical_paper_whp_corrected_local_threshold (by omega) hh hk hn p hp
    exact hf.trans_le (measureReal_mono (by intro ω hω; exact hω.2))

end Arxiv2411_18291
