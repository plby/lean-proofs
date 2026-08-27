import Arxiv.Arxiv2411_18291.RootedCliquePlacement
import Arxiv.Arxiv2411_18291.SmallPatternGreedy

/-! # Finite decoder regions at flexible density exponents -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem small_clique_pattern_bounds_sharp {q s r : ℕ} (hq : 2 ≤ q) (hs : s ≤ 2 * q) :
    s ≤ (4 * q) ^ (2 * q) ∧ s.choose r ≤ (4 * q) ^ (2 * q) := by
  constructor
  · exact hs.trans ((by omega : 2 * q ≤ 4 * q).trans
      (Nat.le_self_pow (by omega : 2 * q ≠ 0) (4 * q)))
  · calc
      _ ≤ 2 ^ s := Nat.choose_le_two_pow s r
      _ ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by decide : 0 < 2) hs
      _ = 4 ^ q := by rw [pow_mul]; norm_num
      _ ≤ (4 * q) ^ q := Nat.pow_le_pow_left (by omega) q
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem exists_indexed_clique_placement_at_exponent
    {W : Type*} [Fintype W] {q r s n : ℕ} (F₀ : Block W (r + 1))
    (hW : Fintype.card W = s) (hqr : r + 1 < q) (hs : s ≤ 2 * q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (t : ℕ) (E : ℕ → Block (Fin n) (r + 1)) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i)
      (A * (n : ℝ) ^ (-ρ))) :
    ∃ Q : Fin t → Block (Fin n) s,
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun i : Fin t => E i) Q ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        ((1 + 4 * (r + 1).factorial * s.choose (r + 1)) *
          (A * (n : ℝ) ^ (-ρ))) := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let θ := (A * (n : ℝ) ^ (-ρ))
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  obtain ⟨hw, hH⟩ := small_clique_pattern_bounds_sharp (r := r + 1) (by omega : 2 ≤ q) hs
  have hc : (complete W (r + 1)).card = s.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap, one_mul] using hbound
  obtain ⟨Ψ, hΨ⟩ := exists_small_pattern_greedy_family_paper_threshold hqr hn
    (by simpa only [hW] using hw) (complete W (r + 1)) (by simpa only [hc] using hH)
    (complete_root_admissible F₀) hA hAb hρ hρhalf t Φ B hB hroots
  refine ⟨fun i => embeddingClique hW (Ψ i).val,
    hΨ.cliqueCover_complement F₀ hW (fun i => E i) B Ψ hE (fun i => hEB i i.isLt), ?_⟩
  have hL : 0 ≤ 4 * (r + 1).factorial * θ := by dsimp only [θ]; positivity
  have hb := (hΨ.graphBounded hB hL).subgraph
    (cliqueGraph_subset_base_union_new F₀ hW (fun i => E i) B Ψ (fun i => hEB i i.isLt))
  have heq : θ + (complete W (r + 1)).card * (4 * (r + 1).factorial * θ) =
      (1 + 4 * (r + 1).factorial * s.choose (r + 1)) * θ := by rw [hc]; ring
  dsimp only [θ] at heq
  simpa only [heq] using hb

theorem exists_clique_placement_at_exponent {q r s n : ℕ}
    (hqr : r + 1 < q) (hrs : r + 1 ≤ s) (hs : s ≤ 2 * q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ))) :
    ∃ Q : B → Block (Fin n) s,
      IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Q ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        ((1 + 4 * (r + 1).factorial * s.choose (r + 1)) *
          (A * (n : ℝ) ^ (-ρ))) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨f, _, hf⟩ := exists_subset_card_eq (s := (univ : Finset (Fin s)))
    (by simpa only [card_univ, Fintype.card_fin] using hrs)
  let F₀ : Block (Fin s) (r + 1) := ⟨f, hf⟩
  rcases B.eq_empty_or_nonempty with hB0 | hBpos
  · subst B
    let Q : (∅ : Hypergraph (Fin n) (r + 1)) → Block (Fin n) s :=
      fun e => (notMem_empty _ e.property).elim
    have hQ : cliqueCoverGraph (r := r) Q = ∅ := by
      ext e
      simp only [cliqueCoverGraph, mem_biUnion, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨i, _⟩
      exact notMem_empty _ i.property
    refine ⟨Q, ⟨fun e => (notMem_empty _ e.property).elim,
      fun i _ _ => (notMem_empty _ i.property).elim⟩, ?_⟩
    rw [hQ]
    have hnNat : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
    have hx : (0 : ℝ) < n := by exact_mod_cast hnNat
    exact isGraphBounded_empty (by positivity) (by simpa only [Fintype.card_fin] using hnNat)
  · obtain ⟨e₀, _⟩ := hBpos
    let enum : Fin B.card ≃ B := B.equivFin.symm
    let E : ℕ → Block (Fin n) (r + 1) :=
      fun i => if hi : i < B.card then (enum ⟨i, hi⟩).val else e₀
    have hE (i : Fin B.card) : E i = (enum i).val := by
      dsimp [E]
      rw [if_pos i.isLt]
    have hEmem (i : Fin B.card) : E i ∈ B := hE i ▸ (enum i).property
    have hEinj : Function.Injective (fun i : Fin B.card => E i) := by
      intro i j hij
      apply enum.injective
      apply Subtype.ext
      simpa only [hE] using hij
    obtain ⟨Q, hQ, hb⟩ := exists_indexed_clique_placement_at_exponent F₀
      (Fintype.card_fin s) hqr hs hn hA hAb hρ hρhalf B.card E B hB hEinj
      (fun i hi => hEmem ⟨i, hi⟩)
      (hB.edgeFamily (fun i : Fin B.card => E i) hEmem hEinj)
    refine ⟨fun e => Q (enum.symm e), ?_, ?_⟩
    · constructor
      · intro e
        have heq : E (enum.symm e) = e.val := by rw [hE, Equiv.apply_symm_apply]
        simpa only [heq] using hQ.punctured (enum.symm e)
      · intro e f hef
        exact hQ.disjoint (fun h => hef (enum.symm.injective h))
    · rw [cliqueCoverGraph_reindex]
      exact hb

end Arxiv2411_18291
