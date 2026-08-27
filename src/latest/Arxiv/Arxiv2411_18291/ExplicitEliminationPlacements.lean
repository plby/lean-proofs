import Arxiv.Arxiv2411_18291.EliminationPlacements
import Arxiv.Arxiv2411_18291.SmallPatternGreedy

/-! # Cancellation placements at the printed finite threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_elimination_placements_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (N : Block W q) (e : Block W (r + 1))
    (hpair : IsEliminationPair S N e) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (M : ℕ) (hM : 0 < M)
    {A ρ : ℝ} (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * M : ℕ) : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M)
    (t : ℕ) (P Q : Fin t → Block (Fin n) q)
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hinter : ∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) :
    ∃ Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n,
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) S.graph B Ψ
          (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
            A * (n : ℝ) ^ (-ρ))) ∧
        (∀ i, mapBlock (Ψ i).val S.base = P i ∧ mapBlock (Ψ i).val N = Q i) ∧
        IsGraphBounded
          (B ∪ greedyFamilyGraph (S.base.val ∪ N.val) S.graph (fun i => (Ψ i).val))
          (A * (n : ℝ) ^ (-ρ) + S.graph.card *
            (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
              A * (n : ℝ) ^ (-ρ)))) := by
  have hK : (1 : ℝ) ≤ (q.choose (r + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hqr.le) hM
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAK : A ≤ ((q.choose (r + 1) * M : ℕ) : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hAnonneg
  have hKA : 1 ≤ ((q.choose (r + 1) * M : ℕ) : ℝ) * A := hA.trans hAK
  have hnW : Fintype.card W ≤ n := hw.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  have hmaps (i : Fin t) : ∃ φ : ↥(S.base.val ∪ N.val) ↪ Fin n,
      rootImage φ S.base subset_union_left = P i ∧ rootImage φ N subset_union_right = Q i := by
    obtain ⟨d, hd⟩ := hinter i
    exact hpair.root_map (P i) (Q i) d hd
  choose φ hφP hφQ using hmaps
  obtain ⟨f₀⟩ := Function.Embedding.nonempty_of_card_le
    (α := W) (β := Fin n) (by simpa only [Fintype.card_fin] using hnW)
  let φ₀ : ↥(S.base.val ∪ N.val) ↪ Fin n :=
    (Function.Embedding.subtype (· ∈ S.base.val ∪ N.val)).trans f₀
  let Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n := fun i =>
    if hi : i < t then φ ⟨i, hi⟩ else φ₀
  have hΦ (i : Fin t) : Φ i = φ i := by
    dsimp only [Φ]
    rw [dif_pos i.isLt]
  have hΦP (i : Fin t) : rootImage (Φ i) S.base subset_union_left = P i := by
    rw [hΦ i]
    exact hφP i
  have hΦQ (i : Fin t) : rootImage (Φ i) N subset_union_right = Q i := by
    rw [hΦ i]
    exact hφQ i
  have hB' : IsGraphBounded B
      (((q.choose (r + 1) * M : ℕ) : ℝ) * A *
        (n : ℝ) ^ (-ρ)) :=
    hB.mono (mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hrel (i : ℕ) (_ : i < t) : (priorRelated (fun _ _ : ℕ => False) i).card ≤ 0 := by
    have hzero : priorRelated (fun _ _ : ℕ => False) i = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      exact ((mem_priorRelated _ _ _).mp hj).2
    rw [hzero, card_empty]
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val ∪ N.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (((q.choose (r + 1) * M : ℕ) : ℝ) * A *
          (n : ℝ) ^ (-ρ)) := by
    intro f hf hroot
    have h := hpair.root_inputs hqr.le hD hM hmult P Q hP hQ hinj (fun i => Φ i)
      hΦP hΦQ f hf hroot
    simpa only [mul_assoc] using h
  obtain ⟨Ψ, hΨ, _⟩ := exists_small_pattern_separated_greedy_family_paper_threshold hqr hn hw
    S.graph hS (hpair.admissible hqr.le) (Nat.zero_le _) hKA
    hAb hρ hρhalf t Φ (fun _ _ => False) B hB' hrel hroots
  refine ⟨Φ, Ψ, hΨ, ?_, hΨ.graphBounded hB (by positivity)⟩
  intro i
  exact pair_extension_roots (Φ i) (hΦP i) (hΦQ i) (Ψ i)

end Arxiv2411_18291
