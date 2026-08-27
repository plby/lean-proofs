import Arxiv.Arxiv2411_18291.CappedFurtherNumerics
import Arxiv.Arxiv2411_18291.VariableFurtherPairCounts

/-! # Constructing the further universal cancellation at the paper threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_capped_further_elimination_paper_threshold
    {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {D : Finset (Block (Fin n) q)} {B : Hypergraph (Fin n) (r + 1)}
    {C : Block (Fin n) q → ℕ}
    (F : VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hF : IsCliqueFamilyBounded r F.cliques
      ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))))
    (hcap : ∀ e : Block (Fin n) (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60))
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e : Block U (r + 1))
    (hpair : IsEliminationPair T N e) (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q))
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative
      ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) +
        T.graph.card * (4 * (r + 1).factorial *
          (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)))))
    (L : VariableFurtherEliminationPairs F E) :
    Nonempty (EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
      ((n : ℝ) ^ (-(5 * paperAlpha q (r + 1) / 18)))) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  let θ : ℝ := (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45))
  let a : ℝ := furtherVariableCoefficient q r T.graph.card
  have hθ : 0 < θ := Real.rpow_pos_of_pos hn0 _
  have ha : a = 4 * q.choose (r + 1) + 2 * ((q - r : ℕ) : ℝ) +
      2 * (1 + T.graph.card * (4 * (r + 1).factorial)) := by
    simp only [a, furtherVariableCoefficient, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
  have hpow : (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60) *
      (n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180)) = θ := by
    dsimp only [θ]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  obtain ⟨hP, hQ⟩ := L.pair_degree_bounds hA hpair hqr.le
    (Real.rpow_pos_of_pos hn0 _) hcap hF
  simp only [Fintype.card_fin, hpow] at hP hQ
  have hP' (s : Block (Fin n) r) :
      (familyDegree L.positive s.val : ℝ) < (a * θ) * n := by
    apply (hP s).trans_le
    apply mul_le_mul_of_nonneg_right _ hn0.le
    apply mul_le_mul_of_nonneg_right _ hθ.le
    rw [ha]
    have hp : (0 : ℝ) ≤ 2 * ((q - r : ℕ) : ℝ) +
        2 * (1 + T.graph.card * (4 * (r + 1).factorial)) := by positivity
    linarith only [hp]
  have hQ' (s : Block (Fin n) r) :
      (familyDegree (fun i : E.badNegative => i.val) s.val : ℝ) < (a * θ) * n := by
    apply (hQ s).trans_le
    apply mul_le_mul_of_nonneg_right _ hn0.le
    change 2 * ((q - r : ℕ) : ℝ) * θ +
      2 * (θ + T.graph.card * (4 * (r + 1).factorial * θ)) ≤ a * θ
    rw [ha]
    nlinarith only [mul_nonneg (Nat.cast_nonneg (q.choose (r + 1)) : (0 : ℝ) ≤ _) hθ.le]
  have hB : IsGraphBounded E.graph (a * θ) := by
    apply E.bounded.mono
    have hc : (1 + T.graph.card * (4 * (r + 1).factorial) : ℝ) ≤ a := by
      dsimp only [a]
      exact_mod_cast first_le_furtherVariableCoefficient q r T.graph.card
    calc
      _ = (1 + T.graph.card * (4 * (r + 1).factorial)) * θ := by dsimp only [θ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hθ.le
  have hsupport (i : E.badNegative) :
      cliqueEdges (r + 1) (L.positive i) ∪ cliqueEdges (r + 1) i.val ⊆ E.graph := by
    intro f hf
    rcases mem_union.mp hf with hp | hq
    · exact mem_union_left _ (F.cliques_support
        (mem_biUnion.mpr ⟨_, L.positive_mem_cliques i, hp⟩))
    · apply E.cliques_support hpair
      refine mem_biUnion.mpr ⟨i.val, ?_, hq⟩
      rw [E.cliques_eq_signs]
      exact mem_union_right _ (mem_sdiff.mp i.property).1
  obtain ⟨hlo, hhi⟩ := capped_further_input_interval hqr hn hT
  obtain ⟨G⟩ := exists_uniform_elimination_family_paper_threshold T N e hpair hqr hn hw hT
    hlo hhi E.graph hB E.badNegative L.positive (fun i => i.val) hsupport hP' hQ'
    (fun i => ⟨L.edge i, L.vertex_inter i⟩)
  exact ⟨{ G with bounded := G.bounded.mono (capped_further_output_density hqr hn hT) }⟩

end Arxiv2411_18291
