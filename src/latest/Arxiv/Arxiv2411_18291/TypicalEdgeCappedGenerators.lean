import Arxiv.Arxiv2411_18291.RelativeEdgeCappedGenerators
import Arxiv.Arxiv2411_18291.GoodGeneratorCriterion

/-! # Edge-capped modular generators inside a typical host

The two explicit cap budgets preserve the face-density bound and give
relative error `delta`, while at most a `delta^2` fraction of cliques is
saturated. The edge cap is retained as part of the constructed output.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r h : ℕ}

theorem exists_good_edge_capped_generating_data (N : ℕ) (hN : 0 < N)
    {K : Hypergraph V (r + 1)} {c η θ δ : ℝ}
    (hT : IsTypical K c h) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    (hn : 0 < Fintype.card V) (hp : 0 < density K)
    (hcη : c ≤ η) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density K ^ q.choose (r + 1)))
    (faceCap edgeCap : ℕ) (hfaceCap : 0 < faceCap) (hedgeCap : 0 < edgeCap)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (herror : η * q * 2 ^ q ≤ δ / 2)
    (hθ : ((q - r : ℕ) : ℝ) * faceCap < θ * Fintype.card V)
    (hfaceBudget : (8 * q.choose (r + 1) * q.choose r * N : ℝ) *
      Fintype.card V * density K ≤ faceCap * δ ^ 2)
    (hedgeBudget : (8 * (q.choose (r + 1) : ℝ) ^ 2 * N) ≤ δ ^ 2 * edgeCap) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators θ ∧
      (∀ e : Block V (r + 1),
        (C.generators.filter fun Q => e.val ⊆ Q.val).card ≤ edgeCap) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤ δ ^ 2 * (cliqueFamily K q).card ∧
      ((K \ C.good).card : ℝ) ≤ δ * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)| <
          δ * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1) := by
  let ζ : ℝ := η * q * 2 ^ q
  let μ := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)
  let L := 2 * Fintype.card V * density K * μ
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hμ : 0 < μ := cliqueMainTerm_pos hnR hp _ _ _
  have hζ : ζ ≤ 1 / 2 := by dsimp only [ζ]; linarith only [herror, hδ1]
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hD : ∀ Q ∈ cliqueFamily K q, cliqueEdges (r + 1) Q ⊆ K :=
    fun _ hQ => (mem_filter.mp hQ).2
  have hface (S : Block V r) :
      (((cliqueFamily K q).filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L := by
    let m := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) r
    have hm : 0 ≤ m := cliqueMainTerm_nonneg hnR.le hp.le _ _ _
    have hc := (abs_le.mp (hT.cliqueFamily_small_root_relative hqh hcη hη hη1 hsize S
      (by omega) (Nat.lt_succ_self r))).2
    change _ ≤ ζ * m at hc
    have hb : m ≤ Fintype.card V * density K * μ := cliqueMainTerm_face_le hnR.le hp.le hqr
    calc
      _ ≤ (1 + ζ) * m := by linarith only [hc]
      _ ≤ 2 * m := mul_le_mul_of_nonneg_right (by linarith only [hζ]) hm
      _ ≤ 2 * (Fintype.card V * density K * μ) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = L := by dsimp only [L]; ring
  have hedge (e : Block V (r + 1)) (he : e ∈ K) :
      |(((cliqueFamily K q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ζ * μ :=
    hT.cliqueFamily_edge_relative hqh hcη hη hη1 hsize hqr he
  have hbudget : (4 * q.choose (r + 1) * q.choose r * N : ℝ) * L ≤
      δ ^ 2 * μ * faceCap := by
    have hh := mul_le_mul_of_nonneg_right hfaceBudget hμ.le
    dsimp only [L]
    nlinarith only [hh]
  obtain ⟨C, hF, hE, hcard, hsat, hbad, hcount⟩ :=
    exists_edge_capped_generating_data_relative N hN K (cliqueFamily K q) hD
      faceCap edgeCap hfaceCap hedgeCap hL hμ hδ hδ1 herror hface hedge hbudget hedgeBudget
  refine ⟨C, cliqueFamilyBounded_of_face_load C.generators faceCap hF hθ,
    hE, hcard, ?_, hbad, hcount⟩
  have hk : (0 : ℝ) < q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr
  have hmean := host_clique_mean_le K (cliqueFamily K q) hD hμ.le hζ hedge
  have hm := mul_le_mul_of_nonneg_left hmean (sq_nonneg δ)
  apply (mul_le_mul_iff_right₀ hk).mp
  nlinarith only [hsat, hm]

end Arxiv2411_18291
