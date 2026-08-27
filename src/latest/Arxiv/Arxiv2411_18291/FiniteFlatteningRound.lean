import Arxiv.Arxiv2411_18291.FiniteGeneratorSplitting
import Arxiv.Arxiv2411_18291.ExplicitBalancedRepresentatives
import Arxiv.Arxiv2411_18291.FiniteUniformElimination
import Arxiv.Arxiv2411_18291.RootedEliminationReduction
import Arxiv.Arxiv2411_18291.GeneratorSplittingIntersections
import Arxiv.Arxiv2411_18291.GeneratorSplittingBounds
import Arxiv.Arxiv2411_18291.FlatteningRecurrence
import Arxiv.Arxiv2411_18291.FlatteningRoundConstants

/-!
# A finite multiplicity-reduction round, uniformly in the input density

Split the input, group only old edges with multiplicity greater than 16,
choose balanced representatives, and place all elimination exchanges.
This preserves the integer span and replaces a multiplicity bound `x`
by `max 16 (2*sqrt(x)+4)`, with a fixed loss in boundary degree.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

theorem exists_uniform_flattening_round_paper_threshold {n : ℕ}
    (S : ExchangeSystem W q (r + 1)) {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (E : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair E N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hwS : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hwE : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hE : E.graph.card ≤ absorberExchangeEdges q (r + 1)) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) ≤ θ)
    (hhi : θ ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)))
    (x : ℕ) (hxn : x ≤ n) (D : Finset (Block (Fin n) q)) (hD : IsCliqueFamilyBounded r D θ)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ x) :
    ∃ D' : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D' (flatteningRoundConstant q r * θ) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy D' J) ∧
      ∀ e : Block (Fin n) (r + 1), (D'.filter fun Q => e.val ⊆ Q.val).card ≤
        flatteningStep x := by
  classical
  let K : ℝ := 3 + 8 * (r + 1).factorial * S.graph.card
  let C : ℝ := (7 + 4 * ((q - r : ℕ) : ℝ) + 24 * (r + 1).factorial * E.graph.card) * K
  have hK : 3 ≤ K := by
    have h : (0 : ℝ) ≤ 8 * (r + 1).factorial * S.graph.card := by positivity
    dsimp only [K]
    linarith only [h]
  have hSr : (S.graph.card : ℝ) ≤ absorberExchangeEdges q (r + 1) := by exact_mod_cast hS
  have hEr : (E.graph.card : ℝ) ≤ absorberExchangeEdges q (r + 1) := by exact_mod_cast hE
  have hCbound : C ≤ flatteningRoundConstant q r := by
    dsimp only [C, K, flatteningRoundConstant]
    push_cast
    gcongr
  have hSb := hS.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)
  have hEb := hE.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hρ : 3 * paperAlpha q (r + 1) / 5 ≤ (2 / 5 : ℝ) := by linarith only [hαupper]
  have hgreedylo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαupper])).trans hlo
  have hexp : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])
  have hpower : (1 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega))
  have hgreedyhi : θ ≤
      (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    (hhi.trans hexp).trans (le_mul_of_one_le_left (Real.rpow_nonneg hnpos.le _) hpower)
  have hKbound : 3 * K ≤ (4 * q : ℝ) ^ (24 * q) := by
    dsimp only [K]
    exact_mod_cast flattening_round_scale_constant hqr hSb
  have hθ : 0 < θ := (Real.rpow_pos_of_pos hnpos _).trans_le hlo
  have hKθ : 0 < K * θ := mul_pos (by linarith only [hK]) hθ
  have hθK : θ ≤ K * θ := by nlinarith only [hK, hθ]
  have hθ3K : θ ≤ 3 * K * θ := by nlinarith only [hK, hθ]
  obtain ⟨F⟩ := exists_generator_splitting_paper_threshold S hqr hn hwS hSb
    hgreedylo hgreedyhi D hD
  have hF : IsCliqueFamilyBounded r F.cliques (K * θ) := by
    convert F.cliques_bounded hD using 1
    dsimp only [K]
    ring
  have hH : IsGraphBounded F.graph (3 * K * θ) := by
    apply F.bounded.mono
    dsimp only [K]
    have hg : 0 ≤ (S.graph.card : ℝ) * (4 * (r + 1).factorial * θ) := by positivity
    nlinarith only [hθ, hg]
  let B₀ := cliqueSupport (r + 1) D
  let B := B₀.filter fun e => 16 < (F.cliques.filter fun P => e.val ⊆ P.val).card
  have hB : B ⊆ B₀ := filter_subset _ _
  have hsingle (P : Block (Fin n) q) (hP : P ∈ F.cliques) :
      (cliqueEdges (r + 1) P ∩ B₀).card ≤ 1 := F.clique_inter_card_le_one hA hP
  obtain ⟨R⟩ := exists_rooted_clique_grouping_sqrt F.cliques B
    (fun P hP => (card_le_card (show cliqueEdges (r + 1) P ∩ B ⊆
        cliqueEdges (r + 1) P ∩ B₀ from fun e he =>
          mem_inter.mpr ⟨(mem_inter.mp he).1, hB (mem_inter.mp he).2⟩)).trans (hsingle P hP)) x
    (fun e he => (F.clique_count_original e (hB he)).trans (hmult e))
  have hsize (c : Finset (Block (Fin n) q)) (hc : c ∈ R.groups) : c.card ≤ n.sqrt + 1 :=
    (R.size c hc).trans (Nat.add_le_add_right (Nat.sqrt_le_sqrt hxn) 1)
  obtain ⟨Q, hQ, hrep⟩ := exists_balanced_clique_representatives_paper_threshold
    hqr hn hρ (hlo.trans hθK) F.cliques hF
    R.groups R.nonempty R.subset R.disjoint hsize
  let I := GroupEliminationIndex R.groups Q
  let P : I → Block (Fin n) q := fun i => Q i.1
  let T : I → Block (Fin n) q := fun i => i.2.val
  have hPmem (i : I) : P i ∈ F.cliques := R.subset i.1.val i.1.property (hQ i.1)
  have hTmem (i : I) : T i ∈ F.cliques :=
    groupEliminationRight_mem F.cliques R.groups R.subset Q i
  have hsupport (i : I) :
      cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (T i) ⊆ F.graph := by
    apply union_subset
    · exact fun e he => F.cliques_support (mem_biUnion.mpr ⟨P i, hPmem i, he⟩)
    · exact fun e he => F.cliques_support (mem_biUnion.mpr ⟨T i, hTmem i, he⟩)
  have hp (t : Block (Fin n) r) : (familyDegree P t.val : ℝ) < (3 * K * θ) * n := by
    have hcount : (familyDegree P t.val : ℝ) ≤ (representativeDegree R.groups Q t.val : ℝ) := by
      exact_mod_cast groupEliminationLeft_degree_le R.groups Q t.val
    have hh := hcount.trans (hrep t)
    have hpos := mul_pos hKθ hnpos
    nlinarith only [hh, hpos]
  have ht (t : Block (Fin n) r) : (familyDegree T t.val : ℝ) < (3 * K * θ) * n := by
    have hcount := groupEliminationRight_degree_le F.cliques R.groups R.subset R.disjoint Q t.val
    have hface := face_clique_count_le_boundary_degree hqr.le F.cliques t
    have hc : (familyDegree T t.val : ℝ) ≤
        ((degree (boundary (r + 1) (indicator F.cliques)) t.val : ℤ) : ℝ) := by
      exact_mod_cast (Int.ofNat_le.mpr hcount).trans hface
    have hf := hF t
    simp only [Fintype.card_fin] at hf
    have hpos := mul_pos hKθ hnpos
    nlinarith only [hc, hf, hpos]
  have hinter (i : I) : ∃ e : Block (Fin n) (r + 1), (P i).val ∩ (T i).val = e.val := by
    refine ⟨(R.root i.1).val, F.same_root_inter hA (hPmem i) (hTmem i) ?_
      (hB (R.root i.1).property) ?_ ?_⟩
    · exact (mem_erase.mp i.2.property).1.symm
    · exact (mem_cliqueEdges _ _).mpr (R.root_mem i.1 (Q i.1) (hQ i.1))
    · exact (mem_cliqueEdges _ _).mpr
        (R.root_mem i.1 i.2.val (mem_erase.mp i.2.property).2)
  have hupper : 3 * K * θ ≤
      (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    (mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 3 * K)).trans
      (mul_le_mul hKbound hexp (Real.rpow_nonneg hnpos.le _) (by positivity))
  obtain ⟨L⟩ := exists_uniform_elimination_family_paper_threshold E N e₀ hpair hqr hn hwE hEb
    (hgreedylo.trans hθ3K) hupper F.graph hH I P T hsupport hp ht hinter
  refine ⟨groupEliminationRetained F.cliques R.groups Q ∪ L.cliques, ?_,
    fun J hJ => L.grouped_generation R Q hQ hpair (F.generated hJ), ?_⟩
  · have hh := L.grouped_bounded R Q hpair hqr.le hKθ.le hF
      (by simpa only [Fintype.card_fin] using hrep)
    have hb : IsCliqueFamilyBounded r
        (groupEliminationRetained F.cliques R.groups Q ∪ L.cliques) (C * θ) := by
      convert hh using 1
      dsimp only [C]
      ring
    exact hb.mono (mul_le_mul_of_nonneg_right hCbound hθ.le)
  · intro e
    have hlow (f : Block (Fin n) (r + 1)) (hf : f ∈ B₀) (hfB : f ∉ B) :
        (F.cliques.filter fun P => f.val ⊆ P.val).card ≤ 16 := by
      have hnot : ¬16 < (F.cliques.filter fun P => f.val ⊆ P.val).card :=
        fun h => hfB (mem_filter.mpr ⟨hf, h⟩)
      omega
    have hh := L.grouped_multiplicity R Q hQ hpair hB subset_union_left
      F.cliques_support hsingle hlow F.clique_count_outside e
    simpa only [flatteningStep, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hh

end Arxiv2411_18291
