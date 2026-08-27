import Arxiv.Arxiv2411_18291.UniformGeneratorSplitting
import Arxiv.Arxiv2411_18291.AsymptoticBalancedRepresentatives
import Arxiv.Arxiv2411_18291.UniformEliminationFamily
import Arxiv.Arxiv2411_18291.RootedEliminationReduction
import Arxiv.Arxiv2411_18291.GeneratorSplittingIntersections
import Arxiv.Arxiv2411_18291.GeneratorSplittingBounds
import Arxiv.Arxiv2411_18291.FlatteningRecurrence
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# One sparse multiplicity-reduction round, uniformly in the input density

Split the input, group only old edges with multiplicity greater than 16,
choose balanced representatives, and place all elimination exchanges.
This preserves the integer span and replaces a multiplicity bound `x`
by `max 16 (2*sqrt(x)+4)`, with a fixed loss in boundary degree.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

theorem eventually_exists_uniform_flattening_round (S : ExchangeSystem W q (r + 1))
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (E : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair E N e₀) (hqr : r + 1 ≤ q)
    {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ : ρ < 1 / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ (n : ℝ) ^ (-σ) →
      ∀ x : ℕ, x ≤ n → ∀ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D θ →
      (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ x) →
      ∃ D' : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D' (C * θ) ∧
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
  have hC : 1 ≤ C := by
    have hcoeff : (7 : ℝ) ≤
        7 + 4 * ((q - r : ℕ) : ℝ) + 24 * (r + 1).factorial * E.graph.card := by
      have h : (0 : ℝ) ≤ 4 * ((q - r : ℕ) : ℝ) +
          24 * (r + 1).factorial * E.graph.card := by positivity
      linarith only [h]
    dsimp only [C]
    nlinarith only [hK, hcoeff]
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_exists_uniform_generator_splitting S hqr hσ hσρ
      (by linarith only [hρ]),
    eventually_exists_balanced_clique_representatives q r hqr hρ,
    eventually_exists_uniform_elimination_family E N e₀ hpair hqr
      (σ := σ / 2) (ρ := ρ) (half_pos hσ)
      (by linarith only [hσ, hσρ]) (by linarith only [hρ]),
    eventually_const_mul_rpow_le (3 * K) (show σ / 2 < σ by linarith only [hσ]),
    eventually_ge_atTop (1 : ℕ)] with n hsplit hbalance helim hscale hn
  intro θ hlo hhi x hxn D hD hmult
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ : 0 < θ := (Real.rpow_pos_of_pos hnpos _).trans_le hlo
  have hKθ : 0 < K * θ := mul_pos (by linarith only [hK]) hθ
  have hθK : θ ≤ K * θ := by nlinarith only [hK, hθ]
  have hθ3K : θ ≤ 3 * K * θ := by nlinarith only [hK, hθ]
  obtain ⟨F⟩ := hsplit θ hlo hhi D hD
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
  obtain ⟨Q, hQ, hrep⟩ := hbalance (K * θ) (hlo.trans hθK) F.cliques hF
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
    have hface := face_clique_count_le_boundary_degree hqr F.cliques t
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
  have hupper : 3 * K * θ ≤ (n : ℝ) ^ (-(σ / 2)) :=
    (mul_le_mul_of_nonneg_left hhi (by positivity : 0 ≤ 3 * K)).trans hscale
  obtain ⟨L⟩ := helim (3 * K * θ) (hlo.trans hθ3K) hupper F.graph hH I P T
    hsupport hp ht hinter
  refine ⟨groupEliminationRetained F.cliques R.groups Q ∪ L.cliques, ?_,
    fun J hJ => L.grouped_generation R Q hQ hpair (F.generated hJ), ?_⟩
  · have hh := L.grouped_bounded R Q hpair hqr hKθ.le hF
      (by simpa only [Fintype.card_fin] using hrep)
    convert hh using 1
    dsimp only [C]
    ring
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
