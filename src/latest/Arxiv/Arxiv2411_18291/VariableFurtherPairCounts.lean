import Arxiv.Arxiv2411_18291.VariableFurtherPartnerSelection
import Arxiv.Arxiv2411_18291.VariableNearPairCounts
import Arxiv.Arxiv2411_18291.EliminationBoundaryBounds

/-! # Further cancellation degrees with a real multiplicity cap

A far positive clique meets the original splitting graph in no edges.
Each of its edges therefore has splitting multiplicity at most two.
Counting first-stage roots at these edges bounds reuse by four times the
number of clique edges times the cap, with no squared multiplicity loss.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' M : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N : Block U q} {e₀ : Block U (r + 1)}
variable {F : VariableSplittingFamily S D B C θ}
variable {E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ'}

theorem VariableSplittingFamily.first_clique_count_outside_original
    (F : VariableSplittingFamily S D B C θ) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    (e : Block V (r + 1)) (he : e ∈ F.graph) (heB : e ∉ B) :
    ((E.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 4 * M := by
  have hsmall : ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ 2 := by
    exact_mod_cast F.clique_count_outside e heB
  have hp := (repeated_clique_degree_le_real F.cliques F.pairPositive
    F.pairPositive_mem (F.near_pair_positive_count_le hA hM hcap) e.val).trans
      (mul_le_mul_of_nonneg_left hsmall hM)
  have hq := (repeated_clique_degree_le_real F.cliques F.pairNegative
    F.pairNegative_mem (F.near_pair_negative_count_le hA hM hcap) e.val).trans
      (mul_le_mul_of_nonneg_left hsmall hM)
  have hE : ((E.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
      (familyDegree F.pairPositive e.val : ℝ) + familyDegree F.pairNegative e.val := by
    exact_mod_cast E.clique_count_original_sharp hpair e he
  linarith only [hp, hq, hE]

theorem VariableFurtherEliminationPairs.positive_count_le
    (L : VariableFurtherEliminationPairs F E) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A) (hpair : IsEliminationPair T N e₀) (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M) (Q : Block V q) :
    ((univ.filter fun i : E.badNegative => L.positive i = Q).card : ℝ) ≤
      4 * q.choose (r + 1) * M := by
  classical
  by_cases hQ : Q ∈ F.positiveFar
  · have hQF : Q ∈ F.cliques := by
      rw [F.cliques_eq_signs]
      exact mem_union_left _ (mem_sdiff.mp hQ).1
    have hc (e : Block V (r + 1)) (he : e ∈ cliqueEdges (r + 1) Q) :
        ((E.cliques.filter fun R => e.val ⊆ R.val).card : ℝ) ≤ 4 * M :=
      F.first_clique_count_outside_original hA E hpair hM hcap e
        (F.cliques_support (mem_biUnion.mpr ⟨Q, hQF, he⟩))
        (fun heB => disjoint_left.mp (F.positiveFar_disjoint_original hQ) he heB)
    have hinj : (univ.filter fun i : E.badNegative => L.positive i = Q).card ≤
        ((cliqueEdges (r + 1) Q).biUnion fun e =>
          E.cliques.filter fun R => e.val ⊆ R.val).card := by
      apply card_le_card_of_injOn Subtype.val
      · intro i hi
        refine mem_biUnion.mpr ⟨L.edge i, ?_, mem_filter.mpr ⟨?_, ?_⟩⟩
        · simpa only [(mem_filter.mp hi).2] using L.edge_positive i
        · rw [E.cliques_eq_signs]
          exact mem_union_right _ (mem_sdiff.mp i.property).1
        · exact (mem_cliqueEdges _ _).mp (L.edge_negative i)
      · exact fun _ _ _ _ hij => Subtype.ext hij
    calc
      _ ≤ ∑ e ∈ cliqueEdges (r + 1) Q,
          ((E.cliques.filter fun R => e.val ⊆ R.val).card : ℝ) := by
        exact_mod_cast hinj.trans card_biUnion_le
      _ ≤ ∑ _e ∈ cliqueEdges (r + 1) Q, 4 * M := sum_le_sum hc
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_cliqueEdges]; ring
  · have hz : (univ.filter fun i : E.badNegative => L.positive i = Q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hQ ((mem_filter.mp hi).2 ▸ L.positive_mem i)
    rw [hz, card_empty, Nat.cast_zero]
    positivity

theorem VariableFurtherEliminationPairs.pair_degree_bounds
    (L : VariableFurtherEliminationPairs F E) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A) (hpair : IsEliminationPair T N e₀)
    (hqr : r + 1 ≤ q) (hM : 0 < M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    {δ : ℝ} (hF : IsCliqueFamilyBounded r F.cliques δ) :
    (∀ s : Block V r, (familyDegree L.positive s.val : ℝ) <
      (4 * q.choose (r + 1) * (M * δ)) * Fintype.card V) ∧
    (∀ s : Block V r, (familyDegree (fun i : E.badNegative => i.val) s.val : ℝ) <
      (2 * ((q - r : ℕ) : ℝ) * (M * δ) + 2 * θ') * Fintype.card V) := by
  classical
  have hk : (0 : ℝ) < q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr
  have hM' : 0 < 4 * (q.choose (r + 1) : ℝ) * M := by positivity
  obtain ⟨hP, hQ⟩ := F.near_pair_degree_bounds hA hqr hM hcap hF
  have hE := E.cliques_bounded_from_degrees hpair (fun s => (hP s).le) (fun s => (hQ s).le)
  constructor
  · intro s
    have hcount := repeated_clique_degree_le_real F.cliques L.positive
      L.positive_mem_cliques (L.positive_count_le hA hpair hM.le hcap) s.val
    have hface : ((F.cliques.filter fun Q => s.val ⊆ Q.val).card : ℝ) ≤
        ((degree (boundary (r + 1) (indicator F.cliques)) s.val : ℤ) : ℝ) := by
      exact_mod_cast face_clique_count_le_boundary_degree hqr F.cliques s
    exact hcount.trans_lt (by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left (hface.trans_lt (hF s)) hM')
  · intro s
    have hcount : familyDegree (fun i : E.badNegative => i.val) s.val ≤
        (E.cliques.filter fun Q => s.val ⊆ Q.val).card := by
      apply card_le_card_of_injOn Subtype.val
      · intro i hi
        refine mem_filter.mpr ⟨?_, (mem_filter.mp hi).2⟩
        rw [E.cliques_eq_signs]
        exact mem_union_right _ (mem_sdiff.mp i.property).1
      · exact fun _ _ _ _ hij => Subtype.ext hij
    have hface : ((E.cliques.filter fun Q => s.val ⊆ Q.val).card : ℝ) ≤
        ((degree (boundary (r + 1) (indicator E.cliques)) s.val : ℤ) : ℝ) := by
      exact_mod_cast face_clique_count_le_boundary_degree hqr E.cliques s
    exact (by exact_mod_cast hcount :
      (familyDegree (fun i : E.badNegative => i.val) s.val : ℝ) ≤
        (E.cliques.filter fun Q => s.val ⊆ Q.val).card).trans_lt (hface.trans_lt (hE s))

end Arxiv2411_18291
