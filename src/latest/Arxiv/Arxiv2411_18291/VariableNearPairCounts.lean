import Arxiv.Arxiv2411_18291.VariableNearCancellationPairs
import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots

/-! # Near cancellation partners are counted at their single original edge

The partner bound is M, rather than choose(q,R)*M. The real-valued form
retains a growing power bound without introducing a rounded capacity.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem repeated_clique_degree_le_real
    {I V : Type*} [Fintype I] [DecidableEq V] {q : ℕ}
    (D : Finset (Block V q)) (Q : I → Block V q) (hQ : ∀ i, Q i ∈ D) {M : ℝ}
    (hrep : ∀ P, ((univ.filter fun i => Q i = P).card : ℝ) ≤ M) (S : Finset V) :
    (familyDegree Q S : ℝ) ≤ M * (D.filter fun P => S ⊆ P.val).card := by
  classical
  let s := univ.filter fun i => S ⊆ (Q i).val
  let d := D.filter fun P => S ⊆ P.val
  have hmap : ∀ i ∈ s, Q i ∈ d :=
    fun i hi => mem_filter.mpr ⟨hQ i, (mem_filter.mp hi).2⟩
  have hfiber (P : Block V q) : ((s.filter fun i => Q i = P).card : ℝ) ≤ M := by
    have hh : ((s.filter fun i => Q i = P).card : ℝ) ≤
        (univ.filter fun i => Q i = P).card := by
      exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ s))
    exact hh.trans (hrep P)
  calc
    _ = ∑ P ∈ d, ((s.filter fun i => Q i = P).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _P ∈ d, M := sum_le_sum fun P _ => hfiber P
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ M : ℝ}

theorem VariableSplittingFamily.near_pair_positive_count_le
    (F : VariableSplittingFamily S D B C θ) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A) (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M) (Q : Block V q) :
    ((univ.filter fun i : F.NearPairs => F.pairPositive i = Q).card : ℝ) ≤ M := by
  by_cases hQ : Q ∈ F.positiveNear
  · obtain ⟨e, _, he⟩ := F.positiveNear_inter hA hQ
    have hcount : (univ.filter fun i : F.NearPairs => F.pairPositive i = Q).card ≤
        (F.cliques.filter fun R => e.val ⊆ R.val).card := by
      apply card_le_card_of_injOn F.pairNegative
      · intro i hi
        obtain ⟨d, hd⟩ := i.property
        have hdB := F.opposite_near_edge_original i.val.1.property i.val.2.property
          (mem_inter.mp hd).1 (mem_inter.mp hd).2
        have hdQ : d ∈ cliqueEdges (r + 1) Q := by
          rw [← (mem_filter.mp hi).2]
          exact (mem_inter.mp hd).2
        have hde : d = e := by
          have hh := mem_inter.mpr ⟨hdQ, hdB⟩
          rwa [he, mem_singleton] at hh
        refine mem_filter.mpr ⟨F.pairNegative_mem i, ?_⟩
        rw [← hde]
        exact (mem_cliqueEdges _ _).mp (mem_inter.mp hd).1
      · intro i hi j hj hij
        exact F.near_pair_injective
          (Prod.ext (((mem_filter.mp hi).2).trans ((mem_filter.mp hj).2).symm) hij)
    exact (by exact_mod_cast hcount :
      ((univ.filter fun i : F.NearPairs => F.pairPositive i = Q).card : ℝ) ≤
        (F.cliques.filter fun R => e.val ⊆ R.val).card).trans (hcap e)
  · have hz : (univ.filter fun i : F.NearPairs => F.pairPositive i = Q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hQ ((mem_filter.mp hi).2 ▸ i.val.2.property)
    simpa only [hz, card_empty, Nat.cast_zero] using hM

theorem VariableSplittingFamily.near_pair_negative_count_le
    (F : VariableSplittingFamily S D B C θ) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A) (hM : 0 ≤ M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M) (Q : Block V q) :
    ((univ.filter fun i : F.NearPairs => F.pairNegative i = Q).card : ℝ) ≤ M := by
  by_cases hQ : Q ∈ F.negativeNear
  · obtain ⟨e, _, he⟩ := F.negativeNear_inter hA hQ
    have hcount : (univ.filter fun i : F.NearPairs => F.pairNegative i = Q).card ≤
        (F.cliques.filter fun R => e.val ⊆ R.val).card := by
      apply card_le_card_of_injOn F.pairPositive
      · intro i hi
        obtain ⟨d, hd⟩ := i.property
        have hdB := F.opposite_near_edge_original i.val.1.property i.val.2.property
          (mem_inter.mp hd).1 (mem_inter.mp hd).2
        have hdQ : d ∈ cliqueEdges (r + 1) Q := by
          rw [← (mem_filter.mp hi).2]
          exact (mem_inter.mp hd).1
        have hde : d = e := by
          have hh := mem_inter.mpr ⟨hdQ, hdB⟩
          rwa [he, mem_singleton] at hh
        refine mem_filter.mpr ⟨F.pairPositive_mem i, ?_⟩
        rw [← hde]
        exact (mem_cliqueEdges _ _).mp (mem_inter.mp hd).2
      · intro i hi j hj hij
        exact F.near_pair_injective
          (Prod.ext hij (((mem_filter.mp hi).2).trans ((mem_filter.mp hj).2).symm))
    exact (by exact_mod_cast hcount :
      ((univ.filter fun i : F.NearPairs => F.pairNegative i = Q).card : ℝ) ≤
        (F.cliques.filter fun R => e.val ⊆ R.val).card).trans (hcap e)
  · have hz : (univ.filter fun i : F.NearPairs => F.pairNegative i = Q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hQ ((mem_filter.mp hi).2 ▸ i.val.1.property)
    simpa only [hz, card_empty, Nat.cast_zero] using hM

theorem VariableSplittingFamily.near_pair_degree_bounds
    (F : VariableSplittingFamily S D B C θ) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A) (hqr : r + 1 ≤ q) (hM : 0 < M)
    (hcap : ∀ e : Block V (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ M)
    {δ : ℝ} (hF : IsCliqueFamilyBounded r F.cliques δ) :
    (∀ T : Block V r, (familyDegree F.pairPositive T.val : ℝ) <
      (M * δ) * Fintype.card V) ∧
    (∀ T : Block V r, (familyDegree F.pairNegative T.val : ℝ) <
      (M * δ) * Fintype.card V) := by
  have hbound (P : F.NearPairs → Block V q) (hP : ∀ i, P i ∈ F.cliques)
      (hrep : ∀ Q, ((univ.filter fun i => P i = Q).card : ℝ) ≤ M) (T : Block V r) :
      (familyDegree P T.val : ℝ) < (M * δ) * Fintype.card V := by
    have hcount := repeated_clique_degree_le_real F.cliques P hP hrep T.val
    have hdegree : ((F.cliques.filter fun Q => T.val ⊆ Q.val).card : ℝ) ≤
        ((degree (boundary (r + 1) (indicator F.cliques)) T.val : ℤ) : ℝ) := by
      exact_mod_cast face_clique_count_le_boundary_degree hqr F.cliques T
    have hface := hdegree.trans_lt (hF T)
    exact hcount.trans_lt (by simpa only [mul_assoc] using mul_lt_mul_of_pos_left hface hM)
  exact ⟨hbound F.pairPositive F.pairPositive_mem
    (F.near_pair_positive_count_le hA hM.le hcap),
    hbound F.pairNegative F.pairNegative_mem (F.near_pair_negative_count_le hA hM.le hcap)⟩

end Arxiv2411_18291
