import Arxiv.Arxiv2411_18291.Incidence
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # True decompositions and nonnegative integral decompositions -/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

theorem card_cliqueEdges (Q : Block V q) : (cliqueEdges r Q).card = q.choose r := by
  simpa [cliqueEdges, Q.property] using
    card_blocks_between (r := r) ∅ Q.val (empty_subset _) (Nat.zero_le _)

theorem cliqueEdges_nonempty (hqr : r ≤ q) (Q : Block V q) :
    (cliqueEdges r Q).Nonempty := by
  rw [← card_pos, card_cliqueEdges]
  exact Nat.choose_pos hqr

/-- A clique in a decomposition has all its edges in the host graph. -/
theorem IsDecomposition.clique_subset {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) {Q : Block V q} (hQ : Q ∈ D) : cliqueEdges r Q ⊆ G := by
  intro e he
  have hcount := (isDecomposition_iff G D).mp hD e
  have hpos : 0 < (D.filter fun Q => e.val ⊆ Q.val).card :=
    card_pos.mpr ⟨Q, mem_filter.mpr ⟨hQ, (mem_cliqueEdges e Q).mp he⟩⟩
  by_contra heG
  rw [if_neg heG] at hcount
  omega

/-- Every host edge is in exactly one clique of a decomposition. -/
theorem IsDecomposition.unique {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) {e : Block V r} (he : e ∈ G) :
    ∃! Q : Block V q, Q ∈ D ∧ e.val ⊆ Q.val := by
  have hcount := (isDecomposition_iff G D).mp hD e
  rw [if_pos he] at hcount
  simpa only [mem_filter] using card_eq_one_iff_existsUnique.mp hcount

/-- A nonnegative integral decomposition is a genuine decomposition. The
proof establishes that all its coefficients are zero or one. -/
theorem hasDecomposition_of_nonneg (hqr : r ≤ q) (G : Hypergraph V r)
    (Φ : Block V q → ℤ) (hΦ : boundary r Φ = indicator G)
    (hpos : ∀ Q, 0 ≤ Φ Q) : HasDecomposition q G := by
  have hle (Q : Block V q) : Φ Q ≤ 1 := by
    obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr Q
    have hs : (if e.val ⊆ Q.val then Φ Q else 0) ≤ boundary r Φ e := by
      unfold boundary
      apply single_le_sum (f := fun Q' : Block V q => if e.val ⊆ Q'.val then Φ Q' else 0)
      · intro Q' _
        split_ifs
        · exact hpos Q'
        · exact le_rfl
      · exact mem_univ Q
    rw [if_pos ((mem_cliqueEdges e Q).mp he), hΦ] at hs
    apply hs.trans
    unfold indicator
    split_ifs <;> norm_num
  refine ⟨univ.filter (fun Q => Φ Q = 1), ?_⟩
  have hchar : indicator (univ.filter (fun Q => Φ Q = 1)) = Φ := by
    funext Q
    have h0 := hpos Q
    have h1 := hle Q
    simp only [indicator, mem_filter, mem_univ, true_and]
    split_ifs with h
    · exact h.symm
    · omega
  simpa only [IsDecomposition, hchar] using hΦ

theorem HasDecomposition.union (hqr : r ≤ q) {G H : Hypergraph V r}
    (hG : HasDecomposition q G) (hH : HasDecomposition q H) (h : Disjoint G H) :
    HasDecomposition q (G ∪ H) := by
  obtain ⟨D, hD⟩ := hG
  obtain ⟨E, hE⟩ := hH
  apply hasDecomposition_of_nonneg hqr (G ∪ H) (indicator D + indicator E)
  · rw [boundary_add, hD, hE, indicator_union h]
  · intro Q
    simp only [Pi.add_apply, indicator]
    split_ifs <;> norm_num

/-- A signed representation can be absorbed by a decomposed negative host.
This is the final algebraic step in Section 3's absorber construction. -/
theorem hasDecomposition_of_signed (hqr : r ≤ q)
    {A L : Hypergraph V r} {M P N : Finset (Block V q)}
    (hM : IsDecomposition A M) (hN : N ⊆ M) (hAL : Disjoint A L)
    (hsigned : boundary r (indicator P - indicator N) = indicator L) :
    HasDecomposition q (A ∪ L) := by
  apply hasDecomposition_of_nonneg hqr (A ∪ L) (indicator P + indicator (M \ N))
  · rw [indicator_sdiff hN, boundary_add, boundary_sub, hM, indicator_union hAL]
    rw [boundary_sub] at hsigned
    funext e
    have h := congrFun hsigned e
    simp only [Pi.sub_apply, Pi.add_apply] at h ⊢
    omega
  · intro Q
    simp only [Pi.add_apply, indicator]
    split_ifs <;> norm_num

end Arxiv2411_18291
