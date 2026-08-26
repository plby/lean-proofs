import ErdosProblems.Erdos556.DenseCore
import ErdosProblems.Erdos556.Separation

/-!
# Connectivity of a minimal dense core

A small separator would split the core into two large parts. Minimality
bounds their edge counts, and the quadratic margin exceeds the edges that
can be incident with the separator.
-/

namespace Erdos556

open SimpleGraph Finset

theorem connectedAfterDeleting_of_minimal_quadratic_density
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℕ) (k η : ℝ) (hk : 0 ≤ k) (hη : 0 ≤ η) (hbk : (b : ℝ) ≤ k)
    (hbudget : (b : ℝ) * Fintype.card V ≤ 2 * η * (k - b) ^ 2)
    (he : k * Fintype.card V + η * (Fintype.card V : ℝ) ^ 2 < (G.edgeFinset.card : ℝ))
    (hdeg : ∀ v, k < (G.degree v : ℝ))
    (hsmall : ∀ T : Finset V, T.card < Fintype.card V →
      ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤ k * T.card + η * (T.card : ℝ) ^ 2) :
    ConnectedAfterDeleting G b := by
  classical
  intro S hS
  by_contra hconn
  obtain ⟨A, B, hA, hB, hAB, hAS, hBS, hcover, hcross⟩ :=
    exists_separation_of_not_preconnected G S hconn
  have hASBS : Disjoint (A ∪ B) S := Finset.disjoint_union_left.mpr ⟨hAS, hBS⟩
  have hcards : A.card + B.card + S.card = Fintype.card V := by
    have h := congrArg Finset.card hcover
    simpa only [card_union_of_disjoint hASBS, card_union_of_disjoint hAB, card_univ] using h
  have hApos := hA.card_pos
  have hBpos := hB.card_pos
  have heA := hsmall A (by omega)
  have heB := hsmall B (by omega)
  have hSR : (S.card : ℝ) ≤ b := by exact_mod_cast hS
  obtain ⟨a, haA⟩ := hA
  obtain ⟨c, hcB⟩ := hB
  have hda := degree_le_parts_of_separation G A B S hcover hcross a haA
  have hdc := degree_le_parts_of_separation G B A S
    (by rw [union_comm B A]; exact hcover)
    (fun x hx y hy hxy => hcross y hy x hx hxy.symm) c hcB
  have hdaR : (G.degree a : ℝ) ≤ (A.card : ℝ) + S.card := by exact_mod_cast hda
  have hdcR : (G.degree c : ℝ) ≤ (B.card : ℝ) + S.card := by exact_mod_cast hdc
  have ha : k - (b : ℝ) ≤ A.card := by have := hdeg a; linarith
  have hb : k - (b : ℝ) ≤ B.card := by have := hdeg c; linarith
  have hedge := edge_count_le_of_separation G A B S hcover hcross
  have hedgeR : (G.edgeFinset.card : ℝ) ≤
      ((G.induce (A : Set V)).edgeFinset.card : ℝ) +
      ((G.induce (B : Set V)).edgeFinset.card : ℝ) + (S.card : ℝ) * Fintype.card V := by
    exact_mod_cast hedge
  have hbound := quadratic_separator_bound (A.card : ℝ) (B.card : ℝ) (S.card : ℝ)
    (Fintype.card V : ℝ) k (b : ℝ) η (G.edgeFinset.card : ℝ)
    (by positivity) (by positivity) (by positivity) hk hη
    (by exact_mod_cast hcards.symm) hSR hbk ha hb hbudget (by linarith)
  exact (not_le_of_gt he) hbound

theorem exists_connected_quadratic_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (k η : ℝ)
    (hk : 0 ≤ k) (hη : 0 ≤ η) (hbk : (b : ℝ) ≤ k)
    (hbudget : (b : ℝ) * Fintype.card V ≤ 2 * η * (k - b) ^ 2)
    (he : k * Fintype.card V + η * (Fintype.card V : ℝ) ^ 2 < (G.edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ConnectedAfterDeleting (G.induce (S : Set V)) b := by
  classical
  obtain ⟨S, hS, hdense, hdeg, hsmall⟩ :=
    exists_minimal_quadratic_dense_core_internal G k η hη he
  have hcard : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hcardle : (Fintype.card (S : Set V) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective (fun x : (S : Set V) => x.val) Subtype.val_injective
  have hbudget' : (b : ℝ) * Fintype.card (S : Set V) ≤ 2 * η * (k - b) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcardle (Nat.cast_nonneg b)).trans hbudget
  refine ⟨S, hS, hdense, hdeg, ?_⟩
  apply connectedAfterDeleting_of_minimal_quadratic_density (G.induce (S : Set V))
    b k η hk hη hbk hbudget'
  · simpa only [hcard] using hdense
  · exact hdeg
  · intro T hT
    exact hsmall T (by simpa only [hcard] using hT)

#print axioms exists_connected_quadratic_dense_core

/-- A dense induced subset is enough to find the connected core. The output
is selected among subsets of the original graph, so no nested vertex type
is needed by the later bipartite-core argument. -/
theorem exists_connected_quadratic_dense_core_of_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (k η : ℝ)
    (hk : 0 ≤ k) (hη : 0 ≤ η) (hbk : (b : ℝ) ≤ k)
    (hbudget : (b : ℝ) * Fintype.card V ≤ 2 * η * (k - b) ^ 2)
    (A : Finset V)
    (he : k * A.card + η * (A.card : ℝ) ^ 2 < ((G.induce (A : Set V)).edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ConnectedAfterDeleting (G.induce (S : Set V)) b := by
  classical
  obtain ⟨S, hS, hdense, hdeg, hsmall⟩ :=
    exists_minimal_quadratic_dense_core_internal_of_subset G k η hη A he
  have hcard : Fintype.card (S : Set V) = S.card := by
    calc
      Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = S.card := Set.ncard_coe_finset S
  have hcardle : (Fintype.card (S : Set V) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective (fun x : (S : Set V) => x.val) Subtype.val_injective
  have hbudget' : (b : ℝ) * Fintype.card (S : Set V) ≤ 2 * η * (k - b) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcardle (Nat.cast_nonneg b)).trans hbudget
  refine ⟨S, hS, hdense, hdeg, ?_⟩
  apply connectedAfterDeleting_of_minimal_quadratic_density (G.induce (S : Set V))
    b k η hk hη hbk hbudget'
  · simpa only [hcard] using hdense
  · exact hdeg
  · intro T hT
    exact hsmall T (by simpa only [hcard] using hT)

#print axioms exists_connected_quadratic_dense_core_of_subset

end Erdos556
