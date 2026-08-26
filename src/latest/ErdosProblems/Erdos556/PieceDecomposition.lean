import ErdosProblems.Erdos556.DecompositionSeparations
import ErdosProblems.Erdos556.SurvivingCore

/-!
# Disjoint large two-connected pieces

For any integer `r ≥ 2`, a graph on `N` vertices has disjoint induced
two-connected pieces, each of order greater than `r`, retaining all but
at most `(r + 1) * N + N² / (r + 1)` edges. We state the bound after
multiplication by `r + 1`, so that all accounting is in natural numbers.
-/

namespace Erdos556

open SimpleGraph Finset

private theorem small_decomposition_bound (r N e : ℕ) (hN : N ≤ r)
    (he : 2 * e ≤ N * N) : (r + 1) * e ≤ (r + 1) ^ 2 * N + N ^ 2 := by
  have h1 := Nat.mul_le_mul_right N hN
  have h2 : e ≤ (r + 1) * N := by nlinarith
  have h3 := Nat.mul_le_mul_left (r + 1) h2
  nlinarith

private theorem small_side_potential (r a b N e f s : ℕ) (hN : a + b = N)
    (he : e ≤ f + a * (r + 1))
    (hf : (r + 1) * f ≤ (r + 1) * s + (r + 1) ^ 2 * b + b ^ 2) :
    (r + 1) * e ≤ (r + 1) * s + (r + 1) ^ 2 * N + N ^ 2 := by
  have h := Nat.mul_le_mul_left (r + 1) he
  nlinarith

universe u

private theorem exists_piece_decomposition_aux (N : ℕ) :
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], Fintype.card V = N →
      ∀ r : ℕ, 2 ≤ r → ∃ P : Finset (Finset V),
        IsTwoConnectedPieceFamily G r P ∧
        (r + 1) * G.edgeFinset.card ≤
          (r + 1) * (∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card) +
            (r + 1) ^ 2 * Fintype.card V + (Fintype.card V) ^ 2 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro V _ _ G _ hcard r hr
      classical
      by_cases hsmall : Fintype.card V ≤ r
      · refine ⟨∅, ⟨by simp, by simp⟩, ?_⟩
        simp only [sum_empty, mul_zero, zero_add]
        apply small_decomposition_bound r (Fintype.card V) G.edgeFinset.card hsmall
        calc
          2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
          _ ≤ ∑ _v : V, Fintype.card V := sum_le_sum fun v _ => (G.degree_lt_card_verts v).le
          _ = Fintype.card V * Fintype.card V := by simp
      by_cases htwo : TwoConnected G
      · let e : G.induce (↑(univ : Finset V) : Set V) ≃g G :=
          (induceSetCongr G _ _ Finset.coe_univ).trans G.induceUnivIso
        have hc : TwoConnected (G.induce (↑(univ : Finset V) : Set V)) :=
          htwo.iso e.symm
        have he : (G.induce (↑(univ : Finset V) : Set V)).edgeFinset.card = G.edgeFinset.card := by
          exact e.card_edgeFinset_eq
        refine ⟨{univ}, ⟨by simp, ?_⟩, ?_⟩
        · intro A hA
          have hA' : A = univ := mem_singleton.mp hA
          subst A
          exact ⟨by simpa only [card_univ] using Nat.lt_of_not_ge hsmall, hc⟩
        · simp only [sum_singleton, he]
          omega
      have hsmallside : ∀ A : Finset V, A.Nonempty → A.card < Fintype.card V →
          (∀ v ∈ A, G.degree v ≤ r + 1) → ∃ P : Finset (Finset V),
          IsTwoConnectedPieceFamily G r P ∧
          (r + 1) * G.edgeFinset.card ≤
            (r + 1) * (∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card) +
              (r + 1) ^ 2 * Fintype.card V + (Fintype.card V) ^ 2 := by
        intro A hA hAlt hdeg
        let T := Aᶜ
        have hTcard : Fintype.card (T : Set V) = T.card := Fintype.card_coe T
        have hsum : A.card + T.card = Fintype.card V := by
          dsimp [T]
          rw [card_compl]
          exact Nat.add_sub_of_le (card_le_univ A)
        have hTlt : Fintype.card (T : Set V) < N := by
          have hpos := card_pos.mpr hA
          omega
        obtain ⟨P, hP, heP⟩ := ih (Fintype.card (T : Set V)) hTlt
          (T : Set V) (G.induce (T : Set V)) rfl r hr
        refine ⟨liftPieces T P, hP.lift, ?_⟩
        rw [sum_edges_liftPieces]
        rw [hTcard] at heP
        have he := edge_count_le_induce_compl_add_card_mul_of_degree_bound G A (r + 1) hdeg
        have he' : G.edgeFinset.card ≤ (G.induce (T : Set V)).edgeFinset.card +
            A.card * (r + 1) := by
          have heq := (induceSetCongr G (A : Set V)ᶜ (T : Set V)
            (Finset.coe_compl A).symm).card_edgeFinset_eq
          rw [heq] at he
          exact he
        exact small_side_potential r A.card T.card (Fintype.card V) _ _ _ hsum he' heP
      obtain ⟨A, B, S, hA, hB, hAB, hAS, hBS, hcover, hS, hcross⟩ :=
        exists_small_separation_of_not_twoConnected G (by omega) htwo
      have hsum := card_sum_of_separation A B S hAB hAS hBS hcover
      have hApos := card_pos.mpr hA
      have hBpos := card_pos.mpr hB
      by_cases hAsmall : A.card ≤ r
      · apply hsmallside A hA (by omega)
        intro v hv
        have hd := degree_le_parts_of_separation G A B S hcover hcross v hv
        omega
      by_cases hBsmall : B.card ≤ r
      · apply hsmallside B hB (by omega)
        intro v hv
        have hcover' : B ∪ A ∪ S = univ := by rw [union_comm B A]; exact hcover
        have hcross' : ∀ b ∈ B, ∀ a ∈ A, ¬ G.Adj b a :=
          fun b hb a ha hadj => hcross a ha b hb hadj.symm
        have hd := degree_le_parts_of_separation G B A S hcover' hcross' v hv
        omega
      have hAc : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
      have hBc : Fintype.card (B : Set V) = B.card := Fintype.card_coe B
      obtain ⟨P, hP, heP⟩ := ih (Fintype.card (A : Set V)) (by omega)
        (A : Set V) (G.induce (A : Set V)) rfl r hr
      obtain ⟨Q, hQ, heQ⟩ := ih (Fintype.card (B : Set V)) (by omega)
        (B : Set V) (G.induce (B : Set V)) rfl r hr
      have hPQ : Disjoint (liftPieces A P) (liftPieces B Q) :=
        disjoint_liftPieces hAB P Q (fun _ h => hP.nonempty h)
      refine ⟨liftPieces A P ∪ liftPieces B Q, hP.lift.union hQ.lift ?_, ?_⟩
      · intro X hX Y hY
        exact hAB.mono (subset_of_mem_liftPieces hX) (subset_of_mem_liftPieces hY)
      · rw [sum_union hPQ, sum_edges_liftPieces, sum_edges_liftPieces]
        rw [hAc] at heP
        rw [hBc] at heQ
        have hedge := edge_count_le_of_separation G A B S hcover hcross
        have hedge' := Nat.mul_le_mul_left (r + 1) hedge
        have hpot := decomposition_split_potential r A.card B.card S.card (Fintype.card V)
          (by omega) (by omega) hS hsum
        nlinarith only [heP, heQ, hedge', hpot]

theorem exists_piece_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 2 ≤ r) :
    ∃ P : Finset (Finset V), IsTwoConnectedPieceFamily G r P ∧
      (r + 1) * G.edgeFinset.card ≤
        (r + 1) * (∑ A ∈ P, (G.induce (A : Set V)).edgeFinset.card) +
          (r + 1) ^ 2 * Fintype.card V + (Fintype.card V) ^ 2 :=
  exists_piece_decomposition_aux (Fintype.card V) V G rfl r hr

#print axioms exists_piece_decomposition

end Erdos556
