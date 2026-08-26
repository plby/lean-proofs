import ErdosProblems.Erdos19.QuantitativePackingRound
import ErdosProblems.Erdos19.PackingSequence
import ErdosProblems.Erdos19.PackingLoadBounds

/-! # Packing a sequence of prescribed even vertex sets

This theorem uses numerical margins on one fixed reservoir, not a separate
existence assumption for each successive matching.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_prescribed_matching_packing
    (G R : _root_.SimpleGraph V) (hRG : R ≤ G)
    (A : ℕ → Set V) (m a r c q K b : ℕ)
    (hn : 0 < Fintype.card V) (hm : m ≤ Fintype.card V)
    (heven : ∀ i < m, Even (A i).ncard)
    (hsmall : ∀ i < m, (A i)ᶜ.ncard ≤ a)
    (habs : ∀ v, ∑ i ∈ range m, (if v ∈ A i then 0 else 1) ≤ a)
    (hri : r + m + 3 * a ≤ Fintype.card V)
    (hsize : Fintype.card V ≤ c * (Fintype.card V - r - m - 3 * a + 1))
    (hbad : Fintype.card V ≤ K * (b + 1))
    (hb : b ≤ Fintype.card V - r - m - 3 * a)
    (hmargin : 2 * q + 2 * b +
      7 * (c * (5 * a + packingLoadBound (Fintype.card V) a c K m + 1)) +
      2 * a + packingLoadBound (Fintype.card V) a c K m + 1 ≤ r)
    (hG : ∀ v, Fintype.card V ≤ (G.neighborSet v).ncard + a)
    (hRlo : ∀ v, r ≤ (R.neighborSet v).ncard + a)
    (hRhi : ∀ v, (R.neighborSet v).ncard ≤ r + a)
    (hcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q * (packingLoadBound (Fintype.card V) a c K m + 1) <
        (R.between (X : Set V) (Y : Set V)).edgeSet.ncard) :
    ∃ M : Fin m → G.Subgraph,
      (∀ i, (M i).IsMatching ∧ (M i).verts = A i) ∧
      Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  classical
  have aux : ∀ i ≤ m, ∃ U : _root_.SimpleGraph V,
      IsMatchingPacking G A i U ∧ IsLoadBalanced K (reservoirLoad U R) ∧
      totalLoad (reservoirLoad U R) ≤ packingTotalBound (Fintype.card V) a c K i := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨⊥, IsMatchingPacking.nil, ?_, ?_⟩
      · intro v
        simp [reservoirLoad]
      · simp [totalLoad, reservoirLoad, packingTotalBound]
    | succ i ih =>
      intro hi
      have him : i < m := by omega
      obtain ⟨U, hpack, hbalanced, htotal⟩ := ih (by omega)
      let L := packingLoadBound (Fintype.card V) a c K i
      have hL : L ≤ packingLoadBound (Fintype.card V) a c K m :=
        packingLoadBound_monotone _ a c K him.le
      have hload : ∀ v, reservoirLoad U R v ≤ L :=
        hbalanced.le_packingLoadBound _ a c K i hn htotal
      obtain ⟨hUlo, hUhi⟩ := hpack.degree_bounds m a him.le habs
      have hri' : r + i + 3 * a ≤ Fintype.card V := by omega
      have hsize' : Fintype.card V ≤ c * (Fintype.card V - r - i - 3 * a + 1) :=
        hsize.trans (Nat.mul_le_mul_left c (by omega))
      have hb' : b ≤ Fintype.card V - r - i - 3 * a := by omega
      have hmargin' : 2 * q + 2 * b + 7 * (c * (5 * a + L + 1)) + 2 * a + L + 1 ≤ r := by
        have hmul := Nat.mul_le_mul_left (7 * c) hL
        nlinarith only [hmargin, hmul, hL]
      have hcut' : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
          q * (L + 1) < (R.between (X : Set V) (Y : Set V)).edgeSet.ncard := by
        intro X Y hXY hX hY
        exact (Nat.mul_le_mul_left q (Nat.add_le_add_right hL 1)).trans_lt (hcut X Y hXY hX hY)
      obtain ⟨N, hN, hNA, hdis, hbal, hsum⟩ := exists_balanced_matching_packing_round
        G U R hRG hpack.used_le (A i) (heven i him) a r i L c q K b
        hn (hsmall i him) hri' hsize' hbad hb' hmargin' hG hRlo hRhi hUlo hUhi hload hbalanced hcut'
      refine ⟨U ⊔ N.spanningCoe, hpack.snoc N hN hNA hdis, hbal, ?_⟩
      rw [packingTotalBound_succ]
      exact hsum.trans (Nat.add_le_add_right htotal _)
  obtain ⟨U, hpack, _, _⟩ := aux m le_rfl
  obtain ⟨M, hM, hp⟩ := hpack.exists_family
  exact ⟨M, fun i ↦ ⟨(hM i).1, (hM i).2.1⟩, hp⟩

#print axioms exists_prescribed_matching_packing

end Erdos19
