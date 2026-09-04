import ErdosProblems.Erdos19.PackingRound
import ErdosProblems.Erdos19.PackingDegrees
import ErdosProblems.Erdos19.ReservoirCuts

/-! # A packing round from explicit degree and load margins -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_balanced_matching_packing_round
    (G U R : _root_.SimpleGraph V) (hRG : R ≤ G) (hUG : U ≤ G)
    (A : Set V) (heven : Even A.ncard) (a r i L c q K b : ℕ)
    (hn : 0 < Fintype.card V) (hsmall : Aᶜ.ncard ≤ a)
    (hri : r + i + 3 * a ≤ Fintype.card V)
    (hsize : Fintype.card V ≤ c * (Fintype.card V - r - i - 3 * a + 1))
    (hbad : Fintype.card V ≤ K * (b + 1))
    (hb : b ≤ Fintype.card V - r - i - 3 * a)
    (hmargin : 2 * q + 2 * b + 7 * (c * (5 * a + L + 1)) + 2 * a + L + 1 ≤ r)
    (hG : ∀ v, Fintype.card V ≤ (G.neighborSet v).ncard + a)
    (hRlo : ∀ v, r ≤ (R.neighborSet v).ncard + a)
    (hRhi : ∀ v, (R.neighborSet v).ncard ≤ r + a)
    (hUlo : ∀ v, i ≤ (U.neighborSet v).ncard + a)
    (hUhi : ∀ v, (U.neighborSet v).ncard ≤ i)
    (hload : ∀ v, reservoirLoad U R v ≤ L)
    (hbalanced : IsLoadBalanced K (reservoirLoad U R))
    (hcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q * (L + 1) < (R.between (X : Set V) (Y : Set V)).edgeSet.ncard) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts = A ∧ Disjoint U N.spanningCoe ∧
      IsLoadBalanced K (reservoirLoad (U ⊔ N.spanningCoe) R) ∧
      totalLoad (reservoirLoad (U ⊔ N.spanningCoe) R) ≤
        totalLoad (reservoirLoad U R) + 3 * (c * (5 * a + L + 1)) := by
  classical
  let Q := (G \ (R ⊔ U)).between A A
  let : DecidableRel Q.Adj := fun x y ↦ Classical.propDecidable (Q.Adj x y)
  let B := overloadedVertices K (reservoirLoad U R)
  have hB : B.card ≤ b := by
    have h := (overloadedVertices_card_mul_lt K (reservoirLoad U R) hn).trans_le hbad
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left h)
  have hload' : ∀ v, ((R ⊓ U).neighborSet v).ncard ≤ L := by
    intro v
    simpa only [reservoirLoad, inf_comm] using hload v
  obtain ⟨hmin', hmax'⟩ := active_base_degree_bounds G R U hRG hUG A a r i L
    hsmall hri hG hRlo hRhi hUlo hUhi hload'
  have hmin : ∀ v ∈ A, Fintype.card V - r - i - 3 * a ≤ Q.degree v := by
    intro v hv
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hmin' v hv
  have hmax : ∀ v, Q.degree v ≤ Fintype.card V - r - i + 2 * a + L := by
    intro v
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hmax' v
  have hdegree : ∀ v ∈ A,
      2 * q + 2 * B.card + 7 * (c * (5 * a + L + 1)) + Aᶜ.ncard + 1 ≤ (R \ U).degree v := by
    intro v _
    have hd := available_reservoir_degree_lower R U r a L hRlo hload' v
    have hd' : 2 * q + 2 * B.card + 7 * (c * (5 * a + L + 1)) + Aᶜ.ncard + 1 ≤
        ((R \ U).neighborSet v).ncard := by omega
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hd'
  obtain ⟨N, T, hN, hNA, hNU, hT, hTB, hsupp⟩ := exists_matching_packing_round G U R Q hRG
    between_le A heven (between_self_support_subset _ A) B
    (Fintype.card V - r - i - 3 * a) (Fintype.card V - r - i + 2 * a + L)
    (c * (5 * a + L + 1)) q hmin hmax (hB.trans hb)
    (active_base_uncovered_bound A a r i L c hri hsize) hdegree
    (reservoir_cut_survives_loads R U q L hload' hcut)
  obtain ⟨hbal, htotal⟩ := reservoirLoad_step U R N hN hNU T hsupp K hbalanced hTB
  exact ⟨N, hN, hNA, hNU, hbal, htotal.trans (Nat.add_le_add_left hT _)⟩

#print axioms exists_balanced_matching_packing_round

end Erdos19
