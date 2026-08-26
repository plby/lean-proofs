import ErdosProblems.Erdos19.DilutedSpoiling
import ErdosProblems.Erdos19.ColorCoverCounting

/-! # An exact lower bound for tentative collision colors under dilution -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

noncomputable def pairOtherNeighbors {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (v p q : V) : Finset V :=
  ((G.neighborSet v).toFinset.erase p).erase q

def dilutedTentativePairEvent {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A)
    (v p q : V) (a : Fin C) : Set (V → Fin A × Fin C) :=
  {sample | sample p = (active, a) ∧ sample q = (active, a) ∧
    ∀ z ∈ pairOtherNeighbors G v p q, sample z ≠ (active, a)}

theorem pairOtherNeighbors_card {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (v p q : V) (hpq : p ≠ q)
    (hp : G.Adj v p) (hq : G.Adj v q) :
    (pairOtherNeighbors G v p q).card = (G.neighborSet v).ncard - 2 := by
  classical
  have hp' : p ∈ (G.neighborSet v).toFinset := Set.mem_toFinset.mpr hp
  have hq' : q ∈ (G.neighborSet v).toFinset.erase p :=
    mem_erase.mpr ⟨hpq.symm, Set.mem_toFinset.mpr hq⟩
  simp only [pairOtherNeighbors, card_erase_of_mem hq', card_erase_of_mem hp',
    Set.toFinset_card, Set.fintypeCard_eq_ncard]
  omega

theorem card_dilutedTentativePairEvent {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A)
    (v p q : V) (a : Fin C) (hpq : p ≠ q) (hp : G.Adj v p) (hq : G.Adj v q) :
    (eventFinset (dilutedTentativePairEvent G active v p q a)).card =
      (A * C - 1) ^ ((G.neighborSet v).ncard - 2) *
        (A * C) ^ (Fintype.card V - ((G.neighborSet v).ncard - 2) - 2) := by
  classical
  have hcount := card_fun_eq_two_avoid_finset_generic (active, a)
    (pairOtherNeighbors G v p q) hpq
    (by simp [pairOtherNeighbors]) (by simp [pairOtherNeighbors])
  rw [card_eventFinset_eq_ncard, ← Set.fintypeCard_eq_ncard,
    ← Nat.card_eq_fintype_card (α := ↥(dilutedTentativePairEvent G active v p q a))]
  change Nat.card {sample : V → Fin A × Fin C // sample p = (active, a) ∧
    sample q = (active, a) ∧ ∀ z ∈ pairOtherNeighbors G v p q, sample z ≠ (active, a)} = _
  rw [hcount, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    pairOtherNeighbors_card G v p q hpq hp hq]

theorem dilutedTentativePair_mem_iff {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V)
    (sample : V → Fin A × Fin C) (a : Fin C)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet)
    (he : sample ∈ dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a)
    (x : V) : x ∈ e.1 ↔ G.Adj v x ∧ sample x = (active, a) := by
  have hedge := nonadjacentNeighborPairGraph_edge_out G v e
  rw [← sym2_mk_out_eq e.1, Sym2.mem_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨hedge.2.1, he.1⟩
    · exact ⟨hedge.2.2.1, he.2.1⟩
  · rintro ⟨hx, hcolor⟩
    by_cases hp : x = e.1.out.1
    · exact Or.inl hp
    by_cases hq : x = e.1.out.2
    · exact Or.inr hq
    have hx' : x ∈ pairOtherNeighbors G v e.1.out.1 e.1.out.2 := by
      simp [pairOtherNeighbors, hp, hq, hx]
    exact (he.2.2 x hx' hcolor).elim

theorem dilutedTentativePair_unique {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V)
    (sample : V → Fin A × Fin C) (a : Fin C)
    {e f : (nonadjacentNeighborPairGraph G v).edgeSet}
    (he : sample ∈ dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a)
    (hf : sample ∈ dilutedTentativePairEvent G active v f.1.out.1 f.1.out.2 a) : e = f := by
  apply Subtype.ext
  apply Sym2.ext
  intro x
  rw [dilutedTentativePair_mem_iff G active v sample a e he,
    dilutedTentativePair_mem_iff G active v sample a f hf]

theorem dilutedTentativePair_implies_collision {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V)
    (sample : V → Fin A × Fin C) (a : Fin C)
    (e : (nonadjacentNeighborPairGraph G v).edgeSet)
    (he : sample ∈ dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a) :
    a ∈ tentativeCollisionColors G (dilutedSample active sample) v := by
  have hedge := nonadjacentNeighborPairGraph_edge_out G v e
  refine ⟨e.1.out.1, e.1.out.2, hedge.1, hedge.2.2.2, ?_, ?_⟩
  · exact (mem_diluted_tentativeFiber G active sample v _ a).mpr ⟨hedge.2.1, he.1⟩
  · exact (mem_diluted_tentativeFiber G active sample v _ a).mpr ⟨hedge.2.2.1, he.2.1⟩

theorem dilutedTentativeCollision_expectation_lower_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V) :
    C * (nonadjacentNeighborPairGraph G v).edgeSet.ncard *
      ((A * C - 1) ^ ((G.neighborSet v).ncard - 2) *
        (A * C) ^ (Fintype.card V - ((G.neighborSet v).ncard - 2) - 2)) ≤
      ∑ sample : V → Fin A × Fin C,
        (tentativeCollisionColors G (dilutedSample active sample) v).ncard := by
  classical
  let E := (nonadjacentNeighborPairGraph G v).edgeSet
  let W (sample : V → Fin A × Fin C) (a : Fin C) : Finset E :=
    univ.filter fun e ↦ sample ∈ dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a
  have hW (sample : V → Fin A × Fin C) (a : Fin C) : (W sample a).card ≤
      if a ∈ tentativeCollisionColors G (dilutedSample active sample) v then 1 else 0 := by
    by_cases ha : a ∈ tentativeCollisionColors G (dilutedSample active sample) v
    · rw [if_pos ha]
      apply card_le_one.mpr
      intro e he f hf
      exact dilutedTentativePair_unique G active v sample a
        (mem_filter.mp he).2 (mem_filter.mp hf).2
    · rw [if_neg ha]
      have hempty : W sample a = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro e he
        exact ha (dilutedTentativePair_implies_collision G active v sample a e (mem_filter.mp he).2)
      simp only [hempty, card_empty, le_refl]
  have hswap : (∑ a : Fin C, ∑ e : E,
      (eventFinset (dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a)).card) =
      ∑ sample : V → Fin A × Fin C, ∑ a : Fin C, (W sample a).card := by
    simp only [eventFinset, card_eq_sum_ones, sum_filter, W]
    conv_lhs =>
      arg 2
      ext a
      rw [sum_comm]
    rw [sum_comm]
  calc
    _ = ∑ a : Fin C, ∑ e : E,
        (eventFinset (dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a)).card := by
      have hcard (a : Fin C) (e : E) :=
        card_dilutedTentativePairEvent G active v e.1.out.1 e.1.out.2 a
          (nonadjacentNeighborPairGraph_edge_out G v e).1
          (nonadjacentNeighborPairGraph_edge_out G v e).2.1
          (nonadjacentNeighborPairGraph_edge_out G v e).2.2.1
      simp only [hcard, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
        Set.fintypeCard_eq_ncard, mul_assoc]
      rfl
    _ = _ := hswap
    _ ≤ ∑ sample : V → Fin A × Fin C,
        ∑ a : Fin C, if a ∈ tentativeCollisionColors G (dilutedSample active sample) v then 1 else 0 :=
      sum_le_sum (fun sample _ ↦ sum_le_sum (fun a _ ↦ hW sample a))
    _ = _ := by simp only [← ncard_eq_sum_indicator]

#print axioms dilutedTentativeCollision_expectation_lower_bound

end Erdos19
