import ErdosProblems.Erdos577.TriangleLabeling
import ErdosProblems.Erdos577.QuadScores
import ErdosProblems.Erdos577.UnattachedModel
import ErdosProblems.Erdos577.PathModel

/-! Encode an actual triangle remainder and cycle in the weighted finite model. -/

namespace Erdos577.Unattached

open Finset Function
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V}

section Diagonals

variable [DecidableRel G.Adj]

def diagonal (q : Quadrilateral G) : Fin 4 :=
  if G.Adj (q 0) (q 2) then
    if G.Adj (q 1) (q 3) then 3 else 1
  else if G.Adj (q 1) (q 3) then 2 else 0

lemma diagonal_first (q : Quadrilateral G) :
    (diagonal q).val.testBit 0 = true ↔ G.Adj (q 0) (q 2) := by
  by_cases h02 : G.Adj (q 0) (q 2) <;> by_cases h13 : G.Adj (q 1) (q 3) <;>
    simp [diagonal, h02, h13]

lemma diagonal_second (q : Quadrilateral G) :
    (diagonal q).val.testBit 1 = true ↔ G.Adj (q 1) (q 3) := by
  by_cases h02 : G.Adj (q 0) (q 2) <;> by_cases h13 : G.Adj (q 1) (q 3) <;>
    simp only [diagonal, h02, h13, if_true, if_false] <;> decide

variable [DecidableEq V]

lemma oldEdges_diagonal (q : Quadrilateral G) :
    oldEdges (diagonal q) = edgeCount G q.support := by
  rw [q.edgeCount_eq]
  by_cases h02 : G.Adj (q 0) (q 2) <;> by_cases h13 : G.Adj (q 1) (q 3) <;>
    simp only [oldEdges, diagonal, h02, h13, if_true, if_false] <;> decide

end Diagonals

variable [Fintype V] [DecidableEq V]

lemma disjoint_tuples (c : TriangleChain G) (q : Quadrilateral G)
    (h : Disjoint c.remainder q.support) :
    Disjoint (tupleSupport c.remainderTuple) (tupleSupport q.toEmbedding) := by
  rw [c.remainderTuple_support]
  exact h

noncomputable def labeling (c : TriangleChain G) (q : Quadrilateral G)
    (h : Disjoint c.remainder q.support) : Fin 8 ↪ V :=
  joinTuples c.remainderTuple q.toEmbedding (disjoint_tuples c q h)

lemma labeling_left (c : TriangleChain G) (q : Quadrilateral G)
    (h : Disjoint c.remainder q.support) (i : Fin 4) :
    labeling c q h (Fin.castAdd 4 i) = c.remainderTuple i :=
  joinTuples_left c.remainderTuple q.toEmbedding (disjoint_tuples c q h) i

lemma labeling_right (c : TriangleChain G) (q : Quadrilateral G)
    (h : Disjoint c.remainder q.support) (i : Fin 4) :
    labeling c q h (Fin.natAdd 4 i) = q i :=
  joinTuples_right c.remainderTuple q.toEmbedding (disjoint_tuples c q h) i

lemma labeling_image (c : TriangleChain G) (q : Quadrilateral G)
    (h : Disjoint c.remainder q.support) :
    univ.image (labeling c q h) = c.remainder ∪ q.support := by
  change tupleSupport (joinTuples _ _ _) = _
  rw [tupleSupport_joinTuples, c.remainderTuple_support]
  rfl

variable [DecidableRel G.Adj]

noncomputable def bits (c : TriangleChain G) (q : Quadrilateral G) (i : Fin 16) : Bool :=
  decide (G.Adj (c.remainderTuple ⟨i.val / 4, by omega⟩)
    (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

noncomputable def encoded (c : TriangleChain G) (q : Quadrilateral G) : Fin 65536 :=
  ⟨PathExchange.encode (bits c q), PathExchange.encode_lt (bits c q)⟩

lemma encoded_bit (c : TriangleChain G) (q : Quadrilateral G) (i j : Fin 4) :
    (encoded c q).val.testBit (4 * i.val + j.val) =
      decide (G.Adj (c.remainderTuple i) (q j)) := by
  have h := PathExchange.testBit_encode (bits c q) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [encoded, bits, hi, hj, Fin.eta] using h

noncomputable def modelCopy (c : TriangleChain G) (q : Quadrilateral G)
    (hd : Disjoint c.remainder q.support) :
    (graph (diagonal q) (encoded c q).val).Copy G where
  toHom := {
    toFun := labeling c q hd
    map_rel' := by
      have hr {a b : Fin 8} (h : relation (diagonal q) (encoded c q).val a b) :
          G.Adj (labeling c q hd a) (labeling c q hd b) := by
        rcases h with h | ⟨ha, hb, hbit⟩
        · rw [basePairs] at h
          rcases mem_union.mp h with h | h1
          · rcases mem_union.mp h with h | h0
            · simp only [mem_insert, mem_singleton] at h
              rcases h with h | h | h | h | h | h | h <;>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              · exact c.triangleTuple_adj (i := 0) (j := 1) (by decide)
              · exact c.triangleTuple_adj (i := 0) (j := 2) (by decide)
              · exact c.triangleTuple_adj (i := 1) (j := 2) (by decide)
              · exact q.adjacent 0
              · exact q.adjacent 1
              · exact q.adjacent 2
              · exact (q.adjacent 3).symm
            · split_ifs at h0 with h0'
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h0)
                exact (diagonal_first q).mp h0'
              · simp at h0
          · split_ifs at h1 with h1'
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h1)
              exact (diagonal_second q).mp h1'
            · simp at h1
        · let i : Fin 4 := ⟨a.val, ha⟩
          let j : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : Fin.castAdd 4 i = a := Fin.ext rfl
          have heb : Fin.natAdd 4 j = b := Fin.ext (by dsimp [j]; omega)
          have hei : 4 * a.val + b.val - 4 = 4 * i.val + j.val := by dsimp [i, j]; omega
          rw [hei, encoded_bit] at hbit
          rw [← hea, ← heb, labeling_left, labeling_right]
          exact of_decide_eq_true hbit
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
      · exact hr hab
      · exact (hr hba).symm }
  injective' := (labeling c q hd).injective

lemma modelCopy_image (c : TriangleChain G) (q : Quadrilateral G)
    (hd : Disjoint c.remainder q.support) :
    univ.image (modelCopy c q hd) = c.remainder ∪ q.support := labeling_image c q hd

lemma weightedCount_eq_sums (m : ℕ) : weightedCount m =
    3 * (∑ j : Fin 4, (m.testBit j.val).toNat) +
      ∑ i : Fin 3, ∑ j : Fin 4, (m.testBit (4 * (i.val + 1) + j.val)).toNat := by
  simp [weightedCount, List.range_succ, Fin.sum_univ_succ, Nat.add_assoc]

lemma weightedCount_encoded (c : TriangleChain G) (q : Quadrilateral G) :
    weightedCount (encoded c q).val =
      3 * degreeIn G c.terminal q.support + contacts G c.triangle q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  have hzero (j : Fin 4) : (encoded c q).val.testBit j.val =
      decide (G.Adj c.terminal (q j)) := by
    simpa only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, c.remainderTuple_zero] using
      encoded_bit c q 0 j
  have hrow (i : Fin 3) (j : Fin 4) :
      (encoded c q).val.testBit (4 * (i.val + 1) + j.val) =
        decide (G.Adj (c.triangleTuple i) (q j)) := by
    have he := encoded_bit c q (Fin.natAdd 1 i) j
    rw [c.remainderTuple_triangle] at he
    simpa only [Fin.val_natAdd, Nat.add_comm 1 i.val] using he
  have hx : degreeIn G c.terminal q.support =
      ∑ j : Fin 4, if G.Adj c.terminal (q j) then 1 else 0 :=
    degreeIn_image G _ _ _ hq
  have ht : contacts G c.triangle q.support =
      ∑ i : Fin 3, ∑ j : Fin 4, if G.Adj (c.triangleTuple i) (q j) then 1 else 0 := by
    rw [← c.triangleTuple_support, tupleSupport, Quadrilateral.support,
      contacts_image_left G _ _ c.triangleTuple.injective]
    simp_rw [degreeIn_image G _ _ _ hq]
  have hb (v w : V) : (decide (G.Adj v w)).toNat = if G.Adj v w then 1 else 0 := by
    by_cases h : G.Adj v w <;> simp [h]
  rw [weightedCount_eq_sums, hx, ht]
  simp_rw [hzero, hrow, hb]

end Erdos577.Unattached
