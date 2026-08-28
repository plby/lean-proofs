import ErdosProblems.Erdos577.CommonTripleModel
import ErdosProblems.Erdos577.PawEncoding

/-! Exact nine-vertex labeling and row transport for Wang's common-triple lemma. -/

namespace Erdos577.CommonTriple

open Finset Function
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) : Fin 9 ↪ V :=
  joinTuples (PawEncoding.labeling p q hd) (singletonTuple z) (by
    rw [tupleSupport_singleton]
    apply disjoint_singleton_right.mpr
    change z ∉ univ.image (PawEncoding.labeling p q hd)
    rw [PawEncoding.labeling_image]
    exact hz)

lemma labeling_old (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) (i : Fin 8) :
    labeling p q hd z hz (Fin.castAdd 1 i) = PawEncoding.labeling p q hd i :=
  joinTuples_left _ _ _ i

def colVertex (j : Fin 4) : Fin 9 := ⟨4 + j.val, by omega⟩

lemma labeling_col (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) (j : Fin 4) :
    labeling p q hd z hz (colVertex j) = q j := by
  change labeling p q hd z hz (Fin.castAdd 1 (Fin.natAdd 4 j)) = _
  rw [labeling_old, PawEncoding.labeling_right]

def rows (p : Paw G) (z : V) (i : Fin 4) : V := ![p.leaf, p.vertices 2, p.vertices 3, z] i

lemma labeling_row (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) (i : Fin 4) :
    labeling p q hd z hz (rowVertex i) = rows p z i := by
  fin_cases i <;> rfl

lemma labeling_quad (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) :
    quad.image (labeling p q hd z hz) = q.support := by
  have he : quad = univ.image colVertex := by decide +kernel
  rw [he, image_image]
  change univ.image (fun j ↦ labeling p q hd z hz (colVertex j)) = univ.image q
  congr 1
  funext j
  exact labeling_col p q hd z hz j

lemma labeling_core (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) :
    core.image (labeling p q hd z hz) = p.support ∪ q.support := by
  have he : core = univ.image (Fin.castAdd 1 : Fin 8 → Fin 9) := by decide +kernel
  rw [he, image_image]
  have hf : (fun i : Fin 8 ↦ labeling p q hd z hz (Fin.castAdd 1 i)) =
      PawEncoding.labeling p q hd := funext (labeling_old p q hd z hz)
  change univ.image (fun i : Fin 8 ↦ labeling p q hd z hz (Fin.castAdd 1 i)) = _
  rw [hf, PawEncoding.labeling_image]

variable [DecidableRel G.Adj]

def bits (p : Paw G) (q : Quadrilateral G) (z : V) (i : Fin 16) : Bool :=
  decide (G.Adj (rows p z ⟨i.val / 4, by omega⟩)
    (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

def encoded (p : Paw G) (q : Quadrilateral G) (z : V) : Fin 65536 :=
  ⟨PathExchange.encode (bits p q z), PathExchange.encode_lt (bits p q z)⟩

omit [DecidableEq V] in
lemma encoded_bit (p : Paw G) (q : Quadrilateral G) (z : V) (i j : Fin 4) :
    (encoded p q z).val.testBit (4 * i.val + j.val) = decide (G.Adj (rows p z i) (q j)) := by
  have h := PathExchange.testBit_encode (bits p q z) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [encoded, bits, hi, hj, Fin.eta] using h

def modelCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) :
    (graph (Unattached.diagonal q) (encoded p q z).val).Copy G where
  toHom := {
    toFun := labeling p q hd z hz
    map_rel' := by
      have hr {a b : Fin 9}
          (h : relation (Unattached.diagonal q) (encoded p q z).val a b) :
          G.Adj (labeling p q hd z hz a) (labeling p q hd z hz b) := by
        rcases h with h | ⟨ha, hb, hb8, hbit⟩
        · rw [basePairs] at h
          rcases mem_union.mp h with h | h1
          · rcases mem_union.mp h with h | h0
            · simp only [mem_insert, mem_singleton] at h
              rcases h with h | h | h | h | h | h | h | h <;>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              · exact p.pendant
              · exact p.edge12
              · exact p.edge13
              · exact p.edge23
              · exact q.adjacent 0
              · exact q.adjacent 1
              · exact q.adjacent 2
              · exact (q.adjacent 3).symm
            · split_ifs at h0 with h0'
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h0)
                exact (Unattached.diagonal_first q).mp h0'
              · simp at h0
          · split_ifs at h1 with h1'
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp h1)
              exact (Unattached.diagonal_second q).mp h1'
            · simp at h1
        · let i : Fin 4 := ⟨rowIndex a, by dsimp [rowIndex]; split_ifs <;> decide⟩
          let j : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : rowVertex i = a := by
            rcases ha with rfl | rfl | rfl | rfl <;> rfl
          have heb : colVertex j = b := Fin.ext (by dsimp [colVertex, j]; omega)
          change (encoded p q z).val.testBit (4 * i.val + j.val) = true at hbit
          rw [encoded_bit] at hbit
          rw [← hea, ← heb, labeling_row, labeling_col]
          exact of_decide_eq_true hbit
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
      · exact hr hab
      · exact (hr hba).symm }
  injective' := (labeling p q hd z hz).injective

lemma Positive.transport (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (z : V) (hz : z ∉ p.support ∪ q.support)
    (h : Positive (Unattached.diagonal q) (encoded p q z).val) :
    CommonReplacement G (p.vertices 2) (p.vertices 3) z q.support ∨
      TwoEdgeReduction G (p.support ∪ q.support) (edgeCount G q.support + 2) := by
  rcases h with h | h
  · left
    have hg := h.image (modelCopy p q hd z hz)
    change CommonReplacement G (p.vertices 2) (p.vertices 3) z
      (quad.image (labeling p q hd z hz)) at hg
    rw [labeling_quad] at hg
    exact hg
  · right
    have hg := h.image (modelCopy p q hd z hz)
    change TwoEdgeReduction G (core.image (labeling p q hd z hz))
      (Unattached.oldEdges (Unattached.diagonal q) + 2) at hg
    rw [labeling_core, Unattached.oldEdges_diagonal] at hg
    exact hg

lemma rowCount_encoded (p : Paw G) (q : Quadrilateral G) (z : V) (i : Fin 4) :
    PawNine.rowCount (encoded p q z).val i = degreeIn G (rows p z i) q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  rw [PawNine.rowCount, Quadrilateral.support, degreeIn_image G _ _ _ hq]
  apply sum_congr rfl
  intro j _
  rw [encoded_bit]
  by_cases he : G.Adj (rows p z i) (q j) <;> simp [he]

lemma crossCount_encoded (p : Paw G) (q : Quadrilateral G) (z : V) :
    PathExchange.crossCount (encoded p q z).val =
      degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
        degreeIn G (p.vertices 3) q.support + degreeIn G z q.support := by
  rw [PathExchange.crossCount_eq_double_sum]
  change (∑ i : Fin 4, PawNine.rowCount (encoded p q z).val i) = _
  simp_rw [rowCount_encoded]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [rows, Matrix.cons_val_zero, Matrix.cons_val_succ]
  omega

end Erdos577.CommonTriple
