import ErdosProblems.Erdos577.Paws
import ErdosProblems.Erdos577.PawModel
import ErdosProblems.Erdos577.DenseOutsideTransport

/-! Encode any disjoint paw and quadrilateral with exact cross-edge bits. -/

namespace Erdos577.PawEncoding

open Finset Function
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) : Fin 8 ↪ V :=
  joinTuples p.vertices q.toEmbedding hd

lemma labeling_left (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (i : Fin 4) : labeling p q hd (Fin.castAdd 4 i) = p.vertices i :=
  joinTuples_left p.vertices q.toEmbedding hd i

lemma labeling_right (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (i : Fin 4) : labeling p q hd (Fin.natAdd 4 i) = q i :=
  joinTuples_right p.vertices q.toEmbedding hd i

lemma labeling_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (labeling p q hd) = p.support ∪ q.support :=
  tupleSupport_joinTuples p.vertices q.toEmbedding hd

variable [DecidableRel G.Adj]

def bits (p : Paw G) (q : Quadrilateral G) (i : Fin 16) : Bool :=
  decide (G.Adj (p.vertices ⟨i.val / 4, by omega⟩)
    (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

def encoded (p : Paw G) (q : Quadrilateral G) : Fin 65536 :=
  ⟨PathExchange.encode (bits p q), PathExchange.encode_lt (bits p q)⟩

omit [DecidableEq V] in
lemma encoded_bit (p : Paw G) (q : Quadrilateral G) (i j : Fin 4) :
    (encoded p q).val.testBit (4 * i.val + j.val) = decide (G.Adj (p.vertices i) (q j)) := by
  have h := PathExchange.testBit_encode (bits p q) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [encoded, bits, hi, hj, Fin.eta] using h

def modelCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (PawModel.graph (Unattached.diagonal q) (encoded p q).val).Copy G where
  toHom := {
    toFun := labeling p q hd
    map_rel' := by
      have hr {a b : Fin 8}
          (h : Unattached.relation (Unattached.diagonal q) (encoded p q).val a b) :
          G.Adj (labeling p q hd a) (labeling p q hd b) := by
        rcases h with h | ⟨ha, hb, hbit⟩
        · rw [Unattached.basePairs] at h
          rcases mem_union.mp h with h | h1
          · rcases mem_union.mp h with h | h0
            · simp only [mem_insert, mem_singleton] at h
              rcases h with h | h | h | h | h | h | h <;>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
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
        · let i : Fin 4 := ⟨a.val, ha⟩
          let j : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : Fin.castAdd 4 i = a := Fin.ext rfl
          have heb : Fin.natAdd 4 j = b := Fin.ext (by dsimp [j]; omega)
          have hei : 4 * a.val + b.val - 4 = 4 * i.val + j.val := by dsimp [i, j]; omega
          rw [hei, encoded_bit] at hbit
          rw [← hea, ← heb, labeling_left, labeling_right]
          exact of_decide_eq_true hbit
      intro a b hab
      rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hab | hab
      · rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
        · exact hr hab
        · exact (hr hba).symm
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hab).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact p.pendant
        · exact p.pendant.symm }
  injective' := (labeling p q hd).injective

lemma modelCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (modelCopy p q hd) = p.support ∪ q.support := labeling_image p q hd

def baseCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (PawModel.graph 0 (encoded p q).val).Copy G :=
  (modelCopy p q hd).comp
    (SimpleGraph.Copy.ofLE _ _ (PawModel.graph_zero_le (Unattached.diagonal q) (encoded p q).val))

lemma baseCopy_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (baseCopy p q hd) = p.support ∪ q.support := labeling_image p q hd

lemma crossCount_encoded (p : Paw G) (q : Quadrilateral G) :
    PathExchange.crossCount (encoded p q).val = contacts G p.support q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  rw [PathExchange.crossCount_eq_double_sum, Paw.support, tupleSupport, Quadrilateral.support,
    contacts_image_left G _ _ p.vertices.injective]
  simp_rw [degreeIn_image G _ _ _ hq, encoded_bit]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases h : G.Adj (p.vertices i) (q j) <;> simp [h]

lemma terminalCount_encoded (p : Paw G) (q : Quadrilateral G) :
    DenseOutside.terminalCount (encoded p q).val = degreeIn G p.leaf q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  have hzero (j : Fin 4) : (encoded p q).val.testBit j.val =
      decide (G.Adj p.leaf (q j)) := by
    calc
      (encoded p q).val.testBit j.val =
          (encoded p q).val.testBit (4 * (0 : Fin 4).val + j.val) := by simp
      _ = decide (G.Adj p.leaf (q j)) := encoded_bit p q 0 j
  rw [DenseOutside.terminalCount_eq_sum, Quadrilateral.support, degreeIn_image G _ _ _ hq]
  apply sum_congr rfl
  intro j _
  rw [hzero]
  by_cases he : G.Adj p.leaf (q j) <;> simp [he]

end Erdos577.PawEncoding
