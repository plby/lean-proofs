import ErdosProblems.Erdos577.MatchingModel
import ErdosProblems.Erdos577.PathModel
import ErdosProblems.Erdos577.Tuples

/-! Transport the matching exchange from its finite model to arbitrary graphs. -/

namespace Erdos577.MatchingExchange

open Finset Function
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def labeling (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    Fin 8 ↪ V := joinTuples p.vertices q.toEmbedding hd

lemma labeling_left (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (i : Fin 4) : labeling p q hd (Fin.castAdd 4 i) = p.vertices i :=
  joinTuples_left p.vertices q.toEmbedding hd i

lemma labeling_right (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (i : Fin 4) : labeling p q hd (Fin.natAdd 4 i) = q i :=
  joinTuples_right p.vertices q.toEmbedding hd i

lemma labeling_image (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (labeling p q hd) = p.support ∪ q.support :=
  tupleSupport_joinTuples p.vertices q.toEmbedding hd

variable [DecidableRel G.Adj]

def bits (p : TwoEdges G) (q : Quadrilateral G) (i : Fin 16) : Bool :=
  decide (G.Adj (p.vertices ⟨i.val / 4, by omega⟩)
    (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

def encoded (p : TwoEdges G) (q : Quadrilateral G) : Fin 65536 :=
  ⟨PathExchange.encode (bits p q), PathExchange.encode_lt (bits p q)⟩

omit [DecidableEq V] in
lemma encoded_bit (p : TwoEdges G) (q : Quadrilateral G) (i j : Fin 4) :
    (encoded p q).val.testBit (4 * i.val + j.val) = decide (G.Adj (p.vertices i) (q j)) := by
  have h := PathExchange.testBit_encode (bits p q) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [encoded, bits, hi, hj, Fin.eta] using h

def modelCopy (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (graph (encoded p q).val).Copy G where
  toHom := {
    toFun := labeling p q hd
    map_rel' := by
      have hr {a b : Fin 8} (h : relation (encoded p q).val a b) :
          G.Adj (labeling p q hd a) (labeling p q hd b) := by
        rcases h with h | ⟨ha, hb, hbit⟩
        · simp only [basePairs, mem_insert, mem_singleton] at h
          rcases h with h | h | h | h | h | h <;>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          · exact p.firstEdge
          · exact p.secondEdge
          · exact q.adjacent 0
          · exact q.adjacent 1
          · exact q.adjacent 2
          · exact (q.adjacent 3).symm
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
  injective' := (labeling p q hd).injective

lemma modelCopy_image (p : TwoEdges G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    univ.image (modelCopy p q hd) = p.support ∪ q.support := labeling_image p q hd

lemma crossCount_encoded (p : TwoEdges G) (q : Quadrilateral G) :
    PathExchange.crossCount (encoded p q).val = contacts G p.support q.support := by
  have hq : Injective (q : Fin 4 → V) := q.injective
  rw [PathExchange.crossCount_eq_double_sum, TwoEdges.support, tupleSupport,
    Quadrilateral.support, contacts_image_left G _ _ p.vertices.injective]
  simp_rw [degreeIn_image G _ _ _ hq, encoded_bit]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases h : G.Adj (p.vertices i) (q j) <;> simp [h]

lemma Positive.transport (p : TwoEdges G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Positive (encoded p q).val) :
    ScoredExchange G (p.support ∪ q.support) 5 ∨ PathReduction G (p.support ∪ q.support) 6 := by
  rcases h with h | h
  · left
    have hg := h.image (modelCopy p q hd)
    rw [modelCopy_image] at hg
    exact hg
  · right
    have hg := h.image (modelCopy p q hd)
    rw [modelCopy_image] at hg
    exact hg

end Erdos577.MatchingExchange
