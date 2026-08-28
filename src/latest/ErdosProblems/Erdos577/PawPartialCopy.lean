import ErdosProblems.Erdos577.PawEncoding

/-! Copy any specified finite subset of the sixteen paw–block cross edges. -/

namespace Erdos577.PawEncoding

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma submask_of_rows (p : Paw G) (q : Quadrilateral G) (m : Fin 65536)
    (h : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) : (encoded p q).val &&& m.val = m.val := by
  apply Nat.eq_of_testBit_eq
  intro a
  rw [Nat.testBit_and]
  by_cases hm : m.val.testBit a = true
  · have ha : a < 16 := by
      by_contra hn
      have hpow : 2 ^ 16 ≤ (2 : ℕ) ^ a := Nat.pow_le_pow_right (by decide) (by omega)
      have hfalse := Nat.testBit_lt_two_pow (lt_of_lt_of_le m.isLt hpow)
      rw [hm] at hfalse
      contradiction
    let i : Fin 4 := ⟨a / 4, by omega⟩
    let j : Fin 4 := ⟨a % 4, Nat.mod_lt _ (by decide)⟩
    have he : 4 * i.val + j.val = a := by dsimp [i, j]; omega
    have hadj := h i j (by rw [he]; exact hm)
    have hb := encoded_bit p q i j
    rw [he] at hb
    rw [hb, decide_eq_true hadj, hm]
    rfl
  · have hf : m.val.testBit a = false := Bool.eq_false_iff.mpr hm
    rw [hf, Bool.and_false]

def copyOfRows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (m : Fin 65536) (h : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) : (PawModel.graph 0 m.val).Copy G :=
  (baseCopy p q hd).comp (SimpleGraph.Copy.ofLE _ _
    (PawModel.graph_mono 0 (submask_of_rows p q m h)))

lemma copyOfRows_apply (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (m : Fin 65536) (h : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) (i : Fin 8) :
    copyOfRows p q hd m h i = labeling p q hd i := rfl

lemma copyOfRows_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (m : Fin 65536) (h : ∀ i j : Fin 4, m.val.testBit (4 * i.val + j.val) = true →
      G.Adj (p.vertices i) (q j)) :
    univ.image (copyOfRows p q hd m h) = p.support ∪ q.support :=
  labeling_image p q hd

end Erdos577.PawEncoding
