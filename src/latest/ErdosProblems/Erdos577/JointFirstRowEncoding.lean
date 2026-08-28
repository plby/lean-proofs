import ErdosProblems.Erdos577.JointFirstRowModel

/-! Encode four independent neighbor rows, with no assumed graph on their vertices. -/

namespace Erdos577.JointFirstRows

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

def bits (rows : Fin 4 → V) (q : Quadrilateral G) (i : Fin 16) : Bool :=
  decide (G.Adj (rows ⟨i.val / 4, by omega⟩)
    (q ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩))

def encoded (rows : Fin 4 → V) (q : Quadrilateral G) : Fin 65536 :=
  ⟨PathExchange.encode (bits rows q), PathExchange.encode_lt (bits rows q)⟩

lemma encoded_bit (rows : Fin 4 → V) (q : Quadrilateral G) (i j : Fin 4) :
    bit (encoded rows q).val i j = decide (G.Adj (rows i) (q j)) := by
  have h := PathExchange.testBit_encode (bits rows q) ⟨4 * i.val + j.val, by omega⟩
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simpa only [bit, encoded, bits, hi, hj, Fin.eta] using h

lemma encoded_row_bit (rows : Fin 4 → V) (q : Quadrilateral G) (i j : Fin 4) :
    (JointCore.row (encoded rows q).val i).val.testBit j.val =
      decide (G.Adj (rows i) (q j)) := by
  rw [JointCore.row_bit]
  exact encoded_bit rows q i j

variable [DecidableEq V]

lemma rowCount_encoded (rows : Fin 4 → V) (q : Quadrilateral G) (i : Fin 4) :
    PawNine.rowCount (encoded rows q).val i = degreeIn G (rows i) q.support := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [PawNine.rowCount, Quadrilateral.support, degreeIn_image G _ _ _ hinj]
  apply sum_congr rfl
  intro j _
  change (bit (encoded rows q).val i j).toNat = _
  rw [encoded_bit]
  by_cases he : G.Adj (rows i) (q j) <;> simp [he]

lemma crossCount_encoded (rows : Fin 4 ↪ V) (q : Quadrilateral G) :
    PathExchange.crossCount (encoded rows q).val = contacts G (tupleSupport rows) q.support := by
  rw [PathExchange.crossCount_eq_double_sum]
  change (∑ i : Fin 4, PawNine.rowCount (encoded rows q).val i) = _
  simp_rw [rowCount_encoded]
  exact (contacts_image_left G univ rows rows.injective q.support).symm

theorem CommonColumn.transport (rows : Fin 4 → V) (q : Quadrilateral G)
    (hout : ∀ i, rows i ∉ q.support)
    (h : CommonColumn (Unattached.diagonal q) (encoded rows q).val) :
    ∃ x y z : Fin 4, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      CommonReplacement G (rows x) (rows y) (rows z) q.support := by
  obtain ⟨z, u, hrep, htwo⟩ := h
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega :
    1 < (otherNeighbors (encoded rows q).val z u).card)
  have hxz : x ≠ z := (mem_erase.mp (mem_filter.mp hx).1).1
  have hyz : y ≠ z := (mem_erase.mp (mem_filter.mp hy).1).1
  have hxbit := (mem_filter.mp hx).2
  have hybit := (mem_filter.mp hy).2
  rw [encoded_bit] at hxbit hybit
  have hquad := replacement_mask_transport q (rows z) (hout z)
    (JointCore.row (encoded rows q).val z) (fun i hi ↦ by
      rw [encoded_row_bit] at hi
      exact of_decide_eq_true hi) u hrep
  exact ⟨x, y, z, hxy, hxz, hyz, q u, (q.mem_support _).mpr ⟨u, rfl⟩,
    of_decide_eq_true hxbit, of_decide_eq_true hybit, hquad⟩

end Erdos577.JointFirstRows
