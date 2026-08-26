import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Pigeonhole a full consecutive block avoiding a bounded forbidden set. -/

namespace Erdos73

open Finset

theorem exists_unflagged_block {n q d : ℕ} (C : Finset (Fin n))
    (hC : C.card ≤ q) (hsize : (q + 1) * d ≤ n) :
    ∃ a : ℕ, a + d ≤ n ∧ ∀ x : Fin n, a ≤ x.val → x.val < a + d → x ∉ C := by
  classical
  let blocks := C.image (fun x => x.val / d)
  have hcard : blocks.card < (Finset.range (q + 1)).card := by
    rw [card_range]
    exact card_image_le.trans_lt (by omega)
  obtain ⟨j, hj, hjC⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hjq : j < q + 1 := mem_range.mp hj
  refine ⟨j * d, ?_, ?_⟩
  · have hh := Nat.mul_le_mul_right d (show j + 1 ≤ q + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    exact hh.trans hsize
  · intro x hlo hhi hxC
    have he : x.val / d = j := Nat.div_eq_of_lt_le hlo (by
      simpa only [Nat.add_mul, Nat.one_mul] using hhi)
    exact hjC (mem_image.mpr ⟨x, hxC, he⟩)

end Erdos73
