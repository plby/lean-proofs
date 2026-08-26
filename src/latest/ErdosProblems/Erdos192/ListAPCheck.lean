import Mathlib

namespace Erdos192

/-- Scan possible midpoints once, moving the endpoint twice per iteration. -/
def halfChecks (x : Nat) : List Nat → List Nat → Bool
  | m :: ms, e :: es => (x + e != 2 * m) && halfChecks x ms (es.drop 1)
  | _, _ => true

def allChecks : List Nat → Bool
  | [] => true
  | x :: xs => halfChecks x xs (xs.drop 1) && allChecks xs

theorem halfChecks_sound (x : Nat) (ms es : List Nat) (h : halfChecks x ms es = true)
    (k : Nat) (hk : k < ms.length) (he : 2 * k < es.length) :
    x + es[2 * k] ≠ 2 * ms[k] := by
  induction ms generalizing es k with
  | nil => simp at hk
  | cons m ms ih =>
    cases es with
    | nil => simp at he
    | cons e es =>
      simp only [halfChecks, Bool.and_eq_true, bne_iff_ne] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
        have hk' : k < ms.length := by simpa using hk
        have he' : 2 * k < (es.drop 1).length := by simp at he ⊢; omega
        have hs := ih (es.drop 1) h.2 k hk' he'
        simp only [show 2 * (k + 1) = (1 + 2 * k) + 1 by omega,
          List.getElem_cons_succ]
        simpa only [List.getElem_drop] using hs

theorem allChecks_sound (p : List Nat) (h : allChecks p = true) (i l : Nat)
    (hl : 0 < l) (hend : i + 2 * l < p.length) :
    p[i] + p[i + 2 * l] ≠ 2 * p[i + l] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  induction p generalizing i with
  | nil => simp at hend
  | cons x xs ih =>
    simp only [allChecks, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have hm : k < xs.length := by simp at hend; omega
      have he : 2 * k < (xs.drop 1).length := by simp at hend ⊢; omega
      have hs := halfChecks_sound x xs (xs.drop 1) h.1 k hm he
      simp only [Nat.zero_add, List.getElem_cons_zero,
        show 2 * (k + 1) = (1 + 2 * k) + 1 by omega, List.getElem_cons_succ]
      simpa only [List.getElem_drop] using hs
    | succ i =>
      have he : i + 2 * (k + 1) < xs.length := by simp at hend; omega
      simpa only [Nat.succ_add, List.getElem_cons_succ] using ih h.2 i he

end Erdos192
