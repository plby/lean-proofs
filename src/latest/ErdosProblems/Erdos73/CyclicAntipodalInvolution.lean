import ErdosProblems.Erdos73.PairedPorts
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A free involution commuting with a full cyclic successor is the half-turn. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem commuting_finRotate_eq_add {n : ℕ} [NeZero n]
    (f : Fin n → Fin n) (h : Function.Commute f (finRotate n)) (i : Fin n) :
    f i = f 0 + i := by
  have hh := h.iterate_right i.val (0 : Fin n)
  have hcycle := finCycle_eq_finRotate_iterate (k := i)
  have hz : (finRotate n)^[i.val] (0 : Fin n) = i := by
    rw [← hcycle]
    simp only [finCycle_apply, zero_add]
  have ha : (finRotate n)^[i.val] (f 0) = f 0 + i := by
    rw [← hcycle]
    rfl
  rw [hz, ha] at hh
  exact hh

theorem free_involution_commuting_finRotate {N : ℕ} (hN : 0 < N)
    (f : Fin (2 * N) → Fin (2 * N)) (hinv : Function.Involutive f)
    (hfree : ∀ i, f i ≠ i) (hcomm : Function.Commute f (finRotate (2 * N))) :
    ∀ i, (f i).val = (N + i.val) % (2 * N) := by
  let : NeZero (2 * N) := ⟨by omega⟩
  let a := f (0 : Fin (2 * N))
  have ha : 0 < a.val := by
    have hh := hfree (0 : Fin (2 * N))
    by_contra hn
    apply hh
    exact Fin.ext (by change a.val = 0; omega)
  have haN := a.isLt
  have hdouble : (a.val + a.val) % (2 * N) = 0 := by
    have hh := congrArg Fin.val (hinv (0 : Fin (2 * N)))
    rw [commuting_finRotate_eq_add f hcomm] at hh
    exact hh
  have hlow : 2 * N ≤ a.val + a.val := by
    by_contra hn
    rw [Nat.mod_eq_of_lt (by omega)] at hdouble
    omega
  have hrem : a.val + a.val - 2 * N < 2 * N := by omega
  have he : a.val = N := by
    rw [Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt hrem] at hdouble
    omega
  intro i
  have hh := congrArg Fin.val (commuting_finRotate_eq_add f hcomm i)
  change (f i).val = (a.val + i.val) % (2 * N) at hh
  simpa only [he] using hh

theorem free_involution_firstPort {N : ℕ} (hN : 0 < N)
    (f : Fin (2 * N) → Fin (2 * N)) (hinv : Function.Involutive f)
    (hfree : ∀ i, f i ≠ i) (hcomm : Function.Commute f (finRotate (2 * N))) (i : Fin N) :
    f (firstPort i) = secondPort i := by
  apply Fin.ext
  rw [free_involution_commuting_finRotate hN f hinv hfree hcomm]
  change (N + i.val) % (2 * N) = N + i.val
  exact Nat.mod_eq_of_lt (by have hi := i.isLt; omega)

end
end Erdos73
