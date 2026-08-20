import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: CyclicFanMiddleSumEven]
lemma CyclicFanMiddleSumEven {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (incoming middle outgoing : α → ℕ)
    (htriangle : ∀ i : α, Even (incoming i + middle i + outgoing i))
    (hcancel : ∀ i : α, outgoing i = incoming (σ i)) :
    Even (∑ i : α, middle i) := by
-- BODY
  let f : α → ZMod 2 := fun i => incoming i
  let m : α → ZMod 2 := fun i => middle i
  have hterm : ∀ i : α, (m i : ZMod 2) = f i + f (σ i) := by
    intro i
    have hzero :
        (((incoming i + middle i + outgoing i : ℕ) : ZMod 2)) = 0 := by
      exact ZMod.natCast_eq_zero_iff_even.mpr (htriangle i)
    have hraw :
        (incoming i : ZMod 2) + (middle i : ZMod 2) + (outgoing i : ZMod 2) = 0 := by
      simpa using hzero
    have hout : (outgoing i : ZMod 2) = f (σ i) := by
      simp [f, hcancel i]
    have hchar : ((incoming i : ZMod 2) + outgoing i) = f i + f (σ i) := by
      simp [f, hout]
    have hm : (middle i : ZMod 2) = (incoming i : ZMod 2) + outgoing i := by
      calc
        (middle i : ZMod 2) =
            ((incoming i : ZMod 2) + middle i + outgoing i) +
              ((incoming i : ZMod 2) + outgoing i) := by
          ring_nf
          simp [show (2 : ZMod 2) = 0 by decide]
        _ = 0 + ((incoming i : ZMod 2) + outgoing i) := by
          rw [hraw]
        _ = (incoming i : ZMod 2) + outgoing i := by
          simp
    simpa [m, hchar] using hm
  have hsum_cast :
      (((∑ i : α, middle i : ℕ) : ZMod 2)) = ∑ i : α, (f i + f (σ i)) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  have hperm : (∑ i : α, f (σ i)) = ∑ i : α, f i := by
    simpa using (Equiv.sum_comp σ f)
  have hzero : (((∑ i : α, middle i : ℕ) : ZMod 2)) = 0 := by
    rw [hsum_cast]
    rw [Finset.sum_add_distrib, hperm]
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by decide]
    simp
  exact ZMod.natCast_eq_zero_iff_even.mp hzero
