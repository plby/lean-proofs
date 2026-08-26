import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Choosing one point in each open gap of a strictly increasing sequence gives
an injective map of gap indices. -/
theorem injective_of_mem_successive_intervals
    (b u : ℕ → ℕ) (hb : StrictMono b)
    (hu : ∀ i, b i < u i ∧ u i < b (i + 1)) :
    Function.Injective u := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hstep : b (i + 1) ≤ b j := hb.monotone (by omega)
    have := hu i
    have := hu j
    omega
  · have hstep : b (j + 1) ≤ b i := hb.monotone (by omega)
    have := hu i
    have := hu j
    omega

/-- Exact divisibility upgrades the preceding point injection to injection of
fixed-modulus quotient pairs. -/
theorem quotient_pair_injOn_of_successive_intervals
    (I : Finset ℕ) (bseq u v : ℕ → ℕ) (a b : ℕ)
    (hbseq : StrictMono bseq)
    (huGap : ∀ i ∈ I, bseq i < u i ∧ u i < bseq (i + 1))
    (hadu : ∀ i ∈ I, a ∣ u i) :
    Set.InjOn (fun i => (u i / a, v i / b)) (I : Set ℕ) := by
  intro i hi j hj hpairs
  have hq : u i / a = u j / a := congrArg Prod.fst hpairs
  have huEq : u i = u j := by
    calc
      u i = a * (u i / a) := (Nat.mul_div_cancel' (hadu i hi)).symm
      _ = a * (u j / a) := by rw [hq]
      _ = u j := Nat.mul_div_cancel' (hadu j hj)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hmono : bseq (i + 1) ≤ bseq j := hbseq.monotone (by omega)
    have hiGap := huGap i hi
    have hjGap := huGap j hj
    omega
  · have hmono : bseq (j + 1) ≤ bseq i := hbseq.monotone (by omega)
    have hiGap := huGap i hi
    have hjGap := huGap j hj
    omega

end Erdos489
