import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative wrap count for sums of canonical cyclic representatives
-/

namespace Erdos336

private lemma sum_zmod_vals_le {N : ℕ} [NeZero N]
    (xs : List (ZMod N)) :
    (xs.map ZMod.val).sum ≤ xs.length * N := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hx : x.val ≤ N := Nat.le_of_lt (ZMod.val_lt x)
      calc
        x.val + (xs.map ZMod.val).sum ≤ N + xs.length * N :=
          Nat.add_le_add hx ih
        _ = (Nat.succ xs.length) * N := by
          rw [Nat.succ_mul]
          omega

private lemma cast_sum_zmod_vals {N : ℕ} [NeZero N]
    (xs : List (ZMod N)) :
    (((xs.map ZMod.val).sum : ℕ) : ZMod N) = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      rw [ZMod.natCast_zmod_val]

/-- If canonical representatives of `d + sum xs` and `r` agree modulo `N`,
the ordinary sum wraps around at most `xs.length` times. -/
theorem exists_bounded_wrap_count
    {N : ℕ} [NeZero N] (r d : ZMod N) (xs : List (ZMod N))
    (heq : d + xs.sum = r) :
    ∃ t : ℕ, t ≤ xs.length ∧
      d.val + (xs.map ZMod.val).sum = r.val + t * N := by
  let S := d.val + (xs.map ZMod.val).sum
  have hcast : (S : ZMod N) = (r.val : ZMod N) := by
    dsimp [S]
    rw [Nat.cast_add]
    rw [cast_sum_zmod_vals, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    exact heq
  have hmod : S % N = r.val % N :=
    (ZMod.natCast_eq_natCast_iff' S r.val N).mp hcast
  have hrmod : r.val % N = r.val := Nat.mod_eq_of_lt (ZMod.val_lt r)
  have hSbound : S < (xs.length + 1) * N := by
    dsimp [S]
    have hd := ZMod.val_lt d
    have hs := sum_zmod_vals_le xs
    nlinarith
  let t := S / N
  have ht : t ≤ xs.length := by
    dsimp [t]
    have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    apply Nat.le_of_lt_succ
    exact (Nat.div_lt_iff_lt_mul hN).2 (by simpa [Nat.add_comm] using hSbound)
  refine ⟨t, ht, ?_⟩
  have hdiv := (Nat.mod_add_div S N).symm
  rw [hmod, hrmod] at hdiv
  dsimp [t]
  calc
    S = r.val + N * (S / N) := hdiv
    _ = r.val + (S / N) * N := by ring

end Erdos336
