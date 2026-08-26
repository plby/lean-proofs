import Mathlib
import ErdosProblems.Erdos336.CyclicWrap

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Norm control for almost-periodic cyclic wrapping
-/

namespace Erdos336

private lemma map_sum_zmod_vals
    {K : Type*} [AddCommGroup K] (φ : ℤ →+ K)
    {N : ℕ} (xs : List (ZMod N)) :
    (xs.map (fun a => φ (a.val : ℤ))).sum =
      φ ((xs.map ZMod.val).sum : ℤ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.cast_add, map_add]

/-- A cyclic sum of `ℓ` canonical representatives differs from its target by
at most `ℓ` copies of the near-return `φ(N)`. -/
theorem norm_cyclic_wrap_error
    {K : Type*} [SeminormedAddCommGroup K] (φ : ℤ →+ K)
    {N : ℕ} [NeZero N] (r d : ZMod N) (xs : List (ZMod N))
    (heq : d + xs.sum = r) :
    ‖φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum -
        φ (r.val : ℤ)‖ ≤ (xs.length : ℝ) * ‖φ (N : ℤ)‖ := by
  obtain ⟨t, ht, hwrap⟩ := exists_bounded_wrap_count r d xs heq
  have hφ :
      φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum =
        φ (r.val : ℤ) + t • φ (N : ℤ) := by
    rw [map_sum_zmod_vals]
    have hwrapZ :
        (d.val : ℤ) + ((xs.map ZMod.val).sum : ℤ) =
          (r.val : ℤ) + (t : ℤ) * (N : ℤ) := by exact_mod_cast hwrap
    rw [← map_add, hwrapZ, map_add]
    congr 1
    simpa [nsmul_eq_mul] using (AddMonoidHom.map_nsmul φ t (N : ℤ))
  rw [hφ]
  simp only [add_sub_cancel_left]
  calc
    ‖t • φ (N : ℤ)‖ ≤ (t : ℝ) * ‖φ (N : ℤ)‖ := norm_nsmul_le
    _ ≤ (xs.length : ℝ) * ‖φ (N : ℤ)‖ := by
      gcongr

end Erdos336
