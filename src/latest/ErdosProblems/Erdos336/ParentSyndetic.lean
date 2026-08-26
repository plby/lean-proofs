import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The normalized parent cover makes an exact power eventually syndetic
-/

namespace Erdos336

/-- A finite family of translates of the exact `h`-power covers a positive
integer tail; here the shifts are precisely `0,c,...,h*c`. -/
def ExactPowerEventuallySyndetic (D : Set ℤ) (c : ℤ) (h : ℕ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ j : ℕ, j ≤ h ∧ ZRepExactly D h (n - (j : ℤ) * c)

/-- Padding the nonexceptional part of a parent representation by zeros shows
that the exact `h`-power of the removed set is eventually syndetic, with at
most `h+1` explicit translates. -/
theorem exactPowerEventuallySyndetic_of_oneExtra
    {D : Set ℤ} {c : ℤ} {h : ℕ}
    (hzero : 0 ∈ D) (hparent : EventuallyWithOneExtra D c h) :
    ExactPowerEventuallySyndetic D c h := by
  obtain ⟨N, hN⟩ := hparent
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨j, hjh, xs, hxslen, hxsmem, hxssum⟩ := hN n hn
  refine ⟨j, hjh, xs ++ List.replicate j 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, hxslen, List.length_replicate]
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact hxsmem x hx
    · exact hzero
  · simp only [List.sum_append, hxssum, List.sum_replicate, nsmul_zero,
      add_zero]

end Erdos336
