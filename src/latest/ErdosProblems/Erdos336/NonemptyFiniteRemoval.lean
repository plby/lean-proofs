import Mathlib
import ErdosProblems.Erdos336.FiniteRemovalNormalization

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Correct nonempty weak-to-strong normalization
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The usable weak-to-strong predicate: unlike the unrestricted version, it
excludes the empty subset of the one-point group. -/
def CyclicWeakStrongBoundNE (h M : ℕ) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ B : Set (ZMod N),
    B.Nonempty →
    (∀ y : ZMod N, GroupRepAtMost B h y) →
    (∃ q : ℕ, ∀ y : ZMod N, GroupRepExactly B q y) →
    ∀ y : ZMod N, GroupRepExactly B M y

/-- The normalized removed set is nonempty because the original finite set
contains zero. -/
lemma shiftToZero_nonempty_of_zero_mem {A : Set G} {x : G}
    (hzero : 0 ∈ A) :
    (ShiftToZero A x).Nonempty := by
  refine ⟨-x, ?_⟩
  simpa [ShiftToZero] using hzero

/-- The nonempty weak-to-strong theorem is exactly sufficient for the finite
removal bound used by compact transference. -/
theorem cyclicRemovalBound_of_weakStrongBoundNE
    {h M : ℕ} (H : CyclicWeakStrongBoundNE h M) :
    CyclicRemovalBound h M := by
  intro N hN A x hzero hparent hexact
  let B : Set (ZMod N) := ShiftToZero A x
  have hBne : B.Nonempty := shiftToZero_nonempty_of_zero_mem hzero
  have hweak : ∀ y : ZMod N, GroupRepAtMost B h y :=
    all_atMost_shift_of_exact_parent hparent
  obtain ⟨q, hq⟩ := hexact
  have hqB : ∀ y : ZMod N, GroupRepExactly B q y :=
    (all_exact_shift_iff q).mp hq
  have hMB := H N hN B hBne hweak ⟨q, hqB⟩
  exact (all_exact_shift_iff M).mpr hMB

end Erdos336
