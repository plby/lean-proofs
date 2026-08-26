import Mathlib
import ErdosProblems.Erdos336.FiniteRemovalNormalization

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The unqualified finite cyclic bound has a one-point-group obstruction
-/

namespace Erdos336

lemma groupRepExactly_empty_iff {G : Type*} [AddCommGroup G]
    {k : ℕ} {y : G} :
    GroupRepExactly (∅ : Set G) k y ↔ k = 0 ∧ y = 0 := by
  constructor
  · rintro ⟨xs, hlen, hxmem, hxsum⟩
    have hxs : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro x hx
      exact (hxmem x hx).elim
    subst xs
    simp_all
  · rintro ⟨rfl, rfl⟩
    exact ⟨[], rfl, by simp, by simp⟩

/-- As originally phrased without a nonempty-set hypothesis,
`CyclicWeakStrongBound h M` is false for every positive `M`: use the empty
set in the one-point cyclic group. -/
theorem not_cyclicWeakStrongBound_of_pos {h M : ℕ} (hM : 0 < M) :
    ¬ CyclicWeakStrongBound h M := by
  intro H
  have hweak : ∀ y : ZMod 1,
      GroupRepAtMost (∅ : Set (ZMod 1)) h y := by
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    subst y
    exact ⟨0, by omega, [], rfl, by simp, by simp⟩
  have hexact : ∃ q : ℕ, ∀ y : ZMod 1,
      GroupRepExactly (∅ : Set (ZMod 1)) q y := by
    refine ⟨0, ?_⟩
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    subst y
    exact ⟨[], rfl, by simp, by simp⟩
  have hbad := H 1 (by omega) (∅ : Set (ZMod 1)) hweak hexact 0
  have := groupRepExactly_empty_iff.mp hbad
  omega

end Erdos336
