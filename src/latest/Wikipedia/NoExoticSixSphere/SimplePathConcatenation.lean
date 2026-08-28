import Mathlib.Topology.Path
import Mathlib.Tactic.Linarith

/-!
# Injectivity and endpoint fibers of concatenated simple paths

The hypotheses describe the actual intersections of the two path
images, with their parameter endpoints retained. The half-interval
concatenation is injective for a single common endpoint; for a closed
curve the only additional fiber joins its two parameter endpoints.
-/

open scoped unitInterval

namespace NoExoticSixSphere.SimplePath

variable {X : Type*} [TopologicalSpace X] {a b c : X}

theorem trans_injective (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t, p s = q t → s = 1 ∧ t = 0) : Function.Injective (p.trans q) := by
  intro s t h
  rw [Path.trans_apply, Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have he := congrArg Subtype.val (hp h)
    apply Subtype.ext
    change 2 * (s : ℝ) = 2 * (t : ℝ) at he
    linarith
  · have he := congrArg Subtype.val (hmeet _ _ h).2
    change 2 * (t : ℝ) - 1 = 0 at he
    exfalso
    linarith
  · have he := congrArg Subtype.val (hmeet _ _ h.symm).2
    change 2 * (s : ℝ) - 1 = 0 at he
    exfalso
    linarith
  · have he := congrArg Subtype.val (hq h)
    apply Subtype.ext
    change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at he
    linarith

theorem closed_trans_eq_iff (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : ∀ s t, p s = q t → (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) (s t : I) :
    p.trans q s = p.trans q t ↔ s = t ∨ (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
  constructor
  · intro h
    rw [Path.trans_apply, Path.trans_apply] at h
    split_ifs at h with hs ht ht
    · left
      have he := congrArg Subtype.val (hp h)
      apply Subtype.ext
      change 2 * (s : ℝ) = 2 * (t : ℝ) at he
      linarith
    · rcases hmeet _ _ h with hmeet | hmeet
      · right
        have h₀ := congrArg Subtype.val hmeet.1
        have h₁ := congrArg Subtype.val hmeet.2
        change 2 * (s : ℝ) = 0 at h₀
        change 2 * (t : ℝ) - 1 = 1 at h₁
        have hs₀ : (s : ℝ) = 0 := by linarith
        have ht₁ : (t : ℝ) = 1 := by linarith
        exact ⟨Or.inl (Subtype.ext hs₀), Or.inr (Subtype.ext ht₁)⟩
      · have he := congrArg Subtype.val hmeet.2
        change 2 * (t : ℝ) - 1 = 0 at he
        exfalso
        linarith
    · rcases hmeet _ _ h.symm with hmeet | hmeet
      · right
        have h₀ := congrArg Subtype.val hmeet.1
        have h₁ := congrArg Subtype.val hmeet.2
        change 2 * (t : ℝ) = 0 at h₀
        change 2 * (s : ℝ) - 1 = 1 at h₁
        have hs₁ : (s : ℝ) = 1 := by linarith
        have ht₀ : (t : ℝ) = 0 := by linarith
        exact ⟨Or.inr (Subtype.ext hs₁), Or.inl (Subtype.ext ht₀)⟩
      · have he := congrArg Subtype.val hmeet.2
        change 2 * (s : ℝ) - 1 = 0 at he
        exfalso
        linarith
    · left
      have he := congrArg Subtype.val (hq h)
      apply Subtype.ext
      change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at he
      linarith
  · rintro (rfl | ⟨hs, ht⟩)
    · rfl
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp

end NoExoticSixSphere.SimplePath
