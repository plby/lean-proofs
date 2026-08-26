import ErdosProblems.Erdos486.Statement

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Delayed congruence survivors

Elementary pointwise facts about the strict activation condition in Erdős
Problem 486.
-/

open Set

namespace Erdos486

theorem pos_of_mem_survivors {A : Set ℕ}
    {X : (n : A) → Set (ZMod (n : ℕ))} {m : ℕ}
    (hm : m ∈ survivors A X) : 0 < m :=
  hm.1

theorem not_mem_survivors_of_assigned {A : Set ℕ}
    {X : (n : A) → Set (ZMod (n : ℕ))} {n : A} {m : ℕ}
    (hnm : (n : ℕ) < m) (hm : (m : ZMod (n : ℕ)) ∈ X n) :
    m ∉ survivors A X := by
  intro hs
  exact (hs.2 n hnm) hm

theorem mem_survivors_congr_below {A : Set ℕ}
    {X Y : (n : A) → Set (ZMod (n : ℕ))} {x m : ℕ}
    (hrows : ∀ n : A, (n : ℕ) < x → X n = Y n) (hmx : m < x) :
    m ∈ survivors A X ↔ m ∈ survivors A Y := by
  constructor
  · rintro ⟨hm, hX⟩
    refine ⟨hm, fun n hnm hmem => ?_⟩
    rw [← hrows n (hnm.trans hmx)] at hmem
    exact hX n hnm hmem
  · rintro ⟨hm, hY⟩
    refine ⟨hm, fun n hnm hmem => ?_⟩
    rw [hrows n (hnm.trans hmx)] at hmem
    exact hY n hnm hmem

theorem logSum_congr_below {B C : Set ℕ} {x : ℝ}
    (h : ∀ m : ℕ, (m : ℝ) < x → (m ∈ B ↔ m ∈ C)) :
    logSum B x = logSum C x := by
  classical
  unfold logSum
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmx : (m : ℝ) < x
  · have hmem := h m hmx
    by_cases hmB : m ∈ B
    · have hmC : m ∈ C := hmem.mp hmB
      simp [hmx, hmB, hmC]
    · have hmC : m ∉ C := fun hm => hmB (hmem.mpr hm)
      simp [hmx, hmB, hmC]
  · simp only [hmx, and_false, ↓reduceIte]

theorem logAverage_congr_below {B C : Set ℕ} {x : ℝ}
    (h : ∀ m : ℕ, (m : ℝ) < x → (m ∈ B ↔ m ∈ C)) :
    logAverage B x = logAverage C x := by
  rw [logAverage, logAverage, logSum_congr_below h]

end Erdos486
