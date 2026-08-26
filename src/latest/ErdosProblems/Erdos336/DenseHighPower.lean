import Mathlib
import ErdosProblems.Erdos336.Basic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A dense high power from finite weak coverage
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G]

/-- The set represented by exactly `j` terms. -/
def ExactPower (A : Set G) (j : ℕ) : Set G :=
  {y | GroupRepExactly A j y}

/-- Translating all generators translates an exact power, hence preserves its
cardinality. -/
theorem ncard_exactPower_shift (A : Set G) (b : G) (j : ℕ) :
    (ExactPower (ShiftToZero A b) j).ncard = (ExactPower A j).ncard := by
  let f : G → G := fun y => y - j • b
  have hset : ExactPower (ShiftToZero A b) j = f '' ExactPower A j := by
    ext y
    constructor
    · intro hy
      have hrep : GroupRepExactly (ShiftToZero A b) j y := hy
      let x : G := y + j • b
      have hx : GroupRepExactly A j x := by
        apply (groupRepExactly_shift_iff (A := A) (e := b) (x := x)).mpr
        simpa [x]
      refine ⟨x, hx, ?_⟩
      simp [f, x]
    · rintro ⟨x, hx, rfl⟩
      exact groupRepExactly_shift_iff.mp hx
  rw [hset, Set.ncard_image_of_injective]
  intro x y hxy
  dsimp [f] at hxy
  exact sub_left_injective hxy

/-- Exact powers of a set containing zero are nested. -/
theorem exactPower_mono_of_zero {A : Set G} (hzero : 0 ∈ A)
    {j h : ℕ} (hjh : j ≤ h) :
    ExactPower A j ⊆ ExactPower A h := by
  intro y hy
  exact groupRepExactly_of_atMost_of_zero ⟨j, hjh, hy⟩ hzero

/-- If a finite group is covered with at most `h` terms from `B`, then after
translating any `b∈B` to zero, the exact `h`-power has density at least
`1/(h+1)`. -/
theorem card_le_mul_ncard_highPower_of_weakCover
    [Fintype G] {B : Set G} {b : G} {h : ℕ} (hb : b ∈ B)
    (hweak : ∀ y : G, GroupRepAtMost B h y) :
    Fintype.card G ≤
      (h + 1) * (ExactPower (ShiftToZero B b) h).ncard := by
  let P : Fin (h + 1) → Set G := fun j => ExactPower B j.1
  have hcover : (Set.univ : Set G) ⊆ ⋃ j, P j := by
    intro y hy
    obtain ⟨j, hjh, hj⟩ := hweak y
    have hjlt : j < h + 1 := by omega
    exact Set.mem_iUnion.2 ⟨⟨j, hjlt⟩, hj⟩
  have hunion : Fintype.card G ≤ ∑ j : Fin (h + 1), (P j).ncard := by
    calc
      Fintype.card G = (Set.univ : Set G).ncard := by simp
      _ ≤ (⋃ j, P j).ncard := Set.ncard_le_ncard hcover
      _ ≤ ∑ j : Fin (h + 1), (P j).ncard :=
        Set.ncard_iUnion_le_of_fintype P
  calc
    Fintype.card G ≤ ∑ j : Fin (h + 1), (P j).ncard := hunion
    _ = ∑ j : Fin (h + 1),
        (ExactPower (ShiftToZero B b) j.1).ncard := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (ncard_exactPower_shift B b j.1).symm
    _ ≤ ∑ _j : Fin (h + 1),
        (ExactPower (ShiftToZero B b) h).ncard := by
      apply Finset.sum_le_sum
      intro j hj
      exact Set.ncard_le_ncard
        (exactPower_mono_of_zero (zero_mem_shiftToZero hb) (Nat.le_of_lt_succ j.2))
    _ = (h + 1) * (ExactPower (ShiftToZero B b) h).ncard := by simp

end Erdos336
