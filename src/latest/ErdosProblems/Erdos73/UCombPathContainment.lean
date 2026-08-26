import ErdosProblems.Erdos73.UCombBoundaryArms

/-! The elementary hooks and clipped boundary arms stay inside their U comb. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Finset

variable {c r : ℕ} {A B : Finset ℕ} {L M a b j : ℕ}

def IsLeftUCombPort (A : Finset ℕ) (L a b : ℕ) (u : ElementaryWallVertex c r) : Prop :=
  u.val.1.val ∈ A ∧ u.val.1.val ≤ L ∧ a ≤ u.val.1.val ∧ u.val.1.val ≤ b ∧ u.val.2.val ≤ 1

def IsRightUCombPort (B : Finset ℕ) (L M a b : ℕ) (u : ElementaryWallVertex c r) : Prop :=
  u.val.1.val ∈ B ∧ u.val.1.val ≤ L ∧ a ≤ 2 * uCombBase L M - u.val.1.val ∧
    2 * uCombBase L M - u.val.1.val ≤ b ∧ 2 * (c - 1) ≤ u.val.2.val

theorem leftHook_subset_rectangularUComb {u v : ElementaryWallVertex c r}
    (hu : IsLeftUCombPort A L a b u) (hv : IsLeftUCombPort A L a b v) (hj : j ≤ M) :
    brickLeftHook (c := c) (r := r) u.val.1.val v.val.1.val j ⊆
      rectangularUComb A B L M a b j := by
  intro w hw
  rw [mem_brickLeftHook] at hw
  rw [mem_rectangularUComb]
  dsimp only [rectangularUCombCondition]
  dsimp only [IsLeftUCombPort] at hu hv
  rcases hw with ⟨hw, hc⟩ | hw
  · apply Or.inl
    rcases hw with hw | hw
    · exact ⟨hw ▸ hu.1, by omega, by omega, by omega, hc⟩
    · exact ⟨hw ▸ hv.1, by omega, by omega, by omega, hc⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    dsimp only [uCombBase] at *
    exact ⟨by omega, by omega, by omega, hw.2.2⟩

theorem rightHook_subset_rectangularUComb {u v : ElementaryWallVertex c r}
    (hu : IsRightUCombPort B L M a b u) (hv : IsRightUCombPort B L M a b v)
    (hj : j ≤ M) (hc : 2 * M + 3 ≤ c) :
    brickRightHook (c := c) (r := r) u.val.1.val v.val.1.val (c - j - 1) ⊆
      rectangularUComb A B L M a b j := by
  intro w hw
  rw [mem_brickRightHook] at hw
  rw [mem_rectangularUComb]
  dsimp only [rectangularUCombCondition]
  rcases hw with ⟨hw, hcol⟩ | hw
  · apply Or.inr ∘ Or.inl
    rcases hw with hw | hw
    · refine ⟨hw ▸ hu.1, ?_, ?_, ?_, ?_⟩ <;>
        dsimp only [IsRightUCombPort, uCombBase] at * <;> omega
    · refine ⟨hw ▸ hv.1, ?_, ?_, ?_, ?_⟩ <;>
        dsimp only [IsRightUCombPort, uCombBase] at * <;> omega
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    dsimp only [IsRightUCombPort, uCombBase] at *
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem leftBoundaryArm_subset_rectangularUComb {u : ElementaryWallVertex c r}
    (hu : IsLeftUCombPort A L a b u) (hBb : uCombBase L M ≤ b) :
    brickBoundaryArm (c := c) (r := r) true u.val.1.val (uCombBase L M - 2 * j) j ⊆
      rectangularUComb A B L M a b j := by
  intro w hw
  rw [mem_brickBoundaryArm] at hw
  rw [mem_rectangularUComb]
  dsimp only [rectangularUCombCondition]
  dsimp only [IsLeftUCombPort] at hu
  rcases hw with ⟨hw, hcol⟩ | hw
  · exact Or.inl ⟨hw ▸ hu.1, by omega, by omega, by omega, hcol⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hw.2.1, by omega, by omega, hw.2.2⟩

theorem rightBoundaryArm_subset_rectangularUComb {u : ElementaryWallVertex c r}
    (hu : IsRightUCombPort B L M a b u) (haB : a ≤ uCombBase L M)
    (hj : j ≤ M) (hc : 2 * M + 3 ≤ c) :
    brickBoundaryArm (c := c) (r := r) false u.val.1.val (uCombBase L M - 2 * j) (c - j - 1) ⊆
      rectangularUComb A B L M a b j := by
  intro w hw
  rw [mem_brickBoundaryArm] at hw
  rw [mem_rectangularUComb]
  dsimp only [rectangularUCombCondition]
  rcases hw with ⟨hw, hcol⟩ | hw
  · change 2 * (c - j - 1) ≤ w.val.2.val at hcol
    apply Or.inr ∘ Or.inl
    refine ⟨hw ▸ hu.1, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [IsRightUCombPort, uCombBase] at * <;> omega
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    dsimp only [IsRightUCombPort, uCombBase] at *
    exact ⟨hw.2.1, by omega, by omega, by omega, by omega⟩

theorem crossbar_mem_rectangularUComb {w : ElementaryWallVertex c r}
    (haB : a ≤ uCombBase L M) (hBb : uCombBase L M ≤ b)
    (hw : w.val.1.val = uCombBase L M - 2 * j ∧
      2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * c - (2 * j + 1)) :
    w ∈ rectangularUComb A B L M a b j := by
  rw [mem_rectangularUComb]
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hw.1, haB, hBb, hw.2⟩)))

end
end Erdos73
