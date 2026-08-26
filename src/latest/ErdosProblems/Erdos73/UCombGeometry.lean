import ErdosProblems.Erdos73.LeftCombRegions

/-! Coordinate separation for nested U-shaped boundary combs with a bottom margin. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Finset

variable {c r : ℕ}

def uCombBase (L M : ℕ) : ℕ := L + 2 * M + 2

def rectangularUCombCondition (leftRows rightRows : Finset ℕ) (L M a b j : ℕ)
    (w : ElementaryWallVertex c r) : Prop :=
    (w.val.1.val ∈ leftRows ∧ w.val.1.val ≤ L ∧ a ≤ w.val.1.val ∧
      w.val.1.val ≤ b ∧ w.val.2.val ≤ 2 * j + 1) ∨
    (w.val.1.val ∈ rightRows ∧ w.val.1.val ≤ L ∧
      a ≤ 2 * uCombBase L M - w.val.1.val ∧ 2 * uCombBase L M - w.val.1.val ≤ b ∧
      2 * c - (2 * j + 2) ≤ w.val.2.val) ∨
    (w.val.1.val ≤ uCombBase L M - 2 * j ∧ a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧
      2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) ∨
    (w.val.1.val ≤ uCombBase L M - 2 * j ∧
      a ≤ 2 * uCombBase L M - w.val.1.val ∧ 2 * uCombBase L M - w.val.1.val ≤ b ∧
      2 * c - (2 * j + 2) ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * c - (2 * j + 1)) ∨
    (w.val.1.val = uCombBase L M - 2 * j ∧ a ≤ uCombBase L M ∧ uCombBase L M ≤ b ∧
      2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * c - (2 * j + 1))

def rectangularUComb (leftRows rightRows : Finset ℕ) (L M a b j : ℕ) :
    Finset (ElementaryWallVertex c r) :=
  univ.filter (rectangularUCombCondition leftRows rightRows L M a b j)

theorem mem_rectangularUComb {A B : Finset ℕ} {L M a b j : ℕ}
    {w : ElementaryWallVertex c r} :
    w ∈ rectangularUComb A B L M a b j ↔ rectangularUCombCondition A B L M a b j w := by
  simp only [rectangularUComb, mem_filter, mem_univ, true_and]

theorem rectangularUComb_row_bound {A B : Finset ℕ} {L M a b j : ℕ}
    (hj : j ≤ M) {w : ElementaryWallVertex c r}
    (hw : w ∈ rectangularUComb A B L M a b j) :
    w.val.1.val ≤ uCombBase L M - 2 * j := by
  rw [mem_rectangularUComb] at hw
  dsimp only [rectangularUCombCondition, uCombBase] at hw ⊢
  rcases hw with hw | hw | hw | hw | hw <;> omega

theorem interval_contains_base_of_gap {L M a b x : ℕ}
    (ha : a ≤ L ∨ 2 * uCombBase L M - L ≤ a)
    (hb : b ≤ L ∨ 2 * uCombBase L M - L ≤ b)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hLx : L < x) (hxL : x < 2 * uCombBase L M - L) :
    a ≤ uCombBase L M ∧ uCombBase L M ≤ b := by
  dsimp only [uCombBase] at *
  omega

theorem rectangularUComb_high_row {A B : Finset ℕ} {L M a b j : ℕ}
    (hj : 0 < j) (hjM : j ≤ M)
    (ha : a ≤ L ∨ 2 * uCombBase L M - L ≤ a)
    (hb : b ≤ L ∨ 2 * uCombBase L M - L ≤ b)
    {w : ElementaryWallVertex c r} (hw : w ∈ rectangularUComb A B L M a b j)
    (hrow : L < w.val.1.val) : a ≤ uCombBase L M ∧ uCombBase L M ≤ b := by
  have hbound := rectangularUComb_row_bound hjM hw
  rw [mem_rectangularUComb] at hw
  dsimp only [rectangularUCombCondition] at hw
  rcases hw with hw | hw | hw | hw | hw
  · omega
  · omega
  · apply interval_contains_base_of_gap ha hb hw.2.1 hw.2.2.1 hrow
    dsimp only [uCombBase] at *
    omega
  · apply interval_contains_base_of_gap ha hb hw.2.1 hw.2.2.1
    · dsimp only [uCombBase] at *
      omega
    · dsimp only [uCombBase] at *
      omega
  · exact ⟨hw.2.1, hw.2.2.1⟩

theorem rectangularUComb_disjoint_series {A B A' B' : Finset ℕ}
    {L M a b j a' b' j' : ℕ} (hc : 2 * M + 3 ≤ c)
    (hj : 0 < j) (hjM : j ≤ M) (hj' : 0 < j') (hjM' : j' ≤ M)
    (ha : a ≤ L ∨ 2 * uCombBase L M - L ≤ a)
    (hb : b ≤ L ∨ 2 * uCombBase L M - L ≤ b)
    (ha' : a' ≤ L ∨ 2 * uCombBase L M - L ≤ a')
    (hb' : b' ≤ L ∨ 2 * uCombBase L M - L ≤ b') (hsep : b < a') :
    Disjoint (rectangularUComb (c := c) (r := r) A B L M a b j)
      (rectangularUComb A' B' L M a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hrow : w.val.1.val ≤ L := by
    by_contra hh
    have h₁ := rectangularUComb_high_row hj hjM ha hb hw (by omega)
    have h₂ := rectangularUComb_high_row hj' hjM' ha' hb' hw' (by omega)
    omega
  rw [mem_rectangularUComb] at hw hw'
  dsimp only [rectangularUCombCondition, uCombBase] at hw hw'
  rcases hw with hw | hw | hw | hw | hw <;>
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega

theorem rectangularUComb_disjoint_nested {A B A' B' : Finset ℕ}
    {L M a b j a' b' j' : ℕ} (hc : 2 * M + 3 ≤ c)
    (hjM : j ≤ M) (hjM' : j' ≤ M) (hdepth : j' < j)
    (hA : ∀ s ∈ A, ¬ (a' ≤ s ∧ s ≤ b'))
    (hB : ∀ s ∈ B, ¬ (a' ≤ 2 * uCombBase L M - s ∧
      2 * uCombBase L M - s ≤ b')) :
    Disjoint (rectangularUComb (c := c) (r := r) A B L M a b j)
      (rectangularUComb A' B' L M a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  rw [mem_rectangularUComb] at hw hw'
  dsimp only [rectangularUCombCondition] at hw hw'
  rcases hw with hw | hw | hw | hw | hw
  · have havoid := hA _ hw.1
    dsimp only [uCombBase] at *
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega
  · have havoid := hB _ hw.1
    dsimp only [uCombBase] at *
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega
  · dsimp only [uCombBase] at *
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega
  · dsimp only [uCombBase] at *
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega
  · dsimp only [uCombBase] at *
    rcases hw' with hw' | hw' | hw' | hw' | hw' <;> omega

end
end Erdos73
