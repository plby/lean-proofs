import ErdosProblems.Erdos796.PruningNormalForms

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Set-level arithmetic classification for pruning

Every positive non-`Y`-smooth integer without three factors above `Y` falls
into one of the two canonical cofactor forms from the manuscript.
-/

namespace Erdos796

namespace PruningClassification

open PruningArithmetic PruningNormalForms

theorem one_ySmooth (Y : ℕ) : YSmooth Y 1 := by
  intro p hp hpdvd
  exact False.elim (hp.not_dvd_one hpdvd)

theorem one_lt_of_pos_not_ySmooth {Y a : ℕ}
    (ha : 0 < a) (hnot : ¬YSmooth Y a) : 1 < a := by
  by_contra h
  have ha1 : a = 1 := by omega
  exact hnot (ha1 ▸ one_ySmooth Y)

theorem largestPrimeFactor_gt_of_not_ySmooth
    {Y a : ℕ} (ha1 : 1 < a) (hnot : ¬YSmooth Y a) :
    Y < largestPrimeFactor a := by
  by_contra h
  have hle : largestPrimeFactor a ≤ Y := Nat.le_of_not_gt h
  apply hnot
  intro p hp hpa
  exact (prime_dvd_le_largestPrimeFactor ha1 hp hpa).trans hle

/-- Canonical smooth branch for an integer `a`. -/
def IsSmoothNormalForm (Y Z a : ℕ) : Prop :=
  let q := largestPrimeFactor a
  let t := a / q
  q.Prime ∧ q ∣ a ∧ Y < q ∧ a = q * t ∧
    ZSmooth Z t ∧ t < Y ^ 4

/-- Canonical two-prime branch for an integer `a`. -/
def IsSplitNormalForm (Y Z a : ℕ) : Prop :=
  let q := largestPrimeFactor a
  let t := a / q
  let r := largestPrimeFactor t
  let s := t / r
  q.Prime ∧ q ∣ a ∧ Y < q ∧ a = q * t ∧
    ¬ZSmooth Z t ∧ r.Prime ∧ r ∣ t ∧ Z < r ∧
      t = r * s ∧ s < Y ^ 4

/-- Exact two-branch classification of every positive non-smooth survivor. -/
theorem smooth_or_split_normal_form
    {Y Z a : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (ha : 0 < a) (hnotSmooth : ¬YSmooth Y a)
    (hnoTriple : ¬HasThreeLargeFactors Y a) :
    IsSmoothNormalForm Y Z a ∨ IsSplitNormalForm Y Z a := by
  have ha1 := one_lt_of_pos_not_ySmooth ha hnotSmooth
  have hqY := largestPrimeFactor_gt_of_not_ySmooth ha1 hnotSmooth
  have hnormal := canonical_pruning_normal_form hZ hZY ha1 hqY hnoTriple
  dsimp only at hnormal
  rcases hnormal with ⟨hqprime, hqa, haqt, hsmooth | hsplit⟩
  · left
    exact ⟨hqprime, hqa, hqY, haqt, hsmooth.1, hsmooth.2⟩
  · right
    exact ⟨hqprime, hqa, hqY, haqt, hsplit.1, hsplit.2.1,
      hsplit.2.2.1, hsplit.2.2.2.1, hsplit.2.2.2.2.1,
      hsplit.2.2.2.2.2⟩

end PruningClassification

end Erdos796
