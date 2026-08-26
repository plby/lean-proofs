import ErdosProblems.Erdos394.Bonferroni

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite Brun sieve: combinatorial transfer and signed error aggregation
-/

open Nat Finset

namespace Erdos394

/-- Subsets retained by a Bonferroni truncation. -/
def truncatedSubsets [DecidableEq α] (P : Finset α) (R : ℕ) :
    Finset (Finset α) := P.powerset.filter (fun T ↦ T.card ≤ R)

/-- Weight of samples for which every condition indexed by `T` is bad. -/
noncomputable def subsetMass [DecidableEq α] [DecidableEq β]
    (A : Finset β) (w : β → ℝ) (bad : β → Finset α) (T : Finset α) : ℝ :=
  ∑ m ∈ A, if T ⊆ bad m then w m else 0

/-- Weight of samples for which no condition is bad. -/
noncomputable def siftedMass [DecidableEq α] [DecidableEq β]
    (A : Finset β) (w : β → ℝ) (bad : β → Finset α) : ℝ :=
  ∑ m ∈ A, if bad m = ∅ then w m else 0

/-- Rewrite a truncation over `bad⊆P` as a truncation over all of `P`, with
an indicator for `T⊆bad`. -/
theorem sum_truncatedSubsets_of_subset [DecidableEq α]
    {bad P : Finset α} (hbad : bad ⊆ P) (R : ℕ) :
    (∑ T ∈ truncatedSubsets bad R, (-1 : ℝ) ^ T.card) =
      ∑ T ∈ truncatedSubsets P R,
        if T ⊆ bad then (-1 : ℝ) ^ T.card else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext T
    simp only [truncatedSubsets, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hTb, hcard⟩
      exact ⟨⟨hTb.trans hbad, hcard⟩, hTb⟩
    · rintro ⟨⟨_, hcard⟩, hTb⟩
      exact ⟨hTb, hcard⟩
  · intro T hT
    rfl

/-- Generic finite Brun upper bound obtained by summing the pointwise even
Bonferroni inequality and reversing the two finite sums. -/
theorem siftedMass_le_brun [DecidableEq α] [DecidableEq β]
    (P : Finset α) (A : Finset β) (w : β → ℝ) (bad : β → Finset α)
    (hbad : ∀ m ∈ A, bad m ⊆ P) (hw : ∀ m ∈ A, 0 ≤ w m)
    (R : ℕ) (hR : Even R) :
    siftedMass A w bad ≤
      ∑ T ∈ truncatedSubsets P R,
        (-1 : ℝ) ^ T.card * subsetMass A w bad T := by
  unfold siftedMass
  calc
    (∑ m ∈ A, if bad m = ∅ then w m else 0) =
        ∑ m ∈ A, w m * (if bad m = ∅ then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro m _
          split <;> simp_all
    _ ≤ ∑ m ∈ A, w m *
        (∑ T ∈ truncatedSubsets P R,
          if T ⊆ bad m then (-1 : ℝ) ^ T.card else 0) := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (hw m hm)
      have hbZ := bonferroni_powerset_upper (bad m) R hR
      have hbR : (if bad m = ∅ then 1 else 0 : ℝ) ≤
          ∑ T ∈ truncatedSubsets (bad m) R, (-1 : ℝ) ^ T.card := by
        exact_mod_cast hbZ
      rw [sum_truncatedSubsets_of_subset (hbad m hm) R] at hbR
      exact hbR
    _ = ∑ m ∈ A, ∑ T ∈ truncatedSubsets P R,
          (-1 : ℝ) ^ T.card * (if T ⊆ bad m then w m else 0) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      by_cases hT : T ⊆ bad m <;> simp [hT, mul_comm]
    _ = ∑ T ∈ truncatedSubsets P R, ∑ m ∈ A,
          (-1 : ℝ) ^ T.card * (if T ⊆ bad m then w m else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ truncatedSubsets P R,
          (-1 : ℝ) ^ T.card * subsetMass A w bad T := by
      apply Finset.sum_congr rfl
      intro T _
      unfold subsetMass
      rw [Finset.mul_sum]

/-- Signed errors of uniformly bounded absolute value contribute at most
`E` times the number of retained subsets. -/
theorem signed_error_sum_le_card_mul {I : Finset α} (err : α → ℝ) (E : ℝ)
    (hE : 0 ≤ E) (herr : ∀ i ∈ I, |err i| ≤ E) (sign : α → ℝ)
    (hsign : ∀ i ∈ I, |sign i| = 1) :
    ∑ i ∈ I, sign i * err i ≤ I.card * E := by
  calc
    (∑ i ∈ I, sign i * err i) ≤ ∑ i ∈ I, |sign i * err i| := by
      apply Finset.sum_le_sum
      intro i _
      exact le_abs_self _
    _ = ∑ i ∈ I, |err i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, hsign i hi, one_mul]
    _ ≤ ∑ _i ∈ I, E := Finset.sum_le_sum herr
    _ = I.card * E := by simp

/-- Substitute uniform main-term approximations into a signed Brun sum. -/
theorem brun_signed_sum_le_main_add_error {I : Finset α}
    (mass density sign : α → ℝ) (X E : ℝ) (hE : 0 ≤ E)
    (hsign : ∀ i ∈ I, |sign i| = 1)
    (happrox : ∀ i ∈ I, |mass i - X * density i| ≤ E) :
    ∑ i ∈ I, sign i * mass i ≤
      X * (∑ i ∈ I, sign i * density i) + I.card * E := by
  let err : α → ℝ := fun i ↦ mass i - X * density i
  have herr : ∀ i ∈ I, |err i| ≤ E := happrox
  have hsigned : ∑ i ∈ I, sign i * err i ≤ I.card * E :=
    signed_error_sum_le_card_mul err E hE herr sign hsign
  calc
    (∑ i ∈ I, sign i * mass i) =
        X * (∑ i ∈ I, sign i * density i) +
          ∑ i ∈ I, sign i * err i := by
      unfold err
      rw [mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ X * (∑ i ∈ I, sign i * density i) +
          I.card * E := by linarith

end Erdos394
