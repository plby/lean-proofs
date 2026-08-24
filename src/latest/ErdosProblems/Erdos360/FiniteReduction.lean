import ErdosProblems.Erdos360.Core

/-!
# Finite coloring reduction for Erdős 360

This file isolates the entirely finite part of the lower-bound argument.  It
passes from a coloring of an arbitrary test set `Y ⊆ {1, ..., n - 1}` to a
large integer-valued color class, applies the already formalized common
divisor extraction, and records the precise completion statement that is
enough to force a monochromatic subset sum equal to `n`.
-/

namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The values in `Y` receiving color `i`, with the range witnesses erased. -/
def integerColorClass {n r : ℕ} (Y : Finset (BelowTarget n))
    (c : BelowTarget n → Fin r) (i : Fin r) : Finset ℕ :=
  (Y.filter fun x ↦ c x = i).image Subtype.val

lemma mem_integerColorClass {n r : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin r} {i : Fin r} {a : ℕ} :
    a ∈ integerColorClass Y c i ↔
      ∃ x ∈ Y, c x = i ∧ x.1 = a := by
  classical
  rw [integerColorClass, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hx' := Finset.mem_filter.mp hx
    exact ⟨x, hx'.1, hx'.2, hxa⟩
  · rintro ⟨x, hxY, hxi, hxa⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxY, hxi⟩, hxa⟩

lemma card_integerColorClass {n r : ℕ} (Y : Finset (BelowTarget n))
    (c : BelowTarget n → Fin r) (i : Fin r) :
    (integerColorClass Y c i).card =
      (Y.filter fun x ↦ c x = i).card := by
  classical
  rw [integerColorClass, Finset.card_image_iff]
  intro x hx y hy hxy
  exact Subtype.ext hxy

lemma integerColorClass_mem_Ico {n r : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin r} {i : Fin r} {a : ℕ}
    (ha : a ∈ integerColorClass Y c i) : a ∈ Finset.Ico 1 n := by
  obtain ⟨x, _hxY, _hxi, rfl⟩ := mem_integerColorClass.mp ha
  exact x.2

/-- The pigeonhole step, in the division-free form used by the analytic
estimates: some color class has at least the average size. -/
theorem exists_large_integerColorClass {n r : ℕ} (hr : 0 < r)
    (Y : Finset (BelowTarget n)) (c : BelowTarget n → Fin r) :
    ∃ i : Fin r, Y.card ≤ r * (integerColorClass Y c i).card := by
  classical
  have hFin : (Finset.univ : Finset (Fin r)).Nonempty := by
    exact ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hiMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin r))
      (fun j ↦ (Y.filter fun x ↦ c x = j).card) hFin
  refine ⟨i, ?_⟩
  have hpartition :
      Y.card = ∑ j : Fin r, (Y.filter fun x ↦ c x = j).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (t := (Finset.univ : Finset (Fin r)))
      (f := c) (s := Y) (by intro x hx; simp)]
  rw [hpartition, card_integerColorClass]
  calc
    (∑ j : Fin r, (Y.filter fun x ↦ c x = j).card) ≤
        ∑ _j : Fin r, (Y.filter fun x ↦ c x = i).card := by
      apply Finset.sum_le_sum
      intro j hj
      exact hiMax j hj
    _ = r * (Y.filter fun x ↦ c x = i).card := by simp

/-- Scaling a subset-sum witness back by a positive common divisor produces
the corresponding subset sum in the original integer color class. -/
lemma scaled_subsetSum_mem_integerColorClass
    {n r d : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin r} {i : Fin r} {Z : Finset ℕ}
    (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ integerColorClass Y c i)
    (hdn : d ∣ n) (hquot : n / d ∈ Z.subsetSum) :
    n ∈ (integerColorClass Y c i).subsetSum := by
  classical
  obtain ⟨T, hTZ, hTsum⟩ := Finset.mem_subsetSum_iff.mp hquot
  rw [Finset.mem_subsetSum_iff]
  refine ⟨T.image (fun z ↦ d * z), ?_, ?_⟩
  · intro a ha
    obtain ⟨z, hzT, rfl⟩ := Finset.mem_image.mp ha
    exact hscale z (hTZ hzT)
  · rw [Finset.sum_image]
    · calc
        ∑ z ∈ T, d * z = d * ∑ z ∈ T, z := by
          rw [Finset.mul_sum]
        _ = d * (n / d) := by simpa using congrArg (fun u ↦ d * u) hTsum
        _ = n := Nat.mul_div_cancel' hdn
    · intro x hx y hy hxy
      exact Nat.eq_of_mul_eq_mul_left hd hxy

/-- A target subset sum in an integer color class gives an actual finite set
of distinct elements of `BelowTarget n`, monochromatic in the original
coloring. -/
lemma exists_monochromatic_of_mem_integerColorClass_subsetSum
    {n r : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin r} {i : Fin r}
    (hn : n ∈ (integerColorClass Y c i).subsetSum) :
    ∃ A : Finset (BelowTarget n),
      A ⊆ Y ∧ Monochromatic c A ∧ A.sum (fun x ↦ x.1) = n := by
  classical
  obtain ⟨T, hTclass, hTsum⟩ := Finset.mem_subsetSum_iff.mp hn
  let A := Y.filter fun x ↦ c x = i ∧ x.1 ∈ T
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy
    have hxi : c x = i := (Finset.mem_filter.mp hx).2.1
    have hyi : c y = i := (Finset.mem_filter.mp hy).2.1
    exact hxi.trans hyi.symm
  · have hvalues : values A = T := by
      ext a
      constructor
      · intro ha
        obtain ⟨x, hxA, hxa⟩ := mem_values.mp ha
        rw [Finset.mem_filter] at hxA
        exact hxa ▸ hxA.2.2
      · intro haT
        have haClass : a ∈ integerColorClass Y c i := hTclass haT
        obtain ⟨x, hxY, hxi, hxa⟩ := mem_integerColorClass.mp haClass
        apply mem_values.mpr
        refine ⟨x, Finset.mem_filter.mpr ⟨hxY, hxi, ?_⟩, hxa⟩
        exact hxa ▸ haT
    calc
      A.sum (fun x ↦ x.1) = (values A).sum id := (sum_values A).symm
      _ = T.sum id := by rw [hvalues]
      _ = n := hTsum

/-- A direct finite completion interface: it is enough to find, in one
color, a positive scaling divisor and a quotient set whose subset sums hit
`n / d`. -/
theorem forcesTarget_of_scaled_colorClass_completion
    {n r : ℕ} (Y : Finset (BelowTarget n))
    (hcomplete : ∀ c : BelowTarget n → Fin r,
      ∃ i : Fin r, ∃ d : ℕ, ∃ Z : Finset ℕ,
        0 < d ∧ d ∣ n ∧
        (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) ∧
        n / d ∈ Z.subsetSum) :
    ForcesTarget n r := by
  intro c
  obtain ⟨i, d, Z, hd, hdn, hscale, hquot⟩ := hcomplete c
  have hnClass := scaled_subsetSum_mem_integerColorClass hd hscale hdn hquot
  obtain ⟨A, _hAY, hmono, hsum⟩ :=
    exists_monochromatic_of_mem_integerColorClass_subsetSum hnClass
  exact ⟨A, hmono, hsum⟩

/-- Pigeonhole plus common-divisor extraction.  All number-theoretic and
additive work remaining in the CFP lower bound is concentrated in
`hcomplete`: it must show that *any* extracted large diverse quotient class
has a quotient subset sum equal to `n / d` (and that the extracted divisor
divides `n`). -/
theorem forcesTarget_of_extracted_colorClass_completion
    {n r B L K : ℕ} (hr : 0 < r) (hB : 0 < B)
    (Y : Finset (BelowTarget n))
    (hcomplete : ∀ (c : BelowTarget n → Fin r) (i : Fin r)
        (d : ℕ) (Z : Finset ℕ),
      Y.card ≤ r * (integerColorClass Y c i).card →
      0 < d → d ≤ B →
      (∀ z ∈ Z, d * z ∈ integerColorClass Y c i) →
      (integerColorClass Y c i).card - Z.card ≤
        L * Nat.log 2 B + K * B →
      (∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
      d ∣ n ∧ n / d ∈ Z.subsetSum) :
    ForcesTarget n r := by
  apply forcesTarget_of_scaled_colorClass_completion Y
  intro c
  obtain ⟨i, hiLarge⟩ := exists_large_integerColorClass hr Y c
  obtain ⟨d, Z, hd, hdB, hscale, hloss, hdiverse⟩ :=
    exists_divisorExtraction B L K hB (integerColorClass Y c i)
  obtain ⟨hdn, hquot⟩ :=
    hcomplete c i d Z hiLarge hd hdB hscale hloss hdiverse
  exact ⟨i, d, Z, hd, hdn, hscale, hquot⟩

end Erdos360
