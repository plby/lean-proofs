import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleCounting

/-!
# Quantitative recurrence for positive bundle counts

After the analytic work at one maximal bundle edge, a good-configuration
count satisfies a scalar recurrence

```
count(s) = p(e) * count(s.erase e) + error,
```

where `0 ≤ p(e) ≤ 1` and the absolute error is uniformly bounded.  The
maximal edge may depend on `s`; no global enumeration is required.  This
file solves that recurrence on arbitrary finite edge families.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- If every nonempty finite family admits one edge whose removal satisfies
a `δ`-accurate multiplicative recurrence, the total error is at most one
`δ` per edge. -/
theorem abs_finiteCount_sub_prod_le_card_mul
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    |count s - ∏ e ∈ s, p e| ≤
      (s.card : ℝ) * δ := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    simp [hempty]
  · have hsne : s.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨e, he, hrec⟩ := hstep s hsne
    have herase : s.erase e ⊂ s :=
      Finset.erase_ssubset he
    have hind :
        |count (s.erase e) -
            ∏ f ∈ s.erase e, p f| ≤
          ((s.erase e).card : ℝ) * δ :=
      ih (s.erase e) herase
    have hpe0 : 0 ≤ p e := (hp e).1
    have hpe1 : p e ≤ 1 := (hp e).2
    have hright0 :
        0 ≤ ((s.erase e).card : ℝ) * δ :=
      mul_nonneg (Nat.cast_nonneg _) hδ
    have hprod :
        (∏ f ∈ s, p f) =
          p e * ∏ f ∈ s.erase e, p f := by
      exact
        (Finset.mul_prod_erase s p he).symm
    calc
      |count s - ∏ f ∈ s, p f| =
          |(count s - p e * count (s.erase e)) +
            p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| := by
        rw [hprod]
        congr 1
        ring
      _ ≤
          |count s - p e * count (s.erase e)| +
            |p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| :=
        abs_add_le _ _
      _ =
          |count s - p e * count (s.erase e)| +
            p e *
              |count (s.erase e) -
                ∏ f ∈ s.erase e, p f| := by
        rw [abs_mul, abs_of_nonneg hpe0]
      _ ≤
          δ + p e *
            (((s.erase e).card : ℝ) * δ) := by
        exact add_le_add hrec
          (mul_le_mul_of_nonneg_left hind hpe0)
      _ ≤
          δ + ((s.erase e).card : ℝ) * δ := by
        exact add_le_add le_rfl
          (mul_le_of_le_one_left hright0 hpe1)
      _ = (s.card : ℝ) * δ := by
        rw [Finset.card_erase_of_mem he]
        have hcard : 1 ≤ s.card :=
          Finset.one_le_card.mpr hsne
        rw [Nat.cast_sub hcard]
        ring

/-- One-sided form of the recurrence estimate. -/
theorem finiteCount_prod_sub_card_mul_le
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    (∏ e ∈ s, p e) - (s.card : ℝ) * δ ≤
      count s := by
  have habs :=
    abs_finiteCount_sub_prod_le_card_mul
      count p hδ hempty hp hstep s
  exact
    sub_le_iff_le_add.mpr
      ((abs_le.mp habs).1 |>
        fun h => by linarith)

/-- If every main density is at least `α`, the finite count is bounded
below by `α` to the number of edges minus the accumulated error. -/
theorem pow_sub_card_mul_le_finiteCount
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hpLower : ∀ i, α ≤ p i)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι) :
    α ^ s.card - (s.card : ℝ) * δ ≤ count s := by
  have hproduct :
      α ^ s.card ≤ ∏ e ∈ s, p e := by
    calc
      α ^ s.card =
          ∏ _e ∈ s, α := by simp
      _ ≤ ∏ e ∈ s, p e := by
        apply Finset.prod_le_prod
        · intro e he
          exact hα
        · intro e he
          exact hpLower e
  exact le_trans
    (sub_le_sub_right hproduct _)
    (finiteCount_prod_sub_card_mul_le
      count p hδ hempty hp hstep s)

/-- Positive-count stopping criterion for the abstract edge recurrence. -/
theorem finiteCount_pos_of_card_mul_lt_pow
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p : ι → ℝ)
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 ≤ δ)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hpLower : ∀ i, α ≤ p i)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ δ)
    (s : Finset ι)
    (hsmall : (s.card : ℝ) * δ < α ^ s.card) :
    0 < count s := by
  have hlower :=
    pow_sub_card_mul_le_finiteCount
      count p hα hδ hempty hp hpLower hstep s
  linarith

/-! ## Edge-dependent recurrence errors -/

/-- Variable-error form of the finite multiplicative recurrence.  The
error attached to a removed edge is charged exactly once. -/
theorem abs_finiteCount_sub_prod_le_sum_error
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι) :
    |count s - ∏ e ∈ s, p e| ≤
      ∑ e ∈ s, error e := by
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    simp [hempty]
  · have hsne : s.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hs
    obtain ⟨e, he, hrec⟩ := hstep s hsne
    have herase : s.erase e ⊂ s :=
      Finset.erase_ssubset he
    have hind :
        |count (s.erase e) -
            ∏ f ∈ s.erase e, p f| ≤
          ∑ f ∈ s.erase e, error f :=
      ih (s.erase e) herase
    have hpe0 : 0 ≤ p e := (hp e).1
    have hpe1 : p e ≤ 1 := (hp e).2
    have hsum0 :
        0 ≤ ∑ f ∈ s.erase e, error f :=
      Finset.sum_nonneg fun f _ => herror f
    have hprod :
        (∏ f ∈ s, p f) =
          p e * ∏ f ∈ s.erase e, p f := by
      exact
        (Finset.mul_prod_erase s p he).symm
    calc
      |count s - ∏ f ∈ s, p f| =
          |(count s - p e * count (s.erase e)) +
            p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| := by
        rw [hprod]
        congr 1
        ring
      _ ≤
          |count s - p e * count (s.erase e)| +
            |p e *
              (count (s.erase e) -
                ∏ f ∈ s.erase e, p f)| :=
        abs_add_le _ _
      _ =
          |count s - p e * count (s.erase e)| +
            p e *
              |count (s.erase e) -
                ∏ f ∈ s.erase e, p f| := by
        rw [abs_mul, abs_of_nonneg hpe0]
      _ ≤
          error e +
            p e * (∑ f ∈ s.erase e, error f) := by
        exact add_le_add hrec
          (mul_le_mul_of_nonneg_left hind hpe0)
      _ ≤
          error e + ∑ f ∈ s.erase e, error f := by
        exact add_le_add le_rfl
          (mul_le_of_le_one_left hsum0 hpe1)
      _ = ∑ f ∈ s, error f := by
        rw [← Finset.sum_erase_add s error he]
        ring

/-- One-sided variable-error form of the recurrence estimate. -/
theorem finiteCount_prod_sub_sum_error_le
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι) :
    (∏ e ∈ s, p e) - (∑ e ∈ s, error e) ≤
      count s := by
  have habs :=
    abs_finiteCount_sub_prod_le_sum_error
      count p error herror hempty hp hstep s
  exact
    sub_le_iff_le_add.mpr
      ((abs_le.mp habs).1 |>
        fun h => by linarith)

/-- Positive-count stopping criterion with one prescribed error per edge. -/
theorem finiteCount_pos_of_sum_error_lt_prod
    {ι : Type*} [DecidableEq ι]
    (count : Finset ι → ℝ)
    (p error : ι → ℝ)
    (herror : ∀ i, 0 ≤ error i)
    (hempty : count ∅ = 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hstep :
      ∀ s : Finset ι, s.Nonempty →
        ∃ e ∈ s,
          |count s - p e * count (s.erase e)| ≤ error e)
    (s : Finset ι)
    (hsmall :
      (∑ e ∈ s, error e) < ∏ e ∈ s, p e) :
    0 < count s := by
  have hlower :=
    finiteCount_prod_sub_sum_error_le
      count p error herror hempty hp hstep s
  linarith

end Wikipedia.SzemeredisTheorem
