import Mathlib

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite averaging for Erdős Problem 486

This file gives elementary finite versions of the averaging principle and
Markov's inequality.  Everything is expressed using `Finset` and `Fintype`;
no measure-theoretic probability space is involved.

The final section evaluates the uniform average over four-colourings when one
of the four colours is designated black.
-/

open scoped BigOperators

namespace Erdos486

section Averages

variable {α 𝕜 : Type*}

/-- The average of `f` over a finite set.  It is defined to be zero on the
empty set, as follows from division by zero in a field. -/
def finsetAverage [Field 𝕜] (s : Finset α) (f : α → 𝕜) : 𝕜 :=
  (∑ x ∈ s, f x) / s.card

/-- The uniform average of a function on a finite type. -/
def fintypeAverage [Fintype α] [Field 𝕜] (f : α → 𝕜) : 𝕜 :=
  (∑ x, f x) / Fintype.card α

@[simp]
theorem finsetAverage_empty [Field 𝕜] (f : α → 𝕜) :
    finsetAverage ∅ f = 0 := by
  simp [finsetAverage]

@[simp]
theorem finsetAverage_const [Field 𝕜] [CharZero 𝕜] (s : Finset α)
    (hs : s.Nonempty) (c : 𝕜) :
    finsetAverage s (fun _ ↦ c) = c := by
  have hcard : (s.card : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  rw [finsetAverage, Finset.sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ c hcard]

@[simp]
theorem fintypeAverage_const [Fintype α] [Nonempty α]
    [Field 𝕜] [CharZero 𝕜] (c : 𝕜) :
    fintypeAverage (fun _ : α ↦ c) = c := by
  have hcard : (Fintype.card α : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [fintypeAverage, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    mul_div_cancel_left₀ c hcard]

/-- A point of a nonempty finite set has value at most the average. -/
theorem exists_mem_le_finsetAverage [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (hs : s.Nonempty) (f : α → 𝕜) :
    ∃ x ∈ s, f x ≤ finsetAverage s f := by
  by_contra h
  push Not at h
  have hsum :
      ∑ x ∈ s, finsetAverage s f < ∑ x ∈ s, f x :=
    Finset.sum_lt_sum (fun x hx ↦ (h x hx).le)
      (hs.imp fun x hx ↦ ⟨hx, h x hx⟩)
  have hcard : (s.card : 𝕜) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have havg :
      ∑ x ∈ s, finsetAverage s f = ∑ x ∈ s, f x := by
    rw [Finset.sum_const, nsmul_eq_mul, finsetAverage,
      mul_div_cancel₀ _ hcard]
  rw [havg] at hsum
  exact (lt_irrefl _) hsum

/-- A function on a nonempty finite type takes a value at most its uniform
average. -/
theorem exists_le_fintypeAverage [Fintype α] [Nonempty α]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (f : α → 𝕜) :
    ∃ x, f x ≤ fintypeAverage f := by
  simpa [fintypeAverage, finsetAverage] using
    (exists_mem_le_finsetAverage (𝕜 := 𝕜) (Finset.univ : Finset α)
      Finset.univ_nonempty f)

/-- The direct probabilistic-method form: an upper bound for a finite average
is attained as an upper bound by at least one outcome. -/
theorem exists_le_of_fintypeAverage_le [Fintype α] [Nonempty α]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : α → 𝕜) {B : 𝕜}
    (haverage : fintypeAverage f ≤ B) :
    ∃ x, f x ≤ B := by
  obtain ⟨x, hx⟩ := exists_le_fintypeAverage f
  exact ⟨x, hx.trans haverage⟩

/-- The corresponding probabilistic-method form for an explicitly specified
nonempty finite set. -/
theorem exists_mem_le_of_finsetAverage_le [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (hs : s.Nonempty) (f : α → 𝕜) {B : 𝕜}
    (haverage : finsetAverage s f ≤ B) :
    ∃ x ∈ s, f x ≤ B := by
  obtain ⟨x, hxs, hx⟩ := exists_mem_le_finsetAverage s hs f
  exact ⟨x, hxs, hx.trans haverage⟩

/-- The average of a nonnegative function over a finite set is nonnegative. -/
theorem finsetAverage_nonneg [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (s : Finset α) (f : α → 𝕜)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ finsetAverage s f := by
  exact div_nonneg (Finset.sum_nonneg fun x hx ↦ hf x hx) (Nat.cast_nonneg _)

/-- The uniform average of a nonnegative function is nonnegative. -/
theorem fintypeAverage_nonneg [Fintype α] [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (f : α → 𝕜) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ fintypeAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ ↦ hf x) (Nat.cast_nonneg _)

end Averages

section Markov

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Finite-sum Markov inequality.  The number of points in `s` at which
`t ≤ f x`, multiplied by `t`, is at most the total sum of a nonnegative
function.  No positivity assumption on `t` is needed for this unnormalized
form. -/
theorem finset_markov (s : Finset α) (f : α → 𝕜)
    (hf : ∀ x ∈ s, 0 ≤ f x) (t : 𝕜) :
    ((s.filter fun x ↦ t ≤ f x).card : 𝕜) * t ≤ ∑ x ∈ s, f x := by
  classical
  calc
    ((s.filter fun x ↦ t ≤ f x).card : 𝕜) * t =
        ∑ x ∈ s.filter fun x ↦ t ≤ f x, t := by
      simp
    _ ≤ ∑ x ∈ s.filter fun x ↦ t ≤ f x, f x := by
      exact Finset.sum_le_sum fun x hx ↦ (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x ∈ s, f x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun x hxs _ ↦ hf x hxs

/-- Markov's inequality on a finite type, stated purely as a cardinality and
a finite sum. -/
theorem fintype_markov [Fintype α] (f : α → 𝕜)
    (hf : ∀ x, 0 ≤ f x) (t : 𝕜) :
    ((Finset.univ.filter fun x ↦ t ≤ f x).card : 𝕜) * t ≤
      ∑ x, f x := by
  simpa using finset_markov (𝕜 := 𝕜) (Finset.univ : Finset α) f
    (fun x _ ↦ hf x) t

end Markov

noncomputable section FourColorings

variable {ι 𝕜 : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

/-- A four-colouring of a finite index type. -/
abbrev FourColoring (ι : Type*) := ι → Fin 4

/-- Colour `0` is black; this counts the black coordinates of a colouring. -/
def blackCount (c : FourColoring ι) : ℕ :=
  ((Finset.univ : Finset ι).filter fun i ↦ c i = 0).card

/-- There are exactly `4 ^ |ι|` four-colourings of `ι`. -/
theorem card_fourColoring :
    Fintype.card (FourColoring ι) = 4 ^ Fintype.card ι := by
  simp [FourColoring]

/-- The weight `2` for black and `1` for every other colour factors over the
coordinates of a colouring. -/
theorem two_pow_blackCount_eq_prod [CommSemiring 𝕜]
    (c : FourColoring ι) :
    (2 : 𝕜) ^ blackCount c =
      ∏ i : ι, if c i = 0 then (2 : 𝕜) else 1 := by
  classical
  rw [blackCount, ← Finset.prod_filter]
  simp

/-- Exact finite counting identity: summing `2^(number of black coordinates)`
over all four-colourings gives `5 ^ |ι|`. -/
theorem sum_two_pow_blackCount [CommSemiring 𝕜] :
    (∑ c : FourColoring ι, (2 : 𝕜) ^ blackCount c) =
      (5 : 𝕜) ^ Fintype.card ι := by
  classical
  calc
    (∑ c : FourColoring ι, (2 : 𝕜) ^ blackCount c) =
        ∑ c : FourColoring ι,
          ∏ i : ι, if c i = 0 then (2 : 𝕜) else 1 := by
      exact Finset.sum_congr rfl fun c _ ↦ two_pow_blackCount_eq_prod c
    _ = ∏ i : ι, ∑ colour : Fin 4,
          if colour = 0 then (2 : 𝕜) else 1 := by
      simpa [Fintype.piFinset_univ] using
        (Finset.sum_prod_piFinset (R := 𝕜) (Finset.univ : Finset (Fin 4))
          (fun _ colour ↦ if colour = 0 then (2 : 𝕜) else 1))
    _ = ∏ _i : ι, (5 : 𝕜) := by
      congr 1
      funext i
      rw [Fin.sum_univ_four]
      norm_num [Fin.ext_iff]
    _ = (5 : 𝕜) ^ Fintype.card ι := by
      simp

/-- The exact uniform average of the black weight, simultaneously valid over
`ℚ`, `ℝ`, or any linear ordered field. -/
theorem fintypeAverage_two_pow_blackCount [Field 𝕜] [CharZero 𝕜] :
    fintypeAverage (fun c : FourColoring ι ↦ (2 : 𝕜) ^ blackCount c) =
      ((5 : 𝕜) / 4) ^ Fintype.card ι := by
  classical
  rw [fintypeAverage, sum_two_pow_blackCount, card_fourColoring]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact (div_pow (5 : 𝕜) 4 (Fintype.card ι)).symm

end FourColorings

end Erdos486
