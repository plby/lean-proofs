import ErdosProblems.Erdos4.FGKMTSmallMaskCount

/-! The actual small-prime mask is an explicit set of allowed CRT residues. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical ProductCharacterEncoding

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def translatedAllowedResidues (h : Fin k → ℕ) (Y p : ℕ) : Finset ℕ :=
  (Finset.range (modulus ell)).filter
    (fun n => ∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0)

theorem translatedAllowedResidues_subset (h : Fin k → ℕ) (Y p : ℕ) :
    translatedAllowedResidues ell h Y p ⊆ Finset.range (modulus ell) :=
  Finset.filter_subset _ _

theorem mem_translatedAllowedResidues (h : Fin k → ℕ) (Y p n : ℕ) :
    n ∈ translatedAllowedResidues ell h Y p ↔ n < modulus ell ∧
      ∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0 := by
  simp only [translatedAllowedResidues, Finset.mem_filter, Finset.mem_range]

theorem translatedSmallMask_indicator (h : Fin k → ℕ) (Y p n : ℕ) :
    translatedSmallMask ell h Y p n =
      if (∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0)
        then 1 else 0 := by
  unfold translatedSmallMask
  by_cases hh : ∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0
  · rw [if_pos hh]
    exact Finset.prod_eq_one (fun l _ => if_pos (hh l))
  · rw [if_neg hh]
    obtain ⟨l, hl⟩ := not_forall.mp hh
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

theorem smallPrime_cast_modulus (n : ℕ) (l : P) :
    ((n % modulus ell : ℕ) : ZMod (ell l)) = (n : ZMod (ell l)) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    ((Nat.mod_modEq n (modulus ell)).of_dvd (local_dvd_modulus ell l))

theorem mem_mod_translatedAllowedResidues (h : Fin k → ℕ) (Y p n : ℕ) :
    n % modulus ell ∈ translatedAllowedResidues ell h Y p ↔
      ∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0 := by
  have hM : 0 < modulus ell := Finset.prod_pos (fun l _ => (Fact.out : (ell l).Prime).pos)
  rw [mem_translatedAllowedResidues]
  simp only [Nat.mod_lt n hM, true_and, smallPrime_cast_modulus]

theorem translatedSmallMask_eq_allowed (h : Fin k → ℕ) (Y p n : ℕ) :
    translatedSmallMask ell h Y p n =
      if n % modulus ell ∈ translatedAllowedResidues ell h Y p then 1 else 0 := by
  rw [translatedSmallMask_indicator]
  simp only [mem_mod_translatedAllowedResidues]

theorem translatedAllowedResidues_card
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (Y p : ℕ) (hp : ∀ l, (p : ZMod (ell l)) ≠ 0) :
    ((translatedAllowedResidues ell h Y p).card : ℝ) =
      smallProductDensity ell (fun l i => (h i : ZMod (ell l))) * (modulus ell : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range (modulus ell),
        if (∀ l, ∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0)
          then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [translatedAllowedResidues, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ n ∈ Finset.range (modulus ell), translatedSmallMask ell h Y p n := by
      apply Finset.sum_congr rfl
      intro n _
      exact (translatedSmallMask_indicator ell h Y p n).symm
    _ = _ := translatedSmallMask_sum ell hcop h Y p hp

theorem translatedAllowedResidues_density
    (hcop : Pairwise (fun l r => (ell l).Coprime (ell r)))
    (h : Fin k → ℕ) (Y p : ℕ) (hp : ∀ l, (p : ZMod (ell l)) ≠ 0) :
    ((translatedAllowedResidues ell h Y p).card : ℝ) / modulus ell =
      smallProductDensity ell (fun l i => (h i : ZMod (ell l))) := by
  rw [translatedAllowedResidues_card ell hcop h Y p hp]
  have hM : 0 < modulus ell := Finset.prod_pos (fun l _ => (Fact.out : (ell l).Prime).pos)
  exact mul_div_cancel_right₀ _ (by exact_mod_cast hM.ne')

end Erdos4.FGKMT
