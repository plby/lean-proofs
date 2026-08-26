import ErdosProblems.Erdos67b.MRTDividedIntervals

/-! # The exact common cofactor interval in the minor-arc fourth moment -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtProductWindow (Z H n p m : ℕ) : Prop :=
  n < m * p ∧ m * p ≤ n + H ∧ m * p ≤ Z

instance mrtProductWindowDecidable (Z H n p m : ℕ) : Decidable (mrtProductWindow Z H n p m) :=
  inferInstanceAs (Decidable (n < m * p ∧ m * p ≤ n + H ∧ m * p ≤ Z))

def mrtProductWindowUpper (Z H n p : ℕ) : ℕ := min ((n + H) / p) (Z / p)

theorem mrtProductWindow_iff_div {p : ℕ} (hp : 0 < p) (Z H n m : ℕ) :
    mrtProductWindow Z H n p m ↔ n / p < m ∧ m ≤ mrtProductWindowUpper Z H n p := by
  simp only [mrtProductWindow, mrtProductWindowUpper, le_min_iff,
    Nat.div_lt_iff_lt_mul hp, Nat.le_div_iff_mul_le hp]

def mrtQuadWindowLower (p n : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  max (max (n.1.1 / p.1.1) (n.1.2 / p.1.2)) (max (n.2.1 / p.2.1) (n.2.2 / p.2.2))

def mrtQuadWindowUpper (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ :=
  min M (min (min (mrtProductWindowUpper Z H n.1.1 p.1.1)
      (mrtProductWindowUpper Z H n.1.2 p.1.2))
    (min (mrtProductWindowUpper Z H n.2.1 p.2.1) (mrtProductWindowUpper Z H n.2.2 p.2.2)))

def mrtQuadCofactors (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ)) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 M).filter fun m ↦
    mrtProductWindow Z H n.1.1 p.1.1 m ∧ mrtProductWindow Z H n.1.2 p.1.2 m ∧
      mrtProductWindow Z H n.2.1 p.2.1 m ∧ mrtProductWindow Z H n.2.2 p.2.2 m

theorem mem_mrtQuadCofactors {Z H M m : ℕ} {p n : (ℕ × ℕ) × (ℕ × ℕ)} :
    m ∈ mrtQuadCofactors Z H M p n ↔
      1 ≤ m ∧ m ≤ M ∧ mrtProductWindow Z H n.1.1 p.1.1 m ∧
        mrtProductWindow Z H n.1.2 p.1.2 m ∧ mrtProductWindow Z H n.2.1 p.2.1 m ∧
          mrtProductWindow Z H n.2.2 p.2.2 m := by
  classical
  simp only [mrtQuadCofactors, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem mrtQuadCofactors_eq_Ioc (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁₁ : 0 < p.1.1) (h₁₂ : 0 < p.1.2) (h₂₁ : 0 < p.2.1) (h₂₂ : 0 < p.2.2) :
    mrtQuadCofactors Z H M p n =
      Finset.Ioc (mrtQuadWindowLower p n) (mrtQuadWindowUpper Z H M p n) := by
  ext m
  rw [mem_mrtQuadCofactors, Finset.mem_Ioc]
  simp only [mrtProductWindow_iff_div h₁₁, mrtProductWindow_iff_div h₁₂,
    mrtProductWindow_iff_div h₂₁, mrtProductWindow_iff_div h₂₂,
    mrtQuadWindowLower, mrtQuadWindowUpper, max_lt_iff, le_min_iff]
  constructor
  · aesop
  · intro hh
    have hmpos : 1 ≤ m := (Nat.zero_le (n.1.1 / p.1.1)).trans_lt hh.1.1.1
    aesop

theorem mrtQuadWindow_length_le (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ))
    {P : ℕ} (hP : 0 < P) (hPp : P ≤ p.1.1) :
    mrtQuadWindowUpper Z H M p n - mrtQuadWindowLower p n ≤ H / P + 1 := by
  have hupper : mrtQuadWindowUpper Z H M p n ≤ (n.1.1 + H) / p.1.1 := by
    unfold mrtQuadWindowUpper mrtProductWindowUpper
    exact (min_le_right _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _)))
  have hlower : n.1.1 / p.1.1 ≤ mrtQuadWindowLower p n := by
    unfold mrtQuadWindowLower
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hlength : (n.1.1 + H) / p.1.1 - n.1.1 / p.1.1 ≤ H / p.1.1 + 1 := by
    have hh := mrtDividedLength_eq_or n.1.1 H p.1.1
    change mrtDividedLength n.1.1 H p.1.1 ≤ _
    rcases hh with hh | hh <;> omega
  have hdiv : H / p.1.1 ≤ H / P := by
    apply (Nat.le_div_iff_mul_le hP).2
    exact (Nat.mul_le_mul_left (H / p.1.1) hPp).trans (Nat.div_mul_le_self H p.1.1)
  exact ((tsub_le_tsub hupper hlower).trans hlength).trans (Nat.add_le_add_right hdiv 1)

theorem card_mrtQuadCofactors_le (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ))
    (h₁₁ : 0 < p.1.1) (h₁₂ : 0 < p.1.2) (h₂₁ : 0 < p.2.1) (h₂₂ : 0 < p.2.2)
    {P : ℕ} (hP : 0 < P) (hPp : P ≤ p.1.1) :
    (mrtQuadCofactors Z H M p n).card ≤ H / P + 1 := by
  rw [mrtQuadCofactors_eq_Ioc Z H M p n h₁₁ h₁₂ h₂₁ h₂₂, Nat.card_Ioc]
  exact mrtQuadWindow_length_le Z H M p n hP hPp

end

end Erdos67b
