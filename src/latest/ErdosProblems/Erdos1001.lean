/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1001.
https://www.erdosproblems.com/forum/thread/1001

Informal authors:
- Harry Kesten
- Vera T. Sós

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1001.md
-/
/-
This file formalizes Erdős Problem 1001, the Erdős--Szüsz--Turán
Diophantine-approximation distribution.

The detailed mathematical proof, including the all-parameter Farey-triangle
formula and the elementary no-overlap specialization, is in `tex/1001.tex`.
-/

import Mathlib

open Filter Set MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Erdos1001

noncomputable section

/-- A real number `α` has one of the reduced rational approximations counted
by the Erdős--Szüsz--Turán problem at scale `N`.  The numerator is an integer,
the denominator is a positive natural number, and all inequalities are the
literal inequalities from the problem. -/
def HasApproximation (N : ℕ) (A c α : ℝ) : Prop :=
  α ∈ Ioo (0 : ℝ) 1 ∧
    ∃ x : ℤ, ∃ y : ℕ,
      0 < y ∧
      N ≤ y ∧
      (y : ℝ) ≤ c * (N : ℝ) ∧
      x.natAbs.Coprime y ∧
      |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2

/-- The subset of `(0,1)` occurring in Erdős Problem 1001. -/
def approximableSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α | HasApproximation N A c α}

/-- `S(N,A,c)`, as a real-valued Lebesgue measure. -/
def S (N : ℕ) (A c : ℝ) : ℝ :=
  volume.real (approximableSet N A c)

/-- A concrete open interval belonging to the reduced fraction `x / y`. -/
def approximationInterval (A : ℝ) (x : ℤ) (y : ℕ) : Set ℝ :=
  Ioo ((x : ℝ) / (y : ℝ) - A / (y : ℝ) ^ 2)
    ((x : ℝ) / (y : ℝ) + A / (y : ℝ) ^ 2)

lemma mem_approximationInterval {A α : ℝ} {x : ℤ} {y : ℕ} :
    α ∈ approximationInterval A x y ↔
      |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2 := by
  rw [approximationInterval, mem_Ioo, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Equality of two reduced fractions with positive denominators forces
equality of numerator and denominator. -/
lemma reducedFraction_unique {x y x' y' : ℕ}
    (hy : 0 < y) (hy' : 0 < y')
    (hxy : x.Coprime y) (hxy' : x'.Coprime y')
    (hcross : x * y' = x' * y) :
    x = x' ∧ y = y' := by
  have hydvd : y ∣ y' := by
    apply (hxy.symm.dvd_mul_left).mp
    rw [hcross]
    exact dvd_mul_left y x'
  have hy'dvd : y' ∣ y := by
    apply (hxy'.symm.dvd_mul_left).mp
    rw [← hcross]
    exact dvd_mul_left y' x
  have hyy' : y = y' := Nat.dvd_antisymm hydvd hy'dvd
  subst y'
  constructor
  · exact Nat.mul_right_cancel hy (by simpa [mul_comm] using hcross)
  · rfl

/-- Two distinct reduced fractions are separated by at least the reciprocal
of the product of their denominators. -/
lemma reducedFraction_separation {x y x' y' : ℕ}
    (hy : 0 < y) (hy' : 0 < y')
    (hxy : x.Coprime y) (hxy' : x'.Coprime y')
    (hne : (x, y) ≠ (x', y')) :
    1 / ((y : ℝ) * (y' : ℝ)) ≤
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| := by
  have hcross : x * y' ≠ x' * y := by
    intro h
    rcases reducedFraction_unique hy hy' hxy hxy' h with ⟨rfl, rfl⟩
    exact hne rfl
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hy'R : (0 : ℝ) < y' := by exact_mod_cast hy'
  have hden : (0 : ℝ) < (y : ℝ) * (y' : ℝ) := mul_pos hyR hy'R
  rcases lt_or_gt_of_ne hcross with hlt | hgt
  · have hgapNat : 1 ≤ x' * y - x * y' :=
      Nat.sub_pos_iff_lt.mpr hlt
    have hgap : (1 : ℝ) ≤ ((x' * y - x * y' : ℕ) : ℝ) := by
      exact_mod_cast hgapNat
    have hfrac : (x : ℝ) / (y : ℝ) < (x' : ℝ) / (y' : ℝ) := by
      rw [div_lt_div_iff₀ hyR hy'R]
      exact_mod_cast hlt
    rw [abs_of_neg (sub_neg.mpr hfrac)]
    have hid :
        (x' : ℝ) / (y' : ℝ) - (x : ℝ) / (y : ℝ) =
          ((x' * y - x * y' : ℕ) : ℝ) /
            ((y : ℝ) * (y' : ℝ)) := by
      rw [Nat.cast_sub hlt.le]
      push_cast
      field_simp
    rw [show -((x : ℝ) / y - (x' : ℝ) / y') =
      (x' : ℝ) / y' - (x : ℝ) / y by ring, hid]
    exact (div_le_div_iff_of_pos_right hden).2 hgap
  · have hgapNat : 1 ≤ x * y' - x' * y :=
      Nat.sub_pos_iff_lt.mpr hgt
    have hgap : (1 : ℝ) ≤ ((x * y' - x' * y : ℕ) : ℝ) := by
      exact_mod_cast hgapNat
    have hfrac : (x' : ℝ) / (y' : ℝ) < (x : ℝ) / (y : ℝ) := by
      rw [div_lt_div_iff₀ hy'R hyR]
      exact_mod_cast hgt
    rw [abs_of_pos (sub_pos.mpr hfrac)]
    have hid :
        (x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ) =
          ((x * y' - x' * y : ℕ) : ℝ) /
            ((y : ℝ) * (y' : ℝ)) := by
      rw [Nat.cast_sub hgt.le]
      push_cast
      field_simp
    rw [hid]
    exact (div_le_div_iff_of_pos_right hden).2 hgap

/-- In the Erdős--Szüsz--Turán sparse range, the sum of the two radii
attached to any two allowed denominators is smaller than the universal
separation `1 / (q*r)`. -/
lemma sparse_radius_sum_lt {A c M q r : ℝ}
    (hA : 0 < A) (hc : 1 ≤ c) (hAc : A < c / (1 + c ^ 2))
    (hM : 0 < M) (hMq : M ≤ q) (hMr : M ≤ r)
    (hqc : q ≤ c * M) (hrc : r ≤ c * M) :
    A / q ^ 2 + A / r ^ 2 < 1 / (q * r) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hq : 0 < q := hM.trans_le hMq
  have hr : 0 < r := hM.trans_le hMr
  have hqcr : q ≤ c * r :=
    hqc.trans (mul_le_mul_of_nonneg_left hMr hcpos.le)
  have hrcq : r ≤ c * q :=
    hrc.trans (mul_le_mul_of_nonneg_left hMq hcpos.le)
  have hpoly : c * (q ^ 2 + r ^ 2) ≤ (c ^ 2 + 1) * (q * r) := by
    have h₁ : 0 ≤ c * r - q := sub_nonneg.mpr hqcr
    have h₂ : 0 ≤ c * q - r := sub_nonneg.mpr hrcq
    nlinarith [mul_nonneg h₁ h₂]
  have hAc' : A * (c ^ 2 + 1) < c := by
    simpa [add_comm] using
      (lt_div_iff₀ (by nlinarith [sq_nonneg c] : 0 < 1 + c ^ 2)).mp hAc
  have hleft := mul_le_mul_of_nonneg_left hpoly hA.le
  have hright := mul_lt_mul_of_pos_right hAc' (mul_pos hq hr)
  have hmain : A * (q ^ 2 + r ^ 2) < q * r := by
    have hscaled : c * (A * (q ^ 2 + r ^ 2)) < c * (q * r) := by
      calc
        c * (A * (q ^ 2 + r ^ 2)) = A * (c * (q ^ 2 + r ^ 2)) := by ring
        _ ≤ A * ((c ^ 2 + 1) * (q * r)) := by simpa [mul_assoc] using hleft
        _ < c * (q * r) := by simpa [mul_assoc] using hright
    nlinarith
  have hden : 0 < q ^ 2 * r ^ 2 := mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos hr)
  have hsum :
      A / q ^ 2 + A / r ^ 2 =
        A * (q ^ 2 + r ^ 2) / (q ^ 2 * r ^ 2) := by
    field_simp
    ring
  have hone :
      1 / (q * r) = (q * r) / (q ^ 2 * r ^ 2) := by
    field_simp
  rw [hsum, hone]
  exact (div_lt_div_iff_of_pos_right hden).2 hmain

/-- Open intervals around two centers are disjoint when the sum of their
radii is strictly smaller than the distance between the centers. -/
lemma approximationInterval_disjoint_of_radius_sum_lt
    {A : ℝ} {x x' : ℤ} {y y' : ℕ}
    (hsep : A / (y : ℝ) ^ 2 + A / (y' : ℝ) ^ 2 <
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)|) :
    Disjoint (approximationInterval A x y)
      (approximationInterval A x' y') := by
  rw [Set.disjoint_left]
  intro α hα hα'
  have hα₁ := mem_approximationInterval.mp hα
  have hα₂ := mem_approximationInterval.mp hα'
  have htri :
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| ≤
        |(x : ℝ) / (y : ℝ) - α| +
          |α - (x' : ℝ) / (y' : ℝ)| := by
    calc
      |(x : ℝ) / y - (x' : ℝ) / y'| =
          |((x : ℝ) / y - α) + (α - (x' : ℝ) / y')| := by ring_nf
      _ ≤ |(x : ℝ) / y - α| + |α - (x' : ℝ) / y'| := abs_add_le _ _
  have hlt :
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| <
        A / (y : ℝ) ^ 2 + A / (y' : ℝ) ^ 2 := by
    refine htri.trans_lt (add_lt_add ?_ hα₂)
    simpa [abs_sub_comm] using hα₁
  exact (not_lt_of_ge hsep.le) hlt

/-- Any two approximation intervals in the denominator window which contain
the same point have uniformly bounded cross determinant.  This reduction is
independent of the scale `N`. -/
lemma crossDet_lt_of_common_point
    {N y y' : ℕ} {A c α : ℝ} {x x' : ℤ}
    (hA : 0 < A) (hc : 1 ≤ c) (hN : 0 < N)
    (hNy : N ≤ y) (hNy' : N ≤ y')
    (hyc : (y : ℝ) ≤ c * (N : ℝ))
    (hyc' : (y' : ℝ) ≤ c * (N : ℝ))
    (hα : α ∈ approximationInterval A x y)
    (hα' : α ∈ approximationInterval A x' y') :
    |(x : ℝ) * (y' : ℝ) - (x' : ℝ) * (y : ℝ)| < 2 * A * c := by
  have hy : (0 : ℝ) < y := by exact_mod_cast hN.trans_le hNy
  have hy' : (0 : ℝ) < y' := by exact_mod_cast hN.trans_le hNy'
  have hcenters :
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| <
        A / (y : ℝ) ^ 2 + A / (y' : ℝ) ^ 2 := by
    have htri := abs_sub_le ((x : ℝ) / (y : ℝ)) α
      ((x' : ℝ) / (y' : ℝ))
    have hx := mem_approximationInterval.mp hα
    have hx' := mem_approximationInterval.mp hα'
    calc
      |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| ≤
          |(x : ℝ) / (y : ℝ) - α| +
            |α - (x' : ℝ) / (y' : ℝ)| := htri
      _ < A / (y : ℝ) ^ 2 + A / (y' : ℝ) ^ 2 := by
        exact add_lt_add (by simpa [abs_sub_comm] using hx) hx'
  have hratio : (y' : ℝ) / (y : ℝ) ≤ c := by
    apply (div_le_iff₀ hy).2
    calc
      (y' : ℝ) ≤ c * (N : ℝ) := hyc'
      _ ≤ c * (y : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hNy) (zero_le_one.trans hc)
  have hratio' : (y : ℝ) / (y' : ℝ) ≤ c := by
    apply (div_le_iff₀ hy').2
    calc
      (y : ℝ) ≤ c * (N : ℝ) := hyc
      _ ≤ c * (y' : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hNy') (zero_le_one.trans hc)
  have hdetIdentity :
      |(x : ℝ) * (y' : ℝ) - (x' : ℝ) * (y : ℝ)| =
        ((y : ℝ) * (y' : ℝ)) *
          |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| := by
    have hfrac :
        (x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ) =
          ((x : ℝ) * (y' : ℝ) - (x' : ℝ) * (y : ℝ)) /
            ((y : ℝ) * (y' : ℝ)) := by
      field_simp
    rw [hfrac, abs_div, abs_of_pos (mul_pos hy hy')]
    field_simp
  rw [hdetIdentity]
  calc
    (y : ℝ) * (y' : ℝ) *
          |(x : ℝ) / (y : ℝ) - (x' : ℝ) / (y' : ℝ)| <
        (y : ℝ) * (y' : ℝ) *
          (A / (y : ℝ) ^ 2 + A / (y' : ℝ) ^ 2) :=
      mul_lt_mul_of_pos_left hcenters (mul_pos hy hy')
    _ = A * ((y' : ℝ) / (y : ℝ) + (y : ℝ) / (y' : ℝ)) := by
      field_simp
    _ ≤ A * (c + c) :=
      mul_le_mul_of_nonneg_left (add_le_add hratio hratio') hA.le
    _ = 2 * A * c := by ring

/-- The cross determinant takes values in a fixed finite integer range,
uniformly in the scale. -/
lemma crossDet_natAbs_lt_ceiling
    {N y y' : ℕ} {A c α : ℝ} {x x' : ℤ}
    (hA : 0 < A) (hc : 1 ≤ c) (hN : 0 < N)
    (hNy : N ≤ y) (hNy' : N ≤ y')
    (hyc : (y : ℝ) ≤ c * (N : ℝ))
    (hyc' : (y' : ℝ) ≤ c * (N : ℝ))
    (hα : α ∈ approximationInterval A x y)
    (hα' : α ∈ approximationInterval A x' y') :
    (x * (y' : ℤ) - x' * (y : ℤ)).natAbs < ⌈2 * A * c⌉₊ := by
  have h := crossDet_lt_of_common_point hA hc hN hNy hNy' hyc hyc' hα hα'
  let z : ℤ := x * (y' : ℤ) - x' * (y : ℤ)
  have hz : |(z : ℝ)| < 2 * A * c := by
    simpa [z] using h
  have hcast : (z.natAbs : ℝ) < 2 * A * c := by
    calc
      (z.natAbs : ℝ) = ((z.natAbs : ℤ) : ℝ) := by norm_num
      _ = ((|z| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(z : ℝ)| := Int.cast_abs
      _ < 2 * A * c := hz
  exact (Nat.lt_ceil).2 hcast

/-- Solutions having the same determinant relative to a primitive base
vector lie on one affine integral line. -/
lemma same_crossDet_parametrization
    {x₀ y₀ : ℕ} (hcop : x₀.Coprime y₀) (hy₀ : 0 < y₀)
    {x₁ y₁ x₂ y₂ : ℤ}
    (hdet : (x₀ : ℤ) * y₁ - x₁ * (y₀ : ℤ) =
      (x₀ : ℤ) * y₂ - x₂ * (y₀ : ℤ)) :
    ∃ t : ℤ, y₁ - y₂ = (y₀ : ℤ) * t ∧ x₁ - x₂ = (x₀ : ℤ) * t := by
  have hlin :
      (x₀ : ℤ) * (y₁ - y₂) = (y₀ : ℤ) * (x₁ - x₂) := by
    linarith
  have hcopZ : IsCoprime (y₀ : ℤ) (x₀ : ℤ) := by
    exact hcop.symm.isCoprime
  have hdiv : (y₀ : ℤ) ∣ y₁ - y₂ := by
    apply hcopZ.dvd_of_dvd_mul_left
    refine ⟨x₁ - x₂, ?_⟩
    exact hlin
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ht, ?_⟩
  have hy₀Z : (y₀ : ℤ) ≠ 0 := by exact_mod_cast hy₀.ne'
  apply mul_left_cancel₀ hy₀Z
  calc
    (y₀ : ℤ) * (x₁ - x₂) = (x₀ : ℤ) * (y₁ - y₂) := hlin.symm
    _ = (x₀ : ℤ) * ((y₀ : ℤ) * t) := by rw [ht]
    _ = (y₀ : ℤ) * ((x₀ : ℤ) * t) := by ring

/-- Denominators in the window `[N, floor (c*N)]`. -/
def denominatorSet (N : ℕ) (c : ℝ) : Finset ℕ :=
  Finset.Icc N ⌊c * (N : ℝ)⌋₊

/-- Reduced numerators for a fixed positive denominator. -/
def numeratorSet (y : ℕ) : Finset ℕ :=
  (Finset.range y).filter (fun x ↦ x.Coprime y)

/-- The finite family of reduced fractions in the denominator window. -/
def reducedPairs (N : ℕ) (c : ℝ) : Finset (Σ _y : ℕ, ℕ) :=
  (denominatorSet N c).sigma numeratorSet

@[simp] lemma mem_denominatorSet {N y : ℕ} {c : ℝ} :
    y ∈ denominatorSet N c ↔ N ≤ y ∧ y ≤ ⌊c * (N : ℝ)⌋₊ := by
  simp [denominatorSet]

@[simp] lemma mem_numeratorSet {x y : ℕ} :
    x ∈ numeratorSet y ↔ x < y ∧ x.Coprime y := by
  simp [numeratorSet]

lemma card_numeratorSet (y : ℕ) :
    (numeratorSet y).card = Nat.totient y := by
  rw [numeratorSet, Nat.totient_eq_card_coprime]
  congr 1
  ext x
  simp [Nat.coprime_comm]

@[simp] lemma mem_reducedPairs {N : ℕ} {c : ℝ} {p : Σ _y : ℕ, ℕ} :
    p ∈ reducedPairs N c ↔
      N ≤ p.1 ∧ p.1 ≤ ⌊c * (N : ℝ)⌋₊ ∧
        p.2 < p.1 ∧ p.2.Coprime p.1 := by
  simp [reducedPairs, and_assoc]

/-- The finite union obtained from all reduced fractions in the denominator
window.  For large `N` it is exactly `approximableSet`; keeping it separate
makes the finite-measure computation transparent. -/
def finiteApproximationUnion (N : ℕ) (A c : ℝ) : Set ℝ :=
  ⋃ p ∈ reducedPairs N c,
    approximationInterval A (p.2 : ℤ) p.1

lemma volume_real_approximationInterval {A : ℝ} (hA : 0 ≤ A)
    (x : ℤ) (y : ℕ) :
    volume.real (approximationInterval A x y) = 2 * A / (y : ℝ) ^ 2 := by
  rw [approximationInterval, Real.volume_real_Ioo]
  rw [max_eq_left]
  · ring
  · have heq :
        (x : ℝ) / y + A / (y : ℝ) ^ 2 -
            ((x : ℝ) / y - A / (y : ℝ) ^ 2) =
          2 * A / (y : ℝ) ^ 2 := by ring
    rw [heq]
    exact div_nonneg (mul_nonneg (by norm_num) hA) (sq_nonneg _)

lemma pairwiseDisjoint_reducedPairs
    {N : ℕ} {A c : ℝ}
    (hA : 0 < A) (hc : 1 ≤ c)
    (hAc : A < c / (1 + c ^ 2)) (hN : 0 < N) :
    (↑(reducedPairs N c) : Set (Σ _y : ℕ, ℕ)).PairwiseDisjoint
      (fun p ↦ approximationInterval A (p.2 : ℤ) p.1) := by
  rintro ⟨y, x⟩ hp ⟨y', x'⟩ hp' hne
  change Sigma.mk y x ∈ reducedPairs N c at hp
  change Sigma.mk y' x' ∈ reducedPairs N c at hp'
  rw [mem_reducedPairs] at hp hp'
  have hcN : 0 ≤ c * (N : ℝ) :=
    mul_nonneg (zero_le_one.trans hc) (Nat.cast_nonneg N)
  have hy : 0 < y := lt_of_lt_of_le hN hp.1
  have hy' : 0 < y' := lt_of_lt_of_le hN hp'.1
  have hyc : (y : ℝ) ≤ c * (N : ℝ) :=
    (Nat.le_floor_iff hcN).mp hp.2.1
  have hy'c : (y' : ℝ) ≤ c * (N : ℝ) :=
    (Nat.le_floor_iff hcN).mp hp'.2.1
  have hpair : (x, y) ≠ (x', y') := by
    intro h
    have hx : x = x' := congrArg Prod.fst h
    have hyy' : y = y' := congrArg Prod.snd h
    subst x'
    subst y'
    exact hne rfl
  have hsep := reducedFraction_separation hy hy'
    hp.2.2.2 hp'.2.2.2 hpair
  have hrad := sparse_radius_sum_lt hA hc hAc
    (by exact_mod_cast hN)
    (by exact_mod_cast hp.1) (by exact_mod_cast hp'.1) hyc hy'c
  apply approximationInterval_disjoint_of_radius_sum_lt
  exact hrad.trans_le hsep

lemma volume_real_finiteApproximationUnion
    {N : ℕ} {A c : ℝ}
    (hA : 0 < A) (hc : 1 ≤ c)
    (hAc : A < c / (1 + c ^ 2)) (hN : 0 < N) :
    volume.real (finiteApproximationUnion N A c) =
      ∑ p ∈ reducedPairs N c, 2 * A / (p.1 : ℝ) ^ 2 := by
  have hmeasure := measureReal_biUnion_finset (μ := volume)
    (pairwiseDisjoint_reducedPairs hA hc hAc hN)
    (fun _ _ ↦ measurableSet_Ioo)
    (h := fun p _ ↦ by
      rw [approximationInterval, Real.volume_Ioo]
      simp)
  rw [finiteApproximationUnion, hmeasure]
  apply Finset.sum_congr rfl
  intro p hp
  exact volume_real_approximationInterval hA.le (p.2 : ℤ) p.1

lemma sum_reducedPairs_eq_totient (N : ℕ) (c : ℝ) (F : ℕ → ℝ) :
    (∑ p ∈ reducedPairs N c, F p.1) =
      ∑ y ∈ denominatorSet N c, (Nat.totient y : ℝ) * F y := by
  calc
    (∑ p ∈ reducedPairs N c, F p.1) =
        ∑ y ∈ denominatorSet N c, ∑ _x ∈ numeratorSet y, F y := by
      simpa [reducedPairs] using
        (Finset.sum_sigma' (denominatorSet N c) numeratorSet
          (fun y _x ↦ F y)).symm
    _ = ∑ y ∈ denominatorSet N c, (Nat.totient y : ℝ) * F y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_const, card_numeratorSet]
      simp

lemma volume_real_finiteApproximationUnion_eq_totient
    {N : ℕ} {A c : ℝ}
    (hA : 0 < A) (hc : 1 ≤ c)
    (hAc : A < c / (1 + c ^ 2)) (hN : 0 < N) :
    volume.real (finiteApproximationUnion N A c) =
      2 * A *
        (∑ y ∈ denominatorSet N c,
          (Nat.totient y : ℝ) / (y : ℝ) ^ 2) := by
  rw [volume_real_finiteApproximationUnion hA hc hAc hN]
  rw [sum_reducedPairs_eq_totient N c
    (fun y ↦ 2 * A / (y : ℝ) ^ 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Once the denominator exceeds `A`, any approximation to a point of
`(0,1)` has a numerator between `0` and the denominator.  Coprimality and
`y ≥ 2` then make both inequalities strict. -/
lemma numerator_natAbs_lt_denominator
    {N y : ℕ} {A α : ℝ} {x : ℤ}
    (hN2 : 2 ≤ N) (hAN : A < N) (hNy : N ≤ y)
    (hα : α ∈ Ioo (0 : ℝ) 1) (hxy : x.natAbs.Coprime y)
    (happrox : |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2) :
    0 ≤ x ∧ x.natAbs < y := by
  have hy : 0 < y := lt_of_lt_of_le (by omega) hNy
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hAy : A < (y : ℝ) := hAN.trans_le (by exact_mod_cast hNy)
  have hrad : A / (y : ℝ) ^ 2 < 1 / (y : ℝ) := by
    have hid : 1 / (y : ℝ) = (y : ℝ) / (y : ℝ) ^ 2 := by
      field_simp
    rw [hid]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hyR)).2 hAy
  rcases (abs_lt.mp happrox) with ⟨hleft, hright⟩
  have hxlowerR : (-1 : ℝ) < (x : ℝ) := by
    have hcenter : -1 / (y : ℝ) < (x : ℝ) / (y : ℝ) := by
      by_contra hnot
      have hcenter' : (x : ℝ) / (y : ℝ) ≤ -1 / (y : ℝ) := le_of_not_gt hnot
      have hneg : 1 / (y : ℝ) ≤ -((x : ℝ) / (y : ℝ)) := by
        calc
          1 / (y : ℝ) = -(-1 / (y : ℝ)) := by ring
          _ ≤ -((x : ℝ) / (y : ℝ)) := neg_le_neg hcenter'
      have hbig : 1 / (y : ℝ) < α - (x : ℝ) / (y : ℝ) := by
        nlinarith [hα.1]
      exact (not_lt_of_ge hrad.le) (hbig.trans hright)
    exact (div_lt_div_iff_of_pos_right hyR).mp hcenter
  have hxlower : (-1 : ℤ) < x := by exact_mod_cast hxlowerR
  have hxnonneg : 0 ≤ x := by
    have := (Int.add_one_le_iff).2 hxlower
    simpa using this
  have hxupperR : (x : ℝ) < (y : ℝ) + 1 := by
    have hcenter : (x : ℝ) / (y : ℝ) < 1 + 1 / (y : ℝ) := by
      nlinarith [hα.2]
    have hdiv : (x : ℝ) / (y : ℝ) < ((y : ℝ) + 1) / (y : ℝ) := by
      convert hcenter using 1
      field_simp
    exact (div_lt_div_iff_of_pos_right hyR).mp hdiv
  have hxupper : x < (y : ℤ) + 1 := by exact_mod_cast hxupperR
  have hxle : x ≤ (y : ℤ) := (Int.lt_add_one_iff).mp hxupper
  have habsCast : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hxnonneg
  have habsle : x.natAbs ≤ y := by
    exact_mod_cast (habsCast.symm ▸ hxle)
  refine ⟨hxnonneg, lt_of_le_of_ne habsle ?_⟩
  intro heq
  have hyone : y = 1 := by
    simpa [heq] using hxy
  omega

lemma approximationInterval_subset_Ioo_of_reduced
    {A : ℝ} {x y : ℕ}
    (hy : 0 < y) (hAy : A < y)
    (hx : 0 < x) (hxy : x < y) :
    approximationInterval A (x : ℤ) y ⊆ Ioo (0 : ℝ) 1 := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hrad : A / (y : ℝ) ^ 2 < 1 / (y : ℝ) := by
    have hid : 1 / (y : ℝ) = (y : ℝ) / (y : ℝ) ^ 2 := by
      field_simp
    rw [hid]
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hyR)).2 hAy
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlower : 1 / (y : ℝ) ≤ (x : ℝ) / (y : ℝ) :=
    (div_le_div_iff_of_pos_right hyR).2 hxone
  have hsum : (x : ℝ) / (y : ℝ) + 1 / (y : ℝ) ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hyR).2
    exact_mod_cast (Nat.succ_le_iff.mpr hxy)
  intro α hα
  rcases hα with ⟨hαlower, hαupper⟩
  simp only [Int.cast_natCast] at hαlower hαupper
  constructor <;> nlinarith

lemma approximableSet_eq_finiteApproximationUnion
    {N : ℕ} {A c : ℝ}
    (hN2 : 2 ≤ N) (hAN : A < N) (hc : 1 ≤ c) :
    approximableSet N A c = finiteApproximationUnion N A c := by
  ext α
  constructor
  · rintro ⟨hα, x, y, hy, hNy, hyc, hxy, happrox⟩
    rcases numerator_natAbs_lt_denominator hN2 hAN hNy hα hxy happrox with
      ⟨hxnonneg, hxlt⟩
    let p : Σ _y : ℕ, ℕ := ⟨y, x.natAbs⟩
    have hcN : 0 ≤ c * (N : ℝ) :=
      mul_nonneg (zero_le_one.trans hc) (Nat.cast_nonneg N)
    have hp : p ∈ reducedPairs N c := by
      rw [mem_reducedPairs]
      exact ⟨hNy, Nat.le_floor hyc, hxlt, hxy⟩
    rw [finiteApproximationUnion]
    refine Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hp ?_)
    rw [mem_approximationInterval]
    simpa [p, Int.natAbs_of_nonneg hxnonneg] using happrox
  · intro hα
    rw [finiteApproximationUnion] at hα
    rcases Set.mem_iUnion₂.mp hα with ⟨p, hp, hαp⟩
    rw [mem_reducedPairs] at hp
    have hNpos : 0 < N := lt_of_lt_of_le (by omega) hN2
    have hyp : 0 < p.1 := lt_of_lt_of_le hNpos hp.1
    have hyp2 : 2 ≤ p.1 := hN2.trans hp.1
    have hxp : 0 < p.2 := by
      apply Nat.pos_of_ne_zero
      intro hxzero
      have hyone : p.1 = 1 := by
        simpa [hxzero] using hp.2.2.2
      omega
    have hAy : A < (p.1 : ℝ) := hAN.trans_le (by exact_mod_cast hp.1)
    have hunit := approximationInterval_subset_Ioo_of_reduced
      hyp hAy hxp hp.2.2.1 hαp
    have hcN : 0 ≤ c * (N : ℝ) :=
      mul_nonneg (zero_le_one.trans hc) (Nat.cast_nonneg N)
    refine ⟨hunit, (p.2 : ℤ), p.1, hyp, hp.1, ?_, ?_, ?_⟩
    · exact (Nat.le_floor_iff hcN).mp hp.2.1
    · simpa using hp.2.2.2
    · exact mem_approximationInterval.mp hαp

/-- In the sparse range and once `N` is larger than the fixed radius
parameter, `S(N,A,c)` is exactly the corresponding weighted totient sum. -/
lemma S_eq_totientSum
    {N : ℕ} {A c : ℝ}
    (hA : 0 < A) (hN2 : 2 ≤ N) (hAN : A < N) (hc : 1 ≤ c)
    (hAc : A < c / (1 + c ^ 2)) :
    S N A c =
      2 * A *
        (∑ y ∈ denominatorSet N c,
          (Nat.totient y : ℝ) / (y : ℝ) ^ 2) := by
  rw [S, approximableSet_eq_finiteApproximationUnion hN2 hAN hc]
  exact volume_real_finiteApproximationUnion_eq_totient
    hA hc hAc (lt_of_lt_of_le (by omega) hN2)

/-! ### The weighted totient limit -/

/-- The real-valued harmonic number. -/
def H (n : ℕ) : ℝ := harmonic n

lemma H_sub_eq_sum_Ioc {a b : ℕ} (hab : a ≤ b) :
    H b - H a = ∑ k ∈ Finset.Ioc a b, (k : ℝ)⁻¹ := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | @succ b hab ih =>
      rw [Finset.sum_Ioc_succ_top hab, ← ih]
      simp only [H, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      ring

lemma H_mono {a b : ℕ} (hab : a ≤ b) : H a ≤ H b := by
  rw [← sub_nonneg, H_sub_eq_sum_Ioc hab]
  positivity

lemma floor_mul_div (c : ℝ) (N d : ℕ) :
    ⌊c * (N : ℝ)⌋₊ / d = ⌊(c / d) * (N : ℝ)⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  ring

lemma nat_div_eq_floor_mul (N d : ℕ) :
    N / d = ⌊((1 : ℝ) / d) * (N : ℝ)⌋₊ := by
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  congr 1
  ring

/-- The moving lower denominator cutoff, after normalization by the Farey
order `⌊cN⌋`, tends to `1 / c`. -/
lemma tendsto_lowerCutoff_fareyOrder (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun N : ℕ => (N : ℝ) / (⌊c * (N : ℝ)⌋₊ : ℝ))
      atTop (nhds (1 / c)) := by
  have hratio :
      Tendsto (fun N : ℕ => (⌊c * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
        atTop (nhds c) :=
    (tendsto_nat_floor_mul_div_atTop hc.le).comp tendsto_natCast_atTop_atTop
  have hinv := hratio.inv₀ hc.ne'
  rw [one_div]
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
      (tendsto_nat_floor_mul_atTop c hc).eventually_gt_atTop 0] with N hN hQ
  rw [inv_div]

/-- The Farey order `⌊cN⌋` tends to infinity for positive `c`. -/
lemma tendsto_fareyOrder_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => ⌊c * (N : ℝ)⌋₊) atTop atTop := by
  exact (tendsto_nat_floor_mul_atTop c hc).comp tendsto_natCast_atTop_atTop

lemma tendsto_log_floor_mul_sub_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (⌊a * (N : ℝ)⌋₊ : ℝ) - Real.log (N : ℝ))
      atTop (𝓝 (Real.log a)) := by
  have hratio :
      Tendsto (fun N : ℕ => (⌊a * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
        atTop (𝓝 a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp tendsto_natCast_atTop_atTop
  have hlog := hratio.log ha.ne'
  apply hlog.congr'
  filter_upwards [eventually_ne_atTop 0,
      (tendsto_nat_floor_mul_atTop a ha).eventually (eventually_ne_atTop 0)] with N hN hfloor
  rw [Real.log_div (by exact_mod_cast hfloor) (by exact_mod_cast hN)]

lemma tendsto_H_floor_mul_sub_log (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun N : ℕ => H ⌊a * (N : ℝ)⌋₊ - Real.log (⌊a * (N : ℝ)⌋₊ : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  exact Real.tendsto_harmonic_sub_log.comp (tendsto_nat_floor_mul_atTop a ha)

lemma tendsto_H_window (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun N : ℕ => H ⌊a * (N : ℝ)⌋₊ - H ⌊b * (N : ℝ)⌋₊)
      atTop (𝓝 (Real.log a - Real.log b)) := by
  have hEa := tendsto_H_floor_mul_sub_log a ha
  have hEb := tendsto_H_floor_mul_sub_log b hb
  have hLa := tendsto_log_floor_mul_sub_log a ha
  have hLb := tendsto_log_floor_mul_sub_log b hb
  convert (hEa.sub hEb).add (hLa.sub hLb) using 1
  · funext N
    abel
  · abel

lemma tendsto_divisor_window (c : ℝ) (hc : 0 < c) {d : ℕ} (hd : 0 < d) :
    Tendsto
      (fun N : ℕ => H (⌊c * (N : ℝ)⌋₊ / d) - H (N / d))
      atTop (𝓝 (Real.log c)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := tendsto_H_window (c / d) (1 / d) (div_pos hc hdR) (one_div_pos.mpr hdR)
  simp_rw [← floor_mul_div c, ← nat_div_eq_floor_mul] at h
  convert h using 1
  rw [Real.log_div hc.ne' hdR.ne', Real.log_div one_ne_zero hdR.ne', Real.log_one]
  ring

lemma floor_mul_ge (c : ℝ) (hc : 1 ≤ c) (N : ℕ) :
    N ≤ ⌊c * (N : ℝ)⌋₊ := by
  apply Nat.le_floor
  calc
    (N : ℝ) = 1 * (N : ℝ) := by ring
    _ ≤ c * (N : ℝ) := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg N)

lemma divisor_window_nonneg (c : ℝ) (hc : 1 ≤ c) (N d : ℕ) :
    0 ≤ H (⌊c * (N : ℝ)⌋₊ / d) - H (N / d) := by
  exact sub_nonneg.mpr (H_mono (Nat.div_le_div_right (floor_mul_ge c hc N)))

lemma divisor_window_le (c : ℝ) (hc : 1 < c) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    H (⌊c * (N : ℝ)⌋₊ / d) - H (N / d) ≤ 1 + Real.log c := by
  let r := ⌊c * (N : ℝ)⌋₊ / d
  let q := N / d
  by_cases hr : r = 0
  · have hq : q = 0 := Nat.eq_zero_of_le_zero
      (Nat.div_le_div_right (floor_mul_ge c hc.le N) |>.trans (le_of_eq hr))
    simp [r, q, hr, hq]
    linarith [Real.log_pos hc]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hqpos : (0 : ℝ) < q + 1 := by positivity
  have hqpos' : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hMnonneg : 0 ≤ c * (N : ℝ) :=
    mul_nonneg (le_trans (by norm_num) hc.le) (Nat.cast_nonneg N)
  have hfloor : (⌊c * (N : ℝ)⌋₊ : ℝ) ≤ c * (N : ℝ) := by
    exact_mod_cast Nat.floor_le hMnonneg
  have hNlt : (N : ℝ) < (d : ℝ) * (q + 1 : ℕ) := by
    exact_mod_cast Nat.lt_mul_div_succ N hd
  have hrlt : (r : ℝ) < c * (q + 1 : ℕ) := by
    calc
      (r : ℝ) ≤ (⌊c * (N : ℝ)⌋₊ : ℝ) / d := Nat.cast_div_le
      _ ≤ (c * (N : ℝ)) / d :=
        div_le_div_of_nonneg_right hfloor (Nat.cast_nonneg d)
      _ < c * (q + 1 : ℕ) := by
        rw [div_lt_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)]
        calc
          c * (N : ℝ) < c * ((d : ℝ) * (q + 1 : ℕ)) :=
            mul_lt_mul_of_pos_left hNlt (by linarith)
          _ = c * (q + 1 : ℕ) * d := by ring
  have hlog : Real.log (r : ℝ) - Real.log (q + 1 : ℕ) ≤ Real.log c := by
    have hmono : Real.log (r : ℝ) ≤ Real.log (c * (q + 1 : ℕ)) :=
      Real.strictMonoOn_log.monotoneOn hrpos
        (mul_pos (by linarith : 0 < c) hqpos') hrlt.le
    rw [Real.log_mul (by linarith : c ≠ 0) hqpos'.ne'] at hmono
    linarith
  calc
    H (⌊c * (N : ℝ)⌋₊ / d) - H (N / d)
        ≤ (1 + Real.log (r : ℝ)) - Real.log (q + 1 : ℕ) := by
          dsimp [r, q]
          exact sub_le_sub (harmonic_le_one_add_log (⌊c * (N : ℝ)⌋₊ / d))
            (log_add_one_le_harmonic (N / d))
    _ ≤ 1 + Real.log c := by linarith

lemma totient_eq_moebius_sum {n : ℕ} (hn : 0 < n) :
    (Nat.totient n : ℝ) =
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ) := by
  have hbase : ∀ m : ℕ, m > 0 →
      ∑ i ∈ m.divisors, (Nat.totient i : ℝ) = (m : ℝ) := by
    intro m hm
    exact_mod_cast Nat.sum_totient m
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hbase) n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun d k ↦ (ArithmeticFunction.moebius d : ℝ) * (k : ℝ))] at hinv
  exact hinv.symm

lemma sum_divisorPairs_eq_factorPairs (N Q : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc N Q, ∑ d ∈ n.divisors, F d (n / d)) =
      ∑ d ∈ Finset.Icc 1 Q, ∑ k ∈ Finset.Ioc (N / d) (Q / d), F d k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
      (i := fun p _ ↦ ⟨p.2, p.1 / p.2⟩)
      (j := fun p _ ↦ ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hNn, hnQ⟩, hd⟩
    have hn : n ≠ 0 := by omega
    have hdmem := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdmem.1 (by omega)
    have hdQ : d ≤ Q := (Nat.le_of_dvd (by omega) hdmem.1).trans hnQ
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc]
    refine ⟨⟨hdpos, hdQ⟩, ?_, Nat.div_le_div_right hnQ⟩
    rw [Nat.div_lt_iff_lt_mul hdpos]
    simpa [Nat.div_mul_cancel hdmem.1] using hNn
  · rintro ⟨d, k⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hdpos, hdQ⟩, hNdk, hkQd⟩
    have hNprod : N < d * k := by
      simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hdpos).mp hNdk
    have hprodQ : d * k ≤ Q := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hkQd
    simp only [Finset.mem_sigma, Finset.mem_Ioc]
    refine ⟨⟨hNprod, hprodQ⟩, Nat.mem_divisors.mpr ⟨dvd_mul_right d k, ?_⟩⟩
    omega
  · rintro ⟨n, d⟩ hp
    simp only [Finset.mem_sigma] at hp
    rcases hp with ⟨hn, hd⟩
    have hd' := (Nat.mem_divisors.mp hd).1
    congr 1
    exact Nat.mul_div_cancel' hd'
  · rintro ⟨d, k⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc] at hp
    rcases hp with ⟨⟨hdpos, hdQ⟩, hNdk, hkQd⟩
    congr 1
    simpa [mul_comm] using Nat.mul_div_left k hdpos
  · rintro ⟨n, d⟩ hp
    rfl

lemma sum_Ioc_totient_eq_factor_sum (N Q : ℕ) (hNQ : N ≤ Q) :
    (∑ n ∈ Finset.Ioc N Q, (Nat.totient n : ℝ) / (n : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 Q,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
          (H (Q / d) - H (N / d)) := by
  classical
  calc
    (∑ n ∈ Finset.Ioc N Q, (Nat.totient n : ℝ) / (n : ℝ) ^ 2) =
        ∑ n ∈ Finset.Ioc N Q,
          (∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ)) /
              (n : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [totient_eq_moebius_sum
          (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)]
    _ = ∑ n ∈ Finset.Ioc N Q,
          ∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ)) /
              ((d * (n / d) : ℕ) : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = ∑ d ∈ Finset.Icc 1 Q,
          ∑ k ∈ Finset.Ioc (N / d) (Q / d),
            ((ArithmeticFunction.moebius d : ℝ) * (k : ℕ)) /
              ((d * k : ℕ) : ℝ) ^ 2 := by
        exact sum_divisorPairs_eq_factorPairs N Q
          (fun d k ↦ ((ArithmeticFunction.moebius d : ℝ) * (k : ℕ)) /
            ((d * k : ℕ) : ℝ) ^ 2)
    _ = ∑ d ∈ Finset.Icc 1 Q,
          ∑ k ∈ Finset.Ioc (N / d) (Q / d),
            (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * (k : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro k hk
        have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hkpos : (0 : ℝ) < k := by
          exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1
        push_cast
        field_simp
    _ = ∑ d ∈ Finset.Icc 1 Q,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
          (H (Q / d) - H (N / d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [H_sub_eq_sum_Ioc (Nat.div_le_div_right hNQ), Finset.mul_sum]

lemma moebius_div_sq_tsum :
    ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 =
      6 / Real.pi ^ 2 := by
  have h_sum : ∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ) =
      1 / (Real.pi ^ 2 / 6) := by
    have h_L2_mu : (∑' d : ℕ,
        (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) =
        (riemannZeta 2)⁻¹ := by
      have h_L2_mu : (∑' d : ℕ,
          (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) =
          (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) := by
        norm_num [LSeries]
        convert Complex.ofReal_tsum _
        norm_num [LSeries.term]
        aesop
      have hmul :
          (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2) *
            (riemannZeta 2) = 1 := by
        convert ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius _ using 1
        focus
          rw [mul_comm]
        focus
          rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta]
        · norm_num
        · norm_num
      exact eq_inv_of_mul_eq_one_left (by aesop)
    have hzeta : riemannZeta 2 = Real.pi ^ 2 / 6 := riemannZeta_two
    simp_all +decide [Complex.ext_iff, sq]
    norm_cast
  simpa only [Nat.cast_pow] using h_sum.trans (by
    field_simp [Real.pi_ne_zero])

lemma summable_moebius_div_sq :
    Summable (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) := by
  have hp : Summable (fun d : ℕ => 1 / (d : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  apply Summable.of_norm_bounded hp
  intro d
  by_cases hd : d = 0
  · simp [hd]
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (d : ℝ))]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)) (sq_nonneg _)

def mobiusWindow (c : ℝ) (N d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 *
    (H (⌊c * (N : ℝ)⌋₊ / d) - H (N / d))

lemma tendsto_mobiusWindow_tsum (c : ℝ) (hc : 1 < c) :
    Tendsto (fun N : ℕ => ∑' d : ℕ, mobiusWindow c N d) atTop
      (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by
  let B := 1 + Real.log c
  have hB : 0 ≤ B := by dsimp [B]; linarith [Real.log_pos hc]
  have hsumBound : Summable (fun d : ℕ => B * (1 / (d : ℝ) ^ 2)) := by
    exact Summable.mul_left B (Real.summable_one_div_nat_pow.2 (by norm_num))
  have hpoint (d : ℕ) :
      Tendsto (fun N : ℕ => mobiusWindow c N d) atTop
        (𝓝 ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2 * Real.log c)) := by
    by_cases hd : d = 0
    · subst d
      simp [mobiusWindow, H]
    · exact tendsto_const_nhds.mul
        (tendsto_divisor_window c (by linarith) (Nat.pos_of_ne_zero hd))
  have hbound : ∀ N d, ‖mobiusWindow c N d‖ ≤ B * (1 / (d : ℝ) ^ 2) := by
    intro N d
    by_cases hd : d = 0
    · subst d
      simp [mobiusWindow, H]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hwin0 := divisor_window_nonneg c hc.le N d
    have hwin := divisor_window_le c hc N hdpos
    have hmu :
        |(ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2| ≤
          1 / (d : ℝ) ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (d : ℝ))]
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)) (sq_nonneg _)
    rw [mobiusWindow, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hwin0]
    rw [mul_comm B]
    exact mul_le_mul hmu hwin (by positivity) (by positivity)
  have htan := tendsto_tsum_of_dominated_convergence hsumBound hpoint
    (Eventually.of_forall hbound)
  convert htan using 1
  rw [summable_moebius_div_sq.tsum_mul_right, moebius_div_sq_tsum]

lemma tsum_mobiusWindow_eq_Ioc (c : ℝ) (hc : 1 ≤ c) (N : ℕ) :
    (∑' d : ℕ, mobiusWindow c N d) =
      ∑ n ∈ Finset.Ioc N ⌊c * (N : ℝ)⌋₊,
        (Nat.totient n : ℝ) / (n : ℝ) ^ 2 := by
  let Q := ⌊c * (N : ℝ)⌋₊
  have hNQ : N ≤ Q := floor_mul_ge c hc N
  rw [tsum_eq_sum (s := Finset.Icc 1 Q)]
  · exact (sum_Ioc_totient_eq_factor_sum N Q hNQ).symm
  · intro d hdmem
    simp only [Finset.mem_Icc, not_and_or] at hdmem
    rcases hdmem with hd0 | hdQ
    · have : d = 0 := by omega
      subst d
      simp [mobiusWindow, H]
    · have hdQ' : Q < d := lt_of_not_ge hdQ
      have hQd : Q / d = 0 := Nat.div_eq_of_lt hdQ'
      have hNd : N / d = 0 := Nat.div_eq_of_lt (hNQ.trans_lt hdQ')
      simp [mobiusWindow, Q, hQd, hNd]

lemma tendsto_totient_term_zero :
    Tendsto (fun N : ℕ => (Nat.totient N : ℝ) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat
  · exact Eventually.of_forall (fun N => by positivity)
  · exact Eventually.of_forall (fun N => by
      by_cases hN : N = 0
      · simp [hN]
      have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      rw [div_le_iff₀ (sq_pos_of_pos hNR), one_div]
      rw [inv_mul_eq_div]
      have heq : (N : ℝ) ^ 2 / (N : ℝ) = (N : ℝ) := by field_simp
      rw [heq]
      exact_mod_cast Nat.totient_le N)

/-- The logarithmically weighted totient sum in a multiplicative interval. -/
theorem weighted_totient_Icc_tendsto (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun N : ℕ => ∑ y ∈ Finset.Icc N ⌊c * (N : ℝ)⌋₊,
        (Nat.totient y : ℝ) / (y : ℝ) ^ 2)
      atTop (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by
  have hIoc : Tendsto
      (fun N : ℕ => ∑ y ∈ Finset.Ioc N ⌊c * (N : ℝ)⌋₊,
        (Nat.totient y : ℝ) / (y : ℝ) ^ 2)
      atTop (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by
    exact (tendsto_mobiusWindow_tsum c hc).congr
      (fun N => tsum_mobiusWindow_eq_Ioc c hc.le N)
  have hadd := tendsto_totient_term_zero.add hIoc
  have hadd' : Tendsto
      (fun N : ℕ => (Nat.totient N : ℝ) / (N : ℝ) ^ 2 +
        ∑ y ∈ Finset.Ioc N ⌊c * (N : ℝ)⌋₊,
          (Nat.totient y : ℝ) / (y : ℝ) ^ 2)
      atTop (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by simpa using hadd
  apply hadd'.congr'
  filter_upwards with N
  symm
  have hNQ := floor_mul_ge c hc.le N
  rw [show Finset.Icc N ⌊c * (N : ℝ)⌋₊ =
      insert N (Finset.Ioc N ⌊c * (N : ℝ)⌋₊) by
        ext y
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
        omega]
  rw [Finset.sum_insert (by simp)]

theorem weighted_totient_Icc_tendsto_of_one_le (c : ℝ) (hc : 1 ≤ c) :
    Tendsto
      (fun N : ℕ => ∑ y ∈ Finset.Icc N ⌊c * (N : ℝ)⌋₊,
        (Nat.totient y : ℝ) / (y : ℝ) ^ 2)
      atTop (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by
  rcases hc.eq_or_lt with rfl | hc
  · convert tendsto_totient_term_zero using 1
    · funext N
      simp
    · simp
  · exact weighted_totient_Icc_tendsto c hc

lemma isOpen_approximableSet (N : ℕ) (A c : ℝ) :
    IsOpen (approximableSet N A c) := by
  rw [isOpen_iff_mem_nhds]
  intro α hα
  rcases hα with ⟨⟨hα0, hα1⟩, x, y, hy, hNy, hyc, hxy, happrox⟩
  have hunit : Ioo (0 : ℝ) 1 ∈ 𝓝 α := Ioo_mem_nhds hα0 hα1
  have hopen : IsOpen (approximationInterval A x y) := isOpen_Ioo
  have hinterval : approximationInterval A x y ∈ 𝓝 α :=
    hopen.mem_nhds (mem_approximationInterval.mpr happrox)
  filter_upwards [hunit, hinterval] with β hβunit hβinterval
  exact ⟨hβunit, x, y, hy, hNy, hyc, hxy,
    mem_approximationInterval.mp hβinterval⟩

lemma measurableSet_approximableSet (N : ℕ) (A c : ℝ) :
    MeasurableSet (approximableSet N A c) :=
  (isOpen_approximableSet N A c).measurableSet

lemma approximableSet_subset (N : ℕ) (A c : ℝ) :
    approximableSet N A c ⊆ Ioo (0 : ℝ) 1 :=
  fun _ hα ↦ hα.1

lemma S_nonneg (N : ℕ) (A c : ℝ) : 0 ≤ S N A c :=
  measureReal_nonneg

lemma S_le_one (N : ℕ) (A c : ℝ) : S N A c ≤ 1 := by
  rw [S]
  calc
    volume.real (approximableSet N A c) ≤ volume.real (Ioo (0 : ℝ) 1) :=
      measureReal_mono (approximableSet_subset N A c) (by
        rw [Real.volume_Ioo]
        simp)
    _ = 1 := by simp

/-- The literal assertion that `f` is the limiting distribution value. -/
def IsLimitValue (A c f : ℝ) : Prop :=
  Tendsto (fun N : ℕ ↦ S N A c) atTop (𝓝 f)

/-- The closed form in the no-overlap range found by Erdős, Szüsz, and
Turán. -/
def sparseLimit (A c : ℝ) : ℝ :=
  12 * A * Real.log c / Real.pi ^ 2

/-- Erdős--Szüsz--Turán's explicit limit in the sparse (no-overlap) range. -/
theorem erdos_1001_sparse (A c : ℝ)
    (hA : 0 < A) (hc : 1 ≤ c) (hAc : A < c / (1 + c ^ 2)) :
    IsLimitValue A c (sparseLimit A c) := by
  have hsum : Tendsto
      (fun N : ℕ => ∑ y ∈ denominatorSet N c,
        (Nat.totient y : ℝ) / (y : ℝ) ^ 2)
      atTop (𝓝 (6 / Real.pi ^ 2 * Real.log c)) := by
    simpa only [denominatorSet] using weighted_totient_Icc_tendsto_of_one_le c hc
  have hscaled : Tendsto
      (fun N : ℕ => 2 * A *
        (∑ y ∈ denominatorSet N c,
          (Nat.totient y : ℝ) / (y : ℝ) ^ 2))
      atTop (𝓝 (sparseLimit A c)) := by
    convert tendsto_const_nhds.mul hsum using 1
    · dsimp [sparseLimit]
      field_simp [Real.pi_ne_zero]
      ring
  rw [IsLimitValue]
  apply hscaled.congr'
  have hAN : ∀ᶠ N : ℕ in atTop, A < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop A)
  filter_upwards [eventually_ge_atTop 2, hAN] with N hN2 hAN
  exact (S_eq_totientSum hA hN2 hAN hc hAc).symm

/-! ### Finite inclusion--exclusion and bounded offset families -/

namespace FiniteInclusionExclusion

variable {X ι : Type*} [MeasurableSpace X]
variable (s : ι → Set X) (t : Finset ι) (μ : Measure X)

lemma sum_nonempty_powerset_by_card
    {M : Type*} [AddCommMonoid M] (F : Finset ι → M) :
    ∑ u ∈ t.powerset with u.Nonempty, F u =
      ∑ k ∈ Finset.range (t.card + 1),
        ∑ u ∈ t.powersetCard k with u.Nonempty, F u := by
  simp_rw [Finset.sum_filter]
  exact Finset.sum_powerset t (fun u ↦ if u.Nonempty then F u else 0)

lemma sum_powerset_filter_of_zero
    {M : Type*} [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p]
    (F : Finset ι → M)
    (hzero : ∀ u ∈ t.powerset, (∃ x ∈ u, ¬ p x) → F u = 0) :
    ∑ u ∈ t.powerset, F u =
      ∑ u ∈ (t.filter p).powerset, F u := by
  classical
  symm
  apply Finset.sum_subset
  · exact Finset.powerset_mono.mpr (Finset.filter_subset p t)
  · intro u hu huf
    apply hzero u hu
    have hnot : ¬ u ⊆ t.filter p := by
      simpa [Finset.mem_powerset] using huf
    obtain ⟨x, hxu, hxnot⟩ := Finset.not_subset.mp hnot
    exact ⟨x, hxu, fun hpx ↦ hxnot (Finset.mem_filter.mpr
      ⟨(Finset.mem_powerset.mp hu) hxu, hpx⟩)⟩

lemma sum_powerset_image_of_injective
    [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    {d : Finset ι} {f : ι → ι} (hf : Function.Injective f)
    (F : Finset ι → M) :
    ∑ v ∈ (d.image f).powerset, F v =
      ∑ w ∈ d.powerset, F (w.image f) := by
  classical
  rw [Finset.powerset_image]
  apply Finset.sum_image
  intro u hu v hv huv
  exact Finset.image_injective hf huv

/-- Positive offsets, at most `K`, whose translates by `i` still belong to
the given index family. -/
def admissibleOffsets (q : Finset ℕ) (i K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun d ↦ i + d ∈ q)

lemma boundedWindow_eq_image_admissibleOffsets
    (q : Finset ℕ) (i K : ℕ) :
    (q.filter (i < ·)).filter (fun j ↦ j - i ≤ K) =
      (admissibleOffsets q i K).image (fun d ↦ i + d) := by
  classical
  ext j
  constructor
  · intro hj
    rw [Finset.mem_filter] at hj
    rcases hj with ⟨hj, hjK⟩
    rw [Finset.mem_filter] at hj
    rcases hj with ⟨hjq, hij⟩
    rw [Finset.mem_image]
    refine ⟨j - i, ?_, Nat.add_sub_of_le hij.le⟩
    rw [admissibleOffsets, Finset.mem_filter, Finset.mem_Icc]
    have hsum : i + (j - i) = j := Nat.add_sub_of_le hij.le
    exact ⟨⟨Nat.sub_pos_iff_lt.mpr hij, hjK⟩, by simpa only [hsum] using hjq⟩
  · intro hj
    rw [Finset.mem_image] at hj
    obtain ⟨d, hd, rfl⟩ := hj
    rw [admissibleOffsets, Finset.mem_filter, Finset.mem_Icc] at hd
    rcases hd with ⟨⟨hd1, hdK⟩, hdiq⟩
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨hdiq, Nat.lt_add_of_pos_right hd1⟩, ?_⟩
    simpa using hdK

lemma admissibleOffsets_Icc
    {L U i K : ℕ} (hi : i ∈ Finset.Icc L U) :
    admissibleOffsets (Finset.Icc L U) i K =
      Finset.Icc 1 (min K (U - i)) := by
  classical
  ext d
  rw [admissibleOffsets]
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_min]
  constructor
  · rintro ⟨⟨hd1, hdK⟩, hdi⟩
    exact ⟨hd1, hdK, Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hdi.2)⟩
  · rintro ⟨hd1, hdK, hdU⟩
    rw [Finset.mem_Icc] at hi
    refine ⟨⟨hd1, hdK⟩, ⟨hi.1.trans ?_, ?_⟩⟩
    · exact Nat.le_add_right i d
    · simpa [Nat.add_comm] using Nat.add_le_of_le_sub hi.2 hdU

lemma sum_nonempty_powerset_by_min
    [LinearOrder ι] {M : Type*} [AddCommMonoid M]
    (F : Finset ι → M) :
    ∑ u ∈ t.powerset with u.Nonempty, F u =
      ∑ i ∈ t, ∑ v ∈ (t.filter (i < ·)).powerset, F (insert i v) := by
  classical
  have hsum :
      ∑ u ∈ t.powerset with u.Nonempty, F u =
        ∑ p ∈ t.sigma (fun i ↦ (t.filter (i < ·)).powerset),
          F (insert p.1 p.2) := by
    refine Finset.sum_bij'
      (i := fun u hu ↦
        (⟨u.min' ((Finset.mem_filter.mp hu).2),
          u.erase (u.min' ((Finset.mem_filter.mp hu).2))⟩ : Σ _ : ι, Finset ι))
      (j := fun p _ ↦ insert p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hpow := (Finset.mem_filter.mp hu).1
      have hne := (Finset.mem_filter.mp hu).2
      rw [Finset.mem_sigma]
      constructor
      · exact (Finset.mem_powerset.mp hpow) (u.min'_mem hne)
      · rw [Finset.mem_powerset]
        intro x hx
        have hxu : x ∈ u := Finset.mem_of_mem_erase hx
        rw [Finset.mem_filter]
        refine ⟨(Finset.mem_powerset.mp hpow) hxu, ?_⟩
        exact lt_of_le_of_ne (u.min'_le x hxu) (Ne.symm (Finset.ne_of_mem_erase hx))
    · rintro ⟨i, v⟩ hp
      rw [Finset.mem_sigma] at hp
      rw [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact hp.1
        · exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp hp.2) hx)).1
      · exact ⟨i, Finset.mem_insert_self i v⟩
    · intro u hu
      have hne := (Finset.mem_filter.mp hu).2
      simp only
      exact Finset.insert_erase (u.min'_mem hne)
    · rintro ⟨i, v⟩ hp
      rw [Finset.mem_sigma] at hp
      have hiv : i ∉ v := by
        intro hi
        have := (Finset.mem_filter.mp ((Finset.mem_powerset.mp hp.2) hi)).2
        exact (lt_irrefl i this)
      have hine : (insert i v).Nonempty := ⟨i, Finset.mem_insert_self i v⟩
      have hmin : (insert i v).min' hine = i := by
        rw [Finset.min'_eq_iff]
        refine ⟨Finset.mem_insert_self i v, ?_⟩
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · exact ((Finset.mem_filter.mp ((Finset.mem_powerset.mp hp.2) hx)).2).le
      apply Sigma.ext hmin
      simp [hmin, hiv]
    · intro u hu
      have hne := (Finset.mem_filter.mp hu).2
      simp only
      rw [Finset.insert_erase (u.min'_mem hne)]
  exact hsum.trans (Finset.sum_sigma _ _ _)

/-- The finite-measure inclusion--exclusion formula, in the notation used by
the Erdős 1001 development. -/
theorem measureReal_iUnion_finset_eq_sum_intersections
    (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hfin : ∀ i ∈ t, μ (s i) ≠ ∞ := by finiteness) :
    μ.real (⋃ i ∈ t, s i) =
      ∑ u ∈ t.powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) * μ.real (⋂ i ∈ u, s i) := by
  exact measureReal_biUnion_eq_sum_powerset hs hfin

/-- The generic finite-measure formula grouped by the least index in each
nonempty subfamily. -/
theorem measureReal_iUnion_finset_eq_sum_min_intersections
    [LinearOrder ι]
    (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hfin : ∀ i ∈ t, μ (s i) ≠ ∞ := by finiteness) :
    μ.real (⋃ i ∈ t, s i) =
      ∑ i ∈ t, ∑ v ∈ (t.filter (i < ·)).powerset,
        (-1 : ℝ) ^ (v.card + 2) *
          μ.real (⋂ j ∈ insert i v, s j) := by
  classical
  rw [measureReal_iUnion_finset_eq_sum_intersections s t μ hs hfin,
    sum_nonempty_powerset_by_min t]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro v hv
  have hiv : i ∉ v := by
    intro hiv
    have hiiv := (Finset.mem_filter.mp
      ((Finset.mem_powerset.mp hv) hiv)).2
    exact (lt_irrefl i hiiv)
  rw [Finset.card_insert_of_notMem hiv]

/-- If every intersection reaching farther than `K` beyond its least natural
index is empty, the least-index inclusion--exclusion sum truncates to the
window of positive offsets at most `K`. -/
theorem measureReal_iUnion_finset_eq_sum_bounded_offsets
    (q : Finset ℕ) (r : ℕ → Set X) (K : ℕ) (ν : Measure X)
    (hr : ∀ i ∈ q, MeasurableSet (r i))
    (hfin : ∀ i ∈ q, ν (r i) ≠ ∞ := by finiteness)
    (hfar : ∀ i ∈ q, ∀ v ∈ (q.filter (i < ·)).powerset,
      (∃ j ∈ v, K < j - i) → ⋂ j ∈ insert i v, r j = ∅) :
    ν.real (⋃ i ∈ q, r i) =
      ∑ i ∈ q,
        ∑ v ∈ ((q.filter (i < ·)).filter (fun j ↦ j - i ≤ K)).powerset,
          (-1 : ℝ) ^ (v.card + 2) *
            ν.real (⋂ j ∈ insert i v, r j) := by
  classical
  rw [measureReal_iUnion_finset_eq_sum_min_intersections r q ν hr hfin]
  apply Finset.sum_congr rfl
  intro i hi
  apply sum_powerset_filter_of_zero
  intro v hv hbad
  obtain ⟨j, hjv, hjbad⟩ := hbad
  have hempty := hfar i hi v hv ⟨j, hjv, Nat.lt_of_not_ge hjbad⟩
  rw [hempty, measureReal_empty, mul_zero]

/-- Fully offset-indexed version of
`measureReal_iUnion_finset_eq_sum_bounded_offsets`.  Every inner summation is
over subsets of `{1, …, K}`; `admissibleOffsets` merely removes translations
which fall outside `q`. -/
theorem measureReal_iUnion_finset_eq_sum_offset_subsets
    (q : Finset ℕ) (r : ℕ → Set X) (K : ℕ) (ν : Measure X)
    (hr : ∀ i ∈ q, MeasurableSet (r i))
    (hfin : ∀ i ∈ q, ν (r i) ≠ ∞ := by finiteness)
    (hfar : ∀ i ∈ q, ∀ v ∈ (q.filter (i < ·)).powerset,
      (∃ j ∈ v, K < j - i) → ⋂ j ∈ insert i v, r j = ∅) :
    ν.real (⋃ i ∈ q, r i) =
      ∑ i ∈ q,
        ∑ w ∈ (admissibleOffsets q i K).powerset,
          (-1 : ℝ) ^ (w.card + 2) *
            ν.real
              (⋂ j ∈ insert i (w.image (fun d ↦ i + d)), r j) := by
  classical
  rw [measureReal_iUnion_finset_eq_sum_bounded_offsets q r K ν hr hfin hfar]
  apply Finset.sum_congr rfl
  intro i hi
  rw [boundedWindow_eq_image_admissibleOffsets]
  rw [sum_powerset_image_of_injective
    (f := fun d ↦ i + d) (fun _ _ h ↦ Nat.add_left_cancel h)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.card_image_of_injective _ (fun _ _ h ↦ Nat.add_left_cancel h)]

/-- Interval-indexed corollary.  Near the right endpoint only the offsets up
to `U - i` remain; away from it the inner family is exactly the powerset of
`{1, …, K}`. -/
theorem measureReal_iUnion_Icc_eq_sum_offset_subsets
    (L U : ℕ) (r : ℕ → Set X) (K : ℕ) (ν : Measure X)
    (hr : ∀ i ∈ Finset.Icc L U, MeasurableSet (r i))
    (hfin : ∀ i ∈ Finset.Icc L U, ν (r i) ≠ ∞ := by finiteness)
    (hfar : ∀ i ∈ Finset.Icc L U,
      ∀ v ∈ ((Finset.Icc L U).filter (i < ·)).powerset,
        (∃ j ∈ v, K < j - i) → ⋂ j ∈ insert i v, r j = ∅) :
    ν.real (⋃ i ∈ Finset.Icc L U, r i) =
      ∑ i ∈ Finset.Icc L U,
        ∑ w ∈ (Finset.Icc 1 (min K (U - i))).powerset,
          (-1 : ℝ) ^ (w.card + 2) *
            ν.real
              (⋂ j ∈ insert i (w.image (fun d ↦ i + d)), r j) := by
  rw [measureReal_iUnion_finset_eq_sum_offset_subsets
    (Finset.Icc L U) r K ν hr hfin hfar]
  apply Finset.sum_congr rfl
  intro i hi
  rw [admissibleOffsets_Icc hi]

end FiniteInclusionExclusion

/-! ### Farey sequences and the Farey-triangle parametrization -/

namespace Farey

/-- Reduced fractions in `[0,1]` whose denominator is at most `Q`. -/
structure Fraction (Q : ℕ) where
  num : ℕ
  den : ℕ
  den_pos : 0 < den
  den_le : den ≤ Q
  num_le : num ≤ den
  reduced : Nat.Coprime num den
  deriving DecidableEq

namespace Fraction

@[ext]
theorem ext {Q : ℕ} {p q : Fraction Q} (hnum : p.num = q.num) (hden : p.den = q.den) :
    p = q := by
  cases p
  cases q
  simp_all

noncomputable instance (Q : ℕ) : Fintype (Fraction Q) :=
  Fintype.ofInjective
    (fun p : Fraction Q =>
      ((⟨p.num, Nat.lt_succ_of_le (p.num_le.trans p.den_le)⟩ : Fin (Q + 1)),
       (⟨p.den, Nat.lt_succ_of_le p.den_le⟩ : Fin (Q + 1))))
    (by
      intro p q h
      apply Fraction.ext
      · exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.2.1) h)

/-- The value of a reduced fraction, regarded as a rational number. -/
def value {Q : ℕ} (p : Fraction Q) : ℚ := p.num / p.den

theorem value_lt_iff {Q : ℕ} (p q : Fraction Q) :
    p.value < q.value ↔ p.num * q.den < q.num * p.den := by
  rw [value, value, div_lt_div_iff₀]
  · norm_cast
  · exact_mod_cast p.den_pos
  · exact_mod_cast q.den_pos

theorem value_injective {Q : ℕ} : Function.Injective (@value Q) := by
  intro p q h
  have hcrossQ : (p.num : ℚ) * q.den = q.num * p.den :=
    (div_eq_div_iff (by exact_mod_cast p.den_pos.ne')
      (by exact_mod_cast q.den_pos.ne')).mp h
  have hcross : p.num * q.den = q.num * p.den := by exact_mod_cast hcrossQ
  have hpden_dvd_qden : p.den ∣ q.den := by
    apply p.reduced.symm.dvd_of_dvd_mul_left
    use q.num
    simpa [mul_comm] using hcross
  have hqden_dvd_pden : q.den ∣ p.den := by
    apply q.reduced.symm.dvd_of_dvd_mul_left
    use p.num
    simpa [mul_comm] using hcross.symm
  have hden : p.den = q.den := Nat.dvd_antisymm hpden_dvd_qden hqden_dvd_pden
  apply Fraction.ext
  · apply Nat.eq_of_mul_eq_mul_right p.den_pos
    simpa [hden] using hcross
  · exact hden

/-- The finite Farey sequence, sorted by rational value. -/
noncomputable def sequence (Q : ℕ) : List (Fraction Q) := by
  letI : Std.Antisymm (Function.onFun (fun x y : ℚ => x ≤ y) (@value Q)) :=
    Function.Injective.antisymm_onFun (fun x y : ℚ => x ≤ y) (f := @value Q) value_injective
  exact (Finset.univ : Finset (Fraction Q)).sort
    (Function.onFun (fun x y : ℚ => x ≤ y) value)

theorem mem_sequence {Q : ℕ} (p : Fraction Q) : p ∈ sequence Q := by
  letI : Std.Antisymm (Function.onFun (fun x y : ℚ => x ≤ y) (@value Q)) :=
    Function.Injective.antisymm_onFun (fun x y : ℚ => x ≤ y) (f := @value Q) value_injective
  rw [sequence, Finset.mem_sort]
  exact Finset.mem_univ p

theorem sequence_pairwise {Q : ℕ} : (sequence Q).Pairwise (fun p q => p.value ≤ q.value) := by
  letI : Std.Antisymm (Function.onFun (fun x y : ℚ => x ≤ y) (@value Q)) :=
    Function.Injective.antisymm_onFun (fun x y : ℚ => x ≤ y) (f := @value Q) value_injective
  exact Finset.pairwise_sort (Finset.univ : Finset (Fraction Q))
    (Function.onFun (fun x y : ℚ => x ≤ y) value)

theorem sequence_nodup {Q : ℕ} : (sequence Q).Nodup := by
  letI : Std.Antisymm (Function.onFun (fun x y : ℚ => x ≤ y) (@value Q)) :=
    Function.Injective.antisymm_onFun (fun x y : ℚ => x ≤ y) (f := @value Q) value_injective
  exact Finset.sort_nodup (Finset.univ : Finset (Fraction Q))
    (Function.onFun (fun x y : ℚ => x ≤ y) value)

end Fraction

/-- A factor common to the two right-hand factors in a determinant-one
identity must be one. -/
theorem coprime_cross_of_det_one {a b c d : ℕ} (h : a * b = c * d + 1) :
    Nat.Coprime b c := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  apply (Nat.dvd_add_iff_right
    (Nat.dvd_mul_right_of_dvd (Nat.gcd_dvd_right b c) d)).mpr
  rw [← h]
  simpa [mul_comm] using Nat.dvd_mul_right_of_dvd (Nat.gcd_dvd_left b c) a

/-- The two denominator factors in a determinant-one identity are coprime. -/
theorem coprime_denominators_of_det_one {a b c d : ℕ} (h : a * b = c * d + 1) :
    Nat.Coprime b d := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  have hcd : b.gcd d ∣ c * d :=
    Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right b d) c
  apply (Nat.dvd_add_iff_right hcd).mpr
  rw [← h]
  exact Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_left b d) a

/-- Both endpoint fractions in a determinant-one identity are reduced. -/
theorem reduced_endpoints_of_det_one {a b c d : ℕ} (h : c * b = a * d + 1) :
    Nat.Coprime a b ∧ Nat.Coprime c d := by
  constructor
  · exact (coprime_cross_of_det_one (a := c) (b := b) (c := a) (d := d) h).symm
  · apply coprime_cross_of_det_one (a := b) (b := c) (c := d) (d := a)
    simpa [mul_comm] using h

/-- The denominator data indexing algebraic Farey edges of order `Q`. -/
structure DenominatorPair (Q : ℕ) where
  u : ℕ+
  v : ℕ+
  u_le : (u : ℕ) ≤ Q
  v_le : (v : ℕ) ≤ Q
  coprime : Nat.Coprime u v
  cutoff : Q < (u : ℕ) + v
  deriving DecidableEq

namespace DenominatorPair

/-- Canonical left numerator supplied by extended Euclid. -/
def leftNum {Q : ℕ} (p : DenominatorPair Q) : ℕ := PNat.gcdX p.u p.v

/-- Canonical right numerator supplied by extended Euclid. -/
def rightNum {Q : ℕ} (p : DenominatorPair Q) : ℕ := PNat.gcdZ p.u p.v

theorem det_one {Q : ℕ} (p : DenominatorPair Q) :
    p.rightNum * (p.u : ℕ) = p.leftNum * (p.v : ℕ) + 1 := by
  simpa [leftNum, rightNum, p.coprime.gcd_eq_one] using PNat.gcd_rel_left p.u p.v

theorem leftNum_lt {Q : ℕ} (p : DenominatorPair Q) : p.leftNum < (p.u : ℕ) := by
  have ha0 := PNat.gcd_a_eq p.u p.v
  have hcoe := PNat.gcdA'_coe p.u p.v
  have hgcd : PNat.gcd p.u p.v = 1 := by
    apply Subtype.ext
    exact p.coprime.gcd_eq_one
  have ha : p.u = PNat.gcdA' p.u p.v := by simpa [hgcd] using ha0
  have : (p.u : ℕ) = PNat.gcdW p.u p.v + PNat.gcdX p.u p.v := by
    calc
      (p.u : ℕ) = (PNat.gcdA' p.u p.v : ℕ) := congrArg Subtype.val ha
      _ = _ := hcoe
  rw [this, leftNum]
  exact Nat.lt_add_of_pos_left (by positivity)

theorem rightNum_le {Q : ℕ} (p : DenominatorPair Q) : p.rightNum ≤ (p.v : ℕ) := by
  have hb0 := PNat.gcd_b_eq p.u p.v
  have hcoe := PNat.gcdB'_coe p.u p.v
  have hgcd : PNat.gcd p.u p.v = 1 := by
    apply Subtype.ext
    exact p.coprime.gcd_eq_one
  have hb : p.v = PNat.gcdB' p.u p.v := by simpa [hgcd] using hb0
  have : (p.v : ℕ) = PNat.gcdY p.u p.v + PNat.gcdZ p.u p.v := by
    calc
      (p.v : ℕ) = (PNat.gcdB' p.u p.v : ℕ) := congrArg Subtype.val hb
      _ = _ := hcoe
  rw [this, rightNum]
  exact Nat.le_add_left _ _

def left {Q : ℕ} (p : DenominatorPair Q) : Fraction Q where
  num := p.leftNum
  den := p.u
  den_pos := by positivity
  den_le := p.u_le
  num_le := (p.leftNum_lt).le
  reduced := (reduced_endpoints_of_det_one p.det_one).1

def right {Q : ℕ} (p : DenominatorPair Q) : Fraction Q where
  num := p.rightNum
  den := p.v
  den_pos := by positivity
  den_le := p.v_le
  num_le := p.rightNum_le
  reduced := (reduced_endpoints_of_det_one p.det_one).2

theorem left_value_lt_right_value {Q : ℕ} (p : DenominatorPair Q) :
    p.left.value < p.right.value := by
  rw [Fraction.value_lt_iff]
  change p.leftNum * (p.v : ℕ) < p.rightNum * (p.u : ℕ)
  have := p.det_one
  omega

end DenominatorPair

theorem pnat_gcdX_lt_left (u v : ℕ+) (hcop : Nat.Coprime u v) :
    PNat.gcdX u v < (u : ℕ) := by
  have ha0 := PNat.gcd_a_eq u v
  have hcoe := PNat.gcdA'_coe u v
  have hgcd : PNat.gcd u v = 1 := by
    apply Subtype.ext
    exact hcop.gcd_eq_one
  have ha : u = PNat.gcdA' u v := by simpa [hgcd] using ha0
  have hu : (u : ℕ) = PNat.gcdW u v + PNat.gcdX u v := by
    calc
      (u : ℕ) = (PNat.gcdA' u v : ℕ) := congrArg Subtype.val ha
      _ = _ := hcoe
  rw [hu]
  exact Nat.lt_add_of_pos_left (by positivity)

/-- Every nonterminal reduced fraction of order `Q` has a determinant-one
right neighbor whose denominator is maximal in the appropriate residue class.
This is the modular-inverse construction in the classical proof of Farey's
theorem. -/
theorem exists_det_one_right_neighbor {Q : ℕ} (p : Fraction Q)
    (hp : p.num < p.den) :
    ∃ r : Fraction Q,
      r.num * p.den = p.num * r.den + 1 ∧ Q < p.den + r.den := by
  have hQ : 0 < Q := p.den_pos.trans_le p.den_le
  by_cases ha0 : p.num = 0
  · have hb1 : p.den = 1 := by
      simpa [ha0] using p.reduced.gcd_eq_one
    let r : Fraction Q :=
      { num := 1
        den := Q
        den_pos := hQ
        den_le := le_rfl
        num_le := hQ
        reduced := Nat.coprime_one_left Q }
    refine ⟨r, ?_, ?_⟩
    · simp [r, ha0, hb1]
    · simp [r, hb1]
  · have ha : 0 < p.num := Nat.pos_of_ne_zero ha0
    let u : ℕ+ := ⟨p.den, p.den_pos⟩
    let v : ℕ+ := ⟨p.num, ha⟩
    have huv : Nat.Coprime u v := by simpa [u, v] using p.reduced.symm
    let s : ℕ := PNat.gcdX u v
    let z : ℕ := PNat.gcdZ u v
    have hslt : s < p.den := by
      simpa [s, u, v] using pnat_gcdX_lt_left u v huv
    have hbase : z * p.den = s * p.num + 1 := by
      have hgcd : PNat.gcd u v = 1 := by
        apply Subtype.ext
        exact huv.gcd_eq_one
      have hrel := PNat.gcd_rel_left u v
      rw [hgcd] at hrel
      simpa [z, s, u, v] using hrel
    have hspos : 0 < s := by
      by_contra hs0
      have hs0' : s = 0 := Nat.eq_zero_of_not_pos hs0
      rw [hs0', zero_mul, zero_add] at hbase
      have hb1 : p.den = 1 := by
        have hzpos : 0 < z := by simp [z]
        nlinarith
      omega
    have hzle : z ≤ s := by
      by_contra hzs
      have hsz : s < z := Nat.lt_of_not_ge hzs
      nlinarith [Nat.mul_le_mul_right s hp.le]
    let k : ℕ := (Q - s) / p.den
    let y : ℕ := s + k * p.den
    let x : ℕ := z + k * p.num
    have hsQ : s ≤ Q := hslt.le.trans p.den_le
    have hyQ : y ≤ Q := by
      calc
        y = s + k * p.den := rfl
        _ ≤ s + (Q - s) := Nat.add_le_add_left (Nat.div_mul_le_self _ _) s
        _ = Q := Nat.add_sub_of_le hsQ
    have hypos : 0 < y := by simp only [y]; omega
    have hxy : x ≤ y := by
      dsimp [x, y]
      exact Nat.add_le_add hzle (Nat.mul_le_mul_left k hp.le)
    have hdet : x * p.den = p.num * y + 1 := by
      dsimp [x, y]
      rw [add_mul, mul_add]
      nlinarith
    have hcutoff : Q < p.den + y := by
      have htail := Nat.lt_div_mul_add (a := Q - s) p.den_pos
      have hQsplit : s + (Q - s) = Q := Nat.add_sub_of_le hsQ
      dsimp [k, y]
      omega
    let r : Fraction Q :=
      { num := x
        den := y
        den_pos := hypos
        den_le := hyQ
        num_le := hxy
        reduced := (reduced_endpoints_of_det_one hdet).2 }
    exact ⟨r, hdet, hcutoff⟩

/-- A fraction strictly between determinant-one endpoints has denominator at
least the sum of the endpoint denominators. -/
theorem denominator_sum_le_of_between
    {a b c d x y : ℕ}
    (hdet : c * b = a * d + 1)
    (hleft : a * y < x * b) (hright : x * d < c * y) :
    b + d ≤ y := by
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt hleft
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hright
  nlinarith

/-- Hence the canonical edge associated to a coprime pair in the Farey
triangle has no order-`Q` reduced fraction strictly between its endpoints. -/
theorem DenominatorPair.no_fraction_between {Q : ℕ} (p : DenominatorPair Q)
    (r : Fraction Q) :
    ¬ (p.left.value < r.value ∧ r.value < p.right.value) := by
  intro h
  have hleft := (Fraction.value_lt_iff p.left r).mp h.1
  have hright := (Fraction.value_lt_iff r p.right).mp h.2
  have hsum : (p.u : ℕ) + p.v ≤ r.den := by
    apply denominator_sum_le_of_between (a := p.leftNum) (c := p.rightNum) (x := r.num)
      (y := r.den)
    · exact p.det_one
    · simpa [DenominatorPair.left] using hleft
    · simpa [DenominatorPair.right] using hright
  exact (not_lt_of_ge r.den_le) (lt_of_lt_of_le p.cutoff hsum)

/-- Two determinant-one solutions with the same positive coprime denominator
pair and left numerator in the standard residue range coincide. -/
theorem det_solution_unique {u v a c x z : ℕ}
    (hu : 0 < u) (hcop : Nat.Coprime u v)
    (ha : a < u) (hx : x < u)
    (h₁ : c * u = a * v + 1) (h₂ : z * u = x * v + 1) :
    a = x ∧ c = z := by
  have ha0 : a * v + 1 ≡ 0 [MOD u] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    use c
    simpa [mul_comm] using h₁.symm
  have hx0 : x * v + 1 ≡ 0 [MOD u] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    use z
    simpa [mul_comm] using h₂.symm
  have havxv : a * v ≡ x * v [MOD u] :=
    Nat.ModEq.add_right_cancel' 1 (ha0.trans hx0.symm)
  have haxmod : a ≡ x [MOD u] :=
    havxv.cancel_right_of_coprime hcop.gcd_eq_one
  have hax : a = x := haxmod.eq_of_lt_of_lt ha hx
  constructor
  · exact hax
  · apply Nat.eq_of_mul_eq_mul_right hu
    rw [h₁, h₂, hax]

/-- Algebraic consecutive Farey fractions of order `Q`.  The determinant-one
condition fixes the orientation, and the cutoff is the usual
`Q < left.den + right.den` criterion. -/
structure Edge (Q : ℕ) where
  left : Fraction Q
  right : Fraction Q
  det_one : right.num * left.den = left.num * right.den + 1
  cutoff : Q < left.den + right.den
  deriving DecidableEq

namespace Edge

theorem ext' {Q : ℕ} {e f : Edge Q} (hleft : e.left = f.left)
    (hright : e.right = f.right) : e = f := by
  cases e
  cases f
  simp_all

theorem left_num_lt {Q : ℕ} (e : Edge Q) : e.left.num < e.left.den := by
  by_contra h
  have heq : e.left.num = e.left.den := Nat.le_antisymm e.left.num_le (Nat.le_of_not_gt h)
  have hmul := Nat.mul_le_mul_right e.left.den e.right.num_le
  have hdet := e.det_one
  rw [heq] at hdet
  nlinarith [hmul]

theorem left_value_lt_right_value {Q : ℕ} (e : Edge Q) :
    e.left.value < e.right.value := by
  rw [Fraction.value_lt_iff]
  have := e.det_one
  omega

/-- Forget the uniquely determined numerators. -/
def toDenominatorPair {Q : ℕ} (e : Edge Q) : DenominatorPair Q where
  u := ⟨e.left.den, e.left.den_pos⟩
  v := ⟨e.right.den, e.right.den_pos⟩
  u_le := e.left.den_le
  v_le := e.right.den_le
  coprime := coprime_denominators_of_det_one e.det_one
  cutoff := e.cutoff

/-- Build the unique algebraic Farey edge associated to denominator data in
the Farey triangle. -/
def ofDenominatorPair {Q : ℕ} (p : DenominatorPair Q) : Edge Q where
  left := p.left
  right := p.right
  det_one := p.det_one
  cutoff := p.cutoff

theorem toDenominatorPair_ofDenominatorPair {Q : ℕ} (p : DenominatorPair Q) :
    toDenominatorPair (ofDenominatorPair p) = p := by
  cases p
  rfl

theorem ofDenominatorPair_toDenominatorPair {Q : ℕ} (e : Edge Q) :
    ofDenominatorPair (toDenominatorPair e) = e := by
  have hcanon := (toDenominatorPair e).det_one
  have huniq := det_solution_unique
    e.left.den_pos
    (coprime_denominators_of_det_one e.det_one)
    e.left_num_lt
    (toDenominatorPair e).leftNum_lt
    e.det_one
    hcanon
  have hleft : (ofDenominatorPair (toDenominatorPair e)).left = e.left := by
    apply Fraction.ext
    · exact huniq.1.symm
    · rfl
  have hright : (ofDenominatorPair (toDenominatorPair e)).right = e.right := by
    apply Fraction.ext
    · exact huniq.2.symm
    · rfl
  exact ext' hleft hright

/-- Consecutive algebraic Farey edges are in bijection with coprime lattice
points `(u,v)` in the Farey triangle `u,v ≤ Q < u+v`. -/
def denominatorPairEquiv (Q : ℕ) : Edge Q ≃ DenominatorPair Q where
  toFun := toDenominatorPair
  invFun := ofDenominatorPair
  left_inv := ofDenominatorPair_toDenominatorPair
  right_inv := toDenominatorPair_ofDenominatorPair

theorem no_fraction_between {Q : ℕ} (e : Edge Q) (r : Fraction Q) :
    ¬ (e.left.value < r.value ∧ r.value < e.right.value) := by
  have h := (toDenominatorPair e).no_fraction_between r
  change ¬ ((ofDenominatorPair (toDenominatorPair e)).left.value < r.value ∧
    r.value < (ofDenominatorPair (toDenominatorPair e)).right.value) at h
  rw [ofDenominatorPair_toDenominatorPair] at h
  exact h

end Edge

/-- Order-theoretic consecutiveness among all reduced fractions of order
`Q`.  This is equivalent to adjacency in `Fraction.sequence Q`. -/
def Consecutive {Q : ℕ} (p q : Fraction Q) : Prop :=
  p.value < q.value ∧ ∀ r : Fraction Q, ¬ (p.value < r.value ∧ r.value < q.value)

theorem Edge.consecutive {Q : ℕ} (e : Edge Q) : Consecutive e.left e.right := by
  exact ⟨e.left_value_lt_right_value, e.no_fraction_between⟩

theorem Consecutive.left_num_lt {Q : ℕ} {p q : Fraction Q}
    (h : Consecutive p q) : p.num < p.den := by
  have hpq := (Fraction.value_lt_iff p q).mp h.1
  have hqmul := Nat.mul_le_mul_right p.den q.num_le
  by_contra hp
  have hpmul := Nat.mul_le_mul_right q.den (Nat.le_of_not_gt hp)
  nlinarith

/-- The difficult direction of the classical Farey-neighbor criterion:
order-theoretically consecutive reduced fractions have determinant one and
their denominator sum exceeds the order. -/
theorem Consecutive.det_one_and_cutoff {Q : ℕ} {p q : Fraction Q}
    (h : Consecutive p q) :
    q.num * p.den = p.num * q.den + 1 ∧ Q < p.den + q.den := by
  obtain ⟨r, hdet, hcutoff⟩ := exists_det_one_right_neighbor p h.left_num_lt
  have hpr : p.value < r.value := by
    rw [Fraction.value_lt_iff]
    omega
  have hrq : r.value ≤ q.value := by
    apply le_of_not_gt
    intro hqr
    have hpq := (Fraction.value_lt_iff p q).mp h.1
    have hqr' := (Fraction.value_lt_iff q r).mp hqr
    have hsum := denominator_sum_le_of_between
      (a := p.num) (b := p.den) (c := r.num) (d := r.den)
      (x := q.num) (y := q.den) hdet hpq hqr'
    have hsumQ : p.den + r.den ≤ Q := hsum.trans q.den_le
    exact (not_lt_of_ge hsumQ) hcutoff
  have hqr : q.value ≤ r.value := by
    apply le_of_not_gt
    intro hrq'
    exact h.2 r ⟨hpr, hrq'⟩
  have hrqeq : r = q := Fraction.value_injective (le_antisymm hrq hqr)
  subst r
  exact ⟨hdet, hcutoff⟩

theorem Consecutive.det_one {Q : ℕ} {p q : Fraction Q} (h : Consecutive p q) :
    q.num * p.den = p.num * q.den + 1 := h.det_one_and_cutoff.1

theorem Consecutive.denominator_sum_gt {Q : ℕ} {p q : Fraction Q}
    (h : Consecutive p q) : Q < p.den + q.den := h.det_one_and_cutoff.2

def Consecutive.toEdge {Q : ℕ} {p q : Fraction Q} (h : Consecutive p q) : Edge Q where
  left := p
  right := q
  det_one := h.det_one
  cutoff := h.denominator_sum_gt

/-- Ordered pairs that are consecutive among all reduced fractions of order
`Q`. -/
def ConsecutivePair (Q : ℕ) :=
  {pq : Fraction Q × Fraction Q // Consecutive pq.1 pq.2}

/-- The algebraic and order-theoretic notions of a Farey edge coincide. -/
def edgeEquivConsecutivePair (Q : ℕ) : Edge Q ≃ ConsecutivePair Q where
  toFun e := ⟨(e.left, e.right), e.consecutive⟩
  invFun pq := pq.property.toEdge
  left_inv e := Edge.ext' rfl rfl
  right_inv pq := by
    apply Subtype.ext
    rfl

/-- The classical Farey bijection: consecutive fractions of order `Q` are
in bijection with coprime positive denominator pairs in the triangle
`u,v ≤ Q < u+v`. -/
def consecutivePairEquivDenominatorPair (Q : ℕ) :
    ConsecutivePair Q ≃ DenominatorPair Q :=
  (edgeEquivConsecutivePair Q).symm.trans (Edge.denominatorPairEquiv Q)

noncomputable instance (Q : ℕ) : Fintype (ConsecutivePair Q) :=
  Fintype.ofInjective (fun p : ConsecutivePair Q ↦ p.1) Subtype.val_injective

/-- Three consecutive Farey fractions satisfy the classical integral
second-order recurrence. -/
theorem triple_recurrence {Q : ℕ} {p0 p1 p2 : Fraction Q}
    (h01 : Consecutive p0 p1) (h12 : Consecutive p1 p2) :
    let k := (Q + p0.den) / p1.den
    p2.den = k * p1.den - p0.den ∧
      p2.num = k * p1.num - p0.num := by
  have hdet01 := h01.det_one
  have hdet12 := h12.det_one
  have hlinear :
      p1.num * (p0.den + p2.den) = (p0.num + p2.num) * p1.den := by
    nlinarith
  have hdvd : p1.den ∣ p0.den + p2.den := by
    apply p1.reduced.symm.dvd_of_dvd_mul_left
    use p0.num + p2.num
    simpa [mul_comm] using hlinear
  let k0 := (p0.den + p2.den) / p1.den
  have hk0den : k0 * p1.den = p0.den + p2.den := by
    exact Nat.div_mul_cancel hdvd
  have hk0num : k0 * p1.num = p0.num + p2.num := by
    apply Nat.eq_of_mul_eq_mul_right p1.den_pos
    calc
      (k0 * p1.num) * p1.den = p1.num * (k0 * p1.den) := by ring
      _ = p1.num * (p0.den + p2.den) := by rw [hk0den]
      _ = (p0.num + p2.num) * p1.den := hlinear
  have hlo : k0 * p1.den ≤ Q + p0.den := by
    rw [hk0den]
    simpa [add_comm] using Nat.add_le_add_right p2.den_le p0.den
  have hhi : Q + p0.den < (k0 + 1) * p1.den := by
    have hcut : Q < p1.den + p2.den := h12.denominator_sum_gt
    rw [Nat.add_mul, one_mul, hk0den]
    omega
  have hk : (Q + p0.den) / p1.den = k0 :=
    Nat.div_eq_of_lt_le hlo hhi
  dsimp only
  rw [hk]
  constructor <;> omega

theorem triple_recurrence_add {Q : ℕ} {p0 p1 p2 : Fraction Q}
    (h01 : Consecutive p0 p1) (h12 : Consecutive p1 p2) :
    let k := (Q + p0.den) / p1.den
    p2.den + p0.den = k * p1.den ∧
      p2.num + p0.num = k * p1.num := by
  have hr := triple_recurrence h01 h12
  have hp2num : 0 < p2.num := by
    have hcross := (Fraction.value_lt_iff p1 p2).mp h12.1
    nlinarith
  have hp2den : 0 < p2.den := p2.den_pos
  dsimp only at hr ⊢
  constructor <;> omega

/-- The integer recurrence coefficient is exactly the floor appearing in the
BCZ return map after normalization by `Q`. -/
theorem triple_index_floor {Q : ℕ} {p0 p1 p2 : Fraction Q}
    (hQ : 0 < Q) (_h01 : Consecutive p0 p1) (_h12 : Consecutive p1 p2) :
    ⌊(1 + (p0.den : ℝ) / Q) / ((p1.den : ℝ) / Q)⌋ =
      (((Q + p0.den) / p1.den : ℕ) : ℤ) := by
  have hratio :
      (1 + (p0.den : ℝ) / Q) / ((p1.den : ℝ) / Q) =
        ((Q + p0.den : ℕ) : ℝ) / p1.den := by
    push_cast
    field_simp [hQ.ne', p1.den_pos.ne']
  rw [hratio, Int.floor_div_natCast, Int.floor_natCast, Int.ofNat_ediv_ofNat]

/-- Normalized consecutive denominators follow the BCZ affine update. -/
theorem triple_normalized_denominator_step {Q : ℕ} {p0 p1 p2 : Fraction Q}
    (hQ : 0 < Q) (h01 : Consecutive p0 p1) (h12 : Consecutive p1 p2) :
    (p2.den : ℝ) / Q =
      (((Q + p0.den) / p1.den : ℕ) : ℝ) * ((p1.den : ℝ) / Q) -
        (p0.den : ℝ) / Q := by
  have hadd := (triple_recurrence_add h01 h12).1
  have haddR :
      (p2.den : ℝ) + p0.den =
        (((Q + p0.den) / p1.den : ℕ) : ℝ) * p1.den := by
    exact_mod_cast hadd
  field_simp [hQ.ne']
  nlinarith

/-- The real center represented by a reduced Farey fraction. -/
def Fraction.realValue {Q : ℕ} (p : Fraction Q) : ℝ :=
  (p.num : ℝ) / p.den

theorem Consecutive.realValue_gap {Q : ℕ} {p q : Fraction Q}
    (h : Consecutive p q) :
    q.realValue - p.realValue = 1 / ((p.den : ℝ) * q.den) := by
  have hdetR : (q.num : ℝ) * p.den = (p.num : ℝ) * q.den + 1 := by
    exact_mod_cast h.det_one
  rw [Fraction.realValue, Fraction.realValue]
  field_simp [p.den_pos.ne', q.den_pos.ne']
  nlinarith

/-- The sum of all determinant-one Farey gaps telescopes to the difference
of the endpoint centers. -/
theorem consecutive_chain_center_gap {Q j : ℕ} (q : ℕ → Fraction Q)
    (hchain : ∀ i, Consecutive (q i) (q (i + 1))) :
    (q j).realValue - (q 0).realValue =
      ∑ i ∈ Finset.range j,
        1 / (((q i).den : ℝ) * (q (i + 1)).den) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hstep := (hchain j).realValue_gap
      linarith

/-- Finite-horizon telescoping of consecutive Farey gaps.  This is the
version used for actual finite segments of a Farey sequence. -/
theorem consecutive_chain_center_gap_le {Q j m : ℕ}
    (q : ℕ → Fraction Q) (hjm : j ≤ m)
    (hchain : ∀ i < m, Consecutive (q i) (q (i + 1))) :
    (q j).realValue - (q 0).realValue =
      ∑ i ∈ Finset.range j,
        1 / (((q i).den : ℝ) * (q (i + 1)).den) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ← ih (by omega)]
      have hstep := (hchain j (by omega)).realValue_gap
      linarith

/-- The upper endpoint of the actual approximation interval at offset `j`,
translated so that the offset-zero center is the origin. -/
def actualUpperEndpoint {Q : ℕ} (A : ℝ) (q : ℕ → Fraction Q) (j : ℕ) : ℝ :=
  (q j).realValue - (q 0).realValue + A / ((q j).den : ℝ) ^ 2

/-- The lower endpoint of the actual approximation interval at offset `j`,
translated so that the offset-zero center is the origin. -/
def actualLowerEndpoint {Q : ℕ} (A : ℝ) (q : ℕ → Fraction Q) (j : ℕ) : ℝ :=
  (q j).realValue - (q 0).realValue - A / ((q j).den : ℝ) ^ 2

/-- Actual (unscaled) length of the intersection of the intervals selected
by a nonempty finite set of offsets. -/
def actualOverlapLength {Q : ℕ} (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Fraction Q) : ℝ :=
  max 0
    ((J.image (actualUpperEndpoint A q)).min' (hJ.image _) -
      (J.image (actualLowerEndpoint A q)).max' (hJ.image _))

def actualInterval {Q : ℕ} (A : ℝ) (q : ℕ → Fraction Q) (j : ℕ) : Set ℝ :=
  Ioo (actualLowerEndpoint A q j) (actualUpperEndpoint A q j)

theorem actualInterval_biInter_eq {Q : ℕ} (A : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) (q : ℕ → Fraction Q) :
    (⋂ j ∈ J, actualInterval A q j) =
      Ioo ((J.image (actualLowerEndpoint A q)).max' (hJ.image _))
        ((J.image (actualUpperEndpoint A q)).min' (hJ.image _)) := by
  ext x
  simp only [Set.mem_iInter, actualInterval, Set.mem_Ioo,
    Finset.max'_lt_iff, Finset.lt_min'_iff, Finset.mem_image]
  aesop

theorem volume_real_actualInterval_biInter {Q : ℕ} (A : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) (q : ℕ → Fraction Q) :
    (volume : Measure ℝ).real (⋂ j ∈ J, actualInterval A q j) =
      actualOverlapLength A J hJ q := by
  rw [actualInterval_biInter_eq A J hJ q, Measure.real_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal']
  simp only [actualOverlapLength, max_comm]

theorem actualInterval_eq_preimage_approximationInterval
    {Q : ℕ} (A : ℝ) (q : ℕ → Fraction Q) (j : ℕ) :
    actualInterval A q j =
      (fun x : ℝ ↦ (q 0).realValue + x) ⁻¹'
        approximationInterval A ((q j).num : ℤ) (q j).den := by
  ext x
  simp only [actualInterval, actualLowerEndpoint, actualUpperEndpoint,
    approximationInterval, Set.mem_Ioo, Set.mem_preimage, Fraction.realValue]
  push_cast
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

theorem actualInterval_biInter_eq_preimage_approximationInterval_biInter
    {Q : ℕ} (A : ℝ) (J : Finset ℕ) (q : ℕ → Fraction Q) :
    (⋂ j ∈ J, actualInterval A q j) =
      (fun x : ℝ ↦ (q 0).realValue + x) ⁻¹'
        (⋂ j ∈ J,
          approximationInterval A ((q j).num : ℤ) (q j).den) := by
  ext x
  simp only [Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [actualInterval_eq_preimage_approximationInterval]
  rfl

/-- Translation of all centers by the first Farey fraction does not change
the length of a finite interval intersection. -/
theorem volume_real_approximationInterval_biInter_eq_actualOverlapLength
    {Q : ℕ} (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Fraction Q) :
    (volume : Measure ℝ).real
        (⋂ j ∈ J,
          approximationInterval A ((q j).num : ℤ) (q j).den) =
      actualOverlapLength A J hJ q := by
  rw [← volume_real_actualInterval_biInter A J hJ q,
    actualInterval_biInter_eq_preimage_approximationInterval_biInter]
  let s : Set ℝ := ⋂ j ∈ J,
    approximationInterval A ((q j).num : ℤ) (q j).den
  simpa only [Measure.real_def] using congrArg ENNReal.toReal
    (measure_preimage_add volume (q 0).realValue s).symm

/-- The finite set of all positive denominator pairs in the Farey triangle;
coprimality is imposed separately by the visible-lattice indicator. -/
def denominatorPairFinset (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 Q).product (Finset.Icc 1 Q)).filter
    (fun p => Q < p.1 + p.2)

/-- The ordinary natural-number denominator pair underlying a Farey edge. -/
def DenominatorPair.raw {Q : ℕ} (p : DenominatorPair Q) : ℕ × ℕ :=
  (p.u, p.v)

theorem DenominatorPair.raw_in_denominatorPairFinset {Q : ℕ}
    (p : DenominatorPair Q) : p.raw ∈ denominatorPairFinset Q := by
  rw [denominatorPairFinset, Finset.mem_filter]
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      exact ⟨(Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt p.u.2)), p.u_le⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨(Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt p.v.2)), p.v_le⟩
  · exact p.cutoff

theorem DenominatorPair.raw_coprime {Q : ℕ} (p : DenominatorPair Q) :
    Nat.Coprime p.raw.1 p.raw.2 := p.coprime

theorem DenominatorPair.raw_injective {Q : ℕ} :
    Function.Injective (@DenominatorPair.raw Q) := by
  intro p r h
  cases p
  cases r
  simp_all [DenominatorPair.raw]

/-- The primitive natural denominator pairs in the explicit Farey triangle. -/
def primitiveDenominatorPairFinset (Q : ℕ) : Finset (ℕ × ℕ) :=
  (denominatorPairFinset Q).filter (fun uv ↦ Nat.Coprime uv.1 uv.2)

/-- Denominator-pair structures are exactly the primitive points of the
explicit finite Farey triangle. -/
def denominatorPairEquivCoprimePoint (Q : ℕ) :
    DenominatorPair Q ≃
      {uv : ℕ × ℕ // uv ∈ primitiveDenominatorPairFinset Q} where
  toFun p := ⟨p.raw, Finset.mem_filter.mpr
    ⟨p.raw_in_denominatorPairFinset, p.raw_coprime⟩⟩
  invFun uv := by
    have hprimitive := uv.property
    change uv.1 ∈ (denominatorPairFinset Q).filter
      (fun uv ↦ Nat.Coprime uv.1 uv.2) at hprimitive
    rw [Finset.mem_filter] at hprimitive
    have hmem : uv.1 ∈ denominatorPairFinset Q := hprimitive.1
    change uv.1 ∈
      (((Finset.Icc 1 Q).product (Finset.Icc 1 Q)).filter
        (fun p => Q < p.1 + p.2)) at hmem
    rw [Finset.mem_filter] at hmem
    have hprod' := Finset.mem_product.mp hmem.1
    have hu := Finset.mem_Icc.mp hprod'.1
    have hv := Finset.mem_Icc.mp hprod'.2
    exact
      { u := ⟨uv.1.1, by omega⟩
        v := ⟨uv.1.2, by omega⟩
        u_le := hu.2
        v_le := hv.2
        coprime := hprimitive.2
        cutoff := hmem.2 }
  left_inv p := by
    apply DenominatorPair.raw_injective
    rfl
  right_inv uv := by
    apply Subtype.ext
    rfl

/-- Reindex a sum over all consecutive Farey pairs by the explicit primitive
lattice points in `denominatorPairFinset`. -/
theorem sum_consecutivePair_eq_sum_denominatorPairFinset
    {Q : ℕ} {M : Type*} [AddCommMonoid M] (F : ℕ × ℕ → M) :
    (∑ e : ConsecutivePair Q,
        F ((e.1.1.den, e.1.2.den))) =
      ∑ uv ∈ denominatorPairFinset Q,
        if Nat.Coprime uv.1 uv.2 then F uv else 0 := by
  letI : Fintype {uv : ℕ × ℕ // uv ∈ primitiveDenominatorPairFinset Q} :=
    Fintype.ofFinset (primitiveDenominatorPairFinset Q) (by intro; rfl)
  let e₁ := consecutivePairEquivDenominatorPair Q
  let e₂ := denominatorPairEquivCoprimePoint Q
  let e := e₁.trans e₂
  calc
    (∑ x : ConsecutivePair Q, F ((x.1.1.den, x.1.2.den))) =
        ∑ y : {uv : ℕ × ℕ // uv ∈ primitiveDenominatorPairFinset Q}, F y := by
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = ∑ uv ∈ denominatorPairFinset Q,
          if Nat.Coprime uv.1 uv.2 then F uv else 0 := by
      rw [← Finset.sum_filter]
      let t := primitiveDenominatorPairFinset Q
      rw [show (denominatorPairFinset Q).filter
          (fun uv ↦ Nat.Coprime uv.1 uv.2) = t by rfl]
      change (∑ y ∈ (Finset.univ : Finset
          {uv : ℕ × ℕ // uv ∈ primitiveDenominatorPairFinset Q}),
            F y.1) = ∑ uv ∈ t, F uv
      have huniv : (Finset.univ : Finset
          {uv : ℕ × ℕ // uv ∈ primitiveDenominatorPairFinset Q}) =
          t.attach := by
        change (Finset.univ : Finset {uv : ℕ × ℕ // uv ∈ t}) = t.attach
        ext y
        simp
      rw [huniv]
      simpa using Finset.sum_attach t F

/-- Evaluation of a weight at the normalized denominator pair `(u/Q,v/Q)`. -/
def normalizedDenominatorPairWeight (F : ℝ × ℝ → ℝ)
    (Q : ℕ) (p : ℕ × ℕ) : ℝ :=
  F ((p.1 : ℝ) / Q, (p.2 : ℝ) / Q)

lemma denominatorPairFinset_ne_zero (Q : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ denominatorPairFinset Q) : p ≠ (0, 0) := by
  rw [denominatorPairFinset, Finset.mem_filter] at hp
  intro h
  simp [h] at hp

/-! #### Indexed Farey sequences -/

/-- The fraction at an index of the sorted Farey sequence. -/
def fractionAt (Q : ℕ) (i : Fin (Fraction.sequence Q).length) : Fraction Q :=
  (Fraction.sequence Q).get i

@[simp] theorem fractionAt_def (Q : ℕ) (i : Fin (Fraction.sequence Q).length) :
    fractionAt Q i = (Fraction.sequence Q).get i := rfl

/-- Every fraction of order `Q` occurs at a unique sequence index. -/
theorem existsUnique_fractionAt_eq {Q : ℕ} (p : Fraction Q) :
    ∃! i : Fin (Fraction.sequence Q).length, fractionAt Q i = p := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (Fraction.mem_sequence p)
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Fraction.sequence_nodup.injective_get
  exact hj.trans hi.symm

/-- The indexed Farey sequence is strictly increasing in rational value. -/
theorem fractionAt_value_strictMono {Q : ℕ}
    {i j : Fin (Fraction.sequence Q).length} (hij : i < j) :
    (fractionAt Q i).value < (fractionAt Q j).value := by
  have hle := Fraction.sequence_pairwise.rel_get_of_lt hij
  exact lt_of_le_of_ne hle fun h => by
    have hpq : fractionAt Q i = fractionAt Q j := Fraction.value_injective h
    exact (Fin.ne_of_lt hij) (Fraction.sequence_nodup.injective_get hpq)

/-- Adjacent entries in the sorted sequence are consecutive Farey fractions. -/
theorem consecutive_fractionAt_succ {Q i : ℕ}
    (hi : i + 1 < (Fraction.sequence Q).length) :
    Consecutive
      (fractionAt Q ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩)
      (fractionAt Q ⟨i + 1, hi⟩) := by
  let i₀ : Fin (Fraction.sequence Q).length :=
    ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
  let i₁ : Fin (Fraction.sequence Q).length := ⟨i + 1, hi⟩
  have hi₀i₁ : i₀ < i₁ := by simp [i₀, i₁]
  refine ⟨fractionAt_value_strictMono hi₀i₁, ?_⟩
  intro r
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Fraction.mem_sequence r)
  intro hbetween
  have hij : i₀ < j := by
    apply lt_of_not_ge
    intro hji
    have hrle := Fraction.sequence_pairwise.rel_get_of_le hji
    rw [hj] at hrle
    exact (not_lt_of_ge hrle) hbetween.1
  have hji₁ : j < i₁ := by
    apply lt_of_not_ge
    intro hi₁j
    have hqle := Fraction.sequence_pairwise.rel_get_of_le hi₁j
    rw [hj] at hqle
    exact (not_lt_of_ge hqle) hbetween.2
  change i < j at hij
  change j < i + 1 at hji₁
  omega

/-- Natural positions at which a Farey sequence has a following entry. -/
def ConsecutiveIndex (Q : ℕ) := Fin ((Fraction.sequence Q).length - 1)

noncomputable instance (Q : ℕ) : Fintype (ConsecutiveIndex Q) :=
  inferInstanceAs (Fintype (Fin ((Fraction.sequence Q).length - 1)))

/-- The adjacent Farey pair beginning at a nonterminal sequence index. -/
def consecutivePairAt (Q : ℕ) (i : ConsecutiveIndex Q) : ConsecutivePair Q := by
  have hi1 : i.1 + 1 < (Fraction.sequence Q).length := by
    have hi := i.isLt
    omega
  exact ⟨(fractionAt Q ⟨i.1, by omega⟩, fractionAt Q ⟨i.1 + 1, hi1⟩),
    consecutive_fractionAt_succ hi1⟩

theorem consecutivePairAt_injective (Q : ℕ) :
    Function.Injective (consecutivePairAt Q) := by
  intro i j hij
  apply Fin.ext
  have hleft :
      fractionAt Q ⟨i.1, by
        have := i.isLt
        exact Nat.lt_of_lt_of_le this (Nat.sub_le _ _)⟩ =
      fractionAt Q ⟨j.1, by
        have := j.isLt
        exact Nat.lt_of_lt_of_le this (Nat.sub_le _ _)⟩ := by
    exact congrArg (fun pq : ConsecutivePair Q ↦ pq.1.1) hij
  have hind := Fraction.sequence_nodup.injective_get hleft
  exact congrArg
    (fun x : Fin (Fraction.sequence Q).length ↦ x.1) hind

theorem consecutivePairAt_surjective (Q : ℕ) :
    Function.Surjective (consecutivePairAt Q) := by
  intro pq
  obtain ⟨i, hi, _⟩ := existsUnique_fractionAt_eq pq.1.1
  obtain ⟨j, hj, _⟩ := existsUnique_fractionAt_eq pq.1.2
  have hij : i < j := by
    apply lt_of_not_ge
    intro hji
    have hle := Fraction.sequence_pairwise.rel_get_of_le hji
    change (fractionAt Q j).value ≤ (fractionAt Q i).value at hle
    rw [hi, hj] at hle
    exact (not_lt_of_ge hle) pq.property.1
  have hadj : j.1 = i.1 + 1 := by
    have hle : i.1 + 1 ≤ j.1 := by omega
    apply le_antisymm
    · apply Nat.le_of_not_gt
      intro hlt
      let k : Fin (Fraction.sequence Q).length := ⟨i.1 + 1, by omega⟩
      have hik : i < k := by change i.1 < i.1 + 1; omega
      have hkj : k < j := by change i.1 + 1 < j.1; exact hlt
      have hpbetween : pq.1.1.value < (fractionAt Q k).value := by
        rw [← hi]
        exact fractionAt_value_strictMono hik
      have hqbetween : (fractionAt Q k).value < pq.1.2.value := by
        rw [← hj]
        exact fractionAt_value_strictMono hkj
      exact pq.property.2 (fractionAt Q k) ⟨hpbetween, hqbetween⟩
    · exact hle
  have hiLast : i.1 < (Fraction.sequence Q).length - 1 := by omega
  let k : ConsecutiveIndex Q := ⟨i.1, hiLast⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change fractionAt Q ⟨i.1, _⟩ = pq.1.1
    exact hi
  · change fractionAt Q ⟨i.1 + 1, _⟩ = pq.1.2
    have hidx : (⟨i.1 + 1, by omega⟩ :
        Fin (Fraction.sequence Q).length) = j := by
      apply Fin.ext
      exact hadj.symm
    rw [hidx]
    exact hj

/-- Adjacent positions in the sorted Farey list are equivalent to all
order-theoretically consecutive Farey pairs. -/
def consecutiveIndexEquivConsecutivePair (Q : ℕ) :
    ConsecutiveIndex Q ≃ ConsecutivePair Q :=
  Equiv.ofBijective (consecutivePairAt Q)
    ⟨consecutivePairAt_injective Q, consecutivePairAt_surjective Q⟩

/-- Reindex a sum over adjacent sequence positions directly by primitive
denominator pairs in the explicit Farey triangle. -/
theorem sum_consecutiveIndex_eq_sum_denominatorPairFinset
    {Q : ℕ} {M : Type*} [AddCommMonoid M] (F : ℕ × ℕ → M) :
    (∑ i : ConsecutiveIndex Q,
        F (((consecutivePairAt Q i).1.1.den,
          (consecutivePairAt Q i).1.2.den))) =
      ∑ uv ∈ denominatorPairFinset Q,
        if Nat.Coprime uv.1 uv.2 then F uv else 0 := by
  calc
    (∑ i : ConsecutiveIndex Q,
        F (((consecutivePairAt Q i).1.1.den,
          (consecutivePairAt Q i).1.2.den))) =
      ∑ e : ConsecutivePair Q, F ((e.1.1.den, e.1.2.den)) := by
        apply Fintype.sum_equiv (consecutiveIndexEquivConsecutivePair Q)
        intro i
        rfl
    _ = _ := sum_consecutivePair_eq_sum_denominatorPairFinset F

theorem sum_consecutiveIndex_normalizedDenominatorPairWeight
    (Q : ℕ) (G : ℝ × ℝ → ℝ) :
    (∑ i : ConsecutiveIndex Q,
        G (((consecutivePairAt Q i).1.1.den : ℝ) / Q,
          ((consecutivePairAt Q i).1.2.den : ℝ) / Q)) =
      ∑ uv ∈ denominatorPairFinset Q,
        if Nat.Coprime uv.1 uv.2 then
          normalizedDenominatorPairWeight G Q uv else 0 := by
  simpa [normalizedDenominatorPairWeight] using
    sum_consecutiveIndex_eq_sum_denominatorPairFinset
      (Q := Q) (F := normalizedDenominatorPairWeight G Q)

/-- The left endpoint `0/1` of every positive-order Farey sequence. -/
def zeroFraction (Q : ℕ) (hQ : 0 < Q) : Fraction Q where
  num := 0
  den := 1
  den_pos := by simp
  den_le := hQ
  num_le := by simp
  reduced := Nat.coprime_one_right 0

/-- The right endpoint `1/1` of every positive-order Farey sequence. -/
def oneFraction (Q : ℕ) (hQ : 0 < Q) : Fraction Q where
  num := 1
  den := 1
  den_pos := by simp
  den_le := hQ
  num_le := le_rfl
  reduced := by simp

/-- Totalized view of the Farey sequence beginning at a nonterminal index.
Only its in-range values are used by the finite-horizon theorems. -/
def fractionAtOffset (Q : ℕ) (hQ : 0 < Q) (i : ConsecutiveIndex Q)
    (j : ℕ) : Fraction Q :=
  if h : i.1 + j < (Fraction.sequence Q).length then
    fractionAt Q ⟨i.1 + j, h⟩
  else zeroFraction Q hQ

theorem fractionAtOffset_eq_of_le {Q m : ℕ} (hQ : 0 < Q)
    (i : ConsecutiveIndex Q)
    (hm : m ≤ (Fraction.sequence Q).length - 1 - i.1)
    {j : ℕ} (hj : j ≤ m) :
    fractionAtOffset Q hQ i j =
      fractionAt Q ⟨i.1 + j, by
        have hi := i.isLt
        omega⟩ := by
  rw [fractionAtOffset, dif_pos]

theorem consecutive_fractionAtOffset {Q m : ℕ} (hQ : 0 < Q)
    (i : ConsecutiveIndex Q)
    (hm : m ≤ (Fraction.sequence Q).length - 1 - i.1)
    {j : ℕ} (hj : j < m) :
    Consecutive (fractionAtOffset Q hQ i j)
      (fractionAtOffset Q hQ i (j + 1)) := by
  rw [fractionAtOffset_eq_of_le hQ i hm (by omega),
    fractionAtOffset_eq_of_le hQ i hm (by omega)]
  exact consecutive_fractionAt_succ (by
    have hi := i.isLt
    omega)

theorem fractionAtOffset_zero {Q : ℕ} (hQ : 0 < Q)
    (i : ConsecutiveIndex Q) :
    fractionAtOffset Q hQ i 0 = (consecutivePairAt Q i).1.1 := by
  unfold fractionAtOffset consecutivePairAt
  simp only [Nat.add_zero]
  rw [dif_pos (by have hi := i.isLt; omega)]

theorem fractionAtOffset_one {Q : ℕ} (hQ : 0 < Q)
    (i : ConsecutiveIndex Q) :
    fractionAtOffset Q hQ i 1 = (consecutivePairAt Q i).1.2 := by
  unfold fractionAtOffset consecutivePairAt
  rw [dif_pos]

theorem initial_normalized_pair_fractionAtOffset {Q : ℕ} (hQ : 0 < Q)
    (i : ConsecutiveIndex Q) :
    ((((fractionAtOffset Q hQ i) 0).den : ℝ) / Q,
        (((fractionAtOffset Q hQ i) 1).den : ℝ) / Q) =
      (((consecutivePairAt Q i).1.1.den : ℝ) / Q,
        ((consecutivePairAt Q i).1.2.den : ℝ) / Q) := by
  rw [fractionAtOffset_zero, fractionAtOffset_one]

theorem sequence_length_pos {Q : ℕ} (hQ : 0 < Q) :
    0 < (Fraction.sequence Q).length := by
  rw [List.length_pos_iff]
  intro hnil
  have hmem := Fraction.mem_sequence (zeroFraction Q hQ)
  simpa [hnil] using hmem

/-- The first indexed entry of a positive-order Farey sequence is `0/1`. -/
theorem fractionAt_zero_eq_zeroFraction {Q : ℕ} (hQ : 0 < Q) :
    fractionAt Q ⟨0, sequence_length_pos hQ⟩ = zeroFraction Q hQ := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Fraction.mem_sequence (zeroFraction Q hQ))
  apply Fraction.value_injective
  apply le_antisymm
  · have h := Fraction.sequence_pairwise.rel_get_of_le
      (a := ⟨0, sequence_length_pos hQ⟩) (b := j) (Nat.zero_le _)
    change (fractionAt Q ⟨0, sequence_length_pos hQ⟩).value ≤
      (fractionAt Q j).value at h
    simp only [fractionAt] at h
    rw [hj] at h
    simpa [Fraction.value, zeroFraction] using h
  · rw [show (zeroFraction Q hQ).value = 0 by
      simp [Fraction.value, zeroFraction]]
    apply div_nonneg <;> positivity

/-- The final indexed entry of a positive-order Farey sequence is `1/1`. -/
theorem fractionAt_last_eq_oneFraction {Q : ℕ} (hQ : 0 < Q) :
    fractionAt Q ⟨(Fraction.sequence Q).length - 1,
      Nat.sub_lt (sequence_length_pos hQ) Nat.zero_lt_one⟩ = oneFraction Q hQ := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Fraction.mem_sequence (oneFraction Q hQ))
  apply Fraction.value_injective
  apply le_antisymm
  · have hnum := (fractionAt Q ⟨(Fraction.sequence Q).length - 1,
        Nat.sub_lt (sequence_length_pos hQ) Nat.zero_lt_one⟩).num_le
    have hden := (fractionAt Q ⟨(Fraction.sequence Q).length - 1,
        Nat.sub_lt (sequence_length_pos hQ) Nat.zero_lt_one⟩).den_pos
    simpa [Fraction.value, oneFraction] using
      (div_le_one (by exact_mod_cast hden : (0 : ℚ) < _)).2 (by exact_mod_cast hnum)
  · have h := Fraction.sequence_pairwise.rel_get_of_le
      (a := j)
      (b := ⟨(Fraction.sequence Q).length - 1,
        Nat.sub_lt (sequence_length_pos hQ) Nat.zero_lt_one⟩)
      (Nat.le_sub_one_of_lt j.isLt)
    change (fractionAt Q j).value ≤
      (fractionAt Q ⟨(Fraction.sequence Q).length - 1,
        Nat.sub_lt (sequence_length_pos hQ) Nat.zero_lt_one⟩).value at h
    simp only [fractionAt] at h
    rw [hj] at h
    simpa [Fraction.value, oneFraction] using h

/-- The union of approximation intervals indexed by entries of the full
Farey sequence whose denominators lie above the lower cutoff `N`. -/
def activeApproximationUnion (N : ℕ) (A c : ℝ) : Set ℝ :=
  let Q := ⌊c * (N : ℝ)⌋₊
  ⋃ i : Fin (Fraction.sequence Q).length,
    ⋃ _h : N ≤ (fractionAt Q i).den,
      approximationInterval A ((fractionAt Q i).num : ℤ) (fractionAt Q i).den

/-- For `N ≥ 2`, the endpoint fractions are inactive and the reduced-pair
union is exactly the union over active entries of the full Farey sequence. -/
theorem finiteApproximationUnion_eq_activeApproximationUnion
    {N : ℕ} {A c : ℝ} (hN2 : 2 ≤ N) :
    finiteApproximationUnion N A c = activeApproximationUnion N A c := by
  let Q := ⌊c * (N : ℝ)⌋₊
  change
    (⋃ p ∈ reducedPairs N c, approximationInterval A (p.2 : ℤ) p.1) =
    (⋃ i : Fin (Fraction.sequence Q).length,
      ⋃ _h : N ≤ (fractionAt Q i).den,
        approximationInterval A ((fractionAt Q i).num : ℤ) (fractionAt Q i).den)
  ext α
  constructor
  · intro hα
    rcases Set.mem_iUnion₂.mp hα with ⟨p, hp, hαp⟩
    rw [mem_reducedPairs] at hp
    let f : Fraction Q :=
      { num := p.2
        den := p.1
        den_pos := lt_of_lt_of_le (by omega) hp.1
        den_le := hp.2.1
        num_le := hp.2.2.1.le
        reduced := hp.2.2.2 }
    obtain ⟨i, hi⟩ := (existsUnique_fractionAt_eq f).exists
    refine Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem ?_ ?_)
    · rw [hi]
      exact hp.1
    · rw [hi]
      exact hαp
  · intro hα
    rcases Set.mem_iUnion.mp hα with ⟨i, hα⟩
    rcases Set.mem_iUnion.mp hα with ⟨hi, hαi⟩
    let f := fractionAt Q i
    have hi' : N ≤ f.den := by simpa [f] using hi
    have hnumlt : f.num < f.den := by
      apply lt_of_le_of_ne f.num_le
      intro heq
      have hden1 : f.den = 1 := (Nat.coprime_self f.den).mp (by
        simpa [heq] using f.reduced)
      omega
    let p : Σ _y : ℕ, ℕ := ⟨f.den, f.num⟩
    have hp : p ∈ reducedPairs N c := by
      rw [mem_reducedPairs]
      exact ⟨hi', f.den_le, hnumlt, f.reduced⟩
    refine Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hp ?_)
    simpa [p, f] using hαi

/-- The literal approximation set equals the active indexed Farey union
whenever the elementary endpoint reduction applies. -/
theorem approximableSet_eq_activeApproximationUnion
    {N : ℕ} {A c : ℝ}
    (hN2 : 2 ≤ N) (hAN : A < N) (hc : 1 ≤ c) :
    approximableSet N A c = activeApproximationUnion N A c := by
  rw [approximableSet_eq_finiteApproximationUnion hN2 hAN hc]
  exact finiteApproximationUnion_eq_activeApproximationUnion hN2

/-- Natural-number indices of Farey fractions whose denominators are at
least `N`. -/
def activeIndexFinset (N Q : ℕ) : Finset ℕ :=
  ((Finset.univ.filter fun i : Fin (Fraction.sequence Q).length ↦
      N ≤ (fractionAt Q i).den).image fun i ↦ i.1)

@[simp] theorem mem_activeIndexFinset {N Q i : ℕ} :
    i ∈ activeIndexFinset N Q ↔
      ∃ hi : i < (Fraction.sequence Q).length,
        N ≤ (fractionAt Q ⟨i, hi⟩).den := by
  rw [activeIndexFinset, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_filter] at hj
    exact ⟨j.isLt, hj.2⟩
  · rintro ⟨hi, hden⟩
    refine ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact hden

/-- The approximation interval at natural index `i`, or the empty set if
the index is not active. -/
def activeIntervalAt (N Q : ℕ) (A : ℝ) (i : ℕ) : Set ℝ :=
  if hi : i < (Fraction.sequence Q).length then
    if _hden : N ≤ (fractionAt Q ⟨i, hi⟩).den then
      approximationInterval A ((fractionAt Q ⟨i, hi⟩).num : ℤ)
        (fractionAt Q ⟨i, hi⟩).den
    else ∅
  else ∅

theorem activeIntervalAt_eq_of_mem {N Q i : ℕ} {A : ℝ}
    (hi : i ∈ activeIndexFinset N Q) :
    activeIntervalAt N Q A i =
      approximationInterval A
        ((fractionAt Q ⟨i, (mem_activeIndexFinset.mp hi).choose⟩).num : ℤ)
        (fractionAt Q ⟨i, (mem_activeIndexFinset.mp hi).choose⟩).den := by
  rw [activeIntervalAt, dif_pos (mem_activeIndexFinset.mp hi).choose,
    dif_pos (mem_activeIndexFinset.mp hi).choose_spec]

theorem activeIntervalAt_eq_empty_of_not_mem {N Q i : ℕ} {A : ℝ}
    (hi : i ∉ activeIndexFinset N Q) :
    activeIntervalAt N Q A i = ∅ := by
  rw [activeIntervalAt]
  split_ifs with hlen hden
  · exact (hi (mem_activeIndexFinset.mpr ⟨hlen, hden⟩)).elim
  · rfl
  · rfl

/-- The sigma-indexed active union equals the same union over the concrete
finite set of natural-number indices. -/
theorem activeApproximationUnion_eq_biUnion_activeIndexFinset
    (N Q : ℕ) (A : ℝ) :
    (⋃ i : Fin (Fraction.sequence Q).length,
      ⋃ _h : N ≤ (fractionAt Q i).den,
        approximationInterval A ((fractionAt Q i).num : ℤ) (fractionAt Q i).den) =
      ⋃ i ∈ activeIndexFinset N Q, activeIntervalAt N Q A i := by
  ext α
  constructor
  · intro hα
    rcases Set.mem_iUnion.mp hα with ⟨i, hα⟩
    rcases Set.mem_iUnion.mp hα with ⟨hden, hαi⟩
    have hi : i.1 ∈ activeIndexFinset N Q :=
      mem_activeIndexFinset.mpr ⟨i.isLt, hden⟩
    refine Set.mem_iUnion_of_mem i.1 (Set.mem_iUnion_of_mem hi ?_)
    rw [activeIntervalAt, dif_pos i.isLt, dif_pos hden]
    exact hαi
  · intro hα
    rcases Set.mem_iUnion₂.mp hα with ⟨i, hi, hαi⟩
    obtain ⟨hlen, hden⟩ := mem_activeIndexFinset.mp hi
    refine Set.mem_iUnion_of_mem ⟨i, hlen⟩
      (Set.mem_iUnion_of_mem hden ?_)
    rw [activeIntervalAt, dif_pos hlen, dif_pos hden] at hαi
    exact hαi

theorem activeApproximationUnion_eq_biUnion_activeIndexFinset_order
    (N : ℕ) (A c : ℝ) :
    activeApproximationUnion N A c =
      ⋃ i ∈ activeIndexFinset N ⌊c * (N : ℝ)⌋₊,
        activeIntervalAt N ⌊c * (N : ℝ)⌋₊ A i := by
  exact activeApproximationUnion_eq_biUnion_activeIndexFinset
    N ⌊c * (N : ℝ)⌋₊ A

/-- Adding inactive indices changes nothing: their indexed interval was
defined to be empty. -/
theorem biUnion_activeIndexFinset_eq_biUnion_Icc
    (N Q : ℕ) (A : ℝ) :
    (⋃ i ∈ activeIndexFinset N Q, activeIntervalAt N Q A i) =
      ⋃ i ∈ Finset.Icc 0 ((Fraction.sequence Q).length - 1),
        activeIntervalAt N Q A i := by
  ext α
  constructor
  · intro hα
    rcases Set.mem_iUnion₂.mp hα with ⟨i, hi, hαi⟩
    have hlen := (mem_activeIndexFinset.mp hi).choose
    refine Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem ?_ hαi)
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le i, Nat.le_sub_one_of_lt hlen⟩
  · intro hα
    rcases Set.mem_iUnion₂.mp hα with ⟨i, hi, hαi⟩
    by_cases hactive : i ∈ activeIndexFinset N Q
    · exact Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem hactive hαi)
    · rw [activeIntervalAt_eq_empty_of_not_mem hactive] at hαi
      exact hαi.elim

/-- Finite inclusion--exclusion for active indexed Farey intervals.  The
only geometric input still required is pairwise disjointness beyond offset
`K`; the generic bounded-offset theorem supplies the exact finite sum. -/
theorem measureReal_biUnion_activeIndexFinset_eq_sum_offset_subsets
    (N Q K : ℕ) (A : ℝ)
    (hfarPair : ∀ i j,
      i ∈ Finset.Icc 0 ((Fraction.sequence Q).length - 1) →
      j ∈ Finset.Icc 0 ((Fraction.sequence Q).length - 1) →
      i < j → K < j - i →
      Disjoint (activeIntervalAt N Q A i) (activeIntervalAt N Q A j)) :
    volume.real (⋃ i ∈ activeIndexFinset N Q, activeIntervalAt N Q A i) =
      ∑ i ∈ Finset.Icc 0 ((Fraction.sequence Q).length - 1),
        ∑ w ∈ (Finset.Icc 1
            (min K ((Fraction.sequence Q).length - 1 - i))).powerset,
          (-1 : ℝ) ^ (w.card + 2) *
            volume.real
              (⋂ j ∈ insert i (w.image fun d ↦ i + d),
                activeIntervalAt N Q A j) := by
  rw [biUnion_activeIndexFinset_eq_biUnion_Icc]
  apply FiniteInclusionExclusion.measureReal_iUnion_Icc_eq_sum_offset_subsets
      (K := K) (hfin := by
        intro i hi
        unfold activeIntervalAt
        split
        · split
          · rw [approximationInterval, Real.volume_Ioo]
            simp
          · simp
        · simp)
  · intro i hi
    unfold activeIntervalAt
    split
    · split
      · exact measurableSet_Ioo
      · exact MeasurableSet.empty
    · exact MeasurableSet.empty
  · intro i hi v hv hlong
    obtain ⟨j, hjv, hK⟩ := hlong
    have hjfilter : j ∈
        (Finset.Icc 0 ((Fraction.sequence Q).length - 1)).filter (i < ·) :=
      (Finset.mem_powerset.mp hv) hjv
    rw [Finset.mem_filter] at hjfilter
    ext α
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hα
    have hαi : α ∈ activeIntervalAt N Q A i := by
      exact Set.mem_iInter.mp
        (Set.mem_iInter.mp hα i) (Finset.mem_insert_self i v)
    have hαj : α ∈ activeIntervalAt N Q A j := by
      exact Set.mem_iInter.mp
        (Set.mem_iInter.mp hα j) (Finset.mem_insert_of_mem hjv)
    exact Set.disjoint_left.mp
      (hfarPair i j hi hjfilter.1 hjfilter.2 hK) hαi hαj

/-- Each Farey gap is at least `1/Q²`; hence an offset of `k` positions
has normalized center displacement at least `k`. -/
theorem natCast_le_sq_mul_fractionAt_realValue_sub
    {Q i k : ℕ} (_hQ : 0 < Q)
    (hik : i + k < (Fraction.sequence Q).length) :
    (k : ℝ) ≤ (Q : ℝ) ^ 2 *
      ((fractionAt Q ⟨i + k, hik⟩).realValue -
        (fractionAt Q ⟨i, by omega⟩).realValue) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ih' := ih (by omega)
      have hstep := (consecutive_fractionAt_succ
        (Q := Q) (i := i + k) (by omega)).realValue_gap
      have hdenprod :
          ((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
              (fractionAt Q ⟨i + k + 1, by omega⟩).den ≤
            (Q : ℝ) ^ 2 := by
        have hleft := (fractionAt Q ⟨i + k, by omega⟩).den_le
        have hright := (fractionAt Q ⟨i + k + 1, by omega⟩).den_le
        simpa [pow_two] using
          (show
            ((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
                (fractionAt Q ⟨i + k + 1, by omega⟩).den ≤
              (Q : ℝ) * Q by
            exact_mod_cast Nat.mul_le_mul hleft hright)
      have hdenpos : 0 <
          ((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
            (fractionAt Q ⟨i + k + 1, by omega⟩).den :=
        mul_pos (by exact_mod_cast
          (fractionAt Q ⟨i + k, by omega⟩).den_pos)
          (by exact_mod_cast
            (fractionAt Q ⟨i + k + 1, by omega⟩).den_pos)
      have hone : (1 : ℝ) ≤ (Q : ℝ) ^ 2 *
          (1 / (((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
            (fractionAt Q ⟨i + k + 1, by omega⟩).den)) := by
        calc
          (1 : ℝ) =
              (((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
                (fractionAt Q ⟨i + k + 1, by omega⟩).den) /
              (((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
                (fractionAt Q ⟨i + k + 1, by omega⟩).den) := by
                  exact (div_self hdenpos.ne').symm
          _ ≤ (Q : ℝ) ^ 2 /
              (((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
                (fractionAt Q ⟨i + k + 1, by omega⟩).den) :=
            (div_le_div_iff_of_pos_right hdenpos).2 hdenprod
          _ = (Q : ℝ) ^ 2 *
              (1 / (((fractionAt Q ⟨i + k, by omega⟩).den : ℝ) *
                (fractionAt Q ⟨i + k + 1, by omega⟩).den)) := by ring
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [Nat.add_assoc] at hstep hone
      rw [show
        (fractionAt Q ⟨i + (k + 1), by omega⟩).realValue -
            (fractionAt Q ⟨i, by omega⟩).realValue =
          ((fractionAt Q ⟨i + (k + 1), by omega⟩).realValue -
            (fractionAt Q ⟨i + k, by omega⟩).realValue) +
          ((fractionAt Q ⟨i + k, by omega⟩).realValue -
            (fractionAt Q ⟨i, by omega⟩).realValue) by ring]
      rw [hstep, mul_add]
      linarith

/-- Active approximation intervals whose Farey indices differ by at least
`2 A c²` are disjoint. -/
theorem activeIntervalAt_disjoint_of_large_offset
    {N Q i j : ℕ} {A c : ℝ}
    (hA : 0 < A) (hc : 1 ≤ c) (hN : 0 < N) (hQ : 0 < Q)
    (hQN : (Q : ℝ) ≤ c * N) (hij : i < j)
    (hlarge : 2 * A * c ^ 2 ≤ (j - i : ℕ)) :
    Disjoint (activeIntervalAt N Q A i) (activeIntervalAt N Q A j) := by
  by_cases hia : i ∈ activeIndexFinset N Q
  swap
  · rw [activeIntervalAt_eq_empty_of_not_mem hia]
    exact Set.empty_disjoint _
  by_cases hja : j ∈ activeIndexFinset N Q
  swap
  · rw [activeIntervalAt_eq_empty_of_not_mem hja]
    exact Set.disjoint_empty _
  obtain ⟨hiLen, hiDen⟩ := mem_activeIndexFinset.mp hia
  obtain ⟨hjLen, hjDen⟩ := mem_activeIndexFinset.mp hja
  let pi := fractionAt Q ⟨i, hiLen⟩
  let pj := fractionAt Q ⟨j, hjLen⟩
  have hiDen' : N ≤ pi.den := by simpa [pi] using hiDen
  have hjDen' : N ≤ pj.den := by simpa [pj] using hjDen
  have hiPos : (0 : ℝ) < pi.den := by exact_mod_cast pi.den_pos
  have hjPos : (0 : ℝ) < pj.den := by exact_mod_cast pj.den_pos
  have hc0 : (0 : ℝ) ≤ c := zero_le_one.trans hc
  have hQi : (Q : ℝ) ≤ c * pi.den := by
    calc
      (Q : ℝ) ≤ c * N := hQN
      _ ≤ c * pi.den :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hiDen') hc0
  have hQj : (Q : ℝ) ≤ c * pj.den := by
    calc
      (Q : ℝ) ≤ c * N := hQN
      _ ≤ c * pj.den :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hjDen') hc0
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hscalei : (Q : ℝ) ^ 2 * (A / (pi.den : ℝ) ^ 2) ≤ A * c ^ 2 := by
    have hsquare : (Q : ℝ) ^ 2 ≤ (c * pi.den) ^ 2 :=
      (sq_le_sq₀ hQ0 (mul_nonneg hc0 hiPos.le)).2 hQi
    calc
      (Q : ℝ) ^ 2 * (A / (pi.den : ℝ) ^ 2) =
          (A * (Q : ℝ) ^ 2) / (pi.den : ℝ) ^ 2 := by ring
      _ ≤ A * c ^ 2 := (div_le_iff₀ (sq_pos_of_pos hiPos)).2 (by
        have := mul_le_mul_of_nonneg_left hsquare hA.le
        nlinarith)
  have hscalej : (Q : ℝ) ^ 2 * (A / (pj.den : ℝ) ^ 2) ≤ A * c ^ 2 := by
    have hsquare : (Q : ℝ) ^ 2 ≤ (c * pj.den) ^ 2 :=
      (sq_le_sq₀ hQ0 (mul_nonneg hc0 hjPos.le)).2 hQj
    calc
      (Q : ℝ) ^ 2 * (A / (pj.den : ℝ) ^ 2) =
          (A * (Q : ℝ) ^ 2) / (pj.den : ℝ) ^ 2 := by ring
      _ ≤ A * c ^ 2 := (div_le_iff₀ (sq_pos_of_pos hjPos)).2 (by
        have := mul_le_mul_of_nonneg_left hsquare hA.le
        nlinarith)
  rw [Set.disjoint_left]
  intro α hαi hαj
  rw [activeIntervalAt, dif_pos hiLen, dif_pos hiDen] at hαi
  rw [activeIntervalAt, dif_pos hjLen, dif_pos hjDen] at hαj
  have hapi := mem_approximationInterval.mp hαi
  have hapj := mem_approximationInterval.mp hαj
  change |α - pi.realValue| < A / (pi.den : ℝ) ^ 2 at hapi
  change |α - pj.realValue| < A / (pj.den : ℝ) ^ 2 at hapj
  have hcenter : pj.realValue - pi.realValue <
      A / (pi.den : ℝ) ^ 2 + A / (pj.den : ℝ) ^ 2 := by
    calc
      pj.realValue - pi.realValue ≤ |pj.realValue - pi.realValue| := le_abs_self _
      _ = |(pj.realValue - α) + (α - pi.realValue)| := by ring_nf
      _ ≤ |pj.realValue - α| + |α - pi.realValue| := abs_add_le _ _
      _ < A / (pj.den : ℝ) ^ 2 + A / (pi.den : ℝ) ^ 2 :=
        add_lt_add (by simpa [abs_sub_comm] using hapj) hapi
      _ = A / (pi.den : ℝ) ^ 2 + A / (pj.den : ℝ) ^ 2 := by ring
  have hlower := natCast_le_sq_mul_fractionAt_realValue_sub
    (Q := Q) (i := i) (k := j - i) hQ (by
      simpa [Nat.add_sub_of_le hij.le] using hjLen)
  have hlower' : ((j - i : ℕ) : ℝ) ≤
      (Q : ℝ) ^ 2 * (pj.realValue - pi.realValue) := by
    simpa [pi, pj, Nat.add_sub_of_le hij.le] using hlower
  have hupper : (Q : ℝ) ^ 2 * (pj.realValue - pi.realValue) <
      2 * A * c ^ 2 := by
    calc
      (Q : ℝ) ^ 2 * (pj.realValue - pi.realValue) <
          (Q : ℝ) ^ 2 *
            (A / (pi.den : ℝ) ^ 2 + A / (pj.den : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_left hcenter (sq_pos_of_pos (by exact_mod_cast hQ))
      _ = (Q : ℝ) ^ 2 * (A / (pi.den : ℝ) ^ 2) +
          (Q : ℝ) ^ 2 * (A / (pj.den : ℝ) ^ 2) := by ring
      _ ≤ A * c ^ 2 + A * c ^ 2 := add_le_add hscalei hscalej
      _ = 2 * A * c ^ 2 := by ring
  have : ((j - i : ℕ) : ℝ) < 2 * A * c ^ 2 := hlower'.trans_lt hupper
  exact (not_lt_of_ge hlarge) this

end Farey

/-! ### Visible-lattice Riemann sums

The all-parameter formula is reduced to weighted sums over primitive lattice
points.  This namespace packages the two independent ingredients of that
reduction: Mathlib's integer-grid Riemann-sum theorem after a fixed divisor
rescaling, and Möbius inversion followed by Tannery's theorem.
-/

namespace VisibleLattice

/-- The exact fixed-divisor grid limit used after Möbius inversion.  The
apparently nonintegral mesh `d / n` is handled by scaling the set and the
weight while keeping Mathlib's integer mesh parameter `n`. -/
lemma scaled_integer_lattice_riemann
    {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ) (d : ℕ)
    (hF : Continuous F)
    (hs₁ : Bornology.IsBounded ((d : ℝ)⁻¹ • s))
    (hs₂ : MeasurableSet ((d : ℝ)⁻¹ • s))
    (hs₃ : volume (frontier ((d : ℝ)⁻¹ • s)) = 0) :
    Tendsto
      (fun n : ℕ => (d : ℝ) ^ Fintype.card ι *
        ((∑' x : ↑(((d : ℝ)⁻¹ • s) ∩
            (n : ℝ)⁻¹ • (Submodule.span ℤ
              (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))),
              F ((d : ℝ) • (x : ι → ℝ))) /
          n ^ Fintype.card ι))
      atTop
      (nhds ((d : ℝ) ^ Fintype.card ι *
        ∫ x in (d : ℝ)⁻¹ • s, F ((d : ℝ) • x))) := by
  have hG : Continuous (fun x : ι → ℝ => F ((d : ℝ) • x)) :=
    hF.comp (continuous_const_smul (d : ℝ))
  exact tendsto_const_nhds.mul
    (tendsto_tsum_div_pow_atTop_integral
      ((d : ℝ)⁻¹ • s) (fun x : ι → ℝ => F ((d : ℝ) • x)) hG hs₁ hs₂ hs₃)

/-- Scaling both the domain and the argument of the integrand contributes
the inverse Jacobian, which is cancelled by `d ^ card ι`. -/
lemma scaled_setIntegral
    {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ)
    (d : ℕ) (hd : 0 < d) :
    (d : ℝ) ^ Fintype.card ι *
        (∫ x in (d : ℝ)⁻¹ • s, F ((d : ℝ) • x)) =
      ∫ x in s, F x := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := MeasureTheory.Measure.setIntegral_comp_smul
    (volume : Measure (ι → ℝ)) F ((d : ℝ)⁻¹ • s) hdR
  rw [Module.finrank_pi] at h
  rw [h]
  rw [smul_smul, mul_inv_cancel₀ hdR, one_smul]
  rw [abs_of_pos (inv_pos.mpr (pow_pos (by positivity) _))]
  rw [smul_eq_mul]
  field_simp

/-- Fixed-divisor lattice sums converge to the original, unscaled integral. -/
lemma scaled_integer_lattice_riemann_to_integral
    {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ) (d : ℕ)
    (hd : 0 < d) (hF : Continuous F)
    (hs₁ : Bornology.IsBounded ((d : ℝ)⁻¹ • s))
    (hs₂ : MeasurableSet ((d : ℝ)⁻¹ • s))
    (hs₃ : volume (frontier ((d : ℝ)⁻¹ • s)) = 0) :
    Tendsto
      (fun n : ℕ => (d : ℝ) ^ Fintype.card ι *
        ((∑' x : ↑(((d : ℝ)⁻¹ • s) ∩
            (n : ℝ)⁻¹ • (Submodule.span ℤ
              (Set.range (Pi.basisFun ℝ ι)) : Set (ι → ℝ))),
              F ((d : ℝ) • (x : ι → ℝ))) /
          n ^ Fintype.card ι))
      atTop (nhds (∫ x in s, F x)) := by
  convert scaled_integer_lattice_riemann s F d hF hs₁ hs₂ hs₃ using 1
  exact congrArg nhds (scaled_setIntegral s F d hd).symm

lemma coprime_indicator_eq_sum_moebius (a b : ℕ) :
    (if Nat.Coprime a b then (1 : ℝ) else 0) =
      ∑ d ∈ (Nat.gcd a b).divisors, (ArithmeticFunction.moebius d : ℝ) := by
  simp only [Nat.coprime_iff_gcd_eq_one]
  have hInt :
      (∑ d ∈ (Nat.gcd a b).divisors, ArithmeticFunction.moebius d) =
        if Nat.gcd a b = 1 then (1 : ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  exact_mod_cast hInt.symm

def commonDivisors (P : Finset (ℕ × ℕ)) : Finset ℕ :=
  P.biUnion fun p => (Nat.gcd p.1 p.2).divisors

lemma weighted_coprime_sum_eq_moebius
    (P : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hnonzero : ∀ p ∈ P, p ≠ (0, 0)) :
    (∑ p ∈ P, if Nat.Coprime p.1 p.2 then w p else 0) =
      ∑ d ∈ commonDivisors P,
        (ArithmeticFunction.moebius d : ℝ) *
          ∑ p ∈ P with d ∣ p.1 ∧ d ∣ p.2, w p := by
  calc
    (∑ p ∈ P, if Nat.Coprime p.1 p.2 then w p else 0) =
        ∑ p ∈ P, (if Nat.Coprime p.1 p.2 then (1 : ℝ) else 0) * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ = ∑ p ∈ P, ∑ d ∈ (Nat.gcd p.1 p.2).divisors,
          (ArithmeticFunction.moebius d : ℝ) * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [coprime_indicator_eq_sum_moebius, Finset.sum_mul]
    _ = ∑ p ∈ P, ∑ d ∈ commonDivisors P with d ∣ p.1 ∧ d ∣ p.2,
          (ArithmeticFunction.moebius d : ℝ) * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext d
      have hgcd : Nat.gcd p.1 p.2 ≠ 0 := by
        simpa [Prod.ext_iff] using hnonzero p hp
      simp [commonDivisors, Nat.mem_divisors, Nat.dvd_gcd_iff, hgcd]
      intro hd1 hd2
      exact ⟨p.1, p.2, hp, ⟨hd1, hd2⟩, fun h1 h2 => hgcd (by simp [h1, h2])⟩
    _ = ∑ d ∈ commonDivisors P, ∑ p ∈ P with d ∣ p.1 ∧ d ∣ p.2,
          (ArithmeticFunction.moebius d : ℝ) * w p := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ commonDivisors P,
        (ArithmeticFunction.moebius d : ℝ) *
          ∑ p ∈ P with d ∣ p.1 ∧ d ∣ p.2, w p := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]

def normalizedDivisorGridTerm
    (P : ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ × ℕ → ℝ)
    (n d : ℕ) : ℝ :=
  if d ∈ commonDivisors (P n) then
    (d : ℝ) ^ 2 * (∑ p ∈ P n with d ∣ p.1 ∧ d ∣ p.2, w n p) /
      (n : ℝ) ^ 2
  else 0

lemma normalized_weighted_coprime_sum_eq_tsum
    (P : ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ × ℕ → ℝ)
    (hnonzero : ∀ n p, p ∈ P n → p ≠ (0, 0)) {n : ℕ} (hn : n ≠ 0) :
    (∑ p ∈ P n, if Nat.Coprime p.1 p.2 then w n p else 0) /
        (n : ℝ) ^ 2 =
      ∑' d : ℕ, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) *
        normalizedDivisorGridTerm P w n d := by
  rw [weighted_coprime_sum_eq_moebius (P n) (w n) (fun p hp => hnonzero n p hp)]
  rw [tsum_eq_sum (s := commonDivisors (P n))]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos : 0 < d := by
      rcases Finset.mem_biUnion.mp hd with ⟨p, hp, hdp⟩
      exact Nat.pos_of_mem_divisors hdp
    rw [normalizedDivisorGridTerm, if_pos hd]
    field_simp
  · intro d hd
    simp [normalizedDivisorGridTerm, hd]

lemma tsum_moebius_div_sq :
    (∑' d : ℕ, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) =
      6 / Real.pi ^ 2 := by
  have h_sum : ∑' d : ℕ,
      (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ) =
        1 / (Real.pi ^ 2 / 6) := by
    have h_L2_mu : (∑' d : ℕ,
        (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) =
          (riemannZeta 2)⁻¹ := by
      have h_L2_mu : (∑' d : ℕ,
          (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) =
            LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 := by
        norm_num [LSeries]
        convert Complex.ofReal_tsum _
        norm_num [LSeries.term]
        aesop
      have h_L2_mu :
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 *
              riemannZeta 2 = 1 := by
        convert ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius _ using 1
        focus
          rw [mul_comm]
        focus
          rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta]
        · norm_num
        · norm_num
      exact eq_inv_of_mul_eq_one_left <| by aesop
    have h_zeta2 : riemannZeta 2 = Real.pi ^ 2 / 6 := riemannZeta_two
    simp_all [Complex.ext_iff, sq]
    norm_cast
  rw [show (fun d : ℕ =>
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) =
        (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) / (d ^ 2 : ℝ)) by
      funext d; norm_num]
  rw [h_sum]
  field_simp

lemma tendsto_moebius_weighted_tsum
    (R : ℕ → ℕ → ℝ) (I M : ℝ)
    (hM : 0 ≤ M)
    (hR : ∀ d, Tendsto (fun n => R n d) atTop (nhds I))
    (hbound : ∀ n d, |R n d| ≤ M) :
    Tendsto
      (fun n => ∑' d : ℕ,
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d)
      atTop (nhds ((6 / Real.pi ^ 2) * I)) := by
  let B : ℕ → ℝ := fun d => M / (d : ℝ) ^ 2
  have hB : Summable B := by
    simpa [B, div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left M
  have hterm (d : ℕ) :
      Tendsto
        (fun n => ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d)
        atTop
        (nhds (((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * I)) :=
    tendsto_const_nhds.mul (hR d)
  have hdom : ∀ n d,
      ‖((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d‖ ≤ B d := by
    intro n d
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (sq_nonneg (d : ℝ))]
    rw [div_mul_eq_mul_div]
    change |(ArithmeticFunction.moebius d : ℝ)| * |R n d| / (d : ℝ) ^ 2 ≤
      M / (d : ℝ) ^ 2
    apply div_le_div_of_nonneg_right _ (sq_nonneg (d : ℝ))
    calc
      |(ArithmeticFunction.moebius d : ℝ)| * |R n d|
          ≤ 1 * M := mul_le_mul (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
            (hbound n d) (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  have hlim := tendsto_tsum_of_dominated_convergence hB hterm
      (Eventually.of_forall hdom)
  have heq : (∑' k : ℕ,
      ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) * I) =
        (6 / Real.pi ^ 2) * I := by
    rw [tsum_mul_right, tsum_moebius_div_sq]
  simpa [heq] using hlim

/-- The positive-index version needed for arithmetic Möbius inversions.
At `d = 0` the Möbius coefficient is zero, so no convergence hypothesis
on the auxiliary grid term is needed there. -/
lemma tendsto_moebius_weighted_tsum_pos
    (R : ℕ → ℕ → ℝ) (I M : ℝ)
    (hM : 0 ≤ M)
    (hR : ∀ d, 0 < d → Tendsto (fun n => R n d) atTop (nhds I))
    (hbound : ∀ n d, |R n d| ≤ M) :
    Tendsto
      (fun n => ∑' d : ℕ,
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d)
      atTop (nhds ((6 / Real.pi ^ 2) * I)) := by
  let B : ℕ → ℝ := fun d => M / (d : ℝ) ^ 2
  have hB : Summable B := by
    simpa [B, div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left M
  have hterm (d : ℕ) :
      Tendsto
        (fun n => ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d)
        atTop
        (nhds (((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * I)) := by
    by_cases hd : d = 0
    · subst d
      simp
    · exact tendsto_const_nhds.mul (hR d (Nat.pos_of_ne_zero hd))
  have hdom : ∀ n d,
      ‖((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d‖ ≤ B d := by
    intro n d
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (sq_nonneg (d : ℝ))]
    rw [div_mul_eq_mul_div]
    change |(ArithmeticFunction.moebius d : ℝ)| * |R n d| / (d : ℝ) ^ 2 ≤
      M / (d : ℝ) ^ 2
    apply div_le_div_of_nonneg_right _ (sq_nonneg (d : ℝ))
    calc
      |(ArithmeticFunction.moebius d : ℝ)| * |R n d|
          ≤ 1 * M := mul_le_mul (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
            (hbound n d) (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  have hlim := tendsto_tsum_of_dominated_convergence hB hterm
      (Eventually.of_forall hdom)
  have heq : (∑' k : ℕ,
      ((ArithmeticFunction.moebius k : ℝ) / (k : ℝ) ^ 2) * I) =
        (6 / Real.pi ^ 2) * I := by
    rw [tsum_mul_right, tsum_moebius_div_sq]
  simpa [heq] using hlim

/-- A reusable visible-lattice transfer principle.  Once a normalized coprime
sum has been rewritten by `weighted_coprime_sum_eq_moebius`, it is enough to
prove a termwise Riemann-sum limit and a summable `1 / d²` majorant. -/
lemma tendsto_visible_of_moebius_decomposition
    (V : ℕ → ℝ) (R : ℕ → ℕ → ℝ) (I M : ℝ)
    (hM : 0 ≤ M)
    (hdecomp : Filter.EventuallyEq atTop V (fun n => ∑' d : ℕ,
      ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) * R n d))
    (hR : ∀ d, Tendsto (fun n => R n d) atTop (nhds I))
    (hbound : ∀ n d, |R n d| ≤ M) :
    Tendsto V atTop (nhds ((6 / Real.pi ^ 2) * I)) :=
  (tendsto_moebius_weighted_tsum R I M hM hR hbound).congr' hdecomp.symm

/-- A fully arithmetic visible-lattice limit theorem.  Its hypotheses are the
termwise grid limits and uniform bound that the preceding
`scaled_integer_lattice_riemann` lemma is designed to provide. -/
lemma tendsto_normalized_weighted_coprime_sum
    (P : ℕ → Finset (ℕ × ℕ)) (w : ℕ → ℕ × ℕ → ℝ)
    (I M : ℝ) (hM : 0 ≤ M)
    (hnonzero : ∀ n p, p ∈ P n → p ≠ (0, 0))
    (hR : ∀ d, Tendsto (fun n => normalizedDivisorGridTerm P w n d)
      atTop (nhds I))
    (hbound : ∀ n d, |normalizedDivisorGridTerm P w n d| ≤ M) :
    Tendsto
      (fun n => (∑ p ∈ P n, if Nat.Coprime p.1 p.2 then w n p else 0) /
        (n : ℝ) ^ 2)
      atTop (nhds ((6 / Real.pi ^ 2) * I)) := by
  apply tendsto_visible_of_moebius_decomposition _ _ I M hM _ hR hbound
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact normalized_weighted_coprime_sum_eq_tsum P w hnonzero hn.ne'

/-- Direct specialization of the Möbius--Tannery theorem to normalized
positive denominator pairs in the Farey triangle.  The two analytic
hypotheses are precisely the fixed-divisor grid limit and its uniform
majorant. -/
theorem tendsto_farey_denominatorPair_sum_of_grid_limits
    (F : ℝ × ℝ → ℝ) (I M : ℝ) (hM : 0 ≤ M)
    (hR : ∀ d, Tendsto
      (fun Q => normalizedDivisorGridTerm Farey.denominatorPairFinset
        (Farey.normalizedDenominatorPairWeight F) Q d) atTop (nhds I))
    (hbound : ∀ Q d,
      |normalizedDivisorGridTerm Farey.denominatorPairFinset
        (Farey.normalizedDenominatorPairWeight F) Q d| ≤ M) :
    Tendsto
      (fun Q =>
        (∑ p ∈ Farey.denominatorPairFinset Q,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight F Q p else 0) /
          (Q : ℝ) ^ 2)
      atTop (nhds ((6 / Real.pi ^ 2) * I)) := by
  exact tendsto_normalized_weighted_coprime_sum
    Farey.denominatorPairFinset (Farey.normalizedDenominatorPairWeight F) I M hM
    (fun Q p hp => Farey.denominatorPairFinset_ne_zero Q p hp) hR hbound

/-! #### The continuous-weight Farey-triangle specialization -/

/-- The Farey triangle in Mathlib's `Fin 2 → ℝ` lattice coordinates. -/
def fareyTrianglePi : Set (Fin 2 → ℝ) :=
  {x | 0 < x 0 ∧ x 0 ≤ 1 ∧ 0 < x 1 ∧ x 1 ≤ 1 ∧ 1 < x 0 + x 1}

def fareyPairVec (a b : ℕ) : Fin 2 → ℝ := ![(a : ℝ), (b : ℝ)]

/-- A positive denominator pair after division by a fixed common divisor. -/
structure ScaledFareyPair (Q d : ℕ) where
  a : ℕ
  b : ℕ
  ha : 0 < a
  hb : 0 < b
  hda : d * a ≤ Q
  hdb : d * b ≤ Q
  hsum : Q < d * (a + b)

def FareyGridPoint (Q d : ℕ) :=
  ↑(((d : ℝ)⁻¹ • fareyTrianglePi) ∩
    (Q : ℝ)⁻¹ • Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin 2))))

lemma normalized_fareyPair_mem_grid {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (p : ScaledFareyPair Q d) :
    (Q : ℝ)⁻¹ • fareyPairVec p.a p.b ∈
      ((d : ℝ)⁻¹ • fareyTrianglePi) ∩
        (Q : ℝ)⁻¹ • (Submodule.span ℤ
          (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ)) := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hQposR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hd
  have hre (r : ℝ) : (d : ℝ) * ((Q : ℝ)⁻¹ * r) = (d : ℝ) * r / Q := by
    field_simp
  constructor
  · rw [Set.mem_inv_smul_set_iff₀ hdR]
    change 0 < (d : ℝ) * ((Q : ℝ)⁻¹ * p.a) ∧
      (d : ℝ) * ((Q : ℝ)⁻¹ * p.a) ≤ 1 ∧
      0 < (d : ℝ) * ((Q : ℝ)⁻¹ * p.b) ∧
      (d : ℝ) * ((Q : ℝ)⁻¹ * p.b) ≤ 1 ∧
      1 < (d : ℝ) * ((Q : ℝ)⁻¹ * p.a) +
        (d : ℝ) * ((Q : ℝ)⁻¹ * p.b)
    constructor
    · rw [hre]
      exact div_pos (mul_pos hdposR (by exact_mod_cast p.ha)) hQposR
    constructor
    · rw [hre, div_le_one hQposR]
      exact_mod_cast p.hda
    constructor
    · rw [hre]
      exact div_pos (mul_pos hdposR (by exact_mod_cast p.hb)) hQposR
    constructor
    · rw [hre, div_le_one hQposR]
      exact_mod_cast p.hdb
    · rw [hre, hre, ← add_div, one_lt_div hQposR]
      exact_mod_cast (show Q < d * p.a + d * p.b by simpa [mul_add] using p.hsum)
  · letI : NeZero Q := ⟨hQ.ne'⟩
    change (Q : ℝ)⁻¹ • fareyPairVec p.a p.b ∈
      (Q : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))
    rw [BoxIntegral.unitPartition.mem_smul_span_iff]
    intro i
    fin_cases i
    · exact ⟨(p.a : ℤ), by simp [fareyPairVec, hQR]⟩
    · exact ⟨(p.b : ℤ), by simp [fareyPairVec, hQR]⟩

def scaledFareyPairToGrid {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    ScaledFareyPair Q d → FareyGridPoint Q d :=
  fun p => ⟨(Q : ℝ)⁻¹ • fareyPairVec p.a p.b,
    normalized_fareyPair_mem_grid hQ hd p⟩

def gridToScaledFareyPair {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    FareyGridPoint Q d → ScaledFareyPair Q d := fun x => by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hxprop : (x : Fin 2 → ℝ) ∈ ((d : ℝ)⁻¹ • fareyTrianglePi) ∩
      (Q : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) := x.property
  have htri := (Set.mem_inv_smul_set_iff₀ hdR fareyTrianglePi (x : Fin 2 → ℝ)).mp hxprop.1
  change 0 < (d : ℝ) * x.1 0 ∧ (d : ℝ) * x.1 0 ≤ 1 ∧
    0 < (d : ℝ) * x.1 1 ∧ (d : ℝ) * x.1 1 ≤ 1 ∧
    1 < (d : ℝ) * x.1 0 + (d : ℝ) * x.1 1 at htri
  let z0 : ℤ := Classical.choose
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp hxprop.2) 0)
  let z1 : ℤ := Classical.choose
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp hxprop.2) 1)
  have hz0 : (z0 : ℝ) = (Q : ℝ) * x.1 0 := Classical.choose_spec
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp hxprop.2) 0)
  have hz1 : (z1 : ℝ) = (Q : ℝ) * x.1 1 := Classical.choose_spec
    ((BoxIntegral.unitPartition.mem_smul_span_iff.mp hxprop.2) 1)
  have hx0pos : 0 < x.1 0 := by nlinarith [htri.1]
  have hx1pos : 0 < x.1 1 := by nlinarith [htri.2.2.1]
  have hz0posR : (0 : ℝ) < z0 := hz0.symm ▸ mul_pos (by exact_mod_cast hQ) hx0pos
  have hz1posR : (0 : ℝ) < z1 := hz1.symm ▸ mul_pos (by exact_mod_cast hQ) hx1pos
  have hz0pos : 0 < z0 := by exact_mod_cast hz0posR
  have hz1pos : 0 < z1 := by exact_mod_cast hz1posR
  have hfloor0 : ⌊(Q : ℝ) * x.1 0⌋ = z0 := by rw [← hz0, Int.floor_intCast]
  have hfloor1 : ⌊(Q : ℝ) * x.1 1⌋ = z1 := by rw [← hz1, Int.floor_intCast]
  let a := ⌊(Q : ℝ) * x.1 0⌋.natAbs
  let b := ⌊(Q : ℝ) * x.1 1⌋.natAbs
  have haCast : (a : ℝ) = (Q : ℝ) * x.1 0 := by
    have haInt : (a : ℤ) = z0 := by
      rw [show (a : ℤ) = ⌊(Q : ℝ) * x.1 0⌋.natAbs by rfl,
        Int.natAbs_of_nonneg]
      · exact hfloor0
      · rw [hfloor0]; exact hz0pos.le
    calc
      (a : ℝ) = (z0 : ℝ) := by exact_mod_cast haInt
      _ = (Q : ℝ) * x.1 0 := hz0
  have hbCast : (b : ℝ) = (Q : ℝ) * x.1 1 := by
    have hbInt : (b : ℤ) = z1 := by
      rw [show (b : ℤ) = ⌊(Q : ℝ) * x.1 1⌋.natAbs by rfl,
        Int.natAbs_of_nonneg]
      · exact hfloor1
      · rw [hfloor1]; exact hz1pos.le
    calc
      (b : ℝ) = (z1 : ℝ) := by exact_mod_cast hbInt
      _ = (Q : ℝ) * x.1 1 := hz1
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show a = z0.natAbs by simp [a, hfloor0]]
    exact Int.natAbs_pos.mpr hz0pos.ne'
  · rw [show b = z1.natAbs by simp [b, hfloor1]]
    exact Int.natAbs_pos.mpr hz1pos.ne'
  · exact_mod_cast (show (d : ℝ) * a ≤ Q by rw [haCast]; nlinarith [htri.2.1])
  · exact_mod_cast (show (d : ℝ) * b ≤ Q by rw [hbCast]; nlinarith [htri.2.2.2.1])
  · exact_mod_cast (show (Q : ℝ) < d * (a + b) by
      rw [haCast, hbCast]; nlinarith [htri.2.2.2.2])

lemma scaledFareyPair_ext {Q d : ℕ} {p q : ScaledFareyPair Q d}
    (ha : p.a = q.a) (hb : p.b = q.b) : p = q := by
  cases p
  cases q
  simp_all

lemma fareyGrid_floor_natAbs_cast {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (x : FareyGridPoint Q d) (i : Fin 2) :
    ((⌊(Q : ℝ) * x.1 i⌋.natAbs : ℕ) : ℝ) = (Q : ℝ) * x.1 i := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hxprop : (x : Fin 2 → ℝ) ∈ ((d : ℝ)⁻¹ • fareyTrianglePi) ∩
      (Q : ℝ)⁻¹ • Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) := x.property
  have htri := (Set.mem_inv_smul_set_iff₀ hdR fareyTrianglePi (x : Fin 2 → ℝ)).mp hxprop.1
  change 0 < (d : ℝ) * x.1 0 ∧ (d : ℝ) * x.1 0 ≤ 1 ∧
    0 < (d : ℝ) * x.1 1 ∧ (d : ℝ) * x.1 1 ≤ 1 ∧
    1 < (d : ℝ) * x.1 0 + (d : ℝ) * x.1 1 at htri
  obtain ⟨z, hz⟩ := (BoxIntegral.unitPartition.mem_smul_span_iff.mp hxprop.2) i
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxi : 0 < x.1 i := by
    fin_cases i
    · rcases (mul_pos_iff.mp htri.1) with h | h
      · exact h.2
      · exact (not_lt_of_ge hdposR.le h.1).elim
    · rcases (mul_pos_iff.mp htri.2.2.1) with h | h
      · exact h.2
      · exact (not_lt_of_ge hdposR.le h.1).elim
  have hzposR : (0 : ℝ) < z := by
    change (0 : ℝ) < (algebraMap ℤ ℝ) z
    rw [hz]
    exact mul_pos (by exact_mod_cast hQ) hxi
  have hzpos : 0 < z := by exact_mod_cast hzposR
  have hfloor : ⌊(Q : ℝ) * x.1 i⌋ = z := by
    rw [← hz]
    change ⌊(z : ℝ)⌋ = z
    exact Int.floor_intCast z
  calc
    ((⌊(Q : ℝ) * x.1 i⌋.natAbs : ℕ) : ℝ) = (z.natAbs : ℝ) := by rw [hfloor]
    _ = ((z.natAbs : ℤ) : ℝ) := by norm_num
    _ = (z : ℝ) := by rw [Int.natCast_natAbs, abs_of_pos hzpos]
    _ = (Q : ℝ) * x.1 i := by simpa using hz

@[simp] lemma gridToScaledFareyPair_a {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (x : FareyGridPoint Q d) :
    (gridToScaledFareyPair hQ hd x).a = ⌊(Q : ℝ) * x.1 0⌋.natAbs := rfl

@[simp] lemma gridToScaledFareyPair_b {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (x : FareyGridPoint Q d) :
    (gridToScaledFareyPair hQ hd x).b = ⌊(Q : ℝ) * x.1 1⌋.natAbs := rfl

def scaledFareyPairEquivGrid {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    ScaledFareyPair Q d ≃ FareyGridPoint Q d where
  toFun := scaledFareyPairToGrid hQ hd
  invFun := gridToScaledFareyPair hQ hd
  left_inv := by
    intro p
    apply scaledFareyPair_ext <;>
      simp [gridToScaledFareyPair, scaledFareyPairToGrid, fareyPairVec, hQ.ne']
    all_goals rfl
  right_inv := by
    intro x
    apply Subtype.ext
    funext i
    fin_cases i
    · change (Q : ℝ)⁻¹ * ((gridToScaledFareyPair hQ hd x).a : ℝ) = x.1 0
      rw [gridToScaledFareyPair_a, fareyGrid_floor_natAbs_cast hQ hd x 0]
      field_simp
    · change (Q : ℝ)⁻¹ * ((gridToScaledFareyPair hQ hd x).b : ℝ) = x.1 1
      rw [gridToScaledFareyPair_b, fareyGrid_floor_natAbs_cast hQ hd x 1]
      field_simp

def DivisibleFareyPair (Q d : ℕ) : Type :=
  ↑((Farey.denominatorPairFinset Q).filter
    (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2))

def divisibleFareyPairToScaled {Q d : ℕ}
    (p : DivisibleFareyPair Q d) : ScaledFareyPair Q d := by
  have hp := Finset.mem_filter.mp p.property
  have hP := Finset.mem_filter.mp hp.1
  have hbox := Finset.mem_product.mp hP.1
  refine ⟨p.1.1 / d, p.1.2 / d, ?_, ?_, ?_, ?_, ?_⟩
  · have hp1 : 0 < p.1.1 := (Finset.mem_Icc.mp hbox.1).1
    exact Nat.div_pos (Nat.le_of_dvd hp1 hp.2.1) (Nat.pos_of_dvd_of_pos hp.2.1 hp1)
  · have hp2 : 0 < p.1.2 := (Finset.mem_Icc.mp hbox.2).1
    exact Nat.div_pos (Nat.le_of_dvd hp2 hp.2.2) (Nat.pos_of_dvd_of_pos hp.2.2 hp2)
  · rw [Nat.mul_div_cancel' hp.2.1]
    exact (Finset.mem_Icc.mp hbox.1).2
  · rw [Nat.mul_div_cancel' hp.2.2]
    exact (Finset.mem_Icc.mp hbox.2).2
  · rw [mul_add, Nat.mul_div_cancel' hp.2.1, Nat.mul_div_cancel' hp.2.2]
    exact hP.2

def scaledToDivisibleFareyPair {Q d : ℕ}
    (p : ScaledFareyPair Q d) : DivisibleFareyPair Q d := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    have hsum := p.hsum
    simp [hd0] at hsum
  refine ⟨(d * p.a, d * p.b), ?_⟩
  rw [Finset.mem_filter]
  constructor
  · rw [Farey.denominatorPairFinset, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨mul_pos hd p.ha, p.hda⟩,
       Finset.mem_Icc.mpr ⟨mul_pos hd p.hb, p.hdb⟩⟩,
      by simpa [mul_add] using p.hsum⟩
  · exact ⟨dvd_mul_right d p.a, dvd_mul_right d p.b⟩

def divisibleFareyPairEquivScaled {Q d : ℕ} (hd : 0 < d) :
    DivisibleFareyPair Q d ≃ ScaledFareyPair Q d where
  toFun := divisibleFareyPairToScaled
  invFun := scaledToDivisibleFareyPair
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · exact Nat.mul_div_cancel' (Finset.mem_filter.mp p.property).2.1
    · exact Nat.mul_div_cancel' (Finset.mem_filter.mp p.property).2.2
  right_inv := by
    intro p
    apply scaledFareyPair_ext
    · change d * p.a / d = p.a
      simpa [Nat.mul_comm] using Nat.mul_div_left p.a hd
    · change d * p.b / d = p.b
      simpa [Nat.mul_comm] using Nat.mul_div_left p.b hd

def divisibleFareyPairEquivGrid {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    DivisibleFareyPair Q d ≃ FareyGridPoint Q d :=
  (divisibleFareyPairEquivScaled hd).trans (scaledFareyPairEquivGrid hQ hd)

def fareyPiWeight (F : ℝ × ℝ → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  F (x 0, x 1)

lemma divisibleFareyPairEquivGrid_coord_zero {Q d : ℕ}
    (hQ : 0 < Q) (hd : 0 < d) (p : DivisibleFareyPair Q d) :
    ((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) : Fin 2 → ℝ) 0 =
      (Q : ℝ)⁻¹ * ((p.1.1 / d : ℕ) : ℝ) := rfl

lemma divisibleFareyPairEquivGrid_coord_one {Q d : ℕ}
    (hQ : 0 < Q) (hd : 0 < d) (p : DivisibleFareyPair Q d) :
    ((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) : Fin 2 → ℝ) 1 =
      (Q : ℝ)⁻¹ * ((p.1.2 / d : ℕ) : ℝ) := rfl

lemma divisibleFareyPair_weight_eq_grid (F : ℝ × ℝ → ℝ)
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) (p : DivisibleFareyPair Q d) :
    Farey.normalizedDenominatorPairWeight F Q p.1 =
      fareyPiWeight F ((d : ℝ) •
        ((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) : Fin 2 → ℝ)) := by
  have hd1 := (Finset.mem_filter.mp p.property).2.1
  have hd2 := (Finset.mem_filter.mp p.property).2.2
  simp only [Farey.normalizedDenominatorPairWeight, fareyPiWeight,
    Pi.smul_apply, smul_eq_mul]
  congr 2
  · rw [divisibleFareyPairEquivGrid_coord_zero, Nat.cast_div hd1]
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
    exact_mod_cast hd.ne'
  · rw [divisibleFareyPairEquivGrid_coord_one, Nat.cast_div hd2]
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
    exact_mod_cast hd.ne'

lemma filtered_fareyPairWeight_eq_grid_tsum (F : ℝ × ℝ → ℝ)
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    (∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) =
      ∑' x : FareyGridPoint Q d,
        fareyPiWeight F ((d : ℝ) • (x : Fin 2 → ℝ)) := by
  calc
    (∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) =
        ∑' p : DivisibleFareyPair Q d,
          Farey.normalizedDenominatorPairWeight F Q p.1 :=
      (Finset.tsum_subtype
        ((Farey.denominatorPairFinset Q).filter
          (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2))
        (Farey.normalizedDenominatorPairWeight F Q)).symm
    _ = ∑' p : DivisibleFareyPair Q d,
        fareyPiWeight F ((d : ℝ) •
          (((divisibleFareyPairEquivGrid hQ hd) p : FareyGridPoint Q d) :
            Fin 2 → ℝ)) := by
      apply tsum_congr
      intro p
      exact divisibleFareyPair_weight_eq_grid F hQ hd p
    _ = ∑' x : FareyGridPoint Q d,
        fareyPiWeight F ((d : ℝ) • (x : Fin 2 → ℝ)) := by
      simpa using ((divisibleFareyPairEquivGrid hQ hd).tsum_eq
        (fun x : FareyGridPoint Q d =>
          fareyPiWeight F ((d : ℝ) • (x : Fin 2 → ℝ))))

lemma measurableSet_fareyTrianglePi : MeasurableSet fareyTrianglePi := by
  unfold fareyTrianglePi
  measurability

lemma isBounded_fareyTrianglePi : Bornology.IsBounded fareyTrianglePi := by
  apply (Metric.isBounded_Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1)).subset
  intro x hx
  rw [Set.mem_Icc]
  constructor
  · intro i
    fin_cases i
    · exact hx.1.le
    · exact hx.2.2.1.le
  · intro i
    fin_cases i
    · exact hx.2.1
    · exact hx.2.2.2.1

lemma convex_fareyTrianglePi : Convex ℝ fareyTrianglePi := by
  let f0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let f1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
  have h0p : Convex ℝ {x : Fin 2 → ℝ | 0 < x 0} :=
    convex_halfSpace_gt f0.isLinear 0
  have h0u : Convex ℝ {x : Fin 2 → ℝ | x 0 ≤ 1} :=
    convex_halfSpace_le f0.isLinear 1
  have h1p : Convex ℝ {x : Fin 2 → ℝ | 0 < x 1} :=
    convex_halfSpace_gt f1.isLinear 0
  have h1u : Convex ℝ {x : Fin 2 → ℝ | x 1 ≤ 1} :=
    convex_halfSpace_le f1.isLinear 1
  have hsum : Convex ℝ {x : Fin 2 → ℝ | 1 < x 0 + x 1} :=
    convex_halfSpace_gt (f0 + f1).isLinear 1
  simpa [fareyTrianglePi, f0, f1, Set.ofPred_and] using
    h0p.inter (h0u.inter (h1p.inter (h1u.inter hsum)))

/-- The divisor-normalized, not-yet-Möbius-weighted Farey grid term. -/
def fareyDivisorGridTerm (F : ℝ × ℝ → ℝ) (Q d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 *
    (∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
      Farey.normalizedDenominatorPairWeight F Q p) / (Q : ℝ) ^ 2

lemma tendsto_fareyDivisorGridTerm (F : ℝ × ℝ → ℝ) (hF : Continuous F)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun Q => fareyDivisorGridTerm F Q d) atTop
      (nhds (∫ x in fareyTrianglePi, fareyPiWeight F x)) := by
  have hpi : Continuous (fareyPiWeight F) :=
    hF.comp ((continuous_apply 0).prodMk (continuous_apply 1))
  have hs₁ : Bornology.IsBounded ((d : ℝ)⁻¹ • fareyTrianglePi) :=
    isBounded_fareyTrianglePi.smul₀ _
  have hs₂ : MeasurableSet ((d : ℝ)⁻¹ • fareyTrianglePi) :=
    measurableSet_fareyTrianglePi.const_smul₀ _
  have hs₃ : volume (frontier ((d : ℝ)⁻¹ • fareyTrianglePi)) = 0 :=
    (convex_fareyTrianglePi.smul _).addHaar_frontier volume
  have hlim := scaled_integer_lattice_riemann_to_integral
    fareyTrianglePi (fareyPiWeight F) d hd hpi hs₁ hs₂ hs₃
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  rw [fareyDivisorGridTerm, filtered_fareyPairWeight_eq_grid_tsum F hQ hd]
  norm_num
  unfold FareyGridPoint
  ring

lemma card_divisible_denominatorPairFinset_le (Q d : ℕ) (hd : 0 < d) :
    ((Farey.denominatorPairFinset Q).filter
      (fun p => d ∣ p.1 ∧ d ∣ p.2)).card ≤ (Q / d) ^ 2 := by
  let D := (Farey.denominatorPairFinset Q).filter
    (fun p => d ∣ p.1 ∧ d ∣ p.2)
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 / d, p.2 / d)
  have hinj : Set.InjOn f D := by
    intro p hp q hq hpq
    have hpdiv := (Finset.mem_filter.mp hp).2
    have hqdiv := (Finset.mem_filter.mp hq).2
    apply Prod.ext
    · have hcoord := congrArg Prod.fst hpq
      simp only [f] at hcoord
      rw [← Nat.mul_div_cancel' hpdiv.1, ← Nat.mul_div_cancel' hqdiv.1, hcoord]
    · have hcoord := congrArg Prod.snd hpq
      simp only [f] at hcoord
      rw [← Nat.mul_div_cancel' hpdiv.2, ← Nat.mul_div_cancel' hqdiv.2, hcoord]
  have himage : D.image f ⊆
      (Finset.Icc 1 (Q / d)).product (Finset.Icc 1 (Q / d)) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hpD := Finset.mem_filter.mp hp
    have hpP := Finset.mem_filter.mp hpD.1
    have hpbox := Finset.mem_product.mp hpP.1
    change (p.1 / d, p.2 / d) ∈
      (Finset.Icc 1 (Q / d)).product (Finset.Icc 1 (Q / d))
    apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hpbox.1).1 hpD.2.1) hd,
        Nat.div_le_div_right (Finset.mem_Icc.mp hpbox.1).2⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hpbox.2).1 hpD.2.2) hd,
        Nat.div_le_div_right (Finset.mem_Icc.mp hpbox.2).2⟩
  calc
    D.card = (D.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((Finset.Icc 1 (Q / d)).product (Finset.Icc 1 (Q / d))).card :=
      Finset.card_le_card himage
    _ = (Q / d) ^ 2 := by simp [pow_two]

lemma abs_fareyDivisorGridTerm_le_of_bound
    (F : ℝ × ℝ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ Q p, p ∈ Farey.denominatorPairFinset Q →
      |Farey.normalizedDenominatorPairWeight F Q p| ≤ C)
    (Q d : ℕ) : |fareyDivisorGridTerm F Q d| ≤ C := by
  by_cases hQ0 : Q = 0
  · subst Q
    simp [fareyDivisorGridTerm, Farey.denominatorPairFinset]
    exact hC0
  by_cases hd0 : d = 0
  · subst d
    simp [fareyDivisorGridTerm]
    exact hC0
  have hQ : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  let D := (Farey.denominatorPairFinset Q).filter
    (fun p => d ∣ p.1 ∧ d ∣ p.2)
  have hsum : |∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
      Farey.normalizedDenominatorPairWeight F Q p| ≤ (D.card : ℝ) * C := by
    calc
      |∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
          Farey.normalizedDenominatorPairWeight F Q p| ≤
          ∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
            |Farey.normalizedDenominatorPairWeight F Q p| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ Farey.denominatorPairFinset Q with
          d ∣ _p.1 ∧ d ∣ _p.2, C := by
        apply Finset.sum_le_sum
        intro p hp
        exact hC Q p (Finset.mem_filter.mp hp).1
      _ = (D.card : ℝ) * C := by simp [D]
  have hcardN := card_divisible_denominatorPairFinset_le Q d hd
  have hcard : (D.card : ℝ) ≤ ((Q / d : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcardN
  have hmulN : d * (Q / d) ≤ Q := Nat.mul_div_le Q d
  have hmul : (d : ℝ) ^ 2 * ((Q / d : ℕ) : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by
    have hmulR : (d : ℝ) * (Q / d : ℕ) ≤ Q := by exact_mod_cast hmulN
    calc
      (d : ℝ) ^ 2 * ((Q / d : ℕ) : ℝ) ^ 2 =
          ((d : ℝ) * (Q / d : ℕ)) ^ 2 := by ring
      _ ≤ (Q : ℝ) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (by positivity) hmulR
  rw [fareyDivisorGridTerm, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg (d : ℝ)), abs_of_nonneg (sq_nonneg (Q : ℝ))]
  apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hQ))).2
  calc
    (d : ℝ) ^ 2 *
          |∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
            Farey.normalizedDenominatorPairWeight F Q p| ≤
        (d : ℝ) ^ 2 * ((D.card : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ (d : ℝ) ^ 2 * (((Q / d : ℕ) : ℝ) ^ 2 * C) := by
      gcongr
    _ ≤ C * (Q : ℝ) ^ 2 := by
      nlinarith

lemma continuous_fareyPairWeight_uniform_bound
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q p, p ∈ Farey.denominatorPairFinset Q →
      |Farey.normalizedDenominatorPairWeight F Q p| ≤ C := by
  have hcompact : IsCompact (Set.Icc ((0, 0) : ℝ × ℝ) (1, 1)) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hF.continuousOn
  have hC0 : 0 ≤ C := by
    have hzero := hC (0, 0) (by simp)
    exact (norm_nonneg (F (0, 0))).trans hzero
  refine ⟨C, hC0, ?_⟩
  intro Q p hp
  have hpP := Finset.mem_filter.mp hp
  have hpbox := Finset.mem_product.mp hpP.1
  have hp1 := (Finset.mem_Icc.mp hpbox.1).1
  have hp1Q := (Finset.mem_Icc.mp hpbox.1).2
  have hQ : 0 < Q := by omega
  rw [← Real.norm_eq_abs]
  apply hC
  rw [Set.mem_Icc]
  constructor
  · constructor
    · exact div_nonneg (by positivity) (by positivity)
    · exact div_nonneg (by positivity) (by positivity)
  · constructor
    · exact (div_le_one (by exact_mod_cast hQ)).2 (by
        exact_mod_cast (Finset.mem_Icc.mp hpbox.1).2)
    · exact (div_le_one (by exact_mod_cast hQ)).2 (by
        exact_mod_cast (Finset.mem_Icc.mp hpbox.2).2)

lemma normalizedDivisorGridTerm_farey_eq (F : ℝ × ℝ → ℝ)
    (Q d : ℕ) (hd : 0 < d) :
    normalizedDivisorGridTerm Farey.denominatorPairFinset
      (Farey.normalizedDenominatorPairWeight F) Q d =
        fareyDivisorGridTerm F Q d := by
  rw [normalizedDivisorGridTerm]
  by_cases hm : d ∈ commonDivisors (Farey.denominatorPairFinset Q)
  · rw [if_pos hm]
    rfl
  · rw [if_neg hm]
    have hsum : (∑ p ∈ Farey.denominatorPairFinset Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      apply hm
      have hpP := (Finset.mem_filter.mp hp).1
      have hpdiv := (Finset.mem_filter.mp hp).2
      rw [commonDivisors]
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hpP, ?_⟩
      rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_gcd hpdiv.1 hpdiv.2,
        by
          intro hg
          have hpzero : p = (0, 0) := by
            apply Prod.ext <;> simp_all [Nat.gcd_eq_zero_iff]
          exact Farey.denominatorPairFinset_ne_zero Q p hpP hpzero⟩
    simp [fareyDivisorGridTerm, hsum]

/-- Continuous weights on the whole Farey triangle satisfy the primitive
lattice-point equidistribution theorem. -/
theorem tendsto_farey_denominatorPair_sum_pi
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Tendsto
      (fun Q =>
        (∑ p ∈ Farey.denominatorPairFinset Q,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight F Q p else 0) /
          (Q : ℝ) ^ 2)
      atTop (nhds ((6 / Real.pi ^ 2) *
        ∫ x in fareyTrianglePi, fareyPiWeight F x)) := by
  obtain ⟨C, hC0, hC⟩ := continuous_fareyPairWeight_uniform_bound F hF
  let R := fun Q d => normalizedDivisorGridTerm Farey.denominatorPairFinset
    (Farey.normalizedDenominatorPairWeight F) Q d
  have hR : ∀ d, 0 < d → Tendsto (fun Q => R Q d) atTop
      (nhds (∫ x in fareyTrianglePi, fareyPiWeight F x)) := by
    intro d hd
    apply (tendsto_fareyDivisorGridTerm F hF d hd).congr'
    exact Eventually.of_forall (fun Q => (normalizedDivisorGridTerm_farey_eq F Q d hd).symm)
  have hbound : ∀ Q d, |R Q d| ≤ C := by
    intro Q d
    by_cases hd : d = 0
    · subst d
      simp [R, normalizedDivisorGridTerm, hC0]
    · change |normalizedDivisorGridTerm Farey.denominatorPairFinset
          (Farey.normalizedDenominatorPairWeight F) Q d| ≤ C
      rw [normalizedDivisorGridTerm_farey_eq F Q d (Nat.pos_of_ne_zero hd)]
      exact abs_fareyDivisorGridTerm_le_of_bound F C hC0 hC Q d
  have htan := tendsto_moebius_weighted_tsum_pos R
    (∫ x in fareyTrianglePi, fareyPiWeight F x) C hC0 hR hbound
  apply htan.congr'
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  exact (normalized_weighted_coprime_sum_eq_tsum
    Farey.denominatorPairFinset (Farey.normalizedDenominatorPairWeight F)
    (fun Q p hp => Farey.denominatorPairFinset_ne_zero Q p hp) hQ.ne').symm

/-! #### Fixed convex cells inside the Farey triangle -/

def normalizedFareyPairVec (Q : ℕ) (p : ℕ × ℕ) : Fin 2 → ℝ :=
  (Q : ℝ)⁻¹ • fareyPairVec p.1 p.2

noncomputable def fareyCellPairFinset (s : Set (Fin 2 → ℝ)) (Q : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (Farey.denominatorPairFinset Q).filter
    (fun p => normalizedFareyPairVec Q p ∈ s)

def DivisibleFareyCellPair (s : Set (Fin 2 → ℝ)) (Q d : ℕ) : Type :=
  ↑((fareyCellPairFinset s Q).filter (fun p => d ∣ p.1 ∧ d ∣ p.2))

def RestrictedDivisibleFareyPair (s : Set (Fin 2 → ℝ)) (Q d : ℕ) : Type :=
  {p : DivisibleFareyPair Q d // normalizedFareyPairVec Q p.1 ∈ s}

def divisibleFareyCellPairEquivRestricted (s : Set (Fin 2 → ℝ)) (Q d : ℕ) :
    DivisibleFareyCellPair s Q d ≃ RestrictedDivisibleFareyPair s Q d where
  toFun := fun p => by
    have hp := Finset.mem_filter.mp p.property
    have hpcell : p.1 ∈ Farey.denominatorPairFinset Q ∧
        normalizedFareyPairVec Q p.1 ∈ s := by
      simpa only [fareyCellPairFinset, Finset.mem_filter] using hp.1
    exact ⟨⟨p.1, Finset.mem_filter.mpr ⟨hpcell.1, hp.2⟩⟩, hpcell.2⟩
  invFun := fun p => by
    have hp := Finset.mem_filter.mp p.1.property
    refine ⟨p.1.1, Finset.mem_filter.mpr ⟨?_, hp.2⟩⟩
    simpa only [fareyCellPairFinset, Finset.mem_filter] using ⟨hp.1, p.property⟩
  left_inv := by intro p; apply Subtype.ext; rfl
  right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; rfl

lemma normalizedFareyPairVec_eq_smul_grid {Q d : ℕ}
    (hQ : 0 < Q) (hd : 0 < d) (p : DivisibleFareyPair Q d) :
    normalizedFareyPairVec Q p.1 = (d : ℝ) •
      ((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) : Fin 2 → ℝ) := by
  funext i
  fin_cases i
  · change (Q : ℝ)⁻¹ * (p.1.1 : ℝ) =
      (d : ℝ) *
        (((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) :
          Fin 2 → ℝ) 0)
    have hd1 := (Finset.mem_filter.mp p.property).2.1
    rw [divisibleFareyPairEquivGrid_coord_zero, Nat.cast_div hd1]
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
    exact_mod_cast hd.ne'
  · change (Q : ℝ)⁻¹ * (p.1.2 : ℝ) =
      (d : ℝ) *
        (((divisibleFareyPairEquivGrid hQ hd p : FareyGridPoint Q d) :
          Fin 2 → ℝ) 1)
    have hd2 := (Finset.mem_filter.mp p.property).2.2
    rw [divisibleFareyPairEquivGrid_coord_one, Nat.cast_div hd2]
    field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast hd.ne']
    exact_mod_cast hd.ne'

def RestrictedFareyGridPoint (s : Set (Fin 2 → ℝ)) (Q d : ℕ) : Type :=
  {x : FareyGridPoint Q d // (d : ℝ) • (x : Fin 2 → ℝ) ∈ s}

def restrictedDivisibleFareyPairEquivGrid (s : Set (Fin 2 → ℝ))
    {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    RestrictedDivisibleFareyPair s Q d ≃ RestrictedFareyGridPoint s Q d :=
  Equiv.subtypeEquiv (divisibleFareyPairEquivGrid hQ hd) (fun p => by
    rw [← normalizedFareyPairVec_eq_smul_grid hQ hd p])

def FareyCellGridPoint (s : Set (Fin 2 → ℝ)) (Q d : ℕ) : Type :=
  ↑(((d : ℝ)⁻¹ • s) ∩
    (Q : ℝ)⁻¹ • Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin 2))))

def restrictedFareyGridEquivCellGrid (s : Set (Fin 2 → ℝ))
    (hs : s ⊆ fareyTrianglePi) {Q d : ℕ} (hd : 0 < d) :
    RestrictedFareyGridPoint s Q d ≃ FareyCellGridPoint s Q d where
  toFun := fun x => by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    refine ⟨x.1.1, ?_⟩
    exact ⟨(Set.mem_inv_smul_set_iff₀ hdR s (x.1.1 : Fin 2 → ℝ)).mpr x.property,
      x.1.property.2⟩
  invFun := fun x => by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hdx : (d : ℝ) • (x.1 : Fin 2 → ℝ) ∈ s :=
      (Set.mem_inv_smul_set_iff₀ hdR s (x.1 : Fin 2 → ℝ)).mp x.property.1
    refine ⟨⟨x.1, ?_⟩, hdx⟩
    exact ⟨(Set.mem_inv_smul_set_iff₀ hdR fareyTrianglePi
      (x.1 : Fin 2 → ℝ)).mpr (hs hdx), x.property.2⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl

def divisibleFareyCellPairEquivGrid (s : Set (Fin 2 → ℝ))
    (hs : s ⊆ fareyTrianglePi) {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    DivisibleFareyCellPair s Q d ≃ FareyCellGridPoint s Q d :=
  (divisibleFareyCellPairEquivRestricted s Q d).trans
    ((restrictedDivisibleFareyPairEquivGrid s hQ hd).trans
      (restrictedFareyGridEquivCellGrid s hs hd))

lemma divisibleFareyCellPair_weight_eq_grid
    (s : Set (Fin 2 → ℝ)) (hs : s ⊆ fareyTrianglePi)
    (F : ℝ × ℝ → ℝ) {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d)
    (p : DivisibleFareyCellPair s Q d) :
    Farey.normalizedDenominatorPairWeight F Q p.1 =
      fareyPiWeight F ((d : ℝ) •
        ((divisibleFareyCellPairEquivGrid s hs hQ hd p : FareyCellGridPoint s Q d).1 :
          Fin 2 → ℝ)) := by
  change Farey.normalizedDenominatorPairWeight F Q p.1 =
    fareyPiWeight F ((d : ℝ) •
      (((divisibleFareyPairEquivGrid hQ hd)
        (divisibleFareyCellPairEquivRestricted s Q d p).1 : FareyGridPoint Q d) :
          Fin 2 → ℝ))
  exact divisibleFareyPair_weight_eq_grid F hQ hd
    (divisibleFareyCellPairEquivRestricted s Q d p).1

lemma filtered_fareyCellWeight_eq_grid_tsum
    (s : Set (Fin 2 → ℝ)) (hs : s ⊆ fareyTrianglePi)
    (F : ℝ × ℝ → ℝ) {Q d : ℕ} (hQ : 0 < Q) (hd : 0 < d) :
    (∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) =
      ∑' x : FareyCellGridPoint s Q d,
        fareyPiWeight F ((d : ℝ) • (x.1 : Fin 2 → ℝ)) := by
  calc
    (∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) =
        ∑' p : DivisibleFareyCellPair s Q d,
          Farey.normalizedDenominatorPairWeight F Q p.1 :=
      (Finset.tsum_subtype
        ((fareyCellPairFinset s Q).filter
          (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2))
        (Farey.normalizedDenominatorPairWeight F Q)).symm
    _ = ∑' p : DivisibleFareyCellPair s Q d,
        fareyPiWeight F ((d : ℝ) •
          (((divisibleFareyCellPairEquivGrid s hs hQ hd) p :
            FareyCellGridPoint s Q d).1 :
            Fin 2 → ℝ)) := by
      apply tsum_congr
      exact divisibleFareyCellPair_weight_eq_grid s hs F hQ hd
    _ = ∑' x : FareyCellGridPoint s Q d,
        fareyPiWeight F ((d : ℝ) • (x.1 : Fin 2 → ℝ)) := by
      simpa using ((divisibleFareyCellPairEquivGrid s hs hQ hd).tsum_eq
        (fun x : FareyCellGridPoint s Q d =>
          fareyPiWeight F ((d : ℝ) • (x.1 : Fin 2 → ℝ))))

def fareyCellDivisorGridTerm (s : Set (Fin 2 → ℝ))
    (F : ℝ × ℝ → ℝ) (Q d : ℕ) : ℝ :=
  (d : ℝ) ^ 2 *
    (∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
      Farey.normalizedDenominatorPairWeight F Q p) / (Q : ℝ) ^ 2

lemma tendsto_fareyCellDivisorGridTerm
    (s : Set (Fin 2 → ℝ)) (hs : s ⊆ fareyTrianglePi)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) (hsc : Convex ℝ s)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun Q => fareyCellDivisorGridTerm s F Q d) atTop
      (nhds (∫ x in s, fareyPiWeight F x)) := by
  have hpi : Continuous (fareyPiWeight F) :=
    hF.comp ((continuous_apply 0).prodMk (continuous_apply 1))
  have hlim := scaled_integer_lattice_riemann_to_integral
    s (fareyPiWeight F) d hd hpi (hsb.smul₀ _) (hsm.const_smul₀ _)
      ((hsc.smul _).addHaar_frontier volume)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  rw [fareyCellDivisorGridTerm, filtered_fareyCellWeight_eq_grid_tsum s hs F hQ hd]
  norm_num
  unfold FareyCellGridPoint
  ring

lemma card_divisible_fareyCellPairFinset_le
    (s : Set (Fin 2 → ℝ)) (Q d : ℕ) (hd : 0 < d) :
    ((fareyCellPairFinset s Q).filter
      (fun p => d ∣ p.1 ∧ d ∣ p.2)).card ≤ (Q / d) ^ 2 := by
  classical
  apply (Finset.card_le_card (t := (Farey.denominatorPairFinset Q).filter
    (fun p => d ∣ p.1 ∧ d ∣ p.2)) ?_).trans
    (card_divisible_denominatorPairFinset_le Q d hd)
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  rw [Finset.mem_filter]
  refine ⟨?_, hp'.2⟩
  simpa only [fareyCellPairFinset, Finset.mem_filter] using
    (Finset.mem_filter.mp hp'.1).1

lemma abs_fareyCellDivisorGridTerm_le_of_bound
    (s : Set (Fin 2 → ℝ)) (F : ℝ × ℝ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ Q p, p ∈ Farey.denominatorPairFinset Q →
      |Farey.normalizedDenominatorPairWeight F Q p| ≤ C)
    (Q d : ℕ) : |fareyCellDivisorGridTerm s F Q d| ≤ C := by
  classical
  by_cases hQ0 : Q = 0
  · subst Q
    simp [fareyCellDivisorGridTerm, fareyCellPairFinset,
      Farey.denominatorPairFinset]
    exact hC0
  by_cases hd0 : d = 0
  · subst d
    simp [fareyCellDivisorGridTerm]
    exact hC0
  have hQ : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  let D := (fareyCellPairFinset s Q).filter
    (fun p => d ∣ p.1 ∧ d ∣ p.2)
  have hsum : |∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
      Farey.normalizedDenominatorPairWeight F Q p| ≤ (D.card : ℝ) * C := by
    calc
      |∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
          Farey.normalizedDenominatorPairWeight F Q p| ≤
          ∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
            |Farey.normalizedDenominatorPairWeight F Q p| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ fareyCellPairFinset s Q with
          d ∣ _p.1 ∧ d ∣ _p.2, C := by
        apply Finset.sum_le_sum
        intro p hp
        apply hC Q p
        have hpcell := (Finset.mem_filter.mp hp).1
        simpa only [fareyCellPairFinset, Finset.mem_filter] using
          (Finset.mem_filter.mp hpcell).1
      _ = (D.card : ℝ) * C := by simp [D]
  have hcardN := card_divisible_fareyCellPairFinset_le s Q d hd
  have hcard : (D.card : ℝ) ≤ ((Q / d : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcardN
  have hmulN : d * (Q / d) ≤ Q := Nat.mul_div_le Q d
  have hmul : (d : ℝ) ^ 2 * ((Q / d : ℕ) : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 := by
    have hmulR : (d : ℝ) * (Q / d : ℕ) ≤ Q := by exact_mod_cast hmulN
    calc
      (d : ℝ) ^ 2 * ((Q / d : ℕ) : ℝ) ^ 2 =
          ((d : ℝ) * (Q / d : ℕ)) ^ 2 := by ring
      _ ≤ (Q : ℝ) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (by positivity) hmulR
  rw [fareyCellDivisorGridTerm, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg (d : ℝ)), abs_of_nonneg (sq_nonneg (Q : ℝ))]
  apply (div_le_iff₀ (sq_pos_of_pos (by exact_mod_cast hQ))).2
  calc
    (d : ℝ) ^ 2 *
          |∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
            Farey.normalizedDenominatorPairWeight F Q p| ≤
        (d : ℝ) ^ 2 * ((D.card : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ ≤ (d : ℝ) ^ 2 * (((Q / d : ℕ) : ℝ) ^ 2 * C) := by
      gcongr
    _ ≤ C * (Q : ℝ) ^ 2 := by
      nlinarith

lemma normalizedDivisorGridTerm_fareyCell_eq
    (s : Set (Fin 2 → ℝ)) (F : ℝ × ℝ → ℝ)
    (Q d : ℕ) (hd : 0 < d) :
    normalizedDivisorGridTerm (fareyCellPairFinset s)
      (Farey.normalizedDenominatorPairWeight F) Q d =
        fareyCellDivisorGridTerm s F Q d := by
  classical
  rw [normalizedDivisorGridTerm]
  by_cases hm : d ∈ commonDivisors (fareyCellPairFinset s Q)
  · rw [if_pos hm]
    rfl
  · rw [if_neg hm]
    have hsum : (∑ p ∈ fareyCellPairFinset s Q with d ∣ p.1 ∧ d ∣ p.2,
        Farey.normalizedDenominatorPairWeight F Q p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exfalso
      apply hm
      have hpP := (Finset.mem_filter.mp hp).1
      have hpdiv := (Finset.mem_filter.mp hp).2
      rw [commonDivisors]
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hpP, ?_⟩
      rw [Nat.mem_divisors]
      refine ⟨Nat.dvd_gcd hpdiv.1 hpdiv.2, ?_⟩
      intro hg
      have hpzero : p = (0, 0) := by
        apply Prod.ext <;> simp_all [Nat.gcd_eq_zero_iff]
      have hpbase : p ∈ Farey.denominatorPairFinset Q := by
        simpa only [fareyCellPairFinset, Finset.mem_filter] using
          (Finset.mem_filter.mp hpP).1
      exact Farey.denominatorPairFinset_ne_zero Q p hpbase hpzero
    simp [fareyCellDivisorGridTerm, hsum]

/-- Primitive lattice points are equidistributed in every fixed bounded,
measurable convex cell contained in the Farey triangle. -/
theorem tendsto_farey_cell_sum_pi
    (s : Set (Fin 2 → ℝ)) (hs : s ⊆ fareyTrianglePi)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) (hsc : Convex ℝ s)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Tendsto
      (fun Q =>
        (∑ p ∈ fareyCellPairFinset s Q,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight F Q p else 0) /
          (Q : ℝ) ^ 2)
      atTop (nhds ((6 / Real.pi ^ 2) * ∫ x in s, fareyPiWeight F x)) := by
  classical
  obtain ⟨C, hC0, hC⟩ := continuous_fareyPairWeight_uniform_bound F hF
  let R := fun Q d => normalizedDivisorGridTerm (fareyCellPairFinset s)
    (Farey.normalizedDenominatorPairWeight F) Q d
  have hR : ∀ d, 0 < d → Tendsto (fun Q => R Q d) atTop
      (nhds (∫ x in s, fareyPiWeight F x)) := by
    intro d hd
    apply (tendsto_fareyCellDivisorGridTerm s hs hsb hsm hsc F hF d hd).congr'
    exact Eventually.of_forall (fun Q =>
      (normalizedDivisorGridTerm_fareyCell_eq s F Q d hd).symm)
  have hbound : ∀ Q d, |R Q d| ≤ C := by
    intro Q d
    by_cases hd : d = 0
    · subst d
      simp [R, normalizedDivisorGridTerm, hC0]
    · change |normalizedDivisorGridTerm (fareyCellPairFinset s)
          (Farey.normalizedDenominatorPairWeight F) Q d| ≤ C
      rw [normalizedDivisorGridTerm_fareyCell_eq s F Q d (Nat.pos_of_ne_zero hd)]
      exact abs_fareyCellDivisorGridTerm_le_of_bound s F C hC0 hC Q d
  have htan := tendsto_moebius_weighted_tsum_pos R
    (∫ x in s, fareyPiWeight F x) C hC0 hR hbound
  apply htan.congr'
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  exact (normalized_weighted_coprime_sum_eq_tsum
    (fareyCellPairFinset s) (Farey.normalizedDenominatorPairWeight F)
    (fun Q p hp => by
      apply Farey.denominatorPairFinset_ne_zero Q p
      simpa only [fareyCellPairFinset, Finset.mem_filter] using
        (Finset.mem_filter.mp hp).1)
    hQ.ne').symm

/-! #### Moving continuous-linear threshold regions -/

namespace MovingThreshold

variable {I : Type*} [Fintype I]

/-- The standard integer lattice in the coordinate space `I → ℝ`. -/
abbrev integerLattice : Set (I → ℝ) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ I)) : Set (I → ℝ))

/-- The normalized integer-grid sum used in the box-integral Riemann-sum
theorem. -/
noncomputable def latticeRiemannSum
    (s : Set (I → ℝ)) (F : (I → ℝ) → ℝ) (n : ℕ) : ℝ :=
  (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))), F x) /
    n ^ Fintype.card I

lemma latticeSection_finite
    {s : Set (I → ℝ)} (hs : Bornology.IsBounded s)
    {n : ℕ} (hn : 0 < n) :
    (s ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))).Finite := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let e : ↑(s ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))) ≃
      ↑((n : ℝ) • s ∩ (integerLattice : Set (I → ℝ))) :=
    Equiv.subtypeEquiv (Equiv.smulRight hnR) (fun x ↦ by
      simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply,
        Set.smul_mem_smul_set_iff₀ hnR, ← Set.mem_inv_smul_set_iff₀ hnR])
  have htarget :
      ((n : ℝ) • s ∩ (integerLattice : Set (I → ℝ))).Finite :=
    ZSpan.setFinite_inter _ (Bornology.IsBounded.smul₀ hs (n : ℝ))
  letI := htarget.fintype
  letI : Finite ↑(s ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))) :=
    Finite.of_equiv _ e.symm
  exact Set.toFinite _

lemma latticeRiemannSum_mono
    {s t : Set (I → ℝ)} {F : (I → ℝ) → ℝ}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t)
    (hst : s ⊆ t) (hF : ∀ x, 0 ≤ F x)
    {n : ℕ} (hn : 0 < n) :
    latticeRiemannSum s F n ≤ latticeRiemannSum t F n := by
  let A := s ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))
  let B := t ∩ (n : ℝ)⁻¹ • (integerLattice : Set (I → ℝ))
  have hA : A.Finite := latticeSection_finite hs hn
  have hB : B.Finite := latticeSection_finite ht hn
  have hAB : A ⊆ B := Set.inter_subset_inter_left _ hst
  rw [latticeRiemannSum, latticeRiemannSum, tsum_subtype, tsum_subtype]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Summable.tsum_le_tsum
  · exact indicator_le_indicator_of_subset hAB (fun x ↦ hF x)
  · apply summable_of_hasFiniteSupport
    exact hA.subset Set.support_indicator_subset
  · apply summable_of_hasFiniteSupport
    exact hB.subset Set.support_indicator_subset

section ThresholdRegion

variable {K : Type*} [Fintype K]

/-- A bounded base region cut out by finitely many moving continuous-linear
half-space inequalities. -/
def linearThresholdRegion
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (r : ℝ) :
    Set (I → ℝ) :=
  B ∩ ⋂ k, {x | ℓ k x ≤ r}

lemma linearThresholdRegion_mono
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ) :
    Monotone (linearThresholdRegion B ℓ) := by
  intro r q hrq x hx
  rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
  exact ⟨hx.1, fun k ↦ (hx.2 k).trans hrq⟩

lemma linearThresholdRegion_subset
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (r : ℝ) :
    linearThresholdRegion B ℓ r ⊆ B := by
  exact Set.inter_subset_left

lemma linearThresholdRegion_isBounded
    {B : Set (I → ℝ)} (hB : Bornology.IsBounded B)
    (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (r : ℝ) :
    Bornology.IsBounded (linearThresholdRegion B ℓ r) :=
  hB.subset (linearThresholdRegion_subset B ℓ r)

lemma linearThresholdRegion_measurableSet
    {B : Set (I → ℝ)} (hB : MeasurableSet B)
    (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (r : ℝ) :
    MeasurableSet (linearThresholdRegion B ℓ r) := by
  rw [linearThresholdRegion]
  exact hB.inter (MeasurableSet.iInter fun k ↦
    measurableSet_le (ℓ k).measurable measurable_const)

lemma linearThresholdRegion_convex
    {B : Set (I → ℝ)} (hB : Convex ℝ B)
    (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (r : ℝ) :
    Convex ℝ (linearThresholdRegion B ℓ r) := by
  rw [linearThresholdRegion]
  exact hB.inter (convex_iInter fun k ↦
    convex_halfSpace_le (ℓ k).toLinearMap.isLinear r)

end ThresholdRegion

section ThresholdCollars

variable {K : Type*} [Fintype K]

lemma iInter_linearThresholdRegion_add_inv_eq
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    (⋂ n : ℕ, linearThresholdRegion B ℓ
      (t + ((n : ℝ) + 1)⁻¹)) = linearThresholdRegion B ℓ t := by
  ext x
  have htend : Tendsto (fun n : ℕ ↦ t + ((n : ℝ) + 1)⁻¹)
      atTop (nhds t) := by
    simpa only [one_div, add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  constructor
  · intro hx
    rw [Set.mem_iInter] at hx
    have hx0 := hx 0
    rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter] at hx0 ⊢
    refine ⟨hx0.1, fun k ↦ ?_⟩
    apply ge_of_tendsto htend
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := hx n
      rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter] at hn
      exact hn.2 k
  · intro hx
    rw [Set.mem_iInter]
    intro n
    exact (linearThresholdRegion_mono B ℓ)
      (le_add_of_nonneg_right (by positivity)) hx

lemma iUnion_linearThresholdRegion_sub_inv_eq
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    (⋃ n : ℕ, linearThresholdRegion B ℓ
      (t - ((n : ℝ) + 1)⁻¹)) = B ∩ ⋂ k, {x | ℓ k x < t} := by
  ext x
  have htend : Tendsto (fun n : ℕ ↦ t - ((n : ℝ) + 1)⁻¹)
      atTop (nhds t) := by
    simpa only [one_div, sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter] at hn
    rw [Set.mem_inter_iff, Set.mem_iInter]
    refine ⟨hn.1, fun k ↦ ?_⟩
    change ℓ k x < t
    exact (hn.2 k).trans_lt (by
      linarith [show 0 < ((n : ℝ) + 1)⁻¹ by positivity])
  · intro hx
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    have heach : ∀ k, ∀ᶠ n : ℕ in atTop,
        ℓ k x < t - ((n : ℝ) + 1)⁻¹ := fun k ↦
      htend.eventually_const_lt (hx.2 k)
    have hall : ∀ᶠ n : ℕ in atTop, ∀ k,
        ℓ k x < t - ((n : ℝ) + 1)⁻¹ :=
      Filter.eventually_all.2 heach
    obtain ⟨n, hn⟩ := hall.exists
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨hx.1, fun k ↦ (hn k).le⟩

/-- The inner and outer continuous-linear collars have the same limiting
integral.  The only possible discrepancy for the inner collars lies on one
of the finitely many threshold hyperplanes. -/
theorem linearThresholdRegion_integral_collars
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ)
    (F : (I → ℝ) → ℝ) (t : ℝ)
    (hBbounded : Bornology.IsBounded B) (hBmeas : MeasurableSet B)
    (hFcont : Continuous F)
    (hlevel : ∀ k, volume {x | ℓ k x = t} = 0) :
    Tendsto
        (fun n : ℕ ↦ ∫ x in linearThresholdRegion B ℓ
          (t - ((n : ℝ) + 1)⁻¹), F x)
        atTop (nhds (∫ x in linearThresholdRegion B ℓ t, F x)) ∧
      Tendsto
        (fun n : ℕ ↦ ∫ x in linearThresholdRegion B ℓ
          (t + ((n : ℝ) + 1)⁻¹), F x)
        atTop (nhds (∫ x in linearThresholdRegion B ℓ t, F x)) := by
  have hFIclosure : IntegrableOn F (closure B) volume :=
    hFcont.continuousOn.integrableOn_compact hBbounded.isCompact_closure
  have hFI : IntegrableOn F B volume :=
    hFIclosure.mono_set subset_closure
  have hlowerThreshold : Monotone
      (fun n : ℕ ↦ t - ((n : ℝ) + 1)⁻¹) := by
    intro a b hab
    have habCast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have habR : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by linarith
    have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) habR
    linarith
  have hupperThreshold : Antitone
      (fun n : ℕ ↦ t + ((n : ℝ) + 1)⁻¹) := by
    intro a b hab
    have habCast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have habR : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by linarith
    have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) habR
    linarith
  have hlowerMono : Monotone (fun n : ℕ ↦
      linearThresholdRegion B ℓ (t - ((n : ℝ) + 1)⁻¹)) :=
    (linearThresholdRegion_mono B ℓ).comp hlowerThreshold
  have hupperAnti : Antitone (fun n : ℕ ↦
      linearThresholdRegion B ℓ (t + ((n : ℝ) + 1)⁻¹)) :=
    (linearThresholdRegion_mono B ℓ).comp_antitone hupperThreshold
  have hmeasLower : ∀ n : ℕ, MeasurableSet
      (linearThresholdRegion B ℓ (t - ((n : ℝ) + 1)⁻¹)) :=
    fun n ↦ linearThresholdRegion_measurableSet hBmeas ℓ _
  have hmeasUpper : ∀ n : ℕ, MeasurableSet
      (linearThresholdRegion B ℓ (t + ((n : ℝ) + 1)⁻¹)) :=
    fun n ↦ linearThresholdRegion_measurableSet hBmeas ℓ _
  have hunionSubset : (⋃ n : ℕ,
      linearThresholdRegion B ℓ (t - ((n : ℝ) + 1)⁻¹)) ⊆ B := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact linearThresholdRegion_subset B ℓ _ hn
  have hinnerCoreSubset :
      B ∩ (⋂ k, {x | ℓ k x < t}) ⊆ linearThresholdRegion B ℓ t := by
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
    rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter]
    refine ⟨hx.1, fun k ↦ ?_⟩
    change ℓ k x ≤ t
    exact (hx.2 k).le
  have hdiffSubset :
      linearThresholdRegion B ℓ t \ (B ∩ (⋂ k, {x | ℓ k x < t})) ⊆
        ⋃ k, {x | ℓ k x = t} := by
    intro x hx
    rw [Set.mem_sdiff] at hx
    have hxt := hx.1
    rw [linearThresholdRegion, Set.mem_inter_iff, Set.mem_iInter] at hxt
    have hnot : ¬ ∀ k, ℓ k x < t := by
      intro hall
      apply hx.2
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact ⟨hxt.1, hall⟩
    push Not at hnot
    obtain ⟨k, hk⟩ := hnot
    rw [Set.mem_iUnion]
    refine ⟨k, ?_⟩
    change ℓ k x = t
    exact le_antisymm (hxt.2 k) hk
  have hdiffZero : volume
      (linearThresholdRegion B ℓ t \ (B ∩ (⋂ k, {x | ℓ k x < t}))) = 0 :=
    measure_mono_null hdiffSubset (measure_iUnion_null hlevel)
  have hcoreAE :
      ((B ∩ (⋂ k : K, {x | ℓ k x < t})) : Set (I → ℝ)) =ᵐ[volume]
        linearThresholdRegion B ℓ t := by
    rw [ae_eq_set]
    refine ⟨?_, hdiffZero⟩
    rw [Set.sdiff_eq_empty.mpr hinnerCoreSubset, measure_empty]
  constructor
  · have h := tendsto_setIntegral_of_monotone hmeasLower hlowerMono
      (hFI.mono_set hunionSubset)
    rw [iUnion_linearThresholdRegion_sub_inv_eq] at h
    convert h using 1
    exact congrArg nhds (setIntegral_congr_set (f := F) hcoreAE).symm
  · have h := tendsto_setIntegral_of_antitone hmeasUpper hupperAnti
      ⟨0, hFI.mono_set (linearThresholdRegion_subset B ℓ _)⟩
    rw [iInter_linearThresholdRegion_add_inv_eq] at h
    exact h

end ThresholdCollars

/-- A two-parameter squeeze lemma.  For every collar index `k`, the moving
sequence is eventually trapped between two sequences having fixed limits;
the two fixed limits themselves converge to the desired value as the collar
shrinks. -/
theorem tendsto_diagonal_of_eventually_squeeze
    {a b : ℕ → ℕ → ℝ} {A B : ℕ → ℝ}
    {f : ℕ → ℝ} {L : ℝ}
    (ha : ∀ k, Tendsto (a k) atTop (nhds (A k)))
    (hb : ∀ k, Tendsto (b k) atTop (nhds (B k)))
    (hA : Tendsto A atTop (nhds L))
    (hB : Tendsto B atTop (nhds L))
    (hsqueeze : ∀ k, ∀ᶠ n in atTop, a k n ≤ f n ∧ f n ≤ b k n) :
    Tendsto f atTop (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  have hkA : ∀ᶠ k in atTop, dist (A k) L < ε / 3 :=
    (Metric.tendsto_nhds.1 hA) (ε / 3) hthird
  have hkB : ∀ᶠ k in atTop, dist (B k) L < ε / 3 :=
    (Metric.tendsto_nhds.1 hB) (ε / 3) hthird
  obtain ⟨k, hkA, hkB⟩ := (hkA.and hkB).exists
  have hna : ∀ᶠ n in atTop, dist (a k n) (A k) < ε / 3 :=
    (Metric.tendsto_nhds.1 (ha k)) (ε / 3) hthird
  have hnb : ∀ᶠ n in atTop, dist (b k n) (B k) < ε / 3 :=
    (Metric.tendsto_nhds.1 (hb k)) (ε / 3) hthird
  filter_upwards [hna, hnb, hsqueeze k] with n hna hnb hn
  rw [Real.dist_eq] at hna hnb hkA hkB ⊢
  rw [abs_lt] at hna hnb hkA hkB ⊢
  constructor <;> linarith

/-- Moving-domain lattice Riemann sums converge once fixed collars converge
to the target integral.  Convexity supplies the null-frontier hypothesis for
each fixed collar; monotonicity and nonnegativity supply the squeeze. -/
theorem tendsto_latticeRiemannSum_moving_of_collars
    (s : ℝ → Set (I → ℝ)) (F : (I → ℝ) → ℝ)
    (u : ℕ → ℝ) (t : ℝ)
    (hFcont : Continuous F) (hFnonneg : ∀ x, 0 ≤ F x)
    (hsmono : Monotone s)
    (hsbounded : ∀ r, Bornology.IsBounded (s r))
    (hsmeas : ∀ r, MeasurableSet (s r))
    (hsconvex : ∀ r, Convex ℝ (s r))
    (hu : Tendsto u atTop (nhds t))
    (hlower : Tendsto
      (fun k : ℕ ↦ ∫ x in s (t - ((k : ℝ) + 1)⁻¹), F x)
      atTop (nhds (∫ x in s t, F x)))
    (hupper : Tendsto
      (fun k : ℕ ↦ ∫ x in s (t + ((k : ℝ) + 1)⁻¹), F x)
      atTop (nhds (∫ x in s t, F x))) :
    Tendsto (fun n ↦ latticeRiemannSum (s (u n)) F n)
      atTop (nhds (∫ x in s t, F x)) := by
  apply tendsto_diagonal_of_eventually_squeeze
    (a := fun k n ↦ latticeRiemannSum (s (t - ((k : ℝ) + 1)⁻¹)) F n)
    (b := fun k n ↦ latticeRiemannSum (s (t + ((k : ℝ) + 1)⁻¹)) F n)
    (A := fun k ↦ ∫ x in s (t - ((k : ℝ) + 1)⁻¹), F x)
    (B := fun k ↦ ∫ x in s (t + ((k : ℝ) + 1)⁻¹), F x)
  · intro k
    exact tendsto_tsum_div_pow_atTop_integral
      (s (t - ((k : ℝ) + 1)⁻¹)) F hFcont
      (hsbounded _) (hsmeas _) ((hsconvex _).addHaar_frontier volume)
  · intro k
    exact tendsto_tsum_div_pow_atTop_integral
      (s (t + ((k : ℝ) + 1)⁻¹)) F hFcont
      (hsbounded _) (hsmeas _) ((hsconvex _).addHaar_frontier volume)
  · exact hlower
  · exact hupper
  · intro k
    have hgap : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
    have hclose : ∀ᶠ n in atTop, dist (u n) t < ((k : ℝ) + 1)⁻¹ :=
      (Metric.tendsto_nhds.1 hu) _ hgap
    filter_upwards [hclose, eventually_gt_atTop 0] with n hnclose hn
    rw [Real.dist_eq, abs_lt] at hnclose
    constructor
    · exact latticeRiemannSum_mono (hsbounded _) (hsbounded _)
        (hsmono (by linarith [hnclose.1])) hFnonneg hn
    · exact latticeRiemannSum_mono (hsbounded _) (hsbounded _)
        (hsmono (by linarith [hnclose.2])) hFnonneg hn

/-- Direct moving-threshold lattice/Riemann-sum theorem for a bounded convex
base cut out by finitely many continuous linear inequalities.  Nullity of the
active level hyperplanes is precisely the no-jump hypothesis needed for the
inner collars. -/
theorem tendsto_latticeRiemannSum_linearThresholdRegion
    {K : Type*} [Fintype K]
    (B : Set (I → ℝ)) (ℓ : K → (I → ℝ) →L[ℝ] ℝ)
    (F : (I → ℝ) → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (hBbounded : Bornology.IsBounded B) (hBmeas : MeasurableSet B)
    (hBconvex : Convex ℝ B)
    (hFcont : Continuous F) (hFnonneg : ∀ x, 0 ≤ F x)
    (hu : Tendsto u atTop (nhds t))
    (hlevel : ∀ k, volume {x | ℓ k x = t} = 0) :
    Tendsto
      (fun n ↦ latticeRiemannSum (linearThresholdRegion B ℓ (u n)) F n)
      atTop (nhds (∫ x in linearThresholdRegion B ℓ t, F x)) := by
  obtain ⟨hlower, hupper⟩ := linearThresholdRegion_integral_collars
    B ℓ F t hBbounded hBmeas hFcont hlevel
  exact tendsto_latticeRiemannSum_moving_of_collars
    (linearThresholdRegion B ℓ) F u t hFcont hFnonneg
    (linearThresholdRegion_mono B ℓ)
    (fun r ↦ linearThresholdRegion_isBounded hBbounded ℓ r)
    (fun r ↦ linearThresholdRegion_measurableSet hBmeas ℓ r)
    (fun r ↦ linearThresholdRegion_convex hBconvex ℓ r)
    hu hlower hupper

end MovingThreshold

end VisibleLattice

/-! ### The explicit all-parameter BCZ formula

The following definitions transcribe the finite integral formula of
Xiong--Zaharescu and Boca.  They are kept independent of the elementary
sparse-range computation above: proving that `S` converges to this expression
requires the visible-lattice equidistribution theorem described in
`tex/1001.tex`.
-/

/-- The Farey triangle used by the Boca--Cobeli--Zaharescu return map. -/
def fareyTriangle : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 ∧ 1 < p.1 + p.2}

/-- The integer index of the Boca--Cobeli--Zaharescu map. -/
def bczIndex (p : ℝ × ℝ) : ℤ :=
  ⌊(1 + p.1) / p.2⌋

/-- The Boca--Cobeli--Zaharescu map on the Farey triangle. -/
def bczMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, (bczIndex p : ℝ) * p.2 - p.1)

/-- On the normalized denominator pair of three consecutive Farey
fractions, `bczMap` advances to the next normalized pair. -/
theorem Farey.bczMap_normalized_pair {Q : ℕ}
    {p0 p1 p2 : Farey.Fraction Q} (hQ : 0 < Q)
    (h01 : Farey.Consecutive p0 p1) (h12 : Farey.Consecutive p1 p2) :
    bczMap ((p0.den : ℝ) / Q, (p1.den : ℝ) / Q) =
      ((p1.den : ℝ) / Q, (p2.den : ℝ) / Q) := by
  have hindex := Farey.triple_index_floor hQ h01 h12
  apply Prod.ext
  · rfl
  · change
      (bczIndex ((p0.den : ℝ) / Q, (p1.den : ℝ) / Q) : ℝ) *
          ((p1.den : ℝ) / Q) - (p0.den : ℝ) / Q =
        (p2.den : ℝ) / Q
    rw [bczIndex, hindex]
    exact (Farey.triple_normalized_denominator_step hQ h01 h12).symm

/-- Iterating the BCZ map follows any infinite chain of consecutive Farey
fractions, on normalized denominator pairs. -/
theorem Farey.bcz_iterate_normalized_chain {Q j : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    (bczMap^[j]) (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (((q j).den : ℝ) / Q, ((q (j + 1)).den : ℝ) / Q) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      exact Farey.bczMap_normalized_pair hQ (hchain j) (hchain (j + 1))

/-- A BCZ orbit follows a finite Farey chain while a full following pair
remains inside the stated horizon. -/
theorem Farey.bcz_iterate_normalized_chain_lt {Q j m : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q) (hjm : j < m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    (bczMap^[j]) (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (((q j).den : ℝ) / Q, ((q (j + 1)).den : ℝ) / Q) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact Farey.bczMap_normalized_pair hQ
        (hchain j (by omega)) (hchain (j + 1) (by omega))

/-- The normalized denominator at offset `j` along a BCZ orbit. -/
def normalizedDenominator (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  (bczMap^[j] p).1

theorem Farey.normalizedDenominator_chain {Q j : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedDenominator j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      ((q j).den : ℝ) / Q := by
  exact congrArg Prod.fst (Farey.bcz_iterate_normalized_chain hQ q hchain)

/-- Every denominator through the closed horizon agrees with the first
coordinate of the corresponding normalized BCZ iterate. -/
theorem Farey.normalizedDenominator_chain_le {Q j m : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q) (hjm : j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedDenominator j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      ((q j).den : ℝ) / Q := by
  cases j with
  | zero => rfl
  | succ j =>
      rw [normalizedDenominator, Function.iterate_succ_apply',
        Farey.bcz_iterate_normalized_chain_lt hQ q (by omega) hchain]
      rfl

/-- The normalized displacement between the centers at offsets `0` and
`j`. -/
def normalizedGap (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range j,
    1 / (normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p)

/-- The normalized BCZ displacement is `Q²` times the actual displacement
between the corresponding Farey centers. -/
theorem Farey.normalizedGap_chain {Q j : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedGap j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * ((q j).realValue - (q 0).realValue) := by
  rw [Farey.consecutive_chain_center_gap q hchain, normalizedGap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Farey.normalizedDenominator_chain hQ q hchain,
    Farey.normalizedDenominator_chain hQ q hchain]
  field_simp [hQ.ne', (q i).den_pos.ne', (q (i + 1)).den_pos.ne']

/-- Finite-horizon normalized center-gap identity. -/
theorem Farey.normalizedGap_chain_le {Q j m : ℕ} (hQ : 0 < Q)
    (q : ℕ → Farey.Fraction Q) (hjm : j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedGap j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * ((q j).realValue - (q 0).realValue) := by
  rw [Farey.consecutive_chain_center_gap_le q hjm hchain,
    normalizedGap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i < j := Finset.mem_range.mp hi
  rw [Farey.normalizedDenominator_chain_le hQ q (by omega) hchain,
    Farey.normalizedDenominator_chain_le hQ q (by omega) hchain]
  field_simp [hQ.ne', (q i).den_pos.ne', (q (i + 1)).den_pos.ne']

/-- The discontinuous BCZ index is Borel measurable. -/
lemma measurable_bczIndex : Measurable bczIndex := by
  exact Int.measurable_floor.comp
    ((measurable_const.add measurable_fst).div measurable_snd)

/-- The BCZ return map is Borel measurable. -/
lemma measurable_bczMap : Measurable bczMap := by
  refine measurable_snd.prodMk ?_
  exact (((measurable_of_countable fun z : ℤ ↦ (z : ℝ)).comp measurable_bczIndex).mul
    measurable_snd).sub measurable_fst

/-- Every normalized denominator coordinate along a finite BCZ orbit is
Borel measurable. -/
lemma measurable_normalizedDenominator (j : ℕ) :
    Measurable (normalizedDenominator j) := by
  exact measurable_fst.comp (measurable_bczMap.iterate j)

/-- The finite normalized center displacement is Borel measurable. -/
lemma measurable_normalizedGap (j : ℕ) : Measurable (normalizedGap j) := by
  apply Finset.measurable_sum
  intro ℓ hℓ
  exact measurable_const.div
    ((measurable_normalizedDenominator ℓ).mul
      (measurable_normalizedDenominator (ℓ + 1)))

def normalizedUpperEndpoint (A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  normalizedGap j p + A / normalizedDenominator j p ^ 2

def normalizedLowerEndpoint (A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  normalizedGap j p - A / normalizedDenominator j p ^ 2

theorem Farey.normalizedUpperEndpoint_chain {Q j : ℕ} (hQ : 0 < Q) (A : ℝ)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedUpperEndpoint A j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualUpperEndpoint A q j := by
  rw [normalizedUpperEndpoint, Farey.actualUpperEndpoint,
    Farey.normalizedGap_chain hQ q hchain,
    Farey.normalizedDenominator_chain hQ q hchain]
  field_simp [hQ.ne', (q j).den_pos.ne']

theorem Farey.normalizedLowerEndpoint_chain {Q j : ℕ} (hQ : 0 < Q) (A : ℝ)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedLowerEndpoint A j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualLowerEndpoint A q j := by
  rw [normalizedLowerEndpoint, Farey.actualLowerEndpoint,
    Farey.normalizedGap_chain hQ q hchain,
    Farey.normalizedDenominator_chain hQ q hchain]
  field_simp [hQ.ne', (q j).den_pos.ne']

theorem Farey.normalizedUpperEndpoint_chain_le {Q j m : ℕ}
    (hQ : 0 < Q) (A : ℝ) (q : ℕ → Farey.Fraction Q) (hjm : j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedUpperEndpoint A j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualUpperEndpoint A q j := by
  rw [normalizedUpperEndpoint, Farey.actualUpperEndpoint,
    Farey.normalizedGap_chain_le hQ q hjm hchain,
    Farey.normalizedDenominator_chain_le hQ q hjm hchain]
  field_simp [hQ.ne', (q j).den_pos.ne']

theorem Farey.normalizedLowerEndpoint_chain_le {Q j m : ℕ}
    (hQ : 0 < Q) (A : ℝ) (q : ℕ → Farey.Fraction Q) (hjm : j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    normalizedLowerEndpoint A j
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualLowerEndpoint A q j := by
  rw [normalizedLowerEndpoint, Farey.actualLowerEndpoint,
    Farey.normalizedGap_chain_le hQ q hjm hchain,
    Farey.normalizedDenominator_chain_le hQ q hjm hchain]
  field_simp [hQ.ne', (q j).den_pos.ne']

lemma measurable_normalizedUpperEndpoint (A : ℝ) (j : ℕ) :
    Measurable (normalizedUpperEndpoint A j) := by
  exact (measurable_normalizedGap j).add
    (measurable_const.div ((measurable_normalizedDenominator j).pow_const 2))

lemma measurable_normalizedLowerEndpoint (A : ℝ) (j : ℕ) :
    Measurable (normalizedLowerEndpoint A j) := by
  exact (measurable_normalizedGap j).sub
    (measurable_const.div ((measurable_normalizedDenominator j).pow_const 2))

lemma measurable_finset_image_min'
    {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x ↦ (s.image (fun i ↦ f i x)).min' (hs.image _)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | @cons a s ha ih =>
      by_cases hs' : s.Nonempty
      · have hfa : Measurable (f a) := hf a (by simp)
        have hfs : ∀ i ∈ s, Measurable (f i) := by
          intro i hi
          exact hf i (by simp [hi])
        have hrest := ih hs' hfs
        simpa only [Finset.cons_eq_insert, Finset.image_insert,
          Finset.min'_insert _ _ (hs'.image _)] using hfa.min hrest
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf a (by simp)

lemma measurable_finset_image_max'
    {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x ↦ (s.image (fun i ↦ f i x)).max' (hs.image _)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | @cons a s ha ih =>
      by_cases hs' : s.Nonempty
      · have hfa : Measurable (f a) := hf a (by simp)
        have hfs : ∀ i ∈ s, Measurable (f i) := by
          intro i hi
          exact hf i (by simp [hi])
        have hrest := ih hs' hfs
        simpa only [Finset.cons_eq_insert, Finset.image_insert,
          Finset.max'_insert _ _ (hs'.image _)] using hfa.max hrest
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf a (by simp)

/-- The normalized length of the intersection indexed by a nonempty finite
set `J` of Farey offsets. -/
def finiteOverlapLength (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (p : ℝ × ℝ) : ℝ :=
  max 0
    ((J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
      (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _))

/-- Along a Farey chain, the normalized overlap length is exactly `Q²`
times the corresponding unscaled interval-intersection length. -/
theorem Farey.finiteOverlapLength_chain {Q : ℕ} (hQ : 0 < Q) (A : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualOverlapLength A J hJ q := by
  let c : ℝ := (Q : ℝ) ^ 2
  let p : ℝ × ℝ := (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hupper (j : ℕ) :
      normalizedUpperEndpoint A j p =
        c * Farey.actualUpperEndpoint A q j := by
    exact Farey.normalizedUpperEndpoint_chain hQ A q hchain
  have hlower (j : ℕ) :
      normalizedLowerEndpoint A j p =
        c * Farey.actualLowerEndpoint A q j := by
    exact Farey.normalizedLowerEndpoint_chain hQ A q hchain
  have himageUpper :
      J.image (fun j ↦ normalizedUpperEndpoint A j p) =
        (J.image (Farey.actualUpperEndpoint A q)).image
          (fun x : ℝ ↦ c * x) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j hj
    exact hupper j
  have himageLower :
      J.image (fun j ↦ normalizedLowerEndpoint A j p) =
        (J.image (Farey.actualLowerEndpoint A q)).image
          (fun x : ℝ ↦ c * x) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j hj
    exact hlower j
  have hmono : Monotone (fun x : ℝ ↦ c * x) := fun _ _ h ↦
    mul_le_mul_of_nonneg_left h hc
  have hmin :
      (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) =
        c * (J.image (Farey.actualUpperEndpoint A q)).min' (hJ.image _) := by
    simpa only [himageUpper] using
      Finset.min'_image hmono (J.image (Farey.actualUpperEndpoint A q))
        ((hJ.image _).image (fun x : ℝ ↦ c * x))
  have hmax :
      (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) =
        c * (J.image (Farey.actualLowerEndpoint A q)).max' (hJ.image _) := by
    simpa only [himageLower] using
      Finset.max'_image hmono (J.image (Farey.actualLowerEndpoint A q))
        ((hJ.image _).image (fun x : ℝ ↦ c * x))
  rw [finiteOverlapLength, Farey.actualOverlapLength, hmin, hmax]
  let U := (J.image (Farey.actualUpperEndpoint A q)).min' (hJ.image _)
  let L := (J.image (Farey.actualLowerEndpoint A q)).max' (hJ.image _)
  change max 0 (c * U - c * L) = c * max 0 (U - L)
  rw [← mul_sub]
  by_cases hUL : 0 ≤ U - L
  · rw [max_eq_right hUL, max_eq_right (mul_nonneg hc hUL)]
  · have hUL' : U - L ≤ 0 := le_of_not_ge hUL
    rw [max_eq_left hUL',
      max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc hUL')]
    simp

theorem Farey.actualOverlapLength_eq_inv_sq_mul_finiteOverlapLength
    {Q : ℕ} (hQ : 0 < Q) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    Farey.actualOverlapLength A J hJ q =
      ((Q : ℝ) ^ 2)⁻¹ * finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) := by
  rw [Farey.finiteOverlapLength_chain hQ A J hJ q hchain]
  field_simp [hQ.ne']

/-- Exact center/BCZ identity for the Lebesgue measure of the intersection
of a finite family of Farey approximation intervals. -/
theorem Farey.volume_real_actualInterval_biInter_eq_inv_sq_mul_finiteOverlapLength
    {Q : ℕ} (hQ : 0 < Q) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Farey.Fraction Q)
    (hchain : ∀ i, Farey.Consecutive (q i) (q (i + 1))) :
    (volume : Measure ℝ).real
        (⋂ j ∈ J, Farey.actualInterval A q j) =
      ((Q : ℝ) ^ 2)⁻¹ * finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) := by
  rw [Farey.volume_real_actualInterval_biInter A J hJ q,
    Farey.actualOverlapLength_eq_inv_sq_mul_finiteOverlapLength
      hQ A J hJ q hchain]

/-- Finite-horizon exact overlap scaling. -/
theorem Farey.finiteOverlapLength_chain_le {Q m : ℕ} (hQ : 0 < Q) (A : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) (q : ℕ → Farey.Fraction Q)
    (hJm : ∀ j ∈ J, j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) =
      (Q : ℝ) ^ 2 * Farey.actualOverlapLength A J hJ q := by
  let c : ℝ := (Q : ℝ) ^ 2
  let p : ℝ × ℝ := (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hupper (j : ℕ) (hj : j ∈ J) :
      normalizedUpperEndpoint A j p =
        c * Farey.actualUpperEndpoint A q j := by
    exact Farey.normalizedUpperEndpoint_chain_le hQ A q (hJm j hj) hchain
  have hlower (j : ℕ) (hj : j ∈ J) :
      normalizedLowerEndpoint A j p =
        c * Farey.actualLowerEndpoint A q j := by
    exact Farey.normalizedLowerEndpoint_chain_le hQ A q (hJm j hj) hchain
  have himageUpper :
      J.image (fun j ↦ normalizedUpperEndpoint A j p) =
        (J.image (Farey.actualUpperEndpoint A q)).image
          (fun x : ℝ ↦ c * x) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j hj
    exact hupper j hj
  have himageLower :
      J.image (fun j ↦ normalizedLowerEndpoint A j p) =
        (J.image (Farey.actualLowerEndpoint A q)).image
          (fun x : ℝ ↦ c * x) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j hj
    exact hlower j hj
  have hmono : Monotone (fun x : ℝ ↦ c * x) := fun _ _ h ↦
    mul_le_mul_of_nonneg_left h hc
  have hmin :
      (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) =
        c * (J.image (Farey.actualUpperEndpoint A q)).min' (hJ.image _) := by
    simpa only [himageUpper] using
      Finset.min'_image hmono (J.image (Farey.actualUpperEndpoint A q))
        ((hJ.image _).image (fun x : ℝ ↦ c * x))
  have hmax :
      (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) =
        c * (J.image (Farey.actualLowerEndpoint A q)).max' (hJ.image _) := by
    simpa only [himageLower] using
      Finset.max'_image hmono (J.image (Farey.actualLowerEndpoint A q))
        ((hJ.image _).image (fun x : ℝ ↦ c * x))
  rw [finiteOverlapLength, Farey.actualOverlapLength, hmin, hmax]
  let U := (J.image (Farey.actualUpperEndpoint A q)).min' (hJ.image _)
  let L := (J.image (Farey.actualLowerEndpoint A q)).max' (hJ.image _)
  change max 0 (c * U - c * L) = c * max 0 (U - L)
  rw [← mul_sub]
  by_cases hUL : 0 ≤ U - L
  · rw [max_eq_right hUL, max_eq_right (mul_nonneg hc hUL)]
  · have hUL' : U - L ≤ 0 := le_of_not_ge hUL
    rw [max_eq_left hUL',
      max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc hUL')]
    simp

theorem Farey.actualOverlapLength_eq_inv_sq_mul_finiteOverlapLength_le
    {Q m : ℕ} (hQ : 0 < Q) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Farey.Fraction Q) (hJm : ∀ j ∈ J, j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    Farey.actualOverlapLength A J hJ q =
      ((Q : ℝ) ^ 2)⁻¹ * finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) := by
  rw [Farey.finiteOverlapLength_chain_le hQ A J hJ q hJm hchain]
  field_simp [hQ.ne']

theorem Farey.volume_real_actualInterval_biInter_eq_inv_sq_mul_finiteOverlapLength_le
    {Q m : ℕ} (hQ : 0 < Q) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Farey.Fraction Q) (hJm : ∀ j ∈ J, j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    (volume : Measure ℝ).real
        (⋂ j ∈ J, Farey.actualInterval A q j) =
      ((Q : ℝ) ^ 2)⁻¹ * finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) := by
  rw [Farey.volume_real_actualInterval_biInter A J hJ q,
    Farey.actualOverlapLength_eq_inv_sq_mul_finiteOverlapLength_le
      hQ A J hJ q hJm hchain]

/-- Exact finite-horizon BCZ formula for the original, untranslated
approximation intervals centered at the Farey fractions. -/
theorem Farey.volume_real_approximationInterval_biInter_eq_inv_sq_mul_finiteOverlapLength_le
    {Q m : ℕ} (hQ : 0 < Q) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (q : ℕ → Farey.Fraction Q) (hJm : ∀ j ∈ J, j ≤ m)
    (hchain : ∀ i < m, Farey.Consecutive (q i) (q (i + 1))) :
    (volume : Measure ℝ).real
        (⋂ j ∈ J,
          approximationInterval A ((q j).num : ℤ) (q j).den) =
      ((Q : ℝ) ^ 2)⁻¹ * finiteOverlapLength A J hJ
        (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q) := by
  rw [Farey.volume_real_approximationInterval_biInter_eq_actualOverlapLength A J hJ q,
    Farey.actualOverlapLength_eq_inv_sq_mul_finiteOverlapLength_le
      hQ A J hJ q hJm hchain]

lemma measurable_finiteOverlapLength (A : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) : Measurable (finiteOverlapLength A J hJ) := by
  exact measurable_const.max
    ((measurable_finset_image_min' J hJ (normalizedUpperEndpoint A)
      fun j _ ↦ measurable_normalizedUpperEndpoint A j).sub
    (measurable_finset_image_max' J hJ (normalizedLowerEndpoint A)
      fun j _ ↦ measurable_normalizedLowerEndpoint A j))

/-- The overlap length after imposing the denominator cutoff `L_j ≥ 1/c`
at every selected offset. -/
def cutoffOverlapIntegrand (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (p : ℝ × ℝ) : ℝ :=
  if ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p then
    finiteOverlapLength A J hJ p
  else 0

lemma measurable_cutoffOverlapIntegrand (A c : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) : Measurable (cutoffOverlapIntegrand A c J hJ) := by
  have hp : MeasurableSet
      {p : ℝ × ℝ | ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p} := by
    rw [show {p : ℝ × ℝ | ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p} =
        ⋂ j ∈ J, {p : ℝ × ℝ | 1 / c ≤ normalizedDenominator j p} by
      ext p
      simp]
    exact J.measurableSet_biInter (fun j _ ↦
      measurableSet_le
        (measurable_const : Measurable (fun _ : ℝ × ℝ ↦ (1 / c : ℝ)))
        (measurable_normalizedDenominator j))
  exact Measurable.ite hp (measurable_finiteOverlapLength A J hJ) measurable_const

lemma finiteOverlapLength_nonneg (A : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) (p : ℝ × ℝ) :
    0 ≤ finiteOverlapLength A J hJ p := by
  exact le_max_left _ _

lemma cutoffOverlapIntegrand_nonneg (A c : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) (p : ℝ × ℝ) :
    0 ≤ cutoffOverlapIntegrand A c J hJ p := by
  simp only [cutoffOverlapIntegrand]
  split_ifs
  · exact finiteOverlapLength_nonneg A J hJ p
  · exact le_rfl

lemma cutoffOverlapIntegrand_le
    {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle) :
    cutoffOverlapIntegrand A c J hJ p ≤ 2 * A * c ^ 2 := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hbound_nonneg : 0 ≤ 2 * A * c ^ 2 := by positivity
  rw [cutoffOverlapIntegrand]
  split_ifs with hcut
  · have hupperMem : normalizedUpperEndpoint A 0 p ∈
        J.image (fun j ↦ normalizedUpperEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
    have hlowerMem : normalizedLowerEndpoint A 0 p ∈
        J.image (fun j ↦ normalizedLowerEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
    have hmin := Finset.min'_le
      (J.image (fun j ↦ normalizedUpperEndpoint A j p))
      (normalizedUpperEndpoint A 0 p) hupperMem
    have hmax := Finset.le_max'
      (J.image (fun j ↦ normalizedLowerEndpoint A j p))
      (normalizedLowerEndpoint A 0 p) hlowerMem
    have hwidth :
        normalizedUpperEndpoint A 0 p - normalizedLowerEndpoint A 0 p =
          2 * A / p.1 ^ 2 := by
      simp [normalizedUpperEndpoint, normalizedLowerEndpoint, normalizedGap]
      simp [normalizedDenominator]
      ring
    have hdiff :
        (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
            (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) ≤
          2 * A / p.1 ^ 2 := by
      rw [← hwidth]
      linarith
    have hcutzero := hcut 0 hzero
    rw [show normalizedDenominator 0 p = p.1 by simp [normalizedDenominator]] at hcutzero
    rw [div_le_iff₀ hcpos] at hcutzero
    have hsq : (1 : ℝ) * 1 ≤ (p.1 * c) * (p.1 * c) :=
      mul_self_le_mul_self (by norm_num) hcutzero
    have hp1pos : 0 < p.1 := hp.1
    have hp1sqpos : 0 < p.1 ^ 2 := sq_pos_of_pos hp1pos
    have hinv : 1 / p.1 ^ 2 ≤ c ^ 2 := by
      rw [div_le_iff₀ hp1sqpos]
      nlinarith
    have hradius : 2 * A / p.1 ^ 2 ≤ 2 * A * c ^ 2 := by
      calc
        2 * A / p.1 ^ 2 = (2 * A) * (1 / p.1 ^ 2) := by ring
        _ ≤ (2 * A) * c ^ 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 2 * A * c ^ 2 := by ring
    rw [finiteOverlapLength]
    exact max_le hbound_nonneg (hdiff.trans hradius)
  · exact hbound_nonneg

lemma measurableSet_fareyTriangle : MeasurableSet fareyTriangle := by
  unfold fareyTriangle
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd measurable_const).inter
          (measurableSet_lt measurable_const
            (measurable_fst.add measurable_snd)))))

lemma measure_fareyTriangle_lt_top : volume fareyTriangle < ∞ := by
  have hsubset : fareyTriangle ⊆ Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
    rintro p hp
    exact ⟨⟨hp.1.le, hp.2.2.1.le⟩, ⟨hp.2.1, hp.2.2.2.1⟩⟩
  exact (measure_mono hsubset).trans_lt isCompact_Icc.measure_lt_top

lemma integrableOn_cutoffOverlapIntegrand
    {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J) :
    IntegrableOn (cutoffOverlapIntegrand A c J hJ) fareyTriangle := by
  refine Measure.integrableOn_of_bounded (M := 2 * A * c ^ 2)
    measure_fareyTriangle_lt_top.ne
    (measurable_cutoffOverlapIntegrand A c J hJ).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_fareyTriangle ?_
  intro p hp
  rw [Real.norm_of_nonneg (cutoffOverlapIntegrand_nonneg A c J hJ p)]
  exact cutoffOverlapIntegrand_le hA hc hJ hzero hp

/-- The finite BCZ/Farey-triangle inclusion--exclusion formula with cutoff
`K`. -/
def explicitLimitAtCutoff (A c : ℝ) (K : ℕ) : ℝ :=
  (6 / Real.pi ^ 2) *
    ∑ J ∈ (Finset.Icc 1 K).powerset,
      (-1 : ℝ) ^ J.card *
        ∫ p in fareyTriangle,
          cutoffOverlapIntegrand A c (insert 0 J) (Finset.insert_nonempty 0 J) p

/-- The canonical overlap cutoff `⌈2 A c²⌉`. -/
def overlapCutoff (A c : ℝ) : ℕ :=
  ⌈2 * A * c ^ 2⌉₊

lemma le_overlapCutoff (A c : ℝ) :
    2 * A * c ^ 2 ≤ (overlapCutoff A c : ℝ) := by
  simpa [overlapCutoff] using Nat.le_ceil (2 * A * c ^ 2)

/-- The exact bounded-offset inclusion--exclusion expansion for the active
Farey intervals at finite scale. -/
theorem Farey.measureReal_activeApproximationUnion_eq_sum_offset_subsets
    {N : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (hN : 0 < N) :
    volume.real (Farey.activeApproximationUnion N A c) =
      ∑ i ∈ Finset.Icc 0
          ((Farey.Fraction.sequence ⌊c * (N : ℝ)⌋₊).length - 1),
        ∑ w ∈ (Finset.Icc 1
            (min (overlapCutoff A c)
              ((Farey.Fraction.sequence ⌊c * (N : ℝ)⌋₊).length - 1 - i))).powerset,
          (-1 : ℝ) ^ (w.card + 2) *
            volume.real
              (⋂ j ∈ insert i (w.image fun d ↦ i + d),
                Farey.activeIntervalAt N ⌊c * (N : ℝ)⌋₊ A j) := by
  let Q := ⌊c * (N : ℝ)⌋₊
  have hc0 : (0 : ℝ) ≤ c := zero_le_one.trans hc
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hcN0 : (0 : ℝ) ≤ c * N := mul_nonneg hc0 hN0
  have hNQ : N ≤ Q := by
    apply Nat.le_floor
    have hNreal : (0 : ℝ) ≤ N := by positivity
    nlinarith
  have hQ : 0 < Q := hN.trans_le hNQ
  have hQN : (Q : ℝ) ≤ c * N := Nat.floor_le hcN0
  rw [Farey.activeApproximationUnion_eq_biUnion_activeIndexFinset_order]
  apply Farey.measureReal_biUnion_activeIndexFinset_eq_sum_offset_subsets
  intro i j hi hj hij hK
  apply Farey.activeIntervalAt_disjoint_of_large_offset
    hA hc hN hQ hQN hij
  exact (le_overlapCutoff A c).trans (by exact_mod_cast hK.le)

/-- The explicit all-parameter candidate from the finite BCZ integral
formula. -/
def erdosSzuszTuranLimit (A c : ℝ) : ℝ :=
  explicitLimitAtCutoff A c (overlapCutoff A c)

lemma bczIndex_pos {p : ℝ × ℝ} (hp : p ∈ fareyTriangle) :
    0 < bczIndex p := by
  change 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 ∧ 1 < p.1 + p.2 at hp
  rw [bczIndex, Int.floor_pos]
  rw [le_div_iff₀ hp.2.2.1]
  linarith

lemma bczMap_mem_fareyTriangle {p : ℝ × ℝ} (hp : p ∈ fareyTriangle) :
    bczMap p ∈ fareyTriangle := by
  change 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 ∧ 1 < p.1 + p.2 at hp
  rcases hp with ⟨hu0, hu1, hv0, hv1, huv⟩
  have hklo : (bczIndex p : ℝ) ≤ (1 + p.1) / p.2 := Int.floor_le _
  have hkhi : (1 + p.1) / p.2 < (bczIndex p : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [le_div_iff₀ hv0] at hklo
  rw [div_lt_iff₀ hv0] at hkhi
  ring_nf at hklo hkhi
  change 0 < p.2 ∧ p.2 ≤ 1 ∧
    0 < (bczIndex p : ℝ) * p.2 - p.1 ∧
    (bczIndex p : ℝ) * p.2 - p.1 ≤ 1 ∧
    1 < p.2 + ((bczIndex p : ℝ) * p.2 - p.1)
  constructor
  · exact hv0
  constructor
  · exact hv1
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma bczMap_iterate_mem_fareyTriangle {p : ℝ × ℝ}
    (hp : p ∈ fareyTriangle) (j : ℕ) :
    bczMap^[j] p ∈ fareyTriangle := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact bczMap_mem_fareyTriangle ih

@[simp] lemma normalizedDenominator_zero (p : ℝ × ℝ) :
    normalizedDenominator 0 p = p.1 := by
  simp [normalizedDenominator]

@[simp] lemma normalizedDenominator_one (p : ℝ × ℝ) :
    normalizedDenominator 1 p = p.2 := by
  simp [normalizedDenominator, bczMap]

lemma normalizedDenominator_add_two (j : ℕ) (p : ℝ × ℝ) :
    normalizedDenominator (j + 2) p =
      (bczIndex (bczMap^[j] p) : ℝ) * normalizedDenominator (j + 1) p -
        normalizedDenominator j p := by
  simp only [normalizedDenominator]
  rw [show j + 2 = (j + 1) + 1 by omega,
    Function.iterate_succ_apply', Function.iterate_succ_apply']
  simp [bczMap]

lemma normalizedDenominator_pos {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (j : ℕ) : 0 < normalizedDenominator j p := by
  change 0 < (bczMap^[j] p).1
  exact (bczMap_iterate_mem_fareyTriangle hp j).1

lemma normalizedDenominator_le_one {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (j : ℕ) : normalizedDenominator j p ≤ 1 := by
  change (bczMap^[j] p).1 ≤ 1
  exact (bczMap_iterate_mem_fareyTriangle hp j).2.1

lemma natCast_le_normalizedGap {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (j : ℕ) : (j : ℝ) ≤ normalizedGap j p := by
  rw [normalizedGap]
  calc
    (j : ℝ) = ∑ _ℓ ∈ Finset.range j, (1 : ℝ) := by simp
    _ ≤ ∑ ℓ ∈ Finset.range j,
        1 / (normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p) := by
      gcongr with ℓ hℓ
      have hleftpos := normalizedDenominator_pos hp ℓ
      have hrightpos := normalizedDenominator_pos hp (ℓ + 1)
      have hleftle := normalizedDenominator_le_one hp ℓ
      have hrightle := normalizedDenominator_le_one hp (ℓ + 1)
      rw [le_div_iff₀ (mul_pos hleftpos hrightpos)]
      nlinarith

lemma cutoffOverlapIntegrand_pos_imp_normalizedGap_lt
    {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (hpos : 0 < cutoffOverlapIntegrand A c J hJ p)
    {k : ℕ} (hk : k ∈ J) :
    normalizedGap k p < 2 * A * c ^ 2 := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [cutoffOverlapIntegrand] at hpos
  split_ifs at hpos with hcut
  · have hupperMem : normalizedUpperEndpoint A 0 p ∈
        J.image (fun j ↦ normalizedUpperEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
    have hlowerMem : normalizedLowerEndpoint A k p ∈
        J.image (fun j ↦ normalizedLowerEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hmin := Finset.min'_le
      (J.image (fun j ↦ normalizedUpperEndpoint A j p))
      (normalizedUpperEndpoint A 0 p) hupperMem
    have hmax := Finset.le_max'
      (J.image (fun j ↦ normalizedLowerEndpoint A j p))
      (normalizedLowerEndpoint A k p) hlowerMem
    have hdiffpos :
        0 <
          (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
            (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) := by
      rw [finiteOverlapLength] at hpos
      simpa [lt_max_iff] using hpos
    have hendpoint :
        normalizedLowerEndpoint A k p < normalizedUpperEndpoint A 0 p := by
      linarith
    have hcutzero := hcut 0 hzero
    have hcutk := hcut k hk
    rw [normalizedDenominator_zero] at hcutzero
    have hinvsq (x : ℝ) (hxpos : 0 < x) (hcutx : 1 / c ≤ x) :
        1 / x ^ 2 ≤ c ^ 2 := by
      rw [div_le_iff₀ hcpos] at hcutx
      have hsq : (1 : ℝ) * 1 ≤ (x * c) * (x * c) :=
        mul_self_le_mul_self (by norm_num) hcutx
      rw [div_le_iff₀ (sq_pos_of_pos hxpos)]
      nlinarith
    have hinvzero : 1 / p.1 ^ 2 ≤ c ^ 2 :=
      hinvsq p.1 hp.1 hcutzero
    have hinvk : 1 / normalizedDenominator k p ^ 2 ≤ c ^ 2 :=
      hinvsq _ (normalizedDenominator_pos hp k) hcutk
    have hradiuszero : A / p.1 ^ 2 ≤ A * c ^ 2 := by
      calc
        A / p.1 ^ 2 = A * (1 / p.1 ^ 2) := by ring
        _ ≤ A * c ^ 2 := mul_le_mul_of_nonneg_left hinvzero hA
    have hradiusk : A / normalizedDenominator k p ^ 2 ≤ A * c ^ 2 := by
      calc
        A / normalizedDenominator k p ^ 2 =
            A * (1 / normalizedDenominator k p ^ 2) := by ring
        _ ≤ A * c ^ 2 := mul_le_mul_of_nonneg_left hinvk hA
    have hupperzero : normalizedUpperEndpoint A 0 p = A / p.1 ^ 2 := by
      simp [normalizedUpperEndpoint, normalizedGap, normalizedDenominator]
    rw [normalizedLowerEndpoint, hupperzero] at hendpoint
    linarith
  · simp at hpos

lemma cutoffOverlapIntegrand_pos_imp_intermediateDenominators_lower
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (hpos : 0 < cutoffOverlapIntegrand A c J hJ p)
    {ℓ : ℕ} (hℓ : ℓ < J.max' hJ) :
    1 / (2 * A * c ^ 2) < normalizedDenominator ℓ p ∧
      1 / (2 * A * c ^ 2) < normalizedDenominator (ℓ + 1) p := by
  let m := J.max' hJ
  have hm : m ∈ J := Finset.max'_mem J hJ
  have hgap : normalizedGap m p < 2 * A * c ^ 2 :=
    cutoffOverlapIntegrand_pos_imp_normalizedGap_lt hA.le hc hJ hzero hp hpos hm
  have htermle :
      1 / (normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p) ≤
        normalizedGap m p := by
    rw [normalizedGap]
    exact Finset.single_le_sum
      (f := fun i ↦
        1 / (normalizedDenominator i p * normalizedDenominator (i + 1) p))
      (fun i _ ↦ by
        exact div_nonneg (by norm_num)
          (mul_nonneg (normalizedDenominator_pos hp i).le
            (normalizedDenominator_pos hp (i + 1)).le))
      (Finset.mem_range.mpr hℓ)
  have hterm :
      1 / (normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p) <
        2 * A * c ^ 2 := htermle.trans_lt hgap
  have hBpos : 0 < 2 * A * c ^ 2 := by positivity
  have hxpos := normalizedDenominator_pos hp ℓ
  have hypos := normalizedDenominator_pos hp (ℓ + 1)
  have hxle := normalizedDenominator_le_one hp ℓ
  have hyle := normalizedDenominator_le_one hp (ℓ + 1)
  have hprodpos :
      0 < normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p :=
    mul_pos hxpos hypos
  have hprodle_x :
      normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p ≤
        normalizedDenominator ℓ p := by nlinarith
  have hprodle_y :
      normalizedDenominator ℓ p * normalizedDenominator (ℓ + 1) p ≤
        normalizedDenominator (ℓ + 1) p := by nlinarith
  constructor
  · apply (one_div_lt hxpos hBpos).mp
    exact (one_div_le_one_div_of_le hprodpos hprodle_x).trans_lt hterm
  · apply (one_div_lt hypos hBpos).mp
    exact (one_div_le_one_div_of_le hprodpos hprodle_y).trans_lt hterm

lemma cutoffOverlapIntegrand_pos_imp_le_overlapCutoff
    {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (hpos : 0 < cutoffOverlapIntegrand A c J hJ p)
    {k : ℕ} (hk : k ∈ J) :
    k ≤ overlapCutoff A c := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [cutoffOverlapIntegrand] at hpos
  split_ifs at hpos with hcut
  · have hupperMem : normalizedUpperEndpoint A 0 p ∈
        J.image (fun j ↦ normalizedUpperEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
    have hlowerMem : normalizedLowerEndpoint A k p ∈
        J.image (fun j ↦ normalizedLowerEndpoint A j p) := by
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hmin := Finset.min'_le
      (J.image (fun j ↦ normalizedUpperEndpoint A j p))
      (normalizedUpperEndpoint A 0 p) hupperMem
    have hmax := Finset.le_max'
      (J.image (fun j ↦ normalizedLowerEndpoint A j p))
      (normalizedLowerEndpoint A k p) hlowerMem
    have hdiffpos :
        0 <
          (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
            (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) := by
      rw [finiteOverlapLength] at hpos
      simpa [lt_max_iff] using hpos
    have hendpoint :
        normalizedLowerEndpoint A k p < normalizedUpperEndpoint A 0 p := by
      linarith
    have hcutzero := hcut 0 hzero
    have hcutk := hcut k hk
    rw [normalizedDenominator_zero] at hcutzero
    have hinvsq (x : ℝ) (hxpos : 0 < x) (hcutx : 1 / c ≤ x) :
        1 / x ^ 2 ≤ c ^ 2 := by
      rw [div_le_iff₀ hcpos] at hcutx
      have hsq : (1 : ℝ) * 1 ≤ (x * c) * (x * c) :=
        mul_self_le_mul_self (by norm_num) hcutx
      rw [div_le_iff₀ (sq_pos_of_pos hxpos)]
      nlinarith
    have hinvzero : 1 / p.1 ^ 2 ≤ c ^ 2 :=
      hinvsq p.1 hp.1 hcutzero
    have hinvk : 1 / normalizedDenominator k p ^ 2 ≤ c ^ 2 :=
      hinvsq _ (normalizedDenominator_pos hp k) hcutk
    have hradiuszero : A / p.1 ^ 2 ≤ A * c ^ 2 := by
      calc
        A / p.1 ^ 2 = A * (1 / p.1 ^ 2) := by ring
        _ ≤ A * c ^ 2 := mul_le_mul_of_nonneg_left hinvzero hA
    have hradiusk : A / normalizedDenominator k p ^ 2 ≤ A * c ^ 2 := by
      calc
        A / normalizedDenominator k p ^ 2 =
            A * (1 / normalizedDenominator k p ^ 2) := by ring
        _ ≤ A * c ^ 2 := mul_le_mul_of_nonneg_left hinvk hA
    have hupperzero : normalizedUpperEndpoint A 0 p = A / p.1 ^ 2 := by
      simp [normalizedUpperEndpoint, normalizedGap, normalizedDenominator]
    have hgap : normalizedGap k p < 2 * A * c ^ 2 := by
      rw [normalizedLowerEndpoint, hupperzero] at hendpoint
      linarith
    have hkreal : (k : ℝ) ≤ 2 * A * c ^ 2 :=
      (natCast_le_normalizedGap hp k).trans hgap.le
    exact_mod_cast hkreal.trans (le_overlapCutoff A c)
  · simp at hpos

/-- The overlap integrand with a direct lower threshold on every selected
normalized denominator. -/
def thresholdOverlapIntegrand (A t : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (p : ℝ × ℝ) : ℝ :=
  if ∀ j ∈ J, t ≤ normalizedDenominator j p then
    finiteOverlapLength A J hJ p
  else 0

lemma thresholdOverlapIntegrand_one_div (A c : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) :
    thresholdOverlapIntegrand A (1 / c) J hJ =
      cutoffOverlapIntegrand A c J hJ := by
  rfl

lemma measurable_thresholdOverlapIntegrand (A t : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) : Measurable (thresholdOverlapIntegrand A t J hJ) := by
  have hp : MeasurableSet
      {p : ℝ × ℝ | ∀ j ∈ J, t ≤ normalizedDenominator j p} := by
    rw [show {p : ℝ × ℝ | ∀ j ∈ J, t ≤ normalizedDenominator j p} =
        ⋂ j ∈ J, {p : ℝ × ℝ | t ≤ normalizedDenominator j p} by
      ext p
      simp]
    exact J.measurableSet_biInter (fun j _ ↦
      measurableSet_le
        (measurable_const : Measurable (fun _ : ℝ × ℝ ↦ t))
        (measurable_normalizedDenominator j))
  exact Measurable.ite hp (measurable_finiteOverlapLength A J hJ) measurable_const

lemma thresholdOverlapIntegrand_nonneg (A t : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) (p : ℝ × ℝ) :
    0 ≤ thresholdOverlapIntegrand A t J hJ p := by
  rw [thresholdOverlapIntegrand]
  split_ifs
  · exact finiteOverlapLength_nonneg A J hJ p
  · exact le_rfl

/-- For the singleton offset family, the normalized overlap is just the
width of the offset-zero approximation interval, subject to its denominator
threshold. -/
lemma thresholdOverlapIntegrand_singleton_zero
    {A t : ℝ} (hA : 0 ≤ A) (p : ℝ × ℝ) :
    thresholdOverlapIntegrand A t {0} (by simp) p =
      if t ≤ p.1 then 2 * A / p.1 ^ 2 else 0 := by
  simp only [thresholdOverlapIntegrand, Finset.mem_singleton, forall_eq]
  rw [normalizedDenominator_zero]
  split_ifs
  · simp only [finiteOverlapLength, normalizedUpperEndpoint, normalizedLowerEndpoint,
      normalizedGap, normalizedDenominator_zero, Finset.image_singleton,
      Finset.min'_singleton, Finset.max'_singleton, Finset.sum_range_zero,
      zero_add, zero_sub, Function.iterate_zero_apply]
    rw [max_eq_right (by
      have hdiv : 0 ≤ A / p.1 ^ 2 := div_nonneg hA (sq_nonneg p.1)
      linarith)]
    ring
  · rfl

lemma thresholdOverlapIntegrand_antitone (A : ℝ) (J : Finset ℕ)
    (hJ : J.Nonempty) :
    Antitone (fun t ↦ thresholdOverlapIntegrand A t J hJ) := by
  intro t u htu p
  change (if ∀ j ∈ J, u ≤ normalizedDenominator j p then
      finiteOverlapLength A J hJ p else 0) ≤
    (if ∀ j ∈ J, t ≤ normalizedDenominator j p then
      finiteOverlapLength A J hJ p else 0)
  by_cases hu : ∀ j ∈ J, u ≤ normalizedDenominator j p
  · rw [if_pos hu, if_pos (fun j hj ↦ htu.trans (hu j hj))]
  · rw [if_neg hu]
    split_ifs
    · exact finiteOverlapLength_nonneg A J hJ p
    · exact le_rfl

lemma thresholdOverlapIntegrand_le_finiteOverlapLength
    (A t : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) (p : ℝ × ℝ) :
    thresholdOverlapIntegrand A t J hJ p ≤ finiteOverlapLength A J hJ p := by
  rw [thresholdOverlapIntegrand]
  split_ifs
  · exact le_rfl
  · exact finiteOverlapLength_nonneg A J hJ p

lemma finiteOverlapLength_le_zero_width
    {A : ℝ} (hA : 0 ≤ A) {J : Finset ℕ} (hJ : J.Nonempty)
    (hzero : 0 ∈ J) {p : ℝ × ℝ} :
    finiteOverlapLength A J hJ p ≤ 2 * A / p.1 ^ 2 := by
  have hupperMem : normalizedUpperEndpoint A 0 p ∈
      J.image (fun j ↦ normalizedUpperEndpoint A j p) := by
    exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
  have hlowerMem : normalizedLowerEndpoint A 0 p ∈
      J.image (fun j ↦ normalizedLowerEndpoint A j p) := by
    exact Finset.mem_image.mpr ⟨0, hzero, rfl⟩
  have hmin := Finset.min'_le
    (J.image (fun j ↦ normalizedUpperEndpoint A j p))
    (normalizedUpperEndpoint A 0 p) hupperMem
  have hmax := Finset.le_max'
    (J.image (fun j ↦ normalizedLowerEndpoint A j p))
    (normalizedLowerEndpoint A 0 p) hlowerMem
  have hwidth :
      normalizedUpperEndpoint A 0 p - normalizedLowerEndpoint A 0 p =
        2 * A / p.1 ^ 2 := by
    simp [normalizedUpperEndpoint, normalizedLowerEndpoint, normalizedGap,
      normalizedDenominator]
    ring
  have hdiff :
      (J.image (fun j ↦ normalizedUpperEndpoint A j p)).min' (hJ.image _) -
          (J.image (fun j ↦ normalizedLowerEndpoint A j p)).max' (hJ.image _) ≤
        2 * A / p.1 ^ 2 := by
    rw [← hwidth]
    linarith
  rw [finiteOverlapLength]
  exact max_le (by positivity) hdiff

lemma thresholdOverlapIntegrand_le
    {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    {p : ℝ × ℝ} :
    thresholdOverlapIntegrand A t J hJ p ≤ 2 * A / t ^ 2 := by
  have hbound_nonneg : 0 ≤ 2 * A / t ^ 2 := by positivity
  rw [thresholdOverlapIntegrand]
  split_ifs with hcut
  · have hcutzero := hcut 0 hzero
    rw [normalizedDenominator_zero] at hcutzero
    have hsq : t ^ 2 ≤ p.1 ^ 2 := by nlinarith
    have hinv : 1 / p.1 ^ 2 ≤ 1 / t ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
    refine (finiteOverlapLength_le_zero_width hA hJ hzero).trans ?_
    calc
      2 * A / p.1 ^ 2 = (2 * A) * (1 / p.1 ^ 2) := by ring
      _ ≤ (2 * A) * (1 / t ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * A / t ^ 2 := by ring
  · exact hbound_nonneg

lemma integrableOn_thresholdOverlapIntegrand
    {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J) :
    IntegrableOn (thresholdOverlapIntegrand A t J hJ) fareyTriangle := by
  refine Measure.integrableOn_of_bounded (M := 2 * A / t ^ 2)
    measure_fareyTriangle_lt_top.ne
    (measurable_thresholdOverlapIntegrand A t J hJ).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_fareyTriangle ?_
  intro p hp
  rw [Real.norm_of_nonneg (thresholdOverlapIntegrand_nonneg A t J hJ p)]
  exact thresholdOverlapIntegrand_le hA ht hJ hzero

lemma tendsto_thresholdOverlapIntegrand_of_denominator_ne
    {ι : Type*} {l : Filter ι} {tseq : ι → ℝ} {t : ℝ}
    (ht : Tendsto tseq l (nhds t))
    (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) (p : ℝ × ℝ)
    (hboundary : ∀ j ∈ J, normalizedDenominator j p ≠ t) :
    Tendsto (fun n ↦ thresholdOverlapIntegrand A (tseq n) J hJ p) l
      (nhds (thresholdOverlapIntegrand A t J hJ p)) := by
  by_cases hcut : ∀ j ∈ J, t ≤ normalizedDenominator j p
  · have hev : ∀ᶠ n in l, ∀ j ∈ J,
        tseq n ≤ normalizedDenominator j p := by
      rw [J.eventually_all]
      intro j hj
      have hjlt : t < normalizedDenominator j p :=
        lt_of_le_of_ne (hcut j hj) (hboundary j hj).symm
      exact ((tendsto_order.1 ht).2 _ hjlt).mono fun _ hn ↦ hn.le
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [thresholdOverlapIntegrand, if_pos hn, if_pos hcut]
  · have hcut' := hcut
    simp only [not_forall, not_le] at hcut'
    obtain ⟨j, hj, hjlt⟩ := hcut'
    have hev : ∀ᶠ n in l, normalizedDenominator j p < tseq n :=
      (tendsto_order.1 ht).1 _ hjlt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    have hncut : ¬ ∀ k ∈ J, tseq n ≤ normalizedDenominator k p := by
      intro hall
      exact (not_lt_of_ge (hall j hj)) hn
    have htcut : ¬ ∀ k ∈ J, t ≤ normalizedDenominator k p := by
      intro hall
      exact (not_lt_of_ge (hall j hj)) hjlt
    simp only [thresholdOverlapIntegrand, if_neg hncut, if_neg htcut]

lemma tendsto_setIntegral_thresholdOverlapIntegrand
    {tseq : ℕ → ℝ} {t : ℝ} (ht : Tendsto tseq atTop (nhds t))
    (htpos : 0 < t) {A : ℝ} (hA : 0 ≤ A)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    (hboundary : ∀ᵐ p ∂volume.restrict fareyTriangle,
      ∀ j ∈ J, normalizedDenominator j p ≠ t) :
    Tendsto
      (fun n ↦ ∫ p in fareyTriangle,
        thresholdOverlapIntegrand A (tseq n) J hJ p)
      atTop
      (nhds (∫ p in fareyTriangle, thresholdOverlapIntegrand A t J hJ p)) := by
  let _ : IsFiniteMeasure (volume.restrict fareyTriangle) :=
    ⟨by simpa using measure_fareyTriangle_lt_top⟩
  have hevent : ∀ᶠ n in atTop, t / 2 ≤ tseq n :=
    ((tendsto_order.1 ht).1 (t / 2) (by linarith)).mono fun _ hn ↦ hn.le
  apply tendsto_integral_filter_of_norm_le_const
  · exact Filter.Eventually.of_forall fun n ↦
      (measurable_thresholdOverlapIntegrand A (tseq n) J hJ).aestronglyMeasurable
  · refine ⟨2 * A / (t / 2) ^ 2, hevent.mono fun n hn ↦ ?_⟩
    refine ae_restrict_of_forall_mem measurableSet_fareyTriangle ?_
    intro p hp
    rw [Real.norm_of_nonneg
      (thresholdOverlapIntegrand_nonneg A (tseq n) J hJ p)]
    exact ((thresholdOverlapIntegrand_antitone A J hJ) hn p).trans
      (thresholdOverlapIntegrand_le hA (by linarith) hJ hzero)
  · exact hboundary.mono fun p hp ↦
      tendsto_thresholdOverlapIntegrand_of_denominator_ne ht A J hJ p hp

lemma tendsto_setIntegral_thresholdOverlapIntegrand_of_levelSet_null
    {tseq : ℕ → ℝ} {t : ℝ} (ht : Tendsto tseq atTop (nhds t))
    (htpos : 0 < t) {A : ℝ} (hA : 0 ≤ A)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    (hlevel : ∀ j ∈ J,
      (volume.restrict fareyTriangle) {p | normalizedDenominator j p = t} = 0) :
    Tendsto
      (fun n ↦ ∫ p in fareyTriangle,
        thresholdOverlapIntegrand A (tseq n) J hJ p)
      atTop
      (nhds (∫ p in fareyTriangle, thresholdOverlapIntegrand A t J hJ p)) := by
  apply tendsto_setIntegral_thresholdOverlapIntegrand ht htpos hA hJ hzero
  rw [J.eventually_all]
  intro j hj
  exact (measure_eq_zero_iff_ae_notMem.mp (hlevel j hj)).mono fun p hp ↦ by
    simpa using hp

/-- The finite BCZ inclusion--exclusion expression with a direct normalized
denominator threshold. -/
def explicitLimitAtThreshold (A t : ℝ) (K : ℕ) : ℝ :=
  (6 / Real.pi ^ 2) *
    ∑ J ∈ (Finset.Icc 1 K).powerset,
      (-1 : ℝ) ^ J.card *
        ∫ p in fareyTriangle,
          thresholdOverlapIntegrand A t (insert 0 J) (Finset.insert_nonempty 0 J) p

lemma explicitLimitAtThreshold_one_div (A c : ℝ) (K : ℕ) :
    explicitLimitAtThreshold A (1 / c) K = explicitLimitAtCutoff A c K := by
  rfl

lemma tendsto_explicitLimitAtThreshold
    {tseq : ℕ → ℝ} {t : ℝ} (ht : Tendsto tseq atTop (nhds t))
    (htpos : 0 < t) {A : ℝ} (hA : 0 ≤ A) (K : ℕ)
    (hlevel : ∀ J ∈ (Finset.Icc 1 K).powerset, ∀ j ∈ insert 0 J,
      (volume.restrict fareyTriangle) {p | normalizedDenominator j p = t} = 0) :
    Tendsto (fun n ↦ explicitLimitAtThreshold A (tseq n) K) atTop
      (nhds (explicitLimitAtThreshold A t K)) := by
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro J hJ
  apply Tendsto.const_mul
  exact tendsto_setIntegral_thresholdOverlapIntegrand_of_levelSet_null
    ht htpos hA (Finset.insert_nonempty 0 J) (Finset.mem_insert_self 0 J)
    (fun j hj ↦ hlevel J hJ j hj)

/-- A level set of a nonzero linear functional on the plane has zero
Lebesgue measure. -/
lemma volume_linear_levelSet_eq_zero
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (t : ℝ) :
    volume {p | f p = t} = 0 := by
  by_cases hne : Set.Nonempty {p | f p = t}
  · obtain ⟨x, hx⟩ := hne
    let s : AffineSubspace ℝ (ℝ × ℝ) := AffineSubspace.mk' x f.ker
    apply measure_mono_null (t := (s : Set (ℝ × ℝ)))
    · intro y hy
      change y - x ∈ f.ker
      rw [LinearMap.mem_ker, map_sub, hy, hx, sub_self]
    · apply Measure.addHaar_affineSubspace volume s
      intro hs
      have hker : f.ker = ⊤ := by
        simpa [s] using congrArg AffineSubspace.direction hs
      exact hf (LinearMap.ker_eq_top.mp hker)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]

/-- The linear branch of the BCZ map with a fixed integer index. -/
def bczBranchLinear (k : ℤ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prod (LinearMap.snd ℝ ℝ ℝ)
    ((k : ℝ) • LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ)

@[simp] lemma bczBranchLinear_apply (k : ℤ) (p : ℝ × ℝ) :
    bczBranchLinear k p = (p.2, (k : ℝ) * p.2 - p.1) := by
  rfl

lemma bczBranchLinear_bijective (k : ℤ) :
    Function.Bijective (bczBranchLinear k) := by
  constructor
  · rintro ⟨u, v⟩ ⟨u', v'⟩ h
    simp only [bczBranchLinear_apply, Prod.mk.injEq] at h
    simp only [Prod.mk.injEq]
    rcases h with ⟨rfl, h⟩
    constructor
    · linarith
    · rfl
  · rintro ⟨u, v⟩
    refine ⟨((k : ℝ) * u - v, u), ?_⟩
    simp [bczBranchLinear_apply]

def bczBranchLinearEquiv (k : ℤ) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.ofBijective (bczBranchLinear k) (bczBranchLinear_bijective k)

@[simp] lemma bczBranchLinearEquiv_apply (k : ℤ) (p : ℝ × ℝ) :
    bczBranchLinearEquiv k p = (p.2, (k : ℝ) * p.2 - p.1) := by
  rfl

/-- Composition of fixed-index BCZ branches.  The head of the list is the
last branch applied. -/
def bczBranchWordEquiv : List ℤ → (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ)
  | [] => LinearEquiv.refl ℝ (ℝ × ℝ)
  | k :: w => (bczBranchWordEquiv w).trans (bczBranchLinearEquiv k)

@[simp] lemma bczBranchWordEquiv_nil_apply (p : ℝ × ℝ) :
    bczBranchWordEquiv [] p = p := by
  rfl

@[simp] lemma bczBranchWordEquiv_cons_apply (k : ℤ) (w : List ℤ)
    (p : ℝ × ℝ) :
    bczBranchWordEquiv (k :: w) p =
      bczBranchLinearEquiv k (bczBranchWordEquiv w p) := by
  rfl

lemma bczMap_eq_branch (p : ℝ × ℝ) :
    bczMap p = bczBranchLinearEquiv (bczIndex p) p := by
  rfl

lemma bcz_iterate_eq_branchWord (p : ℝ × ℝ) (j : ℕ) :
    ∃ w : List ℤ, bczMap^[j] p = bczBranchWordEquiv w p := by
  induction j with
  | zero => exact ⟨[], rfl⟩
  | succ j ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨bczIndex (bczMap^[j] p) :: w, ?_⟩
      rw [Function.iterate_succ_apply', bczMap_eq_branch, hw]
      rfl

/-- On a fixed BCZ itinerary, the normalized denominator is a nonzero
linear functional. -/
def branchDenominatorLinear (w : List ℤ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ ℝ).comp (bczBranchWordEquiv w).toLinearMap

lemma branchDenominatorLinear_ne_zero (w : List ℤ) :
    branchDenominatorLinear w ≠ 0 := by
  intro hzero
  have hval :
      branchDenominatorLinear w ((bczBranchWordEquiv w).symm (1, 0)) = 1 := by
    simp [branchDenominatorLinear]
  rw [hzero] at hval
  norm_num at hval

lemma normalizedDenominator_levelSet_subset_iUnion (j : ℕ) (t : ℝ) :
    {p | normalizedDenominator j p = t} ⊆
      ⋃ w : List ℤ, {p | branchDenominatorLinear w p = t} := by
  intro p hp
  obtain ⟨w, hw⟩ := bcz_iterate_eq_branchWord p j
  refine mem_iUnion.2 ⟨w, ?_⟩
  simpa [normalizedDenominator, branchDenominatorLinear, hw] using hp

/-- Every normalized-denominator level set is null.  No nonzero assumption
on the level is needed. -/
lemma volume_normalizedDenominator_levelSet_eq_zero (j : ℕ) (t : ℝ) :
    volume {p | normalizedDenominator j p = t} = 0 := by
  apply measure_mono_null (normalizedDenominator_levelSet_subset_iUnion j t)
  exact measure_iUnion_null fun w ↦
    volume_linear_levelSet_eq_zero (branchDenominatorLinear w)
      (branchDenominatorLinear_ne_zero w) t

lemma restrict_fareyTriangle_normalizedDenominator_levelSet_eq_zero
    (j : ℕ) (t : ℝ) :
    (volume.restrict fareyTriangle) {p | normalizedDenominator j p = t} = 0 := by
  apply le_zero_iff.mp
  exact ((Measure.restrict_le_self : volume.restrict fareyTriangle ≤ volume)
    {p | normalizedDenominator j p = t}).trans_eq
      (volume_normalizedDenominator_levelSet_eq_zero j t)

lemma tendsto_setIntegral_thresholdOverlapIntegrand_unconditional
    {tseq : ℕ → ℝ} {t : ℝ} (ht : Tendsto tseq atTop (nhds t))
    (htpos : 0 < t) {A : ℝ} (hA : 0 ≤ A)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J) :
    Tendsto
      (fun n ↦ ∫ p in fareyTriangle,
        thresholdOverlapIntegrand A (tseq n) J hJ p)
      atTop
      (nhds (∫ p in fareyTriangle, thresholdOverlapIntegrand A t J hJ p)) := by
  exact tendsto_setIntegral_thresholdOverlapIntegrand_of_levelSet_null
    ht htpos hA hJ hzero fun j _ ↦
      restrict_fareyTriangle_normalizedDenominator_levelSet_eq_zero j t

lemma tendsto_explicitLimitAtThreshold_unconditional
    {tseq : ℕ → ℝ} {t : ℝ} (ht : Tendsto tseq atTop (nhds t))
    (htpos : 0 < t) {A : ℝ} (hA : 0 ≤ A) (K : ℕ) :
    Tendsto (fun n ↦ explicitLimitAtThreshold A (tseq n) K) atTop
      (nhds (explicitLimitAtThreshold A t K)) := by
  exact tendsto_explicitLimitAtThreshold ht htpos hA K fun _ _ j _ ↦
    restrict_fareyTriangle_normalizedDenominator_levelSet_eq_zero j t

/-- The primitive Farey-triangle sum for a fixed finite set of offsets,
with the exact moving cutoff `N / floor(cN)` and normalization by the square
of the Farey order. -/
def normalizedPrimitiveFareyOverlapSum
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  let Q := ⌊c * (N : ℝ)⌋₊
  (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          (thresholdOverlapIntegrand A
            ((N : ℝ) / (Q : ℝ)) J hJ) Q p
      else 0) /
    (Q : ℝ) ^ 2

/-- The primitive lattice-point sum is exactly the same sum indexed by
adjacent entries of the finite Farey sequence. -/
theorem normalizedPrimitiveFareyOverlapSum_eq_consecutiveIndex
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) :
    normalizedPrimitiveFareyOverlapSum N A c J hJ =
      let Q := ⌊c * (N : ℝ)⌋₊
      (∑ i : Farey.ConsecutiveIndex Q,
        thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
          (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
            ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)) /
        (Q : ℝ) ^ 2 := by
  let Q := ⌊c * (N : ℝ)⌋₊
  change
    (∑ p ∈ Farey.denominatorPairFinset Q,
        if Nat.Coprime p.1 p.2 then
          Farey.normalizedDenominatorPairWeight
            (thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ) Q p
        else 0) / (Q : ℝ) ^ 2 = _
  rw [← Farey.sum_consecutiveIndex_normalizedDenominatorPairWeight]

namespace Farey

/-- A selected family of absolute indices obtained from a least index is
the same family as the corresponding offsets. -/
theorem biInter_insert_image_add_eq_biInter_insert_zero
    {α : Type*} (s : ℕ → Set α) (i : ℕ) (w : Finset ℕ) :
    (⋂ j ∈ insert i (w.image fun d ↦ i + d), s j) =
      ⋂ d ∈ insert 0 w, s (i + d) := by
  ext x
  simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro h d hd
    rcases hd with rfl | hd
    · simpa using h i (Or.inl rfl)
    · exact h (i + d) (Or.inr ⟨d, hd, rfl⟩)
  · intro h j hj
    rcases hj with rfl | ⟨d, hd, rfl⟩
    · simpa using h 0 (Or.inl rfl)
    · exact h d (Or.inr hd)

/-- Exact normalization of an in-range active intersection beginning at a
nonterminal Farey index. -/
theorem volume_real_activeIntervalAt_biInter_eq_thresholdOverlapIntegrand
    {N Q : ℕ} {A : ℝ} (hQ : 0 < Q) (i : ConsecutiveIndex Q)
    (J : Finset ℕ) (hJ : J.Nonempty)
    (hJrange : ∀ d ∈ J,
      d ≤ (Fraction.sequence Q).length - 1 - i.1) :
    volume.real (⋂ d ∈ J, activeIntervalAt N Q A (i.1 + d)) =
      ((Q : ℝ) ^ 2)⁻¹ *
        thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
          (((consecutivePairAt Q i).1.1.den : ℝ) / Q,
            ((consecutivePairAt Q i).1.2.den : ℝ) / Q) := by
  let m := (Fraction.sequence Q).length - 1 - i.1
  let q : ℕ → Fraction Q := fractionAtOffset Q hQ i
  have hm : 1 ≤ m := by
    have hi := i.isLt
    omega
  have hchain : ∀ d < m, Consecutive (q d) (q (d + 1)) := by
    intro d hd
    exact consecutive_fractionAtOffset hQ i le_rfl hd
  have hq (d : ℕ) (hd : d ≤ m) :
      q d = fractionAt Q ⟨i.1 + d, by
        have hi := i.isLt
        omega⟩ :=
    fractionAtOffset_eq_of_le hQ i le_rfl hd
  let p : ℝ × ℝ :=
    (((q 0).den : ℝ) / Q, ((q 1).den : ℝ) / Q)
  have hp : p =
      (((consecutivePairAt Q i).1.1.den : ℝ) / Q,
        ((consecutivePairAt Q i).1.2.den : ℝ) / Q) := by
    exact initial_normalized_pair_fractionAtOffset hQ i
  rw [← hp]
  by_cases hcut : ∀ d ∈ J, (N : ℝ) / Q ≤ normalizedDenominator d p
  · have hden (d : ℕ) (hd : d ∈ J) : N ≤ (q d).den := by
      have hnorm := normalizedDenominator_chain_le hQ q (hJrange d hd) hchain
      have hcutd := hcut d hd
      have hnormp : normalizedDenominator d p = (q d).den / (Q : ℝ) := by
        simpa only [p] using hnorm
      rw [hnormp] at hcutd
      exact_mod_cast
        ((div_le_div_iff_of_pos_right (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp
          hcutd)
    have hactive (d : ℕ) (hd : d ∈ J) :
        activeIntervalAt N Q A (i.1 + d) =
          approximationInterval A ((q d).num : ℤ) (q d).den := by
      have hdm := hJrange d hd
      have hvalid : i.1 + d < (Fraction.sequence Q).length := by
        have hi := i.isLt
        omega
      have hqd := hq d hdm
      have hden' : N ≤ (fractionAt Q ⟨i.1 + d, hvalid⟩).den := by
        simpa only [← hqd] using hden d hd
      rw [activeIntervalAt, dif_pos hvalid, dif_pos hden', ← hqd]
    have hsets :
        (⋂ d ∈ J, activeIntervalAt N Q A (i.1 + d)) =
          ⋂ d ∈ J, approximationInterval A ((q d).num : ℤ) (q d).den := by
      ext x
      simp only [Set.mem_iInter]
      constructor
      · intro hx d hd
        rw [← hactive d hd]
        exact hx d hd
      · intro hx d hd
        rw [hactive d hd]
        exact hx d hd
    rw [thresholdOverlapIntegrand, if_pos hcut, hsets]
    exact volume_real_approximationInterval_biInter_eq_inv_sq_mul_finiteOverlapLength_le
      hQ A J hJ q hJrange hchain
  · have hcut0 := hcut
    simp only [not_forall, not_le] at hcut
    obtain ⟨d, hdJ, hdlt⟩ := hcut
    have hnorm := normalizedDenominator_chain_le hQ q (hJrange d hdJ) hchain
    have hnormp : normalizedDenominator d p = (q d).den / (Q : ℝ) := by
      simpa only [p] using hnorm
    rw [hnormp] at hdlt
    have hden : (q d).den < N := by
      exact_mod_cast
        ((div_lt_div_iff_of_pos_right (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp hdlt)
    have hdm := hJrange d hdJ
    have hvalid : i.1 + d < (Fraction.sequence Q).length := by
      have hi := i.isLt
      omega
    have hqd := hq d hdm
    have hinactive : activeIntervalAt N Q A (i.1 + d) = ∅ := by
      rw [activeIntervalAt, dif_pos hvalid, dif_neg]
      simpa only [← hqd] using (Nat.not_le_of_lt hden)
    have hempty : (⋂ k ∈ J, activeIntervalAt N Q A (i.1 + k)) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      intro hx
      have hxd := hx d hdJ
      rw [hinactive] at hxd
      exact hxd
    rw [thresholdOverlapIntegrand, if_neg hcut0, hempty]
    simp

/-- The terminal Farey fraction has denominator one, so it is inactive once
`N ≥ 2`. -/
theorem activeIntervalAt_last_eq_empty {N Q : ℕ} {A : ℝ}
    (hQ : 0 < Q) (hN2 : 2 ≤ N) :
    activeIntervalAt N Q A ((Fraction.sequence Q).length - 1) = ∅ := by
  have hlen := sequence_length_pos hQ
  rw [activeIntervalAt, dif_pos (Nat.sub_lt hlen Nat.zero_lt_one),
    fractionAt_last_eq_oneFraction hQ, dif_neg]
  simpa [oneFraction] using (show ¬ N ≤ 1 by omega)

end Farey

/-- Contribution from starting Farey edges for which at least one selected
offset runs past the terminal fraction. -/
def boundaryFareyOverlapSum
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  let Q := ⌊c * (N : ℝ)⌋₊
  (∑ i : Farey.ConsecutiveIndex Q,
      if ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
        0
      else
        thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
          (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
            ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)) /
    (Q : ℝ) ^ 2

/-- Splitting the full primitive sum into in-range starts and the explicit
right-boundary correction. -/
theorem normalizedPrimitiveFareyOverlapSum_eq_inRange_add_boundary
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) :
    normalizedPrimitiveFareyOverlapSum N A c J hJ =
      let Q := ⌊c * (N : ℝ)⌋₊
      (∑ i : Farey.ConsecutiveIndex Q,
          if ∀ d ∈ J,
              d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
            thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
              (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
                ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)
          else 0) / (Q : ℝ) ^ 2 +
        boundaryFareyOverlapSum N A c J hJ := by
  rw [normalizedPrimitiveFareyOverlapSum_eq_consecutiveIndex]
  let Q := ⌊c * (N : ℝ)⌋₊
  simp only [boundaryFareyOverlapSum]
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

lemma boundaryFareyOverlapSum_nonneg
    {N : ℕ} {A c : ℝ} (_hA : 0 ≤ A)
    (J : Finset ℕ) (hJ : J.Nonempty) :
    0 ≤ boundaryFareyOverlapSum N A c J hJ := by
  rw [boundaryFareyOverlapSum]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact le_rfl
    · exact thresholdOverlapIntegrand_nonneg A _ J hJ _
  · positivity

/-- At most `K` Farey edges can contribute to the right-boundary term when
all selected offsets are at most `K`. -/
lemma card_boundaryIndices_le
    (Q K : ℕ) (J : Finset ℕ) (hJK : ∀ d ∈ J, d ≤ K) :
    ((Finset.univ : Finset (Farey.ConsecutiveIndex Q)).filter
      (fun i ↦ ¬ ∀ d ∈ J,
        d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1)).card ≤ K := by
  let s := (Finset.univ : Finset (Farey.ConsecutiveIndex Q)).filter
    (fun i ↦ ¬ ∀ d ∈ J,
      d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1)
  let f : Farey.ConsecutiveIndex Q → ℕ := fun i ↦
    (Farey.Fraction.sequence Q).length - 1 - i.1
  have hcard := Finset.card_le_card_of_injOn f
    (s := s) (t := Finset.range K) (by
      intro i hi
      change f i ∈ Finset.range K
      rw [Finset.mem_range]
      change i ∈ s at hi
      change i ∈ (Finset.univ : Finset (Farey.ConsecutiveIndex Q)).filter
        (fun i ↦ ¬ ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1) at hi
      rw [Finset.mem_filter] at hi
      simp only [Finset.mem_univ, true_and, not_forall, not_le] at hi
      obtain ⟨d, hdJ, hlt⟩ := hi
      exact hlt.trans_le (hJK d hdJ)) (by
    intro i hi j hj heq
    apply Fin.ext
    change (Farey.Fraction.sequence Q).length - 1 - i.1 =
      (Farey.Fraction.sequence Q).length - 1 - j.1 at heq
    have hii := i.isLt
    have hjj := j.isLt
    omega)
  simpa [s] using hcard

/-- Quantitative boundary estimate.  After the `Q⁻²` normalization, each
boundary edge costs at most `2A/N²`, and there are at most `K` of them. -/
theorem abs_boundaryFareyOverlapSum_le
    {N K : ℕ} {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c) (hN : 0 < N)
    {J : Finset ℕ} (hJ : J.Nonempty) (hzero : 0 ∈ J)
    (hJK : ∀ d ∈ J, d ≤ K) :
    |boundaryFareyOverlapSum N A c J hJ| ≤
      (K : ℝ) * (2 * A) / (N : ℝ) ^ 2 := by
  let Q := ⌊c * (N : ℝ)⌋₊
  have hNQ : N ≤ Q := by
    apply Nat.le_floor
    have hNreal : (0 : ℝ) ≤ N := by positivity
    nlinarith [show (0 : ℝ) ≤ c * N by positivity]
  have hQ : 0 < Q := hN.trans_le hNQ
  have ht : 0 < (N : ℝ) / Q := by positivity
  let f : Farey.ConsecutiveIndex Q → ℝ := fun i ↦
    thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
      (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
        ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)
  let s := (Finset.univ : Finset (Farey.ConsecutiveIndex Q)).filter
    (fun i ↦ ¬ ∀ d ∈ J,
      d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1)
  have hrewrite :
      (∑ i : Farey.ConsecutiveIndex Q,
          if ∀ d ∈ J,
              d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
            0 else f i) = ∑ i ∈ s, f i := by
    change (Finset.univ : Finset (Farey.ConsecutiveIndex Q)).sum
      (fun i ↦ if ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
        0 else f i) =
      ((Finset.univ : Finset (Farey.ConsecutiveIndex Q)).filter
        (fun i ↦ ¬ ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1)).sum f
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hirange : ∀ d ∈ J,
        d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1
    · rw [if_pos hirange, if_neg]
      exact not_not_intro hirange
    · rw [if_neg hirange, if_pos hirange]
  rw [abs_of_nonneg (boundaryFareyOverlapSum_nonneg hA J hJ)]
  rw [boundaryFareyOverlapSum]
  change (∑ i : Farey.ConsecutiveIndex Q,
      if ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
        0 else f i) / (Q : ℝ) ^ 2 ≤ _
  rw [hrewrite]
  have hsum : (∑ i ∈ s, f i) ≤ s.card • (2 * A / ((N : ℝ) / Q) ^ 2) := by
    apply Finset.sum_le_card_nsmul
    intro i hi
    exact thresholdOverlapIntegrand_le hA ht hJ hzero
  have hcard : s.card ≤ K := by
    exact card_boundaryIndices_le Q K J hJK
  have hbound :
      s.card • (2 * A / ((N : ℝ) / Q) ^ 2) ≤
        (K : ℝ) * (2 * A / ((N : ℝ) / Q) ^ 2) := by
    simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right
      (show (s.card : ℝ) ≤ K by exact_mod_cast hcard)
      (by positivity : 0 ≤ 2 * A / ((N : ℝ) / Q) ^ 2)
  calc
    (∑ i ∈ s, f i) / (Q : ℝ) ^ 2 ≤
        ((K : ℝ) * (2 * A / ((N : ℝ) / Q) ^ 2)) / (Q : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (hsum.trans hbound) (sq_nonneg (Q : ℝ))
    _ = (K : ℝ) * (2 * A) / (N : ℝ) ^ 2 := by
      field_simp [show (N : ℝ) ≠ 0 by positivity, show (Q : ℝ) ≠ 0 by positivity]

/-- The normalized overlap sum restricted to starts for which every
selected offset remains inside the finite Farey sequence. -/
def inRangeFareyOverlapSum
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  let Q := ⌊c * (N : ℝ)⌋₊
  (∑ i : Farey.ConsecutiveIndex Q,
      if ∀ d ∈ J,
          d ≤ (Farey.Fraction.sequence Q).length - 1 - i.1 then
        thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
          (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
            ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)
      else 0) / (Q : ℝ) ^ 2

theorem normalizedPrimitiveFareyOverlapSum_eq_inRangeFareyOverlapSum_add_boundary
    (N : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) :
    normalizedPrimitiveFareyOverlapSum N A c J hJ =
      inRangeFareyOverlapSum N A c J hJ +
        boundaryFareyOverlapSum N A c J hJ := by
  exact normalizedPrimitiveFareyOverlapSum_eq_inRange_add_boundary N A c J hJ

/-- Rearrangement of the triangular base-index/offset-subset sum occurring
in finite inclusion--exclusion.  After discarding the empty terminal term,
one may sum first over all offset subsets and then over the nonterminal base
indices, retaining exactly the condition that every offset stays in range. -/
theorem sum_Icc_powerset_min_eq_sum_powerset_sum_range
    {R : Type*} [AddCommMonoid R] (L K : ℕ) (F : ℕ → Finset ℕ → R)
    (hlast : F L ∅ = 0) :
    (∑ i ∈ Finset.Icc 0 L,
        ∑ w ∈ (Finset.Icc 1 (min K (L - i))).powerset, F i w) =
      ∑ w ∈ (Finset.Icc 1 K).powerset,
        ∑ i ∈ Finset.range L,
          if ∀ d ∈ w, d ≤ L - i then F i w else 0 := by
  have hIcc : Finset.Icc 0 L = Finset.range (L + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, Finset.sum_range_succ]
  have hlastsum :
      (∑ w ∈ (Finset.Icc 1 (min K (L - L))).powerset, F L w) = 0 := by
    simp [hlast]
  rw [hlastsum, add_zero]
  have hinner (i : ℕ) (hi : i ∈ Finset.range L) :
      (∑ w ∈ (Finset.Icc 1 (min K (L - i))).powerset, F i w) =
        ∑ w ∈ (Finset.Icc 1 K).powerset,
          if ∀ d ∈ w, d ≤ L - i then F i w else 0 := by
    have hpow :
        (Finset.Icc 1 (min K (L - i))).powerset =
          ((Finset.Icc 1 K).powerset).filter
            (fun w ↦ ∀ d ∈ w, d ≤ L - i) := by
      ext w
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro hw
        constructor
        · intro d hd
          have hdIcc := Finset.mem_Icc.mp (hw hd)
          exact Finset.mem_Icc.mpr ⟨hdIcc.1, hdIcc.2.trans (min_le_left _ _)⟩
        · intro d hd
          exact (Finset.mem_Icc.mp (hw hd)).2.trans (min_le_right _ _)
      · rintro ⟨hwK, hwL⟩ d hd
        have hdK := Finset.mem_Icc.mp (hwK hd)
        exact Finset.mem_Icc.mpr ⟨hdK.1, le_min hdK.2 (hwL d hd)⟩
    rw [hpow, Finset.sum_filter]
  calc
    (∑ i ∈ Finset.range L,
        ∑ w ∈ (Finset.Icc 1 (min K (L - i))).powerset, F i w) =
        ∑ i ∈ Finset.range L, ∑ w ∈ (Finset.Icc 1 K).powerset,
          if ∀ d ∈ w, d ≤ L - i then F i w else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hinner i hi
    _ = _ := by rw [Finset.sum_comm]

/-- Exact finite-`N` inclusion--exclusion after normalizing every in-range
Farey chain. -/
theorem measureReal_activeApproximationUnion_eq_inRangeFareyOverlapSum
    {N : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (hN2 : 2 ≤ N) :
    volume.real (Farey.activeApproximationUnion N A c) =
      ∑ w ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ w.card *
          inRangeFareyOverlapSum N A c
            (insert 0 w) (Finset.insert_nonempty 0 w) := by
  let Q := ⌊c * (N : ℝ)⌋₊
  let K := overlapCutoff A c
  let L := (Farey.Fraction.sequence Q).length - 1
  have hN : 0 < N := by omega
  have hNQ : N ≤ Q := by
    apply Nat.le_floor
    have hNreal : (0 : ℝ) ≤ N := by positivity
    nlinarith [show (0 : ℝ) ≤ c * N by positivity]
  have hQ : 0 < Q := hN.trans_le hNQ
  let F : ℕ → Finset ℕ → ℝ := fun i w ↦
    (-1 : ℝ) ^ w.card *
      volume.real
        (⋂ j ∈ insert i (w.image fun d ↦ i + d),
          Farey.activeIntervalAt N Q A j)
  have hlast : F L ∅ = 0 := by
    have hterminal : Farey.activeIntervalAt N Q A L = ∅ := by
      exact Farey.activeIntervalAt_last_eq_empty hQ hN2
    simp [F, hterminal]
  rw [Farey.measureReal_activeApproximationUnion_eq_sum_offset_subsets
    hA hc hN]
  have hsign (w : Finset ℕ) :
      (-1 : ℝ) ^ (w.card + 2) = (-1 : ℝ) ^ w.card := by
    rw [pow_add]
    norm_num
  simp_rw [hsign]
  change (∑ i ∈ Finset.Icc 0 L,
      ∑ w ∈ (Finset.Icc 1 (min K (L - i))).powerset, F i w) = _
  rw [sum_Icc_powerset_min_eq_sum_powerset_sum_range L K F hlast]
  apply Finset.sum_congr rfl
  intro w hw
  rw [inRangeFareyOverlapSum]
  change (∑ i ∈ Finset.range L,
      if ∀ d ∈ w, d ≤ L - i then F i w else 0) =
    (-1 : ℝ) ^ w.card *
      ((∑ i : Farey.ConsecutiveIndex Q,
          if ∀ d ∈ insert 0 w, d ≤ L - i.1 then
            thresholdOverlapIntegrand A ((N : ℝ) / Q)
              (insert 0 w) (Finset.insert_nonempty 0 w)
              (((Farey.consecutivePairAt Q i).1.1.den : ℝ) / Q,
                ((Farey.consecutivePairAt Q i).1.2.den : ℝ) / Q)
          else 0) / (Q : ℝ) ^ 2)
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦
    if ∀ d ∈ w, d ≤ L - i then F i w else 0) L]
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change Farey.ConsecutiveIndex Q at i
  by_cases hrange : ∀ d ∈ w, d ≤ L - i.1
  · have hrange0 : ∀ d ∈ insert 0 w, d ≤ L - i.1 := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · omega
      · exact hrange d hd
    rw [if_pos hrange, if_pos hrange0]
    have hset := Farey.biInter_insert_image_add_eq_biInter_insert_zero
      (fun j ↦ Farey.activeIntervalAt N Q A j) i.1 w
    have hmeasure :=
      Farey.volume_real_activeIntervalAt_biInter_eq_thresholdOverlapIntegrand
        (N := N) (Q := Q) (A := A) hQ i (insert 0 w)
        (Finset.insert_nonempty 0 w) hrange0
    dsimp only [F]
    rw [hset, hmeasure]
    simp only [div_eq_mul_inv]
    ring
  · have hrange0 : ¬ ∀ d ∈ insert 0 w, d ≤ L - i.1 := by
      intro h
      exact hrange fun d hd ↦ h d (Finset.mem_insert_of_mem hd)
    rw [if_neg hrange, if_neg hrange0]
    ring

/-- The finite inclusion--exclusion combination of the primitive Farey
overlap sums at the canonical offset cutoff. -/
noncomputable def normalizedPrimitiveFareyIESum (N : ℕ) (A c : ℝ) : ℝ :=
  ∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
    (-1 : ℝ) ^ J.card *
      normalizedPrimitiveFareyOverlapSum N A c
        (insert 0 J) (Finset.insert_nonempty 0 J)

/-- Alternating sum of the finitely many terminal-edge corrections. -/
noncomputable def normalizedPrimitiveFareyIEBoundarySum
    (N : ℕ) (A c : ℝ) : ℝ :=
  ∑ w ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
    (-1 : ℝ) ^ w.card *
      boundaryFareyOverlapSum N A c
        (insert 0 w) (Finset.insert_nonempty 0 w)

theorem measureReal_activeApproximationUnion_eq_primitiveIESum_sub_boundary
    {N : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (hN2 : 2 ≤ N) :
    volume.real (Farey.activeApproximationUnion N A c) =
      normalizedPrimitiveFareyIESum N A c -
        normalizedPrimitiveFareyIEBoundarySum N A c := by
  rw [measureReal_activeApproximationUnion_eq_inRangeFareyOverlapSum hA hc hN2]
  rw [normalizedPrimitiveFareyIESum, normalizedPrimitiveFareyIEBoundarySum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [normalizedPrimitiveFareyOverlapSum_eq_inRangeFareyOverlapSum_add_boundary]
  ring

theorem S_eq_primitiveIESum_sub_boundary
    {N : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (hN2 : 2 ≤ N) (hAN : A < N) :
    S N A c = normalizedPrimitiveFareyIESum N A c -
      normalizedPrimitiveFareyIEBoundarySum N A c := by
  rw [S, Farey.approximableSet_eq_activeApproximationUnion hN2 hAN hc]
  exact measureReal_activeApproximationUnion_eq_primitiveIESum_sub_boundary
    hA hc hN2

theorem abs_normalizedPrimitiveFareyIEBoundarySum_le
    {N : ℕ} {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c) (hN : 0 < N) :
    |normalizedPrimitiveFareyIEBoundarySum N A c| ≤
      (((Finset.Icc 1 (overlapCutoff A c)).powerset.card : ℕ) : ℝ) *
        ((overlapCutoff A c : ℝ) * (2 * A) / (N : ℝ) ^ 2) := by
  let P := (Finset.Icc 1 (overlapCutoff A c)).powerset
  let B := (overlapCutoff A c : ℝ) * (2 * A) / (N : ℝ) ^ 2
  have hterm (w : Finset ℕ) (hw : w ∈ P) :
      |(-1 : ℝ) ^ w.card *
          boundaryFareyOverlapSum N A c
            (insert 0 w) (Finset.insert_nonempty 0 w)| ≤ B := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    apply abs_boundaryFareyOverlapSum_le hA hc hN
      (Finset.insert_nonempty 0 w) (Finset.mem_insert_self 0 w)
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact Nat.zero_le _
    · exact (Finset.mem_Icc.mp ((Finset.mem_powerset.mp hw) hd)).2
  rw [normalizedPrimitiveFareyIEBoundarySum]
  change |∑ w ∈ P, (-1 : ℝ) ^ w.card *
      boundaryFareyOverlapSum N A c
        (insert 0 w) (Finset.insert_nonempty 0 w)| ≤ (P.card : ℝ) * B
  refine (Finset.abs_sum_le_sum_abs _ P).trans ?_
  have hsum := Finset.sum_le_card_nsmul P
    (fun w ↦ |(-1 : ℝ) ^ w.card *
      boundaryFareyOverlapSum N A c
        (insert 0 w) (Finset.insert_nonempty 0 w)|) B hterm
  simpa [nsmul_eq_mul] using hsum

theorem tendsto_normalizedPrimitiveFareyIEBoundarySum_zero
    {A c : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c) :
    Tendsto (fun N ↦ normalizedPrimitiveFareyIEBoundarySum N A c)
      atTop (nhds 0) := by
  let C : ℝ :=
    (((Finset.Icc 1 (overlapCutoff A c)).powerset.card : ℕ) : ℝ) *
      ((overlapCutoff A c : ℝ) * (2 * A))
  have hden : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun N : ℕ ↦ C / (N : ℝ) ^ 2)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun N ↦ abs_nonneg _)
    _ hmajor
  filter_upwards [eventually_gt_atTop 0] with N hN
  calc
    |normalizedPrimitiveFareyIEBoundarySum N A c| ≤
        (((Finset.Icc 1 (overlapCutoff A c)).powerset.card : ℕ) : ℝ) *
          ((overlapCutoff A c : ℝ) * (2 * A) / (N : ℝ) ^ 2) :=
      abs_normalizedPrimitiveFareyIEBoundarySum_le hA hc hN
    _ = C / (N : ℝ) ^ 2 := by ring

/-- The exact finite inclusion--exclusion formula differs from the full
primitive denominator-pair sum only by a vanishing terminal-edge error. -/
theorem tendsto_S_sub_normalizedPrimitiveFareyIESum_zero
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) :
    Tendsto (fun N ↦ S N A c - normalizedPrimitiveFareyIESum N A c)
      atTop (nhds 0) := by
  have hboundary :=
    (tendsto_normalizedPrimitiveFareyIEBoundarySum_zero hA.le hc).neg
  have hboundary' : Tendsto
      (fun N ↦ -normalizedPrimitiveFareyIEBoundarySum N A c)
      atTop (nhds 0) := by simpa using hboundary
  apply hboundary'.congr'
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop A)] with N hN hAN
  rw [S_eq_primitiveIESum_sub_boundary hA hc (by omega) hAN]
  ring

/-- Final finite-sum assembly with an asymptotically negligible boundary
error.  This is the form appropriate for the final few Farey edges, which
need not have all successors occurring in a fixed offset set. -/
theorem isLimitValue_erdosSzuszTuranLimit_of_overlapSums_error
    (A c : ℝ) (_hA : 0 < A) (_hc : 1 ≤ c)
    (hoverlap : ∀ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
      Tendsto
        (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c
          (insert 0 J) (Finset.insert_nonempty 0 J))
        atTop
        (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle,
            thresholdOverlapIntegrand A (1 / c)
              (insert 0 J) (Finset.insert_nonempty 0 J) p)))
    (herror : Tendsto
      (fun N ↦ S N A c - normalizedPrimitiveFareyIESum N A c)
      atTop (nhds 0)) :
    IsLimitValue A c (erdosSzuszTuranLimit A c) := by
  have hsum : Tendsto (normalizedPrimitiveFareyIESum · A c) atTop
      (nhds (∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          ((6 / Real.pi ^ 2) *
            ∫ p in fareyTriangle,
              thresholdOverlapIntegrand A (1 / c)
                (insert 0 J) (Finset.insert_nonempty 0 J) p))) := by
    unfold normalizedPrimitiveFareyIESum
    apply tendsto_finsetSum
    intro J hJ
    exact tendsto_const_nhds.mul (hoverlap J hJ)
  have hlimit :
      (∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          ((6 / Real.pi ^ 2) *
            ∫ p in fareyTriangle,
              thresholdOverlapIntegrand A (1 / c)
                (insert 0 J) (Finset.insert_nonempty 0 J) p)) =
        erdosSzuszTuranLimit A c := by
    rw [erdosSzuszTuranLimit, ← explicitLimitAtThreshold_one_div]
    rw [explicitLimitAtThreshold, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring
  rw [IsLimitValue, ← hlimit]
  convert herror.add hsum using 1
  · funext N
    ring
  · simp

/-- Final finite-sum assembly.  The two hypotheses expose exactly the
remaining arithmetic/geometric bridges: a fixed-offset visible-lattice
limit, and the eventual exact finite inclusion--exclusion identity for `S`.
-/
theorem isLimitValue_erdosSzuszTuranLimit_of_overlapSums
    (A c : ℝ) (_hA : 0 < A) (_hc : 1 ≤ c)
    (hoverlap : ∀ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
      Tendsto
        (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c
          (insert 0 J) (Finset.insert_nonempty 0 J))
        atTop
        (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle,
            thresholdOverlapIntegrand A (1 / c)
              (insert 0 J) (Finset.insert_nonempty 0 J) p)))
    (hIE : (fun N ↦ S N A c) =ᶠ[atTop]
      fun N ↦ ∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          normalizedPrimitiveFareyOverlapSum N A c
            (insert 0 J) (Finset.insert_nonempty 0 J)) :
    IsLimitValue A c (erdosSzuszTuranLimit A c) := by
  have hsum : Tendsto
      (fun N ↦ ∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          normalizedPrimitiveFareyOverlapSum N A c
            (insert 0 J) (Finset.insert_nonempty 0 J))
      atTop
      (nhds (∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          ((6 / Real.pi ^ 2) *
            ∫ p in fareyTriangle,
              thresholdOverlapIntegrand A (1 / c)
                (insert 0 J) (Finset.insert_nonempty 0 J) p))) := by
    apply tendsto_finsetSum
    intro J hJ
    exact tendsto_const_nhds.mul (hoverlap J hJ)
  have hlimit :
      (∑ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
        (-1 : ℝ) ^ J.card *
          ((6 / Real.pi ^ 2) *
            ∫ p in fareyTriangle,
              thresholdOverlapIntegrand A (1 / c)
                (insert 0 J) (Finset.insert_nonempty 0 J) p)) =
        erdosSzuszTuranLimit A c := by
    rw [erdosSzuszTuranLimit, ← explicitLimitAtThreshold_one_div]
    rw [explicitLimitAtThreshold, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring
  rw [IsLimitValue, ← hlimit]
  exact hsum.congr' hIE.symm

/-! ### Finite convex BCZ itinerary cells -/

namespace BCZCells

/-- A length-`K` BCZ itinerary with entries bounded by `B`. -/
abbrev Itinerary (K B : ℕ) := Fin K → Fin (B + 1)

def coefficient {K B : ℕ} (k : Itinerary K B) (j : ℕ) : ℤ :=
  if h : j < K then (k ⟨j, h⟩ : ℕ) else 0

def cell {K B : ℕ} (k : Itinerary K B) : Set (ℝ × ℝ) :=
  {p | ∀ j, j < K → bczIndex (bczMap^[j] p) = coefficient k j}

def denominatorCoefficients {K B : ℕ} (k : Itinerary K B) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | j + 2 =>
      (coefficient k j * (denominatorCoefficients k (j + 1)).1 -
          (denominatorCoefficients k j).1,
        coefficient k j * (denominatorCoefficients k (j + 1)).2 -
          (denominatorCoefficients k j).2)

def denominator {K B : ℕ} (k : Itinerary K B) (j : ℕ)
    (p : ℝ × ℝ) : ℝ :=
  (denominatorCoefficients k j).1 * p.1 +
    (denominatorCoefficients k j).2 * p.2

@[simp] lemma denominator_zero {K B : ℕ} (k : Itinerary K B)
    (p : ℝ × ℝ) : denominator k 0 p = p.1 := by
  simp [denominator, denominatorCoefficients]

@[simp] lemma denominator_one {K B : ℕ} (k : Itinerary K B)
    (p : ℝ × ℝ) : denominator k 1 p = p.2 := by
  simp [denominator, denominatorCoefficients]

lemma denominator_add_two {K B : ℕ} (k : Itinerary K B)
    (j : ℕ) (p : ℝ × ℝ) :
    denominator k (j + 2) p =
      (coefficient k j : ℝ) * denominator k (j + 1) p - denominator k j p := by
  simp only [denominator, denominatorCoefficients]
  push_cast
  ring

lemma continuous_denominator {K B : ℕ} (k : Itinerary K B) (j : ℕ) :
    Continuous (denominator k j) :=
  (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

lemma normalizedDenominator_eq_denominator {K B : ℕ}
    (k : Itinerary K B) {p : ℝ × ℝ} (hp : p ∈ cell k)
    {j : ℕ} (hj : j ≤ K + 1) :
    normalizedDenominator j p = denominator k j p := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j ih₀ ih₁ =>
      have hjK : j < K := by omega
      rw [normalizedDenominator_add_two, denominator_add_two, hp j hjK,
        ih₀ (by omega), ih₁ (by omega)]

def clippedDenominator {K B : ℕ} (k : Itinerary K B)
    (δ : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  max δ (denominator k j p)

lemma continuous_clippedDenominator {K B : ℕ}
    (k : Itinerary K B) (δ : ℝ) (j : ℕ) :
    Continuous (clippedDenominator k δ j) :=
  continuous_const.max (continuous_denominator k j)

def gapExtension {K B : ℕ} (k : Itinerary K B)
    (δ : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.range j,
    1 / (clippedDenominator k δ ℓ p * clippedDenominator k δ (ℓ + 1) p)

lemma continuous_gapExtension {K B : ℕ}
    (k : Itinerary K B) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    Continuous (gapExtension k δ j) := by
  apply continuous_finsetSum
  intro ℓ hℓ
  apply continuous_const.div
  · exact (continuous_clippedDenominator k δ ℓ).mul
      (continuous_clippedDenominator k δ (ℓ + 1))
  · intro p
    have hℓ₀ : 0 < clippedDenominator k δ ℓ p :=
      hδ.trans_le (le_max_left _ _)
    have hℓ₁ : 0 < clippedDenominator k δ (ℓ + 1) p :=
      hδ.trans_le (le_max_left _ _)
    positivity

def upperExtension {K B : ℕ} (k : Itinerary K B)
    (δ A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  gapExtension k δ j p + A / clippedDenominator k δ j p ^ 2

def lowerExtension {K B : ℕ} (k : Itinerary K B)
    (δ A : ℝ) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  gapExtension k δ j p - A / clippedDenominator k δ j p ^ 2

lemma continuous_upperExtension {K B : ℕ} (k : Itinerary K B)
    {δ : ℝ} (hδ : 0 < δ) (A : ℝ) (j : ℕ) :
    Continuous (upperExtension k δ A j) := by
  apply (continuous_gapExtension k hδ j).add
  apply continuous_const.div
  · exact (continuous_clippedDenominator k δ j).pow 2
  · intro p
    have : 0 < clippedDenominator k δ j p := hδ.trans_le (le_max_left _ _)
    positivity

lemma continuous_lowerExtension {K B : ℕ} (k : Itinerary K B)
    {δ : ℝ} (hδ : 0 < δ) (A : ℝ) (j : ℕ) :
    Continuous (lowerExtension k δ A j) := by
  apply (continuous_gapExtension k hδ j).sub
  apply continuous_const.div
  · exact (continuous_clippedDenominator k δ j).pow 2
  · intro p
    have : 0 < clippedDenominator k δ j p := hδ.trans_le (le_max_left _ _)
    positivity

lemma continuous_image_min'
    {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x ↦ (s.image (fun i ↦ f i x)).min' (hs.image _)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | @cons a s ha ih =>
      by_cases hs' : s.Nonempty
      · have hrest := ih hs' (fun i hi ↦ hf i (by simp [hi]))
        simpa only [Finset.cons_eq_insert, Finset.image_insert,
          Finset.min'_insert _ _ (hs'.image _)] using (hf a (by simp)).min hrest
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf a (by simp)

lemma continuous_image_max'
    {X ι : Type*} [TopologicalSpace X] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x ↦ (s.image (fun i ↦ f i x)).max' (hs.image _)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | @cons a s ha ih =>
      by_cases hs' : s.Nonempty
      · have hrest := ih hs' (fun i hi ↦ hf i (by simp [hi]))
        simpa only [Finset.cons_eq_insert, Finset.image_insert,
          Finset.max'_insert _ _ (hs'.image _)] using (hf a (by simp)).max hrest
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf a (by simp)

def overlapExtension {K B : ℕ} (k : Itinerary K B)
    (δ A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) (p : ℝ × ℝ) : ℝ :=
  max 0
    ((J.image (fun j ↦ upperExtension k δ A j p)).min' (hJ.image _) -
      (J.image (fun j ↦ lowerExtension k δ A j p)).max' (hJ.image _))

lemma continuous_overlapExtension {K B : ℕ} (k : Itinerary K B)
    {δ : ℝ} (hδ : 0 < δ) (A : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) :
    Continuous (overlapExtension k δ A J hJ) := by
  apply continuous_const.max
  apply Continuous.sub
  · exact continuous_image_min' J hJ _
      (fun j _ ↦ continuous_upperExtension k hδ A j)
  · exact continuous_image_max' J hJ _
      (fun j _ ↦ continuous_lowerExtension k hδ A j)

lemma overlapExtension_eq_finiteOverlapLength {K B : ℕ}
    (k : Itinerary K B) {δ A : ℝ} (J : Finset ℕ) (hJ : J.Nonempty)
    {p : ℝ × ℝ} (hp : p ∈ cell k) {m : ℕ}
    (hmK : m ≤ K + 1) (hJm : ∀ j ∈ J, j ≤ m)
    (hstrip : ∀ ℓ ≤ m, δ ≤ normalizedDenominator ℓ p) :
    overlapExtension k δ A J hJ p = finiteOverlapLength A J hJ p := by
  have hclip (j : ℕ) (hj : j ≤ m) :
      clippedDenominator k δ j p = normalizedDenominator j p := by
    rw [clippedDenominator, ← normalizedDenominator_eq_denominator k hp (hj.trans hmK)]
    exact max_eq_right (hstrip j hj)
  have hgap (j : ℕ) (hj : j ≤ m) : gapExtension k δ j p = normalizedGap j p := by
    rw [gapExtension, normalizedGap]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hℓj := Finset.mem_range.mp hℓ
    rw [hclip ℓ (by omega), hclip (ℓ + 1) (by omega)]
  have hu (j : ℕ) (hj : j ≤ m) :
      upperExtension k δ A j p = normalizedUpperEndpoint A j p := by
    rw [upperExtension, normalizedUpperEndpoint, hgap j hj, hclip j hj]
  have hl (j : ℕ) (hj : j ≤ m) :
      lowerExtension k δ A j p = normalizedLowerEndpoint A j p := by
    rw [lowerExtension, normalizedLowerEndpoint, hgap j hj, hclip j hj]
  have hU : J.image (fun j ↦ upperExtension k δ A j p) =
      J.image (fun j ↦ normalizedUpperEndpoint A j p) := by
    apply Finset.image_congr
    intro j hj
    exact hu j (hJm j hj)
  have hL : J.image (fun j ↦ lowerExtension k δ A j p) =
      J.image (fun j ↦ normalizedLowerEndpoint A j p) := by
    apply Finset.image_congr
    intro j hj
    exact hl j (hJm j hj)
  simp only [overlapExtension, finiteOverlapLength, hU, hL]

lemma denominator_affineCombination {K B : ℕ}
    (k : Itinerary K B) (j : ℕ) (a b : ℝ) (p q : ℝ × ℝ) :
    denominator k j (a • p + b • q) = a * denominator k j p + b * denominator k j q := by
  simp only [denominator, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

def affineCell {K B : ℕ} (k : Itinerary K B) : Set (ℝ × ℝ) :=
  {p | ∀ j, j < K →
    (coefficient k j : ℝ) * denominator k (j + 1) p ≤ 1 + denominator k j p ∧
      1 + denominator k j p < ((coefficient k j : ℝ) + 1) * denominator k (j + 1) p}

def strip {K B : ℕ} (k : Itinerary K B) (δ : ℝ) (m : ℕ) : Set (ℝ × ℝ) :=
  {p | ∀ j ≤ m, δ ≤ denominator k j p}

def cutoffRegion {K B : ℕ} (k : Itinerary K B)
    (c : ℝ) (J : Finset ℕ) : Set (ℝ × ℝ) :=
  {p | ∀ j ∈ J, 1 / c ≤ denominator k j p}

def pairDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : Set (ℝ × ℝ) :=
  fareyTriangle ∩ affineCell k ∩ strip k δ m ∩ cutoffRegion k c J

def finTwoToPair (x : Fin 2 → ℝ) : ℝ × ℝ := (x 0, x 1)

lemma continuous_finTwoToPair : Continuous finTwoToPair :=
  (continuous_apply 0).prodMk (continuous_apply 1)

def finTwoToPairLinear : (Fin 2 → ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := finTwoToPair
  map_add' := by intro x y; ext <;> simp [finTwoToPair]
  map_smul' := by intro a x; ext <;> simp [finTwoToPair]

def finTwoDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : Set (Fin 2 → ℝ) :=
  finTwoToPairLinear ⁻¹' pairDomain k δ c J m

lemma le_combo {a b c x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : c ≤ x) (hy : c ≤ y) : c ≤ a * x + b * y := by
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * x + b * y := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma combo_le {a b c x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : x ≤ c) (hy : y ≤ c) : a * x + b * y ≤ c := by
  calc
    a * x + b * y ≤ a * c + b * c := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = c := by rw [← add_mul, hab, one_mul]

lemma lt_combo {a b c x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : c < x) (hy : c < y) : c < a * x + b * y := by
  rcases lt_or_eq_of_le ha with ha' | rfl
  · calc
      c = a * c + b * c := by rw [← add_mul, hab, one_mul]
      _ < a * x + b * y := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hx ha') (mul_le_mul_of_nonneg_left hy.le hb)
  · have hb1 : b = 1 := by linarith
    subst b
    simpa using hy

lemma combo_mono {a b x₀ x₁ y₀ y₁ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) :
    a * x₀ + b * y₀ ≤ a * x₁ + b * y₁ :=
  add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma combo_lt {a b x₀ x₁ y₀ y₁ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x₀ < x₁) (hy : y₀ < y₁) :
    a * x₀ + b * y₀ < a * x₁ + b * y₁ := by
  rcases lt_or_eq_of_le ha with ha' | rfl
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx ha')
      (mul_le_mul_of_nonneg_left hy.le hb)
  · have hb1 : b = 1 := by linarith
    subst b
    simpa using hy

lemma convex_farey : Convex ℝ fareyTriangle := by
  intro p hp q hq a b ha hb hab
  change 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 ∧ 1 < p.1 + p.2 at hp
  change 0 < q.1 ∧ q.1 ≤ 1 ∧ 0 < q.2 ∧ q.2 ≤ 1 ∧ 1 < q.1 + q.2 at hq
  change 0 < (a • p + b • q).1 ∧ (a • p + b • q).1 ≤ 1 ∧
    0 < (a • p + b • q).2 ∧ (a • p + b • q).2 ≤ 1 ∧
      1 < (a • p + b • q).1 + (a • p + b • q).2
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rcases hp with ⟨hp₀, hp₁, hp₂, hp₃, hp₄⟩
  rcases hq with ⟨hq₀, hq₁, hq₂, hq₃, hq₄⟩
  exact ⟨lt_combo ha hb hab hp₀ hq₀, combo_le ha hb hab hp₁ hq₁,
    lt_combo ha hb hab hp₂ hq₂, combo_le ha hb hab hp₃ hq₃,
    by have h := lt_combo ha hb hab hp₄ hq₄; nlinarith⟩

lemma convex_affineCell {K B : ℕ} (k : Itinerary K B) : Convex ℝ (affineCell k) := by
  intro p hp q hq a b ha hb hab j hj
  have hpj := hp j hj
  have hqj := hq j hj
  rw [denominator_affineCombination, denominator_affineCombination]
  constructor
  · have h := combo_mono ha hb hpj.1 hqj.1; nlinarith
  · have h := combo_lt ha hb hab hpj.2 hqj.2; nlinarith

lemma convex_strip {K B : ℕ} (k : Itinerary K B) (δ : ℝ) (m : ℕ) :
    Convex ℝ (strip k δ m) := by
  intro p hp q hq a b ha hb hab j hj
  rw [denominator_affineCombination]
  exact le_combo ha hb hab (hp j hj) (hq j hj)

lemma convex_cutoffRegion {K B : ℕ} (k : Itinerary K B) (c : ℝ) (J : Finset ℕ) :
    Convex ℝ (cutoffRegion k c J) := by
  intro p hp q hq a b ha hb hab j hj
  rw [denominator_affineCombination]
  exact le_combo ha hb hab (hp j hj) (hq j hj)

lemma convex_pairDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : Convex ℝ (pairDomain k δ c J m) :=
  ((convex_farey.inter (convex_affineCell k)).inter (convex_strip k δ m)).inter
    (convex_cutoffRegion k c J)

lemma convex_finTwoDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : Convex ℝ (finTwoDomain k δ c J m) :=
  (convex_pairDomain k δ c J m).linear_preimage finTwoToPairLinear

lemma measurableSet_affineCell {K B : ℕ} (k : Itinerary K B) :
    MeasurableSet (affineCell k) := by
  rw [show affineCell k =
      (⋂ j : ℕ, ⋂ (_ : j < K), {p : ℝ × ℝ |
        (coefficient k j : ℝ) * denominator k (j + 1) p ≤ 1 + denominator k j p ∧
          1 + denominator k j p < ((coefficient k j : ℝ) + 1) * denominator k (j + 1) p}) by
    ext p; simp [affineCell]]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact (measurableSet_le
      (measurable_const.mul (continuous_denominator k (j + 1)).measurable)
      (measurable_const.add (continuous_denominator k j).measurable)).inter
    (measurableSet_lt
      (measurable_const.add (continuous_denominator k j).measurable)
      (measurable_const.mul (continuous_denominator k (j + 1)).measurable))

lemma measurableSet_strip {K B : ℕ} (k : Itinerary K B) (δ : ℝ) (m : ℕ) :
    MeasurableSet (strip k δ m) := by
  rw [show strip k δ m = ⋂ j : ℕ, ⋂ (_ : j ≤ m),
      {p : ℝ × ℝ | δ ≤ denominator k j p} by ext p; simp [strip]]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le measurable_const (continuous_denominator k j).measurable

lemma measurableSet_cutoffRegion {K B : ℕ} (k : Itinerary K B)
    (c : ℝ) (J : Finset ℕ) : MeasurableSet (cutoffRegion k c J) := by
  rw [show cutoffRegion k c J = ⋂ j : ℕ, ⋂ (_ : j ∈ J),
      {p : ℝ × ℝ | 1 / c ≤ denominator k j p} by ext p; simp [cutoffRegion]]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le measurable_const (continuous_denominator k j).measurable

lemma measurableSet_pairDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : MeasurableSet (pairDomain k δ c J m) :=
  (((measurableSet_fareyTriangle.inter (measurableSet_affineCell k)).inter
    (measurableSet_strip k δ m)).inter (measurableSet_cutoffRegion k c J))

lemma measurableSet_finTwoDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : MeasurableSet (finTwoDomain k δ c J m) :=
  (measurableSet_pairDomain k δ c J m).preimage continuous_finTwoToPair.measurable

lemma isBounded_finTwoDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : Bornology.IsBounded (finTwoDomain k δ c J m) := by
  apply (Metric.isBounded_Icc (0 : Fin 2 → ℝ) 1).subset
  intro x hx
  have htri := hx.1.1.1
  change 0 < (finTwoToPair x).1 ∧ (finTwoToPair x).1 ≤ 1 ∧
    0 < (finTwoToPair x).2 ∧ (finTwoToPair x).2 ≤ 1 ∧
      1 < (finTwoToPair x).1 + (finTwoToPair x).2 at htri
  rw [mem_Icc]
  constructor <;> intro i
  · fin_cases i <;> simp [finTwoToPair] at htri ⊢
    · exact htri.1.le
    · exact htri.2.2.1.le
  · fin_cases i <;> simp [finTwoToPair] at htri ⊢
    · exact htri.2.1
    · exact htri.2.2.2.1

lemma volume_frontier_finTwoDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) : volume (frontier (finTwoDomain k δ c J m)) = 0 :=
  (convex_finTwoDomain k δ c J m).addHaar_frontier volume

lemma index_eq_coefficient_of_affine {K B : ℕ} (k : Itinerary K B)
    {p : ℝ × ℝ} (hp : p ∈ affineCell k) {j : ℕ} (hj : j < K)
    (hden₀ : normalizedDenominator j p = denominator k j p)
    (hden₁ : normalizedDenominator (j + 1) p = denominator k (j + 1) p)
    (hpos : 0 < denominator k (j + 1) p) :
    bczIndex (bczMap^[j] p) = coefficient k j := by
  have hfst : (bczMap^[j] p).1 = normalizedDenominator j p := rfl
  have hsnd : (bczMap^[j] p).2 = normalizedDenominator (j + 1) p := by
    rw [normalizedDenominator, Function.iterate_succ_apply']
    rfl
  rw [bczIndex, Int.floor_eq_iff, hfst, hsnd, hden₀, hden₁]
  exact ⟨(le_div_iff₀ hpos).2 (hp j hj).1, (div_lt_iff₀ hpos).2 (hp j hj).2⟩

lemma normalizedDenominator_eq_denominator_of_affine {K B : ℕ}
    (k : Itinerary K B) {p : ℝ × ℝ} (hp : p ∈ affineCell k)
    (hpos : ∀ j ≤ K + 1, 0 < denominator k j p) {j : ℕ} (hj : j ≤ K + 1) :
    normalizedDenominator j p = denominator k j p := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j ih₀ ih₁ =>
      have hjK : j < K := by omega
      have hidx := index_eq_coefficient_of_affine k hp hjK
        (ih₀ (by omega)) (ih₁ (by omega)) (hpos (j + 1) (by omega))
      rw [normalizedDenominator_add_two, denominator_add_two, hidx,
        ih₀ (by omega), ih₁ (by omega)]

lemma affineCell_subset_cell_of_pos {K B : ℕ} (k : Itinerary K B)
    {p : ℝ × ℝ} (hp : p ∈ affineCell k)
    (hpos : ∀ j ≤ K + 1, 0 < denominator k j p) : p ∈ cell k := by
  intro j hj
  exact index_eq_coefficient_of_affine k hp hj
    (normalizedDenominator_eq_denominator_of_affine k hp hpos (by omega))
    (normalizedDenominator_eq_denominator_of_affine k hp hpos (by omega))
    (hpos (j + 1) (by omega))

lemma overlapExtension_eq_cutoff_on_pairDomain {K B : ℕ}
    (k : Itinerary K B) {δ c A : ℝ} (hδ : 0 < δ)
    (J : Finset ℕ) (hJ : J.Nonempty) (hJbound : ∀ j ∈ J, j ≤ K + 1)
    {p : ℝ × ℝ} (hp : p ∈ pairDomain k δ c J (K + 1)) :
    overlapExtension k δ A J hJ p = cutoffOverlapIntegrand A c J hJ p := by
  rcases hp with ⟨⟨⟨htri, haff⟩, hstrip⟩, hcut⟩
  have hpos : ∀ j ≤ K + 1, 0 < denominator k j p :=
    fun j hj ↦ hδ.trans_le (hstrip j hj)
  have hbcz : p ∈ cell k := affineCell_subset_cell_of_pos k haff hpos
  have heq (j : ℕ) (hj : j ≤ K + 1) :
      normalizedDenominator j p = denominator k j p :=
    normalizedDenominator_eq_denominator_of_affine k haff hpos hj
  have hnormstrip : ∀ j ≤ K + 1, δ ≤ normalizedDenominator j p := by
    intro j hj
    rw [heq j hj]
    exact hstrip j hj
  have hext : overlapExtension k δ A J hJ p = finiteOverlapLength A J hJ p :=
    overlapExtension_eq_finiteOverlapLength k J hJ hbcz le_rfl hJbound hnormstrip
  have hnormcut : ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p := by
    intro j hj
    rw [heq j (hJbound j hj)]
    exact hcut j hj
  rw [cutoffOverlapIntegrand, if_pos hnormcut, hext]

/-- An unconditional integer-grid Riemann theorem for one convex itinerary
cell, stated using the original overlap integrand on both sides. -/
lemma tendsto_integerGrid_cutoff_on_cell {K B : ℕ} (k : Itinerary K B)
    {δ : ℝ} (hδ : 0 < δ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (hJbound : ∀ j ∈ J, j ≤ K + 1) :
    let s := finTwoDomain k δ c J (K + 1)
    Tendsto
      (fun n : ℕ ↦ ((∑' x : ↑(s ∩
        (n : ℝ)⁻¹ • (Submodule.span ℤ
          (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))),
          cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) / n ^ 2))
      atTop
      (nhds (∫ x in s, cutoffOverlapIntegrand A c J hJ (finTwoToPair x))) := by
  dsimp only
  let s := finTwoDomain k δ c J (K + 1)
  have hsmeas : MeasurableSet s := measurableSet_finTwoDomain k δ c J (K + 1)
  have heq (x : Fin 2 → ℝ) (hx : x ∈ s) :
      overlapExtension k δ A J hJ (finTwoToPair x) =
        cutoffOverlapIntegrand A c J hJ (finTwoToPair x) :=
    overlapExtension_eq_cutoff_on_pairDomain k hδ J hJ hJbound hx
  have ht := tendsto_tsum_div_pow_atTop_integral s
    (fun x : Fin 2 → ℝ ↦ overlapExtension k δ A J hJ (finTwoToPair x))
    ((continuous_overlapExtension k hδ A J hJ).comp continuous_finTwoToPair)
    (isBounded_finTwoDomain k δ c J (K + 1)) hsmeas
    (volume_frontier_finTwoDomain k δ c J (K + 1))
  have hseq :
      (fun n : ℕ ↦ ((∑' x : ↑(s ∩
        (n : ℝ)⁻¹ • (Submodule.span ℤ
          (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))),
          cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) / n ^ 2)) =
      (fun n : ℕ ↦ ((∑' x : ↑(s ∩
        (n : ℝ)⁻¹ • (Submodule.span ℤ
          (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))),
          overlapExtension k δ A J hJ (finTwoToPair x)) / n ^ 2)) := by
    funext n
    congr 1
    apply tsum_congr
    intro x
    exact (heq x x.property.1).symm
  have hint :
      (∫ x in s, cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) =
        ∫ x in s, overlapExtension k δ A J hJ (finTwoToPair x) :=
    setIntegral_congr_fun hsmeas fun x hx ↦ (heq x hx).symm
  rw [hseq, hint]
  simpa using ht

lemma cell_subset_affineCell {K B : ℕ} (k : Itinerary K B)
    {p : ℝ × ℝ} (hp : p ∈ cell k)
    (hnormpos : ∀ j ≤ K + 1, 0 < normalizedDenominator j p) : p ∈ affineCell k := by
  intro j hj
  have hjval := hp j hj
  have hfloor :
      (coefficient k j : ℝ) ≤ (1 + (bczMap^[j] p).1) / (bczMap^[j] p).2 ∧
        (1 + (bczMap^[j] p).1) / (bczMap^[j] p).2 < (coefficient k j : ℝ) + 1 := by
    rw [← Int.floor_eq_iff]
    exact hjval
  have hfst : (bczMap^[j] p).1 = normalizedDenominator j p := rfl
  have hsnd : (bczMap^[j] p).2 = normalizedDenominator (j + 1) p := by
    rw [normalizedDenominator, Function.iterate_succ_apply']
    rfl
  have hpos := hnormpos (j + 1) (by omega)
  rw [hfst, hsnd] at hfloor
  have heq₀ := normalizedDenominator_eq_denominator (K := K) (B := B) (j := j) k hp (by omega)
  have heq₁ := normalizedDenominator_eq_denominator (K := K) (B := B) k hp
    (by omega : j + 1 ≤ K + 1)
  rw [heq₀, heq₁] at hfloor
  rw [heq₁] at hpos
  exact ⟨(le_div_iff₀ hpos).1 hfloor.1, (div_lt_iff₀ hpos).1 hfloor.2⟩

lemma index_cast_le_two_div_of_bounds {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    {K j : ℕ} (hj : j < K) {δ : ℝ} (hδ : 0 < δ)
    (hlo : ∀ m ≤ K + 1, δ ≤ normalizedDenominator m p) :
    (bczIndex (bczMap^[j] p) : ℝ) ≤ 2 / δ := by
  have hindex : (0 : ℝ) ≤ bczIndex (bczMap^[j] p) := by
    exact_mod_cast (bczIndex_pos (bczMap_iterate_mem_fareyTriangle hp j)).le
  have hrec := normalizedDenominator_add_two j p
  have hmul : (bczIndex (bczMap^[j] p) : ℝ) * δ ≤ 2 := by
    calc
      (bczIndex (bczMap^[j] p) : ℝ) * δ ≤
          (bczIndex (bczMap^[j] p) : ℝ) * normalizedDenominator (j + 1) p :=
        mul_le_mul_of_nonneg_left (hlo _ (by omega)) hindex
      _ = normalizedDenominator (j + 2) p + normalizedDenominator j p := by linarith
      _ ≤ 1 + 1 := add_le_add (normalizedDenominator_le_one hp _) (normalizedDenominator_le_one hp _)
      _ = 2 := by norm_num
  exact (le_div_iff₀ hδ).2 hmul

lemma exists_bounded_cell_of_bounds {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    {K B : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hlo : ∀ m ≤ K + 1, δ ≤ normalizedDenominator m p)
    (hB : 2 / δ < (B + 1 : ℕ)) : ∃ k : Itinerary K B, p ∈ cell k := by
  have hpos (j : ℕ) : 0 < bczIndex (bczMap^[j] p) :=
    bczIndex_pos (bczMap_iterate_mem_fareyTriangle hp j)
  have hlt (j : ℕ) (hj : j < K) : (bczIndex (bczMap^[j] p)).toNat < B + 1 := by
    apply (Int.toNat_lt (hpos j).le).2
    have hreal : (bczIndex (bczMap^[j] p) : ℝ) < (B + 1 : ℕ) :=
      (index_cast_le_two_div_of_bounds hp hj hδ hlo).trans_lt hB
    exact_mod_cast hreal
  let k : Itinerary K B := fun j ↦
    ⟨(bczIndex (bczMap^[j.1] p)).toNat, hlt j.1 j.2⟩
  refine ⟨k, ?_⟩
  intro j hj
  rw [coefficient, dif_pos hj]
  change bczIndex (bczMap^[j] p) = ((bczIndex (bczMap^[j] p)).toNat : ℕ)
  exact (Int.toNat_of_nonneg (hpos j).le).symm

lemma exists_pairDomain_of_cutoff_pos
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (hpos : 0 < cutoffOverlapIntegrand A c J hJ p)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    ∃ k : Itinerary K B, p ∈ pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1) := by
  have hmax : J.max' hJ = K + 1 := by
    apply le_antisymm
    · exact hJbound _ (Finset.max'_mem J hJ)
    · exact Finset.le_max' J _ hK
  have hlower : ∀ m ≤ K + 1,
      1 / (2 * A * c ^ 2) ≤ normalizedDenominator m p := by
    intro m hm
    rcases lt_or_eq_of_le hm with hm' | rfl
    · have h := cutoffOverlapIntegrand_pos_imp_intermediateDenominators_lower
        hA hc hJ h0 hp hpos (show m < J.max' hJ by rw [hmax]; exact hm')
      exact h.1.le
    · have h := cutoffOverlapIntegrand_pos_imp_intermediateDenominators_lower
        hA hc hJ h0 hp hpos (show K < J.max' hJ by simp [hmax])
      simpa using h.2.le
  have hδ : 0 < 1 / (2 * A * c ^ 2) := by positivity
  have hB' : 2 / (1 / (2 * A * c ^ 2)) < (B + 1 : ℕ) := by
    convert hB using 1 <;> field_simp <;> ring
  obtain ⟨k, hk⟩ := exists_bounded_cell_of_bounds hp hδ hlower hB'
  refine ⟨k, ?_⟩
  have hnormpos : ∀ j ≤ K + 1, 0 < normalizedDenominator j p :=
    fun j _ ↦ normalizedDenominator_pos hp j
  have haff := cell_subset_affineCell k hk hnormpos
  have hstrip : p ∈ strip k (1 / (2 * A * c ^ 2)) (K + 1) := by
    intro j hj
    rw [← normalizedDenominator_eq_denominator k hk hj]
    exact hlower j hj
  have hcutNorm : ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p := by
    rw [cutoffOverlapIntegrand] at hpos
    split_ifs at hpos with hcut
    · exact hcut
    · simp at hpos
  have hcut : p ∈ cutoffRegion k c J := by
    intro j hj
    rw [← normalizedDenominator_eq_denominator k hk (hJbound j hj)]
    exact hcutNorm j hj
  exact ⟨⟨⟨hp, haff⟩, hstrip⟩, hcut⟩

lemma pairDomain_unique {K B : ℕ} {k l : Itinerary K B} {δ c : ℝ}
    (hδ : 0 < δ) (J : Finset ℕ) {p : ℝ × ℝ}
    (hpk : p ∈ pairDomain k δ c J (K + 1))
    (hpl : p ∈ pairDomain l δ c J (K + 1)) : k = l := by
  have hkpos : ∀ j ≤ K + 1, 0 < denominator k j p := fun j hj ↦ hδ.trans_le (hpk.1.2 j hj)
  have hlpos : ∀ j ≤ K + 1, 0 < denominator l j p := fun j hj ↦ hδ.trans_le (hpl.1.2 j hj)
  have hkc := affineCell_subset_cell_of_pos k hpk.1.1.2 hkpos
  have hlc := affineCell_subset_cell_of_pos l hpl.1.1.2 hlpos
  funext i
  have hi : coefficient k i = coefficient l i := (hkc i i.2).symm.trans (hlc i i.2)
  apply Fin.ext
  simpa [coefficient, i.2] using hi

def finiteDecomposition {K B : ℕ} (δ A c : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) (p : ℝ × ℝ) : ℝ :=
  ∑ k : Itinerary K B, (pairDomain k δ c J (K + 1)).indicator
    (overlapExtension k δ A J hJ) p

lemma finiteDecomposition_eq_cutoff
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1) (hB : 4 * A * c ^ 2 < (B + 1 : ℕ))
    (p : ℝ × ℝ) (hp : p ∈ fareyTriangle) :
    finiteDecomposition (K := K) (B := B) (1 / (2 * A * c ^ 2)) A c J hJ p =
      cutoffOverlapIntegrand A c J hJ p := by
  classical
  let δ : ℝ := 1 / (2 * A * c ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_cases hne : cutoffOverlapIntegrand A c J hJ p = 0
  · rw [hne]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Set.indicator]
    split_ifs with hmem
    · rw [overlapExtension_eq_cutoff_on_pairDomain k hδ J hJ hJbound hmem, hne]
    · rfl
  · have hpos : 0 < cutoffOverlapIntegrand A c J hJ p :=
      lt_of_le_of_ne (cutoffOverlapIntegrand_nonneg A c J hJ p) (Ne.symm hne)
    obtain ⟨k₀, hk₀⟩ := exists_pairDomain_of_cutoff_pos
      hA hc J hJ h0 hK hJbound hp hpos hB
    change (∑ k : Itinerary K B, (pairDomain k δ c J (K + 1)).indicator
      (overlapExtension k δ A J hJ) p) = _
    rw [Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hk₀,
        overlapExtension_eq_cutoff_on_pairDomain k₀ hδ J hJ hJbound hk₀]
    · intro k hk hkk₀
      have hnot : p ∉ pairDomain k δ c J (K + 1) := by
        intro hmem
        exact hkk₀ (pairDomain_unique hδ J hmem hk₀)
      simp [Set.indicator, hnot]
    · simp

lemma pairDomain_subset_Icc {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) :
    pairDomain k δ c J m ⊆ Set.Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
  intro p hp
  rcases hp.1.1.1 with ⟨hp₀, hp₁, hp₂, hp₃, hp₄⟩
  exact ⟨⟨hp₀.le, hp₂.le⟩, hp₁, hp₃⟩

lemma pairDomain_subset_fareyTriangle {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) :
    pairDomain k δ c J m ⊆ fareyTriangle := fun _ hp ↦ hp.1.1.1

lemma finTwoDomain_subset_fareyTrianglePi {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) :
    finTwoDomain k δ c J m ⊆ VisibleLattice.fareyTrianglePi := by
  intro x hx
  have htri := hx.1.1.1
  change 0 < x 0 ∧ x 0 ≤ 1 ∧ 0 < x 1 ∧ x 1 ≤ 1 ∧ 1 < x 0 + x 1
  exact htri

/-- Passing between pair coordinates and `Fin 2` coordinates preserves the
set integral; this is the coordinate form used by the lattice Riemann theorem. -/
lemma setIntegral_finTwoDomain_eq_pairDomain {K B : ℕ} (k : Itinerary K B)
    (δ c : ℝ) (J : Finset ℕ) (m : ℕ) (f : ℝ × ℝ → ℝ) :
    (∫ x in finTwoDomain k δ c J m, f (finTwoToPair x)) =
      ∫ p in pairDomain k δ c J m, f p := by
  have hpres := volume_preserving_finTwoArrow ℝ
  have hemb : MeasurableEmbedding (@MeasurableEquiv.finTwoArrow ℝ _) :=
    MeasurableEquiv.finTwoArrow.measurableEmbedding
  have h := hpres.setIntegral_preimage_emb hemb f (pairDomain k δ c J m)
  change
    (∫ x in (fun x : Fin 2 → ℝ => (x 0, x 1)) ⁻¹' pairDomain k δ c J m,
      f (x 0, x 1)) = _
  exact h

lemma integrableOn_overlapExtension_pairDomain
    {K B : ℕ} (k : Itinerary K B) {δ : ℝ} (hδ : 0 < δ)
    (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) (m : ℕ) :
    IntegrableOn (overlapExtension k δ A J hJ) (pairDomain k δ c J m) :=
  ((continuous_overlapExtension k hδ A J hJ).integrableOn_Icc).mono_set
    (pairDomain_subset_Icc k δ c J m)

lemma integral_finTwoDomain_cutoff_eq_pairDomain_overlap
    {K B : ℕ} (k : Itinerary K B) {δ : ℝ} (hδ : 0 < δ)
    (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty)
    (hJbound : ∀ j ∈ J, j ≤ K + 1) :
    (∫ x in finTwoDomain k δ c J (K + 1),
      cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) =
      ∫ p in pairDomain k δ c J (K + 1), overlapExtension k δ A J hJ p := by
  calc
    (∫ x in finTwoDomain k δ c J (K + 1),
        cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) =
        ∫ x in finTwoDomain k δ c J (K + 1),
          overlapExtension k δ A J hJ (finTwoToPair x) :=
      setIntegral_congr_fun (measurableSet_finTwoDomain k δ c J (K + 1)) fun x hx ↦
        (overlapExtension_eq_cutoff_on_pairDomain k hδ J hJ hJbound hx).symm
    _ = ∫ p in pairDomain k δ c J (K + 1), overlapExtension k δ A J hJ p :=
      setIntegral_finTwoDomain_eq_pairDomain k δ c J (K + 1)
        (overlapExtension k δ A J hJ)

/-- The cutoff overlap integral is exactly a finite sum of integrals over
the bounded convex BCZ itinerary/cutoff cells. -/
lemma integral_finiteDecomposition
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1) (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    (∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p) =
      ∑ k : Itinerary K B,
        ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
          overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p := by
  classical
  let δ : ℝ := 1 / (2 * A * c ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  calc
    (∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p) =
        ∫ p in fareyTriangle, finiteDecomposition (K := K) (B := B) δ A c J hJ p :=
      setIntegral_congr_fun measurableSet_fareyTriangle fun p hp ↦
        (finiteDecomposition_eq_cutoff hA hc J hJ h0 hK hJbound hB p hp).symm
    _ = ∑ k : Itinerary K B, ∫ p in fareyTriangle,
          (pairDomain k δ c J (K + 1)).indicator
            (overlapExtension k δ A J hJ) p := by
      unfold finiteDecomposition
      apply integral_finsetSum
      intro k hk
      exact ((integrableOn_overlapExtension_pairDomain k hδ A c J hJ (K + 1)).integrable_indicator
        (measurableSet_pairDomain k δ c J (K + 1))).integrableOn
    _ = ∑ k : Itinerary K B,
          ∫ p in pairDomain k δ c J (K + 1), overlapExtension k δ A J hJ p := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [setIntegral_indicator (measurableSet_pairDomain k δ c J (K + 1)),
        Set.inter_eq_right.mpr (pairDomain_subset_fareyTriangle k δ c J (K + 1))]

/-- Summing the unconditional cellwise Riemann theorems gives a single
finite-cell integer-grid limit for the original cutoff overlap integrand. -/
lemma tendsto_integerGrid_finiteDecomposition
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1) (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    Tendsto
      (fun n : ℕ ↦ ∑ k : Itinerary K B,
        ((∑' x : ↑(finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1) ∩
          (n : ℝ)⁻¹ • (Submodule.span ℤ
            (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))),
          cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) / n ^ 2))
      atTop (nhds (∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p)) := by
  classical
  let δ : ℝ := 1 / (2 * A * c ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum : Tendsto
      (fun n : ℕ ↦ ∑ k : Itinerary K B,
        ((∑' x : ↑(finTwoDomain k δ c J (K + 1) ∩
          (n : ℝ)⁻¹ • (Submodule.span ℤ
            (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))),
          cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) / n ^ 2))
      atTop (nhds (∑ k : Itinerary K B,
        ∫ x in finTwoDomain k δ c J (K + 1),
          cutoffOverlapIntegrand A c J hJ (finTwoToPair x))) := by
    apply tendsto_finsetSum
    intro k hk
    exact tendsto_integerGrid_cutoff_on_cell k hδ A c J hJ hJbound
  have hlimit : (∑ k : Itinerary K B,
      ∫ x in finTwoDomain k δ c J (K + 1),
        cutoffOverlapIntegrand A c J hJ (finTwoToPair x)) =
      ∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p := by
    rw [integral_finiteDecomposition hA hc J hJ h0 hK hJbound hB]
    apply Finset.sum_congr rfl
    intro k hk
    exact integral_finTwoDomain_cutoff_eq_pairDomain_overlap k hδ A c J hJ hJbound
  rw [hlimit] at hsum
  exact hsum

/-- The auxiliary positive-denominator strip in the cell decomposition may
be replaced by any smaller positive strip. -/
lemma exists_pairDomain_of_cutoff_pos_of_delta_le
    {A c δ : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (_hδ : 0 < δ)
    (hδle : δ ≤ 1 / (2 * A * c ^ 2))
    (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    {p : ℝ × ℝ} (hp : p ∈ fareyTriangle)
    (hpos : 0 < cutoffOverlapIntegrand A c J hJ p)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    ∃ k : Itinerary K B, p ∈ pairDomain k δ c J (K + 1) := by
  obtain ⟨k, hk⟩ := exists_pairDomain_of_cutoff_pos
    hA hc J hJ h0 hK hJbound hp hpos hB
  refine ⟨k, ⟨⟨hk.1.1, ?_⟩, hk.2⟩⟩
  intro j hj
  exact hδle.trans (hk.1.2 j hj)

lemma finiteDecomposition_eq_cutoff_of_delta_le
    {A c δ : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (hδ : 0 < δ)
    (hδle : δ ≤ 1 / (2 * A * c ^ 2))
    (J : Finset ℕ) (hJ : J.Nonempty)
    {K B : ℕ} (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ))
    (p : ℝ × ℝ) (hp : p ∈ fareyTriangle) :
    finiteDecomposition (K := K) (B := B) δ A c J hJ p =
      cutoffOverlapIntegrand A c J hJ p := by
  classical
  by_cases hne : cutoffOverlapIntegrand A c J hJ p = 0
  · rw [hne]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Set.indicator]
    split_ifs with hmem
    · rw [overlapExtension_eq_cutoff_on_pairDomain k hδ J hJ hJbound hmem, hne]
    · rfl
  · have hpos : 0 < cutoffOverlapIntegrand A c J hJ p :=
      lt_of_le_of_ne (cutoffOverlapIntegrand_nonneg A c J hJ p) (Ne.symm hne)
    obtain ⟨k₀, hk₀⟩ := exists_pairDomain_of_cutoff_pos_of_delta_le
      hA hc hδ hδle J hJ h0 hK hJbound hp hpos hB
    change (∑ k : Itinerary K B, (pairDomain k δ c J (K + 1)).indicator
      (overlapExtension k δ A J hJ) p) = _
    rw [Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hk₀,
        overlapExtension_eq_cutoff_on_pairDomain k₀ hδ J hJ hJbound hk₀]
    · intro k hk hkk₀
      have hnot : p ∉ pairDomain k δ c J (K + 1) := by
        intro hmem
        exact hkk₀ (pairDomain_unique hδ J hmem hk₀)
      simp [Set.indicator, hnot]
    · simp

/-- The contribution of one bounded BCZ itinerary cell to the moving-cutoff
primitive Farey sum.  Both cutoffs use the exact finite-scale ratio
`floor(cN) / N`; their limits are the corresponding cutoffs at `c`. -/
noncomputable def normalizedPrimitiveFareyCellSum
    {K B : ℕ} (k : Itinerary K B) (N : ℕ) (A c : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  let Q := ⌊c * (N : ℝ)⌋₊
  let cN := (Q : ℝ) / (N : ℝ)
  let δ := 1 / (2 * A * c ^ 2)
  (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          ((pairDomain k δ cN J (K + 1)).indicator
            (overlapExtension k δ A J hJ)) Q p
      else 0) / (Q : ℝ) ^ 2

lemma normalized_pair_mem_fareyTriangle {Q : ℕ} (hQ : 0 < Q)
    {p : ℕ × ℕ} (hp : p ∈ Farey.denominatorPairFinset Q) :
    (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) ∈ fareyTriangle := by
  rw [Farey.denominatorPairFinset, Finset.mem_filter] at hp
  obtain ⟨hpbox, hsum⟩ := hp
  obtain ⟨hu, hv⟩ := Finset.mem_product.mp hpbox
  rw [Finset.mem_Icc] at hu hv
  change 0 < (p.1 : ℝ) / Q ∧ (p.1 : ℝ) / Q ≤ 1 ∧
    0 < (p.2 : ℝ) / Q ∧ (p.2 : ℝ) / Q ≤ 1 ∧
      1 < (p.1 : ℝ) / Q + (p.2 : ℝ) / Q
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  constructor
  · exact div_pos (by exact_mod_cast hu.1) hQR
  constructor
  · exact (div_le_one hQR).2 (by exact_mod_cast hu.2)
  constructor
  · exact div_pos (by exact_mod_cast hv.1) hQR
  constructor
  · exact (div_le_one hQR).2 (by exact_mod_cast hv.2)
  · rw [← add_div, one_lt_div hQR]
    exact_mod_cast hsum

/-- The primitive Farey overlap sum with a fixed normalized cutoff `1 / c`. -/
noncomputable def normalizedPrimitiveFareyFixedCutoffSum
    (Q : ℕ) (A c : ℝ) (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          (cutoffOverlapIntegrand A c J hJ) Q p
      else 0) / (Q : ℝ) ^ 2

/-- The contribution of one fixed BCZ itinerary cell to the primitive
Farey sum with a fixed cutoff parameter `c`. -/
noncomputable def normalizedPrimitiveFareyFixedCellSum
    {K B : ℕ} (k : Itinerary K B) (Q : ℕ) (A c : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) : ℝ :=
  let δ := 1 / (2 * A * c ^ 2)
  (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          ((pairDomain k δ c J (K + 1)).indicator
            (overlapExtension k δ A J hJ)) Q p
      else 0) / (Q : ℝ) ^ 2

lemma normalizedPrimitiveFareyFixedCellSum_eq_filtered
    {K B : ℕ} (k : Itinerary K B) (Q : ℕ) (A c : ℝ)
    (J : Finset ℕ) (hJ : J.Nonempty) :
    normalizedPrimitiveFareyFixedCellSum k Q A c J hJ =
      (∑ p ∈ VisibleLattice.fareyCellPairFinset
          (finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1)) Q,
        if Nat.Coprime p.1 p.2 then
          Farey.normalizedDenominatorPairWeight
            (overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ) Q p
        else 0) / (Q : ℝ) ^ 2 := by
  classical
  simp only [normalizedPrimitiveFareyFixedCellSum]
  congr 1
  rw [VisibleLattice.fareyCellPairFinset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hmem : VisibleLattice.normalizedFareyPairVec Q p ∈
      finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1)
  · rw [if_pos hmem]
    have hpair : (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) ∈
        pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1) := by
      simpa [finTwoDomain, finTwoToPairLinear, finTwoToPair,
        VisibleLattice.normalizedFareyPairVec, VisibleLattice.fareyPairVec,
        div_eq_mul_inv, mul_comm] using hmem
    by_cases hcop : Nat.Coprime p.1 p.2
    · rw [if_pos hcop, if_pos hcop]
      unfold Farey.normalizedDenominatorPairWeight
      rw [Set.indicator]
      rw [if_pos (by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpair)]
    · simp [hcop]
  · rw [if_neg hmem]
    have hpair : (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) ∉
        pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1) := by
      simpa [finTwoDomain, finTwoToPairLinear, finTwoToPair,
        VisibleLattice.normalizedFareyPairVec, VisibleLattice.fareyPairVec,
        div_eq_mul_inv, mul_comm] using hmem
    by_cases hcop : Nat.Coprime p.1 p.2
    · rw [if_pos hcop]
      unfold Farey.normalizedDenominatorPairWeight
      rw [Set.indicator]
      rw [if_neg (by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpair)]
    · simp [hcop]

/-- Primitive Farey sums on a single fixed BCZ itinerary cell converge to
the corresponding cell integral. -/
lemma tendsto_normalizedPrimitiveFareyFixedCellSum
    {K B : ℕ} (k : Itinerary K B) {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) :
    Tendsto (fun Q ↦ normalizedPrimitiveFareyFixedCellSum k Q A c J hJ)
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
          overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p)) := by
  have hδ : 0 < 1 / (2 * A * c ^ 2) := by positivity
  have ht := VisibleLattice.tendsto_farey_cell_sum_pi
    (finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1))
    (finTwoDomain_subset_fareyTrianglePi k (1 / (2 * A * c ^ 2)) c J (K + 1))
    (isBounded_finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1))
    (measurableSet_finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1))
    (convex_finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1))
    (overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ)
    (continuous_overlapExtension k hδ A J hJ)
  have hseq : (fun Q ↦ normalizedPrimitiveFareyFixedCellSum k Q A c J hJ) =
      fun Q ↦
        (∑ p ∈ VisibleLattice.fareyCellPairFinset
            (finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1)) Q,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight
              (overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ) Q p
          else 0) / (Q : ℝ) ^ 2 := by
    funext Q
    exact normalizedPrimitiveFareyFixedCellSum_eq_filtered k Q A c J hJ
  have hint :
      (∫ x in finTwoDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
        VisibleLattice.fareyPiWeight
          (overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ) x) =
        ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
          overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p := by
    exact setIntegral_finTwoDomain_eq_pairDomain k (1 / (2 * A * c ^ 2))
      c J (K + 1) (overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ)
  rw [hseq]
  convert ht using 1
  rw [hint]

lemma normalizedPrimitiveFareyFixedCutoffSum_eq_sum_cells_eventually
    {K B : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    (fun Q ↦ normalizedPrimitiveFareyFixedCutoffSum Q A c J hJ) =ᶠ[atTop]
      fun Q ↦ ∑ k : Itinerary K B,
        normalizedPrimitiveFareyFixedCellSum k Q A c J hJ := by
  classical
  filter_upwards [eventually_gt_atTop 0] with Q hQ
  let δ : ℝ := 1 / (2 * A * c ^ 2)
  have hpoint (p : ℕ × ℕ) (hp : p ∈ Farey.denominatorPairFinset Q) :
      cutoffOverlapIntegrand A c J hJ
          (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) =
        ∑ k : Itinerary K B,
          (pairDomain k δ c J (K + 1)).indicator
            (overlapExtension k δ A J hJ)
              (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) := by
    exact (finiteDecomposition_eq_cutoff hA hc J hJ h0 hK hJbound hB
      _ (normalized_pair_mem_fareyTriangle hQ hp)).symm
  unfold normalizedPrimitiveFareyFixedCutoffSum
  simp only [normalizedPrimitiveFareyFixedCellSum]
  change
    (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          (cutoffOverlapIntegrand A c J hJ) Q p
      else 0) / (Q : ℝ) ^ 2 =
    ∑ k : Itinerary K B,
      (∑ p ∈ Farey.denominatorPairFinset Q,
        if Nat.Coprime p.1 p.2 then
          Farey.normalizedDenominatorPairWeight
            ((pairDomain k δ c J (K + 1)).indicator
              (overlapExtension k δ A J hJ)) Q p
        else 0) / (Q : ℝ) ^ 2
  calc
    _ = (∑ p ∈ Farey.denominatorPairFinset Q,
        ∑ k : Itinerary K B,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight
              ((pairDomain k δ c J (K + 1)).indicator
                (overlapExtension k δ A J hJ)) Q p
          else 0) / (Q : ℝ) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hcop : Nat.Coprime p.1 p.2
      · simp only [hcop, ↓reduceIte, Farey.normalizedDenominatorPairWeight]
        rw [hpoint p hp]
        simp [hcop]
      · simp [hcop]
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]

/-- Fixed-cutoff primitive Farey overlap sums have the expected BCZ
integral limit. -/
theorem tendsto_normalizedPrimitiveFareyFixedCutoffSum
    {K B : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    Tendsto (fun Q ↦ normalizedPrimitiveFareyFixedCutoffSum Q A c J hJ)
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p)) := by
  have hsum : Tendsto
      (fun Q ↦ ∑ k : Itinerary K B,
        normalizedPrimitiveFareyFixedCellSum k Q A c J hJ)
      atTop
      (nhds (∑ k : Itinerary K B,
        (6 / Real.pi ^ 2) *
          ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
            overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p)) := by
    apply tendsto_finsetSum
    intro k hk
    exact tendsto_normalizedPrimitiveFareyFixedCellSum k hA hc J hJ
  rw [← Finset.mul_sum,
    ← integral_finiteDecomposition hA hc J hJ h0 hK hJbound hB] at hsum
  exact hsum.congr'
    (normalizedPrimitiveFareyFixedCutoffSum_eq_sum_cells_eventually
      hA hc J hJ h0 hK hJbound hB).symm

lemma cutoffOverlapIntegrand_mono_cutoff
    {A c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (J : Finset ℕ) (hJ : J.Nonempty) (p : ℝ × ℝ) :
    cutoffOverlapIntegrand A c J hJ p ≤ cutoffOverlapIntegrand A d J hJ p := by
  have hinv : 1 / d ≤ 1 / c := by
    simpa only [one_div] using one_div_le_one_div_of_le hc hcd
  rw [cutoffOverlapIntegrand, cutoffOverlapIntegrand]
  by_cases hcut : ∀ j ∈ J, 1 / c ≤ normalizedDenominator j p
  · have hcut' : ∀ j ∈ J, 1 / d ≤ normalizedDenominator j p :=
      fun j hj ↦ hinv.trans (hcut j hj)
    rw [if_pos hcut, if_pos hcut']
  · rw [if_neg hcut]
    exact cutoffOverlapIntegrand_nonneg A d J hJ p

lemma normalizedPrimitiveFareyFixedCutoffSum_mono
    {A c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (J : Finset ℕ) (hJ : J.Nonempty) (Q : ℕ) :
    normalizedPrimitiveFareyFixedCutoffSum Q A c J hJ ≤
      normalizedPrimitiveFareyFixedCutoffSum Q A d J hJ := by
  unfold normalizedPrimitiveFareyFixedCutoffSum
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro p hp
  by_cases hcop : Nat.Coprime p.1 p.2
  · rw [if_pos hcop, if_pos hcop]
    exact cutoffOverlapIntegrand_mono_cutoff hc hcd J hJ _
  · simp [hcop]

lemma normalizedPrimitiveFareyOverlapSum_eq_fixedCutoff
    {A c : ℝ} (hc : 1 ≤ c) (J : Finset ℕ) (hJ : J.Nonempty)
    {N : ℕ} (hN : 0 < N) :
    normalizedPrimitiveFareyOverlapSum N A c J hJ =
      normalizedPrimitiveFareyFixedCutoffSum ⌊c * (N : ℝ)⌋₊ A
        ((⌊c * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) J hJ := by
  let Q := ⌊c * (N : ℝ)⌋₊
  let cN : ℝ := (Q : ℝ) / (N : ℝ)
  have hQ : 0 < Q := hN.trans_le (floor_mul_ge c hc N)
  have hthreshold : (N : ℝ) / Q = 1 / cN := by
    dsimp [cN]
    field_simp
  unfold normalizedPrimitiveFareyOverlapSum normalizedPrimitiveFareyFixedCutoffSum
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hcop : Nat.Coprime p.1 p.2
  · rw [if_pos hcop, if_pos hcop]
    unfold Farey.normalizedDenominatorPairWeight
    rw [hthreshold, thresholdOverlapIntegrand_one_div]
  · simp [hcop]

def lowerCutoffApproximation (c : ℝ) (k : ℕ) : ℝ :=
  c - (c - 1) / ((k : ℝ) + 1)

lemma lowerCutoffApproximation_one_le {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    1 ≤ lowerCutoffApproximation c k := by
  have hden : 1 ≤ (k : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hnum : 0 ≤ c - 1 := sub_nonneg.mpr hc
  have hmul : c - 1 ≤ (c - 1) * ((k : ℝ) + 1) := by
    simpa using mul_le_mul_of_nonneg_left hden hnum
  have hdiv : (c - 1) / ((k : ℝ) + 1) ≤ c - 1 := by
    rw [div_le_iff₀ (by positivity)]
    exact hmul
  dsimp [lowerCutoffApproximation]
  linarith

lemma lowerCutoffApproximation_le {c : ℝ} (hc : 1 ≤ c) (k : ℕ) :
    lowerCutoffApproximation c k ≤ c := by
  have : 0 ≤ (c - 1) / ((k : ℝ) + 1) := div_nonneg (sub_nonneg.mpr hc) (by positivity)
  dsimp [lowerCutoffApproximation]
  linarith

lemma lowerCutoffApproximation_lt {c : ℝ} (hc : 1 < c) (k : ℕ) :
    lowerCutoffApproximation c k < c := by
  have : 0 < (c - 1) / ((k : ℝ) + 1) := div_pos (sub_pos.mpr hc) (by positivity)
  dsimp [lowerCutoffApproximation]
  linarith

lemma tendsto_lowerCutoffApproximation (c : ℝ) :
    Tendsto (lowerCutoffApproximation c) atTop (nhds c) := by
  change Tendsto (fun k : ℕ ↦ c - (c - 1) / ((k : ℝ) + 1)) atTop (nhds c)
  have hi : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    by simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hm : Tendsto (fun k : ℕ ↦ (c - 1) * ((k : ℝ) + 1)⁻¹)
      atTop (nhds ((c - 1) * 0)) := tendsto_const_nhds.mul hi
  simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hm

/-- The exact moving-cutoff primitive Farey overlap sum converges, without
any remaining cellwise limit hypothesis. -/
theorem tendsto_normalizedPrimitiveFareyOverlapSum
    {K B : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    Tendsto (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c J hJ)
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p)) := by
  let r : ℕ → ℝ := lowerCutoffApproximation c
  let Q : ℕ → ℕ := fun N ↦ ⌊c * (N : ℝ)⌋₊
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hQ : Tendsto Q atTop atTop := tendsto_fareyOrder_atTop c hcpos
  have hcN : Tendsto (fun N : ℕ ↦ (Q N : ℝ) / (N : ℝ)) atTop (nhds c) := by
    exact (tendsto_nat_floor_mul_div_atTop hcpos.le).comp tendsto_natCast_atTop_atTop
  apply VisibleLattice.MovingThreshold.tendsto_diagonal_of_eventually_squeeze
    (a := fun k N ↦ normalizedPrimitiveFareyFixedCutoffSum (Q N) A (r k) J hJ)
    (b := fun _ N ↦ normalizedPrimitiveFareyFixedCutoffSum (Q N) A c J hJ)
    (A := fun k ↦ (6 / Real.pi ^ 2) *
      ∫ p in fareyTriangle, cutoffOverlapIntegrand A (r k) J hJ p)
    (B := fun _ ↦ (6 / Real.pi ^ 2) *
      ∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p)
  · intro k
    have hr1 : 1 ≤ r k := lowerCutoffApproximation_one_le hc k
    have hrc : r k ≤ c := lowerCutoffApproximation_le hc k
    have hrsq : (r k) ^ 2 ≤ c ^ 2 :=
      (sq_le_sq₀ (zero_le_one.trans hr1) (zero_le_one.trans hc)).2 hrc
    have hBr : 4 * A * (r k) ^ 2 < (B + 1 : ℕ) :=
      (mul_le_mul_of_nonneg_left hrsq (by positivity)).trans_lt hB
    exact (tendsto_normalizedPrimitiveFareyFixedCutoffSum
      hA hr1 J hJ h0 hK hJbound hBr).comp hQ
  · intro k
    exact (tendsto_normalizedPrimitiveFareyFixedCutoffSum
      hA hc J hJ h0 hK hJbound hB).comp hQ
  · have hr := tendsto_lowerCutoffApproximation c
    have hrinv : Tendsto (fun k ↦ 1 / r k) atTop (nhds (1 / c)) := by
      simpa only [one_div] using hr.inv₀ hcpos.ne'
    have hi := tendsto_setIntegral_thresholdOverlapIntegrand_unconditional
      hrinv (one_div_pos.mpr hcpos) hA.le hJ h0
    have hmul : Tendsto (fun n ↦ (6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle, thresholdOverlapIntegrand A (1 / r n) J hJ p)
        atTop (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle, thresholdOverlapIntegrand A (1 / c) J hJ p)) :=
      tendsto_const_nhds.mul hi
    simpa only [thresholdOverlapIntegrand_one_div] using hmul
  · exact tendsto_const_nhds
  · intro k
    have hr1 : 1 ≤ r k := lowerCutoffApproximation_one_le hc k
    have hrc : r k ≤ c := lowerCutoffApproximation_le hc k
    have hbelow : ∀ᶠ N in atTop, r k ≤ (Q N : ℝ) / (N : ℝ) := by
      by_cases hc1 : c = 1
      · subst c
        filter_upwards [eventually_gt_atTop 0] with N hN
        simp [r, lowerCutoffApproximation, Q, hN.ne']
      · exact (hcN.eventually_const_lt
          (lowerCutoffApproximation_lt (lt_of_le_of_ne hc (Ne.symm hc1)) k)).mono
          fun _ h ↦ h.le
    filter_upwards [eventually_gt_atTop 0, hbelow] with N hN hrN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hQN : (Q N : ℝ) ≤ c * N := by
      dsimp [Q]
      exact Nat.floor_le (mul_nonneg hcpos.le (Nat.cast_nonneg N))
    have hcNle : (Q N : ℝ) / (N : ℝ) ≤ c := by
      rw [div_le_iff₀ hNreal]
      simpa using hQN
    have hcNpos : 0 < (Q N : ℝ) / (N : ℝ) :=
      (zero_lt_one.trans_le hr1).trans_le hrN
    rw [normalizedPrimitiveFareyOverlapSum_eq_fixedCutoff hc J hJ hN]
    exact ⟨normalizedPrimitiveFareyFixedCutoffSum_mono
      (zero_lt_one.trans_le hr1) hrN J hJ (Q N),
      normalizedPrimitiveFareyFixedCutoffSum_mono hcNpos hcNle J hJ (Q N)⟩

/-- Convenient specialization for a nonempty family of positive offsets:
adjoin offset zero and choose the itinerary and alphabet bounds canonically. -/
theorem tendsto_normalizedPrimitiveFareyOverlapSum_insert_zero
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (hJpos : ∀ j ∈ J, 1 ≤ j) :
    Tendsto
      (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c
        (insert 0 J) (Finset.insert_nonempty 0 J))
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle,
          thresholdOverlapIntegrand A (1 / c)
            (insert 0 J) (Finset.insert_nonempty 0 J) p)) := by
  let L := J.max' hJ
  let K := L - 1
  let B := ⌊4 * A * c ^ 2⌋₊
  have hLmem : L ∈ J := Finset.max'_mem J hJ
  have hLpos : 1 ≤ L := hJpos L hLmem
  have hKL : K + 1 = L := Nat.sub_add_cancel hLpos
  have htop : K + 1 ∈ insert 0 J := by
    rw [hKL]
    exact Finset.mem_insert_of_mem hLmem
  have hbound : ∀ j ∈ insert 0 J, j ≤ K + 1 := by
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · omega
    · rw [hKL]
      exact Finset.le_max' J j hj
  have hB : 4 * A * c ^ 2 < (B + 1 : ℕ) := by
    dsimp [B]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (4 * A * c ^ 2))
  have ht := tendsto_normalizedPrimitiveFareyOverlapSum
    (K := K) (B := B) hA hc (insert 0 J) (Finset.insert_nonempty 0 J)
      (Finset.mem_insert_self 0 J) htop hbound hB
  simpa only [thresholdOverlapIntegrand_one_div] using ht

/-- At every sufficiently large scale, the moving-cutoff primitive overlap
sum is exactly the finite sum of its bounded itinerary-cell contributions. -/
lemma normalizedPrimitiveFareyOverlapSum_eq_sum_cells_eventually
    {K B : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ)) :
    (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c J hJ) =ᶠ[atTop]
      fun N ↦ ∑ k : Itinerary K B,
        normalizedPrimitiveFareyCellSum k N A c J hJ := by
  filter_upwards [eventually_gt_atTop 0] with N hN
  let Q := ⌊c * (N : ℝ)⌋₊
  let cN : ℝ := (Q : ℝ) / (N : ℝ)
  let δ : ℝ := 1 / (2 * A * c ^ 2)
  have hNQ : N ≤ Q := floor_mul_ge c hc N
  have hQ : 0 < Q := hN.trans_le hNQ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcN : 1 ≤ cN := by
    dsimp [cN]
    rw [le_div_iff₀ hNR]
    simpa using (show (N : ℝ) ≤ Q by exact_mod_cast hNQ)
  have hQN : (Q : ℝ) ≤ c * N := by
    dsimp [Q]
    exact Nat.floor_le (mul_nonneg (zero_le_one.trans hc) (Nat.cast_nonneg N))
  have hcNle : cN ≤ c := by
    dsimp [cN]
    rw [div_le_iff₀ hNR]
    simpa using hQN
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hcN0 : 0 ≤ cN := zero_le_one.trans hcN
  have hB' : 4 * A * cN ^ 2 < (B + 1 : ℕ) := by
    have hsquare : cN ^ 2 ≤ c ^ 2 :=
      (sq_le_sq₀ hcN0 hc0).2 hcNle
    exact (mul_le_mul_of_nonneg_left hsquare (by positivity)).trans_lt hB
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 / (2 * A * cN ^ 2) := by
    dsimp [δ]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hcN0 hc0).2 hcNle) (by positivity)
  have hthreshold : (N : ℝ) / Q = 1 / cN := by
    dsimp [cN]
    field_simp
  have hpoint (p : ℕ × ℕ) (hp : p ∈ Farey.denominatorPairFinset Q) :
      thresholdOverlapIntegrand A ((N : ℝ) / Q) J hJ
          (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) =
        ∑ k : Itinerary K B,
          (pairDomain k δ cN J (K + 1)).indicator
            (overlapExtension k δ A J hJ)
              (((p.1 : ℝ) / Q), ((p.2 : ℝ) / Q)) := by
    rw [hthreshold, thresholdOverlapIntegrand_one_div]
    exact (finiteDecomposition_eq_cutoff_of_delta_le
      hA hcN hδ hδle J hJ h0 hK hJbound hB'
      _ (normalized_pair_mem_fareyTriangle hQ hp)).symm
  unfold normalizedPrimitiveFareyOverlapSum normalizedPrimitiveFareyCellSum
  dsimp only
  change
    (∑ p ∈ Farey.denominatorPairFinset Q,
      if Nat.Coprime p.1 p.2 then
        Farey.normalizedDenominatorPairWeight
          (thresholdOverlapIntegrand A ((N : ℝ) / (Q : ℝ)) J hJ) Q p
      else 0) / (Q : ℝ) ^ 2 =
    ∑ k : Itinerary K B,
      (∑ p ∈ Farey.denominatorPairFinset Q,
        if Nat.Coprime p.1 p.2 then
          Farey.normalizedDenominatorPairWeight
            ((pairDomain k δ cN J (K + 1)).indicator
              (overlapExtension k δ A J hJ)) Q p
        else 0) / (Q : ℝ) ^ 2
  calc
    _ = (∑ p ∈ Farey.denominatorPairFinset Q,
        ∑ k : Itinerary K B,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight
              ((pairDomain k δ cN J (K + 1)).indicator
                (overlapExtension k δ A J hJ)) Q p
          else 0) / (Q : ℝ) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hcop : Nat.Coprime p.1 p.2
      · simp only [hcop, ↓reduceIte, Farey.normalizedDenominatorPairWeight]
        rw [hpoint p hp]
        simp [hcop]
      · simp [hcop]
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]

/-- A fixed-offset primitive-overlap limit follows from the finitely many
cell primitive limits.  Thus the remaining analytic work is local to one
bounded convex BCZ cell. -/
theorem tendsto_normalizedPrimitiveFareyOverlapSum_of_cell_limits
    {K B : ℕ} {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (J : Finset ℕ) (hJ : J.Nonempty) (h0 : 0 ∈ J) (hK : K + 1 ∈ J)
    (hJbound : ∀ j ∈ J, j ≤ K + 1)
    (hB : 4 * A * c ^ 2 < (B + 1 : ℕ))
    (hcell : ∀ k : Itinerary K B,
      Tendsto (fun N ↦ normalizedPrimitiveFareyCellSum k N A c J hJ)
        atTop
        (nhds ((6 / Real.pi ^ 2) *
          ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
            overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p))) :
    Tendsto (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c J hJ)
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle, cutoffOverlapIntegrand A c J hJ p)) := by
  have hsum : Tendsto
      (fun N ↦ ∑ k : Itinerary K B,
        normalizedPrimitiveFareyCellSum k N A c J hJ)
      atTop
      (nhds (∑ k : Itinerary K B,
        (6 / Real.pi ^ 2) *
          ∫ p in pairDomain k (1 / (2 * A * c ^ 2)) c J (K + 1),
            overlapExtension k (1 / (2 * A * c ^ 2)) A J hJ p)) := by
    apply tendsto_finsetSum
    intro k hk
    exact hcell k
  rw [← Finset.mul_sum,
    ← integral_finiteDecomposition hA hc J hJ h0 hK hJbound hB] at hsum
  exact hsum.congr'
    (normalizedPrimitiveFareyOverlapSum_eq_sum_cells_eventually
      hA hc J hJ h0 hK hJbound hB).symm

end BCZCells

def singletonFareyCell (t : ℝ) : Set (Fin 2 → ℝ) :=
  VisibleLattice.fareyTrianglePi ∩ {x | t ≤ x 0}

noncomputable def singletonClippedWeight (A t : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * A / (max t p.1) ^ 2

lemma continuous_singletonClippedWeight {A t : ℝ} (ht : 0 < t) :
    Continuous (singletonClippedWeight A t) := by
  apply continuous_const.div
  · exact (continuous_const.max continuous_fst).pow 2
  · intro p
    exact (sq_pos_of_pos (ht.trans_le (le_max_left _ _))).ne'

lemma singletonFareyCell_subset (t : ℝ) :
    singletonFareyCell t ⊆ VisibleLattice.fareyTrianglePi :=
  Set.inter_subset_left

lemma isBounded_singletonFareyCell (t : ℝ) :
    Bornology.IsBounded (singletonFareyCell t) :=
  VisibleLattice.isBounded_fareyTrianglePi.subset (singletonFareyCell_subset t)

lemma measurableSet_singletonFareyCell (t : ℝ) :
    MeasurableSet (singletonFareyCell t) :=
  VisibleLattice.measurableSet_fareyTrianglePi.inter
    (measurableSet_le measurable_const (continuous_apply 0).measurable)

lemma convex_singletonFareyCell (t : ℝ) : Convex ℝ (singletonFareyCell t) := by
  apply VisibleLattice.convex_fareyTrianglePi.inter
  intro x hx y hy a b ha hb hab
  change t ≤ (a • x + b • y) 0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact BCZCells.le_combo ha hb hab hx hy

lemma normalizedPrimitiveFareyFixedCutoffSum_singleton_eq_filtered
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (Q : ℕ) :
    BCZCells.normalizedPrimitiveFareyFixedCutoffSum Q A c {0} (by simp) =
      (∑ p ∈ VisibleLattice.fareyCellPairFinset
          (singletonFareyCell (1 / c)) Q,
        if Nat.Coprime p.1 p.2 then
          Farey.normalizedDenominatorPairWeight
            (singletonClippedWeight A (1 / c)) Q p
        else 0) / (Q : ℝ) ^ 2 := by
  classical
  unfold BCZCells.normalizedPrimitiveFareyFixedCutoffSum
  congr 1
  rw [VisibleLattice.fareyCellPairFinset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hQ : 0 < Q := by
    rw [Farey.denominatorPairFinset, Finset.mem_filter] at hp
    have hu := (Finset.mem_product.mp hp.1).1
    rw [Finset.mem_Icc] at hu
    omega
  have hcoord : (VisibleLattice.normalizedFareyPairVec Q p) 0 =
      (p.1 : ℝ) / Q := by
    simp [VisibleLattice.normalizedFareyPairVec,
      VisibleLattice.fareyPairVec, div_eq_mul_inv, mul_comm]
  have htri : VisibleLattice.normalizedFareyPairVec Q p ∈
      VisibleLattice.fareyTrianglePi := by
    have hpPair := BCZCells.normalized_pair_mem_fareyTriangle hQ hp
    simpa [VisibleLattice.normalizedFareyPairVec,
      VisibleLattice.fareyPairVec, VisibleLattice.fareyTrianglePi,
      fareyTriangle, div_eq_mul_inv, mul_comm] using hpPair
  by_cases hcut : 1 / c ≤ (p.1 : ℝ) / Q
  · have hmem : VisibleLattice.normalizedFareyPairVec Q p ∈
        singletonFareyCell (1 / c) := ⟨htri, by simpa [hcoord] using hcut⟩
    rw [if_pos hmem]
    by_cases hcop : Nat.Coprime p.1 p.2
    · rw [if_pos hcop, if_pos hcop]
      unfold Farey.normalizedDenominatorPairWeight
      rw [← thresholdOverlapIntegrand_one_div,
        thresholdOverlapIntegrand_singleton_zero hA,
        if_pos hcut]
      unfold singletonClippedWeight
      rw [max_eq_right (by simpa only [one_div] using hcut)]
    · simp [hcop]
  · have hmem : VisibleLattice.normalizedFareyPairVec Q p ∉
        singletonFareyCell (1 / c) := by
      intro h
      exact hcut (by simpa [hcoord] using h.2)
    rw [if_neg hmem]
    by_cases hcop : Nat.Coprime p.1 p.2
    · rw [if_pos hcop]
      unfold Farey.normalizedDenominatorPairWeight
      rw [← thresholdOverlapIntegrand_one_div,
        thresholdOverlapIntegrand_singleton_zero hA, if_neg hcut]
    · simp [hcop]

theorem tendsto_normalizedPrimitiveFareyFixedCutoffSum_singleton
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) :
    Tendsto
      (fun Q ↦ BCZCells.normalizedPrimitiveFareyFixedCutoffSum
        Q A c {0} (by simp)) atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle,
          cutoffOverlapIntegrand A c {0} (by simp) p)) := by
  let t : ℝ := 1 / c
  have ht : 0 < t := one_div_pos.mpr (zero_lt_one.trans_le hc)
  have hvis := VisibleLattice.tendsto_farey_cell_sum_pi
    (singletonFareyCell t) (singletonFareyCell_subset t)
    (isBounded_singletonFareyCell t) (measurableSet_singletonFareyCell t)
    (convex_singletonFareyCell t) (singletonClippedWeight A t)
    (continuous_singletonClippedWeight ht)
  have hseq :
      (fun Q ↦ BCZCells.normalizedPrimitiveFareyFixedCutoffSum
        Q A c {0} (by simp)) =
      (fun Q ↦
        (∑ p ∈ VisibleLattice.fareyCellPairFinset (singletonFareyCell t) Q,
          if Nat.Coprime p.1 p.2 then
            Farey.normalizedDenominatorPairWeight
              (singletonClippedWeight A t) Q p else 0) / (Q : ℝ) ^ 2) := by
    funext Q
    exact normalizedPrimitiveFareyFixedCutoffSum_singleton_eq_filtered hA.le
      (zero_lt_one.trans_le hc) Q
  rw [hseq]
  convert hvis using 1
  let s : Set (ℝ × ℝ) := fareyTriangle ∩ {p | t ≤ p.1}
  have hsmeas : MeasurableSet s := measurableSet_fareyTriangle.inter
    (measurableSet_le measurable_const measurable_fst)
  have hcoord :
      (∫ x in singletonFareyCell t,
          VisibleLattice.fareyPiWeight (singletonClippedWeight A t) x) =
        ∫ p in s, singletonClippedWeight A t p := by
    have hpres := volume_preserving_finTwoArrow ℝ
    have hemb : MeasurableEmbedding (@MeasurableEquiv.finTwoArrow ℝ _) :=
      MeasurableEquiv.finTwoArrow.measurableEmbedding
    have h := hpres.setIntegral_preimage_emb hemb
      (singletonClippedWeight A t) s
    change
      (∫ x in (fun x : Fin 2 → ℝ ↦ (x 0, x 1)) ⁻¹' s,
        singletonClippedWeight A t (x 0, x 1)) = _ at h
    simpa [s, singletonFareyCell, VisibleLattice.fareyTrianglePi,
      fareyTriangle, VisibleLattice.fareyPiWeight] using h
  have heq (p : ℝ × ℝ) (hp : p ∈ s) :
      singletonClippedWeight A t p =
        cutoffOverlapIntegrand A c {0} (by simp) p := by
    have hcut : 1 / c ≤ p.1 := by simpa [t] using hp.2
    rw [← thresholdOverlapIntegrand_one_div,
      thresholdOverlapIntegrand_singleton_zero hA.le, if_pos hcut]
    unfold singletonClippedWeight
    rw [max_eq_right (by simpa only [t, one_div] using hcut)]
  have hsmall :
      (∫ p in s, singletonClippedWeight A t p) =
        ∫ p in s, cutoffOverlapIntegrand A c {0} (by simp) p :=
    setIntegral_congr_fun hsmeas heq
  have hsubset : s ⊆ fareyTriangle := Set.inter_subset_left
  have hbig :
      (∫ p in fareyTriangle, cutoffOverlapIntegrand A c {0} (by simp) p) =
        ∫ p in s, cutoffOverlapIntegrand A c {0} (by simp) p := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_fareyTriangle hsubset
    intro p hp
    have hnot : ¬ 1 / c ≤ p.1 := by
      intro hpcut
      exact hp.2 ⟨hp.1, by simpa [t] using hpcut⟩
    rw [← thresholdOverlapIntegrand_one_div,
      thresholdOverlapIntegrand_singleton_zero hA.le, if_neg hnot]
  exact congrArg nhds (congrArg (fun z : ℝ ↦ (6 / Real.pi ^ 2) * z)
    (hcoord.trans (hsmall.trans hbig.symm)).symm)

/-- The moving lower cutoff also converges for the singleton offset family.
This is the base term missing from the bounded-itinerary decomposition, whose
general theorem necessarily assumes a positive terminal offset. -/
theorem tendsto_normalizedPrimitiveFareyOverlapSum_singleton
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) :
    Tendsto (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c {0} (by simp))
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle, cutoffOverlapIntegrand A c {0} (by simp) p)) := by
  let r : ℕ → ℝ := BCZCells.lowerCutoffApproximation c
  let Q : ℕ → ℕ := fun N ↦ ⌊c * (N : ℝ)⌋₊
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hQ : Tendsto Q atTop atTop := tendsto_fareyOrder_atTop c hcpos
  have hcN : Tendsto (fun N : ℕ ↦ (Q N : ℝ) / (N : ℝ)) atTop (nhds c) := by
    exact (tendsto_nat_floor_mul_div_atTop hcpos.le).comp tendsto_natCast_atTop_atTop
  apply VisibleLattice.MovingThreshold.tendsto_diagonal_of_eventually_squeeze
    (a := fun k N ↦ BCZCells.normalizedPrimitiveFareyFixedCutoffSum
      (Q N) A (r k) {0} (by simp))
    (b := fun _ N ↦ BCZCells.normalizedPrimitiveFareyFixedCutoffSum
      (Q N) A c {0} (by simp))
    (A := fun k ↦ (6 / Real.pi ^ 2) *
      ∫ p in fareyTriangle, cutoffOverlapIntegrand A (r k) {0} (by simp) p)
    (B := fun _ ↦ (6 / Real.pi ^ 2) *
      ∫ p in fareyTriangle, cutoffOverlapIntegrand A c {0} (by simp) p)
  · intro k
    have hr1 : 1 ≤ r k := BCZCells.lowerCutoffApproximation_one_le hc k
    exact (tendsto_normalizedPrimitiveFareyFixedCutoffSum_singleton hA hr1).comp hQ
  · intro k
    exact (tendsto_normalizedPrimitiveFareyFixedCutoffSum_singleton hA hc).comp hQ
  · have hr := BCZCells.tendsto_lowerCutoffApproximation c
    have hrinv : Tendsto (fun k ↦ 1 / r k) atTop (nhds (1 / c)) := by
      simpa only [one_div] using hr.inv₀ hcpos.ne'
    have hi := tendsto_setIntegral_thresholdOverlapIntegrand_unconditional
      hrinv (one_div_pos.mpr hcpos) hA.le (J := {0}) (by simp) (by simp)
    have hmul : Tendsto (fun n ↦ (6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle,
          thresholdOverlapIntegrand A (1 / r n) {0} (by simp) p)
        atTop (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle,
            thresholdOverlapIntegrand A (1 / c) {0} (by simp) p)) :=
      tendsto_const_nhds.mul hi
    simpa only [thresholdOverlapIntegrand_one_div] using hmul
  · exact tendsto_const_nhds
  · intro k
    have hr1 : 1 ≤ r k := BCZCells.lowerCutoffApproximation_one_le hc k
    have hrc : r k ≤ c := BCZCells.lowerCutoffApproximation_le hc k
    have hbelow : ∀ᶠ N in atTop, r k ≤ (Q N : ℝ) / (N : ℝ) := by
      by_cases hc1 : c = 1
      · subst c
        filter_upwards [eventually_gt_atTop 0] with N hN
        simp [r, BCZCells.lowerCutoffApproximation, Q, hN.ne']
      · exact (hcN.eventually_const_lt
          (BCZCells.lowerCutoffApproximation_lt
            (lt_of_le_of_ne hc (Ne.symm hc1)) k)).mono
          fun _ h ↦ h.le
    filter_upwards [eventually_gt_atTop 0, hbelow] with N hN hrN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hQN : (Q N : ℝ) ≤ c * N := by
      dsimp [Q]
      exact Nat.floor_le (mul_nonneg hcpos.le (Nat.cast_nonneg N))
    have hcNle : (Q N : ℝ) / (N : ℝ) ≤ c := by
      rw [div_le_iff₀ hNreal]
      simpa using hQN
    have hcNpos : 0 < (Q N : ℝ) / (N : ℝ) :=
      (zero_lt_one.trans_le hr1).trans_le hrN
    rw [BCZCells.normalizedPrimitiveFareyOverlapSum_eq_fixedCutoff
      hc {0} (by simp) hN]
    exact ⟨BCZCells.normalizedPrimitiveFareyFixedCutoffSum_mono
      (zero_lt_one.trans_le hr1) hrN {0} (by simp) (Q N),
      BCZCells.normalizedPrimitiveFareyFixedCutoffSum_mono
        hcNpos hcNle {0} (by simp) (Q N)⟩


/-- Once the singleton offset limit is known, all offset families in the
finite inclusion--exclusion formula follow from the bounded BCZ theorem. -/
theorem fixed_offset_overlap_limits_of_singleton
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c)
    (hsingle : Tendsto
      (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c {0} (by simp))
      atTop
      (nhds ((6 / Real.pi ^ 2) *
        ∫ p in fareyTriangle,
          thresholdOverlapIntegrand A (1 / c) {0} (by simp) p))) :
    ∀ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
      Tendsto
        (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c
          (insert 0 J) (Finset.insert_nonempty 0 J))
        atTop
        (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle,
            thresholdOverlapIntegrand A (1 / c)
              (insert 0 J) (Finset.insert_nonempty 0 J) p)) := by
  intro J hJsub
  by_cases hJ : J.Nonempty
  swap
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simpa using hsingle
  let m := J.max' hJ
  have hmMem : m ∈ J := Finset.max'_mem J hJ
  have hsubset := Finset.mem_powerset.mp hJsub
  have hmIcc : m ∈ Finset.Icc 1 (overlapCutoff A c) := hsubset hmMem
  have hmpos : 0 < m := (Finset.mem_Icc.mp hmIcc).1
  let K := m - 1
  let B := ⌈4 * A * c ^ 2⌉₊
  have hKm : K + 1 = m := by dsimp [K]; omega
  have hzero : 0 ∈ insert 0 J := Finset.mem_insert_self 0 J
  have hlast : K + 1 ∈ insert 0 J := by
    rw [hKm]
    exact Finset.mem_insert_of_mem hmMem
  have hbound : ∀ j ∈ insert 0 J, j ≤ K + 1 := by
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · omega
    · rw [hKm]
      exact Finset.le_max' J j hj
  have hB : 4 * A * c ^ 2 < (B + 1 : ℕ) := by
    have hceil : 4 * A * c ^ 2 ≤ (B : ℝ) := by
      dsimp [B]
      exact Nat.le_ceil _
    exact hceil.trans_lt (by exact_mod_cast Nat.lt_succ_self B)
  have ht := BCZCells.tendsto_normalizedPrimitiveFareyOverlapSum
    (K := K) (B := B) hA hc (insert 0 J) (Finset.insert_nonempty 0 J)
      hzero hlast hbound hB
  simpa only [thresholdOverlapIntegrand_one_div] using ht

/-- Every fixed offset family occurring in the finite inclusion--exclusion
formula has the predicted primitive Farey overlap limit. -/
theorem fixed_offset_overlap_limits
    {A c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) :
    ∀ J ∈ (Finset.Icc 1 (overlapCutoff A c)).powerset,
      Tendsto
        (fun N ↦ normalizedPrimitiveFareyOverlapSum N A c
          (insert 0 J) (Finset.insert_nonempty 0 J))
        atTop
        (nhds ((6 / Real.pi ^ 2) *
          ∫ p in fareyTriangle,
            thresholdOverlapIntegrand A (1 / c)
              (insert 0 J) (Finset.insert_nonempty 0 J) p)) := by
  apply fixed_offset_overlap_limits_of_singleton hA hc
  simpa only [thresholdOverlapIntegrand_one_div] using
    tendsto_normalizedPrimitiveFareyOverlapSum_singleton hA hc

/-- Resolution of Erdős Problem 1001: for every `A > 0` and `c ≥ 1`, the
measures of the rational-approximation unions converge to the explicit
finite BCZ integral `erdosSzuszTuranLimit A c`. -/
theorem erdos_1001 (A c : ℝ) (hA : 0 < A) (hc : 1 ≤ c) :
    IsLimitValue A c (erdosSzuszTuranLimit A c) := by
  exact isLimitValue_erdosSzuszTuranLimit_of_overlapSums_error A c hA hc
    (fixed_offset_overlap_limits hA hc)
    (tendsto_S_sub_normalizedPrimitiveFareyIESum_zero hA hc)



/-- Boundedness of `S` always supplies a convergent subsequence.  This lemma
is deliberately weaker than convergence of the full sequence and is useful
for separating compactness from the number-theoretic uniqueness argument. -/
theorem exists_subsequence_limit (A c : ℝ) :
    ∃ f ∈ Icc (0 : ℝ) 1, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto ((fun N : ℕ ↦ S N A c) ∘ φ) atTop (𝓝 f) := by
  exact isCompact_Icc.tendsto_subseq fun N ↦
    ⟨S_nonneg N A c, S_le_one N A c⟩

#print axioms weighted_totient_Icc_tendsto
#print axioms erdos_1001_sparse
#print axioms bczMap_mem_fareyTriangle
#print axioms exists_subsequence_limit
#print axioms erdos_1001

end

end Erdos1001
