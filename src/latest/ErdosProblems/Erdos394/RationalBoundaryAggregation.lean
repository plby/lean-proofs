import ErdosProblems.Erdos394.RationalPairVector
import ErdosProblems.Erdos394.RationalBoundaryMoment
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Aggregating rational reduced-vector boundary terms
-/

open Nat Finset

namespace Erdos394

/-- Local multiplier weight attached to a pair of root labels. -/
def pairMultiplierLocalWeight (p : ℕ) (ab : ℕ × ℕ) : ℕ :=
  if ab = (0, 0) then p - 1 else 1

/-- Product multiplier weight of a global label pair. -/
def pairMultiplierGlobalWeight (P : Finset ℕ)
    (f : ∀ _p : ↥P, ℕ × ℕ) : ℕ :=
  ∏ p : ↥P, pairMultiplierLocalWeight p.val (f p)

/-- The local multiplier weights over the full label square sum to
`p-1+(K²-1)`. -/
theorem sum_pairMultiplierLocalWeight_all {p K : ℕ} (hK : 0 < K) :
    (∑ ab ∈ allLabelPairs K, pairMultiplierLocalWeight p ab) =
      p - 1 + (K * K - 1) := by
  unfold pairMultiplierLocalWeight
  rw [sum_allLabelPairs_zero_other hK (p - 1) 1]
  simp

/-- On one compatible nonzero rational line every multiplier weight is one. -/
theorem sum_pairMultiplierLocalWeight_compatible
    {p K A B : ℕ} :
    (∑ ab ∈ compatibleRatioLabels K A B,
      pairMultiplierLocalWeight p ab) =
      (compatibleRatioLabels K A B).card := by
  calc
    (∑ ab ∈ compatibleRatioLabels K A B,
      pairMultiplierLocalWeight p ab) =
        ∑ _ab ∈ compatibleRatioLabels K A B, 1 := by
      apply Finset.sum_congr rfl
      intro ab hab
      have habnz : ab ≠ (0, 0) :=
        (Finset.mem_erase.mp (Finset.mem_filter.mp hab).1).1
      simp [pairMultiplierLocalWeight, habnz]
    _ = (compatibleRatioLabels K A B).card := by simp

/-- Labels allowed at one prime for one rational witness and one time. -/
def rationalAllowedLabelPairs (p K j : ℕ) (w : ℕ × ℕ) :
    Finset (ℕ × ℕ) :=
  if p ∣ j then allLabelPairs K
  else compatibleRatioLabels K w.1 w.2

/-- Independent global allowed-label box. -/
def globalRationalAllowedLabels (P : Finset ℕ) (K j : ℕ)
    (w : ℕ × ℕ) : Finset (∀ _p : ↥P, ℕ × ℕ) :=
  Fintype.piFinset (fun p : ↥P ↦ rationalAllowedLabelPairs p.val K j w)

/-- Sum of global multiplier weights over an independent allowed box factors
into the local sums. -/
theorem sum_globalRationalAllowedLabels_weight
    (P : Finset ℕ) (K j : ℕ) (w : ℕ × ℕ) :
    (∑ f ∈ globalRationalAllowedLabels P K j w,
      pairMultiplierGlobalWeight P f) =
      ∏ p : ↥P,
        ∑ ab ∈ rationalAllowedLabelPairs p.val K j w,
          pairMultiplierLocalWeight p.val ab := by
  unfold globalRationalAllowedLabels pairMultiplierGlobalWeight
  exact (Finset.prod_univ_sum
    (fun p : ↥P ↦ rationalAllowedLabelPairs p.val K j w)
    (fun p ab ↦ pairMultiplierLocalWeight p.val ab)).symm

/-- A fixed rational-witness fibre at time `j` has weight at most the generic
two-state local weight used in F-035. -/
theorem rational_witness_fibre_weight_le
    (P : Finset ℕ) (K j : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (w : ℕ × ℕ) (hw : w ∈ nonzeroLabelPairs K)
    (S : Finset (∀ _p : ↥P, ℕ × ℕ))
    (height : (∀ _p : ↥P, ℕ × ℕ) → ℕ)
    (witness : (∀ _p : ↥P, ℕ × ℕ) → ℕ × ℕ)
    (hSglobal : S ⊆ globalLabelPairs P K)
    (hcompat : ∀ f ∈ S, ∀ p : ↥P, ¬p.val ∣ height f →
      f p ∈ compatibleRatioLabels K (witness f).1 (witness f).2) :
    (∑ f ∈ S.filter (fun f ↦ witness f = w ∧ height f ∣ j),
      pairMultiplierGlobalWeight P f) ≤
      twoStateLocalWeight P
        (fun p ↦ p - 1 + 2 * (K * K - 1))
        (fun _p ↦ K - 1) j := by
  let T := S.filter (fun f ↦ witness f = w ∧ height f ∣ j)
  have hsub : T ⊆ globalRationalAllowedLabels P K j w := by
    intro f hf
    have hfS := (Finset.mem_filter.mp hf).1
    have hfw := (Finset.mem_filter.mp hf).2.1
    have hfdiv := (Finset.mem_filter.mp hf).2.2
    apply Fintype.mem_piFinset.mpr
    intro p
    unfold rationalAllowedLabelPairs
    by_cases hpj : p.val ∣ j
    · rw [if_pos hpj]
      have hfglobal := hSglobal hfS
      exact Fintype.mem_piFinset.mp hfglobal p
    · rw [if_neg hpj]
      have hpL : ¬p.val ∣ height f := by
        intro hpheight
        exact hpj (dvd_trans hpheight hfdiv)
      simpa [hfw] using hcompat f hfS p hpL
  calc
    (∑ f ∈ T, pairMultiplierGlobalWeight P f) ≤
        ∑ f ∈ globalRationalAllowedLabels P K j w,
          pairMultiplierGlobalWeight P f :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∏ p : ↥P,
        ∑ ab ∈ rationalAllowedLabelPairs p.val K j w,
          pairMultiplierLocalWeight p.val ab := by
      exact sum_globalRationalAllowedLabels_weight P K j w
    _ ≤ ∏ p : ↥P,
        (if p.val ∣ j then p.val - 1 + 2 * (K * K - 1)
          else K - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        unfold rationalAllowedLabelPairs
        by_cases hpj : p.val ∣ j
        · rw [if_pos hpj, if_pos hpj,
            sum_pairMultiplierLocalWeight_all hK]
          omega
        · rw [if_neg hpj, if_neg hpj,
            sum_pairMultiplierLocalWeight_compatible]
          have hwnz : w ≠ (0, 0) :=
            (Finset.mem_erase.mp hw).1
          have hst : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
            by_contra hz
            push Not at hz
            apply hwnz
            exact Prod.ext hz.1 hz.2
          exact card_compatibleRatioLabels_le hK hst
    _ = twoStateLocalWeight P
        (fun p ↦ p - 1 + 2 * (K * K - 1))
        (fun _p ↦ K - 1) j := by
      unfold twoStateLocalWeight
      rw [← Finset.attach_eq_univ]
      simpa using Finset.prod_attach P (fun p ↦
        if p ∣ j then p - 1 + 2 * (K * K - 1) else K - 1)

/-- Summing all rational fibres and all repetitions of their selected vector
is bounded by `K²-1` copies of F-035's rational boundary moment. -/
theorem rational_repeated_weight_le_moment
    (P : Finset ℕ) (K Y : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (S : Finset (∀ _p : ↥P, ℕ × ℕ))
    (height : (∀ _p : ↥P, ℕ × ℕ) → ℕ)
    (witness : (∀ _p : ↥P, ℕ × ℕ) → ℕ × ℕ)
    (hSglobal : S ⊆ globalLabelPairs P K)
    (hheight : ∀ f ∈ S, 0 < height f)
    (hwitness : ∀ f ∈ S, witness f ∈ nonzeroLabelPairs K)
    (hcompat : ∀ f ∈ S, ∀ p : ↥P, ¬p.val ∣ height f →
      f p ∈ compatibleRatioLabels K (witness f).1 (witness f).2) :
    (∑ f ∈ S,
      pairMultiplierGlobalWeight P f * (Y / height f)) ≤
      (K * K - 1) * rationalBoundaryMoment P K (K - 1) Y := by
  have hpoint : ∀ f ∈ S,
      pairMultiplierGlobalWeight P f * (Y / height f) =
        ∑ j ∈ Icc 1 Y,
          pairMultiplierGlobalWeight P f *
            (if height f ∣ j then 1 else 0) := by
    intro f hf
    rw [← Finset.mul_sum]
    congr 1
    exact (sum_Icc_dvd_indicator (hheight f hf)).symm
  calc
    (∑ f ∈ S,
      pairMultiplierGlobalWeight P f * (Y / height f)) =
        ∑ f ∈ S, ∑ j ∈ Icc 1 Y,
          pairMultiplierGlobalWeight P f *
            (if height f ∣ j then 1 else 0) := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = ∑ j ∈ Icc 1 Y, ∑ f ∈ S,
          pairMultiplierGlobalWeight P f *
            (if height f ∣ j then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Icc 1 Y, ∑ w ∈ nonzeroLabelPairs K,
          ∑ f ∈ S.filter (fun f ↦ witness f = w ∧ height f ∣ j),
            pairMultiplierGlobalWeight P f := by
      apply Finset.sum_congr rfl
      intro j hj
      symm
      calc
        (∑ w ∈ nonzeroLabelPairs K,
          ∑ f ∈ S.filter (fun f ↦ witness f = w ∧ height f ∣ j),
            pairMultiplierGlobalWeight P f) =
          ∑ w ∈ nonzeroLabelPairs K, ∑ f ∈ S,
            if witness f = w ∧ height f ∣ j then
              pairMultiplierGlobalWeight P f else 0 := by
                simp_rw [Finset.sum_filter]
        _ = ∑ f ∈ S, ∑ w ∈ nonzeroLabelPairs K,
            if witness f = w ∧ height f ∣ j then
              pairMultiplierGlobalWeight P f else 0 := by
                rw [Finset.sum_comm]
        _ = ∑ f ∈ S,
            pairMultiplierGlobalWeight P f *
              (if height f ∣ j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro f hf
          by_cases hdiv : height f ∣ j
          · have hw := hwitness f hf
            simp only [hdiv, and_true, if_true, mul_one]
            rw [Finset.sum_ite_eq]
            simp [hw]
          · simp [hdiv]
    _ ≤ ∑ j ∈ Icc 1 Y,
        (K * K - 1) * twoStateLocalWeight P
          (fun p ↦ p - 1 + 2 * (K * K - 1))
          (fun _p ↦ K - 1) j := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ w ∈ nonzeroLabelPairs K,
          ∑ f ∈ S.filter (fun f ↦ witness f = w ∧ height f ∣ j),
            pairMultiplierGlobalWeight P f) ≤
          ∑ _w ∈ nonzeroLabelPairs K,
            twoStateLocalWeight P
              (fun p ↦ p - 1 + 2 * (K * K - 1))
              (fun _p ↦ K - 1) j := by
          apply Finset.sum_le_sum
          intro w hw
          exact rational_witness_fibre_weight_le P K j hK hprime w hw
            S height witness hSglobal hcompat
        _ = (K * K - 1) * twoStateLocalWeight P
              (fun p ↦ p - 1 + 2 * (K * K - 1))
              (fun _p ↦ K - 1) j := by
          have hcard : (nonzeroLabelPairs K).card = K * K - 1 := by
            simpa [nonzeroLabelPairs, allLabelPairs] using
              (card_allLabelPairs_erase_zero hK)
          simp [hcard]
    _ = (K * K - 1) * rationalBoundaryMoment P K (K - 1) Y := by
      unfold rationalBoundaryMoment twoStateMoment
      rw [Finset.mul_sum]

/-- Real boundary form: `Y/L < ⌊Y/L⌋+1` converts every rational
`40Y/L` term into the repeated-weight moment plus one additive state weight. -/
theorem rational_real_boundary_le
    (P : Finset ℕ) (K Y : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (S : Finset (∀ _p : ↥P, ℕ × ℕ))
    (height : (∀ _p : ↥P, ℕ × ℕ) → ℕ)
    (witness : (∀ _p : ↥P, ℕ × ℕ) → ℕ × ℕ)
    (hSglobal : S ⊆ globalLabelPairs P K)
    (hheight : ∀ f ∈ S, 0 < height f)
    (hwitness : ∀ f ∈ S, witness f ∈ nonzeroLabelPairs K)
    (hcompat : ∀ f ∈ S, ∀ p : ↥P, ¬p.val ∣ height f →
      f p ∈ compatibleRatioLabels K (witness f).1 (witness f).2) :
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))) ≤
      40 * (K * K - 1 : ℕ) *
          (rationalBoundaryMoment P K (K - 1) Y : ℝ) +
        40 * ∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) := by
  have hterm : ∀ f ∈ S,
      (pairMultiplierGlobalWeight P f : ℝ) *
          (40 * ((Y : ℝ) / (height f : ℝ))) ≤
        40 * (pairMultiplierGlobalWeight P f * (Y / height f) : ℕ) +
          40 * (pairMultiplierGlobalWeight P f : ℝ) := by
    intro f hf
    have hfloor := (natCast_div_lt_natDiv_add_one (Y := Y)
      (hheight f hf)).le
    have hw0 : (0 : ℝ) ≤ pairMultiplierGlobalWeight P f := by positivity
    push_cast
    nlinarith
  calc
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) *
      (40 * ((Y : ℝ) / (height f : ℝ)))) ≤
        ∑ f ∈ S,
          (40 * (pairMultiplierGlobalWeight P f * (Y / height f) : ℕ) +
            40 * (pairMultiplierGlobalWeight P f : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = 40 * (∑ f ∈ S,
          pairMultiplierGlobalWeight P f * (Y / height f) : ℕ) +
        40 * ∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) := by
      push_cast
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 40 * (K * K - 1 : ℕ) *
          (rationalBoundaryMoment P K (K - 1) Y : ℝ) +
        40 * ∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) := by
      have hrep := rational_repeated_weight_le_moment P K Y hK hprime
        S height witness hSglobal hheight hwitness hcompat
      have hrepR :
          ((∑ f ∈ S, pairMultiplierGlobalWeight P f *
            (Y / height f) : ℕ) : ℝ) ≤
          (((K * K - 1) * rationalBoundaryMoment P K (K - 1) Y : ℕ) : ℝ) := by
        exact_mod_cast hrep
      norm_num only [Nat.cast_mul] at hrepR
      nlinarith

/-- A global multiplier weight divided by the local unit universe factors as
F-059's constant-error local weight. -/
theorem pairMultiplierGlobalWeight_div_primeUnitCount
    (P : Finset ℕ) (K : ℕ) (f : ∀ _p : ↥P, ℕ × ℕ)
    (hf : f ∈ globalLabelPairs P K)
    (hprime : ∀ p ∈ P, p.Prime) :
    (pairMultiplierGlobalWeight P f : ℝ) / (primeUnitCount P : ℝ) =
      ∏ p : ↥P, pairConstantLocalFactor p.val K (f p) := by
  unfold pairMultiplierGlobalWeight primeUnitCount
  push_cast
  rw [← Finset.attach_eq_univ]
  rw [← Finset.prod_attach P (fun p ↦ ((p - 1 : ℕ) : ℝ))]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP : p.val ∈ P := p.property
  have hp2 : 2 ≤ p.val := (hprime p.val hpP).two_le
  have hp1 : (0 : ℝ) < (p.val - 1 : ℕ) := by
    exact_mod_cast (show 0 < p.val - 1 by omega)
  have hfp := Fintype.mem_piFinset.mp hf p
  unfold pairMultiplierLocalWeight pairConstantLocalFactor
  by_cases hz : f p = (0, 0)
  · simp [hz, ne_of_gt hp1]
  · simp [hz]

/-- Therefore any subset of global label states has normalized total
multiplier weight at most F-059's constant Euler sum. -/
theorem normalized_pairMultiplierWeight_subset_le
    (P : Finset ℕ) (K : ℕ) (hK : 0 < K)
    (hprime : ∀ p ∈ P, p.Prime)
    (S : Finset (∀ _p : ↥P, ℕ × ℕ))
    (hS : S ⊆ globalLabelPairs P K) :
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ)) /
        (primeUnitCount P : ℝ) ≤
      ∏ p ∈ P,
        (1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hprime p hp).two_le
        omega)
  rw [Finset.sum_div]
  calc
    (∑ f ∈ S, (pairMultiplierGlobalWeight P f : ℝ) /
      (primeUnitCount P : ℝ)) =
        ∑ f ∈ S, ∏ p : ↥P,
          pairConstantLocalFactor p.val K (f p) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact pairMultiplierGlobalWeight_div_primeUnitCount P K f
        (hS hf) hprime
    _ ≤ ∑ f ∈ globalLabelPairs P K, ∏ p : ↥P,
          pairConstantLocalFactor p.val K (f p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro f hf hnot
      apply Finset.prod_nonneg
      intro p hp
      unfold pairConstantLocalFactor
      split_ifs <;> positivity
    _ = ∏ p ∈ P,
        (1 + ((K * K - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
      global_constant_label_sum_eq P K hK

end Erdos394
