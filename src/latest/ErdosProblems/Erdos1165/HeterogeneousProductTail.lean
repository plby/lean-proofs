/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.HLOZThresholdedShellScreening
import ErdosProblems.Erdos1165.PreStoppingConditionalLaw

/-!
# Heterogeneous exact-total product tails

The stopped product fibre in HLOZ has one (truncated) negative-binomial
coordinate for every retained spatial domino.  The external multiplicity and
the truncation can vary with the domino, so the adjacent-shell count is not a
binomial random variable with one globally fixed parameter.

This file proves the finite replacement used by the thresholded shell
screen.  We first fix the *actual support* of coordinates which land in the
two adjacent windows.  On that support the product moment at `log 2`
factorizes coordinatewise.  A uniform upper/lower window-mass comparison
bounds each factor.  We then sum over all supports of the prescribed, genuinely
random, total size.  Thus neither independence after conditioning on the
total nor a homogeneous parameter is postulated.
-/

open Set
open scoped BigOperators

namespace Erdos1165.HeterogeneousProductTail

open NearFavoriteThresholded
open HLOZThresholdedShellScreening

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
variable {State : Coordinate → Type*} [∀ c, Fintype (State c)]

/-- Product point mass of a heterogeneous finite coordinate vector. -/
def productPointMass (weight : ∀ c, State c → ℝ)
    (ell : ∀ c, State c) : ℝ :=
  ∏ c, weight c (ell c)

/-- Coordinates whose values lie in either of the two adjacent windows. -/
def pairSupport (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (ell : ∀ c, State c) : Finset Coordinate :=
  Finset.univ.filter fun c ↦ upper c (ell c) ∨ lower c (ell c)

/-- Number of coordinates in the upper one of the two adjacent windows. -/
def upperCount (upper : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] (ell : ∀ c, State c) : ℕ :=
  ∑ c, if upper c (ell c) then 1 else 0

/-- Exact pair-total fibre together with an upper-count tail. -/
def fixedTotalUpperTail (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total cut : ℕ) (ell : ∀ c, State c) : Prop :=
  (pairSupport upper lower ell).card = total ∧ cut ≤ upperCount upper ell

instance instDecidablePredFixedTotalUpperTail
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total cut : ℕ) : DecidablePred (fixedTotalUpperTail upper lower total cut) :=
  fun ell ↦ by
    unfold fixedTotalUpperTail
    infer_instance

/-- Restrict a coordinate weight to one prescribed adjacent-window support. -/
def supportWeight (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) (c : Coordinate) (v : State c) : ℝ :=
  if c ∈ A then
    if upper c v ∨ lower c v then weight c v else 0
  else
    if upper c v ∨ lower c v then 0 else weight c v

/-- Total product mass carried by one exact adjacent-window support. -/
def supportMass (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) : ℝ :=
  ∏ c, ∑ v, supportWeight weight upper lower A c v

/-- The mass of the genuinely random adjacent-pair total. -/
def exactPairTotalMass (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total : ℕ) : ℝ :=
  ∑ ell : ∀ c, State c,
    if (pairSupport upper lower ell).card = total then
      productPointMass weight ell else 0

lemma productPointMass_nonneg
    (weight : ∀ c, State c → ℝ) (hweight : ∀ c v, 0 ≤ weight c v)
    (ell : ∀ c, State c) :
    0 ≤ productPointMass weight ell := by
  exact Finset.prod_nonneg fun c _ ↦ hweight c (ell c)

lemma supportWeight_nonneg
    (weight : ∀ c, State c → ℝ) (hweight : ∀ c v, 0 ≤ weight c v)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) (c : Coordinate) (v : State c) :
    0 ≤ supportWeight weight upper lower A c v := by
  unfold supportWeight
  split_ifs
  · exact hweight c v
  · exact le_rfl
  · exact le_rfl
  · exact hweight c v

lemma prod_supportWeight_eq
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) (ell : ∀ c, State c) :
    (∏ c, supportWeight weight upper lower A c (ell c)) =
      if pairSupport upper lower ell = A then productPointMass weight ell else 0 := by
  classical
  by_cases hsupport : pairSupport upper lower ell = A
  · rw [if_pos hsupport]
    unfold productPointMass
    apply Finset.prod_congr rfl
    intro c _
    have hc : (c ∈ A) ↔ (upper c (ell c) ∨ lower c (ell c)) := by
      rw [← hsupport]
      simp [pairSupport]
    unfold supportWeight
    by_cases hA : c ∈ A
    · simp [hA, hc.mp hA]
    · have hpair : ¬ (upper c (ell c) ∨ lower c (ell c)) :=
        fun h ↦ hA (hc.mpr h)
      simp [hA, hpair]
  · rw [if_neg hsupport]
    have hdiff : ∃ c, (c ∈ A) ≠ (upper c (ell c) ∨ lower c (ell c)) := by
      by_contra hnot
      apply hsupport
      ext c
      have hc : (c ∈ A) = (upper c (ell c) ∨ lower c (ell c)) := by
        by_contra hne
        exact hnot ⟨c, hne⟩
      simpa [pairSupport] using hc.symm
    obtain ⟨c, hc⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    unfold supportWeight
    by_cases hA : c ∈ A
    · have hpair : ¬ (upper c (ell c) ∨ lower c (ell c)) := by
        intro hp
        exact hc (propext ⟨fun _ ↦ hp, fun _ ↦ hA⟩)
      simp [hA, hpair]
    · have hpair : upper c (ell c) ∨ lower c (ell c) := by
        by_contra hp
        exact hc (propext ⟨fun h ↦ (hA h).elim, fun h ↦ (hp h).elim⟩)
      simp [hA, hpair]

lemma sum_support_eq_supportMass
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) :
    (∑ ell : ∀ c, State c,
      if pairSupport upper lower ell = A then productPointMass weight ell else 0) =
        supportMass weight upper lower A := by
  classical
  calc
    (∑ ell : ∀ c, State c,
      if pairSupport upper lower ell = A then productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c,
          ∏ c, supportWeight weight upper lower A c (ell c) := by
      apply Finset.sum_congr rfl
      intro ell _
      exact (prod_supportWeight_eq weight upper lower A ell).symm
    _ = ∏ c, ∑ v, supportWeight weight upper lower A c v :=
      (Fintype.prod_sum (supportWeight weight upper lower A)).symm
    _ = supportMass weight upper lower A := rfl

lemma fixedTotalMass_eq_exactPairTotalMass
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total : ℕ) :
    (∑ ell : ∀ c, State c,
      if (pairSupport upper lower ell).card = total then
        productPointMass weight ell else 0) =
      exactPairTotalMass weight upper lower total := by
  rfl

lemma exactPairTotalMass_eq_sum_supportMass
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total : ℕ) :
    exactPairTotalMass weight upper lower total =
      ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
        supportMass weight upper lower A := by
  classical
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (s := (Finset.univ : Finset (∀ c, State c)))
    (t := (Finset.univ : Finset (Finset Coordinate)).filter
      fun A ↦ A.card = total)
    (pairSupport upper lower) (productPointMass weight)
  simp_rw [← sum_support_eq_supportMass weight upper lower]
  simpa [exactPairTotalMass, Finset.sum_filter] using hfiber.symm

lemma fixedTotalUpperTailMass_eq_sum_supportTail
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total cut : ℕ) :
    (∑ ell : ∀ c, State c,
      if fixedTotalUpperTail upper lower total cut ell then
        productPointMass weight ell else 0) =
      ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
        ∑ ell : ∀ c, State c,
          if pairSupport upper lower ell = A ∧ cut ≤ upperCount upper ell then
            productPointMass weight ell else 0 := by
  classical
  let f : (∀ c, State c) → ℝ := fun ell ↦
    if cut ≤ upperCount upper ell then productPointMass weight ell else 0
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (s := (Finset.univ : Finset (∀ c, State c)))
    (t := (Finset.univ : Finset (Finset Coordinate)).filter
      fun A ↦ A.card = total)
    (pairSupport upper lower) f
  calc
    (∑ ell : ∀ c, State c,
      if fixedTotalUpperTail upper lower total cut ell then
        productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c,
          if (pairSupport upper lower ell).card = total then
            if cut ≤ upperCount upper ell then productPointMass weight ell else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      by_cases htotal : (pairSupport upper lower ell).card = total <;>
        by_cases hcut : cut ≤ upperCount upper ell <;>
          simp [fixedTotalUpperTail, htotal, hcut]
    _ = ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
        ∑ ell : ∀ c, State c,
          if pairSupport upper lower ell = A then
            if cut ≤ upperCount upper ell then productPointMass weight ell else 0
          else 0 := by
      simpa [f, Finset.sum_filter] using hfiber.symm
    _ = ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
        ∑ ell : ∀ c, State c,
          if pairSupport upper lower ell = A ∧ cut ≤ upperCount upper ell then
            productPointMass weight ell else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro ell _
      by_cases hs : pairSupport upper lower ell = A <;>
        by_cases hc : cut ≤ upperCount upper ell <;> simp [hs, hc]

lemma exactPairTotalMass_nonneg
    (weight : ∀ c, State c → ℝ) (hweight : ∀ c v, 0 ≤ weight c v)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (total : ℕ) :
    0 ≤ exactPairTotalMass weight upper lower total := by
  rw [← fixedTotalMass_eq_exactPairTotalMass]
  exact Finset.sum_nonneg fun ell _ ↦ by
    split_ifs
    · exact productPointMass_nonneg weight hweight ell
    · exact le_rfl

lemma supportWeight_mul_two_pow_upperCount_eq
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (A : Finset Coordinate) (ell : ∀ c, State c) :
    (∏ c, supportWeight weight upper lower A c (ell c)) *
        (2 : ℝ) ^ upperCount upper ell =
      ∏ c, supportWeight weight upper lower A c (ell c) *
        (if upper c (ell c) then 2 else 1) := by
  classical
  unfold upperCount
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ
    (fun c ↦ if upper c (ell c) then 1 else 0) (2 : ℝ)]
  simp_rw [pow_ite, pow_one, pow_zero]
  exact Finset.prod_mul_distrib.symm

lemma coordinate_moment_le
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (A : Finset Coordinate) (c : Coordinate) :
    (∑ v, supportWeight weight upper lower A c v *
        (if upper c v then 2 else 1)) ≤
      (if c ∈ A then 1 + C / (1 + C) else 1) *
        ∑ v, supportWeight weight upper lower A c v := by
  classical
  by_cases hA : c ∈ A
  · rw [if_pos hA]
    let p : ℝ := ∑ v, if upper c v then weight c v else 0
    let q : ℝ := ∑ v, if lower c v then weight c v else 0
    have hp : 0 ≤ p := by
      dsimp only [p]
      exact Finset.sum_nonneg fun v _ ↦ by
        split_ifs with h
        · exact hweight c v
        · exact le_rfl
    have hq : 0 ≤ q := by
      dsimp only [q]
      exact Finset.sum_nonneg fun v _ ↦ by
        split_ifs with h
        · exact hweight c v
        · exact le_rfl
    have hpq : p ≤ C * q := hratio c
    have hden : 0 < 1 + C := by linarith
    have hleft :
        (∑ v, supportWeight weight upper lower A c v *
            (if upper c v then 2 else 1)) = 2 * p + q := by
      unfold supportWeight
      simp only [hA, if_pos]
      calc
        (∑ v, (if upper c v ∨ lower c v then weight c v else 0) *
            if upper c v then 2 else 1) =
            ∑ v, (2 * (if upper c v then weight c v else 0) +
              (if lower c v then weight c v else 0)) := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hu : upper c v
          · have hnl : ¬ lower c v := fun hl ↦ hdisjoint c v ⟨hu, hl⟩
            simp [hu, hnl]
            ring
          · by_cases hl : lower c v <;> simp [hu, hl]
        _ = 2 * p + q := by
          dsimp only [p, q]
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    have hright :
        (∑ v, supportWeight weight upper lower A c v) = p + q := by
      unfold supportWeight
      simp only [hA, if_pos]
      calc
        (∑ v, if upper c v ∨ lower c v then weight c v else 0) =
            ∑ v, ((if upper c v then weight c v else 0) +
              (if lower c v then weight c v else 0)) := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hu : upper c v
          · have hnl : ¬ lower c v := fun hl ↦ hdisjoint c v ⟨hu, hl⟩
            simp [hu, hnl]
          · by_cases hl : lower c v <;> simp [hu, hl]
        _ = p + q := by
          dsimp only [p, q]
          rw [Finset.sum_add_distrib]
    rw [hleft, hright]
    have hid :
        (1 + C / (1 + C)) * (p + q) =
          ((1 + 2 * C) * (p + q)) / (1 + C) := by
      field_simp
      ring
    rw [hid, le_div_iff₀ hden]
    nlinarith
  · rw [if_neg hA, one_mul]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro v _
    unfold supportWeight
    by_cases hp : upper c v ∨ lower c v
    · simp [hA, hp]
    · have hu : ¬ upper c v := fun h ↦ hp (Or.inl h)
      simp [hA, hu]

lemma support_moment_le
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (A : Finset Coordinate) :
    (∑ ell : ∀ c, State c,
        (∏ c, supportWeight weight upper lower A c (ell c)) *
          (2 : ℝ) ^ upperCount upper ell) ≤
      (1 + C / (1 + C)) ^ A.card * supportMass weight upper lower A := by
  classical
  simp_rw [supportWeight_mul_two_pow_upperCount_eq]
  calc
    (∑ ell : ∀ c, State c,
      ∏ c, supportWeight weight upper lower A c (ell c) *
        (if upper c (ell c) then 2 else 1)) =
        ∏ c, ∑ v, supportWeight weight upper lower A c v *
          (if upper c v then 2 else 1) :=
      (Fintype.prod_sum (fun c v ↦
        supportWeight weight upper lower A c v *
          (if upper c v then 2 else 1))).symm
    _ ≤
        ∏ c, (if c ∈ A then 1 + C / (1 + C) else 1) *
          ∑ v, supportWeight weight upper lower A c v := by
      apply Finset.prod_le_prod
      · intro c _
        exact Finset.sum_nonneg fun v _ ↦ by
          exact mul_nonneg (supportWeight_nonneg weight hweight upper lower A c v)
            (by split_ifs <;> norm_num)
      · intro c _
        exact coordinate_moment_le weight upper lower hweight hdisjoint hC
          hratio A c
    _ = (1 + C / (1 + C)) ^ A.card *
        ∏ c, ∑ v, supportWeight weight upper lower A c v := by
      rw [Finset.prod_mul_distrib]
      congr 1
      simp
    _ = (1 + C / (1 + C)) ^ A.card *
        supportMass weight upper lower A := rfl

lemma support_upperTail_le
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (A : Finset Coordinate) (cut : ℕ) :
    (∑ ell : ∀ c, State c,
      if pairSupport upper lower ell = A ∧ cut ≤ upperCount upper ell then
        productPointMass weight ell else 0) ≤
      (1 + C / (1 + C)) ^ A.card * supportMass weight upper lower A /
        (2 : ℝ) ^ cut := by
  classical
  calc
    (∑ ell : ∀ c, State c,
      if pairSupport upper lower ell = A ∧ cut ≤ upperCount upper ell then
        productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c,
          if cut ≤ upperCount upper ell then
            ∏ c, supportWeight weight upper lower A c (ell c) else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [prod_supportWeight_eq]
      by_cases hs : pairSupport upper lower ell = A <;>
        by_cases hc : cut ≤ upperCount upper ell <;> simp [hs, hc]
    _ ≤ (∑ ell : ∀ c, State c,
          (∏ c, supportWeight weight upper lower A c (ell c)) *
            (2 : ℝ) ^ upperCount upper ell) / (2 : ℝ) ^ cut := by
      apply (le_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ cut)).2
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ell _
      by_cases hell : cut ≤ upperCount upper ell
      · rw [if_pos hell]
        rw [mul_comm ((2 : ℝ) ^ cut)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hell)
          (Finset.prod_nonneg fun c _ ↦
            supportWeight_nonneg weight hweight upper lower A c (ell c))
      · rw [if_neg hell]
        simp only [mul_zero]
        exact mul_nonneg
          (Finset.prod_nonneg fun c _ ↦
            supportWeight_nonneg weight hweight upper lower A c (ell c))
          (by positivity : 0 ≤ (2 : ℝ) ^ upperCount upper ell)
    _ ≤ (1 + C / (1 + C)) ^ A.card *
        supportMass weight upper lower A / (2 : ℝ) ^ cut := by
      exact div_le_div_of_nonneg_right
        (support_moment_le weight upper lower hweight hdisjoint hC hratio A)
        (by positivity)

/-- Heterogeneous fixed-total Chernoff bound, retaining the exact mass of the
realized adjacent-pair total. -/
theorem fixedTotalUpperTail_product_bound
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (total cut : ℕ) :
    (∑ ell : ∀ c, State c,
      if fixedTotalUpperTail upper lower total cut ell then
        productPointMass weight ell else 0) ≤
      exactPairTotalMass weight upper lower total *
        (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
  classical
  have hdecompose :
      (∑ ell : ∀ c, State c,
        if fixedTotalUpperTail upper lower total cut ell then
          productPointMass weight ell else 0) =
        ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
          ∑ ell : ∀ c, State c,
            if pairSupport upper lower ell = A ∧
                cut ≤ upperCount upper ell then
              productPointMass weight ell else 0 :=
    fixedTotalUpperTailMass_eq_sum_supportTail weight upper lower total cut
  rw [hdecompose]
  calc
    (∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
      ∑ ell : ∀ c, State c,
          if pairSupport upper lower ell = A ∧ cut ≤ upperCount upper ell then
            productPointMass weight ell else 0) ≤
        ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard total,
          (1 + C / (1 + C)) ^ total *
            supportMass weight upper lower A / (2 : ℝ) ^ cut := by
      apply Finset.sum_le_sum
      intro A hA
      have hcard : A.card = total := (Finset.mem_powersetCard.mp hA).2
      simpa only [hcard] using
        support_upperTail_le weight upper lower hweight hdisjoint hC
          hratio A cut
    _ = exactPairTotalMass weight upper lower total *
        (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
      rw [exactPairTotalMass_eq_sum_supportMass]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      ring

/-- If every coordinate weight is a subprobability mass, the exact-total
factor in the preceding theorem is at most one. -/
theorem exactPairTotalMass_le_one
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (total : ℕ) :
    exactPairTotalMass weight upper lower total ≤ 1 := by
  rw [← fixedTotalMass_eq_exactPairTotalMass]
  calc
    (∑ ell : ∀ c, State c,
      if (pairSupport upper lower ell).card = total then
        productPointMass weight ell else 0) ≤
        ∑ ell : ∀ c, State c, productPointMass weight ell := by
      apply Finset.sum_le_sum
      intro ell _
      split_ifs
      · exact le_rfl
      · exact productPointMass_nonneg weight hweight ell
    _ = ∏ c, ∑ v, weight c v := by
      exact (Fintype.prod_sum weight).symm
    _ ≤ ∏ _c : Coordinate, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro c _
        exact Finset.sum_nonneg fun v _ ↦ hweight c v
      · intro c _
        exact hnorm c
    _ = 1 := by simp

/-- The masses of all exact realized totals in an arbitrary finite range sum
to at most one.  This is the step which prevents the random-total
disintegration from paying the number of possible totals. -/
theorem sum_exactPairTotalMass_range_le_one
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (bound : ℕ) :
    (∑ total ∈ Finset.range (bound + 1),
      exactPairTotalMass weight upper lower total) ≤ 1 := by
  classical
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (s := (Finset.univ : Finset (∀ c, State c)))
    (t := Finset.range (bound + 1))
    (fun ell ↦ (pairSupport upper lower ell).card)
    (productPointMass weight)
  have hrewrite :
      (∑ total ∈ Finset.range (bound + 1),
        exactPairTotalMass weight upper lower total) =
        ∑ ell : ∀ c, State c,
          if (pairSupport upper lower ell).card < bound + 1 then
            productPointMass weight ell else 0 := by
    simpa [exactPairTotalMass, Finset.sum_filter] using hfiber
  rw [hrewrite]
  calc
    (∑ ell : ∀ c, State c,
      if (pairSupport upper lower ell).card < bound + 1 then
        productPointMass weight ell else 0) ≤
        ∑ ell : ∀ c, State c, productPointMass weight ell := by
      apply Finset.sum_le_sum
      intro ell _
      split_ifs
      · exact le_rfl
      · exact productPointMass_nonneg weight hweight ell
    _ = ∏ c, ∑ v, weight c v := (Fintype.prod_sum weight).symm
    _ ≤ ∏ _c : Coordinate, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro c _
        exact Finset.sum_nonneg fun v _ ↦ hweight c v
      · intro c _
        exact hnorm c
    _ = 1 := by simp

/-- Sum exact-total costs using a uniform envelope, without a factor equal to
the number of totals. -/
theorem sum_exactPairTotalMass_mul_cost_le
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (bound : ℕ) (cost : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ total < bound + 1, cost total ≤ K) :
    (∑ total ∈ Finset.range (bound + 1),
      exactPairTotalMass weight upper lower total * cost total) ≤ K := by
  calc
    (∑ total ∈ Finset.range (bound + 1),
      exactPairTotalMass weight upper lower total * cost total) ≤
        ∑ total ∈ Finset.range (bound + 1),
          exactPairTotalMass weight upper lower total * K := by
      apply Finset.sum_le_sum
      intro total htotal
      exact mul_le_mul_of_nonneg_left
        (hcost total (Finset.mem_range.mp htotal))
        (exactPairTotalMass_nonneg weight hweight upper lower total)
    _ = (∑ total ∈ Finset.range (bound + 1),
        exactPairTotalMass weight upper lower total) * K := by
      rw [Finset.sum_mul]
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right
      (sum_exactPairTotalMass_range_le_one weight upper lower hweight hnorm bound) hK
    _ = K := one_mul K

/-- Unit-mass corollary in the exact form used as a
`RandomTotalProductLaw.product_bound`. -/
theorem fixedTotalUpperTail_product_bound_one
    (weight : ∀ c, State c → ℝ)
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (hweight : ∀ c v, 0 ≤ weight c v)
    (hnorm : ∀ c, (∑ v, weight c v) ≤ 1)
    (hdisjoint : ∀ c v, ¬ (upper c v ∧ lower c v))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c,
      (∑ v, if upper c v then weight c v else 0) ≤
        C * ∑ v, if lower c v then weight c v else 0)
    (total cut : ℕ) :
    (∑ ell : ∀ c, State c,
      if fixedTotalUpperTail upper lower total cut ell then
        productPointMass weight ell else 0) ≤
      (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
  refine (fixedTotalUpperTail_product_bound weight upper lower hweight
    hdisjoint hC hratio total cut).trans ?_
  have hfactor : 0 ≤ (1 + C / (1 + C)) ^ total := by positivity
  have hmass := exactPairTotalMass_le_one weight upper lower hweight hnorm total
  exact div_le_div_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hfactor)
    (by positivity)

/-! ## Direct constructor for the thresholded random-total interface -/

/-- Assemble `RandomTotalProductLaw.product_bound` from heterogeneous finite
product fibres.  The exact-total path/product identity remains the literal
stopped disintegration input; its quantitative consequence is proved here.
-/
def randomTotalProductLawOfHeterogeneousProduct
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) (balanced : ℕ → Set Omega)
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ)
    (G shellCount : ℕ) (totalBound : ℕ → ℕ)
    (Coordinate : ℕ → Type*) [∀ j, Fintype (Coordinate j)]
    [∀ j, DecidableEq (Coordinate j)]
    (State : ∀ j, Coordinate j → Type*)
    [∀ j c, Fintype (State j c)]
    (weight : ∀ j c, State j c → ℝ)
    (upper lower : ∀ j c, State j c → Prop)
    [∀ j c, DecidablePred (upper j c)]
    [∀ j c, DecidablePred (lower j c)]
    (C : ℕ → ℝ)
    (hpairBound : ∀ j < shellCount - 1, ∀ omega,
      omega ∈ balanced j ∩ thresholdedGrowthFailure occupancy threshold G j →
        occupancy omega j + occupancy omega (j + 1) ≤ totalBound j)
    (hdisintegrate : ∀ j < shellCount - 1, ∀ total < totalBound j + 1,
      mu.real (fixedTotalThresholdedFailure balanced occupancy threshold
        G j total) =
        ∑ ell : ∀ c, State j c,
          if fixedTotalUpperTail (upper j) (lower j) total
              (thresholdedGrowthCut threshold G j total) ell then
            productPointMass (weight j) ell else 0)
    (hweight : ∀ j c v, 0 ≤ weight j c v)
    (hdisjoint : ∀ j c v, ¬ (upper j c v ∧ lower j c v))
    (hC : ∀ j, 0 ≤ C j)
    (hratio : ∀ j c,
      (∑ v, if upper j c v then weight j c v else 0) ≤
        C j * ∑ v, if lower j c v then weight j c v else 0) :
    RandomTotalProductLaw mu balanced occupancy threshold G shellCount where
  totalBound := totalBound
  productMass j total :=
    ∑ ell : ∀ c, State j c,
      if fixedTotalUpperTail (upper j) (lower j) total
          (thresholdedGrowthCut threshold G j total) ell then
        productPointMass (weight j) ell else 0
  fixedCost j total :=
    exactPairTotalMass (weight j) (upper j) (lower j) total *
      (1 + C j / (1 + C j)) ^ total /
        (2 : ℝ) ^ thresholdedGrowthCut threshold G j total
  pair_bound := hpairBound
  disintegrate := hdisintegrate
  product_bound := by
    intro j hj total htotal
    exact fixedTotalUpperTail_product_bound (weight j) (upper j) (lower j)
      (hweight j) (hdisjoint j) (hC j) (hratio j) total
      (thresholdedGrowthCut threshold G j total)

/-! ## Literal prefix-corrected truncated negative-binomial product -/

open LazyDecomposition PathInsertion SpatialInsertionFiber
open PrefixConditionalLaw PreStoppingConditionalLaw
open NegativeBinomial SmallWindow
open NegativeBinomialLocalCLT ScreeningInstantiation

lemma upperTruncatedDominoMass_nonneg
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (cap : ExternalDomino x r → ℕ) (b : ExternalDomino x r) (v : ℕ) :
    0 ≤ upperTruncatedDominoMass x r cap b v := by
  unfold upperTruncatedDominoMass
  split_ifs
  · apply div_nonneg
    · exact NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) _ _
    · exact Finset.sum_nonneg fun j _ ↦
        NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) _ _
  · exact le_rfl

lemma sum_upperTruncatedDominoMass_eq_one
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (cap : ExternalDomino x r → ℕ) (b : ExternalDomino x r)
    (hcap : 0 < cap b) :
    (∑ v : Fin (cap b), upperTruncatedDominoMass x r cap b v) = 1 := by
  let successes := dominoExternalMultiplicity x r b
  have hs : 0 < successes := dominoExternalMultiplicity_pos x r b
  let den : ℝ := ∑ j ∈ Finset.range (cap b),
    NegativeBinomial.mass (15 / 16 : ℝ) successes j
  have hden : 0 < den := by
    dsimp only [den]
    apply Finset.sum_pos'
    · intro j hj
      exact NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) _ _
    · refine ⟨0, Finset.mem_range.mpr hcap, ?_⟩
      exact NegativeBinomial.mass_pos (by norm_num) (by norm_num) hs 0
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ upperTruncatedDominoMass x r cap b k) (cap b)]
  calc
    (∑ j ∈ Finset.range (cap b), upperTruncatedDominoMass x r cap b j) =
        ∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ) successes j / den := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold upperTruncatedDominoMass
      rw [if_pos (Finset.mem_range.mp hj)]
    _ = den / den := by
      rw [Finset.sum_div]
    _ = 1 := div_self hden.ne'

/-- A finite value window has its untruncated HLOZ mass divided by the common
coordinate truncation normalizer. -/
lemma sum_upperTruncatedDominoMass_window
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (cap : ExternalDomino x r → ℕ) (b : ExternalDomino x r)
    (window : Finset ℕ)
    (hwindow : ∀ v ∈ window, v < cap b) :
    (∑ v : Fin (cap b),
      if (v : ℕ) ∈ window then upperTruncatedDominoMass x r cap b v else 0) =
      windowMass (dominoExternalMultiplicity x r b) window /
        ∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ)
            (dominoExternalMultiplicity x r b) j := by
  let successes := dominoExternalMultiplicity x r b
  let den : ℝ := ∑ j ∈ Finset.range (cap b),
    NegativeBinomial.mass (15 / 16 : ℝ) successes j
  have hfilter :
      (Finset.range (cap b)).filter (fun v ↦ v ∈ window) = window := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h ↦ h.2
    · intro hv
      exact ⟨hwindow v hv, hv⟩
  change (∑ v : Fin (cap b),
      (fun k : ℕ ↦ if k ∈ window then
        upperTruncatedDominoMass x r cap b k else 0) v) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ if k ∈ window then
      upperTruncatedDominoMass x r cap b k else 0) (cap b)]
  rw [← Finset.sum_filter, hfilter]
  calc
    (∑ v ∈ window, upperTruncatedDominoMass x r cap b v) =
        ∑ v ∈ window,
          NegativeBinomial.mass (15 / 16 : ℝ) successes v / den := by
      apply Finset.sum_congr rfl
      intro v hv
      unfold upperTruncatedDominoMass
      rw [if_pos (hwindow v hv)]
    _ = windowMass successes window / den := by
      rw [← Finset.sum_div]
      unfold windowMass hlozMass hlozSuccess
      rfl
    _ = windowMass (dominoExternalMultiplicity x r b) window /
        ∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ)
            (dominoExternalMultiplicity x r b) j := rfl

/-- The checked untruncated window comparison survives every positive,
coordinate-dependent prefix truncation. -/
lemma upperTruncatedDominoMass_window_ratio
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (cap : ExternalDomino x r → ℕ) (b : ExternalDomino x r)
    (upperWindow lowerWindow : Finset ℕ) {C : ℝ}
    (hupper : ∀ v ∈ upperWindow, v < cap b)
    (hlower : ∀ v ∈ lowerWindow, v < cap b)
    (hratio : windowMass (dominoExternalMultiplicity x r b) upperWindow ≤
      C * windowMass (dominoExternalMultiplicity x r b) lowerWindow) :
    (∑ v : Fin (cap b),
      if (v : ℕ) ∈ upperWindow then
        upperTruncatedDominoMass x r cap b v else 0) ≤
      C * ∑ v : Fin (cap b),
        if (v : ℕ) ∈ lowerWindow then
          upperTruncatedDominoMass x r cap b v else 0 := by
  rw [sum_upperTruncatedDominoMass_window x r cap b upperWindow hupper,
    sum_upperTruncatedDominoMass_window x r cap b lowerWindow hlower]
  have hden : 0 ≤
      ∑ j ∈ Finset.range (cap b),
        NegativeBinomial.mass (15 / 16 : ℝ)
          (dominoExternalMultiplicity x r b) j :=
    Finset.sum_nonneg fun j _ ↦
      NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) _ _
  calc
    windowMass (dominoExternalMultiplicity x r b) upperWindow /
        (∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ)
            (dominoExternalMultiplicity x r b) j) ≤
      (C * windowMass (dominoExternalMultiplicity x r b) lowerWindow) /
        (∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ)
            (dominoExternalMultiplicity x r b) j) :=
      div_le_div_of_nonneg_right hratio hden
    _ = C * (windowMass (dominoExternalMultiplicity x r b) lowerWindow /
        (∑ j ∈ Finset.range (cap b),
          NegativeBinomial.mass (15 / 16 : ℝ)
            (dominoExternalMultiplicity x r b) j)) := by ring

/-- Local-CLT specialization of the preceding truncation-invariant ratio.
This is the heterogeneous form used by the HLOZ adjacent-shell windows. -/
lemma upperTruncatedDominoMass_window_ratio_of_localCLT
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (cap : ExternalDomino x r → ℕ) (b : ExternalDomino x r)
    (upperWindow lowerWindow : Finset ℕ)
    (hupperCap : ∀ v ∈ upperWindow, v < cap b)
    (hlowerCap : ∀ v ∈ lowerWindow, v < cap b)
    {D W : ℝ} (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hmoderate : D ≤ (dominoExternalMultiplicity x r b : ℝ) / 30)
    (hlower : lowerWindow.Nonempty)
    (hcard : upperWindow.card ≤ lowerWindow.card)
    (hupperDev : ∀ v ∈ upperWindow,
      |deviation (dominoExternalMultiplicity x r b) v| ≤ D)
    (hlowerDev : ∀ v ∈ lowerWindow,
      |deviation (dominoExternalMultiplicity x r b) v| ≤ D)
    (hpair : ∀ u ∈ upperWindow, ∀ l ∈ lowerWindow,
      |deviation (dominoExternalMultiplicity x r b) u -
        deviation (dominoExternalMultiplicity x r b) l| ≤ W) :
    (∑ v : Fin (cap b),
      if (v : ℕ) ∈ upperWindow then
        upperTruncatedDominoMass x r cap b v else 0) ≤
      adjacentLocalRatio (dominoExternalMultiplicity x r b) D W *
        ∑ v : Fin (cap b),
          if (v : ℕ) ∈ lowerWindow then
            upperTruncatedDominoMass x r cap b v else 0 := by
  apply upperTruncatedDominoMass_window_ratio x r cap b upperWindow lowerWindow
    hupperCap hlowerCap
  exact adjacentWindowMass_le_adjacentLocalRatio
    (dominoExternalMultiplicity_pos x r b) hD hW hmoderate hlower hcard
    hupperDev hlowerDev hpair

/-- Literal stopped-product fixed-total tail.  External multiplicities,
windows, and prefix cutoffs may all vary with the away domino. -/
theorem upperProductScreenMass_fixedTotalUpperTail_le
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (D : Finset Point) (cap : ExternalDomino x r → ℕ)
    (upperWindow lowerWindow : AwayDomino x r D → Finset ℕ)
    (hupper : ∀ b v, v ∈ upperWindow b → v < cap b.1)
    (hlower : ∀ b v, v ∈ lowerWindow b → v < cap b.1)
    (hdisjoint : ∀ b, Disjoint (upperWindow b) (lowerWindow b))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ b,
      windowMass (dominoExternalMultiplicity x r b.1) (upperWindow b) ≤
        C * windowMass (dominoExternalMultiplicity x r b.1) (lowerWindow b))
    (total cut : ℕ) :
    upperProductScreenMass x r D cap
        (fixedTotalUpperTail
          (fun b v ↦ (v : ℕ) ∈ upperWindow b)
          (fun b v ↦ (v : ℕ) ∈ lowerWindow b) total cut) ≤
      exactPairTotalMass
          (fun b (v : Fin (cap b.1)) ↦
            upperTruncatedDominoMass x r cap b.1 v)
          (fun b (v : Fin (cap b.1)) ↦ (v : ℕ) ∈ upperWindow b)
          (fun b (v : Fin (cap b.1)) ↦ (v : ℕ) ∈ lowerWindow b) total *
        (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
  let weight : ∀ b : AwayDomino x r D, Fin (cap b.1) → ℝ :=
    fun b v ↦ upperTruncatedDominoMass x r cap b.1 v
  let upperP : ∀ b : AwayDomino x r D, Fin (cap b.1) → Prop :=
    fun b v ↦ (v : ℕ) ∈ upperWindow b
  let lowerP : ∀ b : AwayDomino x r D, Fin (cap b.1) → Prop :=
    fun b v ↦ (v : ℕ) ∈ lowerWindow b
  have hweight : ∀ b v, 0 ≤ weight b v := fun b v ↦
    upperTruncatedDominoMass_nonneg x r cap b.1 v
  have hdisj : ∀ b v, ¬ (upperP b v ∧ lowerP b v) := by
    intro b v hv
    exact Finset.disjoint_left.mp (hdisjoint b) hv.1 hv.2
  have hratio' : ∀ b,
      (∑ v, if upperP b v then weight b v else 0) ≤
        C * ∑ v, if lowerP b v then weight b v else 0 := by
    intro b
    exact upperTruncatedDominoMass_window_ratio x r cap b.1
      (upperWindow b) (lowerWindow b) (hupper b) (hlower b) (hratio b)
  have htail := fixedTotalUpperTail_product_bound
    (Coordinate := AwayDomino x r D) (State := fun b ↦ Fin (cap b.1))
    weight upperP lowerP hweight hdisj hC hratio' total cut
  rw [upperProductScreenMass_eq_product]
  exact htail

/-- Unit-mass version of the literal stopped-product tail, ready for a
`RandomTotalProductLaw.fixedCost` which does not retain the pair-total mass. -/
theorem upperProductScreenMass_fixedTotalUpperTail_le_one
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (D : Finset Point) (cap : ExternalDomino x r → ℕ)
    (hcap : ∀ b : AwayDomino x r D, 0 < cap b.1)
    (upperWindow lowerWindow : AwayDomino x r D → Finset ℕ)
    (hupper : ∀ b v, v ∈ upperWindow b → v < cap b.1)
    (hlower : ∀ b v, v ∈ lowerWindow b → v < cap b.1)
    (hdisjoint : ∀ b, Disjoint (upperWindow b) (lowerWindow b))
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ b,
      windowMass (dominoExternalMultiplicity x r b.1) (upperWindow b) ≤
        C * windowMass (dominoExternalMultiplicity x r b.1) (lowerWindow b))
    (total cut : ℕ) :
    upperProductScreenMass x r D cap
        (fixedTotalUpperTail
          (fun b v ↦ (v : ℕ) ∈ upperWindow b)
          (fun b v ↦ (v : ℕ) ∈ lowerWindow b) total cut) ≤
      (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
  let weight : ∀ b : AwayDomino x r D, Fin (cap b.1) → ℝ :=
    fun b v ↦ upperTruncatedDominoMass x r cap b.1 v
  let upperP : ∀ b : AwayDomino x r D, Fin (cap b.1) → Prop :=
    fun b v ↦ (v : ℕ) ∈ upperWindow b
  let lowerP : ∀ b : AwayDomino x r D, Fin (cap b.1) → Prop :=
    fun b v ↦ (v : ℕ) ∈ lowerWindow b
  have hweight : ∀ b v, 0 ≤ weight b v := fun b v ↦
    upperTruncatedDominoMass_nonneg x r cap b.1 v
  have hnorm : ∀ b, (∑ v, weight b v) ≤ 1 := fun b ↦
    (sum_upperTruncatedDominoMass_eq_one x r cap b.1 (hcap b)).le
  have hdisj : ∀ b v, ¬ (upperP b v ∧ lowerP b v) := by
    intro b v hv
    exact Finset.disjoint_left.mp (hdisjoint b) hv.1 hv.2
  have hratio' : ∀ b,
      (∑ v, if upperP b v then weight b v else 0) ≤
        C * ∑ v, if lowerP b v then weight b v else 0 := by
    intro b
    exact upperTruncatedDominoMass_window_ratio x r cap b.1
      (upperWindow b) (lowerWindow b) (hupper b) (hlower b) (hratio b)
  have htail := fixedTotalUpperTail_product_bound_one
    (Coordinate := AwayDomino x r D) (State := fun b ↦ Fin (cap b.1))
    weight upperP lowerP hweight hnorm hdisj hC hratio' total cut
  rw [upperProductScreenMass_eq_product]
  exact htail

/-- Literal heterogeneous product tail with every point-mass comparison
discharged by the checked logarithmic local CLT. -/
theorem upperProductScreenMass_fixedTotalUpperTail_le_of_localCLT
    {o : Orientation} {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
    (Dset : Finset Point) (cap : ExternalDomino x r → ℕ)
    (upperWindow lowerWindow : AwayDomino x r Dset → Finset ℕ)
    (hupperCap : ∀ b v, v ∈ upperWindow b → v < cap b.1)
    (hlowerCap : ∀ b v, v ∈ lowerWindow b → v < cap b.1)
    (hdisjoint : ∀ b, Disjoint (upperWindow b) (lowerWindow b))
    (radius separation : AwayDomino x r Dset → ℝ)
    (hradius : ∀ b, 0 ≤ radius b)
    (hseparation : ∀ b, 0 ≤ separation b)
    (hmoderate : ∀ b,
      radius b ≤ (dominoExternalMultiplicity x r b.1 : ℝ) / 30)
    (hlower : ∀ b, (lowerWindow b).Nonempty)
    (hcard : ∀ b, (upperWindow b).card ≤ (lowerWindow b).card)
    (hupperDev : ∀ b v, v ∈ upperWindow b →
      |deviation (dominoExternalMultiplicity x r b.1) v| ≤ radius b)
    (hlowerDev : ∀ b v, v ∈ lowerWindow b →
      |deviation (dominoExternalMultiplicity x r b.1) v| ≤ radius b)
    (hpair : ∀ b u, u ∈ upperWindow b → ∀ l, l ∈ lowerWindow b →
      |deviation (dominoExternalMultiplicity x r b.1) u -
        deviation (dominoExternalMultiplicity x r b.1) l| ≤ separation b)
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ b,
      adjacentLocalRatio (dominoExternalMultiplicity x r b.1)
        (radius b) (separation b) ≤ C)
    (total cut : ℕ) :
    upperProductScreenMass x r Dset cap
        (fixedTotalUpperTail
          (fun b v ↦ (v : ℕ) ∈ upperWindow b)
          (fun b v ↦ (v : ℕ) ∈ lowerWindow b) total cut) ≤
      exactPairTotalMass
          (fun b (v : Fin (cap b.1)) ↦
            upperTruncatedDominoMass x r cap b.1 v)
          (fun b (v : Fin (cap b.1)) ↦ (v : ℕ) ∈ upperWindow b)
          (fun b (v : Fin (cap b.1)) ↦ (v : ℕ) ∈ lowerWindow b) total *
        (1 + C / (1 + C)) ^ total / (2 : ℝ) ^ cut := by
  apply upperProductScreenMass_fixedTotalUpperTail_le x r Dset cap
    upperWindow lowerWindow hupperCap hlowerCap hdisjoint hC
  intro b
  refine (adjacentWindowMass_le_adjacentLocalRatio
    (dominoExternalMultiplicity_pos x r b.1) (hradius b) (hseparation b)
    (hmoderate b) (hlower b) (hcard b) (hupperDev b) (hlowerDev b)
    (hpair b)).trans ?_
  exact mul_le_mul_of_nonneg_right (hratio b)
    (windowMass_nonneg (dominoExternalMultiplicity x r b.1) (lowerWindow b))

end

end Erdos1165.HeterogeneousProductTail
