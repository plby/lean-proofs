/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import ErdosProblems.Erdos390.PoissonDickmanDensityReal
import ErdosProblems.Erdos783.GSKernel
import ErdosProblems.Erdos783.PrimeQuadrature
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-!
# Erdős Problem 783

For a reciprocal budget `C`, this file studies pairwise-coprime finite sets
`A ⊆ {2, ..., N}` and the proportion of positive integers at most `N` not
divisible by any member of `A`.  The main theorem is the Tao--Hildebrand
asymptotic resolution: the minimum proportion tends to `ρ (exp C)`, where
`ρ` is the Dickman--de Bruijn function.

The mathematical reconstruction and the correspondence between the
intermediate mathematical and Lean lemmas are in `tex/783.tex`.
-/

open Filter
open scoped BigOperators Topology
open MeasureTheory
open Set

namespace Erdos783

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact finite problem -/

/-- The reciprocal budget used by Erdős. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

@[simp] lemma reciprocalMass_empty : reciprocalMass ∅ = 0 := by
  simp [reciprocalMass]

lemma reciprocalMass_eq_sum (A : Finset ℕ) :
    reciprocalMass A = ∑ a ∈ A, (a : ℝ)⁻¹ := rfl

/-- Pairwise coprimality of the moduli, with distinctness supplied by
`Set.Pairwise`. -/
def PairwiseCoprime (A : Finset ℕ) : Prop :=
  Set.Pairwise (A : Set ℕ) Nat.Coprime

@[simp] lemma pairwiseCoprime_empty : PairwiseCoprime ∅ := by
  simp [PairwiseCoprime]

lemma PairwiseCoprime.mono {A B : Finset ℕ} (hA : PairwiseCoprime A)
    (hBA : B ⊆ A) : PairwiseCoprime B := by
  intro a ha b hb hab
  exact hA (hBA ha) (hBA hb) hab

/-- Positive integers at most `N` surviving the sieve by `A`. -/
def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

@[simp] lemma mem_unsieved {N n : ℕ} {A : Finset ℕ} :
    n ∈ unsieved N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∀ a ∈ A, ¬a ∣ n := by
  simp [unsieved, and_assoc]

@[simp] lemma unsieved_empty (N : ℕ) : unsieved N ∅ = Finset.Icc 1 N := by
  ext n
  simp [unsieved]

/-- The normalized number of survivors.  It is set to zero at `N = 0`, as
forced by division in `ℝ`; every asymptotic theorem is eventually in the
positive range. -/
def sieveDensity (N : ℕ) (A : Finset ℕ) : ℝ :=
  (unsieved N A).card / (N : ℝ)

lemma sieveDensity_nonneg (N : ℕ) (A : Finset ℕ) :
    0 ≤ sieveDensity N A := by
  exact div_nonneg (by positivity) (by positivity)

@[simp] lemma sieveDensity_zero (A : Finset ℕ) : sieveDensity 0 A = 0 := by
  simp [sieveDensity, unsieved]

@[simp] lemma sieveDensity_empty {N : ℕ} (hN : 0 < N) :
    sieveDensity N ∅ = 1 := by
  simp [sieveDensity, Nat.card_Icc, hN.ne']

/-- The hypotheses in the finite optimization problem, without any hidden
asymptotic or infinitude assumptions. -/
def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 N ∧ PairwiseCoprime A ∧ reciprocalMass A ≤ C

lemma Admissible.subset_interval {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) : A ⊆ Finset.Icc 2 N := hA.1

lemma Admissible.pairwiseCoprime {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) : PairwiseCoprime A := hA.2.1

lemma Admissible.mass_le {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) : reciprocalMass A ≤ C := hA.2.2

lemma Admissible.two_le {C : ℝ} {N a : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) (ha : a ∈ A) : 2 ≤ a :=
  (Finset.mem_Icc.mp (hA.1 ha)).1

lemma Admissible.le_endpoint {C : ℝ} {N a : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) (ha : a ∈ A) : a ≤ N :=
  (Finset.mem_Icc.mp (hA.1 ha)).2

lemma admissible_empty {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    Admissible C N ∅ := by
  exact ⟨by simp, pairwiseCoprime_empty, by simpa using hC⟩

/-- The finite family over which Problem 783 optimizes. -/
def admissibleFamily (C : ℝ) (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 2 N).powerset.filter (Admissible C N)

lemma mem_admissibleFamily {C : ℝ} {N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleFamily C N ↔ Admissible C N A := by
  classical
  simp only [admissibleFamily, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.1, h⟩

lemma admissibleFamily_nonempty {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    (admissibleFamily C N).Nonempty := by
  exact ⟨∅, mem_admissibleFamily.mpr (admissible_empty hC N)⟩

/-- The literal finite minimum in Problem 783. -/
def minimumDensity (C : ℝ) (N : ℕ) : ℝ :=
  if hC : 0 ≤ C then
    ((admissibleFamily C N).image (sieveDensity N)).min'
      ((admissibleFamily_nonempty hC N).image (sieveDensity N))
  else 0

lemma minimumDensity_mem {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    minimumDensity C N ∈ (admissibleFamily C N).image (sieveDensity N) := by
  rw [minimumDensity, dif_pos hC]
  exact Finset.min'_mem _ _

lemma minimumDensity_le {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) : minimumDensity C N ≤ sieveDensity N A := by
  rw [minimumDensity, dif_pos hC]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨A, mem_admissibleFamily.mpr hA, rfl⟩)

lemma exists_admissible_minimizer {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    ∃ A : Finset ℕ, Admissible C N A ∧
      sieveDensity N A = minimumDensity C N := by
  obtain ⟨A, hA, hEq⟩ := Finset.mem_image.mp (minimumDensity_mem hC N)
  exact ⟨A, mem_admissibleFamily.mp hA, hEq⟩

lemma minimumDensity_nonneg {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    0 ≤ minimumDensity C N := by
  obtain ⟨A, _hA, hEq⟩ := exists_admissible_minimizer hC N
  rw [← hEq]
  exact sieveDensity_nonneg N A

lemma minimumDensity_le_one {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 0 < N) :
    minimumDensity C N ≤ 1 := by
  simpa [sieveDensity_empty hN] using
    minimumDensity_le hC (admissible_empty hC N)

/-! ## Exact elementary bounds -/

lemma reciprocalMass_nonneg_of_two_le {A : Finset ℕ}
    (_hA : ∀ a ∈ A, 2 ≤ a) : 0 ≤ reciprocalMass A := by
  exact Finset.sum_nonneg fun a ha => inv_nonneg.mpr (by positivity)

lemma reciprocalMass_nonneg (A : Finset ℕ) : 0 ≤ reciprocalMass A := by
  exact Finset.sum_nonneg fun _a _ha => inv_nonneg.mpr (by positivity)

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B)
    (_hA : ∀ a ∈ A, 1 ≤ a) : reciprocalMass A ≤ reciprocalMass B := by
  rw [reciprocalMass, reciprocalMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun a _ha _haA => by
    positivity

/-- The standard factorial bound for a nonnegative elementary symmetric
sum.  It is recorded here in a completely generic finite form because all
three truncation estimates below use it. -/
theorem sum_powersetCard_prod_le_sum_pow_div_factorial
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (t : ℕ) :
    (∑ x ∈ s.powersetCard t, ∏ a ∈ x, w a) ≤
      (∑ a ∈ s, w a) ^ t / t.factorial := by
  induction s using Finset.induction_on generalizing t with
  | empty =>
      cases t with
      | zero => simp [Finset.powersetCard_zero]
      | succ t =>
          rw [Finset.powersetCard_eq_empty.mpr (Nat.succ_pos t)]
          simp
  | @insert a s ha ih =>
      cases t with
      | zero => simp [ha, Finset.powersetCard_zero]
      | succ t =>
          have hdisj :
              Disjoint (s.powersetCard t.succ)
                ((s.powersetCard t).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx2 with ⟨y, hy, rfl⟩
            have hxsub : insert a y ⊆ s :=
              (Finset.mem_powersetCard.mp hx1).1
            exact ha (hxsub (by simp))
          have hy_not : ∀ y ∈ s.powersetCard t, a ∉ y := by
            intro y hy hay
            exact ha ((Finset.mem_powersetCard.mp hy).1 hay)
          rw [Finset.powersetCard_succ_insert ha t,
            Finset.sum_union hdisj, Finset.sum_image]
          swap
          · intro y hy z hz h
            apply Finset.ext
            intro b
            by_cases hb : b = a
            · subst hb
              simp [hy_not y hy, hy_not z hz]
            · have hmem := congrArg (fun u : Finset α => b ∈ u) h
              simpa [hb] using hmem
          have hins :
              (∑ y ∈ s.powersetCard t, ∏ b ∈ insert a y, w b) =
                w a * ∑ y ∈ s.powersetCard t, ∏ b ∈ y, w b := by
            calc
              (∑ y ∈ s.powersetCard t, ∏ b ∈ insert a y, w b) =
                  ∑ y ∈ s.powersetCard t, w a * ∏ b ∈ y, w b := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.prod_insert (hy_not y hy)]
              _ = w a * ∑ y ∈ s.powersetCard t, ∏ b ∈ y, w b := by
                    rw [← Finset.mul_sum]
          have hwa : 0 ≤ w a := hw a (by simp)
          have hws : ∀ b ∈ s, 0 ≤ w b := by
            intro b hb
            exact hw b (Finset.mem_insert_of_mem hb)
          have hsum : 0 ≤ ∑ b ∈ s, w b :=
            Finset.sum_nonneg hws
          rw [hins]
          have hmain :
              (∑ x ∈ s.powersetCard t.succ, ∏ b ∈ x, w b) +
                  w a * ∑ x ∈ s.powersetCard t, ∏ b ∈ x, w b ≤
                (∑ b ∈ s, w b) ^ t.succ / t.succ.factorial +
                  w a * ((∑ b ∈ s, w b) ^ t / t.factorial) := by
            exact add_le_add (ih hws t.succ)
              (mul_le_mul_of_nonneg_left (ih hws t) hwa)
          refine hmain.trans ?_
          have hbinom :
              (∑ b ∈ s, w b) ^ t.succ +
                  (t.succ : ℝ) * w a * (∑ b ∈ s, w b) ^ t ≤
                ((∑ b ∈ s, w b) + w a) ^ t.succ := by
            by_cases hsumZero : (∑ b ∈ s, w b) = 0
            · rw [hsumZero]
              cases t with
              | zero => simp
              | succ t => simp [hwa]
            · have hsumPos : 0 < ∑ b ∈ s, w b :=
                lt_of_le_of_ne hsum (by simpa [eq_comm] using hsumZero)
              have hratio : -2 ≤ w a / ∑ b ∈ s, w b := by
                have : 0 ≤ w a / ∑ b ∈ s, w b :=
                  div_nonneg hwa hsum
                linarith
              have hpow :
                  (∑ b ∈ s, w b) ^ t.succ *
                      (1 + (t.succ : ℝ) * (w a / ∑ b ∈ s, w b)) ≤
                    (∑ b ∈ s, w b) ^ t.succ *
                      (1 + w a / ∑ b ∈ s, w b) ^ t.succ := by
                exact mul_le_mul_of_nonneg_left
                  (one_add_mul_le_pow hratio t.succ)
                  (pow_nonneg hsum _)
              calc
                (∑ b ∈ s, w b) ^ t.succ +
                    (t.succ : ℝ) * w a * (∑ b ∈ s, w b) ^ t =
                    (∑ b ∈ s, w b) ^ t.succ *
                      (1 + (t.succ : ℝ) *
                        (w a / ∑ b ∈ s, w b)) := by
                          rw [pow_succ']
                          field_simp [hsumZero]
                _ ≤ (∑ b ∈ s, w b) ^ t.succ *
                      (1 + w a / ∑ b ∈ s, w b) ^ t.succ := hpow
                _ = ((∑ b ∈ s, w b) *
                      (1 + w a / ∑ b ∈ s, w b)) ^ t.succ := by
                        rw [mul_pow]
                _ = ((∑ b ∈ s, w b) + w a) ^ t.succ := by
                  congr 1
                  field_simp [hsumZero]
          have hfact :
              (∑ b ∈ s, w b) ^ t.succ / t.succ.factorial +
                  w a * ((∑ b ∈ s, w b) ^ t / t.factorial) =
                ((∑ b ∈ s, w b) ^ t.succ +
                    (t.succ : ℝ) * w a * (∑ b ∈ s, w b) ^ t) /
                  t.succ.factorial := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
              Nat.cast_one]
            field_simp [show (t.factorial : ℝ) ≠ 0 by positivity]
          rw [hfact]
          have hdiv :
              ((∑ b ∈ s, w b) ^ t.succ +
                    (t.succ : ℝ) * w a * (∑ b ∈ s, w b) ^ t) /
                  t.succ.factorial ≤
                ((∑ b ∈ s, w b) + w a) ^ t.succ /
                  t.succ.factorial :=
            div_le_div_of_nonneg_right hbinom (by positivity)
          refine hdiv.trans_eq ?_
          simp [Finset.sum_insert, ha, add_comm]

/-- The elementary symmetric reciprocal mass at exact depth `j`. -/
def elementaryReciprocalMass (A : Finset ℕ) (j : ℕ) : ℝ :=
  ∑ S ∈ A.powersetCard j, ∏ a ∈ S, (a : ℝ)⁻¹

lemma elementaryReciprocalMass_le (A : Finset ℕ) (j : ℕ) :
    elementaryReciprocalMass A j ≤
      reciprocalMass A ^ j / j.factorial := by
  simpa only [elementaryReciprocalMass, reciprocalMass] using
    sum_powersetCard_prod_le_sum_pow_div_factorial A
      (fun a : ℕ => (a : ℝ)⁻¹) (fun _a _ha => by positivity) j

/-! The next definitions expose the covering complement used by the union
bound and by Tao's Lipschitz lemma. -/

/-- Integers in `[1,N]` removed by at least one modulus in `A`. -/
def covered (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∃ a ∈ A, a ∣ n

@[simp] lemma mem_covered {N n : ℕ} {A : Finset ℕ} :
    n ∈ covered N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∃ a ∈ A, a ∣ n := by
  simp [covered, and_assoc]

lemma unsieved_disjoint_covered (N : ℕ) (A : Finset ℕ) :
    Disjoint (unsieved N A) (covered N A) := by
  rw [Finset.disjoint_left]
  intro n hnU hnC
  obtain ⟨_hn1, _hnN, a, haA, han⟩ := mem_covered.mp hnC
  exact (mem_unsieved.mp hnU).2.2 a haA han

lemma unsieved_union_covered (N : ℕ) (A : Finset ℕ) :
    unsieved N A ∪ covered N A = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_union, mem_unsieved, mem_covered, Finset.mem_Icc]
  constructor
  · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩
  · rintro ⟨hn1, hnN⟩
    by_cases h : ∃ a ∈ A, a ∣ n
    · exact Or.inr ⟨hn1, hnN, h⟩
    · left
      refine ⟨hn1, hnN, ?_⟩
      intro a haA han
      exact h ⟨a, haA, han⟩

lemma card_unsieved_add_card_covered (N : ℕ) (A : Finset ℕ) :
    (unsieved N A).card + (covered N A).card = (Finset.Icc 1 N).card := by
  rw [← Finset.card_union_of_disjoint (unsieved_disjoint_covered N A),
    unsieved_union_covered]

/-- Multiples of `a` in the positive prefix. -/
def multiplesIn (N a : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => a ∣ n

@[simp] lemma mem_multiplesIn {N a n : ℕ} :
    n ∈ multiplesIn N a ↔ 1 ≤ n ∧ n ≤ N ∧ a ∣ n := by
  simp only [multiplesIn, Finset.mem_filter, Finset.mem_Ioc]
  omega

lemma covered_subset_biUnion_multiples (N : ℕ) (A : Finset ℕ) :
    covered N A ⊆ A.biUnion (multiplesIn N) := by
  intro n hn
  obtain ⟨_hn1, _hnN, a, haA, han⟩ := mem_covered.mp hn
  simp only [Finset.mem_biUnion]
  exact ⟨a, haA, mem_multiplesIn.mpr ⟨_hn1, _hnN, han⟩⟩

lemma card_covered_le_sum_card_multiples (N : ℕ) (A : Finset ℕ) :
    (covered N A).card ≤ ∑ a ∈ A, (multiplesIn N a).card := by
  exact (Finset.card_le_card (covered_subset_biUnion_multiples N A)).trans
    Finset.card_biUnion_le

lemma multiplesIn_card_eq_div (N a : ℕ) :
    (multiplesIn N a).card = N / a := by
  simpa only [multiplesIn] using Nat.Ioc_filter_dvd_card_eq_div N a

lemma card_covered_le_sum_div (N : ℕ) (A : Finset ℕ) :
    (covered N A).card ≤ ∑ a ∈ A, N / a := by
  exact (card_covered_le_sum_card_multiples N A).trans
    (Finset.sum_le_sum fun a _ha => (multiplesIn_card_eq_div N a).le)

lemma card_covered_cast_le_mass (N : ℕ) (A : Finset ℕ) :
    ((covered N A).card : ℝ) ≤ (N : ℝ) * reciprocalMass A := by
  have hcard := card_covered_le_sum_div N A
  calc
    ((covered N A).card : ℝ) ≤ (∑ a ∈ A, N / a : ℕ) := by
      exact_mod_cast hcard
    _ ≤ ∑ a ∈ A, (N : ℝ) / (a : ℝ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro a _ha
      exact (Nat.cast_div_le : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ))
    _ = (N : ℝ) * reciprocalMass A := by
      simp only [reciprocalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [div_eq_mul_inv]

lemma unsieved_subset_union_changed (N : ℕ) (A B : Finset ℕ) :
    unsieved N A ⊆ unsieved N B ∪ covered N (B \ A) := by
  intro n hnA
  rw [Finset.mem_union]
  by_cases hnB : n ∈ unsieved N B
  · exact Or.inl hnB
  · right
    have hnA' := mem_unsieved.mp hnA
    have hex : ∃ b ∈ B, b ∣ n := by
      by_contra h
      apply hnB
      exact mem_unsieved.mpr ⟨hnA'.1, hnA'.2.1, by
        intro b hbB hbn
        exact h ⟨b, hbB, hbn⟩⟩
    obtain ⟨b, hbB, hbn⟩ := hex
    have hbA : b ∉ A := by
      intro hbA
      exact hnA'.2.2 b hbA hbn
    exact mem_covered.mpr
      ⟨hnA'.1, hnA'.2.1, b, Finset.mem_sdiff.mpr ⟨hbB, hbA⟩, hbn⟩

lemma card_unsieved_le_add_changed (N : ℕ) (A B : Finset ℕ) :
    (unsieved N A).card ≤
      (unsieved N B).card + (covered N (B \ A)).card := by
  exact (Finset.card_le_card (unsieved_subset_union_changed N A B)).trans
    (Finset.card_union_le (unsieved N B) (covered N (B \ A)))

/-- Tao's elementary Lipschitz estimate: adjoining/removing moduli can change
the survivor density by at most their reciprocal mass. -/
theorem sieveDensity_sub_mass_sdiff_le {N : ℕ} (hN : 0 < N)
    (A B : Finset ℕ) :
    sieveDensity N A - reciprocalMass (B \ A) ≤ sieveDensity N B := by
  have hcard := card_unsieved_le_add_changed N A B
  have hcovered := card_covered_cast_le_mass N (B \ A)
  have hcast :
      ((unsieved N A).card : ℝ) ≤
        ((unsieved N B).card : ℝ) +
          (N : ℝ) * reciprocalMass (B \ A) := by
    calc
      ((unsieved N A).card : ℝ) ≤
          ((unsieved N B).card : ℝ) + ((covered N (B \ A)).card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ ((unsieved N B).card : ℝ) +
          (N : ℝ) * reciprocalMass (B \ A) :=
        add_le_add_right hcovered ((unsieved N B).card : ℝ)
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [sieveDensity, sieveDensity, sub_le_iff_le_add]
  calc
    ((unsieved N A).card : ℝ) / (N : ℝ) ≤
        (((unsieved N B).card : ℝ) +
          (N : ℝ) * reciprocalMass (B \ A)) / (N : ℝ) :=
      div_le_div_of_nonneg_right hcast hNReal.le
    _ = ((unsieved N B).card : ℝ) / (N : ℝ) +
        reciprocalMass (B \ A) := by
      rw [add_div, mul_div_cancel_left₀ _ hNReal.ne']

/-- The symmetric difference of two finite modulus sets. -/
def symmetricDifference (A B : Finset ℕ) : Finset ℕ :=
  (A \ B) ∪ (B \ A)

@[simp] lemma mem_symmetricDifference {A B : Finset ℕ} {a : ℕ} :
    a ∈ symmetricDifference A B ↔
      (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A) := by
  simp [symmetricDifference]

lemma reciprocalMass_symmetricDifference (A B : Finset ℕ) :
    reciprocalMass (symmetricDifference A B) =
      reciprocalMass (A \ B) + reciprocalMass (B \ A) := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a haA haB
    exact (Finset.mem_sdiff.mp haA).2 (Finset.mem_sdiff.mp haB).1
  unfold symmetricDifference reciprocalMass
  exact Finset.sum_union hdisj

/-- Symmetric form of the reciprocal-mass Lipschitz estimate. -/
theorem abs_sieveDensity_sub_le_mass_symmetricDifference {N : ℕ}
    (hN : 0 < N) (A B : Finset ℕ) :
    |sieveDensity N A - sieveDensity N B| ≤
      reciprocalMass (symmetricDifference A B) := by
  rw [reciprocalMass_symmetricDifference]
  have hAB := sieveDensity_sub_mass_sdiff_le hN A B
  have hBA := sieveDensity_sub_mass_sdiff_le hN B A
  have hnonnegAB := reciprocalMass_nonneg (A \ B)
  have hnonnegBA := reciprocalMass_nonneg (B \ A)
  rw [abs_le]
  constructor <;> linarith

/-! ## Pairwise-coprime composite moduli are sparse -/

/-- The composite members of a finite set of moduli. -/
def compositePart (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a => ¬a.Prime

@[simp] lemma mem_compositePart {A : Finset ℕ} {a : ℕ} :
    a ∈ compositePart A ↔ a ∈ A ∧ ¬a.Prime := by
  simp [compositePart]

lemma minFac_injOn_compositePart {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) :
    Set.InjOn Nat.minFac (compositePart A) := by
  intro a ha b hb hab
  by_contra habne
  have hcop : Nat.Coprime a b :=
    hA.pairwiseCoprime
      (mem_compositePart.mp ha).1
      (mem_compositePart.mp hb).1 habne
  have hp : a.minFac.Prime := Nat.minFac_prime (by
    have := hA.two_le (mem_compositePart.mp ha).1
    omega)
  have hnotcop : ¬Nat.Coprime a b :=
    Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨a.minFac, hp, Nat.minFac_dvd _, by
        rw [hab]
        exact Nat.minFac_dvd _⟩
  exact hnotcop hcop

/-- Distinct pairwise-coprime composites have distinct least prime factors;
all of these factors are at most `√N`. -/
lemma compositePart_card_le_sqrt {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : Admissible C N A) :
    (compositePart A).card ≤ N.sqrt := by
  let f : {a // a ∈ compositePart A} → Finset.Icc 1 N.sqrt := fun a =>
    ⟨a.1.minFac, Finset.mem_Icc.mpr ⟨
      (Nat.minFac_prime (by
        have ha2 := hA.two_le (mem_compositePart.mp a.2).1
        omega)).one_le,
      (Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self
        (by have := hA.two_le (mem_compositePart.mp a.2).1; omega)
        (mem_compositePart.mp a.2).2)).trans
          (Nat.sqrt_le_sqrt (hA.le_endpoint (mem_compositePart.mp a.2).1))⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra habne
    have hcop : Nat.Coprime a.1 b.1 :=
      hA.pairwiseCoprime
        (mem_compositePart.mp a.2).1
        (mem_compositePart.mp b.2).1 habne
    have hfac : a.1.minFac = b.1.minFac := congrArg Subtype.val hab
    have hp : a.1.minFac.Prime := Nat.minFac_prime (by
      have := hA.two_le (mem_compositePart.mp a.2).1
      omega)
    have hnotcop : ¬Nat.Coprime a.1 b.1 :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨a.1.minFac, hp, Nat.minFac_dvd _, by
          rw [hfac]
          exact Nat.minFac_dvd _⟩
    exact hnotcop hcop
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Nat.card_Icc] using hcard

/-- Composite moduli above a cutoff `z`. -/
def largeCompositePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (compositePart A).filter fun a => z ≤ a

@[simp] lemma mem_largeCompositePart {A : Finset ℕ} {z a : ℕ} :
    a ∈ largeCompositePart A z ↔ a ∈ A ∧ ¬a.Prime ∧ z ≤ a := by
  simp [largeCompositePart, and_assoc]

lemma largeCompositePart_card_le_sqrt {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) :
    (largeCompositePart A z).card ≤ N.sqrt := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (compositePart_card_le_sqrt hA)

/-- The reciprocal mass of the composite tail is at most `√N / z`.
This is the quantitative reason that composites can be discarded after a
slowly growing cutoff. -/
lemma reciprocalMass_largeCompositePart_le {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) (hz : 0 < z) :
    reciprocalMass (largeCompositePart A z) ≤ (N.sqrt : ℝ) / z := by
  have hcard : ((largeCompositePart A z).card : ℝ) ≤ N.sqrt := by
    exact_mod_cast largeCompositePart_card_le_sqrt hA (z := z)
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  rw [reciprocalMass]
  calc
    (∑ a ∈ largeCompositePart A z, (a : ℝ)⁻¹) ≤
        ∑ _a ∈ largeCompositePart A z, ((z : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a ha
      have hza : (z : ℝ) ≤ a := by
        exact_mod_cast (mem_largeCompositePart.mp ha).2.2
      exact (inv_le_inv₀ (hzR.trans_le hza) hzR).2 hza
    _ = ((largeCompositePart A z).card : ℝ) * (z : ℝ)⁻¹ := by
      simp
    _ ≤ (N.sqrt : ℝ) * (z : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hzR.le)
    _ = (N.sqrt : ℝ) / z := by rw [div_eq_mul_inv]

/-- Composite tail elements whose least prime factor is at most `√z`. -/
def smallMinFacCompositePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (largeCompositePart A z).filter fun a => a.minFac ≤ z.sqrt

/-- Composite tail elements whose least prime factor exceeds `√z`. -/
def largeMinFacCompositePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  (largeCompositePart A z).filter fun a => z.sqrt < a.minFac

lemma smallMinFacCompositePart_card_le_sqrt {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) :
    (smallMinFacCompositePart A z).card ≤ z.sqrt := by
  have hinj : Set.InjOn Nat.minFac (smallMinFacCompositePart A z) := by
    apply (minFac_injOn_compositePart hA).mono
    intro a ha
    have hlarge := mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1
    exact mem_compositePart.mpr ⟨hlarge.1, hlarge.2.1⟩
  rw [← Finset.card_image_of_injOn hinj]
  have hsubset :
      (smallMinFacCompositePart A z).image Nat.minFac ⊆
        Finset.Icc 1 z.sqrt := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have ha2 := hA.two_le
      (mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1).1
    exact Finset.mem_Icc.mpr ⟨
      (Nat.minFac_prime (by omega)).one_le,
      (Finset.mem_filter.mp ha).2⟩
  simpa [Nat.card_Icc] using Finset.card_le_card hsubset

lemma reciprocalMass_smallMinFacCompositePart_le {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) (hz : 0 < z) :
    reciprocalMass (smallMinFacCompositePart A z) ≤
      (z.sqrt : ℝ) / z := by
  have hcard : ((smallMinFacCompositePart A z).card : ℝ) ≤ z.sqrt := by
    exact_mod_cast smallMinFacCompositePart_card_le_sqrt hA
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  rw [reciprocalMass]
  calc
    (∑ a ∈ smallMinFacCompositePart A z, (a : ℝ)⁻¹) ≤
        ∑ _a ∈ smallMinFacCompositePart A z, ((z : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro a ha
      have hza : (z : ℝ) ≤ a := by
        exact_mod_cast
          (mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1).2.2
      exact (inv_le_inv₀ (hzR.trans_le hza) hzR).2 hza
    _ = ((smallMinFacCompositePart A z).card : ℝ) * (z : ℝ)⁻¹ := by
      simp
    _ ≤ (z.sqrt : ℝ) * (z : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hzR.le)
    _ = (z.sqrt : ℝ) / z := by rw [div_eq_mul_inv]

lemma reciprocalMass_largeMinFacCompositePart_le {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) (hz : 0 < z) :
    reciprocalMass (largeMinFacCompositePart A z) ≤
      ((z.sqrt : ℝ))⁻¹ := by
  let R := largeMinFacCompositePart A z
  have hinj : Set.InjOn Nat.minFac R := by
    apply (minFac_injOn_compositePart hA).mono
    intro a ha
    have hlarge := mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1
    exact mem_compositePart.mpr ⟨hlarge.1, hlarge.2.1⟩
  have hterm : ∀ a ∈ R,
      (a : ℝ)⁻¹ ≤ (((a.minFac : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro a ha
    have hlarge := mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1
    have ha2 := hA.two_le hlarge.1
    have hp2Nat : a.minFac ^ 2 ≤ a :=
      Nat.minFac_sq_le_self (by omega) hlarge.2.1
    have hp : 0 < (a.minFac : ℝ) := by
      exact_mod_cast (Nat.minFac_prime (by omega)).pos
    have hp2 : 0 < ((a.minFac : ℝ) ^ 2) := sq_pos_of_pos hp
    have haR : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
    exact (inv_le_inv₀ haR hp2).2 (by exact_mod_cast hp2Nat)
  have hsumImage :
      (∑ a ∈ R, (((a.minFac : ℕ) : ℝ) ^ 2)⁻¹) =
        ∑ p ∈ R.image Nat.minFac, ((p : ℝ) ^ 2)⁻¹ := by
    symm
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  have himageSubset :
      R.image Nat.minFac ⊆ Finset.Ioc z.sqrt (max z.sqrt N) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have hlarge := mem_largeCompositePart.mp (Finset.mem_filter.mp ha).1
    have ha2 := hA.two_le hlarge.1
    have hp_le_a : a.minFac ≤ a :=
      Nat.le_of_dvd (by omega) (Nat.minFac_dvd a)
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp ha).2,
      hp_le_a.trans (hA.le_endpoint hlarge.1) |>.trans
        (le_max_right z.sqrt N)⟩
  have hsqrt0 : z.sqrt ≠ 0 := (Nat.sqrt_pos.mpr hz).ne'
  rw [reciprocalMass]
  calc
    (∑ a ∈ R, (a : ℝ)⁻¹) ≤
        ∑ a ∈ R, (((a.minFac : ℕ) : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum fun a ha => hterm a ha
    _ = ∑ p ∈ R.image Nat.minFac, ((p : ℝ) ^ 2)⁻¹ := hsumImage
    _ ≤ ∑ p ∈ Finset.Ioc z.sqrt (max z.sqrt N),
        ((p : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himageSubset
        (fun _p _hp _hnot => by positivity)
    _ ≤ (z.sqrt : ℝ)⁻¹ - ((max z.sqrt N : ℕ) : ℝ)⁻¹ := by
      exact sum_Ioc_inv_sq_le_sub hsqrt0 (le_max_left z.sqrt N)
    _ ≤ (z.sqrt : ℝ)⁻¹ := by
      have hnonneg : 0 ≤ ((max z.sqrt N : ℕ) : ℝ)⁻¹ := by positivity
      linarith

lemma largeCompositePart_eq_minFac_union (A : Finset ℕ) (z : ℕ) :
    largeCompositePart A z =
      smallMinFacCompositePart A z ∪ largeMinFacCompositePart A z := by
  ext a
  simp only [smallMinFacCompositePart, largeMinFacCompositePart,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ha
    by_cases h : a.minFac ≤ z.sqrt
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, lt_of_not_ge h⟩
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha

lemma disjoint_small_largeMinFacCompositePart (A : Finset ℕ) (z : ℕ) :
    Disjoint (smallMinFacCompositePart A z)
      (largeMinFacCompositePart A z) := by
  rw [Finset.disjoint_left]
  intro a hsmall hlarge
  have hle := (Finset.mem_filter.mp hsmall).2
  have hlt := (Finset.mem_filter.mp hlarge).2
  omega

lemma reciprocalMass_largeCompositePart_eq_minFac_sum
    (A : Finset ℕ) (z : ℕ) :
    reciprocalMass (largeCompositePart A z) =
      reciprocalMass (smallMinFacCompositePart A z) +
        reciprocalMass (largeMinFacCompositePart A z) := by
  rw [largeCompositePart_eq_minFac_union]
  unfold reciprocalMass
  exact Finset.sum_union (disjoint_small_largeMinFacCompositePart A z)

/-- The uniform composite-tail estimate used in Tao's reduction.  Unlike the
earlier `√N / z` estimate, this bound is independent of the endpoint `N`. -/
theorem reciprocalMass_largeCompositePart_uniform {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) (hz : 0 < z) :
    reciprocalMass (largeCompositePart A z) ≤
      2 / (z.sqrt : ℝ) := by
  have hsmall := reciprocalMass_smallMinFacCompositePart_le hA hz
  have hlarge := reciprocalMass_largeMinFacCompositePart_le hA hz
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hsqrtR : (0 : ℝ) < z.sqrt := by
    exact_mod_cast (Nat.sqrt_pos.mpr hz)
  have hsqrtDiv : (z.sqrt : ℝ) / z ≤ ((z.sqrt : ℝ))⁻¹ := by
    rw [inv_eq_one_div, div_le_iff₀ hzR]
    rw [mul_comm, one_div, ← div_eq_mul_inv]
    rw [le_div_iff₀ hsqrtR]
    exact_mod_cast Nat.sqrt_le z
  rw [reciprocalMass_largeCompositePart_eq_minFac_sum]
  calc
    reciprocalMass (smallMinFacCompositePart A z) +
        reciprocalMass (largeMinFacCompositePart A z) ≤
      (z.sqrt : ℝ) / z + ((z.sqrt : ℝ))⁻¹ :=
        add_le_add hsmall hlarge
    _ ≤ ((z.sqrt : ℝ))⁻¹ + ((z.sqrt : ℝ))⁻¹ :=
      add_le_add hsqrtDiv le_rfl
    _ = 2 / (z.sqrt : ℝ) := by
      rw [div_eq_mul_inv]
      ring

theorem tendsto_uniformCompositeTailBound :
    Tendsto (fun z : ℕ => 2 / (z.sqrt : ℝ)) atTop (nhds 0) := by
  have hsqrtNat : Tendsto Nat.sqrt atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b * b, ?_⟩
    intro z hz
    exact Nat.le_sqrt.mpr hz
  have hsqrtReal : Tendsto (fun z : ℕ => (z.sqrt : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsqrtNat
  have hinv : Tendsto (fun z : ℕ => ((z.sqrt : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrtReal
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun z : ℕ => (2 : ℝ) * ((z.sqrt : ℝ))⁻¹)
        atTop (nhds ((2 : ℝ) * 0)))

/-- Retain every prime modulus and only the composite moduli below `z`. -/
def primeOrSmallCompositePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  A.filter fun a => a.Prime ∨ a < z

lemma sdiff_primeOrSmallCompositePart (A : Finset ℕ) (z : ℕ) :
    A \ primeOrSmallCompositePart A z = largeCompositePart A z := by
  ext a
  simp only [Finset.mem_sdiff, primeOrSmallCompositePart,
    Finset.mem_filter, mem_largeCompositePart]
  constructor
  · rintro ⟨ha, hnot⟩
    exact ⟨ha, fun hp => hnot ⟨ha, Or.inl hp⟩,
      le_of_not_gt fun hlt => hnot ⟨ha, Or.inr hlt⟩⟩
  · rintro ⟨ha, hprime, hza⟩
    exact ⟨ha, fun h => h.2.elim hprime (not_lt_of_ge hza)⟩

lemma admissible_primeOrSmallCompositePart {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) :
    Admissible C N (primeOrSmallCompositePart A z) := by
  have hsub : primeOrSmallCompositePart A z ⊆ A := Finset.filter_subset _ _
  refine ⟨fun a ha => hA.subset_interval (hsub ha),
    hA.pairwiseCoprime.mono hsub, ?_⟩
  exact (reciprocalMass_mono hsub
    (fun a ha => by have := hA.two_le (hsub ha); omega)).trans hA.mass_le

/-- Quantitative finite reduction from arbitrary pairwise-coprime moduli to
primes plus finitely many small composites. -/
theorem sieveDensity_primeOrSmallCompositePart_sub_le {C : ℝ} {N z : ℕ}
    {A : Finset ℕ} (hA : Admissible C N A) (hN : 0 < N) (hz : 0 < z) :
    sieveDensity N (primeOrSmallCompositePart A z) -
        2 / (z.sqrt : ℝ) ≤ sieveDensity N A := by
  have hlip := sieveDensity_sub_mass_sdiff_le hN
    (primeOrSmallCompositePart A z) A
  rw [sdiff_primeOrSmallCompositePart] at hlip
  have htail := reciprocalMass_largeCompositePart_uniform hA hz
  linarith

/-- The elementary union bound in normalized form. -/
theorem sieveDensity_ge_one_sub_mass {N : ℕ} (hN : 0 < N)
    (A : Finset ℕ) :
    1 - reciprocalMass A ≤ sieveDensity N A := by
  have hpartition := card_unsieved_add_card_covered N A
  have hIcc : (Finset.Icc 1 N).card = N := by
    simp [Nat.card_Icc]
  have hcast := card_covered_cast_le_mass N A
  have hsumReal :
      ((unsieved N A).card : ℝ) + ((covered N A).card : ℝ) = N := by
    exact_mod_cast (hpartition.trans hIcc)
  have hNReal : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [sieveDensity]
  apply (le_div_iff₀ hNReal).2
  nlinarith [hNReal]

/-! ## Exact Bonferroni inequalities

The analytic argument later truncates inclusion--exclusion at a fixed
depth.  The following lemmas isolate the completely finite, pointwise
combinatorics.  In particular, there is no probability or limiting argument
hidden in this layer. -/

/-- The alternating binomial sum through degree `r`. -/
def alternatingChooseSum (k r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1), (-1 : ℤ) ^ j * (k.choose j : ℤ)

@[simp] lemma alternatingChooseSum_zero (r : ℕ) :
    alternatingChooseSum 0 r = 1 := by
  induction r with
  | zero => simp [alternatingChooseSum]
  | succ r ih =>
      rw [alternatingChooseSum]
      rw [show r.succ + 1 = (r + 1) + 1 by omega,
        Finset.sum_range_succ]
      change alternatingChooseSum 0 r +
        (-1 : ℤ) ^ (r + 1) * ((0 : ℕ).choose (r + 1) : ℤ) = 1
      rw [ih, Nat.choose_eq_zero_of_lt (by omega)]
      simp

@[simp] lemma alternatingChooseSum_succ (k r : ℕ) :
    alternatingChooseSum (k + 1) r =
      (-1 : ℤ) ^ r * (k.choose r : ℤ) := by
  simpa [alternatingChooseSum] using
    (Int.alternating_sum_range_choose_eq_choose (n := k) (m := r))

lemma alternatingChooseSum_even_nonneg (k r : ℕ) :
    0 ≤ alternatingChooseSum k (2 * r) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [alternatingChooseSum_succ,
        (show Even (2 * r) by simp).neg_one_pow]
      positivity

lemma alternatingChooseSum_odd_nonpos (k r : ℕ) :
    alternatingChooseSum (k + 1) (2 * r + 1) ≤ 0 := by
  rw [alternatingChooseSum_succ,
    (show Odd (2 * r + 1) by simp).neg_one_pow]
  simp

/-- The set of moduli from `A` which divide the integer `n`. -/
def divisorsFrom (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a => a ∣ n

@[simp] lemma mem_divisorsFrom {n a : ℕ} {A : Finset ℕ} :
    a ∈ divisorsFrom n A ↔ a ∈ A ∧ a ∣ n := by
  simp [divisorsFrom]

/-- The exact `0`--`1` indicator that `n` survives the sieve by `A`. -/
def survivorIndicator (n : ℕ) (A : Finset ℕ) : ℤ :=
  if ∀ a ∈ A, ¬a ∣ n then 1 else 0

lemma divisorsFrom_eq_empty_iff (n : ℕ) (A : Finset ℕ) :
    divisorsFrom n A = ∅ ↔ ∀ a ∈ A, ¬a ∣ n := by
  simp [divisorsFrom]

lemma survivorIndicator_eq_one_iff (n : ℕ) (A : Finset ℕ) :
    survivorIndicator n A = 1 ↔ divisorsFrom n A = ∅ := by
  rw [divisorsFrom_eq_empty_iff]
  simp [survivorIndicator]

/-- The pointwise inclusion--exclusion polynomial, truncated at degree `r`.
The number of contributing `j`-subsets is written literally as a cardinality
so that later counting arguments can reindex it by subsets of `A`. -/
def bonferroniAt (n : ℕ) (A : Finset ℕ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1 : ℤ) ^ j * ((divisorsFrom n A).powersetCard j).card

lemma bonferroniAt_eq_alternatingChooseSum (n : ℕ)
    (A : Finset ℕ) (r : ℕ) :
    bonferroniAt n A r =
      alternatingChooseSum (divisorsFrom n A).card r := by
  simp only [bonferroniAt, alternatingChooseSum,
    Finset.card_powersetCard]

/-- Even Bonferroni truncations majorize the survivor indicator. -/
theorem survivorIndicator_le_bonferroniAt_even (n : ℕ)
    (A : Finset ℕ) (r : ℕ) :
    survivorIndicator n A ≤ bonferroniAt n A (2 * r) := by
  rw [bonferroniAt_eq_alternatingChooseSum]
  by_cases hzero : (divisorsFrom n A).card = 0
  · have hempty : divisorsFrom n A = ∅ := Finset.card_eq_zero.mp hzero
    have hindicator : survivorIndicator n A = 1 :=
      (survivorIndicator_eq_one_iff n A).2 hempty
    rw [hindicator, hzero]
    simp
  · have hsurv : survivorIndicator n A = 0 := by
      have hnot : ¬∀ a ∈ A, ¬a ∣ n := by
        intro h
        exact hzero (Finset.card_eq_zero.mpr
          ((divisorsFrom_eq_empty_iff n A).2 h))
      simp [survivorIndicator, hnot]
    rw [hsurv]
    exact alternatingChooseSum_even_nonneg _ _

/-- Odd Bonferroni truncations minorize the survivor indicator. -/
theorem bonferroniAt_odd_le_survivorIndicator (n : ℕ)
    (A : Finset ℕ) (r : ℕ) :
    bonferroniAt n A (2 * r + 1) ≤ survivorIndicator n A := by
  rw [bonferroniAt_eq_alternatingChooseSum]
  cases hcard : (divisorsFrom n A).card with
  | zero =>
      have hempty : divisorsFrom n A = ∅ := Finset.card_eq_zero.mp hcard
      have hindicator : survivorIndicator n A = 1 :=
        (survivorIndicator_eq_one_iff n A).2 hempty
      rw [hindicator]
      simp
  | succ k =>
      have hsurv : survivorIndicator n A = 0 := by
        have hnot : ¬∀ a ∈ A, ¬a ∣ n := by
          intro h
          have hempty := (divisorsFrom_eq_empty_iff n A).2 h
          rw [hempty] at hcard
          simp at hcard
        simp [survivorIndicator, hnot]
      rw [hsurv]
      exact alternatingChooseSum_odd_nonpos k r

/-- The `j`-subsets of the moduli dividing `n` are exactly the `j`-subsets
of `A` on which every divisibility predicate holds. -/
lemma powersetCard_divisorsFrom (n : ℕ) (A : Finset ℕ) (j : ℕ) :
    (divisorsFrom n A).powersetCard j =
      (A.powersetCard j).filter (fun S => ∀ a ∈ S, a ∣ n) := by
  ext S
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hS, hcard⟩
    exact ⟨⟨fun a ha => (mem_divisorsFrom.mp (hS ha)).1, hcard⟩,
      fun a ha => (mem_divisorsFrom.mp (hS ha)).2⟩
  · rintro ⟨⟨hSA, hcard⟩, hdiv⟩
    exact ⟨fun a ha => mem_divisorsFrom.mpr ⟨hSA ha, hdiv a ha⟩,
      hcard⟩

/-- The subset-indexed version of the pointwise truncated
inclusion--exclusion polynomial. -/
def truncatedInclusionAt (n : ℕ) (A : Finset ℕ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1),
    ∑ S ∈ A.powersetCard j,
      if ∀ a ∈ S, a ∣ n then (-1 : ℤ) ^ j else 0

lemma truncatedInclusionAt_eq_bonferroniAt (n : ℕ)
    (A : Finset ℕ) (r : ℕ) :
    truncatedInclusionAt n A r = bonferroniAt n A r := by
  unfold truncatedInclusionAt bonferroniAt
  apply Finset.sum_congr rfl
  intro j _hj
  rw [powersetCard_divisorsFrom, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm]

/-- The untruncated inclusion--exclusion sum over all subsets of `A`. -/
def fullInclusionAt (n : ℕ) (A : Finset ℕ) : ℤ :=
  ∑ S ∈ A.powerset,
    if ∀ a ∈ S, a ∣ n then (-1 : ℤ) ^ S.card else 0

/-- Exact pointwise inclusion--exclusion: after restricting to subsets all
of whose elements divide `n`, the indexing set is precisely the powerset of
`divisorsFrom n A`. -/
theorem fullInclusionAt_eq_survivorIndicator (n : ℕ) (A : Finset ℕ) :
    fullInclusionAt n A = survivorIndicator n A := by
  have hfilter :
      A.powerset.filter (fun S => ∀ a ∈ S, a ∣ n) =
        (divisorsFrom n A).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSA, hdiv⟩ a ha
      exact mem_divisorsFrom.mpr ⟨hSA ha, hdiv a ha⟩
    · intro hS
      exact ⟨fun a ha => (mem_divisorsFrom.mp (hS ha)).1,
        fun a ha => (mem_divisorsFrom.mp (hS ha)).2⟩
  rw [fullInclusionAt, ← Finset.sum_filter, hfilter,
    Finset.sum_powerset_neg_one_pow_card]
  by_cases hempty : divisorsFrom n A = ∅
  · rw [if_pos hempty]
    exact (survivorIndicator_eq_one_iff n A).2 hempty |>.symm
  · rw [if_neg hempty]
    have hnot : ¬∀ a ∈ A, ¬a ∣ n := by
      exact fun h => hempty ((divisorsFrom_eq_empty_iff n A).2 h)
    simp [survivorIndicator, hnot]

/-! ## Exact periodicity for a fixed family -/

/-- A common period for all divisibility conditions generated by `A`. -/
def modulusProduct (A : Finset ℕ) : ℕ :=
  ∏ a ∈ A, a

lemma dvd_modulusProduct {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∣ modulusProduct A := by
  exact Finset.dvd_prod_of_mem id ha

/-- Congruence modulo the product preserves every individual divisibility
condition.  Pairwise coprimality is not needed for this direction. -/
lemma divides_iff_of_modEq_modulusProduct {A : Finset ℕ} {m n a : ℕ}
    (hmod : n ≡ m [MOD modulusProduct A]) (ha : a ∈ A) :
    a ∣ n ↔ a ∣ m := by
  have hamod : n ≡ m [MOD a] := hmod.of_dvd (dvd_modulusProduct ha)
  constructor
  · intro han
    exact Nat.modEq_zero_iff_dvd.mp
      (hamod.symm.trans (Nat.modEq_zero_iff_dvd.mpr han))
  · intro ham
    exact Nat.modEq_zero_iff_dvd.mp
      (hamod.trans (Nat.modEq_zero_iff_dvd.mpr ham))

lemma survivorPredicate_iff_of_modEq_modulusProduct
    {A : Finset ℕ} {m n : ℕ}
    (hmod : n ≡ m [MOD modulusProduct A]) :
    (∀ a ∈ A, ¬a ∣ n) ↔ ∀ a ∈ A, ¬a ∣ m := by
  constructor
  · intro hn a ha ham
    exact hn a ha ((divides_iff_of_modEq_modulusProduct hmod ha).2 ham)
  · intro hm a ha han
    exact hm a ha ((divides_iff_of_modEq_modulusProduct hmod ha).1 han)

theorem survivorIndicator_periodic (n : ℕ) (A : Finset ℕ) :
    survivorIndicator (n + modulusProduct A) A = survivorIndicator n A := by
  have hiff : (∀ a ∈ A, ¬a ∣ n + modulusProduct A) ↔
      ∀ a ∈ A, ¬a ∣ n :=
    survivorPredicate_iff_of_modEq_modulusProduct
      (show n + modulusProduct A ≡ n [MOD modulusProduct A] by
        simp [Nat.ModEq])
  by_cases hleft : ∀ a ∈ A, ¬a ∣ n + modulusProduct A
  · have hright := hiff.mp hleft
    unfold survivorIndicator
    rw [if_pos hleft, if_pos hright]
  · have hright : ¬∀ a ∈ A, ¬a ∣ n := by
      exact fun h => hleft (hiff.mpr h)
    unfold survivorIndicator
    rw [if_neg hleft, if_neg hright]

/-- The product of the moduli in a subset. -/
def subsetProduct (S : Finset ℕ) : ℕ :=
  ∏ a ∈ S, a

lemma cast_subsetProduct (S : Finset ℕ) :
    (subsetProduct S : ℝ) = ∏ a ∈ S, (a : ℝ) := by
  simp [subsetProduct]

lemma inv_cast_subsetProduct (S : Finset ℕ) :
    (subsetProduct S : ℝ)⁻¹ = ∏ a ∈ S, (a : ℝ)⁻¹ := by
  rw [cast_subsetProduct, Finset.prod_inv_distrib]

lemma subsetProduct_pos {A S : Finset ℕ}
    (hSA : S ⊆ A) (hpos : ∀ a ∈ A, 0 < a) :
    0 < subsetProduct S := by
  exact Finset.prod_pos fun a ha => hpos a (hSA ha)

/-- The absolute reciprocal mass of all `j`-fold products which still fit
below the endpoint. -/
def cutoffElementaryReciprocalMass
    (N : ℕ) (A : Finset ℕ) (j : ℕ) : ℝ :=
  ∑ S ∈ (A.powersetCard j).filter (fun S => subsetProduct S ≤ N),
    (subsetProduct S : ℝ)⁻¹

/-- The same exact depth with `⌊N/d⌋/N` in place of `1/d`. -/
def floorElementaryMass (N : ℕ) (A : Finset ℕ) (j : ℕ) : ℝ :=
  ∑ S ∈ A.powersetCard j,
    ((N / subsetProduct S : ℕ) : ℝ) / (N : ℝ)

/-- A single normalized floor differs from its reciprocal model by at most
`1/N`. -/
lemma natDiv_normalized_error {N d : ℕ}
    (hd : 0 < d) (hdN : d ≤ N) :
    0 ≤ (d : ℝ)⁻¹ - ((N / d : ℕ) : ℝ) / (N : ℝ) ∧
      (d : ℝ)⁻¹ - ((N / d : ℕ) : ℝ) / (N : ℝ) ≤
        (N : ℝ)⁻¹ := by
  have hN : 0 < N := hd.trans_le hdN
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hqLe : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d :=
    Nat.cast_div_le
  have hltNat := Nat.lt_mul_div_succ N hd
  have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).2
    have hcast : (N : ℝ) < (d : ℝ) * ((N / d : ℕ) + 1) := by
      exact_mod_cast hltNat
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcast
  have heq :
      (d : ℝ)⁻¹ - ((N / d : ℕ) : ℝ) / N =
        (((N : ℝ) / d) - ((N / d : ℕ) : ℝ)) / N := by
    rw [inv_eq_one_div]
    field_simp [hdR.ne', hNR.ne']
  rw [heq]
  constructor
  · positivity
  · rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hNR.le
    linarith

lemma cutoffElementaryReciprocalMass_nonneg
    (N : ℕ) (A : Finset ℕ) (j : ℕ) :
    0 ≤ cutoffElementaryReciprocalMass N A j := by
  exact Finset.sum_nonneg fun _S _hS => by positivity

lemma cutoffElementaryReciprocalMass_le_elementary
    (N : ℕ) (A : Finset ℕ) (j : ℕ) :
    cutoffElementaryReciprocalMass N A j ≤
      elementaryReciprocalMass A j := by
  rw [cutoffElementaryReciprocalMass, elementaryReciprocalMass]
  simp_rw [inv_cast_subsetProduct]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun _S _hS _hnot => by positivity)

lemma cutoffElementaryReciprocalMass_le
    (N : ℕ) (A : Finset ℕ) (j : ℕ) :
    cutoffElementaryReciprocalMass N A j ≤
      reciprocalMass A ^ j / j.factorial :=
  (cutoffElementaryReciprocalMass_le_elementary N A j).trans
    (elementaryReciprocalMass_le A j)

lemma floorElementaryMass_le_cutoff {N : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (j : ℕ) :
    floorElementaryMass N A j ≤
      cutoffElementaryReciprocalMass N A j := by
  rw [floorElementaryMass, cutoffElementaryReciprocalMass,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro S hS
  have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
  have hprod : 0 < subsetProduct S := subsetProduct_pos hSA hpos
  by_cases hSN : subsetProduct S ≤ N
  · rw [if_pos hSN]
    exact sub_nonneg.mp (natDiv_normalized_error hprod hSN).1
  · have hNS : N < subsetProduct S := lt_of_not_ge hSN
    rw [if_neg hSN, Nat.div_eq_of_lt hNS]
    simp

lemma cutoff_sub_floorElementaryMass_le {N : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (j : ℕ) :
    cutoffElementaryReciprocalMass N A j -
        floorElementaryMass N A j ≤
      ((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card / (N : ℝ) := by
  rw [floorElementaryMass, cutoffElementaryReciprocalMass,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  calc
    (∑ S ∈ A.powersetCard j,
        ((if subsetProduct S ≤ N then
            (subsetProduct S : ℝ)⁻¹ else 0) -
          ((N / subsetProduct S : ℕ) : ℝ) / (N : ℝ))) ≤
        ∑ S ∈ A.powersetCard j,
          if subsetProduct S ≤ N then (N : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro S hS
      have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
      have hprod : 0 < subsetProduct S := subsetProduct_pos hSA hpos
      by_cases hSN : subsetProduct S ≤ N
      · simp only [if_pos hSN]
        exact (natDiv_normalized_error hprod hSN).2
      · have hNS : N < subsetProduct S := lt_of_not_ge hSN
        simp only [if_neg hSN, Nat.div_eq_of_lt hNS]
        simp
    _ = ((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card / (N : ℝ) := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The weak prime-number-theorem input needed for the floor-count error:
the number of primes up to `x` is `o(x)`. -/
lemma eventually_primeCounting_le_delta_mul {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x := by
  have hcheb := Chebyshev.eventually_primeCounting_le
    (show (0 : ℝ) < 1 by norm_num)
  have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hlog
  have hcoef : Tendsto
      (fun x : ℝ => (Real.log 4 + 1) / Real.log x)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun x : ℝ => (Real.log 4 + 1) *
          (Real.log x)⁻¹) atTop
          (nhds ((Real.log 4 + 1) * 0)))
  have hcoefδ : ∀ᶠ x : ℝ in atTop,
      (Real.log 4 + 1) / Real.log x < δ :=
    hcoef.eventually (Iio_mem_nhds hδ)
  filter_upwards [hcheb, hcoefδ, eventually_ge_atTop (0 : ℝ)]
      with x hprime hcoefx hx
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
        (Real.log 4 + 1) * x / Real.log x := hprime
    _ = ((Real.log 4 + 1) / Real.log x) * x := by ring
    _ ≤ δ * x := mul_le_mul_of_nonneg_right hcoefx.le hx

/-- Endpoint-fitting subsets all of whose elements lie below `z`. -/
def smallProductSubsets (A : Finset ℕ) (j z : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard j).filter fun S => S ⊆ Finset.range z

/-- Possible maximal-prime extensions of a fixed `(j-1)`-subset. -/
def primeMaxExtensions (N z : ℕ) (A R : Finset ℕ) : Finset ℕ :=
  A.filter fun q => q.Prime ∧ z ≤ q ∧ q ∉ R ∧
    (∀ a ∈ R, a < q) ∧ subsetProduct R * q ≤ N

/-- Subsets reconstructed from their maximal prime and the remaining
elements. -/
def primeMaxProductSubsets
    (N z : ℕ) (A : Finset ℕ) (j : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard (j - 1)).biUnion fun R =>
    (primeMaxExtensions N z A R).image fun q => insert q R

/-- If every composite modulus is below `z`, an endpoint-fitting nonempty
subset is either wholly below `z`, or has a prime as its maximal element. -/
lemma cutoffProductSubsets_subset_small_union_primeMax
    {N z j : ℕ} {A : Finset ℕ} (hj : 0 < j)
    (hcomp : ∀ a ∈ A, ¬a.Prime → a < z) :
    (A.powersetCard j).filter (fun S => subsetProduct S ≤ N) ⊆
      smallProductSubsets A j z ∪ primeMaxProductSubsets N z A j := by
  intro S hS
  have hScard :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hsmall : S ⊆ Finset.range z
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hS).1, hsmall⟩)
  · apply Finset.mem_union_right
    let q := S.max' hSne
    let R := S.erase q
    have hqS : q ∈ S := S.max'_mem hSne
    have hSA : S ⊆ A :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1
    have hzq : z ≤ q := by
      by_contra hqz
      apply hsmall
      intro a ha
      exact Finset.mem_range.mpr ((S.le_max' a ha).trans_lt
        (lt_of_not_ge hqz))
    have hqprime : q.Prime := by
      by_contra hnprime
      exact (not_lt_of_ge hzq) (hcomp q (hSA hqS) hnprime)
    have hRcard : R.card = j - 1 := by
      dsimp only [R]
      rw [Finset.card_erase_of_mem hqS, hScard]
    have hRA : R ⊆ A := (Finset.erase_subset _ _).trans hSA
    have hqR : q ∉ R := Finset.notMem_erase _ _
    have hRlt : ∀ a ∈ R, a < q := by
      intro a ha
      have haS : a ∈ S := Finset.mem_of_mem_erase ha
      have hale := S.le_max' a haS
      exact lt_of_le_of_ne hale (fun h => hqR (h ▸ ha))
    have hprod : subsetProduct R * q = subsetProduct S := by
      rw [show S = insert q R by simp [R, hqS]]
      simp [subsetProduct, hqR, mul_comm]
    rw [primeMaxProductSubsets]
    simp only [Finset.mem_biUnion, Finset.mem_image]
    refine ⟨R, Finset.mem_powersetCard.mpr ⟨hRA, hRcard⟩,
      q, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨hSA hqS, hqprime, hzq, hqR, hRlt,
          hprod.trans_le (Finset.mem_filter.mp hS).2⟩
    · simp [R, hqS]

lemma card_smallProductSubsets_le (A : Finset ℕ) (j z : ℕ) :
    (smallProductSubsets A j z).card ≤ 2 ^ z := by
  have hsub :
      smallProductSubsets A j z ⊆ (Finset.range z).powerset := by
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hS).2
  exact (Finset.card_le_card hsub).trans_eq (by simp)

lemma primeMaxExtensions_subset_primesLE
    {N z : ℕ} {A R : Finset ℕ} (hRA : R ⊆ A)
    (hpos : ∀ a ∈ A, 0 < a) :
    primeMaxExtensions N z A R ⊆
      Nat.primesLE ⌊(N : ℝ) / subsetProduct R⌋₊ := by
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  have hd : 0 < subsetProduct R := subsetProduct_pos hRA hpos
  have hdR : (0 : ℝ) < subsetProduct R := by exact_mod_cast hd
  have hcast :
      (subsetProduct R : ℝ) * q ≤ (N : ℝ) := by
    exact_mod_cast hq'.2.2.2.2.2
  have hqle : (q : ℝ) ≤ (N : ℝ) / subsetProduct R :=
    (le_div_iff₀ hdR).2 (by simpa [mul_comm] using hcast)
  exact Nat.mem_primesLE.mpr
    ⟨Nat.le_floor hqle, hq'.2.1⟩

/-- An existing maximal-prime extension forces the real quotient `N/prod R`
above every threshold whose `j`-th power is at most `N`. -/
lemma threshold_le_div_of_mem_primeMaxExtensions
    {N z j t q : ℕ} {A R : Finset ℕ}
    (hj : 0 < j) (hRcard : R.card = j - 1)
    (hRA : R ⊆ A) (hpos : ∀ a ∈ A, 0 < a)
    (hNt : (t : ℝ) ^ j ≤ (N : ℝ))
    (hq : q ∈ primeMaxExtensions N z A R) :
    (t : ℝ) ≤ (N : ℝ) / subsetProduct R := by
  have hq' := Finset.mem_filter.mp hq
  have hd : 0 < subsetProduct R := subsetProduct_pos hRA hpos
  have hdR : (0 : ℝ) < subsetProduct R := by exact_mod_cast hd
  have hprodLe : subsetProduct R ≤ q ^ (j - 1) := by
    rw [subsetProduct]
    calc
      (∏ a ∈ R, a) ≤ ∏ _a ∈ R, q := by
        apply Finset.prod_le_prod
        · intro a _ha
          exact Nat.zero_le a
        intro a ha
        exact hq'.2.2.2.2.1 a ha |>.le
      _ = q ^ R.card := by simp
      _ = q ^ (j - 1) := by rw [hRcard]
  have hprodLeR :
      (subsetProduct R : ℝ) ≤ (q : ℝ) ^ (j - 1) := by
    exact_mod_cast hprodLe
  have hcast :
      (subsetProduct R : ℝ) * q ≤ (N : ℝ) := by
    exact_mod_cast hq'.2.2.2.2.2
  let x : ℝ := (N : ℝ) / subsetProduct R
  have hx0 : 0 ≤ x := by positivity
  have hqx : (q : ℝ) ≤ x :=
    (le_div_iff₀ hdR).2 (by simpa [mul_comm] using hcast)
  have hdx : (subsetProduct R : ℝ) * x = N := by
    dsimp only [x]
    field_simp [hdR.ne']
  have hNpow : (N : ℝ) ≤ x ^ j := by
    calc
      (N : ℝ) = (subsetProduct R : ℝ) * x := hdx.symm
      _ ≤ (q : ℝ) ^ (j - 1) * x :=
        mul_le_mul_of_nonneg_right hprodLeR hx0
      _ ≤ x ^ (j - 1) * x := by gcongr
      _ = x ^ ((j - 1) + 1) := (pow_succ x (j - 1)).symm
      _ = x ^ j := by congr 1; omega
  have hpow : (t : ℝ) ^ j ≤ x ^ j := hNt.trans hNpow
  exact le_of_pow_le_pow_left₀ hj.ne' hx0 hpow

lemma card_primeMaxExtensions_le_delta
    {N z j t : ℕ} {δ : ℝ} {A R : Finset ℕ}
    (hj : 0 < j) (hR : R ∈ A.powersetCard (j - 1))
    (hpos : ∀ a ∈ A, 0 < a) (hδ : 0 ≤ δ)
    (hNt : (t : ℝ) ^ j ≤ (N : ℝ))
    (hpi : ∀ x : ℝ, (t : ℝ) ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x) :
    ((primeMaxExtensions N z A R).card : ℝ) ≤
      δ * (N : ℝ) * (subsetProduct R : ℝ)⁻¹ := by
  have hRA := (Finset.mem_powersetCard.mp hR).1
  have hRcard := (Finset.mem_powersetCard.mp hR).2
  by_cases he : (primeMaxExtensions N z A R).Nonempty
  · obtain ⟨q, hq⟩ := he
    have ht := threshold_le_div_of_mem_primeMaxExtensions hj hRcard
      hRA hpos hNt hq
    have hcardNat := Finset.card_le_card
      (primeMaxExtensions_subset_primesLE
        (N := N) (z := z) hRA hpos)
    have hcard : ((primeMaxExtensions N z A R).card : ℝ) ≤
        (Nat.primeCounting ⌊(N : ℝ) / subsetProduct R⌋₊ : ℝ) := by
      simpa using (show
        ((primeMaxExtensions N z A R).card : ℝ) ≤
          ((Nat.primesLE
            ⌊(N : ℝ) / subsetProduct R⌋₊).card : ℝ) by
            exact_mod_cast hcardNat)
    calc
      ((primeMaxExtensions N z A R).card : ℝ) ≤
          (Nat.primeCounting
            ⌊(N : ℝ) / subsetProduct R⌋₊ : ℝ) := hcard
      _ ≤ δ * ((N : ℝ) / subsetProduct R) := hpi _ ht
      _ = δ * (N : ℝ) * (subsetProduct R : ℝ)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have hprod0 : (0 : ℝ) ≤ (subsetProduct R : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le (subsetProduct R))
    simpa using mul_nonneg (mul_nonneg hδ hN0) hprod0

lemma card_primeMaxProductSubsets_le_sum (N z : ℕ)
    (A : Finset ℕ) (j : ℕ) :
    (primeMaxProductSubsets N z A j).card ≤
      ∑ R ∈ A.powersetCard (j - 1),
        (primeMaxExtensions N z A R).card := by
  unfold primeMaxProductSubsets
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun _R _hR => Finset.card_image_le)

lemma card_primeMaxProductSubsets_cast_le_delta
    {N z j t : ℕ} {δ : ℝ} {A : Finset ℕ}
    (hj : 0 < j) (hpos : ∀ a ∈ A, 0 < a) (hδ : 0 ≤ δ)
    (hNt : (t : ℝ) ^ j ≤ (N : ℝ))
    (hpi : ∀ x : ℝ, (t : ℝ) ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x) :
    ((primeMaxProductSubsets N z A j).card : ℝ) ≤
      δ * (N : ℝ) * elementaryReciprocalMass A (j - 1) := by
  have hcardNat := card_primeMaxProductSubsets_le_sum N z A j
  have hcard : ((primeMaxProductSubsets N z A j).card : ℝ) ≤
      ∑ R ∈ A.powersetCard (j - 1),
        ((primeMaxExtensions N z A R).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((primeMaxProductSubsets N z A j).card : ℝ) ≤
        ∑ R ∈ A.powersetCard (j - 1),
          ((primeMaxExtensions N z A R).card : ℝ) := hcard
    _ ≤ ∑ R ∈ A.powersetCard (j - 1),
          δ * (N : ℝ) * (subsetProduct R : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun R hR =>
        card_primeMaxExtensions_le_delta hj hR hpos hδ hNt hpi
    _ = δ * (N : ℝ) * elementaryReciprocalMass A (j - 1) := by
      rw [elementaryReciprocalMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro R _hR
      rw [inv_cast_subsetProduct]

/-- Quantitative cardinal bound for the endpoint-fitting `j`-subsets.  The
first term is the bounded family lying below `z`; the second is the `o(N)`
prime-extension term. -/
lemma cutoffSubsetCount_div_le
    {N z j t : ℕ} {δ : ℝ} {A : Finset ℕ}
    (hN : 0 < N) (hj : 0 < j)
    (hpos : ∀ a ∈ A, 0 < a)
    (hcomp : ∀ a ∈ A, ¬a.Prime → a < z)
    (hδ : 0 ≤ δ) (hNt : (t : ℝ) ^ j ≤ (N : ℝ))
    (hpi : ∀ x : ℝ, (t : ℝ) ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x) :
    (((A.powersetCard j).filter
        (fun S => subsetProduct S ≤ N)).card : ℝ) / (N : ℝ) ≤
      (2 ^ z : ℕ) / (N : ℝ) +
        δ * elementaryReciprocalMass A (j - 1) := by
  have hsub := cutoffProductSubsets_subset_small_union_primeMax
    (N := N) hj hcomp
  have hcardNat :
      ((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card ≤
        (smallProductSubsets A j z).card +
          (primeMaxProductSubsets N z A j).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcard :
      (((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card : ℝ) ≤
        ((smallProductSubsets A j z).card : ℝ) +
          ((primeMaxProductSubsets N z A j).card : ℝ) := by
    exact_mod_cast hcardNat
  have hsmall : ((smallProductSubsets A j z).card : ℝ) ≤
      (2 ^ z : ℕ) := by
    exact_mod_cast card_smallProductSubsets_le A j z
  have hlarge := card_primeMaxProductSubsets_cast_le_delta
    hj hpos hδ hNt hpi (z := z)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (((A.powersetCard j).filter
        (fun S => subsetProduct S ≤ N)).card : ℝ) / (N : ℝ) ≤
        (((smallProductSubsets A j z).card : ℝ) +
          ((primeMaxProductSubsets N z A j).card : ℝ)) / N :=
      div_le_div_of_nonneg_right hcard hNR.le
    _ = ((smallProductSubsets A j z).card : ℝ) / N +
        ((primeMaxProductSubsets N z A j).card : ℝ) / N := by
      rw [add_div]
    _ ≤ (2 ^ z : ℕ) / (N : ℝ) +
        (δ * (N : ℝ) * elementaryReciprocalMass A (j - 1)) / N := by
      exact add_le_add
        (div_le_div_of_nonneg_right hsmall hNR.le)
        (div_le_div_of_nonneg_right hlarge hNR.le)
    _ = (2 ^ z : ℕ) / (N : ℝ) +
        δ * elementaryReciprocalMass A (j - 1) := by
      field_simp [hNR.ne']

/-- Tao's finite reciprocal truncation `σ_{N,r}(A)`.  Terms whose subset
product exceeds `N` are omitted exactly as in the paper. -/
def truncatedSieveApprox (N : ℕ) (A : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j

/-- Subsets indexing the same truncation, with the degree and endpoint
product conditions recorded in a single finite set. -/
def cutoffSubsets (N : ℕ) (A : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ) :=
  A.powerset.filter fun S => S.card ≤ r ∧ subsetProduct S ≤ N

/-- The signed reciprocal monomial attached to a subset of moduli. -/
def reciprocalSubsetTerm (S : Finset ℕ) : ℝ :=
  (-1 : ℝ) ^ S.card * (subsetProduct S : ℝ)⁻¹

lemma subsetProduct_union {S T : Finset ℕ} (h : Disjoint S T) :
    subsetProduct (S ∪ T) = subsetProduct S * subsetProduct T := by
  simp [subsetProduct, Finset.prod_union h]

lemma reciprocalSubsetTerm_union {S T : Finset ℕ}
    (h : Disjoint S T) :
    reciprocalSubsetTerm (S ∪ T) =
      reciprocalSubsetTerm S * reciprocalSubsetTerm T := by
  rw [reciprocalSubsetTerm, reciprocalSubsetTerm,
    reciprocalSubsetTerm, Finset.card_union_of_disjoint h,
    subsetProduct_union h, pow_add, Nat.cast_mul]
  rw [mul_inv_rev]
  ring

lemma truncatedSieveApprox_eq_sum_cutoffSubsets
    (N : ℕ) (A : Finset ℕ) (r : ℕ) :
    truncatedSieveApprox N A r =
      ∑ S ∈ cutoffSubsets N A r, reciprocalSubsetTerm S := by
  rw [cutoffSubsets, Finset.sum_filter, Finset.sum_powerset]
  let f : ℕ → ℝ := fun j =>
    ∑ S ∈ A.powersetCard j,
      if S.card ≤ r ∧ subsetProduct S ≤ N then
        reciprocalSubsetTerm S else 0
  change truncatedSieveApprox N A r =
    ∑ j ∈ Finset.range (A.card + 1), f j
  have heq (j : ℕ) (hj : j ≤ r) :
      (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j = f j := by
    rw [cutoffElementaryReciprocalMass, Finset.mul_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    have hcardeq := (Finset.mem_powersetCard.mp hS).2
    dsimp only [f, reciprocalSubsetTerm]
    rw [hcardeq]
    by_cases hprod : subsetProduct S ≤ N <;> simp [hj, hprod]
  have hfzero (j : ℕ) (hrj : r < j) : f j = 0 := by
    change (∑ S ∈ A.powersetCard j,
      if S.card ≤ r ∧ subsetProduct S ≤ N then
        reciprocalSubsetTerm S else 0) = 0
    apply Finset.sum_eq_zero
    intro S hS
    have hcard := (Finset.mem_powersetCard.mp hS).2
    rw [hcard]
    simp [Nat.not_le.mpr hrj]
  by_cases hrcard : r ≤ A.card
  · have hle : r + 1 ≤ A.card + 1 := Nat.succ_le_succ hrcard
    rw [truncatedSieveApprox]
    have hprefix :
        (∑ j ∈ Finset.range (r + 1),
          (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j) =
        ∑ j ∈ Finset.range (r + 1), f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact heq j (by simpa using hj)
    rw [hprefix, ← Finset.sum_range_add_sum_Ico f hle]
    have htail :
        ∑ j ∈ Finset.Ico (r + 1) (A.card + 1), f j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hfzero j (by
        have hj' := Finset.mem_Ico.mp hj
        omega)
    rw [htail, add_zero]
  · have hcardr : A.card ≤ r := Nat.le_of_not_ge hrcard
    have hle : A.card + 1 ≤ r + 1 := Nat.succ_le_succ hcardr
    rw [truncatedSieveApprox]
    rw [← Finset.sum_range_add_sum_Ico
      (fun j => (-1 : ℝ) ^ j *
        cutoffElementaryReciprocalMass N A j) hle]
    have hprefix :
        (∑ j ∈ Finset.range (A.card + 1),
          (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j) =
        ∑ j ∈ Finset.range (A.card + 1), f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact heq j (by
        have hj' := Finset.mem_range.mp hj
        omega)
    rw [hprefix]
    have htail :
        ∑ j ∈ Finset.Ico (A.card + 1) (r + 1),
          (-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have hjcard : A.card < j := by omega
      have hpowers : A.powersetCard j = ∅ :=
        Finset.powersetCard_eq_empty.mpr hjcard
      rw [cutoffElementaryReciprocalMass, hpowers]
      simp
    rw [htail, add_zero]

/-- The total unit-floor error at truncation depth `r`. -/
def floorErrorBound (N : ℕ) (A : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    ((A.powersetCard j).filter
        (fun S => subsetProduct S ≤ N)).card / (N : ℝ)

/-- Fixed coefficient multiplying the prime-counting error in the uniform
floor estimate. -/
def floorErrorCoefficient (C : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    if j = 0 then 0 else C ^ (j - 1) / (j - 1).factorial

lemma floorErrorBound_le_majorant
    {C δ : ℝ} {N z r t : ℕ} {A : Finset ℕ}
    (_hC : 0 ≤ C) (hδ : 0 ≤ δ) (hN : 0 < N)
    (hA : Admissible C N A)
    (hcomp : ∀ a ∈ A, ¬a.Prime → a < z)
    (hpow : ∀ j : ℕ, j ≤ r → (t : ℝ) ^ j ≤ (N : ℝ))
    (hpi : ∀ x : ℝ, (t : ℝ) ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x) :
    floorErrorBound N A r ≤
      (r + 1 : ℕ) * ((2 ^ z : ℕ) / (N : ℝ)) +
        δ * floorErrorCoefficient C r := by
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha
    exact (hA.two_le ha).trans_lt' (by omega)
  rw [floorErrorBound]
  calc
    (∑ j ∈ Finset.range (r + 1),
        ((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card / (N : ℝ)) ≤
      ∑ j ∈ Finset.range (r + 1),
        ((2 ^ z : ℕ) / (N : ℝ) +
          if j = 0 then 0 else
            δ * (C ^ (j - 1) / (j - 1).factorial)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        have hfilter :
            (A.powersetCard 0).filter
                (fun S => subsetProduct S ≤ N) = {∅} := by
          ext S
          simp only [Finset.mem_filter, Finset.mem_powersetCard,
            Finset.mem_singleton]
          constructor
          · rintro ⟨⟨_hSA, hcard⟩, _hprod⟩
            exact Finset.card_eq_zero.mp hcard
          · intro hS
            subst S
            have h1N : 1 ≤ N := hN
            simp [subsetProduct, h1N]
        rw [hfilter]
        simp only [Finset.card_singleton, Nat.cast_one, if_pos]
        have hpowzNat : 1 ≤ 2 ^ z :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        have hpowz : (1 : ℝ) ≤ (2 ^ z : ℕ) := by
          exact_mod_cast hpowzNat
        have hNR : (0 : ℝ) ≤ N := by positivity
        simpa using div_le_div_of_nonneg_right hpowz hNR
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hjr : j ≤ r := by
          simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj
        have hcount := cutoffSubsetCount_div_le hN hjpos hpos hcomp
          hδ (hpow j hjr) hpi
        rw [if_neg hj0]
        refine hcount.trans (add_le_add le_rfl ?_)
        have helem := elementaryReciprocalMass_le A (j - 1)
        have hmassPow :
            reciprocalMass A ^ (j - 1) ≤ C ^ (j - 1) :=
          pow_le_pow_left₀ (reciprocalMass_nonneg A) hA.mass_le _
        have hdiv :
            reciprocalMass A ^ (j - 1) / (j - 1).factorial ≤
              C ^ (j - 1) / (j - 1).factorial :=
          div_le_div_of_nonneg_right hmassPow (by positivity)
        exact mul_le_mul_of_nonneg_left (helem.trans hdiv) hδ
    _ = (r + 1 : ℕ) * ((2 ^ z : ℕ) / (N : ℝ)) +
        δ * floorErrorCoefficient C r := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [floorErrorCoefficient, Finset.mul_sum]
      apply congrArg (fun x : ℝ =>
        (r + 1 : ℕ) * ((2 ^ z : ℕ) / (N : ℝ)) + x)
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases h : j = 0 <;> simp [h]

lemma floorErrorCoefficient_nonneg {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    0 ≤ floorErrorCoefficient C r := by
  rw [floorErrorCoefficient]
  apply Finset.sum_nonneg
  intro j _hj
  by_cases h : j = 0
  · simp [h]
  · simp only [if_neg h]
    positivity

/-- Uniform form of the `O(r e^C / log N)` floor error in Tao's
Bonferroni lemma.  Only the qualitative `o(1)` consequence is needed by the
later parameter hierarchy. -/
theorem eventually_floorErrorBound_lt
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (z r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      Admissible C N A →
      (∀ a ∈ A, ¬a.Prime → a < z) →
      floorErrorBound N A r < ε := by
  let B := floorErrorCoefficient C r
  have hB : 0 ≤ B := floorErrorCoefficient_nonneg hC r
  let δ := ε / (4 * (B + 1))
  have hden : 0 < 4 * (B + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδB : δ * B < ε / 2 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hpnt := eventually_primeCounting_le_delta_mul hδ
  rw [eventually_atTop] at hpnt
  obtain ⟨T, hT⟩ := hpnt
  obtain ⟨t₀, ht₀⟩ := exists_nat_ge T
  let t := max t₀ 1
  have ht₀t : t₀ ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t := le_max_right _ _
  have hpi : ∀ x : ℝ, (t : ℝ) ≤ x →
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ δ * x := by
    intro x htx
    apply hT x
    exact ht₀.trans (by exact_mod_cast ht₀t) |>.trans htx
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmallT : Tendsto
      (fun N : ℕ => (r + 1 : ℕ) *
        ((2 ^ z : ℕ) / (N : ℝ))) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : ℕ =>
          (((r + 1 : ℕ) : ℝ) * (2 ^ z : ℕ)) * (N : ℝ)⁻¹)
          atTop (nhds
            ((((r + 1 : ℕ) : ℝ) * (2 ^ z : ℕ)) * 0)))
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (r + 1 : ℕ) * ((2 ^ z : ℕ) / (N : ℝ)) < ε / 2 :=
    hsmallT.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hsmall, eventually_ge_atTop (t ^ r),
      eventually_ge_atTop 1] with N hsmallN hNt hN1
  intro A hA hcomp
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hpow : ∀ j : ℕ, j ≤ r → (t : ℝ) ^ j ≤ (N : ℝ) := by
    intro j hjr
    have hpowNat : t ^ j ≤ t ^ r := Nat.pow_le_pow_right ht1 hjr
    have hpowReal : (t : ℝ) ^ j ≤ (t : ℝ) ^ r := by
      exact_mod_cast hpowNat
    have hNtReal : (t : ℝ) ^ r ≤ (N : ℝ) := by
      exact_mod_cast hNt
    exact hpowReal.trans hNtReal
  have hmajor := floorErrorBound_le_majorant hC hδ.le hN hA hcomp
    hpow hpi
  change floorErrorBound N A r < ε
  have hBdef : floorErrorCoefficient C r = B := rfl
  rw [hBdef] at hmajor
  linarith

/-- The exact averaged Bonferroni polynomial before replacing floors by
reciprocal products. -/
def truncatedFloorSum (N : ℕ) (A : Finset ℕ) (r : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (r + 1),
    ∑ S ∈ A.powersetCard j,
      (-1 : ℤ) ^ j * (N / subsetProduct S : ℕ)

/-- The real normalized form of `truncatedFloorSum`. -/
def truncatedFloorApprox (N : ℕ) (A : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1 : ℝ) ^ j * floorElementaryMass N A j

lemma cast_truncatedFloorSum_div (N : ℕ) (A : Finset ℕ) (r : ℕ) :
    (truncatedFloorSum N A r : ℝ) / (N : ℝ) =
      truncatedFloorApprox N A r := by
  unfold truncatedFloorSum truncatedFloorApprox floorElementaryMass
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Int.cast_sum, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _hS
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast]
  rw [mul_div_assoc]

lemma abs_truncatedSieveApprox_sub_floor_le {N : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (r : ℕ) :
    |truncatedSieveApprox N A r - truncatedFloorApprox N A r| ≤
      floorErrorBound N A r := by
  rw [truncatedSieveApprox, truncatedFloorApprox,
    floorErrorBound, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j -
          (-1 : ℝ) ^ j * floorElementaryMass N A j)| ≤
        ∑ j ∈ Finset.range (r + 1),
          |(-1 : ℝ) ^ j * cutoffElementaryReciprocalMass N A j -
            (-1 : ℝ) ^ j * floorElementaryMass N A j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (r + 1),
          (cutoffElementaryReciprocalMass N A j -
            floorElementaryMass N A j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← mul_sub]
      have hnonneg :
          0 ≤ cutoffElementaryReciprocalMass N A j -
            floorElementaryMass N A j :=
        sub_nonneg.mpr (floorElementaryMass_le_cutoff hpos j)
      simp [abs_mul, abs_of_nonneg hnonneg]
    _ ≤ ∑ j ∈ Finset.range (r + 1),
        ((A.powersetCard j).filter
          (fun S => subsetProduct S ≤ N)).card / (N : ℝ) := by
      exact Finset.sum_le_sum fun j _hj =>
        cutoff_sub_floorElementaryMass_le hpos j

/-- For a subset of a pairwise-coprime family, simultaneous divisibility is
equivalent to divisibility by the product. -/
lemma subsetProduct_dvd_iff {A S : Finset ℕ} {n : ℕ}
    (hA : PairwiseCoprime A) (hSA : S ⊆ A) :
    subsetProduct S ∣ n ↔ ∀ a ∈ S, a ∣ n := by
  constructor
  · intro hprod a ha
    exact (Finset.dvd_prod_of_mem id ha).trans hprod
  · intro hall
    induction S using Finset.induction_on with
    | empty => simp [subsetProduct]
    | @insert a S haS ih =>
        rw [subsetProduct, Finset.prod_insert haS]
        have hada : a ∣ n := hall a (Finset.mem_insert_self a S)
        have hdS : subsetProduct S ∣ n := by
          apply ih (Finset.Subset.trans (Finset.subset_insert a S) hSA)
          intro b hb
          exact hall b (Finset.mem_insert_of_mem hb)
        have hcop : Nat.Coprime a (subsetProduct S) := by
          rw [subsetProduct]
          apply Nat.Coprime.prod_right
          intro b hb
          exact hA (hSA (Finset.mem_insert_self a S))
            (hSA (Finset.mem_insert_of_mem hb))
            (Ne.symm (ne_of_mem_of_not_mem hb haS))
        exact hcop.mul_dvd_of_dvd_of_dvd hada hdS

/-- Integers in the positive prefix divisible by every member of `S`. -/
def commonMultiplesIn (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ∀ a ∈ S, a ∣ n

lemma commonMultiplesIn_eq_multiplesIn {A S : Finset ℕ} (N : ℕ)
    (hA : PairwiseCoprime A) (hSA : S ⊆ A) :
    commonMultiplesIn N S = multiplesIn N (subsetProduct S) := by
  ext n
  simp only [commonMultiplesIn, multiplesIn, Finset.mem_filter,
    Finset.mem_Ioc]
  exact and_congr_right fun _ => (subsetProduct_dvd_iff hA hSA).symm

/-- Exact common-multiple count, the arithmetic input to finite
inclusion--exclusion. -/
lemma commonMultiplesIn_card_eq_div {A S : Finset ℕ} (N : ℕ)
    (hA : PairwiseCoprime A) (hSA : S ⊆ A) :
    (commonMultiplesIn N S).card = N / subsetProduct S := by
  rw [commonMultiplesIn_eq_multiplesIn N hA hSA,
    multiplesIn_card_eq_div]

lemma Icc_one_eq_Ioc_zero (N : ℕ) :
    Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp
  omega

/-- Summing the pointwise indicator recovers the literal survivor count. -/
lemma sum_survivorIndicator (N : ℕ) (A : Finset ℕ) :
    (∑ n ∈ Finset.Icc 1 N, survivorIndicator n A) =
      ((unsieved N A).card : ℤ) := by
  simp [survivorIndicator, unsieved]

lemma sum_subsetDivisibilityIndicator {A S : Finset ℕ} (N : ℕ)
    (hA : PairwiseCoprime A) (hSA : S ⊆ A) :
    (∑ n ∈ Finset.Icc 1 N,
      if ∀ a ∈ S, a ∣ n then (-1 : ℤ) ^ S.card else 0) =
      (-1 : ℤ) ^ S.card * (N / subsetProduct S : ℕ) := by
  rw [Icc_one_eq_Ioc_zero]
  rw [← Finset.sum_filter]
  change (∑ _n ∈ commonMultiplesIn N S, (-1 : ℤ) ^ S.card) = _
  rw [Finset.sum_const, nsmul_eq_mul,
    commonMultiplesIn_card_eq_div N hA hSA]
  push_cast
  ring

/-- Averaging the subset-indexed truncated polynomial gives precisely the
floor sum.  Pairwise coprimality is used only to identify a simultaneous
divisibility condition with divisibility by the subset product. -/
lemma sum_truncatedInclusionAt {N : ℕ} {A : Finset ℕ}
    (hA : PairwiseCoprime A) (r : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, truncatedInclusionAt n A r) =
      truncatedFloorSum N A r := by
  unfold truncatedInclusionAt truncatedFloorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hSA : S ⊆ A := (Finset.mem_powersetCard.mp hS).1
  have hsum := sum_subsetDivisibilityIndicator N hA hSA
  simpa only [(Finset.mem_powersetCard.mp hS).2] using hsum

/-- Odd averaged Bonferroni truncations are lower bounds for the literal
survivor count. -/
lemma truncatedFloorSum_odd_le_card_unsieved {N : ℕ} {A : Finset ℕ}
    (hA : PairwiseCoprime A) (r : ℕ) :
    truncatedFloorSum N A (2 * r + 1) ≤ ((unsieved N A).card : ℤ) := by
  rw [← sum_truncatedInclusionAt hA,
    ← sum_survivorIndicator]
  apply Finset.sum_le_sum
  intro n _hn
  rw [truncatedInclusionAt_eq_bonferroniAt]
  exact bonferroniAt_odd_le_survivorIndicator n A r

/-- Even averaged Bonferroni truncations are upper bounds for the literal
survivor count. -/
lemma card_unsieved_le_truncatedFloorSum_even {N : ℕ} {A : Finset ℕ}
    (hA : PairwiseCoprime A) (r : ℕ) :
    ((unsieved N A).card : ℤ) ≤ truncatedFloorSum N A (2 * r) := by
  rw [← sum_truncatedInclusionAt hA,
    ← sum_survivorIndicator]
  apply Finset.sum_le_sum
  intro n _hn
  rw [truncatedInclusionAt_eq_bonferroniAt]
  exact survivorIndicator_le_bonferroniAt_even n A r

/-- Normalized odd Bonferroni bound, expressed in the reciprocal model plus
its explicit floor error. -/
lemma truncatedSieveApprox_sub_error_le_sieveDensity
    {N : ℕ} (hN : 0 < N) {A : Finset ℕ}
    (hA : PairwiseCoprime A) (hpos : ∀ a ∈ A, 0 < a) (r : ℕ) :
    truncatedSieveApprox N A (2 * r + 1) -
        floorErrorBound N A (2 * r + 1) ≤
      sieveDensity N A := by
  have hfloorInt :=
    truncatedFloorSum_odd_le_card_unsieved (N := N) hA r
  have hfloorCast :
      (truncatedFloorSum N A (2 * r + 1) : ℝ) ≤
        ((unsieved N A).card : ℝ) := by
    exact_mod_cast hfloorInt
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor :
      truncatedFloorApprox N A (2 * r + 1) ≤ sieveDensity N A := by
    simpa only [cast_truncatedFloorSum_div, sieveDensity] using
      (div_le_div_of_nonneg_right hfloorCast hNR.le)
  have herr := abs_truncatedSieveApprox_sub_floor_le
    (N := N) hpos (2 * r + 1)
  have hleft :
      truncatedSieveApprox N A (2 * r + 1) -
          truncatedFloorApprox N A (2 * r + 1) ≤
        floorErrorBound N A (2 * r + 1) :=
    (le_abs_self _).trans herr
  linarith

/-- The corresponding normalized upper Bonferroni bound. -/
lemma sieveDensity_le_truncatedSieveApprox_add_error
    {N : ℕ} (hN : 0 < N) {A : Finset ℕ}
    (hA : PairwiseCoprime A) (hpos : ∀ a ∈ A, 0 < a) (r : ℕ) :
    sieveDensity N A ≤
      truncatedSieveApprox N A (2 * r) + floorErrorBound N A (2 * r) := by
  have hfloorInt :=
    card_unsieved_le_truncatedFloorSum_even (N := N) hA r
  have hfloorCast :
      ((unsieved N A).card : ℝ) ≤
        (truncatedFloorSum N A (2 * r) : ℝ) := by
    exact_mod_cast hfloorInt
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfloor :
      sieveDensity N A ≤ truncatedFloorApprox N A (2 * r) := by
    simpa only [cast_truncatedFloorSum_div, sieveDensity] using
      (div_le_div_of_nonneg_right hfloorCast hNR.le)
  have herr := abs_truncatedSieveApprox_sub_floor_le
    (N := N) hpos (2 * r)
  have hright :
      truncatedFloorApprox N A (2 * r) -
          truncatedSieveApprox N A (2 * r) ≤
        floorErrorBound N A (2 * r) := by
    have := (neg_le_abs
      (truncatedSieveApprox N A (2 * r) -
        truncatedFloorApprox N A (2 * r))).trans herr
    linarith
  linarith

/-- Exact finite inclusion--exclusion for every pairwise-coprime family. -/
lemma cutoffElementaryReciprocalMass_le_budget
    {C : ℝ} {N j : ℕ} {A : Finset ℕ}
    (hC : 0 ≤ C) (hmass : reciprocalMass A ≤ C) :
    cutoffElementaryReciprocalMass N A j ≤ C ^ j / j.factorial := by
  exact (cutoffElementaryReciprocalMass_le_elementary N A j).trans
    ((elementaryReciprocalMass_le A j).trans
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (reciprocalMass_nonneg A) hmass j)
        (by positivity)))

lemma truncatedSieveApprox_succ (N : ℕ) (A : Finset ℕ) (r : ℕ) :
    truncatedSieveApprox N A (r + 1) =
      truncatedSieveApprox N A r +
        (-1 : ℝ) ^ (r + 1) *
          cutoffElementaryReciprocalMass N A (r + 1) := by
  rw [truncatedSieveApprox, truncatedSieveApprox,
    show r + 1 + 1 = (r + 1) + 1 by omega,
    Finset.sum_range_succ]

lemma sieveDensity_truncated_abs_le
    {C : ℝ} (hC : 0 ≤ C) {N r : ℕ} {A : Finset ℕ}
    (hN : 0 < N) (hA : Admissible C N A) :
    |sieveDensity N A - truncatedSieveApprox N A r| ≤
      C ^ (r + 1) / (r + 1).factorial +
        max (floorErrorBound N A r) (floorErrorBound N A (r + 1)) := by
  have hpos : ∀ a ∈ A, 0 < a := fun a ha =>
    (hA.two_le ha).trans_lt' (by omega)
  have hlayer := cutoffElementaryReciprocalMass_le_budget
    hC hA.mass_le (N := N) (j := r + 1)
  have hlayer0 := cutoffElementaryReciprocalMass_nonneg N A (r + 1)
  rcases Nat.even_or_odd r with heven | hodd
  · obtain ⟨s, rfl⟩ := heven
    have hu := sieveDensity_le_truncatedSieveApprox_add_error
      hN hA.pairwiseCoprime hpos s
    have hl := truncatedSieveApprox_sub_error_le_sieveDensity
      hN hA.pairwiseCoprime hpos s
    have hsucc := truncatedSieveApprox_succ N A (2 * s)
    norm_num [pow_succ] at hsucc
    have h2 : 2 * s = s + s := by omega
    simp only [h2] at hu hl hsucc
    have hlow :
        truncatedSieveApprox N A (s + s) - sieveDensity N A ≤
          C ^ (s + s + 1) / (s + s + 1).factorial +
            floorErrorBound N A (s + s + 1) := by
      linarith
    rw [abs_le]
    constructor
    · have hmax := le_max_right (floorErrorBound N A (s + s))
          (floorErrorBound N A (s + s + 1))
      linarith [pow_nonneg hC (s + s + 1)]
    · have hmax := le_max_left (floorErrorBound N A (s + s))
          (floorErrorBound N A (s + s + 1))
      linarith [div_nonneg (pow_nonneg hC (s + s + 1)) (by positivity)]
  · obtain ⟨s, rfl⟩ := hodd
    have hl := truncatedSieveApprox_sub_error_le_sieveDensity
      hN hA.pairwiseCoprime hpos s
    have hu := sieveDensity_le_truncatedSieveApprox_add_error
      hN hA.pairwiseCoprime hpos (s + 1)
    have hsucc := truncatedSieveApprox_succ N A (2 * s + 1)
    norm_num [pow_succ] at hsucc
    have h2 : 2 * s + 1 = s + s + 1 := by omega
    have hn : 2 * (s + 1) = s + s + 1 + 1 := by omega
    simp only [h2] at hlayer hlayer0 ⊢
    simp only [h2, hn] at hu hl hsucc
    have hu' : sieveDensity N A - truncatedSieveApprox N A (s + s + 1) ≤
        C ^ (s + s + 1 + 1) / (s + s + 1 + 1).factorial +
          floorErrorBound N A (s + s + 1 + 1) := by
      linarith
    rw [abs_le]
    constructor
    · have hmax := le_max_left (floorErrorBound N A (s + s + 1))
          (floorErrorBound N A (s + s + 1 + 1))
      linarith [div_nonneg (pow_nonneg hC (s + s + 1 + 1))
        (by positivity)]
    · have hmax := le_max_right (floorErrorBound N A (s + s + 1))
          (floorErrorBound N A (s + s + 1 + 1))
      linarith [pow_nonneg hC (s + s + 1 + 1)]

theorem eventually_sieveDensity_truncated_abs_lt
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (z r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      Admissible C N A →
      (∀ a ∈ A, ¬a.Prime → a < z) →
      |sieveDensity N A - truncatedSieveApprox N A r| <
        C ^ (r + 1) / (r + 1).factorial + ε := by
  have hfloorR := eventually_floorErrorBound_lt hC (half_pos hε) z r
  have hfloorS := eventually_floorErrorBound_lt hC (half_pos hε) z (r + 1)
  filter_upwards [hfloorR, hfloorS, eventually_ge_atTop 1]
    with N hR hS hN
  intro A hA hcomp
  have hmax : max (floorErrorBound N A r)
      (floorErrorBound N A (r + 1)) < ε := by
    rw [max_lt_iff]
    exact ⟨(hR A hA hcomp).trans (half_lt_self hε),
      (hS A hA hcomp).trans (half_lt_self hε)⟩
  have hbound := sieveDensity_truncated_abs_le hC
    (zero_lt_one.trans_le hN) hA (r := r)
  linarith


theorem card_unsieved_eq_inclusionExclusion {N : ℕ} {A : Finset ℕ}
    (hA : PairwiseCoprime A) :
    ((unsieved N A).card : ℤ) =
      ∑ S ∈ A.powerset,
        (-1 : ℤ) ^ S.card * (N / subsetProduct S : ℕ) := by
  rw [← sum_survivorIndicator]
  calc
    (∑ n ∈ Finset.Icc 1 N, survivorIndicator n A) =
        ∑ n ∈ Finset.Icc 1 N, fullInclusionAt n A := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact (fullInclusionAt_eq_survivorIndicator n A).symm
    _ = ∑ S ∈ A.powerset,
        ∑ n ∈ Finset.Icc 1 N,
          if ∀ a ∈ S, a ∣ n then (-1 : ℤ) ^ S.card else 0 := by
      simp only [fullInclusionAt]
      rw [Finset.sum_comm]
    _ = ∑ S ∈ A.powerset,
        (-1 : ℤ) ^ S.card * (N / subsetProduct S : ℕ) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact sum_subsetDivisibilityIndicator N hA
        (Finset.mem_powerset.mp hS)

lemma modulusProduct_div_subsetProduct {A S : Finset ℕ}
    (hSA : S ⊆ A) (hpos : ∀ a ∈ A, 0 < a) :
    modulusProduct A / subsetProduct S = subsetProduct (A \ S) := by
  have hfactor :
      subsetProduct (A \ S) * subsetProduct S = modulusProduct A := by
    simpa only [subsetProduct, modulusProduct] using
      (Finset.prod_sdiff hSA (f := fun a : ℕ => a))
  have hSpos : 0 < subsetProduct S := by
    apply Finset.prod_pos
    intro a ha
    exact hpos a (hSA ha)
  rw [← hfactor, mul_comm, Nat.mul_div_cancel_left _ hSpos]

/-- The algebraic product expansion underlying exact density in one complete
period. -/
lemma inclusionExclusion_product_identity (A : Finset ℕ) :
    (∑ S ∈ A.powerset,
      (-1 : ℤ) ^ S.card * (subsetProduct (A \ S) : ℤ)) =
      ∏ a ∈ A, ((a : ℤ) - 1) := by
  symm
  simpa [subsetProduct] using
    (Finset.prod_sub (fun a : ℕ => (a : ℤ)) (fun _a : ℕ => (1 : ℤ)) A)

/-- Exact survivor count in a complete common period. -/
theorem card_unsieved_modulusProduct {A : Finset ℕ}
    (hA : PairwiseCoprime A) (hpos : ∀ a ∈ A, 0 < a) :
    ((unsieved (modulusProduct A) A).card : ℤ) =
      ∏ a ∈ A, ((a : ℤ) - 1) := by
  rw [card_unsieved_eq_inclusionExclusion hA]
  calc
    (∑ S ∈ A.powerset,
        (-1 : ℤ) ^ S.card *
          (modulusProduct A / subsetProduct S : ℕ)) =
        ∑ S ∈ A.powerset,
          (-1 : ℤ) ^ S.card * (subsetProduct (A \ S) : ℤ) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [modulusProduct_div_subsetProduct
        (Finset.mem_powerset.mp hS) hpos]
    _ = ∏ a ∈ A, ((a : ℤ) - 1) :=
      inclusionExclusion_product_identity A

/-- The Euler product which is the exact survivor density over a complete
period of a pairwise-coprime family. -/
def periodicDensity (A : Finset ℕ) : ℝ :=
  ∏ a ∈ A, (1 - (a : ℝ)⁻¹)

/-- The full alternating reciprocal expansion of the finite Euler product.
This is the untruncated comparison object in the pure Brun argument. -/
def fullReciprocalExpansion (A : Finset ℕ) : ℝ :=
  ∑ S ∈ A.powerset,
    (-1 : ℝ) ^ S.card * (subsetProduct S : ℝ)⁻¹

lemma periodicDensity_eq_fullReciprocalExpansion (A : Finset ℕ) :
    periodicDensity A = fullReciprocalExpansion A := by
  unfold periodicDensity fullReciprocalExpansion
  simpa [inv_cast_subsetProduct] using
    (Finset.prod_sub (fun _a : ℕ => (1 : ℝ))
      (fun a : ℕ => (a : ℝ)⁻¹) A)

lemma fullReciprocalExpansion_eq_sum_depth (A : Finset ℕ) :
    fullReciprocalExpansion A =
      ∑ j ∈ Finset.range (A.card + 1),
        (-1 : ℝ) ^ j * elementaryReciprocalMass A j := by
  rw [fullReciprocalExpansion, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  rw [elementaryReciprocalMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_powersetCard.mp hS).2, inv_cast_subsetProduct]

/-- The product of a `j`-element subfamily is at most the `j`-th power of
a common upper bound for its members. -/
lemma subsetProduct_le_pow {A S : Finset ℕ} {z : ℕ}
    (hSA : S ⊆ A) (hz : ∀ a ∈ A, a ≤ z) :
    subsetProduct S ≤ z ^ S.card := by
  rw [subsetProduct]
  calc
    (∏ a ∈ S, a) ≤ ∏ _a ∈ S, z := by
      apply Finset.prod_le_prod
      · intro a _ha
        exact Nat.zero_le a
      intro a ha
      exact hz a (hSA ha)
    _ = z ^ S.card := by simp

/-- If every product at depth `j` fits below the endpoint, the cutoff
elementary mass is the complete elementary symmetric mass. -/
lemma cutoffElementaryReciprocalMass_eq
    {N z j : ℕ} {A : Finset ℕ}
    (hz : ∀ a ∈ A, a ≤ z) (hpow : z ^ j ≤ N) :
    cutoffElementaryReciprocalMass N A j =
      elementaryReciprocalMass A j := by
  unfold cutoffElementaryReciprocalMass elementaryReciprocalMass
  have hfilter :
      (A.powersetCard j).filter (fun S => subsetProduct S ≤ N) =
        A.powersetCard j := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    have hdata := Finset.mem_powersetCard.mp hS
    exact (subsetProduct_le_pow hdata.1 hz).trans
      (by simpa [hdata.2] using hpow)
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro S _hS
  exact inv_cast_subsetProduct S

lemma truncatedSieveApprox_eq_sum_depth
    {N z r : ℕ} {A : Finset ℕ}
    (hzpos : 0 < z) (hz : ∀ a ∈ A, a ≤ z) (hpow : z ^ r ≤ N) :
    truncatedSieveApprox N A r =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℝ) ^ j * elementaryReciprocalMass A j := by
  unfold truncatedSieveApprox
  apply Finset.sum_congr rfl
  intro j hj
  rw [cutoffElementaryReciprocalMass_eq hz]
  have hjr : j ≤ r := by simpa using hj
  exact (Nat.pow_le_pow_right hzpos hjr).trans hpow

/-- The exponential-series majorant for all reciprocal layers deeper than
`r`.  It is written as a shifted series so that convergence to zero is
available directly from `tendsto_sum_nat_add`. -/
def factorialTail (C : ℝ) (r : ℕ) : ℝ :=
  ∑' k : ℕ, C ^ (k + (r + 1)) / (k + (r + 1)).factorial

lemma factorialTail_nonneg {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    0 ≤ factorialTail C r := by
  unfold factorialTail
  exact tsum_nonneg fun k => by positivity

lemma tendsto_factorialTail (C : ℝ) :
    Tendsto (factorialTail C) atTop (nhds 0) := by
  have h := tendsto_sum_nat_add
    (fun n : ℕ => C ^ n / n.factorial)
  have hadd : Tendsto (fun r : ℕ => r + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  exact h.comp hadd

lemma exists_factorialTail_lt {C ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, factorialTail C r < ε := by
  have h := (tendsto_factorialTail C).eventually
    (Iio_mem_nhds hε)
  exact h.exists

lemma factorialLayer_le_factorialTail {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    C ^ (r + 1) / (r + 1).factorial ≤ factorialTail C r := by
  have hs : Summable (fun k : ℕ =>
      C ^ (k + (r + 1)) / (k + (r + 1)).factorial) := by
    have hbase := Real.summable_pow_div_factorial C
    have hshift := (summable_nat_add_iff (r + 1)).2 hbase
    simpa only [Nat.add_comm] using hshift
  have hle := hs.le_tsum 0 (fun j hj => by positivity)
  simpa [factorialTail] using hle

lemma elementaryReciprocalMass_nonneg (A : Finset ℕ) (j : ℕ) :
    0 ≤ elementaryReciprocalMass A j := by
  unfold elementaryReciprocalMass
  positivity

/-- Tao's pure Brun lemma: once all products through depth `r` fit below
the endpoint, the truncated reciprocal sieve differs from the complete
Euler product by at most the factorial tail. -/
lemma pureBrunApproximation
    {C : ℝ} {N z r : ℕ} {A : Finset ℕ}
    (hC : 0 ≤ C) (hmass : reciprocalMass A ≤ C)
    (hzpos : 0 < z) (hz : ∀ a ∈ A, a ≤ z) (hpow : z ^ r ≤ N) :
    |truncatedSieveApprox N A r - periodicDensity A| ≤
      factorialTail C r := by
  rw [truncatedSieveApprox_eq_sum_depth hzpos hz hpow,
    periodicDensity_eq_fullReciprocalExpansion,
    fullReciprocalExpansion_eq_sum_depth]
  let f : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ j * elementaryReciprocalMass A j
  let b : ℕ → ℝ := fun j => C ^ j / j.factorial
  change |(∑ j ∈ Finset.range (r + 1), f j) -
    ∑ j ∈ Finset.range (A.card + 1), f j| ≤ factorialTail C r
  have hbSummable : Summable (fun k : ℕ => b ((r + 1) + k)) := by
    have hs : Summable (fun n : ℕ => C ^ n / n.factorial) :=
      Real.summable_pow_div_factorial C
    have hsShift : Summable (fun k : ℕ =>
        C ^ (k + (r + 1)) / (k + (r + 1)).factorial) :=
      (summable_nat_add_iff (r + 1)).2 hs
    simpa only [b, Nat.add_comm] using hsShift
  by_cases hrcard : r < A.card
  · have hle : r + 1 ≤ A.card + 1 := Nat.succ_le_succ hrcard.le
    have hsplit := Finset.sum_range_add_sum_Ico f hle
    have heq :
        (∑ j ∈ Finset.range (r + 1), f j) -
            ∑ j ∈ Finset.range (A.card + 1), f j =
          -(∑ j ∈ Finset.Ico (r + 1) (A.card + 1), f j) := by
      rw [← hsplit]
      ring
    rw [heq, abs_neg]
    calc
      |∑ j ∈ Finset.Ico (r + 1) (A.card + 1), f j| ≤
          ∑ j ∈ Finset.Ico (r + 1) (A.card + 1), |f j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.Ico (r + 1) (A.card + 1),
          elementaryReciprocalMass A j := by
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp only [f]
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (elementaryReciprocalMass_nonneg A j)]
      _ ≤ ∑ j ∈ Finset.Ico (r + 1) (A.card + 1), b j := by
        apply Finset.sum_le_sum
        intro j _hj
        dsimp only [b]
        exact (elementaryReciprocalMass_le A j).trans
          (div_le_div_of_nonneg_right
            (pow_le_pow_left₀ (reciprocalMass_nonneg A) hmass j)
            (by positivity))
      _ = ∑ k ∈ Finset.range ((A.card + 1) - (r + 1)),
          b ((r + 1) + k) :=
        Finset.sum_Ico_eq_sum_range b (r + 1) (A.card + 1)
      _ ≤ ∑' k : ℕ, b ((r + 1) + k) := by
        apply Summable.sum_le_tsum
        · intro k _hk
          dsimp only [b]
          positivity
        · exact hbSummable
      _ = factorialTail C r := by
        unfold factorialTail
        apply tsum_congr
        intro k
        dsimp only [b]
        rw [Nat.add_comm]
  · have hcardr : A.card ≤ r := Nat.le_of_not_gt hrcard
    have hle : A.card + 1 ≤ r + 1 := Nat.succ_le_succ hcardr
    have hsplit := Finset.sum_range_add_sum_Ico f hle
    have hzero :
        ∑ j ∈ Finset.Ico (A.card + 1) (r + 1), f j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjcard : A.card < j := (Finset.mem_Ico.mp hj).1
      have hpowers : A.powersetCard j = ∅ :=
        Finset.powersetCard_eq_empty.mpr hjcard
      dsimp only [f]
      rw [elementaryReciprocalMass, hpowers]
      simp
    have heq :
        (∑ j ∈ Finset.range (r + 1), f j) =
          ∑ j ∈ Finset.range (A.card + 1), f j := by
      rw [← hsplit, hzero, add_zero]
    rw [heq, sub_self, abs_zero]
    exact factorialTail_nonneg hC r

/-! ## Tao's splitting lemma -/

def separateCutoffPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  cutoffSubsets N A₁ r ×ˢ cutoffSubsets N A₂ r

def jointCutoffPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (separateCutoffPairs N A₁ A₂ r).filter fun ST =>
    (ST.1 ∪ ST.2).card ≤ r ∧ subsetProduct (ST.1 ∪ ST.2) ≤ N

def splitDefectPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  separateCutoffPairs N A₁ A₂ r \ jointCutoffPairs N A₁ A₂ r

@[simp] lemma mem_cutoffSubsets {N r : ℕ} {A S : Finset ℕ} :
    S ∈ cutoffSubsets N A r ↔
      S ⊆ A ∧ S.card ≤ r ∧ subsetProduct S ≤ N := by
  simp [cutoffSubsets, and_assoc]

lemma subsetProduct_mono_union_left {S T : Finset ℕ}
    (hdisj : Disjoint S T) (hpos : ∀ a ∈ S ∪ T, 0 < a) :
    subsetProduct S ≤ subsetProduct (S ∪ T) := by
  rw [subsetProduct_union hdisj]
  have hS : 0 < subsetProduct S := subsetProduct_pos
    Finset.subset_union_left hpos
  have hT : 0 < subsetProduct T := subsetProduct_pos
    Finset.subset_union_right hpos
  nlinarith

lemma jointCutoffPairs_sum_eq_union
    {N r : ℕ} {A₁ A₂ : Finset ℕ}
    (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a) :
    (∑ ST ∈ jointCutoffPairs N A₁ A₂ r,
      reciprocalSubsetTerm (ST.1 ∪ ST.2)) =
      truncatedSieveApprox N (A₁ ∪ A₂) r := by
  rw [truncatedSieveApprox_eq_sum_cutoffSubsets]
  symm
  apply Finset.sum_bij'
    (fun S _hS => (S ∩ A₁, S ∩ A₂))
    (fun ST _hST => ST.1 ∪ ST.2)
  · intro S hS
    have hS' := mem_cutoffSubsets.mp hS
    have hparts : (S ∩ A₁) ∪ (S ∩ A₂) = S := by
      ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨haS, _⟩ | ⟨haS, _⟩) <;> exact haS
      · intro haS
        rcases Finset.mem_union.mp (hS'.1 haS) with ha1 | ha2
        · exact Or.inl ⟨haS, ha1⟩
        · exact Or.inr ⟨haS, ha2⟩
    have hpartDisj : Disjoint (S ∩ A₁) (S ∩ A₂) :=
      hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hposParts : ∀ a ∈ (S ∩ A₁) ∪ (S ∩ A₂), 0 < a := by
      intro a ha
      rw [hparts] at ha
      exact hpos a (hS'.1 ha)
    have hcard1 : (S ∩ A₁).card ≤ r :=
      (Finset.card_le_card Finset.inter_subset_left).trans hS'.2.1
    have hcard2 : (S ∩ A₂).card ≤ r :=
      (Finset.card_le_card Finset.inter_subset_left).trans hS'.2.1
    have hprod1 : subsetProduct (S ∩ A₁) ≤ N := by
      have hp := subsetProduct_mono_union_left hpartDisj hposParts
      rw [hparts] at hp
      exact hp.trans hS'.2.2
    have hprod2 : subsetProduct (S ∩ A₂) ≤ N := by
      have hp := subsetProduct_mono_union_left hpartDisj.symm (by
        intro a ha
        apply hposParts a
        simpa [Finset.union_comm] using ha)
      rw [Finset.union_comm, hparts] at hp
      exact hp.trans hS'.2.2
    rw [jointCutoffPairs]
    simp only [Finset.mem_filter, separateCutoffPairs,
      Finset.mem_product]
    refine ⟨⟨mem_cutoffSubsets.mpr
      ⟨Finset.inter_subset_right, hcard1, hprod1⟩,
      mem_cutoffSubsets.mpr
      ⟨Finset.inter_subset_right, hcard2, hprod2⟩⟩, ?_⟩
    rw [hparts]
    exact hS'.2
  · intro ST hST
    have hST' := Finset.mem_filter.mp hST
    have hmem := Finset.mem_product.mp hST'.1
    have h1 := (mem_cutoffSubsets.mp hmem.1).1
    have h2 := (mem_cutoffSubsets.mp hmem.2).1
    exact mem_cutoffSubsets.mpr
      ⟨Finset.union_subset (h1.trans Finset.subset_union_left)
        (h2.trans Finset.subset_union_right), hST'.2⟩
  · intro S hS
    have hS' := mem_cutoffSubsets.mp hS
    ext a
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨haS, _⟩ | ⟨haS, _⟩) <;> exact haS
    · intro haS
      rcases Finset.mem_union.mp (hS'.1 haS) with ha1 | ha2
      · exact Or.inl ⟨haS, ha1⟩
      · exact Or.inr ⟨haS, ha2⟩
  · intro ST hST
    have hST' := Finset.mem_filter.mp hST
    have hmem := Finset.mem_product.mp hST'.1
    have h1 := (mem_cutoffSubsets.mp hmem.1).1
    have h2 := (mem_cutoffSubsets.mp hmem.2).1
    apply Prod.ext
    · ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨ha1 | ha2, haA1⟩
        · exact ha1
        · exact False.elim
            ((Finset.disjoint_left.mp hdisj) haA1 (h2 ha2))
      · intro ha1
        exact ⟨Or.inl ha1, h1 ha1⟩
    · ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨ha1 | ha2, haA2⟩
        · exact False.elim
            ((Finset.disjoint_left.mp hdisj) (h1 ha1) haA2)
        · exact ha2
      · intro ha2
        exact ⟨Or.inr ha2, h2 ha2⟩
  · intro S hS
    have hS' := mem_cutoffSubsets.mp hS
    apply congrArg reciprocalSubsetTerm
    ext a
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro haS
      rcases Finset.mem_union.mp (hS'.1 haS) with ha1 | ha2
      · exact Or.inl ⟨haS, ha1⟩
      · exact Or.inr ⟨haS, ha2⟩
    · rintro (⟨haS, _⟩ | ⟨haS, _⟩) <;> exact haS

lemma mul_truncatedSieveApprox_eq_sum_separateCutoffPairs
    {N r : ℕ} {A₁ A₂ : Finset ℕ} (hdisj : Disjoint A₁ A₂) :
    truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r =
      ∑ ST ∈ separateCutoffPairs N A₁ A₂ r,
        reciprocalSubsetTerm (ST.1 ∪ ST.2) := by
  rw [truncatedSieveApprox_eq_sum_cutoffSubsets,
    truncatedSieveApprox_eq_sum_cutoffSubsets,
    separateCutoffPairs, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [reciprocalSubsetTerm_union]
  exact hdisj.mono
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)

lemma sum_separate_eq_joint_add_defect
    (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    (∑ ST ∈ separateCutoffPairs N A₁ A₂ r,
        reciprocalSubsetTerm (ST.1 ∪ ST.2)) =
      (∑ ST ∈ jointCutoffPairs N A₁ A₂ r,
        reciprocalSubsetTerm (ST.1 ∪ ST.2)) +
      ∑ ST ∈ splitDefectPairs N A₁ A₂ r,
        reciprocalSubsetTerm (ST.1 ∪ ST.2) := by
  have hsub : jointCutoffPairs N A₁ A₂ r ⊆
      separateCutoffPairs N A₁ A₂ r := Finset.filter_subset _ _
  have hsum := Finset.sum_sdiff hsub
    (f := fun ST : Finset ℕ × Finset ℕ =>
      reciprocalSubsetTerm (ST.1 ∪ ST.2))
  rw [splitDefectPairs]
  linarith

def splitDefectMass (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ ST ∈ splitDefectPairs N A₁ A₂ r,
    (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹

lemma abs_reciprocalSubsetTerm {A S : Finset ℕ}
    (hSA : S ⊆ A) (hpos : ∀ a ∈ A, 0 < a) :
    |reciprocalSubsetTerm S| = (subsetProduct S : ℝ)⁻¹ := by
  rw [reciprocalSubsetTerm, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_pos]
  exact inv_pos.mpr (by exact_mod_cast subsetProduct_pos hSA hpos)

lemma splittingError_le_defectMass
    {N r : ℕ} {A₁ A₂ : Finset ℕ}
    (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a) :
    |truncatedSieveApprox N (A₁ ∪ A₂) r -
        truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| ≤
      splitDefectMass N A₁ A₂ r := by
  have hmul := mul_truncatedSieveApprox_eq_sum_separateCutoffPairs
    (N := N) (r := r) hdisj
  have hsplit := sum_separate_eq_joint_add_defect N A₁ A₂ r
  have hjoint := jointCutoffPairs_sum_eq_union
    (N := N) (r := r) hdisj hpos
  rw [hjoint] at hsplit
  have heq :
      truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r =
        -(∑ ST ∈ splitDefectPairs N A₁ A₂ r,
          reciprocalSubsetTerm (ST.1 ∪ ST.2)) := by
    rw [hmul, hsplit]
    ring
  rw [heq, abs_neg, splitDefectMass]
  calc
    |∑ ST ∈ splitDefectPairs N A₁ A₂ r,
        reciprocalSubsetTerm (ST.1 ∪ ST.2)| ≤
      ∑ ST ∈ splitDefectPairs N A₁ A₂ r,
        |reciprocalSubsetTerm (ST.1 ∪ ST.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ST ∈ splitDefectPairs N A₁ A₂ r,
        (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro ST hST
      have hsep := (Finset.mem_sdiff.mp hST).1
      rw [separateCutoffPairs] at hsep
      have hmem := Finset.mem_product.mp hsep
      have h1 := (mem_cutoffSubsets.mp hmem.1).1
      have h2 := (mem_cutoffSubsets.mp hmem.2).1
      have hsub : ST.1 ∪ ST.2 ⊆ A₁ ∪ A₂ :=
        Finset.union_subset (h1.trans Finset.subset_union_left)
          (h2.trans Finset.subset_union_right)
      rw [abs_reciprocalSubsetTerm hsub hpos]

def highDegreeSplitPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (separateCutoffPairs N A₁ A₂ r).filter fun ST =>
    r < (ST.1 ∪ ST.2).card

def crossCutoffSplitPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (separateCutoffPairs N A₁ A₂ r).filter fun ST =>
    (ST.1 ∪ ST.2).card ≤ r ∧ N < subsetProduct (ST.1 ∪ ST.2)

lemma splitDefectPairs_eq_union (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    splitDefectPairs N A₁ A₂ r =
      highDegreeSplitPairs N A₁ A₂ r ∪
        crossCutoffSplitPairs N A₁ A₂ r := by
  ext ST
  simp only [splitDefectPairs, jointCutoffPairs, highDegreeSplitPairs,
    crossCutoffSplitPairs, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · rintro ⟨hsep, hnot⟩
    by_cases hcard : (ST.1 ∪ ST.2).card ≤ r
    · right
      refine ⟨hsep, hcard, ?_⟩
      have : ¬ subsetProduct (ST.1 ∪ ST.2) ≤ N := by
        intro hp
        exact hnot ⟨hsep, hcard, hp⟩
      omega
    · left
      exact ⟨hsep, by omega⟩
  · rintro (⟨hsep, hcard⟩ | ⟨hsep, hcard, hprod⟩)
    · refine ⟨hsep, ?_⟩
      rintro ⟨_hsep, hle, _hprod⟩
      omega
    · refine ⟨hsep, ?_⟩
      rintro ⟨_hsep, _hle, hleprod⟩
      omega

lemma disjoint_highDegree_crossCutoff
    (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Disjoint (highDegreeSplitPairs N A₁ A₂ r)
      (crossCutoffSplitPairs N A₁ A₂ r) := by
  rw [Finset.disjoint_left]
  intro ST hhigh hcross
  have hh := (Finset.mem_filter.mp hhigh).2
  have hc := (Finset.mem_filter.mp hcross).2.1
  omega

def highCardSubsets (A : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun S => r < S.card

lemma sum_highCardSubsets_eq
    (A : Finset ℕ) (r : ℕ) :
    (∑ S ∈ highCardSubsets A r, (subsetProduct S : ℝ)⁻¹) =
      ∑ j ∈ Finset.Ico (r + 1) (A.card + 1),
        elementaryReciprocalMass A j := by
  rw [highCardSubsets, Finset.sum_filter, Finset.sum_powerset]
  have hIco : Finset.Ico (r + 1) (A.card + 1) =
      (Finset.range (A.card + 1)).filter (fun j => r < j) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  rw [hIco, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [elementaryReciprocalMass]
  by_cases hrj : r < j
  · rw [if_pos (by omega)]
    apply Finset.sum_congr rfl
    intro S hS
    have hcard := (Finset.mem_powersetCard.mp hS).2
    rw [hcard, if_pos hrj, inv_cast_subsetProduct]
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro S hS
    have hcard := (Finset.mem_powersetCard.mp hS).2
    rw [hcard]
    simp [hrj]

lemma sum_highCardSubsets_le_factorialTail
    {C : ℝ} (hC : 0 ≤ C) (A : Finset ℕ)
    (hmass : reciprocalMass A ≤ C) (r : ℕ) :
    (∑ S ∈ highCardSubsets A r, (subsetProduct S : ℝ)⁻¹) ≤
      factorialTail C r := by
  rw [sum_highCardSubsets_eq]
  rw [Finset.sum_Ico_eq_sum_range]
  let b : ℕ → ℝ := fun j => C ^ j / j.factorial
  calc
    (∑ k ∈ Finset.range ((A.card + 1) - (r + 1)),
        elementaryReciprocalMass A ((r + 1) + k)) ≤
      ∑ k ∈ Finset.range ((A.card + 1) - (r + 1)),
        b ((r + 1) + k) := by
      apply Finset.sum_le_sum
      intro k _hk
      dsimp only [b]
      exact (elementaryReciprocalMass_le A ((r + 1) + k)).trans
        (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (reciprocalMass_nonneg A) hmass _)
          (by positivity))
    _ ≤ ∑' k : ℕ, b ((r + 1) + k) := by
      apply Summable.sum_le_tsum
      · intro k _hk
        dsimp only [b]
        positivity
      · have hs : Summable (fun n : ℕ => C ^ n / n.factorial) :=
          Real.summable_pow_div_factorial C
        have hsShift : Summable (fun k : ℕ =>
            C ^ (k + (r + 1)) / (k + (r + 1)).factorial) :=
          (summable_nat_add_iff (r + 1)).2 hs
        simpa only [b, Nat.add_comm] using hsShift
    _ = factorialTail C r := by
      unfold factorialTail
      apply tsum_congr
      intro k
      dsimp only [b]
      rw [Nat.add_comm]

lemma unionMap_injectiveOn
    {A₁ A₂ : Finset ℕ} (hdisj : Disjoint A₁ A₂) :
    Set.InjOn (fun ST : Finset ℕ × Finset ℕ => ST.1 ∪ ST.2)
      (↑(A₁.powerset ×ˢ A₂.powerset) :
        Set (Finset ℕ × Finset ℕ)) := by
  intro ST hST UV hUV heq
  have hSTm := Finset.mem_product.mp hST
  have hUVm := Finset.mem_product.mp hUV
  have hST1 := Finset.mem_powerset.mp hSTm.1
  have hST2 := Finset.mem_powerset.mp hSTm.2
  have hUV1 := Finset.mem_powerset.mp hUVm.1
  have hUV2 := Finset.mem_powerset.mp hUVm.2
  change ST.1 ∪ ST.2 = UV.1 ∪ UV.2 at heq
  apply Prod.ext
  · ext a
    constructor
    · intro ha
      have hau : a ∈ ST.1 ∪ ST.2 := Finset.mem_union_left _ ha
      rw [heq] at hau
      rcases Finset.mem_union.mp hau with ha1 | ha2
      · exact ha1
      · exact False.elim
          ((Finset.disjoint_left.mp hdisj) (hST1 ha) (hUV2 ha2))
    · intro ha
      have hau : a ∈ UV.1 ∪ UV.2 := Finset.mem_union_left _ ha
      rw [← heq] at hau
      rcases Finset.mem_union.mp hau with ha1 | ha2
      · exact ha1
      · exact False.elim
          ((Finset.disjoint_left.mp hdisj) (hUV1 ha) (hST2 ha2))
  · ext a
    constructor
    · intro ha
      have hau : a ∈ ST.1 ∪ ST.2 := Finset.mem_union_right _ ha
      rw [heq] at hau
      rcases Finset.mem_union.mp hau with ha1 | ha2
      · exact False.elim
          ((Finset.disjoint_left.mp hdisj) (hUV1 ha1) (hST2 ha))
      · exact ha2
    · intro ha
      have hau : a ∈ UV.1 ∪ UV.2 := Finset.mem_union_right _ ha
      rw [← heq] at hau
      rcases Finset.mem_union.mp hau with ha1 | ha2
      · exact False.elim
          ((Finset.disjoint_left.mp hdisj) (hST1 ha1) (hUV2 ha))
      · exact ha2

lemma highDegreeSplitMass_le_factorialTail
    {C : ℝ} {N r : ℕ} {A₁ A₂ : Finset ℕ}
    (hC : 0 ≤ C) (hdisj : Disjoint A₁ A₂)
    (hmass : reciprocalMass (A₁ ∪ A₂) ≤ C) :
    (∑ ST ∈ highDegreeSplitPairs N A₁ A₂ r,
      (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹) ≤
      factorialTail C r := by
  let U : Finset (Finset ℕ) :=
    (highDegreeSplitPairs N A₁ A₂ r).image
      (fun ST => ST.1 ∪ ST.2)
  have hinj : Set.InjOn
      (fun ST : Finset ℕ × Finset ℕ => ST.1 ∪ ST.2)
      (highDegreeSplitPairs N A₁ A₂ r : Set (Finset ℕ × Finset ℕ)) := by
    apply (unionMap_injectiveOn hdisj).mono
    intro ST hST
    have hsep := (Finset.mem_filter.mp hST).1
    rw [separateCutoffPairs] at hsep
    have hm := Finset.mem_product.mp hsep
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr (mem_cutoffSubsets.mp hm.1).1,
       Finset.mem_powerset.mpr (mem_cutoffSubsets.mp hm.2).1⟩
  have hsumImage :
      (∑ S ∈ U, (subsetProduct S : ℝ)⁻¹) =
        ∑ ST ∈ highDegreeSplitPairs N A₁ A₂ r,
          (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ := by
    exact Finset.sum_image hinj
  rw [← hsumImage]
  have hUsub : U ⊆ highCardSubsets (A₁ ∪ A₂) r := by
    intro S hS
    obtain ⟨ST, hST, rfl⟩ := Finset.mem_image.mp hS
    have hdata := Finset.mem_filter.mp hST
    have hsep := hdata.1
    rw [separateCutoffPairs] at hsep
    have hm := Finset.mem_product.mp hsep
    have h1 := (mem_cutoffSubsets.mp hm.1).1
    have h2 := (mem_cutoffSubsets.mp hm.2).1
    simp only [highCardSubsets, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.union_subset
      (h1.trans Finset.subset_union_left)
      (h2.trans Finset.subset_union_right), hdata.2⟩
  calc
    (∑ S ∈ U, (subsetProduct S : ℝ)⁻¹) ≤
        ∑ S ∈ highCardSubsets (A₁ ∪ A₂) r,
          (subsetProduct S : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hUsub
        (fun _S _hlarge _hnot => by positivity)
    _ ≤ factorialTail C r :=
      sum_highCardSubsets_le_factorialTail hC _ hmass r

def splitPrimeWindow (y K : ℕ) : Finset ℕ :=
  (Finset.Ioc y (K * (y + 1))).filter Nat.Prime

@[simp] lemma mem_splitPrimeWindow {y K p : ℕ} :
    p ∈ splitPrimeWindow y K ↔
      y < p ∧ p ≤ K * (y + 1) ∧ p.Prime := by
  simp [splitPrimeWindow, and_assoc]

lemma splitPrimeWindow_self_subset_primesLE (y K : ℕ) :
    splitPrimeWindow y K ⊆ Nat.primesLE (K * (y + 1)) := by
  intro p hp
  exact Nat.mem_primesLE.mpr
    ⟨(mem_splitPrimeWindow.mp hp).2.1,
      (mem_splitPrimeWindow.mp hp).2.2⟩

lemma reciprocalMass_splitPrimeWindow_le
    {y K : ℕ} (hy : 0 < y) :
    reciprocalMass (splitPrimeWindow y K) ≤
      (Nat.primeCounting (K * (y + 1)) : ℝ) / (y : ℝ) := by
  rw [reciprocalMass]
  calc
    (∑ p ∈ splitPrimeWindow y K, (p : ℝ)⁻¹) ≤
        ∑ _p ∈ splitPrimeWindow y K, (y : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ (by exact_mod_cast hy) (by
        exact_mod_cast (mem_splitPrimeWindow.mp hp).1.le)
    _ = ((splitPrimeWindow y K).card : ℝ) / (y : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (Nat.primeCounting (K * (y + 1)) : ℝ) / (y : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hc := Finset.card_le_card
        (splitPrimeWindow_self_subset_primesLE y K)
      rw [Nat.primesLE_card_eq_primeCounting] at hc
      exact_mod_cast hc

theorem eventually_splitPrimeWindowMass_lt
    {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∀ᶠ y : ℕ in atTop,
      reciprocalMass (splitPrimeWindow y K) < ε := by
  by_cases hK : K = 0
  · subst K
    filter_upwards [] with y
    simpa [splitPrimeWindow, reciprocalMass] using hε
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    let δ := ε / (4 * (K : ℝ))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hpnt := eventually_primeCounting_le_delta_mul hδ
    rw [eventually_atTop] at hpnt
    obtain ⟨T, hT⟩ := hpnt
    obtain ⟨t, ht⟩ := exists_nat_ge T
    filter_upwards [eventually_ge_atTop (max t 1)] with y hy
    have hy1 : 1 ≤ y := (le_max_right t 1).trans hy
    have hypos : 0 < y := zero_lt_one.trans_le hy1
    have hty : (t : ℝ) ≤ (K * (y + 1) : ℕ) := by
      have htyNat : t ≤ K * (y + 1) := by
        have hty' : t ≤ y := (le_max_left t 1).trans hy
        calc
          t ≤ y := hty'
          _ ≤ y + 1 := Nat.le_succ y
          _ ≤ K * (y + 1) := by
            nlinarith
      exact_mod_cast htyNat
    have hpi : (Nat.primeCounting (K * (y + 1)) : ℝ) ≤
        δ * (K * (y + 1) : ℕ) := by
      simpa only [Nat.floor_natCast] using
        hT (K * (y + 1) : ℕ) (ht.trans hty)
    have hmass := reciprocalMass_splitPrimeWindow_le
      (K := K) hypos
    have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
    have hratio : ((K * (y + 1) : ℕ) : ℝ) / (y : ℝ) ≤
        2 * (K : ℝ) := by
      push_cast
      have : (y : ℝ) + 1 ≤ 2 * y := by
        exact_mod_cast (show y + 1 ≤ 2 * y by omega)
      calc
        (K : ℝ) * ((y : ℝ) + 1) / y ≤
            (K : ℝ) * (2 * y) / y := by gcongr
        _ = 2 * (K : ℝ) := by field_simp [hyR.ne']
    calc
      reciprocalMass (splitPrimeWindow y K) ≤
          (Nat.primeCounting (K * (y + 1)) : ℝ) / (y : ℝ) := hmass
      _ ≤ (δ * (K * (y + 1) : ℕ)) / (y : ℝ) := by
        exact div_le_div_of_nonneg_right hpi (by positivity)
      _ = δ * (((K * (y + 1) : ℕ) : ℝ) / (y : ℝ)) := by ring
      _ ≤ δ * (2 * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio hδ.le
      _ = ε / 2 := by
        dsimp only [δ]
        field_simp [show (K : ℝ) ≠ 0 by exact_mod_cast hK]
        ring
      _ < ε := half_lt_self hε


def splitAllSubsetMass (A : Finset ℕ) : ℝ :=
  ∑ S ∈ A.powerset, (subsetProduct S : ℝ)⁻¹

lemma splitAllSubsetMass_le_exp (A : Finset ℕ) :
    splitAllSubsetMass A ≤ Real.exp (reciprocalMass A) := by
  have heq : splitAllSubsetMass A =
      ∏ a ∈ A, (1 + (a : ℝ)⁻¹) := by
    unfold splitAllSubsetMass
    simpa [inv_cast_subsetProduct, add_comm] using
      (Finset.prod_add (fun a : ℕ => (a : ℝ)⁻¹)
        (fun _a : ℕ => (1 : ℝ)) A).symm
  rw [heq, reciprocalMass]
  rw [show Real.exp (∑ a ∈ A, (a : ℝ)⁻¹) =
      ∏ a ∈ A, Real.exp ((a : ℝ)⁻¹) by
    exact Real.exp_sum A (fun a : ℕ => (a : ℝ)⁻¹)]
  apply Finset.prod_le_prod
  · intro a ha
    positivity
  intro a ha
  simpa [add_comm] using Real.add_one_le_exp ((a : ℝ)⁻¹)

def crossWitnessPairs (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset ((Finset ℕ × Finset ℕ) × ℕ) :=
  (crossCutoffSplitPairs N A₁ A₂ r ×ˢ A₂).filter fun W =>
    W.2 ∈ W.1.2

def crossWitnessMap
    (W : (Finset ℕ × Finset ℕ) × ℕ) :
    (Finset ℕ × Finset ℕ) × ℕ :=
  ((W.1.1, W.1.2.erase W.2), W.2)

lemma cross_second_nonempty
    {N r : ℕ} {A₁ A₂ : Finset ℕ}
    {ST : Finset ℕ × Finset ℕ}
    (hST : ST ∈ crossCutoffSplitPairs N A₁ A₂ r) :
    ST.2.Nonempty := by
  have hdata := Finset.mem_filter.mp hST
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hdata
  simp only [Finset.union_empty] at hdata
  have hsep := hdata.1
  rw [separateCutoffPairs] at hsep
  have hm := Finset.mem_product.mp hsep
  have hprod := (mem_cutoffSubsets.mp hm.1).2.2
  omega

lemma crossMass_le_witnessSum
    {N r : ℕ} {A₁ A₂ : Finset ℕ} :
    (∑ ST ∈ crossCutoffSplitPairs N A₁ A₂ r,
      (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹) ≤
      ∑ W ∈ crossWitnessPairs N A₁ A₂ r,
        (subsetProduct (W.1.1 ∪ W.1.2) : ℝ)⁻¹ := by
  rw [crossWitnessPairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_le_sum
  intro ST hST
  have hnonempty := cross_second_nonempty hST
  have hsubA₂ : ST.2 ⊆ A₂ := by
    have hsep := (Finset.mem_filter.mp hST).1
    rw [separateCutoffPairs] at hsep
    exact (mem_cutoffSubsets.mp (Finset.mem_product.mp hsep).2).1
  calc
    (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ ≤
        ∑ _q ∈ ST.2,
          (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (1 : ℝ) ≤ ST.2.card := by
        exact_mod_cast hnonempty.card_pos
      have hmul := mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ by positivity)
      simpa using hmul
    _ ≤ ∑ q ∈ A₂,
        if q ∈ ST.2 then
          (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹ else 0 := by
      rw [← Finset.sum_filter]
      have hsub : ST.2 ⊆ A₂.filter (fun q => q ∈ ST.2) := by
        intro q hq
        exact Finset.mem_filter.mpr ⟨hsubA₂ hq, hq⟩
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _q _hA _hnot => by positivity)

lemma crossWitnessMap_injective
    {N r : ℕ} {A₁ A₂ : Finset ℕ} :
    Set.InjOn crossWitnessMap
      (crossWitnessPairs N A₁ A₂ r :
        Set ((Finset ℕ × Finset ℕ) × ℕ)) := by
  intro W hW V hV heq
  have hqW := (Finset.mem_filter.mp hW).2
  have hqV := (Finset.mem_filter.mp hV).2
  change ((W.1.1, W.1.2.erase W.2), W.2) =
    ((V.1.1, V.1.2.erase V.2), V.2) at heq
  injection heq with hpairs hq
  injection hpairs with hS₁ hR
  apply Prod.ext
  · apply Prod.ext hS₁
    rw [← Finset.insert_erase hqW, ← Finset.insert_erase hqV]
    have hR' : W.1.2.erase V.2 = V.1.2.erase V.2 := by
      simpa only [hq] using hR
    rw [hq, hR']
  · exact hq

lemma crossWitness_weight
    {N r : ℕ} {A₁ A₂ : Finset ℕ}
    (hdisj : Disjoint A₁ A₂)
    {W : (Finset ℕ × Finset ℕ) × ℕ}
    (hW : W ∈ crossWitnessPairs N A₁ A₂ r) :
    (subsetProduct (W.1.1 ∪ W.1.2) : ℝ)⁻¹ =
      (subsetProduct W.1.1 : ℝ)⁻¹ *
        (subsetProduct (W.1.2.erase W.2) : ℝ)⁻¹ *
          (W.2 : ℝ)⁻¹ := by
  have hdata := Finset.mem_filter.mp hW
  have hcross := (Finset.mem_product.mp hdata.1).1
  have hq := hdata.2
  have hsep := (Finset.mem_filter.mp hcross).1
  rw [separateCutoffPairs] at hsep
  have hm := Finset.mem_product.mp hsep
  have hS₁ := (mem_cutoffSubsets.mp hm.1).1
  have hS₂ := (mem_cutoffSubsets.mp hm.2).1
  have hSTdisj : Disjoint W.1.1 W.1.2 := hdisj.mono hS₁ hS₂
  have hprod₂ : subsetProduct W.1.2 =
      subsetProduct (W.1.2.erase W.2) * W.2 := by
    unfold subsetProduct
    exact (Finset.prod_erase_mul (s := W.1.2)
      (f := fun a : ℕ => a) hq).symm
  rw [subsetProduct_union hSTdisj, hprod₂, Nat.cast_mul,
    Nat.cast_mul, mul_inv_rev, mul_inv_rev]
  ring

def crossWitnessImage (N : ℕ) (A₁ A₂ : Finset ℕ) (r : ℕ) :
    Finset ((Finset ℕ × Finset ℕ) × ℕ) :=
  (crossWitnessPairs N A₁ A₂ r).image crossWitnessMap

lemma witnessSum_eq_imageSum
    {N r : ℕ} {A₁ A₂ : Finset ℕ}
    (hdisj : Disjoint A₁ A₂) :
    (∑ W ∈ crossWitnessPairs N A₁ A₂ r,
      (subsetProduct (W.1.1 ∪ W.1.2) : ℝ)⁻¹) =
      ∑ V ∈ crossWitnessImage N A₁ A₂ r,
        (subsetProduct V.1.1 : ℝ)⁻¹ *
          (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹ := by
  rw [crossWitnessImage, Finset.sum_image crossWitnessMap_injective]
  apply Finset.sum_congr rfl
  intro W hW
  exact crossWitness_weight hdisj hW

lemma crossWitnessMap_mem_window
    {N r z zplus Y : ℕ} {A₁ A₂ : Finset ℕ}
    (hz : 0 < z) (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hsmall : ∀ a ∈ A₁, a ≤ z)
    (hprime : ∀ q ∈ A₂, q.Prime)
    (hlarge : ∀ q ∈ A₂, zplus < q)
    (hscale : z ^ r * Y ≤ zplus)
    {W : (Finset ℕ × Finset ℕ) × ℕ}
    (hW : W ∈ crossWitnessPairs N A₁ A₂ r) :
    let V := crossWitnessMap W
    let y := N / (subsetProduct V.1.1 * subsetProduct V.1.2)
    Y ≤ y ∧ V.2 ∈ splitPrimeWindow y (z ^ r) ∧
      V.1.1 ⊆ A₁ ∧ V.1.2 ⊆ A₂ := by
  dsimp only
  have hWdata := Finset.mem_filter.mp hW
  have hcross := (Finset.mem_product.mp hWdata.1).1
  have hqS₂ := hWdata.2
  have hcrossData := Finset.mem_filter.mp hcross
  have hsep := hcrossData.1
  rw [separateCutoffPairs] at hsep
  have hm := Finset.mem_product.mp hsep
  have hS₁data := mem_cutoffSubsets.mp hm.1
  have hS₂data := mem_cutoffSubsets.mp hm.2
  have hqA₂ : W.2 ∈ A₂ := hS₂data.1 hqS₂
  have hRsub : W.1.2.erase W.2 ⊆ A₂ :=
    (Finset.erase_subset _ _).trans hS₂data.1
  have hSdisj : Disjoint W.1.1 W.1.2 :=
    hdisj.mono hS₁data.1 hS₂data.1
  have hRdisj : Disjoint W.1.1 (W.1.2.erase W.2) :=
    hSdisj.mono Finset.Subset.rfl (Finset.erase_subset _ _)
  have hprod₂ : subsetProduct W.1.2 =
      subsetProduct (W.1.2.erase W.2) * W.2 := by
    unfold subsetProduct
    exact (Finset.prod_erase_mul (s := W.1.2)
      (f := fun a : ℕ => a) hqS₂).symm
  have hprodUnion : subsetProduct (W.1.1 ∪ W.1.2) =
      (subsetProduct W.1.1 * subsetProduct (W.1.2.erase W.2)) * W.2 := by
    rw [subsetProduct_union hSdisj, hprod₂]
    simp [mul_assoc]
  have hposS₁ : 0 < subsetProduct W.1.1 :=
    subsetProduct_pos hS₁data.1
      (fun a ha => hpos a (Finset.mem_union_left _ ha))
  have hposR : 0 < subsetProduct (W.1.2.erase W.2) :=
    subsetProduct_pos hRsub
      (fun a ha => hpos a (Finset.mem_union_right _ ha))
  have hdpos : 0 < subsetProduct W.1.1 *
      subsetProduct (W.1.2.erase W.2) := Nat.mul_pos hposS₁ hposR
  let y := N / (subsetProduct W.1.1 *
    subsetProduct (W.1.2.erase W.2))
  have hylq : y < W.2 := by
    change N / (subsetProduct W.1.1 *
      subsetProduct (W.1.2.erase W.2)) < W.2
    rw [Nat.div_lt_iff_lt_mul hdpos]
    have hcrossProd := hcrossData.2.2
    rw [hprodUnion] at hcrossProd
    nlinarith
  have hNnext : N < (y + 1) *
      (subsetProduct W.1.1 * subsetProduct (W.1.2.erase W.2)) := by
    exact (Nat.div_lt_iff_lt_mul hdpos).mp (Nat.lt_succ_self y)
  have hRqupper : subsetProduct (W.1.2.erase W.2) * W.2 ≤ N := by
    rw [← hprod₂]
    exact hS₂data.2.2
  have hcardS₁ : W.1.1.card ≤ r := by
    have hcardUnion := hcrossData.2.1
    exact (Finset.card_le_card Finset.subset_union_left).trans hcardUnion
  have hprodS₁K : subsetProduct W.1.1 ≤ z ^ r := by
    exact (subsetProduct_le_pow hS₁data.1 hsmall).trans
      (Nat.pow_le_pow_right hz hcardS₁)
  have hqupper : W.2 ≤ z ^ r * (y + 1) := by
    nlinarith
  have hYy : Y ≤ y := by
    by_contra hnot
    have hyY : y < Y := Nat.lt_of_not_ge hnot
    have hy1Y : y + 1 ≤ Y := by omega
    have hqz : W.2 ≤ z ^ r * Y :=
      hqupper.trans (Nat.mul_le_mul_left (z ^ r) hy1Y)
    exact (not_lt_of_ge (hqz.trans hscale)) (hlarge W.2 hqA₂)
  refine ⟨hYy, ?_, hS₁data.1, hRsub⟩
  exact mem_splitPrimeWindow.mpr
    ⟨hylq, hqupper, hprime W.2 hqA₂⟩

def allWindowWitnesses (N K Y : ℕ) (A₁ A₂ : Finset ℕ) :
    Finset ((Finset ℕ × Finset ℕ) × ℕ) :=
  ((A₁.powerset ×ˢ A₂.powerset) ×ˢ Nat.primesLE (K * (N + 1))).filter
    fun V =>
      let y := N / (subsetProduct V.1.1 * subsetProduct V.1.2)
      Y ≤ y ∧ V.2 ∈ splitPrimeWindow y K

lemma crossWitnessImage_subset_allWindow
    {N r z zplus Y : ℕ} {A₁ A₂ : Finset ℕ}
    (hz : 0 < z) (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hsmall : ∀ a ∈ A₁, a ≤ z)
    (hprime : ∀ q ∈ A₂, q.Prime)
    (hlarge : ∀ q ∈ A₂, zplus < q)
    (hendpoint : ∀ q ∈ A₂, q ≤ N)
    (hscale : z ^ r * Y ≤ zplus) :
    crossWitnessImage N A₁ A₂ r ⊆
      allWindowWitnesses N (z ^ r) Y A₁ A₂ := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hV
  have hwindows := crossWitnessMap_mem_window hz hdisj hpos hsmall
    hprime hlarge hscale hW
  have hWdata := Finset.mem_filter.mp hW
  have hcross := (Finset.mem_product.mp hWdata.1).1
  have hqS₂ := hWdata.2
  have hsep := (Finset.mem_filter.mp hcross).1
  rw [separateCutoffPairs] at hsep
  have hm := Finset.mem_product.mp hsep
  have hS₂sub := (mem_cutoffSubsets.mp hm.2).1
  have hqA₂ := hS₂sub hqS₂
  have hpowpos : 0 < z ^ r := pow_pos hz r
  have hqBound : W.2 ≤ z ^ r * (N + 1) := by
    calc
      W.2 ≤ N := hendpoint W.2 hqA₂
      _ ≤ N + 1 := Nat.le_succ N
      _ ≤ z ^ r * (N + 1) := by
        nlinarith
  rw [allWindowWitnesses]
  simp only [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, Nat.mem_primesLE.mpr
    ⟨hqBound, hprime W.2 hqA₂⟩⟩, hwindows.1, hwindows.2.1⟩
  exact ⟨Finset.mem_powerset.mpr hwindows.2.2.1,
    Finset.mem_powerset.mpr hwindows.2.2.2⟩

lemma splitPrimeWindow_subset_primesLE
    {N K y : ℕ} (hK : 0 < K) (hyN : y ≤ N) :
    splitPrimeWindow y K ⊆ Nat.primesLE (K * (N + 1)) := by
  intro q hq
  have hq' := mem_splitPrimeWindow.mp hq
  exact Nat.mem_primesLE.mpr ⟨hq'.2.1.trans
    (Nat.mul_le_mul_left K (Nat.succ_le_succ hyN)), hq'.2.2⟩

lemma allWindowWitnessMass_le
    {N K Y : ℕ} {δ : ℝ} {A₁ A₂ : Finset ℕ}
    (hK : 0 < K) (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hδ : 0 ≤ δ)
    (hwindow : ∀ y : ℕ, Y ≤ y →
      reciprocalMass (splitPrimeWindow y K) ≤ δ) :
    (∑ V ∈ allWindowWitnesses N K Y A₁ A₂,
      (subsetProduct V.1.1 : ℝ)⁻¹ *
        (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹) ≤
      δ * splitAllSubsetMass A₁ * splitAllSubsetMass A₂ := by
  rw [allWindowWitnesses, Finset.sum_filter, Finset.sum_product,
    Finset.sum_product]
  calc
    (∑ S ∈ A₁.powerset, ∑ R ∈ A₂.powerset,
      ∑ q ∈ Nat.primesLE (K * (N + 1)),
        if Y ≤ N / (subsetProduct S * subsetProduct R) ∧
            q ∈ splitPrimeWindow
              (N / (subsetProduct S * subsetProduct R)) K then
          (subsetProduct S : ℝ)⁻¹ *
            (subsetProduct R : ℝ)⁻¹ * (q : ℝ)⁻¹ else 0) ≤
      ∑ S ∈ A₁.powerset, ∑ R ∈ A₂.powerset,
        (subsetProduct S : ℝ)⁻¹ *
          (subsetProduct R : ℝ)⁻¹ * δ := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro R hR
      have hSsub := Finset.mem_powerset.mp hS
      have hRsub := Finset.mem_powerset.mp hR
      have hSpos : 0 < subsetProduct S := subsetProduct_pos hSsub
        (fun a ha => hpos a (Finset.mem_union_left _ ha))
      have hRpos : 0 < subsetProduct R := subsetProduct_pos hRsub
        (fun a ha => hpos a (Finset.mem_union_right _ ha))
      let y := N / (subsetProduct S * subsetProduct R)
      by_cases hY : Y ≤ y
      · have hyN : y ≤ N := Nat.div_le_self _ _
        have hsub := splitPrimeWindow_subset_primesLE hK hyN
        have hsumSub :
            (∑ q ∈ Nat.primesLE (K * (N + 1)),
              if Y ≤ y ∧ q ∈ splitPrimeWindow y K then
                (subsetProduct S : ℝ)⁻¹ *
                  (subsetProduct R : ℝ)⁻¹ * (q : ℝ)⁻¹ else 0) =
              (subsetProduct S : ℝ)⁻¹ *
                (subsetProduct R : ℝ)⁻¹ *
                  reciprocalMass (splitPrimeWindow y K) := by
          have hfilter :
              (Nat.primesLE (K * (N + 1))).filter
                  (fun q => q ∈ splitPrimeWindow y K) =
                splitPrimeWindow y K := by
            ext q
            simp only [Finset.mem_filter]
            constructor
            · exact fun hq => hq.2
            · exact fun hq => ⟨hsub hq, hq⟩
          simp only [hY, true_and]
          rw [← Finset.sum_filter, hfilter, reciprocalMass,
            Finset.mul_sum]
        change (∑ q ∈ Nat.primesLE (K * (N + 1)),
              if Y ≤ y ∧ q ∈ splitPrimeWindow y K then
                (subsetProduct S : ℝ)⁻¹ *
                  (subsetProduct R : ℝ)⁻¹ * (q : ℝ)⁻¹ else 0) ≤ _
        rw [hsumSub]
        exact mul_le_mul_of_nonneg_left (hwindow y hY)
          (mul_nonneg (by positivity) (by positivity))
      · change (∑ q ∈ Nat.primesLE (K * (N + 1)),
            if Y ≤ y ∧ q ∈ splitPrimeWindow y K then
              (subsetProduct S : ℝ)⁻¹ *
                (subsetProduct R : ℝ)⁻¹ * (q : ℝ)⁻¹ else 0) ≤ _
        simp only [hY, false_and, if_false, Finset.sum_const_zero]
        positivity
    _ = δ * splitAllSubsetMass A₁ * splitAllSubsetMass A₂ := by
      rw [splitAllSubsetMass, splitAllSubsetMass]
      calc
        (∑ S ∈ A₁.powerset, ∑ R ∈ A₂.powerset,
            (subsetProduct S : ℝ)⁻¹ *
              (subsetProduct R : ℝ)⁻¹ * δ) =
            ∑ S ∈ A₁.powerset,
              (δ * (subsetProduct S : ℝ)⁻¹) *
                ∑ R ∈ A₂.powerset,
                  (subsetProduct R : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro S _hS
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro R _hR
          ring
        _ = (∑ S ∈ A₁.powerset,
              δ * (subsetProduct S : ℝ)⁻¹) *
                ∑ R ∈ A₂.powerset,
                  (subsetProduct R : ℝ)⁻¹ := by
          exact (Finset.sum_mul A₁.powerset
            (fun S => δ * (subsetProduct S : ℝ)⁻¹)
            (∑ R ∈ A₂.powerset,
              (subsetProduct R : ℝ)⁻¹)).symm
        _ = (δ * ∑ S ∈ A₁.powerset,
              (subsetProduct S : ℝ)⁻¹) *
                ∑ R ∈ A₂.powerset,
                  (subsetProduct R : ℝ)⁻¹ := by
          congr 1
          exact (Finset.mul_sum A₁.powerset
            (fun S => (subsetProduct S : ℝ)⁻¹) δ).symm

lemma crossCutoffSplitMass_le
    {C δ : ℝ} {N r z zplus Y : ℕ} {A₁ A₂ : Finset ℕ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hz : 0 < z)
    (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hmass : reciprocalMass (A₁ ∪ A₂) ≤ C)
    (hsmall : ∀ a ∈ A₁, a ≤ z)
    (hprime : ∀ q ∈ A₂, q.Prime)
    (hlarge : ∀ q ∈ A₂, zplus < q)
    (hendpoint : ∀ q ∈ A₂, q ≤ N)
    (hscale : z ^ r * Y ≤ zplus)
    (hwindow : ∀ y : ℕ, Y ≤ y →
      reciprocalMass (splitPrimeWindow y (z ^ r)) ≤ δ) :
    (∑ ST ∈ crossCutoffSplitPairs N A₁ A₂ r,
      (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹) ≤
      δ * Real.exp C := by
  have hcrossWitness := crossMass_le_witnessSum
    (N := N) (r := r) (A₁ := A₁) (A₂ := A₂)
  have himage := witnessSum_eq_imageSum
    (N := N) (r := r) hdisj
  have hsub := crossWitnessImage_subset_allWindow hz hdisj hpos
    hsmall hprime hlarge hendpoint hscale
  have himageLe :
      (∑ V ∈ crossWitnessImage N A₁ A₂ r,
        (subsetProduct V.1.1 : ℝ)⁻¹ *
          (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹) ≤
        ∑ V ∈ allWindowWitnesses N (z ^ r) Y A₁ A₂,
          (subsetProduct V.1.1 : ℝ)⁻¹ *
            (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _V _hlarge _hnot => by positivity)
  have hwindowLe := allWindowWitnessMass_le
    (K := z ^ r) (N := N) (A₁ := A₁) (A₂ := A₂)
    (pow_pos hz r) hpos hδ hwindow
  have hA₁exp := splitAllSubsetMass_le_exp A₁
  have hA₂exp := splitAllSubsetMass_le_exp A₂
  have hA₂nonneg : 0 ≤ splitAllSubsetMass A₂ := by
    unfold splitAllSubsetMass
    positivity
  have hmassEq : reciprocalMass (A₁ ∪ A₂) =
      reciprocalMass A₁ + reciprocalMass A₂ := by
    unfold reciprocalMass
    exact Finset.sum_union hdisj
  have hexpMass : Real.exp (reciprocalMass A₁) *
      Real.exp (reciprocalMass A₂) ≤ Real.exp C := by
    rw [← Real.exp_add, ← hmassEq]
    exact Real.exp_le_exp.mpr hmass
  calc
    (∑ ST ∈ crossCutoffSplitPairs N A₁ A₂ r,
        (subsetProduct (ST.1 ∪ ST.2) : ℝ)⁻¹) ≤
      ∑ W ∈ crossWitnessPairs N A₁ A₂ r,
        (subsetProduct (W.1.1 ∪ W.1.2) : ℝ)⁻¹ := hcrossWitness
    _ = ∑ V ∈ crossWitnessImage N A₁ A₂ r,
        (subsetProduct V.1.1 : ℝ)⁻¹ *
          (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹ := himage
    _ ≤ ∑ V ∈ allWindowWitnesses N (z ^ r) Y A₁ A₂,
        (subsetProduct V.1.1 : ℝ)⁻¹ *
          (subsetProduct V.1.2 : ℝ)⁻¹ * (V.2 : ℝ)⁻¹ := himageLe
    _ ≤ δ * splitAllSubsetMass A₁ * splitAllSubsetMass A₂ := hwindowLe
    _ ≤ δ * Real.exp (reciprocalMass A₁) *
        Real.exp (reciprocalMass A₂) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hA₁exp hδ)
        hA₂exp hA₂nonneg
        (mul_nonneg hδ (by positivity))
    _ = δ * (Real.exp (reciprocalMass A₁) *
        Real.exp (reciprocalMass A₂)) := by ring
    _ ≤ δ * Real.exp C := mul_le_mul_of_nonneg_left hexpMass hδ

lemma splitDefectMass_le
    {C δ : ℝ} {N r z zplus Y : ℕ} {A₁ A₂ : Finset ℕ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hz : 0 < z)
    (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hmass : reciprocalMass (A₁ ∪ A₂) ≤ C)
    (hsmall : ∀ a ∈ A₁, a ≤ z)
    (hprime : ∀ q ∈ A₂, q.Prime)
    (hlarge : ∀ q ∈ A₂, zplus < q)
    (hendpoint : ∀ q ∈ A₂, q ≤ N)
    (hscale : z ^ r * Y ≤ zplus)
    (hwindow : ∀ y : ℕ, Y ≤ y →
      reciprocalMass (splitPrimeWindow y (z ^ r)) ≤ δ) :
    splitDefectMass N A₁ A₂ r ≤
      factorialTail C r + δ * Real.exp C := by
  have hhigh := highDegreeSplitMass_le_factorialTail
    hC hdisj hmass (N := N) (r := r)
  have hcross := crossCutoffSplitMass_le hC hδ hz hdisj hpos hmass
    hsmall hprime hlarge hendpoint hscale hwindow
  rw [splitDefectMass, splitDefectPairs_eq_union,
    Finset.sum_union (disjoint_highDegree_crossCutoff N A₁ A₂ r)]
  exact add_le_add hhigh hcross

lemma splittingApproximation
    {C δ : ℝ} {N r z zplus Y : ℕ} {A₁ A₂ : Finset ℕ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hz : 0 < z)
    (hdisj : Disjoint A₁ A₂)
    (hpos : ∀ a ∈ A₁ ∪ A₂, 0 < a)
    (hmass : reciprocalMass (A₁ ∪ A₂) ≤ C)
    (hsmall : ∀ a ∈ A₁, a ≤ z)
    (hprime : ∀ q ∈ A₂, q.Prime)
    (hlarge : ∀ q ∈ A₂, zplus < q)
    (hendpoint : ∀ q ∈ A₂, q ≤ N)
    (hscale : z ^ r * Y ≤ zplus)
    (hwindow : ∀ y : ℕ, Y ≤ y →
      reciprocalMass (splitPrimeWindow y (z ^ r)) ≤ δ) :
    |truncatedSieveApprox N (A₁ ∪ A₂) r -
        truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| ≤
      factorialTail C r + δ * Real.exp C := by
  exact (splittingError_le_defectMass hdisj hpos).trans
    (splitDefectMass_le hC hδ hz hdisj hpos hmass hsmall
      hprime hlarge hendpoint hscale hwindow)


/-- Parameter-ready form of the splitting lemma.  For fixed reciprocal
budget, low cutoff and truncation depth, one may choose the upper end of the
gap so that the cross-cutoff error is at most any prescribed `ε`, uniformly
in the endpoint and in both families. -/
theorem exists_splittingScale
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (z r : ℕ) (hz : 0 < z) :
    ∃ zplus : ℕ, ∀ {N : ℕ} {A₁ A₂ : Finset ℕ},
      Disjoint A₁ A₂ →
      (∀ a ∈ A₁ ∪ A₂, 0 < a) →
      reciprocalMass (A₁ ∪ A₂) ≤ C →
      (∀ a ∈ A₁, a ≤ z) →
      (∀ q ∈ A₂, q.Prime) →
      (∀ q ∈ A₂, zplus < q) →
      (∀ q ∈ A₂, q ≤ N) →
      |truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r *
            truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + ε := by
  let δ := ε / Real.exp C
  have hδ : 0 < δ := div_pos hε (Real.exp_pos C)
  have hwindowEventually :=
    eventually_splitPrimeWindowMass_lt hδ (z ^ r)
  rw [eventually_atTop] at hwindowEventually
  obtain ⟨Y, hY⟩ := hwindowEventually
  refine ⟨z ^ r * Y, ?_⟩
  intro N A₁ A₂ hdisj hpos hmass hsmall hprime hlarge hendpoint
  have hwindow : ∀ y : ℕ, Y ≤ y →
      reciprocalMass (splitPrimeWindow y (z ^ r)) ≤ δ := by
    intro y hy
    exact (hY y hy).le
  have hsplit := splittingApproximation hC hδ.le hz hdisj hpos
    hmass hsmall hprime hlarge hendpoint le_rfl hwindow
  have hδexp : δ * Real.exp C = ε := by
    dsimp only [δ]
    field_simp [(Real.exp_pos C).ne']
  rw [hδexp] at hsplit
  exact hsplit

/-! ## Choosing a low-mass scale gap -/


def scaleGap (A : Finset ℕ) (z : ℕ → ℕ) (j : ℕ) : Finset ℕ :=
  A.filter fun a => z j < a ∧ a ≤ z (j + 1)

@[simp] lemma mem_scaleGap {A : Finset ℕ} {z : ℕ → ℕ} {j a : ℕ} :
    a ∈ scaleGap A z j ↔ a ∈ A ∧ z j < a ∧ a ≤ z (j + 1) := by
  simp [scaleGap, and_assoc]

lemma scaleGap_subset (A : Finset ℕ) (z : ℕ → ℕ) (j : ℕ) :
    scaleGap A z j ⊆ A := by
  intro a ha
  exact (mem_scaleGap.mp ha).1

lemma disjoint_scaleGap_of_lt {A : Finset ℕ} {z : ℕ → ℕ}
    (hz : StrictMono z) {i j : ℕ} (hij : i < j) :
    Disjoint (scaleGap A z i) (scaleGap A z j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  have hi := (mem_scaleGap.mp hai).2
  have hj := (mem_scaleGap.mp haj).2
  have hzle : z (i + 1) ≤ z j := hz.monotone (by omega)
  omega

lemma pairwiseDisjoint_scaleGap (A : Finset ℕ) (z : ℕ → ℕ)
    (hz : StrictMono z) (k : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range k)) (scaleGap A z) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact disjoint_scaleGap_of_lt hz hlt
  · exact (disjoint_scaleGap_of_lt hz hgt).symm

lemma sum_reciprocalMass_scaleGap_le
    {C : ℝ} {A : Finset ℕ} (hmass : reciprocalMass A ≤ C)
    (z : ℕ → ℕ) (hz : StrictMono z) (k : ℕ) :
    (∑ j ∈ Finset.range k, reciprocalMass (scaleGap A z j)) ≤ C := by
  have hdisj := pairwiseDisjoint_scaleGap A z hz k
  have hsum := Finset.sum_biUnion
    (f := fun a : ℕ => (a : ℝ)⁻¹) hdisj
  have hsub : (Finset.range k).biUnion (scaleGap A z) ⊆ A := by
    rw [Finset.biUnion_subset_iff_forall_subset]
    intro j hj
    exact scaleGap_subset A z j
  have hle :
      (∑ a ∈ (Finset.range k).biUnion (scaleGap A z), (a : ℝ)⁻¹) ≤
        reciprocalMass A := by
    unfold reciprocalMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _a _ha _hnot => by positivity)
  rw [hsum] at hle
  exact hle.trans hmass

theorem exists_scaleGap_mass_le
    {C : ℝ} {A : Finset ℕ} (hmass : reciprocalMass A ≤ C)
    (z : ℕ → ℕ) (hz : StrictMono z) {k : ℕ} (hk : 0 < k) :
    ∃ j < k, reciprocalMass (scaleGap A z j) ≤ C / k := by
  by_contra hnot
  push_neg at hnot
  have hsum := sum_reciprocalMass_scaleGap_le hmass z hz k
  have hrange : (Finset.range k).Nonempty := by
    simp [Nat.ne_of_gt hk]
  have hlt :
      (∑ _j ∈ Finset.range k, C / (k : ℝ)) <
        ∑ j ∈ Finset.range k, reciprocalMass (scaleGap A z j) := by
    apply Finset.sum_lt_sum_of_nonempty hrange
    intro j hj
    exact hnot j (Finset.mem_range.mp hj)
  have hconst : (∑ _j ∈ Finset.range k, C / (k : ℝ)) = C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hk]
  rw [hconst] at hlt
  linarith

noncomputable def nextSplittingScale
    (C ε : ℝ) (r z : ℕ) : ℕ :=
  if h : 0 ≤ C ∧ 0 < ε ∧ 0 < z then
    max (Classical.choose
      (exists_splittingScale h.1 h.2.1 z r h.2.2)) (z + 1)
  else z + 1

lemma lt_nextSplittingScale (C ε : ℝ) (r z : ℕ) :
    z < nextSplittingScale C ε r z := by
  rw [nextSplittingScale]
  split_ifs
  · exact lt_of_lt_of_le (Nat.lt_succ_self z) (le_max_right _ _)
  · exact Nat.lt_succ_self z

lemma nextSplittingScale_spec
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (r z : ℕ) (hz : 0 < z) :
    ∀ {N : ℕ} {A₁ A₂ : Finset ℕ},
      Disjoint A₁ A₂ →
      (∀ a ∈ A₁ ∪ A₂, 0 < a) →
      reciprocalMass (A₁ ∪ A₂) ≤ C →
      (∀ a ∈ A₁, a ≤ z) →
      (∀ q ∈ A₂, q.Prime) →
      (∀ q ∈ A₂, nextSplittingScale C ε r z < q) →
      (∀ q ∈ A₂, q ≤ N) →
      |truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r *
            truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + ε := by
  rw [nextSplittingScale, dif_pos ⟨hC, hε, hz⟩]
  intro N A₁ A₂ hdisj hpos hmass hsmall hprime hlarge hendpoint
  apply (Classical.choose_spec
    (exists_splittingScale hC hε z r hz)) hdisj hpos hmass
      hsmall hprime _ hendpoint
  intro q hq
  exact lt_of_le_of_lt (le_max_left _ _) (hlarge q hq)

noncomputable def splittingScaleSeq
    (C ε : ℝ) (r z₀ : ℕ) : ℕ → ℕ
  | 0 => z₀
  | j + 1 => nextSplittingScale C ε r
      (splittingScaleSeq C ε r z₀ j)

lemma splittingScaleSeq_succ (C ε : ℝ) (r z₀ j : ℕ) :
    splittingScaleSeq C ε r z₀ (j + 1) =
      nextSplittingScale C ε r (splittingScaleSeq C ε r z₀ j) := rfl

lemma strictMono_splittingScaleSeq (C ε : ℝ) (r z₀ : ℕ) :
    StrictMono (splittingScaleSeq C ε r z₀) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [splittingScaleSeq_succ]
  exact lt_nextSplittingScale C ε r _

lemma splittingScaleSeq_pos
    {C ε : ℝ} {r z₀ : ℕ} (hz₀ : 0 < z₀) (j : ℕ) :
    0 < splittingScaleSeq C ε r z₀ j := by
  exact hz₀.trans_le
    ((strictMono_splittingScaleSeq C ε r z₀).monotone (Nat.zero_le j))

lemma splittingScaleSeq_spec
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (r z₀ j : ℕ) (hz₀ : 0 < z₀) :
    ∀ {N : ℕ} {A₁ A₂ : Finset ℕ},
      Disjoint A₁ A₂ →
      (∀ a ∈ A₁ ∪ A₂, 0 < a) →
      reciprocalMass (A₁ ∪ A₂) ≤ C →
      (∀ a ∈ A₁, a ≤ splittingScaleSeq C ε r z₀ j) →
      (∀ q ∈ A₂, q.Prime) →
      (∀ q ∈ A₂, splittingScaleSeq C ε r z₀ (j + 1) < q) →
      (∀ q ∈ A₂, q ≤ N) →
      |truncatedSieveApprox N (A₁ ∪ A₂) r -
          truncatedSieveApprox N A₁ r *
            truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + ε := by
  rw [splittingScaleSeq_succ]
  exact nextSplittingScale_spec hC hε r _
    (splittingScaleSeq_pos hz₀ j)


def lowScalePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  A.filter fun a => a ≤ z

def highScalePart (A : Finset ℕ) (z : ℕ) : Finset ℕ :=
  A.filter fun a => z < a

@[simp] lemma mem_lowScalePart {A : Finset ℕ} {z a : ℕ} :
    a ∈ lowScalePart A z ↔ a ∈ A ∧ a ≤ z := by
  simp [lowScalePart]

@[simp] lemma mem_highScalePart {A : Finset ℕ} {z a : ℕ} :
    a ∈ highScalePart A z ↔ a ∈ A ∧ z < a := by
  simp [highScalePart]

lemma lowScalePart_subset (A : Finset ℕ) (z : ℕ) :
    lowScalePart A z ⊆ A := Finset.filter_subset _ _

lemma highScalePart_subset (A : Finset ℕ) (z : ℕ) :
    highScalePart A z ⊆ A := Finset.filter_subset _ _

lemma disjoint_lowScalePart_highScalePart
    (A : Finset ℕ) {z zplus : ℕ} (hzz : z < zplus) :
    Disjoint (lowScalePart A z) (highScalePart A zplus) := by
  rw [Finset.disjoint_left]
  intro a hlow hhigh
  have hl := mem_lowScalePart.mp hlow
  have hh := mem_highScalePart.mp hhigh
  omega

lemma union_lowScalePart_highScalePart_subset
    (A : Finset ℕ) (z zplus : ℕ) :
    lowScalePart A z ∪ highScalePart A zplus ⊆ A := by
  exact Finset.union_subset (lowScalePart_subset A z)
    (highScalePart_subset A zplus)

lemma sdiff_union_low_high_eq_scaleGap
    (A : Finset ℕ) (z : ℕ → ℕ) (j : ℕ) :
    A \ (lowScalePart A (z j) ∪ highScalePart A (z (j + 1))) =
      scaleGap A z j := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union, mem_lowScalePart,
    mem_highScalePart, mem_scaleGap]
  constructor
  · rintro ⟨ha, hnot⟩
    have hlow : ¬a ≤ z j := fun hle => hnot (Or.inl ⟨ha, hle⟩)
    have hhigh : ¬z (j + 1) < a :=
      fun hlt => hnot (Or.inr ⟨ha, hlt⟩)
    exact ⟨ha, by omega, by omega⟩
  · rintro ⟨ha, hlo, hhi⟩
    refine ⟨ha, ?_⟩
    rintro (⟨_ha, hle⟩ | ⟨_ha, hgt⟩) <;> omega

lemma Admissible.mono {C : ℝ} {N : ℕ} {A B : Finset ℕ}
    (hA : Admissible C N A) (hBA : B ⊆ A) :
    Admissible C N B := by
  refine ⟨hBA.trans hA.subset_interval,
    hA.pairwiseCoprime.mono hBA, ?_⟩
  exact (reciprocalMass_mono hBA
    (fun b hb => by have := hA.two_le (hBA hb); omega)).trans hA.mass_le

lemma sieveDensity_le_one {N : ℕ} (hN : 0 < N) (A : Finset ℕ) :
    sieveDensity N A ≤ 1 := by
  have hsub : unsieved N A ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(mem_unsieved.mp hn).1,
      (mem_unsieved.mp hn).2.1⟩
  have hcard : (unsieved N A).card ≤ N := by
    simpa [Nat.card_Icc] using Finset.card_le_card hsub
  rw [sieveDensity]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_one hNR]
  exact_mod_cast hcard

lemma periodicDensity_nonneg {A : Finset ℕ}
    (hA : ∀ a ∈ A, 2 ≤ a) : 0 ≤ periodicDensity A := by
  unfold periodicDensity
  apply Finset.prod_nonneg
  intro a ha
  have haNat := hA a ha
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have haPos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hainv : (a : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ haPos).mpr haR
  linarith

lemma periodicDensity_le_one {A : Finset ℕ}
    (hA : ∀ a ∈ A, 2 ≤ a) : periodicDensity A ≤ 1 := by
  unfold periodicDensity
  apply Finset.prod_le_one
    (fun a ha => by
      have haNat := hA a ha
      have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
      have haPos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      have hainv : (a : ℝ)⁻¹ ≤ 1 := by
        exact (inv_le_one₀ haPos).mpr haR
      linarith)
  intro a ha
  have hinv : 0 ≤ (a : ℝ)⁻¹ := by positivity
  linarith


theorem sieveDensity_modulusProduct {A : Finset ℕ}
    (hA : PairwiseCoprime A) (hpos : ∀ a ∈ A, 0 < a) :
    sieveDensity (modulusProduct A) A = periodicDensity A := by
  have hcardR :
      ((unsieved (modulusProduct A) A).card : ℝ) =
        ∏ a ∈ A, ((a : ℝ) - 1) := by
    exact_mod_cast card_unsieved_modulusProduct hA hpos
  rw [sieveDensity, hcardR]
  have hmodulusR :
      (modulusProduct A : ℝ) = ∏ a ∈ A, (a : ℝ) := by
    simp [modulusProduct]
  rw [hmodulusR, ← Finset.prod_div_distrib]
  unfold periodicDensity
  apply Finset.prod_congr rfl
  intro a ha
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hpos a ha))
  rw [sub_div, div_self ha0, div_eq_mul_inv, one_mul]

/-! ## The terminal block of primes -/

/-- The primes in the half-open terminal interval `(y, N]`.  Using a
half-open lower endpoint makes its survivor set exactly Mathlib's
`(y + 1)`-smooth numbers. -/
def terminalPrimeBlock (N y : ℕ) : Finset ℕ :=
  (Finset.Ioc y N).filter Nat.Prime

@[simp] lemma mem_terminalPrimeBlock {N y p : ℕ} :
    p ∈ terminalPrimeBlock N y ↔ y < p ∧ p ≤ N ∧ p.Prime := by
  simp [terminalPrimeBlock, and_assoc]

lemma pairwiseCoprime_terminalPrimeBlock (N y : ℕ) :
    PairwiseCoprime (terminalPrimeBlock N y) := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (mem_terminalPrimeBlock.mp hp).2.2
    (mem_terminalPrimeBlock.mp hq).2.2).mpr hpq

/-- Exact smooth-number interpretation of the terminal-prime construction:
an integer at most `N` avoids every prime greater than `y` if and only if
all its prime factors are at most `y`. -/
theorem unsieved_terminalPrimeBlock_eq_smoothNumbersUpTo (N y : ℕ) :
    unsieved N (terminalPrimeBlock N y) =
      N.smoothNumbersUpTo (y + 1) := by
  ext n
  constructor
  · intro hn
    have hn' := mem_unsieved.mp hn
    rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers']
    refine ⟨hn'.2.1, ?_⟩
    intro p hp hpn
    by_contra hnot
    have hyp : y < p := by omega
    have hpN : p ≤ N :=
      (Nat.le_of_dvd (by omega : 0 < n) hpn).trans hn'.2.1
    exact hn'.2.2 p (mem_terminalPrimeBlock.mpr ⟨hyp, hpN, hp⟩) hpn
  · intro hn
    have hn0 : n ≠ 0 :=
      Nat.ne_zero_of_mem_smoothNumbers
        (Nat.mem_smoothNumbersUpTo.mp hn).2
    rw [Nat.mem_smoothNumbersUpTo, Nat.mem_smoothNumbers'] at hn
    rw [mem_unsieved]
    refine ⟨Nat.one_le_iff_ne_zero.mpr hn0, hn.1, ?_⟩
    intro p hp hpn
    have hp' := mem_terminalPrimeBlock.mp hp
    have hpy := hn.2 p hp'.2.2 hpn
    omega

lemma sieveDensity_terminalPrimeBlock (N y : ℕ) :
    sieveDensity N (terminalPrimeBlock N y) =
      (N.smoothNumbersUpTo (y + 1)).card / (N : ℝ) := by
  rw [sieveDensity, unsieved_terminalPrimeBlock_eq_smoothNumbersUpTo]

/-- The cumulative reciprocal mass of primes at most `N`. -/
def primeReciprocalCumulative (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, (p : ℝ)⁻¹

lemma terminalPrimeBlock_eq_sdiff (N y : ℕ) :
    terminalPrimeBlock N y =
      (Finset.Ioc 0 N).filter Nat.Prime \
        (Finset.Ioc 0 y).filter Nat.Prime := by
  ext p
  simp only [mem_terminalPrimeBlock, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hyp, hpN, hp⟩
    refine ⟨⟨⟨hp.pos, hpN⟩, hp⟩, ?_⟩
    rintro ⟨⟨_hp0, hpy⟩, _hp⟩
    omega
  · rintro ⟨⟨⟨_hp0, hpN⟩, hp⟩, hnot⟩
    refine ⟨?_, hpN, hp⟩
    by_contra hyp
    exact hnot ⟨⟨hp.pos, by omega⟩, hp⟩

lemma reciprocalMass_terminalPrimeBlock (N y : ℕ) (hyN : y ≤ N) :
    reciprocalMass (terminalPrimeBlock N y) =
      primeReciprocalCumulative N - primeReciprocalCumulative y := by
  rw [terminalPrimeBlock_eq_sdiff]
  have hsubset :
      (Finset.Ioc 0 y).filter Nat.Prime ⊆
        (Finset.Ioc 0 N).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hyN⟩, hp.2⟩
  have hsum := Finset.sum_sdiff
    (f := fun p : ℕ => (p : ℝ)⁻¹) hsubset
  unfold reciprocalMass primeReciprocalCumulative
  linarith

/-- Mertens' second theorem, in its exact finite form with an explicit error
term.  The imported proof is entirely internal to Lean and Mathlib. -/
lemma primeReciprocalCumulative_eq_mertens (N : ℕ) :
    primeReciprocalCumulative N =
      Real.log (Real.log (N : ℝ)) + Mertens.M + Mertens.E₂p N := by
  simpa [primeReciprocalCumulative, Nat.floor_natCast, one_div] using
    Mertens.sum_prime_div_eq (N : ℝ)

lemma reciprocalMass_terminalPrimeBlock_eq_mertens
    (N y : ℕ) (hyN : y ≤ N) :
    reciprocalMass (terminalPrimeBlock N y) =
      (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (y : ℝ))) +
        (Mertens.E₂p N - Mertens.E₂p y) := by
  rw [reciprocalMass_terminalPrimeBlock N y hyN,
    primeReciprocalCumulative_eq_mertens,
    primeReciprocalCumulative_eq_mertens]
  ring

lemma admissible_terminalPrimeBlock {C : ℝ} {N y : ℕ}
    (hmass : reciprocalMass (terminalPrimeBlock N y) ≤ C) :
    Admissible C N (terminalPrimeBlock N y) := by
  refine ⟨?_, pairwiseCoprime_terminalPrimeBlock N y, hmass⟩
  intro p hp
  have hp' := mem_terminalPrimeBlock.mp hp
  exact Finset.mem_Icc.mpr ⟨hp'.2.2.two_le, hp'.2.1⟩

/-- The explicit Mertens error tends to zero along natural endpoints. -/
theorem tendsto_mertensError_nat :
    Tendsto (fun N : ℕ => Mertens.E₂p (N : ℝ)) atTop (nhds 0) := by
  exact ((Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound').comp
    tendsto_natCast_atTop_atTop

/-! ## The power cutoff in the terminal-prime construction -/

/-- The natural cutoff obtained by rounding `N ^ a` down. -/
noncomputable def powerCutoff (a : ℝ) (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ a⌋₊

theorem tendsto_powerCutoff_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (powerCutoff a) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

/-- Rounding `N ^ a` down does not change its logarithmic exponent. -/
theorem tendsto_log_powerCutoff_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun N : ℕ =>
        Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ))
      atTop (nhds a) := by
  let x : ℕ → ℝ := fun N => (N : ℝ) ^ a
  have hx : Tendsto x atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto (fun N : ℕ => (powerCutoff a N : ℝ) / x N)
        atTop (nhds 1) := by
    exact tendsto_nat_floor_div_atTop.comp hx
  have hlogRatio :
      Tendsto
        (fun N : ℕ => Real.log ((powerCutoff a N : ℝ) / x N))
        atTop (nhds 0) := by
    simpa using hratio.log one_ne_zero
  have hlogN :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall :
      Tendsto
        (fun N : ℕ =>
          Real.log ((powerCutoff a N : ℝ) / x N) /
            Real.log (N : ℝ))
        atTop (nhds 0) :=
    hlogRatio.div_atTop hlogN
  have hconst : Tendsto (fun _ : ℕ => a) atTop (nhds a) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Real.log ((powerCutoff a N : ℝ) / x N) /
              Real.log (N : ℝ) + a)
        atTop (nhds (0 + a)) :=
    hsmall.add hconst
  convert hsum.congr' ?_ using 1
  · ring_nf
  · filter_upwards
      [hratio.eventually (Ioi_mem_nhds zero_lt_one),
        eventually_ge_atTop 2] with N hratioPos hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hxPos : 0 < x N := Real.rpow_pos_of_pos hNpos a
    rw [show (powerCutoff a N : ℝ) =
        ((powerCutoff a N : ℝ) / x N) * x N by
      field_simp [hxPos.ne'],
      Real.log_mul hratioPos.ne' hxPos.ne']
    have hxLog : Real.log (x N) = a * Real.log (N : ℝ) := by
      exact Real.log_rpow hNpos a
    rw [hxLog]
    have hlogN0 : Real.log (N : ℝ) ≠ 0 := by
      have : (1 : ℝ) < N := by
        exact_mod_cast (show 1 < N by omega)
      exact (Real.log_pos this).ne'
    field_simp [hlogN0]

lemma powerCutoff_le_self {a : ℝ} (ha1 : a ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) : powerCutoff a N ≤ N := by
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ a ≤ (N : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase ha1
  have hfloor : (powerCutoff a N : ℝ) ≤ (N : ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg (by positivity) a)).trans hpow
  exact_mod_cast hfloor

/-- Mertens' theorem computes the reciprocal mass of the terminal block
whose lower endpoint is `floor (N ^ a)`. -/
theorem tendsto_reciprocalMass_terminalPrimeBlock_powerCutoff
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto
      (fun N : ℕ =>
        reciprocalMass (terminalPrimeBlock N (powerCutoff a N)))
      atTop (nhds (-Real.log a)) := by
  have hyTop := tendsto_powerCutoff_atTop ha
  have hratio := tendsto_log_powerCutoff_div_log ha
  have hlogRatio :
      Tendsto
        (fun N : ℕ =>
          Real.log
            (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)))
        atTop (nhds (Real.log a)) :=
    hratio.log ha.ne'
  have hmain :
      Tendsto
        (fun N : ℕ =>
          -Real.log
            (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)))
        atTop (nhds (-Real.log a)) :=
    hlogRatio.neg
  have herrY :
      Tendsto (fun N : ℕ => Mertens.E₂p (powerCutoff a N : ℝ))
        atTop (nhds 0) :=
    tendsto_mertensError_nat.comp hyTop
  have herr :
      Tendsto
        (fun N : ℕ => Mertens.E₂p (N : ℝ) -
          Mertens.E₂p (powerCutoff a N : ℝ))
        atTop (nhds 0) := by
    simpa using tendsto_mertensError_nat.sub herrY
  have hsum := hmain.add herr
  convert hsum.congr' ?_ using 1
  · ring_nf
  · filter_upwards
      [eventually_ge_atTop 2,
        hyTop.eventually (Ici_mem_atTop 2)] with N hN hy2
    have hyN : powerCutoff a N ≤ N :=
      powerCutoff_le_self ha1 (by omega)
    rw [reciprocalMass_terminalPrimeBlock_eq_mertens N
      (powerCutoff a N) hyN]
    have hlogN : Real.log (N : ℝ) ≠ 0 := by
      exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have hlogY : Real.log (powerCutoff a N : ℝ) ≠ 0 := by
      exact (Real.log_pos (by
        exact_mod_cast (show 1 < powerCutoff a N by omega))).ne'
    rw [Real.log_div hlogY hlogN]
    ring

lemma powerCutoff_mono_exponent {a b : ℝ} (hab : a ≤ b)
    {N : ℕ} (hN : 1 ≤ N) :
    powerCutoff a N ≤ powerCutoff b N := by
  unfold powerCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab

/-- Mertens mass of a fixed logarithmic prime cell
`(N ^ a, N ^ b]`: it tends to `log b - log a`. -/
theorem tendsto_reciprocalMass_powerCutoff_primeCell
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun N : ℕ => reciprocalMass
        (terminalPrimeBlock (powerCutoff b N) (powerCutoff a N)))
      atTop (nhds (Real.log b - Real.log a)) := by
  have hb : 0 < b := ha.trans_le hab
  have haRatio := tendsto_log_powerCutoff_div_log ha
  have hbRatio := tendsto_log_powerCutoff_div_log hb
  have hlogA :
      Tendsto
        (fun N : ℕ => Real.log
          (Real.log (powerCutoff a N : ℝ) / Real.log (N : ℝ)))
        atTop (nhds (Real.log a)) :=
    haRatio.log ha.ne'
  have hlogB :
      Tendsto
        (fun N : ℕ => Real.log
          (Real.log (powerCutoff b N : ℝ) / Real.log (N : ℝ)))
        atTop (nhds (Real.log b)) :=
    hbRatio.log hb.ne'
  have hmain := hlogB.sub hlogA
  have haTop := tendsto_powerCutoff_atTop ha
  have hbTop := tendsto_powerCutoff_atTop hb
  have herrA := tendsto_mertensError_nat.comp haTop
  have herrB := tendsto_mertensError_nat.comp hbTop
  have herr :
      Tendsto
        (fun N : ℕ => Mertens.E₂p (powerCutoff b N : ℝ) -
          Mertens.E₂p (powerCutoff a N : ℝ))
        atTop (nhds 0) := by
    simpa using herrB.sub herrA
  have hsum := hmain.add herr
  convert hsum.congr' ?_ using 1
  · ring_nf
  · filter_upwards
      [eventually_ge_atTop 2,
        haTop.eventually (Ici_mem_atTop 2),
        hbTop.eventually (Ici_mem_atTop 2)] with N hN ha2 hb2
    have habN : powerCutoff a N ≤ powerCutoff b N :=
      powerCutoff_mono_exponent hab (by omega)
    rw [reciprocalMass_terminalPrimeBlock_eq_mertens _ _ habN]
    have hlogN : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have hlogA0 : Real.log (powerCutoff a N : ℝ) ≠ 0 :=
      (Real.log_pos (by
        exact_mod_cast (show 1 < powerCutoff a N by omega))).ne'
    have hlogB0 : Real.log (powerCutoff b N : ℝ) ≠ 0 :=
      (Real.log_pos (by
        exact_mod_cast (show 1 < powerCutoff b N by omega))).ne'
    rw [Real.log_div hlogB0 hlogN, Real.log_div hlogA0 hlogN]
    ring

/-! ## The analytic target and its two sharp halves

The following definitions spell out the quantifiers in Tao's theorem.  In
particular, `TaoLowerBound` is uniform in the admissible set `A`; replacing it
by a statement about one preselected sequence of sets would not suffice for
the finite minimum.
-/

/-- A zero-extended Dickman--de Bruijn profile, characterized by its initial
condition, positivity, compact Lipschitz regularity, and integral delay
equation.  The last identity is equivalent (away from the first transition)
to `u * ρ' u = -ρ (u - 1)`. -/
def IsDickmanProfile (ρ : ℝ → ℝ) : Prop :=
  (∀ u : ℝ, u < 0 → ρ u = 0) ∧
  (∀ u : ℝ, 0 ≤ u → u ≤ 1 → ρ u = 1) ∧
  (∀ u : ℝ, 0 ≤ u → 0 < ρ u) ∧
  (∀ R : ℝ, 0 ≤ R →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v : ℝ,
      0 ≤ u → u ≤ R → 0 ≤ v → v ≤ R →
        |ρ u - ρ v| ≤ K * |u - v|) ∧
  (∀ u : ℝ, 1 ≤ u →
    (∫ v : ℝ in (u - 1)..u, ρ v) = u * ρ u)

/-- The canonical Dickman--de Bruijn function, constructed as the normalized
density of the scale-invariant Poisson perpetuity. -/
def dickmanRho : ℝ → ℝ :=
  Erdos390.poissonDickmanProfile

theorem dickmanRho_profile : IsDickmanProfile dickmanRho := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact Erdos390.poissonDickmanProfile_of_neg hu
  · intro u hu0 hu1
    exact Erdos390.poissonDickmanProfile_of_mem_unit hu0 hu1
  · intro u hu
    exact Erdos390.poissonDickmanProfile_pos hu
  · intro R _hR
    refine ⟨1, by norm_num, ?_⟩
    intro u v hu0 _huR hv0 _hvR
    simpa [dickmanRho] using
      Erdos390.abs_poissonDickmanProfile_sub_le hu0 hv0
  · intro u hu
    exact Erdos390.poissonDickmanProfile_integral_delay hu

theorem dickmanRho_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ dickmanRho u :=
  Erdos390.poissonDickmanProfile_nonneg hu

theorem dickmanRho_le_one {u : ℝ} (hu : 0 ≤ u) :
    dickmanRho u ≤ 1 :=
  Erdos390.poissonDickmanProfile_le_one hu

theorem continuousAt_dickmanRho_of_pos {u : ℝ} (hu : 0 < u) :
    ContinuousAt dickmanRho u := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min ε u, lt_min hε hu, ?_⟩
  intro v hv
  rw [Real.dist_eq] at hv ⊢
  have hvu : |v - u| < u := hv.trans_le (min_le_right _ _)
  have hv0 : 0 ≤ v := by
    rw [abs_lt] at hvu
    linarith
  exact (Erdos390.abs_poissonDickmanProfile_sub_le hv0 hu.le).trans_lt
    (hv.trans_le (min_le_left _ _))

theorem lipschitzOnWith_one_dickmanRho :
    LipschitzOnWith 1 dickmanRho (Ici (0 : ℝ)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  simpa [dickmanRho, Real.dist_eq] using
    Erdos390.abs_poissonDickmanProfile_sub_le hu hv

theorem continuousOn_dickmanRho_Ici_zero :
    ContinuousOn dickmanRho (Ici (0 : ℝ)) :=
  lipschitzOnWith_one_dickmanRho.continuousOn

/-- Uniform oscillation bound for the Buchstab kernel on a compact
logarithmic strip. -/
theorem dickmanRho_buchstabKernel_oscillation
    {K u s t : ℝ}
    (huK : u ≤ K) (hs1 : 1 ≤ s) (ht1 : 1 ≤ t)
    (hsu : s ≤ u) (htu : t ≤ u) :
    |dickmanRho (u / s - 1) - dickmanRho (u / t - 1)| ≤
      K * |s - t| := by
  have hsPos : 0 < s := zero_lt_one.trans_le hs1
  have htPos : 0 < t := zero_lt_one.trans_le ht1
  have hu0 : 0 ≤ u := by linarith
  have hxs : 0 ≤ u / s - 1 := by
    rw [sub_nonneg, one_le_div₀ hsPos]
    exact hsu
  have hxt : 0 ≤ u / t - 1 := by
    rw [sub_nonneg, one_le_div₀ htPos]
    exact htu
  have hrho := Erdos390.abs_poissonDickmanProfile_sub_le hxs hxt
  change
    |dickmanRho (u / s - 1) - dickmanRho (u / t - 1)| ≤
      |(u / s - 1) - (u / t - 1)| at hrho
  calc
    |dickmanRho (u / s - 1) - dickmanRho (u / t - 1)| ≤
        |(u / s - 1) - (u / t - 1)| := hrho
    _ = u * |s - t| / (s * t) := by
      rw [show (u / s - 1) - (u / t - 1) =
          u * (t - s) / (s * t) by
        field_simp [hsPos.ne', htPos.ne']
        ring]
      rw [abs_div, abs_mul, abs_of_nonneg hu0,
        abs_mul, abs_of_pos hsPos, abs_of_pos htPos,
        abs_sub_comm]
    _ ≤ u * |s - t| := by
      apply div_le_self
      · positivity
      · nlinarith [mul_le_mul hs1 ht1 (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : 0 ≤ s)]
    _ ≤ K * |s - t| :=
      mul_le_mul_of_nonneg_right huK (abs_nonneg _)

lemma intervalIntegrable_dickmanRho_of_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable dickmanRho volume a b := by
  exact (continuousOn_dickmanRho_Ici_zero.mono fun x hx => by
    rcases mem_uIcc.mp hx with hx | hx
    · exact ha.trans hx.1
    · exact hb.trans hx.1) |>.intervalIntegrable

theorem measurable_dickmanRho : Measurable dickmanRho := by
  unfold dickmanRho Erdos390.poissonDickmanProfile
  apply Measurable.ite (by simp) measurable_const
  unfold Erdos390.poissonDickmanTotalDensityReal
  exact
    (Erdos390.measurable_poissonDickmanTotalDensityFormula.ennreal_toReal
      ).div_const _

/-- A fixed primitive used to differentiate the Dickman delay equation. -/
def dickmanPrimitive (u : ℝ) : ℝ :=
  ∫ v : ℝ in (0 : ℝ)..u, dickmanRho v

theorem hasDerivAt_dickmanPrimitive {u : ℝ} (hu : 0 < u) :
    HasDerivAt dickmanPrimitive (dickmanRho u) u := by
  exact
    (intervalIntegral.integral_hasStrictDerivAt_right
      (intervalIntegrable_dickmanRho_of_nonneg
        (a := 0) (b := u) (by norm_num) hu.le)
      measurable_dickmanRho.stronglyMeasurable.stronglyMeasurableAtFilter
      (continuousAt_dickmanRho_of_pos hu)).hasDerivAt

theorem dickmanPrimitive_sub (u : ℝ) (hu : 1 ≤ u) :
    dickmanPrimitive u - dickmanPrimitive (u - 1) =
      ∫ v : ℝ in (u - 1)..u, dickmanRho v := by
  unfold dickmanPrimitive
  exact
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_dickmanRho_of_nonneg
        (a := 0) (b := u) (by norm_num) (zero_le_one.trans hu))
      (intervalIntegrable_dickmanRho_of_nonneg
        (a := 0) (b := u - 1) (by norm_num) (by linarith [hu]))

/-- Differential form of the delay equation above the first transition. -/
theorem hasDerivAt_dickmanRho {u : ℝ} (hu : 1 < u) :
    HasDerivAt dickmanRho (-dickmanRho (u - 1) / u) u := by
  let numerator : ℝ → ℝ := fun v =>
    dickmanPrimitive v - dickmanPrimitive (v - 1)
  have hnum :
      HasDerivAt numerator (dickmanRho u - dickmanRho (u - 1)) u := by
    have hraw :=
      (hasDerivAt_dickmanPrimitive (zero_lt_one.trans hu)).sub
        ((hasDerivAt_dickmanPrimitive (by linarith)).comp u
          (HasDerivAt.sub_const 1 (hasDerivAt_id' u)))
    change HasDerivAt
      (fun v : ℝ => dickmanPrimitive v - dickmanPrimitive (v - 1))
      (dickmanRho u - dickmanRho (u - 1) * 1) u at hraw
    simpa only [numerator, mul_one] using hraw
  have hquot :
      HasDerivAt (fun v : ℝ => numerator v / v)
        (((dickmanRho u - dickmanRho (u - 1)) * u - numerator u) /
          u ^ 2) u := by
    have hraw :=
      hnum.div (hasDerivAt_id' u) (ne_of_gt (zero_lt_one.trans hu))
    change HasDerivAt (fun v : ℝ => numerator v / v)
      (((dickmanRho u - dickmanRho (u - 1)) * u - numerator u * 1) /
        u ^ 2) u at hraw
    simpa only [mul_one] using hraw
  have heq :
      dickmanRho =ᶠ[nhds u] fun v : ℝ => numerator v / v := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    have hv0 : v ≠ 0 := ne_of_gt (zero_lt_one.trans hv)
    rw [eq_div_iff hv0]
    rw [show numerator v =
        ∫ x : ℝ in (v - 1)..v, dickmanRho x by
      exact dickmanPrimitive_sub v hv.le]
    rw [dickmanRho_profile.2.2.2.2 v hv.le]
    ring
  have hdelay : numerator u = u * dickmanRho u := by
    rw [show numerator u =
        ∫ x : ℝ in (u - 1)..u, dickmanRho x by
      exact dickmanPrimitive_sub u hu.le,
      dickmanRho_profile.2.2.2.2 u hu.le]
  have hquot' :
      HasDerivAt (fun v : ℝ => numerator v / v)
        (-dickmanRho (u - 1) / u) u := by
    convert hquot using 1
    rw [hdelay]
    field_simp [ne_of_gt (zero_lt_one.trans hu)]
    ring
  exact hquot'.congr_of_eventuallyEq heq

/-- Integral form of the Dickman differential equation, normalized at
`ρ(1) = 1`. -/
theorem dickmanRho_eq_one_sub_integral (u : ℝ) (hu : 1 ≤ u) :
    dickmanRho u = 1 -
      ∫ t : ℝ in (1 : ℝ)..u, dickmanRho (t - 1) / t := by
  let f : ℝ → ℝ := fun t => -dickmanRho (t - 1) / t
  have hfcont : ContinuousOn f (Icc (1 : ℝ) u) := by
    apply ContinuousOn.div
    · exact (continuousOn_dickmanRho_Ici_zero.comp
        (continuous_id.sub continuous_const).continuousOn (by
          intro t ht
          exact sub_nonneg.mpr ht.1)) |>.neg
    · exact continuousOn_id
    · intro t ht ht0
      linarith [ht.1]
  have hfint : IntervalIntegrable f volume 1 u :=
    hfcont.intervalIntegrable_of_Icc hu
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hu (continuousOn_dickmanRho_Ici_zero.mono (by
      intro t ht
      exact zero_le_one.trans ht.1))
    (fun t ht => by
      simpa only [f] using hasDerivAt_dickmanRho ht.1)
    hfint
  have hrho1 : dickmanRho 1 = 1 :=
    dickmanRho_profile.2.1 1 (by norm_num) (by norm_num)
  change (∫ t : ℝ in (1 : ℝ)..u, f t) =
    dickmanRho u - dickmanRho 1 at hfund
  rw [hrho1] at hfund
  have hfneg : f = fun t : ℝ => -(dickmanRho (t - 1) / t) := by
    funext t
    simp only [f, neg_div]
  rw [hfneg, intervalIntegral.integral_neg] at hfund
  linarith

/-- The continuous Buchstab kernel is the Dickman delay kernel after the
inversion `t = u / s`. -/
theorem dickmanRho_buchstab_integral (u : ℝ) (hu : 1 ≤ u) :
    (∫ s : ℝ in (1 : ℝ)..u,
        dickmanRho (u / s - 1) / s) =
      ∫ t : ℝ in (1 : ℝ)..u, dickmanRho (t - 1) / t := by
  let phi : ℝ → ℝ := fun s => u / s
  let phi' : ℝ → ℝ := fun s => -u / s ^ 2
  let g : ℝ → ℝ := fun t => dickmanRho (t - 1) / t
  have hphi : ∀ s ∈ Set.uIcc (1 : ℝ) u,
      HasDerivAt phi (phi' s) s := by
    intro s hs
    rw [Set.uIcc_of_le hu] at hs
    have hs0 : s ≠ 0 := ne_of_gt (zero_lt_one.trans_le hs.1)
    have h := (hasDerivAt_inv hs0).const_mul u
    change HasDerivAt phi (u * -(s ^ 2)⁻¹) s at h
    have heq : u * -(s ^ 2)⁻¹ = phi' s := by
      dsimp only [phi', div_eq_mul_inv]
      ring
    rw [heq] at h
    exact h
  have hphi' : ContinuousOn phi' (Set.uIcc (1 : ℝ) u) := by
    rw [Set.uIcc_of_le hu]
    apply ContinuousOn.div continuousOn_const
      (continuousOn_id.pow 2)
    intro s hs hs0
    have hspos : 0 < s := zero_lt_one.trans_le hs.1
    exact (pow_pos hspos 2).ne' hs0
  have hgIci : ContinuousOn g (Set.Ici (1 : ℝ)) := by
    apply ContinuousOn.div
    · exact continuousOn_dickmanRho_Ici_zero.comp
        (continuous_id.sub continuous_const).continuousOn (by
          intro t ht
          change 1 ≤ t at ht
          exact sub_nonneg.mpr ht)
    · exact continuousOn_id
    · intro t ht ht0
      exact (ne_of_gt (zero_lt_one.trans_le ht)) ht0
  have himage : phi '' Set.uIcc (1 : ℝ) u ⊆ Set.Ici (1 : ℝ) := by
    rintro t ⟨s, hs, rfl⟩
    rw [Set.uIcc_of_le hu] at hs
    dsimp only [phi]
    apply (le_div_iff₀ (zero_lt_one.trans_le hs.1)).2
    simpa using hs.2
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    hphi hphi' (hgIci.mono himage)
  change
    (∫ s : ℝ in (1 : ℝ)..u,
      (g ∘ phi) s * phi' s) =
      ∫ t : ℝ in phi 1..phi u, g t at hsubst
  have hleft :
      (fun s : ℝ => (g ∘ phi) s * phi' s) =
        fun s : ℝ => -(dickmanRho (u / s - 1) / s) := by
    funext s
    by_cases hs : s = 0
    · subst s
      simp [g, phi, phi']
    · dsimp only [g, phi, phi', Function.comp_apply]
      field_simp [hs]
  have hphiOne : phi 1 = u := by simp [phi]
  have hphiU : phi u = 1 := by
    simp [phi, ne_of_gt (zero_lt_one.trans_le hu)]
  rw [hleft, intervalIntegral.integral_neg,
    hphiOne, hphiU] at hsubst
  have hsymm :
      (∫ t : ℝ in u..(1 : ℝ), g t) =
        -(∫ t : ℝ in (1 : ℝ)..u, g t) := by
    rw [intervalIntegral.integral_symm]
  rw [hsymm] at hsubst
  dsimp only [g] at hsubst
  linarith

/-- Buchstab's continuous identity in the logarithmic prime coordinate. -/
theorem dickmanRho_buchstab (u : ℝ) (hu : 1 ≤ u) :
    dickmanRho u = 1 -
      ∫ s : ℝ in (1 : ℝ)..u,
        dickmanRho (u / s - 1) / s := by
  rw [dickmanRho_buchstab_integral u hu]
  exact dickmanRho_eq_one_sub_integral u hu

/-- The canonical Dickman profile is nonincreasing on its natural domain. -/
theorem antitoneOn_dickmanRho_Ici_one :
    AntitoneOn dickmanRho (Ici (1 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (D := Ici (1 : ℝ))
    (show Convex ℝ (Ici (1 : ℝ)) from convex_Ici _)
    (continuousOn_dickmanRho_Ici_zero.mono (by
      intro u hu
      change 1 ≤ u at hu
      exact zero_le_one.trans hu))
  · intro u hu
    rw [interior_Ici] at hu
    exact
      (hasDerivAt_dickmanRho hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ici] at hu
    change 1 < u at hu
    rw [(hasDerivAt_dickmanRho hu).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr
        (dickmanRho_profile.2.2.1 (u - 1) (by linarith)).le)
      (by linarith)

theorem antitoneOn_dickmanRho_Ici_zero :
    AntitoneOn dickmanRho (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  by_cases hy1 : y ≤ 1
  · rw [dickmanRho_profile.2.1 x hx (hxy.trans hy1),
      dickmanRho_profile.2.1 y hy hy1]
  · have hy1' : 1 ≤ y := le_of_not_ge hy1
    by_cases hx1 : x ≤ 1
    · rw [dickmanRho_profile.2.1 x hx hx1,
        ← dickmanRho_profile.2.1 (1 : ℝ) (by norm_num) (by norm_num)]
      exact antitoneOn_dickmanRho_Ici_one (by simp) hy1' hy1'
    · exact antitoneOn_dickmanRho_Ici_one (le_of_not_ge hx1) hy1' hxy

/-! ## Hildebrand's Dickman product bridge -/


lemma dickmanRho_eq_one_sub_log {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    dickmanRho u = 1 - Real.log u := by
  rw [dickmanRho_eq_one_sub_integral u hu1]
  congr 1
  calc
    (∫ t : ℝ in (1 : ℝ)..u, dickmanRho (t - 1) / t) =
        ∫ t : ℝ in (1 : ℝ)..u, 1 / t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hu1] at ht
      have ht0 : 0 ≤ t - 1 := sub_nonneg.mpr ht.1
      have ht1 : t - 1 ≤ 1 := by linarith [ht.2, hu2]
      change dickmanRho (t - 1) / t = 1 / t
      rw [dickmanRho_profile.2.1 (t - 1) ht0 ht1]
    _ = Real.log (u / 1) := by
      apply integral_one_div
      rw [Set.uIcc_of_le hu1]
      exact fun ht => by linarith [ht.1]
    _ = Real.log u := by rw [div_one]

lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
    Real.log_two_gt_d9

lemma dickmanRho_exp_inv_nat {q : ℕ} (hq : 2 ≤ q) :
    dickmanRho (Real.exp ((q : ℝ)⁻¹)) = 1 - (q : ℝ)⁻¹ := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hinv0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have hinvHalf : (q : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using
      (inv_le_inv₀ hqPos (by norm_num : (0 : ℝ) < 2)).2
        (by exact_mod_cast hq : (2 : ℝ) ≤ q)
  have hexp1 : 1 ≤ Real.exp ((q : ℝ)⁻¹) := by
    simpa using (Real.exp_le_exp.mpr hinv0)
  have hlog2 : (q : ℝ)⁻¹ ≤ Real.log 2 :=
    hinvHalf.trans half_lt_log_two.le
  have hexp2 : Real.exp ((q : ℝ)⁻¹) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    exact hlog2
  rw [dickmanRho_eq_one_sub_log hexp1 hexp2, Real.log_exp]

def DickmanProductInequality (ρ : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → ρ (u * v) ≤ ρ u * ρ v

def dickmanHazard (u : ℝ) : ℝ :=
  dickmanRho (u - 1) / (u * dickmanRho u)

lemma dickmanHazard_pos {u : ℝ} (hu : 1 < u) :
    0 < dickmanHazard u := by
  unfold dickmanHazard
  exact div_pos (dickmanRho_profile.2.2.1 (u - 1) (by linarith))
    (mul_pos (by linarith) (dickmanRho_profile.2.2.1 u (by linarith)))

lemma hasDerivAt_log_dickmanRho {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun x => Real.log (dickmanRho x))
      (-dickmanHazard u) u := by
  have hρ := hasDerivAt_dickmanRho hu
  have hpos := dickmanRho_profile.2.2.1 u (by linarith)
  convert hρ.log hpos.ne' using 1
  unfold dickmanHazard
  field_simp [hpos.ne']

lemma continuousAt_dickmanHazard {u : ℝ} (hu : 1 < u) :
    ContinuousAt dickmanHazard u := by
  unfold dickmanHazard
  have hnum : ContinuousAt (fun x : ℝ => dickmanRho (x - 1)) u := by
    have hshift : ContinuousAt (fun x : ℝ => x - 1) u :=
      continuousAt_id.sub continuousAt_const
    exact (continuousAt_dickmanRho_of_pos (u := u - 1) (by linarith)).comp_of_eq
      hshift rfl
  exact hnum.div
    (continuousAt_id.mul (continuousAt_dickmanRho_of_pos (by linarith)))
    (mul_ne_zero (by linarith) (ne_of_gt
      (dickmanRho_profile.2.2.1 u (by linarith))))

lemma hasDerivAt_dickmanHazard {u : ℝ} (hu : 2 < u) :
    HasDerivAt dickmanHazard
      (dickmanHazard u *
        (dickmanHazard u - dickmanHazard (u - 1) - u⁻¹)) u := by
  have hρu := hasDerivAt_dickmanRho (by linarith : 1 < u)
  have hρprev := (hasDerivAt_dickmanRho (by linarith : 1 < u - 1)).comp u
    ((hasDerivAt_id' u).sub_const 1)
  have hupos : 0 < u := by linarith
  have hρupos := dickmanRho_profile.2.2.1 u hupos.le
  have hρprevpos := dickmanRho_profile.2.2.1 (u - 1) (by linarith)
  have huprevne : u - 1 ≠ 0 := by linarith
  have hraw := hρprev.div
      ((hasDerivAt_id' u).mul hρu)
      (mul_ne_zero hupos.ne' hρupos.ne')
  unfold dickmanHazard
  apply hraw.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply, mul_one, one_mul]
  rw [inv_eq_one_div]
  field_simp [hupos.ne', huprevne, hρupos.ne', hρprevpos.ne']
  ring

lemma deriv_dickmanHazard {u : ℝ} (hu : 2 < u) :
    deriv dickmanHazard u =
      dickmanHazard u *
        (dickmanHazard u - dickmanHazard (u - 1) - u⁻¹) :=
  (hasDerivAt_dickmanHazard hu).deriv

lemma dickmanHazard_eq_base {u : ℝ} (hu1 : 1 < u) (hu2 : u ≤ 2) :
    dickmanHazard u = (u * (1 - Real.log u))⁻¹ := by
  have huprev0 : 0 ≤ u - 1 := by linarith
  have huprev1 : u - 1 ≤ 1 := by linarith
  rw [dickmanHazard, dickmanRho_profile.2.1 (u - 1) huprev0 huprev1,
    dickmanRho_eq_one_sub_log hu1.le hu2]
  simp only [one_div]

lemma dickmanHazard_eq_base_closed {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    dickmanHazard u = (u * (1 - Real.log u))⁻¹ := by
  have huprev0 : 0 ≤ u - 1 := by linarith
  have huprev1 : u - 1 ≤ 1 := by linarith
  rw [dickmanHazard, dickmanRho_profile.2.1 (u - 1) huprev0 huprev1,
    dickmanRho_eq_one_sub_log hu1 hu2]
  simp only [one_div]

lemma hasDerivAt_dickmanHazard_base {u : ℝ} (hu1 : 1 < u) (hu2 : u < 2) :
    HasDerivAt dickmanHazard
      (Real.log u / (u * (1 - Real.log u)) ^ 2) u := by
  have hloglt : Real.log u < 1 := by
    have hlu := Real.log_lt_sub_one_of_pos (by linarith : 0 < u) (by linarith : u ≠ 1)
    linarith
  have hden : u * (1 - Real.log u) ≠ 0 :=
    mul_ne_zero (by linarith) (by linarith)
  have hevent : dickmanHazard =ᶠ[nhds u]
      fun x : ℝ => (x * (1 - Real.log x))⁻¹ := by
    filter_upwards [Ioo_mem_nhds hu1 hu2] with x hx
    exact dickmanHazard_eq_base hx.1 hx.2.le
  have hinnerRaw := (hasDerivAt_id' u).mul
    ((hasDerivAt_const u 1).sub (Real.hasDerivAt_log (by linarith)))
  have hinner : HasDerivAt (fun x : ℝ => x * (1 - Real.log x))
      (-Real.log u) u := by
    apply hinnerRaw.congr_deriv
    simp only [Pi.sub_apply, one_mul]
    change (1 - Real.log u) + u * (0 - u⁻¹) = -Real.log u
    rw [mul_sub, mul_zero, mul_inv_cancel₀ (show u ≠ 0 by linarith)]
    ring
  have hinv := hinner.inv hden
  apply (hinv.congr_deriv ?_).congr_of_eventuallyEq hevent
  ring

lemma deriv_dickmanHazard_base_pos {u : ℝ} (hu1 : 1 < u) (hu2 : u < 2) :
    0 < deriv dickmanHazard u := by
  rw [(hasDerivAt_dickmanHazard_base hu1 hu2).deriv]
  have hlog : 0 < Real.log u := Real.log_pos hu1
  have hloglt := Real.log_lt_sub_one_of_pos
    (by linarith : 0 < u) (by linarith : u ≠ 1)
  exact div_pos hlog (sq_pos_of_pos (mul_pos (by linarith) (by linarith)))

def dickmanHazardGap (u : ℝ) : ℝ :=
  dickmanHazard u - dickmanHazard (u - 1) - u⁻¹

lemma dickmanHazardGap_two_pos : 0 < dickmanHazardGap 2 := by
  unfold dickmanHazardGap
  rw [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [dickmanHazard_eq_base_closed (u := 2) (by norm_num) (by norm_num),
    dickmanHazard_eq_base_closed (u := 1) (by norm_num) (by norm_num)]
  norm_num [Real.log_one]
  have hloglt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hden : 0 < (2 : ℝ) * (1 - Real.log 2) := by positivity
  have hloggt : (2 / 3 : ℝ) < Real.log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hinv : (3 / 2 : ℝ) < ((2 : ℝ) * (1 - Real.log 2))⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hden]
    nlinarith
  have heq : (1 - Real.log 2)⁻¹ * (1 / 2 : ℝ) =
      ((2 : ℝ) * (1 - Real.log 2))⁻¹ := by
    rw [mul_inv_rev]
    norm_num
  rw [heq]
  linarith

lemma continuousOn_dickmanHazard_Icc_one_two :
    ContinuousOn dickmanHazard (Icc (1 : ℝ) 2) := by
  have hcont : ContinuousOn
      (fun u : ℝ => (u * (1 - Real.log u))⁻¹) (Icc (1 : ℝ) 2) := by
    intro u hu
    have huPos : 0 < u := by linarith [hu.1]
    have hloglt : Real.log u < 1 := by
      have hlu : Real.log u ≤ Real.log 2 := by
        exact Real.log_le_log huPos hu.2
      exact hlu.trans_lt (Real.log_two_lt_d9.trans (by norm_num))
    have hden : u * (1 - Real.log u) ≠ 0 := by
      apply mul_ne_zero huPos.ne'
      linarith
    exact ((continuousAt_id.mul
      (continuousAt_const.sub (Real.continuousAt_log huPos.ne'))).inv₀
        hden).continuousWithinAt
  exact hcont.congr fun u hu => dickmanHazard_eq_base_closed hu.1 hu.2

lemma strictMonoOn_dickmanHazard_Icc_one_two :
    StrictMonoOn dickmanHazard (Icc (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (1 : ℝ) 2)
    continuousOn_dickmanHazard_Icc_one_two
  intro u hu
  rw [interior_Icc] at hu
  exact deriv_dickmanHazard_base_pos hu.1 hu.2

lemma continuousOn_dickmanHazardGap_Ici_two :
    ContinuousOn dickmanHazardGap (Ici (2 : ℝ)) := by
  intro u hu
  by_cases hu2 : u = 2
  · subst u
    have hmodel : ContinuousAt (fun x : ℝ =>
        dickmanHazard x -
          ((x - 1) * (1 - Real.log (x - 1)))⁻¹ - x⁻¹) 2 := by
      have hshift : ContinuousAt (fun x : ℝ => x - 1) 2 :=
        continuousAt_id.sub continuousAt_const
      have hlogShift : ContinuousAt (fun x : ℝ => Real.log (x - 1)) 2 :=
        (Real.continuousAt_log (by norm_num : (2 - 1 : ℝ) ≠ 0)).comp_of_eq
          hshift rfl
      have hbaseTerm : ContinuousAt (fun x : ℝ =>
          ((x - 1) * (1 - Real.log (x - 1)))⁻¹) 2 := by
        apply (hshift.mul (continuousAt_const.sub hlogShift)).inv₀
        norm_num [Real.log_one]
      exact ((continuousAt_dickmanHazard (by norm_num)).sub hbaseTerm).sub
        (continuousAt_id.inv₀ (by norm_num))
    have heq : dickmanHazardGap =ᶠ[nhdsWithin 2 (Ici (2 : ℝ))]
        (fun x : ℝ => dickmanHazard x -
          ((x - 1) * (1 - Real.log (x - 1)))⁻¹ - x⁻¹) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (show (2 : ℝ) < 3 by norm_num))] with x hx hx3
      have hx2 : (2 : ℝ) ≤ x := hx
      have hx3' : x < (3 : ℝ) := hx3
      unfold dickmanHazardGap
      rw [dickmanHazard_eq_base_closed (u := x - 1)
        (by linarith) (by linarith)]
    apply hmodel.continuousWithinAt.congr_of_eventuallyEq heq
    unfold dickmanHazardGap
    rw [show (2 : ℝ) - 1 = 1 by norm_num]
    rw [dickmanHazard_eq_base_closed (u := 1) (by norm_num) (by norm_num)]
  · have huGt : 2 < u := lt_of_le_of_ne hu (Ne.symm hu2)
    unfold dickmanHazardGap
    have hshift : ContinuousAt (fun x : ℝ => x - 1) u :=
      continuousAt_id.sub continuousAt_const
    have hprev : ContinuousAt (fun x : ℝ => dickmanHazard (x - 1)) u :=
      (continuousAt_dickmanHazard (u := u - 1) (by linarith)).comp_of_eq
        hshift rfl
    have hinv : ContinuousAt (fun x : ℝ => x⁻¹) u :=
      (continuousAt_id.inv₀ (show id u ≠ 0 by simpa only [id_eq] using
        (show u ≠ 0 by linarith)))
    exact (((continuousAt_dickmanHazard (by linarith : 1 < u)).sub hprev).sub
      hinv).continuousWithinAt

def dickmanHazardReciprocal (u : ℝ) : ℝ :=
  u * dickmanRho u / dickmanRho (u - 1)

lemma dickmanHazardReciprocal_pos {u : ℝ} (hu : 1 < u) :
    0 < dickmanHazardReciprocal u := by
  unfold dickmanHazardReciprocal
  exact div_pos
    (mul_pos (by linarith) (dickmanRho_profile.2.2.1 u (by linarith)))
    (dickmanRho_profile.2.2.1 (u - 1) (by linarith))

lemma dickmanHazard_inv_eq_reciprocal {u : ℝ} (hu : 1 < u) :
    (dickmanHazard u)⁻¹ = dickmanHazardReciprocal u := by
  have hu0 : u ≠ 0 := by linarith
  have hρu : dickmanRho u ≠ 0 :=
    (dickmanRho_profile.2.2.1 u (by linarith)).ne'
  have hρprev : dickmanRho (u - 1) ≠ 0 :=
    (dickmanRho_profile.2.2.1 (u - 1) (by linarith)).ne'
  unfold dickmanHazard dickmanHazardReciprocal
  field_simp

lemma hasDerivAt_dickmanHazardReciprocal {u : ℝ} (hu : 2 < u) :
    HasDerivAt dickmanHazardReciprocal
      (((dickmanRho u - dickmanRho (u - 1)) * dickmanRho (u - 1) -
          u * dickmanRho u *
            (-dickmanRho (u - 2) / (u - 1))) /
        (dickmanRho (u - 1)) ^ 2) u := by
  have hρu := hasDerivAt_dickmanRho (by linarith : 1 < u)
  have hnum := (hasDerivAt_id' u).mul hρu
  have hρprev := (hasDerivAt_dickmanRho (by linarith : 1 < u - 1)).comp u
    ((hasDerivAt_id' u).sub_const 1)
  have hρprevne : dickmanRho (u - 1) ≠ 0 :=
    (dickmanRho_profile.2.2.1 (u - 1) (by linarith)).ne'
  unfold dickmanHazardReciprocal
  apply (hnum.div hρprev hρprevne).congr_deriv
  simp only [Function.comp_apply, mul_one]
  congr 3
  · field_simp [show u ≠ 0 by linarith]
    ring
  · congr 2
    ring_nf

def dickmanHazardDriftIntegrand (u t : ℝ) : ℝ :=
  (dickmanRho (u - t) / dickmanRho (u - 1)) *
    (dickmanHazard (u - 1) - dickmanHazard (u - t))

lemma continuousOn_dickmanHazardDriftIntegrand {u : ℝ} (hu : 2 < u) :
    ContinuousOn (dickmanHazardDriftIntegrand u) (Icc 0 1) := by
  intro t ht
  have hut : 1 < u - t := by linarith [ht.2]
  unfold dickmanHazardDriftIntegrand
  have hshift : ContinuousAt (fun s : ℝ => u - s) t :=
    continuousAt_const.sub continuousAt_id
  have hρshift : ContinuousAt (fun s : ℝ => dickmanRho (u - s)) t :=
    (continuousAt_dickmanRho_of_pos (u := u - t) (by linarith)).comp_of_eq
      hshift rfl
  have hhshift : ContinuousAt (fun s : ℝ => dickmanHazard (u - s)) t :=
    (continuousAt_dickmanHazard hut).comp_of_eq hshift rfl
  exact ((hρshift.div_const _).mul
    (continuousAt_const.sub hhshift)).continuousWithinAt

lemma deriv_dickmanHazardReciprocal_eq_integral {u : ℝ} (hu : 2 < u) :
    deriv dickmanHazardReciprocal u =
      ∫ t : ℝ in (0 : ℝ)..1, dickmanHazardDriftIntegrand u t := by
  rw [(hasDerivAt_dickmanHazardReciprocal hu).deriv]
  have hu0 : u ≠ 0 := by linarith
  have huprev0 : u - 1 ≠ 0 := by linarith
  have hρu : dickmanRho u ≠ 0 :=
    (dickmanRho_profile.2.2.1 u (by linarith)).ne'
  have hρprev : dickmanRho (u - 1) ≠ 0 :=
    (dickmanRho_profile.2.2.1 (u - 1) (by linarith)).ne'
  have hFTC :
      (∫ t : ℝ in (0 : ℝ)..1,
        dickmanRho (u - t - 1) / (u - t)) =
          dickmanRho (u - 1) - dickmanRho u := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => dickmanRho (u - s))
          (dickmanRho (u - t - 1) / (u - t)) t := by
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      have hut : 1 < u - t := by linarith [ht.2]
      have h := (hasDerivAt_dickmanRho hut).comp t
        ((hasDerivAt_const t u).sub (hasDerivAt_id' t))
      apply h.congr_deriv
      ring
    have hint : IntervalIntegrable
        (fun t : ℝ => dickmanRho (u - t - 1) / (u - t)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by norm_num)]
      intro t ht
      have hut : 1 < u - t := by linarith [ht.2]
      have hnumShift :
          ContinuousAt (fun s : ℝ => dickmanRho (u - s - 1)) t := by
        have hs : ContinuousAt (fun s : ℝ => u - s - 1) t :=
          (continuousAt_const.sub continuousAt_id).sub continuousAt_const
        exact (continuousAt_dickmanRho_of_pos (u := u - t - 1)
          (by linarith)).comp_of_eq hs rfl
      have hdenShift : ContinuousAt (fun s : ℝ => u - s) t :=
        continuousAt_const.sub continuousAt_id
      exact (hnumShift.div hdenShift (by
        change u - t ≠ 0
        linarith)).continuousWithinAt
    simpa only [sub_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hIntRho :
      (∫ t : ℝ in (0 : ℝ)..1, dickmanRho (u - t)) =
        u * dickmanRho u := by
    have hdelay := dickmanRho_profile.2.2.2.2 u (by linarith : 1 ≤ u)
    rw [← hdelay]
    rw [intervalIntegral.integral_comp_sub_left dickmanRho u]
    norm_num
  have hcontRho : IntervalIntegrable (fun t : ℝ => dickmanRho (u - t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    intro t ht
    have hshift : ContinuousAt (fun s : ℝ => u - s) t :=
      continuousAt_const.sub continuousAt_id
    exact ((continuousAt_dickmanRho_of_pos (u := u - t) (by linarith [ht.2])).comp_of_eq
      hshift rfl).continuousWithinAt
  have hcontKernel : IntervalIntegrable
      (fun t : ℝ => dickmanRho (u - t - 1) / (u - t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    intro t ht
    have hut : 1 < u - t := by linarith [ht.2]
    have hnumShift :
        ContinuousAt (fun s : ℝ => dickmanRho (u - s - 1)) t := by
      have hs : ContinuousAt (fun s : ℝ => u - s - 1) t :=
        (continuousAt_const.sub continuousAt_id).sub continuousAt_const
      exact (continuousAt_dickmanRho_of_pos (u := u - t - 1)
        (by linarith)).comp_of_eq hs rfl
    have hdenShift : ContinuousAt (fun s : ℝ => u - s) t :=
      continuousAt_const.sub continuousAt_id
    exact (hnumShift.div hdenShift (by
      change u - t ≠ 0
      linarith)).continuousWithinAt
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dickmanHazardDriftIntegrand u t =
        (dickmanHazard (u - 1) / dickmanRho (u - 1)) *
            dickmanRho (u - t) -
          (dickmanRho (u - 1))⁻¹ *
            (dickmanRho (u - t - 1) / (u - t)) := by
    have hut : 1 < u - t := by linarith [ht.2]
    have hut0 : u - t ≠ 0 := by linarith
    have hρut : dickmanRho (u - t) ≠ 0 :=
      (dickmanRho_profile.2.2.1 (u - t) (by linarith)).ne'
    unfold dickmanHazardDriftIntegrand dickmanHazard
    field_simp [hρprev, hρut, hut0]
  rw [show (∫ t : ℝ in (0 : ℝ)..1, dickmanHazardDriftIntegrand u t) =
      ∫ t : ℝ in (0 : ℝ)..1,
        (dickmanHazard (u - 1) / dickmanRho (u - 1)) *
            dickmanRho (u - t) -
          (dickmanRho (u - 1))⁻¹ *
            (dickmanRho (u - t - 1) / (u - t)) by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      exact hpoint t ht]
  rw [intervalIntegral.integral_sub
      (hcontRho.const_mul _) (hcontKernel.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hIntRho, hFTC]
  unfold dickmanHazard
  field_simp [hu0, huprev0, hρu, hρprev]
  have harg : u - 1 - 1 = u - 2 := by ring
  rw [harg]
  ring

lemma deriv_dickmanHazardReciprocal_neg_of_strict
    {u : ℝ} (hu : 2 < u)
    (hmono : ∀ x : ℝ, u - 1 < x → x < u →
      dickmanHazard (u - 1) < dickmanHazard x) :
    deriv dickmanHazardReciprocal u < 0 := by
  rw [deriv_dickmanHazardReciprocal_eq_integral hu]
  have hcont := continuousOn_dickmanHazardDriftIntegrand hu
  have hneg : 0 < ∫ t : ℝ in (0 : ℝ)..1,
      -dickmanHazardDriftIntegrand u t := by
    have hcontNeg : ContinuousOn (fun t : ℝ =>
        -dickmanHazardDriftIntegrand u t) (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact hcont.neg
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      hcontNeg.intervalIntegrable
    · intro t ht
      have hut : u - 1 < u - t := by linarith [ht.2]
      have htu : u - t < u := by linarith [ht.1]
      have hratio : 0 < dickmanRho (u - t) / dickmanRho (u - 1) :=
        div_pos (dickmanRho_profile.2.2.1 (u - t) (by linarith))
          (dickmanRho_profile.2.2.1 (u - 1) (by linarith))
      unfold dickmanHazardDriftIntegrand
      have := hmono (u - t) hut htu
      nlinarith
    · norm_num
  rw [intervalIntegral.integral_neg] at hneg
  linarith

lemma deriv_dickmanHazard_pos_of_strict
    {u : ℝ} (hu : 2 < u)
    (hmono : ∀ x : ℝ, u - 1 < x → x < u →
      dickmanHazard (u - 1) < dickmanHazard x) :
    0 < deriv dickmanHazard u := by
  have hD := hasDerivAt_dickmanHazardReciprocal hu
  have hDneg := deriv_dickmanHazardReciprocal_neg_of_strict hu hmono
  have hDpos := dickmanHazardReciprocal_pos (by linarith : 1 < u)
  have hinv := hD.inv hDpos.ne'
  have hevent : dickmanHazard =ᶠ[nhds u]
      fun x : ℝ => (dickmanHazardReciprocal x)⁻¹ := by
    filter_upwards [Ioi_mem_nhds (show 1 < u by linarith)] with x hx
    rw [← dickmanHazard_inv_eq_reciprocal hx, inv_inv]
  have hderiv : deriv dickmanHazard u =
      -deriv dickmanHazardReciprocal u /
        (dickmanHazardReciprocal u) ^ 2 := by
    have hh := (hinv.congr_of_eventuallyEq hevent).deriv
    rw [← hD.deriv] at hh
    exact hh
  rw [hderiv]
  exact div_pos (neg_pos.mpr hDneg) (sq_pos_of_pos hDpos)

lemma dickmanHazardGap_pos {u : ℝ} (hu : 2 < u) :
    0 < dickmanHazardGap u := by
  by_contra hnot
  have hgapLe : dickmanHazardGap u ≤ 0 := le_of_not_gt hnot
  let S : Set ℝ := Icc (2 : ℝ) u ∩ dickmanHazardGap ⁻¹' Iic 0
  have hSne : S.Nonempty := by
    refine ⟨u, ?_⟩
    exact ⟨⟨hu.le, le_rfl⟩, hgapLe⟩
  have hcontGap : ContinuousOn dickmanHazardGap (Icc (2 : ℝ) u) :=
    continuousOn_dickmanHazardGap_Ici_two.mono (Icc_subset_Ici_self)
  have hSclosed : IsClosed S := by
    exact hcontGap.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSbdd : BddBelow S := by
    refine ⟨2, ?_⟩
    intro x hx
    exact hx.1.1
  let s : ℝ := sInf S
  have hsMem : s ∈ S := by
    exact hSclosed.csInf_mem hSne hSbdd
  have hsTwo : 2 ≤ s := hsMem.1.1
  have hsU : s ≤ u := hsMem.1.2
  have hsGapLe : dickmanHazardGap s ≤ 0 := hsMem.2
  have hsGt : 2 < s := by
    apply lt_of_le_of_ne hsTwo
    intro hsEq
    have : dickmanHazardGap s = dickmanHazardGap 2 := congrArg _ hsEq.symm
    linarith [dickmanHazardGap_two_pos]
  have hprior : ∀ x : ℝ, 2 < x → x < s → 0 < dickmanHazardGap x := by
    intro x hxTwo hxS
    by_contra hxNot
    have hxGapLe : dickmanHazardGap x ≤ 0 := le_of_not_gt hxNot
    have hxMem : x ∈ S := by
      exact ⟨⟨hxTwo.le, (hxS.le.trans hsU)⟩, hxGapLe⟩
    have hsLeX : s ≤ x := csInf_le hSbdd hxMem
    linarith
  have hcontUpper : ContinuousOn dickmanHazard (Icc (2 : ℝ) s) := by
    intro x hx
    exact (continuousAt_dickmanHazard (by linarith [hx.1])).continuousWithinAt
  have hupper : StrictMonoOn dickmanHazard (Icc (2 : ℝ) s) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (2 : ℝ) s) hcontUpper
    intro x hx
    rw [interior_Icc] at hx
    rw [deriv_dickmanHazard hx.1]
    change 0 < dickmanHazard x * dickmanHazardGap x
    exact mul_pos (dickmanHazard_pos (u := x) (by linarith [hx.1]))
      (hprior x hx.1 hx.2)
  have hlocal : ∀ x : ℝ, s - 1 < x → x < s →
      dickmanHazard (s - 1) < dickmanHazard x := by
    intro x hax hxs
    have haOne : 1 < s - 1 := by linarith
    have hxOne : 1 < x := haOne.trans hax
    by_cases hxTwoLe : x ≤ 2
    · exact strictMonoOn_dickmanHazard_Icc_one_two
        ⟨haOne.le, hax.le.trans hxTwoLe⟩ ⟨hxOne.le, hxTwoLe⟩ hax
    · have hxTwo : 2 < x := lt_of_not_ge hxTwoLe
      have hxUpper : x ∈ Icc (2 : ℝ) s := ⟨hxTwo.le, hxs.le⟩
      have htwoUpper : (2 : ℝ) ∈ Icc (2 : ℝ) s := ⟨le_rfl, hsTwo⟩
      by_cases haTwoLe : s - 1 ≤ 2
      · by_cases haEq : s - 1 = 2
        · simpa only [haEq] using hupper htwoUpper hxUpper hxTwo
        · have haTwo : s - 1 < 2 := lt_of_le_of_ne haTwoLe haEq
          have hbase := strictMonoOn_dickmanHazard_Icc_one_two
            ⟨haOne.le, haTwo.le⟩ ⟨by norm_num, by norm_num⟩ haTwo
          exact hbase.trans (hupper htwoUpper hxUpper hxTwo)
      · have htwoA : 2 < s - 1 := lt_of_not_ge haTwoLe
        exact hupper ⟨htwoA.le, by linarith⟩ hxUpper hax
  have hderivPos := deriv_dickmanHazard_pos_of_strict hsGt hlocal
  rw [deriv_dickmanHazard hsGt] at hderivPos
  change 0 < dickmanHazard s * dickmanHazardGap s at hderivPos
  have hhpos := dickmanHazard_pos (by linarith : 1 < s)
  nlinarith

lemma strictMonoOn_dickmanHazard_Ici_two :
    StrictMonoOn dickmanHazard (Ici (2 : ℝ)) := by
  have hcont : ContinuousOn dickmanHazard (Ici (2 : ℝ)) := by
    intro u hu
    have huTwo : (2 : ℝ) ≤ u := hu
    exact (continuousAt_dickmanHazard (by linarith)).continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ici (2 : ℝ)) hcont
  intro u hu
  rw [interior_Ici] at hu
  have huTwo : (2 : ℝ) < u := hu
  rw [deriv_dickmanHazard hu]
  change 0 < dickmanHazard u * dickmanHazardGap u
  exact mul_pos (dickmanHazard_pos (by linarith))
    (dickmanHazardGap_pos huTwo)

lemma strictMonoOn_dickmanHazard_Ioi_one :
    StrictMonoOn dickmanHazard (Ioi (1 : ℝ)) := by
  intro x hx y hy hxy
  by_cases hyTwo : y ≤ 2
  · exact strictMonoOn_dickmanHazard_Icc_one_two
      ⟨hx.le, hxy.le.trans hyTwo⟩ ⟨hy.le, hyTwo⟩ hxy
  · have hyGt : 2 < y := lt_of_not_ge hyTwo
    have hyMem : y ∈ Ici (2 : ℝ) := hyGt.le
    by_cases hxTwo : x < 2
    · have hbase := strictMonoOn_dickmanHazard_Icc_one_two
        ⟨hx.le, hxTwo.le⟩ ⟨by norm_num, by norm_num⟩ hxTwo
      have htwoMem : (2 : ℝ) ∈ Ici (2 : ℝ) := by norm_num
      have hupp := strictMonoOn_dickmanHazard_Ici_two
        htwoMem hyMem hyGt
      exact hbase.trans hupp
    · have hxMem : x ∈ Ici (2 : ℝ) := le_of_not_gt hxTwo
      exact strictMonoOn_dickmanHazard_Ici_two hxMem hyMem hxy

def dickmanLogRatio (u v : ℝ) : ℝ :=
  Real.log (dickmanRho (u * v)) - Real.log (dickmanRho v)

lemma continuousOn_dickmanLogRatio_Ici_one {u : ℝ} (hu : 1 < u) :
    ContinuousOn (dickmanLogRatio u) (Ici (1 : ℝ)) := by
  intro v hv
  have hvOne : (1 : ℝ) ≤ v := hv
  have hvPos : 0 < v := by linarith
  have huvPos : 0 < u * v := mul_pos (by linarith) hvPos
  have hmul : ContinuousAt (fun x : ℝ => u * x) v :=
    continuousAt_const.mul continuousAt_id
  have hρmul : ContinuousAt (fun x : ℝ => dickmanRho (u * x)) v :=
    (continuousAt_dickmanRho_of_pos (u := u * v) huvPos).comp_of_eq
      hmul rfl
  have hρv : ContinuousAt dickmanRho v :=
    continuousAt_dickmanRho_of_pos hvPos
  unfold dickmanLogRatio
  exact (hρmul.log (dickmanRho_profile.2.2.1 (u * v) huvPos.le).ne').sub
    (hρv.log (dickmanRho_profile.2.2.1 v hvPos.le).ne') |>.continuousWithinAt

lemma hasDerivAt_dickmanLogRatio {u v : ℝ} (hu : 1 < u) (hv : 1 < v) :
    HasDerivAt (dickmanLogRatio u)
      (dickmanHazard v - u * dickmanHazard (u * v)) v := by
  have hvPos : 0 < v := by linarith
  have huv : 1 < u * v := by nlinarith
  have hmul : HasDerivAt (fun x : ℝ => u * x) u v := by
    simpa only [mul_one] using (hasDerivAt_id' v).const_mul u
  have hleft := (hasDerivAt_log_dickmanRho huv).comp v hmul
  have hright := hasDerivAt_log_dickmanRho hv
  unfold dickmanLogRatio
  apply (hleft.sub hright).congr_deriv
  ring

lemma strictAntiOn_dickmanLogRatio_Ici_one {u : ℝ} (hu : 1 < u) :
    StrictAntiOn (dickmanLogRatio u) (Ici (1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ))
    (continuousOn_dickmanLogRatio_Ici_one hu)
  intro v hv
  rw [interior_Ici] at hv
  have hvOne : (1 : ℝ) < v := hv
  rw [(hasDerivAt_dickmanLogRatio hu hvOne).deriv]
  have huv : 1 < u * v := by nlinarith
  have hvuv : v < u * v := by nlinarith
  have hhaz := strictMonoOn_dickmanHazard_Ioi_one hvOne huv hvuv
  have hscale : dickmanHazard (u * v) < u * dickmanHazard (u * v) :=
    lt_mul_of_one_lt_left (dickmanHazard_pos huv) hu
  linarith

theorem dickmanProductInequality : DickmanProductInequality dickmanRho := by
  intro u v hu hv
  rcases hu.eq_or_lt with rfl | huGt
  · have hρone : dickmanRho 1 = 1 :=
      dickmanRho_profile.2.1 1 (by norm_num) (by norm_num)
    simp [hρone]
  rcases hv.eq_or_lt with rfl | hvGt
  · have hρone : dickmanRho 1 = 1 :=
      dickmanRho_profile.2.1 1 (by norm_num) (by norm_num)
    simp [hρone]
  have honeMem : (1 : ℝ) ∈ Ici (1 : ℝ) := by norm_num
  have hvMem : v ∈ Ici (1 : ℝ) := hv
  have hratio := strictAntiOn_dickmanLogRatio_Ici_one huGt
    honeMem hvMem hvGt
  have hρone : dickmanRho 1 = 1 :=
    dickmanRho_profile.2.1 1 (by norm_num) (by norm_num)
  unfold dickmanLogRatio at hratio
  rw [mul_one, hρone, Real.log_one, sub_zero] at hratio
  have hlog : Real.log (dickmanRho (u * v)) ≤
      Real.log (dickmanRho u) + Real.log (dickmanRho v) := by
    linarith
  have hρu := dickmanRho_profile.2.2.1 u (by linarith : 0 ≤ u)
  have hρv := dickmanRho_profile.2.2.1 v (by linarith : 0 ≤ v)
  have hρuv := dickmanRho_profile.2.2.1 (u * v)
    (mul_nonneg (by linarith) (by linarith))
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hρuv, Real.exp_add, Real.exp_log hρu,
    Real.exp_log hρv] at hexp
  exact hexp

lemma periodicDensity_eq_prod_dickmanRho_exp_inv {A : Finset ℕ}
    (hA : ∀ a ∈ A, 2 ≤ a) :
    periodicDensity A =
      ∏ a ∈ A, dickmanRho (Real.exp ((a : ℝ)⁻¹)) := by
  unfold periodicDensity
  apply Finset.prod_congr rfl
  intro a ha
  exact (dickmanRho_exp_inv_nat (hA a ha)).symm

lemma prod_dickmanRho_ge_exp_sum
    (hprod : DickmanProductInequality dickmanRho)
    (A : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ a ∈ A, 0 ≤ w a) :
    dickmanRho (Real.exp (∑ a ∈ A, w a)) ≤
      ∏ a ∈ A, dickmanRho (Real.exp (w a)) := by
  induction A using Finset.induction_on with
  | empty =>
      simp [dickmanRho_profile.2.1]
  | @insert a A ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Real.exp_add]
      have hu : 1 ≤ Real.exp (∑ x ∈ A, w x) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (Finset.sum_nonneg fun x hx => hw x (by simp [hx]))
      have hv : 1 ≤ Real.exp (w a) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (hw a (by simp))
      have ih' := ih (fun x hx => hw x (by simp [hx]))
      exact (hprod _ _ hv hu).trans
        (mul_le_mul_of_nonneg_left ih' (dickmanRho_nonneg
          (Real.exp_pos _).le))

lemma periodicDensity_mul_dickmanRho_ge
    (hprod : DickmanProductInequality dickmanRho)
    {A : Finset ℕ} (hA : ∀ a ∈ A, 2 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    dickmanRho (Real.exp (reciprocalMass A + x)) ≤
      periodicDensity A * dickmanRho (Real.exp x) := by
  have hfinite := prod_dickmanRho_ge_exp_sum hprod A
    (fun a => (a : ℝ)⁻¹) (fun _a _ha => by positivity)
  have hu : 1 ≤ Real.exp (reciprocalMass A) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (reciprocalMass_nonneg A)
  have hv : 1 ≤ Real.exp x := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hx
  rw [Real.exp_add]
  calc
    dickmanRho (Real.exp (reciprocalMass A) * Real.exp x) ≤
        dickmanRho (Real.exp (reciprocalMass A)) *
          dickmanRho (Real.exp x) := hprod _ _ hu hv
    _ ≤ (∏ a ∈ A, dickmanRho (Real.exp ((a : ℝ)⁻¹))) *
          dickmanRho (Real.exp x) :=
      mul_le_mul_of_nonneg_right hfinite
        (dickmanRho_nonneg (Real.exp_pos _).le)
    _ = periodicDensity A * dickmanRho (Real.exp x) := by
      rw [← periodicDensity_eq_prod_dickmanRho_exp_inv hA]


/-! ## Dickman prime quadrature -/

/-- The clamped Dickman statistic used in the Buchstab prime sum.  Clamping
makes it globally monotone without changing it on `(y,x]`. -/
def dickmanBuchstabStatistic (x y k : ℕ) : ℝ :=
  dickmanRho
    (Real.log (x : ℝ) /
        Real.log (max y (min k x) : ℕ) - 1)

def realDickmanBuchstabStatistic (x : ℕ) (t : ℝ) : ℝ :=
  dickmanRho (Real.log (x : ℝ) / Real.log t - 1)

theorem dickmanBuchstabStatistic_eq
    {x y k : ℕ} (hyk : y ≤ k) (hkx : k ≤ x) :
    dickmanBuchstabStatistic x y k =
      dickmanRho
        (Real.log (x : ℝ) / Real.log (k : ℝ) - 1) := by
  simp [dickmanBuchstabStatistic, min_eq_left hkx,
    max_eq_right hyk]

theorem monotoneOn_realDickmanBuchstabStatistic
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) :
    MonotoneOn (realDickmanBuchstabStatistic x)
      (Set.Icc (y : ℝ) x) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogX : 0 < Real.log (x : ℝ) :=
    Real.log_pos (hyOne.trans_le (by exact_mod_cast hyx))
  intro s hs t ht hst
  have hsPos : 0 < s := hyPos.trans_le hs.1
  have htPos : 0 < t := hsPos.trans_le hst
  have hlogS : 0 < Real.log s :=
    Real.log_pos (hyOne.trans_le hs.1)
  have hlogT : 0 < Real.log t :=
    Real.log_pos (hyOne.trans_le ht.1)
  have hlogST : Real.log s ≤ Real.log t :=
    Real.log_le_log hsPos hst
  have hquotient :
      Real.log (x : ℝ) / Real.log t ≤
        Real.log (x : ℝ) / Real.log s :=
    div_le_div_of_nonneg_left hlogX.le hlogS hlogST
  have hargS :
      0 ≤ Real.log (x : ℝ) / Real.log s - 1 := by
    rw [sub_nonneg, one_le_div hlogS]
    exact Real.log_le_log hsPos (by exact_mod_cast hs.2)
  have hargT :
      0 ≤ Real.log (x : ℝ) / Real.log t - 1 := by
    rw [sub_nonneg, one_le_div hlogT]
    exact Real.log_le_log htPos (by exact_mod_cast ht.2)
  apply antitoneOn_dickmanRho_Ici_zero hargT hargS
  linarith

theorem dickmanBuchstabStatistic_eq_real
    {x y k : ℕ} (hyk : y ≤ k) (hkx : k ≤ x) :
    dickmanBuchstabStatistic x y k =
      realDickmanBuchstabStatistic x k := by
  exact dickmanBuchstabStatistic_eq hyk hkx

theorem intervalIntegrable_realDickmanBuchstabKernel
    {x y : ℕ} {a b : ℝ}
    (hy : 3 ≤ y) (hya : (y : ℝ) ≤ a)
    (hab : a ≤ b) (hbx : b ≤ (x : ℝ)) :
    IntervalIntegrable
      (fun t : ℝ ↦
        realDickmanBuchstabStatistic x t *
          (t⁻¹ / Real.log t))
      volume a b := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hbase :
      IntervalIntegrable
        (fun t : ℝ ↦ t⁻¹ / Real.log t)
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have htOne : 1 < t := hyOne.trans_le (hya.trans ht.1)
    have htPos : 0 < t := zero_lt_one.trans htOne
    have hlogt : Real.log t ≠ 0 := (Real.log_pos htOne).ne'
    exact
      (continuousAt_inv₀ htPos.ne').div
        (Real.continuousAt_log htPos.ne') hlogt |>.continuousWithinAt
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ ↦
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t))
        (volume.restrict (Set.uIoc a b)) := by
    apply Measurable.aestronglyMeasurable
    unfold realDickmanBuchstabStatistic
    exact
      (measurable_dickmanRho.comp
        (measurable_const.div Real.measurable_log |>.sub
          measurable_const)).mul
        (measurable_inv.div Real.measurable_log)
  apply hbase.mono_fun hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le hab] at ht
  have htLower : (y : ℝ) ≤ t := hya.trans ht.1.le
  have htUpper : t ≤ (x : ℝ) := ht.2.trans hbx
  have htOne : 1 < t := hyOne.trans_le htLower
  have htPos : 0 < t := zero_lt_one.trans htOne
  have hlogt : 0 < Real.log t := Real.log_pos htOne
  have harg :
      0 ≤ Real.log (x : ℝ) / Real.log t - 1 := by
    rw [sub_nonneg, one_le_div hlogt]
    exact Real.log_le_log htPos htUpper
  have hrho0 : 0 ≤ realDickmanBuchstabStatistic x t :=
    dickmanRho_nonneg harg
  have hrho1 : realDickmanBuchstabStatistic x t ≤ 1 :=
    dickmanRho_le_one harg
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg hrho0,
    abs_of_pos (div_pos (inv_pos.mpr htPos) hlogt)]
  exact
    mul_le_of_le_one_left
      (div_nonneg (inv_nonneg.mpr htPos.le) hlogt.le) hrho1

theorem dickmanBuchstabCell_error
    {x y k : ℕ} (hy : 3 ≤ y)
    (hyk : y < k) (hkx : k ≤ x) :
    |realDickmanBuchstabStatistic x k *
          logLogCellWeight k -
        ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t)| ≤
      (realDickmanBuchstabStatistic x k -
          realDickmanBuchstabStatistic x (k - 1 : ℕ)) *
        logLogCellWeight k := by
  have hyx : y ≤ x := hyk.le.trans hkx
  have hykm1 : y ≤ k - 1 := by omega
  have hkm1k : (k - 1 : ℕ) ≤ k := Nat.sub_le _ _
  have hkm1Real : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast hkm1k
  have hmono := monotoneOn_realDickmanBuchstabStatistic hy hyx
  have hbase :
      IntervalIntegrable
        (fun t : ℝ ↦ t⁻¹ / Real.log t)
        volume ((k - 1 : ℕ) : ℝ) k := by
    have hkm1One : (1 : ℝ) < (k - 1 : ℕ) := by
      exact_mod_cast (show 1 < k - 1 by omega)
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hkm1Real] at ht
    have htOne : 1 < t := hkm1One.trans_le ht.1
    have htPos : 0 < t := zero_lt_one.trans htOne
    exact
      (continuousAt_inv₀ htPos.ne').div
        (Real.continuousAt_log htPos.ne')
        (Real.log_pos htOne).ne' |>.continuousWithinAt
  have hactual :
      IntervalIntegrable
        (fun t : ℝ ↦
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t))
        volume ((k - 1 : ℕ) : ℝ) k :=
    intervalIntegrable_realDickmanBuchstabKernel
      hy (by exact_mod_cast hykm1) hkm1Real (by exact_mod_cast hkx)
  let upperDifference : ℝ :=
    realDickmanBuchstabStatistic x k -
      realDickmanBuchstabStatistic x (k - 1 : ℕ)
  have hupperIntegrable :
      IntervalIntegrable
        (fun t : ℝ ↦ upperDifference * (t⁻¹ / Real.log t))
        volume ((k - 1 : ℕ) : ℝ) k :=
    hbase.const_mul upperDifference
  have herrorIntegrable :
      IntervalIntegrable
        (fun t : ℝ ↦
          (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x t) *
            (t⁻¹ / Real.log t))
        volume ((k - 1 : ℕ) : ℝ) k := by
    convert
      (hbase.const_mul
        (realDickmanBuchstabStatistic x k)).sub hactual using 1
    funext t
    ring
  have herrorEq :
      realDickmanBuchstabStatistic x k * logLogCellWeight k -
          (∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
            realDickmanBuchstabStatistic x t *
              (t⁻¹ / Real.log t)) =
        ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
          (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x t) *
            (t⁻¹ / Real.log t) := by
    rw [logLogCellWeight_eq_integral (show 3 ≤ k by omega),
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub
        (hbase.const_mul (realDickmanBuchstabStatistic x k)) hactual]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  have hpointwise
      (t : ℝ) (ht : t ∈ Set.Icc (((k - 1 : ℕ) : ℝ)) k) :
      0 ≤
          (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x t) *
            (t⁻¹ / Real.log t) ∧
        (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x t) *
            (t⁻¹ / Real.log t) ≤
          upperDifference * (t⁻¹ / Real.log t) := by
    have htLower : (y : ℝ) ≤ t :=
      (by exact_mod_cast hykm1 : (y : ℝ) ≤ (k - 1 : ℕ)).trans ht.1
    have htUpper : t ≤ (x : ℝ) :=
      ht.2.trans (by exact_mod_cast hkx)
    have htOne : 1 < t := by
      have : (1 : ℝ) < (y : ℝ) := by
        exact_mod_cast (show 1 < y by omega)
      exact this.trans_le htLower
    have htk :
        realDickmanBuchstabStatistic x t ≤
          realDickmanBuchstabStatistic x k :=
      hmono ⟨htLower, htUpper⟩
        ⟨by exact_mod_cast hyk.le, by exact_mod_cast hkx⟩ ht.2
    have hkm1t :
        realDickmanBuchstabStatistic x (k - 1 : ℕ) ≤
          realDickmanBuchstabStatistic x t :=
      hmono
        ⟨by exact_mod_cast hykm1,
          by exact_mod_cast (hkm1k.trans hkx)⟩
        ⟨htLower, htUpper⟩ ht.1
    have hkernel : 0 ≤ t⁻¹ / Real.log t :=
      div_nonneg (inv_nonneg.mpr (le_of_lt (zero_lt_one.trans htOne)))
        (Real.log_pos htOne).le
    constructor
    · exact mul_nonneg (sub_nonneg.mpr htk) hkernel
    · apply mul_le_mul_of_nonneg_right _ hkernel
      dsimp only [upperDifference]
      linarith
  rw [herrorEq, abs_of_nonneg
    (intervalIntegral.integral_nonneg hkm1Real
      (fun t ht ↦ (hpointwise t ht).1))]
  calc
    (∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
        (realDickmanBuchstabStatistic x k -
            realDickmanBuchstabStatistic x t) *
          (t⁻¹ / Real.log t)) ≤
        ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
          upperDifference * (t⁻¹ / Real.log t) := by
      apply intervalIntegral.integral_mono_on hkm1Real
        herrorIntegrable hupperIntegrable
      exact fun t ht ↦ (hpointwise t ht).2
    _ = upperDifference * logLogCellWeight k := by
      rw [intervalIntegral.integral_const_mul,
        ← logLogCellWeight_eq_integral (show 3 ≤ k by omega)]
    _ =
        (realDickmanBuchstabStatistic x k -
            realDickmanBuchstabStatistic x (k - 1 : ℕ)) *
          logLogCellWeight k := by rfl

theorem logLogCellWeight_le_inv_log_sq
    {y k : ℕ} (hy : 3 ≤ y) (hyk : y < k) :
    logLogCellWeight k ≤ 1 / Real.log (y : ℝ) ^ 2 := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogY : 0 < Real.log (y : ℝ) := Real.log_pos hyOne
  have hykm1 : y ≤ k - 1 := by omega
  have hkm1Real : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.sub_le k 1)
  have hbase :
      IntervalIntegrable
        (fun t : ℝ ↦ t⁻¹ / Real.log t)
        volume ((k - 1 : ℕ) : ℝ) k := by
    have hkm1One : (1 : ℝ) < (k - 1 : ℕ) := by
      exact_mod_cast (show 1 < k - 1 by omega)
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hkm1Real] at ht
    have htOne : 1 < t := hkm1One.trans_le ht.1
    have htPos : 0 < t := zero_lt_one.trans htOne
    exact
      (continuousAt_inv₀ htPos.ne').div
        (Real.continuousAt_log htPos.ne')
        (Real.log_pos htOne).ne' |>.continuousWithinAt
  rw [logLogCellWeight_eq_integral (show 3 ≤ k by omega)]
  calc
    (∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
        t⁻¹ / Real.log t) ≤
        ∫ _t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
          1 / Real.log (y : ℝ) ^ 2 := by
      apply intervalIntegral.integral_mono_on
        hkm1Real hbase intervalIntegrable_const
      intro t ht
      have hyt : (y : ℝ) ≤ t :=
        (by exact_mod_cast hykm1 :
          (y : ℝ) ≤ (k - 1 : ℕ)).trans ht.1
      have htPos : 0 < t := hyPos.trans_le hyt
      have hlogT : 0 < Real.log t :=
        Real.log_pos (hyOne.trans_le hyt)
      have hlogYT : Real.log (y : ℝ) ≤ Real.log t :=
        Real.log_le_log hyPos hyt
      have hinvTY : t⁻¹ ≤ ((y : ℝ)⁻¹) :=
        (inv_le_inv₀ htPos hyPos).2 hyt
      calc
        t⁻¹ / Real.log t ≤
            (y : ℝ)⁻¹ / Real.log (y : ℝ) := by
          exact div_le_div₀
            (inv_nonneg.mpr hyPos.le) hinvTY hlogY hlogYT
        _ = 1 / ((y : ℝ) * Real.log (y : ℝ)) := by
          field_simp [hyPos.ne', hlogY.ne']
        _ ≤ 1 / Real.log (y : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left
            (by norm_num : (0 : ℝ) ≤ 1)
          · positivity
          · have hlogYLeY : Real.log (y : ℝ) ≤ (y : ℝ) :=
              (Real.log_le_sub_one_of_pos hyPos).trans (by linarith)
            nlinarith
    _ = 1 / Real.log (y : ℝ) ^ 2 := by
      have hcastDiff :
          (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_sub (show 1 ≤ k by omega)]
        norm_num
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      rw [hcastDiff, one_mul]

theorem dickmanLogLogCells_error
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) :
    |(∑ k ∈ Finset.Ioc y x,
          dickmanBuchstabStatistic x y k * logLogCellWeight k) -
        ∫ t : ℝ in (y : ℝ)..x,
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t)| ≤
      1 / Real.log (y : ℝ) ^ 2 := by
  have hsplit :
      (∫ t : ℝ in (y : ℝ)..x,
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t)) =
        ∑ k ∈ Finset.Ioc y x,
          ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
            realDickmanBuchstabStatistic x t *
              (t⁻¹ / Real.log t) := by
    apply intervalIntegral_eq_sum_Ioc_unit
      (f := fun t : ℝ ↦
        realDickmanBuchstabStatistic x t *
          (t⁻¹ / Real.log t)) hyx
    · intro n hyn hnx
      exact intervalIntegrable_realDickmanBuchstabKernel
        hy le_rfl (by exact_mod_cast hyn) (by exact_mod_cast hnx)
    · intro n hyn hnx
      exact intervalIntegrable_realDickmanBuchstabKernel
        hy (by exact_mod_cast hyn) (by norm_num)
        (by exact_mod_cast (show n + 1 ≤ x by omega))
  rw [hsplit, ← Finset.sum_sub_distrib]
  have hterm
      (k : ℕ) (hk : k ∈ Finset.Ioc y x) :
      |dickmanBuchstabStatistic x y k * logLogCellWeight k -
          (∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
            realDickmanBuchstabStatistic x t *
              (t⁻¹ / Real.log t))| ≤
        (realDickmanBuchstabStatistic x k -
            realDickmanBuchstabStatistic x (k - 1 : ℕ)) *
          logLogCellWeight k := by
    have hkBounds := Finset.mem_Ioc.mp hk
    rw [dickmanBuchstabStatistic_eq_real
      hkBounds.1.le hkBounds.2]
    exact dickmanBuchstabCell_error hy hkBounds.1 hkBounds.2
  have hmono := monotoneOn_realDickmanBuchstabStatistic hy hyx
  have hdelta0
      (k : ℕ) (hk : k ∈ Finset.Ioc y x) :
      0 ≤ realDickmanBuchstabStatistic x k -
        realDickmanBuchstabStatistic x (k - 1 : ℕ) := by
    have hkBounds := Finset.mem_Ioc.mp hk
    have hykm1 : y ≤ k - 1 := by omega
    exact sub_nonneg.mpr
      (hmono
        ⟨by exact_mod_cast hykm1,
          by exact_mod_cast ((Nat.sub_le k 1).trans hkBounds.2)⟩
        ⟨by exact_mod_cast hkBounds.1.le,
          by exact_mod_cast hkBounds.2⟩
        (by exact_mod_cast (Nat.sub_le k 1)))
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  calc
    |∑ k ∈ Finset.Ioc y x,
        (dickmanBuchstabStatistic x y k * logLogCellWeight k -
          ∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
            realDickmanBuchstabStatistic x t *
              (t⁻¹ / Real.log t))| ≤
        ∑ k ∈ Finset.Ioc y x,
          |dickmanBuchstabStatistic x y k * logLogCellWeight k -
            (∫ t : ℝ in ((k - 1 : ℕ) : ℝ)..k,
              realDickmanBuchstabStatistic x t *
                (t⁻¹ / Real.log t))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ k ∈ Finset.Ioc y x,
          (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x (k - 1 : ℕ)) *
            logLogCellWeight k := by
      apply Finset.sum_le_sum
      exact hterm
    _ ≤
        ∑ k ∈ Finset.Ioc y x,
          (realDickmanBuchstabStatistic x k -
              realDickmanBuchstabStatistic x (k - 1 : ℕ)) *
            (1 / Real.log (y : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
        (logLogCellWeight_le_inv_log_sq hy
          (Finset.mem_Ioc.mp hk).1)
        (hdelta0 k hk)
    _ =
        (realDickmanBuchstabStatistic x x -
            realDickmanBuchstabStatistic x y) *
          (1 / Real.log (y : ℝ) ^ 2) := by
      rw [← Finset.sum_mul,
        sum_Ioc_sub_pred
          (fun k : ℕ ↦ realDickmanBuchstabStatistic x k) hyx]
    _ ≤ 1 / Real.log (y : ℝ) ^ 2 := by
      have hyArg :
          0 ≤ Real.log (x : ℝ) / Real.log (y : ℝ) - 1 := by
        rw [sub_nonneg, one_le_div hlogY]
        exact Real.log_le_log
          (by exact_mod_cast (show 0 < y by omega))
          (by exact_mod_cast hyx)
      have hSy0 : 0 ≤ realDickmanBuchstabStatistic x y :=
        dickmanRho_nonneg hyArg
      have hSx1 : realDickmanBuchstabStatistic x x ≤ 1 := by
        unfold realDickmanBuchstabStatistic
        exact dickmanRho_le_one
          (by
            have hxPos : 0 < (x : ℝ) := by
              exact_mod_cast (show 0 < x by omega)
            have hlogX : Real.log (x : ℝ) ≠ 0 :=
              Real.log_ne_zero_of_pos_of_ne_one hxPos
                (by exact_mod_cast (show x ≠ 1 by omega))
            rw [div_self hlogX]
            norm_num)
      have hfactor :
          realDickmanBuchstabStatistic x x -
              realDickmanBuchstabStatistic x y ≤ 1 := by
        linarith
      exact
        (mul_le_mul_of_nonneg_right hfactor
          (by positivity)).trans_eq (one_mul _)

theorem monotone_dickmanBuchstabStatistic
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) :
    Monotone (dickmanBuchstabStatistic x y) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogX : 0 < Real.log (x : ℝ) :=
    Real.log_pos (hyOne.trans_le (by exact_mod_cast hyx))
  intro k l hkl
  let ck : ℕ := max y (min k x)
  let cl : ℕ := max y (min l x)
  have hckcl : ck ≤ cl := by
    dsimp only [ck, cl]
    exact max_le_max_left y (min_le_min_right x hkl)
  have hyck : y ≤ ck := le_max_left _ _
  have hycl : y ≤ cl := le_max_left _ _
  have hckx : ck ≤ x := by
    dsimp only [ck]
    omega
  have hclx : cl ≤ x := by
    dsimp only [cl]
    omega
  have hlogCk : 0 < Real.log (ck : ℝ) :=
    Real.log_pos (hyOne.trans_le (by exact_mod_cast hyck))
  have hlogCl : 0 < Real.log (cl : ℝ) :=
    Real.log_pos (hyOne.trans_le (by exact_mod_cast hycl))
  have hlogCkCl : Real.log (ck : ℝ) ≤ Real.log (cl : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < ck by omega))
      (by exact_mod_cast hckcl)
  have hquotient :
      Real.log (x : ℝ) / Real.log (cl : ℝ) ≤
        Real.log (x : ℝ) / Real.log (ck : ℝ) :=
    div_le_div_of_nonneg_left hlogX.le hlogCk hlogCkCl
  have hargCk :
      0 ≤ Real.log (x : ℝ) / Real.log (ck : ℝ) - 1 := by
    rw [sub_nonneg, one_le_div hlogCk]
    exact Real.log_le_log
      (by exact_mod_cast (show 0 < ck by omega))
      (by exact_mod_cast hckx)
  have hargCl :
      0 ≤ Real.log (x : ℝ) / Real.log (cl : ℝ) - 1 := by
    rw [sub_nonneg, one_le_div hlogCl]
    exact Real.log_le_log
      (by exact_mod_cast (show 0 < cl by omega))
      (by exact_mod_cast hclx)
  apply antitoneOn_dickmanRho_Ici_zero hargCl hargCk
  linarith

theorem dickmanBuchstabStatistic_mem_unit
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) (k : ℕ) :
    0 ≤ dickmanBuchstabStatistic x y k ∧
      dickmanBuchstabStatistic x y k ≤ 1 := by
  let c : ℕ := max y (min k x)
  have hyc : y ≤ c := le_max_left _ _
  have hcx : c ≤ x := by
    dsimp only [c]
    omega
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogC : 0 < Real.log (c : ℝ) :=
    Real.log_pos (hyOne.trans_le (by exact_mod_cast hyc))
  have harg :
      0 ≤ Real.log (x : ℝ) / Real.log (c : ℝ) - 1 := by
    rw [sub_nonneg, one_le_div hlogC]
    exact Real.log_le_log
      (by exact_mod_cast (show 0 < c by omega))
      (by exact_mod_cast hcx)
  change
    0 ≤ dickmanRho
        (Real.log (x : ℝ) / Real.log (c : ℝ) - 1) ∧
      dickmanRho
        (Real.log (x : ℝ) / Real.log (c : ℝ) - 1) ≤ 1
  exact ⟨dickmanRho_nonneg harg, dickmanRho_le_one harg⟩

/-- Mertens--Stieltjes quadrature for the Dickman Buchstab statistic,
uniformly in the endpoints. -/
theorem eventually_dickmanPrimeLogLogQuadrature :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
        |(∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
              dickmanRho
                (Real.log (x : ℝ) / Real.log (p : ℝ) - 1) / p) -
            ∑ k ∈ Finset.Ioc y x,
              dickmanBuchstabStatistic x y k *
                logLogCellWeight k| < ε := by
  intro ε hε
  have hquad := eventually_monotonePrimeLogLogQuadrature ε hε
  filter_upwards [hquad, eventually_ge_atTop 3] with y hquad hy3
  intro x hyx
  have hbase := hquad x hyx (dickmanBuchstabStatistic x y)
    (monotone_dickmanBuchstabStatistic hy3 hyx)
    (fun k => (dickmanBuchstabStatistic_mem_unit hy3 hyx k).1)
    (fun k => (dickmanBuchstabStatistic_mem_unit hy3 hyx k).2)
  have hsum :
      (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          dickmanBuchstabStatistic x y p / p) =
        ∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          dickmanRho
            (Real.log (x : ℝ) / Real.log (p : ℝ) - 1) / p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpIoc : p ∈ Finset.Ioc y x :=
      (Finset.mem_filter.mp hp).1
    have hpBounds := Finset.mem_Ioc.mp hpIoc
    rw [dickmanBuchstabStatistic_eq hpBounds.1.le hpBounds.2]
  rw [hsum] at hbase
  exact hbase

theorem tendsto_inv_log_nat_sq :
    Tendsto (fun y : ℕ => 1 / Real.log (y : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow :
      Tendsto
        (fun y : ℕ => Real.log (y : ℝ) * Real.log (y : ℝ))
        atTop atTop :=
    hlog.atTop_mul_atTop₀ hlog
  have hinv := tendsto_inv_atTop_zero.comp hpow
  change Tendsto
    (fun y : ℕ =>
      (Real.log (y : ℝ) * Real.log (y : ℝ))⁻¹)
    atTop (nhds 0) at hinv
  simpa only [one_div, pow_two] using hinv

/-- Reciprocal-prime sums against the Dickman Buchstab statistic converge,
uniformly in the upper endpoint, to the corresponding physical integral. -/
theorem eventually_dickmanPrimeQuadrature :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
        |(∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
              dickmanRho
                (Real.log (x : ℝ) / Real.log (p : ℝ) - 1) / p) -
            ∫ t : ℝ in (y : ℝ)..x,
              realDickmanBuchstabStatistic x t *
                (t⁻¹ / Real.log t)| < ε := by
  intro ε hε
  have hprime :=
    eventually_dickmanPrimeLogLogQuadrature (ε / 2) (half_pos hε)
  have hcellSmall :
      ∀ᶠ y : ℕ in atTop,
        1 / Real.log (y : ℝ) ^ 2 < ε / 2 :=
    tendsto_inv_log_nat_sq.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hprime, hcellSmall, eventually_ge_atTop 3]
      with y hprime hcellSmall hy3
  intro x hyx
  have hp := hprime x hyx
  have hc := dickmanLogLogCells_error hy3 hyx
  let primeSum : ℝ :=
    ∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
      dickmanRho
        (Real.log (x : ℝ) / Real.log (p : ℝ) - 1) / p
  let cellSum : ℝ :=
    ∑ k ∈ Finset.Ioc y x,
      dickmanBuchstabStatistic x y k * logLogCellWeight k
  let continuousIntegral : ℝ :=
    ∫ t : ℝ in (y : ℝ)..x,
      realDickmanBuchstabStatistic x t *
        (t⁻¹ / Real.log t)
  change |primeSum - cellSum| < ε / 2 at hp
  change |cellSum - continuousIntegral| ≤
    1 / Real.log (y : ℝ) ^ 2 at hc
  change |primeSum - continuousIntegral| < ε
  calc
    |primeSum - continuousIntegral| ≤
        |primeSum - cellSum| + |cellSum - continuousIntegral| := by
      have : primeSum - continuousIntegral =
          (primeSum - cellSum) + (cellSum - continuousIntegral) := by
        ring
      rw [this]
      exact abs_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add hp (hc.trans_lt hcellSmall)
    _ = ε := by ring

/-- Logarithmic change of variables from the physical prime coordinate to
the multiplicative Buchstab coordinate. -/
theorem dickmanPhysicalIntegral_eq_buchstabIntegral
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) :
    (∫ t : ℝ in (y : ℝ)..x,
        realDickmanBuchstabStatistic x t *
          (t⁻¹ / Real.log t)) =
      ∫ w : ℝ in (1 : ℝ)..smoothParameter x y,
        dickmanRho (smoothParameter x y / w - 1) / w := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hyOne : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogY : 0 < Real.log (y : ℝ) := Real.log_pos hyOne
  have hxPos : 0 < (x : ℝ) :=
    hyPos.trans_le (by exact_mod_cast hyx)
  have hu : 1 ≤ smoothParameter x y := by
    unfold smoothParameter
    rw [one_le_div hlogY]
    exact Real.log_le_log hyPos (by exact_mod_cast hyx)
  let change : ℝ → ℝ := fun w ↦ (y : ℝ) ^ w
  let change' : ℝ → ℝ :=
    fun w ↦ Real.log (y : ℝ) * (y : ℝ) ^ w
  let physicalIntegrand : ℝ → ℝ := fun t ↦
    realDickmanBuchstabStatistic x t * (t⁻¹ / Real.log t)
  have hchangeContinuous :
      ContinuousOn change (Set.uIcc (1 : ℝ) (smoothParameter x y)) :=
    (Real.continuous_const_rpow hyPos.ne').continuousOn
  have hchangeDeriv :
      ∀ w ∈ Set.Ioo (1 : ℝ) (smoothParameter x y),
        HasDerivAt change (change' w) w := by
    intro w _hw
    simpa only [change, change', id_eq, one_mul, mul_one] using
      (hasDerivAt_id w).const_rpow hyPos
  have hchangeNonneg :
      ∀ w ∈ Set.Ioo (1 : ℝ) (smoothParameter x y),
        0 ≤ change' w := by
    intro w _hw
    dsimp only [change']
    positivity
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (1 : ℝ)) (b := smoothParameter x y)
      (f := change) (f' := change') (g := physicalIntegrand)
      hchangeContinuous
      (by
        simpa [min_eq_left hu, max_eq_right hu] using hchangeDeriv)
      (by
        simpa [min_eq_left hu, max_eq_right hu] using hchangeNonneg)
  have hchangeOne : change 1 = (y : ℝ) := by
    dsimp only [change]
    exact Real.rpow_one _
  have hchangeU : change (smoothParameter x y) = (x : ℝ) := by
    dsimp only [change]
    unfold smoothParameter
    exact Real.rpow_logb hyPos (ne_of_gt hyOne) hxPos
  rw [hchangeOne, hchangeU] at hsub
  have hintegrand :
      (fun w : ℝ ↦ (physicalIntegrand ∘ change) w * change' w) =
        fun w : ℝ ↦
          dickmanRho (smoothParameter x y / w - 1) / w := by
    funext w
    by_cases hw : w = 0
    · subst w
      simp [physicalIntegrand, change, change',
        realDickmanBuchstabStatistic]
    · have hpowPos : 0 < (y : ℝ) ^ w :=
        Real.rpow_pos_of_pos hyPos w
      have hlogPow :
          Real.log ((y : ℝ) ^ w) = w * Real.log (y : ℝ) :=
        Real.log_rpow hyPos w
      have harg :
          Real.log (x : ℝ) / Real.log ((y : ℝ) ^ w) - 1 =
            smoothParameter x y / w - 1 := by
        rw [hlogPow]
        unfold smoothParameter
        field_simp [hw, hlogY.ne']
      dsimp only [Function.comp_apply, physicalIntegrand, change, change',
        realDickmanBuchstabStatistic]
      rw [harg, hlogPow]
      field_simp [hw, hlogY.ne', hpowPos.ne']
  rw [hintegrand] at hsub
  exact hsub.symm

/-- Dickman's Buchstab identity in the physical prime coordinate. -/
theorem dickmanRho_physicalBuchstab
    {x y : ℕ} (hy : 3 ≤ y) (hyx : y ≤ x) :
    dickmanRho (smoothParameter x y) =
      1 -
        ∫ t : ℝ in (y : ℝ)..x,
          realDickmanBuchstabStatistic x t *
            (t⁻¹ / Real.log t) := by
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hu : 1 ≤ smoothParameter x y := by
    unfold smoothParameter
    rw [one_le_div hlogY]
    exact Real.log_le_log hyPos (by exact_mod_cast hyx)
  rw [dickmanPhysicalIntegral_eq_buchstabIntegral hy hyx]
  exact dickmanRho_buchstab (smoothParameter x y) hu

/-- The density of primes among the first `n` integers tends to zero.  The
weak Chebyshev bound is more than sufficient for the flooring error below. -/
theorem tendsto_primeCounting_div_nat :
    Tendsto
      (fun n : ℕ => (Nat.primeCounting n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  let c : ℝ := Real.log 4 + 1
  have hchebReal := Chebyshev.eventually_primeCounting_le
    (ε := (1 : ℝ)) one_pos
  have hchebNat :
      ∀ᶠ n : ℕ in atTop,
        (Nat.primeCounting n : ℝ) ≤
          c * (n : ℝ) / Real.log (n : ℝ) := by
    have hcomp := tendsto_natCast_atTop_atTop.eventually hchebReal
    simpa only [Nat.floor_natCast, c] using hcomp
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  change Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹)
      atTop (nhds 0) at hinv
  have hright :
      Tendsto (fun n : ℕ => c / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    positivity
  · filter_upwards [hchebNat, eventually_ge_atTop 2] with n hn hn2
    have hnPos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    have hlogPos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    calc
      (Nat.primeCounting n : ℝ) / (n : ℝ) ≤
          (c * (n : ℝ) / Real.log (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hn hnPos.le
      _ = c / Real.log (n : ℝ) := by
        field_simp [hnPos.ne', hlogPos.ne']
  · exact hright

/-- On a fixed smoothness strip, the reciprocal mass of the Buchstab primes
is bounded independently of both endpoints. -/
theorem eventually_buchstabPrimeReciprocalMass_le (k : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
      smoothParameter x y ≤ (k : ℝ) + 1 →
      (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
          (p : ℝ)⁻¹) ≤ Real.log ((k : ℝ) + 1) + 1 := by
  have hcum := eventually_uniform_primeLogLogCumulative 1 one_pos
  filter_upwards [hcum, eventually_ge_atTop 3] with y hcum hy3
  intro x hyx huK
  have hcum' := hcum x hyx
  have hyPos : 0 < (y : ℝ) := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (x : ℝ) :=
    Real.log_pos
      ((by exact_mod_cast (show 1 < y by omega) : (1 : ℝ) < y).trans_le
        (by exact_mod_cast hyx))
  have hu1 : 1 ≤ smoothParameter x y := by
    unfold smoothParameter
    rw [one_le_div hlogY]
    exact Real.log_le_log hyPos (by exact_mod_cast hyx)
  have hlogu :
      Real.log (smoothParameter x y) =
        Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (y : ℝ)) := by
    unfold smoothParameter
    rw [Real.log_div hlogX.ne' hlogY.ne']
  have hlogBound :
      Real.log (smoothParameter x y) ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log (zero_lt_one.trans_le hu1) huK
  rw [finiteIocCumulative_primeLogLogDiscrepancyCoefficient hyx] at hcum'
  rw [← hlogu] at hcum'
  linarith [lt_of_abs_lt hcum']

theorem natDivNormalized_sub_inv_mem
    {x p : ℕ} (hp : 0 < p) (hpx : p ≤ x) :
    0 ≤ (1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x ∧
      (1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x ≤
        1 / (x : ℝ) := by
  have hx : 0 < x := hp.trans_le hpx
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  have hqLe : ((x / p : ℕ) : ℝ) ≤ (x : ℝ) / p :=
    Nat.cast_div_le
  have hltNat := Nat.lt_mul_div_succ x hp
  have hlt : (x : ℝ) / p < ((x / p : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hpR).2
    have hcast : (x : ℝ) < (p : ℝ) * ((x / p : ℕ) + 1) := by
      exact_mod_cast hltNat
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcast
  have heq :
      (1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x =
        (((x : ℝ) / p) - ((x / p : ℕ) : ℝ)) / x := by
    field_simp [hpR.ne', hxR.ne']
  rw [heq]
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ hxR.le
    linarith

theorem card_prime_Ioc_le_primeCounting (x y : ℕ) :
    ((Finset.Ioc y x).filter Nat.Prime).card ≤ Nat.primeCounting x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Nat.mem_primesLE]
  exact ⟨hp.1.2, hp.2⟩

theorem tendsto_const_div_log_nat (c : ℝ) :
    Tendsto (fun n : ℕ => c / Real.log (n : ℝ)) atTop (nhds 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hlog
  change Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹)
      atTop (nhds 0) at hinv
  simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)

/-- The rounded, recursively parameterized Buchstab prime sum converges
uniformly on each fixed strip to the continuous Dickman integral. -/
theorem eventually_dickmanRoundedPrimeQuadrature (k : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
        smoothParameter x y ≤ (k : ℝ) + 2 →
        |(∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
              (((x / p : ℕ) : ℝ) / (x : ℝ)) *
                dickmanRho (smoothParameter (x / p) p)) -
            ∫ t : ℝ in (y : ℝ)..x,
              realDickmanBuchstabStatistic x t *
                (t⁻¹ / Real.log t)| < ε := by
  intro ε hε
  let D : ℝ := Real.log ((k : ℝ) + 2) + 1
  have hD : 0 < D := by
    dsimp only [D]
    have hk : (1 : ℝ) ≤ (k : ℝ) + 2 := by
      exact_mod_cast (show 1 ≤ k + 2 by omega)
    have : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg hk
    linarith
  have hquad :=
    eventually_dickmanPrimeQuadrature (ε / 3) (by positivity)
  have hmass := eventually_buchstabPrimeReciprocalMass_le (k + 1)
  have hfloor0 := tendsto_primeCounting_div_nat.eventually
    (Iio_mem_nhds (by positivity : 0 < ε / 3))
  have hfloor :
      ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
        (Nat.primeCounting x : ℝ) / (x : ℝ) < ε / 3 := by
    rw [eventually_atTop] at hfloor0 ⊢
    obtain ⟨Y, hY⟩ := hfloor0
    exact ⟨Y, fun y hy x hyx ↦ hY x (hy.trans hyx)⟩
  have hparam0 := tendsto_const_div_log_nat (D * Real.log 2)
  have hparam :
      ∀ᶠ y : ℕ in atTop,
        D * (Real.log 2 / Real.log (y : ℝ)) < ε / 3 := by
    have h := hparam0.eventually
      (Iio_mem_nhds (by positivity : 0 < ε / 3))
    simpa only [mul_div_assoc] using h
  filter_upwards [hquad, hmass, hfloor, hparam, eventually_ge_atTop 3]
      with y hquad hmass hfloor hparam hy3
  intro x hyx hu
  have hxPos : 0 < x := by omega
  have hxRPos : 0 < (x : ℝ) := by exact_mod_cast hxPos
  have hmass' :
      (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime, (p : ℝ)⁻¹) ≤ D := by
    have h := hmass x hyx (by
      norm_num [Nat.cast_add, Nat.cast_one] at ⊢
      linarith [hu])
    dsimp only [D]
    convert h using 1 <;> push_cast <;> ring_nf
  have hquad' := hquad x hyx
  have hfloor' := hfloor x hyx
  let primes : Finset ℕ := (Finset.Ioc y x).filter Nat.Prime
  let roundedTerm : ℕ → ℝ := fun p ↦
    (((x / p : ℕ) : ℝ) / (x : ℝ)) *
      dickmanRho (smoothParameter (x / p) p)
  let actualTerm : ℕ → ℝ := fun p ↦
    dickmanRho (smoothParameter (x / p) p) / p
  let idealTerm : ℕ → ℝ := fun p ↦
    dickmanRho
      (Real.log (x : ℝ) / Real.log (p : ℝ) - 1) / p
  let physicalIntegral : ℝ :=
    ∫ t : ℝ in (y : ℝ)..x,
      realDickmanBuchstabStatistic x t * (t⁻¹ / Real.log t)
  change |∑ p ∈ primes, idealTerm p - physicalIntegral| < ε / 3 at hquad'
  have hfloorTerm (p : ℕ) (hp : p ∈ primes) :
      |roundedTerm p - actualTerm p| ≤ 1 / (x : ℝ) := by
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Ioc.mp hpData.1
    have hpPrime : p.Prime := hpData.2
    have hpPos : 0 < p := hpPrime.pos
    have hqPos : 0 < x / p := Nat.div_pos hpBounds.2 hpPos
    have hp2 : 2 ≤ p := hpPrime.two_le
    have harg0 : 0 ≤ smoothParameter (x / p) p :=
      smoothParameter_nonneg hqPos hp2
    have hrho0 : 0 ≤ dickmanRho (smoothParameter (x / p) p) :=
      dickmanRho_nonneg harg0
    have hrho1 : dickmanRho (smoothParameter (x / p) p) ≤ 1 :=
      dickmanRho_le_one harg0
    have hd := natDivNormalized_sub_inv_mem hpPos hpBounds.2
    have heq :
        actualTerm p - roundedTerm p =
          dickmanRho (smoothParameter (x / p) p) *
            ((1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x) := by
      dsimp only [actualTerm, roundedTerm]
      ring
    rw [abs_sub_comm, heq, abs_of_nonneg (mul_nonneg hrho0 hd.1)]
    calc
      dickmanRho (smoothParameter (x / p) p) *
          ((1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x) ≤
          1 * ((1 : ℝ) / p - ((x / p : ℕ) : ℝ) / x) :=
        mul_le_mul_of_nonneg_right hrho1 hd.1
      _ ≤ 1 / (x : ℝ) := by simpa using hd.2
  have hfloorSum :
      |(∑ p ∈ primes, roundedTerm p) -
          ∑ p ∈ primes, actualTerm p| < ε / 3 := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ p ∈ primes, (roundedTerm p - actualTerm p)| ≤
          ∑ p ∈ primes, |roundedTerm p - actualTerm p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ primes, 1 / (x : ℝ) := by
        apply Finset.sum_le_sum
        exact hfloorTerm
      _ = (primes.card : ℝ) / (x : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ (Nat.primeCounting x : ℝ) / (x : ℝ) := by
        apply div_le_div_of_nonneg_right _ hxRPos.le
        exact_mod_cast card_prime_Ioc_le_primeCounting x y
      _ < ε / 3 := hfloor'
  have hparamTerm (p : ℕ) (hp : p ∈ primes) :
      |actualTerm p - idealTerm p| ≤
        (Real.log 2 / Real.log (y : ℝ)) * ((p : ℝ)⁻¹) := by
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Ioc.mp hpData.1
    have hpPrime : p.Prime := hpData.2
    have hpPos : 0 < p := hpPrime.pos
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hqPos : 0 < x / p := Nat.div_pos hpBounds.2 hpPos
    have ha0 : 0 ≤ smoothParameter (x / p) p :=
      smoothParameter_nonneg hqPos hp2
    have hlogP : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hi0 :
        0 ≤ Real.log (x : ℝ) / Real.log (p : ℝ) - 1 := by
      rw [sub_nonneg, one_le_div hlogP]
      exact Real.log_le_log (by exact_mod_cast hpPos)
        (by exact_mod_cast hpBounds.2)
    have hrho := Erdos390.abs_poissonDickmanProfile_sub_le ha0 hi0
    change
      |dickmanRho (smoothParameter (x / p) p) -
          dickmanRho
            (Real.log (x : ℝ) / Real.log (p : ℝ) - 1)| ≤
        |smoothParameter (x / p) p -
          (Real.log (x : ℝ) / Real.log (p : ℝ) - 1)| at hrho
    have happ := smoothParameter_div_approx hp2 hpBounds.2
    have hlogY : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hlogYP : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpBounds.1.le)
    have hquot :
        Real.log 2 / Real.log (p : ℝ) ≤
          Real.log 2 / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num))
        hlogY hlogYP
    dsimp only [actualTerm, idealTerm]
    rw [← sub_div, abs_div,
      abs_of_pos (by exact_mod_cast hpPos : (0 : ℝ) < p),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (hrho.trans (happ.trans hquot)) (inv_nonneg.mpr (by positivity))
  have hparamSum :
      |(∑ p ∈ primes, actualTerm p) -
          ∑ p ∈ primes, idealTerm p| < ε / 3 := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ p ∈ primes, (actualTerm p - idealTerm p)| ≤
          ∑ p ∈ primes, |actualTerm p - idealTerm p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ primes,
          (Real.log 2 / Real.log (y : ℝ)) * ((p : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        exact hparamTerm
      _ = (Real.log 2 / Real.log (y : ℝ)) *
          ∑ p ∈ primes, (p : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
      _ ≤ (Real.log 2 / Real.log (y : ℝ)) * D := by
        apply mul_le_mul_of_nonneg_left hmass'
        positivity
      _ = D * (Real.log 2 / Real.log (y : ℝ)) := by ring
      _ < ε / 3 := hparam
  change |(∑ p ∈ primes, roundedTerm p) - physicalIntegral| < ε
  calc
    |(∑ p ∈ primes, roundedTerm p) - physicalIntegral| ≤
        |(∑ p ∈ primes, roundedTerm p) -
            ∑ p ∈ primes, actualTerm p| +
          |(∑ p ∈ primes, actualTerm p) -
            ∑ p ∈ primes, idealTerm p| +
          |(∑ p ∈ primes, idealTerm p) - physicalIntegral| := by
      have hrearrange :
          (∑ p ∈ primes, roundedTerm p) - physicalIntegral =
            ((∑ p ∈ primes, roundedTerm p) -
              ∑ p ∈ primes, actualTerm p) +
            ((∑ p ∈ primes, actualTerm p) -
              ∑ p ∈ primes, idealTerm p) +
            ((∑ p ∈ primes, idealTerm p) - physicalIntegral) := by
        ring
      rw [hrearrange]
      exact abs_add_three _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add hfloorSum hparamSum) hquad'
    _ = ε := by ring

/-- Uniform Dickman approximation on the first `k + 1` smoothness strips. -/
def UniformSmoothApproximationUpTo (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ y : ℕ in atTop, ∀ x : ℕ, y ≤ x →
      smoothParameter x y ≤ (k : ℝ) + 1 →
      |((smoothCountingFunction x y : ℝ) / (x : ℝ)) -
        dickmanRho (smoothParameter x y)| < ε

/-- Exact Buchstab recursion plus uniform prime quadrature propagates the
smooth-number asymptotic through every fixed finite number of strips. -/
theorem uniformSmoothApproximationUpTo :
    ∀ k : ℕ, UniformSmoothApproximationUpTo k := by
  intro k
  induction k with
  | zero =>
      intro ε hε
      filter_upwards [eventually_ge_atTop 2] with y hy2
      intro x hyx hu
      have hx : 0 < x := by omega
      have hxy : x ≤ y :=
        (smoothParameter_le_one_iff_le hx hy2).mp (by simpa using hu)
      have hparam0 : 0 ≤ smoothParameter x y :=
        smoothParameter_nonneg hx hy2
      rw [smoothCountingFunction_eq_self_of_le hxy,
        dickmanRho_profile.2.1 _ hparam0 (by simpa using hu)]
      simp [ne_of_gt (by exact_mod_cast hx : (0 : ℝ) < x), hε]
  | succ k ih =>
      intro ε hε
      let D : ℝ := Real.log ((k : ℝ) + 2) + 1
      have hD : 0 < D := by
        dsimp only [D]
        have hk : (1 : ℝ) ≤ (k : ℝ) + 2 := by
          exact_mod_cast (show 1 ≤ k + 2 by omega)
        have : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg hk
        linarith
      let δ : ℝ := ε / (2 * D)
      have hδ : 0 < δ := by
        dsimp only [δ]
        positivity
      have hIH := ih δ hδ
      rw [eventually_atTop] at hIH
      obtain ⟨YIH, hIH⟩ := hIH
      have hmodel :=
        eventually_dickmanRoundedPrimeQuadrature k (ε / 2) (half_pos hε)
      have hmass := eventually_buchstabPrimeReciprocalMass_le (k + 1)
      filter_upwards [hmodel, hmass, eventually_ge_atTop 3,
          eventually_ge_atTop YIH]
          with y hmodel hmass hy3 hyIH
      intro x hyx hu
      have hx : 0 < x := by omega
      have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
      have hy2 : 2 ≤ y := by omega
      have hparam0 : 0 ≤ smoothParameter x y :=
        smoothParameter_nonneg hx hy2
      by_cases hu1 : smoothParameter x y ≤ 1
      · have hxy : x ≤ y :=
          (smoothParameter_le_one_iff_le hx hy2).mp hu1
        rw [smoothCountingFunction_eq_self_of_le hxy,
          dickmanRho_profile.2.1 _ hparam0 hu1]
        simp [hxR.ne', hε]
      · have hu1' : 1 < smoothParameter x y := lt_of_not_ge hu1
        have hmodel' := hmodel x hyx (by
          convert hu using 1 <;> push_cast <;> ring)
        have hmass' :
            (∑ p ∈ (Finset.Ioc y x).filter Nat.Prime,
                (p : ℝ)⁻¹) ≤ D := by
          have h := hmass x hyx hu
          dsimp only [D]
          convert h using 1 <;> push_cast <;> ring_nf
        let primes : Finset ℕ := (Finset.Ioc y x).filter Nat.Prime
        let actualTerm : ℕ → ℝ := fun p ↦
          (smoothCountingFunction (x / p) p : ℝ) / (x : ℝ)
        let modelTerm : ℕ → ℝ := fun p ↦
          (((x / p : ℕ) : ℝ) / (x : ℝ)) *
            dickmanRho (smoothParameter (x / p) p)
        let physicalIntegral : ℝ :=
          ∫ t : ℝ in (y : ℝ)..x,
            realDickmanBuchstabStatistic x t * (t⁻¹ / Real.log t)
        have hcastCount :
            (smoothCountingFunction x y : ℝ) =
              (x : ℝ) -
                ∑ p ∈ primes,
                  (smoothCountingFunction (x / p) p : ℝ) := by
          have hnat := smoothCountingFunction_buchstab x y
          have hcountPos : 0 < smoothCountingFunction x y := by
            rw [smoothCountingFunction]
            apply Finset.card_pos.mpr
            refine ⟨1, ?_⟩
            rw [Nat.mem_smoothNumbersUpTo]
            exact ⟨hx, Nat.mem_smoothNumbers_of_lt (by norm_num) (by omega)⟩
          have hsumLe :
              (∑ p ∈ primes,
                smoothCountingFunction (x / p) p) ≤ x := by
            by_contra hnot
            have hzero :
                x - ∑ p ∈ primes,
                    smoothCountingFunction (x / p) p = 0 :=
              Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hnot)
            dsimp only [primes] at hzero
            rw [hzero] at hnat
            omega
          rw [hnat, Nat.cast_sub (by
            simpa only [primes] using hsumLe)]
          push_cast
          rfl
        have hcastBuchstab :
            (smoothCountingFunction x y : ℝ) / (x : ℝ) =
              1 - ∑ p ∈ primes, actualTerm p := by
          rw [hcastCount]
          dsimp only [actualTerm]
          rw [sub_div, div_self hxR.ne', Finset.sum_div]
        have hchildNorm (p : ℕ) (hp : p ∈ primes) :
            |(smoothCountingFunction (x / p) p : ℝ) /
                  ((x / p : ℕ) : ℝ) -
                dickmanRho (smoothParameter (x / p) p)| ≤ δ := by
          have hpData := Finset.mem_filter.mp hp
          have hpBounds := Finset.mem_Ioc.mp hpData.1
          have hpPrime : p.Prime := hpData.2
          have hpPos : 0 < p := hpPrime.pos
          have hqPos : 0 < x / p := Nat.div_pos hpBounds.2 hpPos
          have hp2 : 2 ≤ p := hpPrime.two_le
          have hchild0 : 0 ≤ smoothParameter (x / p) p :=
            smoothParameter_nonneg hqPos hp2
          by_cases hqp : x / p ≤ p
          · have hchild1 : smoothParameter (x / p) p ≤ 1 :=
              (smoothParameter_le_one_iff_le hqPos hp2).2 hqp
            rw [smoothCountingFunction_eq_self_of_le hqp,
              dickmanRho_profile.2.1 _ hchild0 hchild1]
            simpa [ne_of_gt (by exact_mod_cast hqPos :
              (0 : ℝ) < (x / p : ℕ))] using hδ.le
          · have hpq : p ≤ x / p := Nat.le_of_not_ge hqp
            have hchildUpper :
                smoothParameter (x / p) p ≤ (k : ℝ) + 1 := by
              have hdesc := smoothParameter_div_lt_pred
                (k := k + 1) hx hy2 hpBounds.1 hpBounds.2 (by
                  norm_num [Nat.cast_add, Nat.cast_one] at hu ⊢
                  linarith [hu])
              norm_num [Nat.cast_add, Nat.cast_one] at hdesc ⊢
              exact hdesc.le
            exact (hIH p (hyIH.trans hpBounds.1.le)
              (x / p) hpq hchildUpper).le
        have hterm (p : ℕ) (hp : p ∈ primes) :
            |actualTerm p - modelTerm p| ≤ δ * ((p : ℝ)⁻¹) := by
          have hpData := Finset.mem_filter.mp hp
          have hpBounds := Finset.mem_Ioc.mp hpData.1
          have hpPrime : p.Prime := hpData.2
          have hpPos : 0 < p := hpPrime.pos
          have hqPos : 0 < x / p := Nat.div_pos hpBounds.2 hpPos
          have hqR : 0 < ((x / p : ℕ) : ℝ) := by exact_mod_cast hqPos
          have hfactor :
              ((x / p : ℕ) : ℝ) / (x : ℝ) ≤ (p : ℝ)⁻¹ := by
            calc
              ((x / p : ℕ) : ℝ) / (x : ℝ) ≤
                  ((x : ℝ) / p) / (x : ℝ) :=
                div_le_div_of_nonneg_right Nat.cast_div_le hxR.le
              _ = (p : ℝ)⁻¹ := by
                field_simp [hxR.ne',
                  (ne_of_gt (by exact_mod_cast hpPos : (0 : ℝ) < p))]
          have heq :
              actualTerm p - modelTerm p =
                (((x / p : ℕ) : ℝ) / (x : ℝ)) *
                  ((smoothCountingFunction (x / p) p : ℝ) /
                      ((x / p : ℕ) : ℝ) -
                    dickmanRho (smoothParameter (x / p) p)) := by
            dsimp only [actualTerm, modelTerm]
            field_simp [hxR.ne', hqR.ne']
          rw [heq, abs_mul, abs_of_pos (div_pos hqR hxR)]
          calc
            (((x / p : ℕ) : ℝ) / (x : ℝ)) *
                |(smoothCountingFunction (x / p) p : ℝ) /
                    ((x / p : ℕ) : ℝ) -
                  dickmanRho (smoothParameter (x / p) p)| ≤
                (((x / p : ℕ) : ℝ) / (x : ℝ)) * δ :=
              mul_le_mul_of_nonneg_left (hchildNorm p hp)
                (div_nonneg hqR.le hxR.le)
            _ ≤ (p : ℝ)⁻¹ * δ :=
              mul_le_mul_of_nonneg_right hfactor hδ.le
            _ = δ * (p : ℝ)⁻¹ := by ring
        have hsubError :
            |(∑ p ∈ primes, actualTerm p) -
                ∑ p ∈ primes, modelTerm p| ≤ ε / 2 := by
          rw [← Finset.sum_sub_distrib]
          calc
            |∑ p ∈ primes, (actualTerm p - modelTerm p)| ≤
                ∑ p ∈ primes, |actualTerm p - modelTerm p| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ p ∈ primes, δ * (p : ℝ)⁻¹ := by
              apply Finset.sum_le_sum
              exact hterm
            _ = δ * ∑ p ∈ primes, (p : ℝ)⁻¹ := by
              rw [Finset.mul_sum]
            _ ≤ δ * D := mul_le_mul_of_nonneg_left hmass' hδ.le
            _ = ε / 2 := by
              dsimp only [δ]
              field_simp [hD.ne']
        have hphysical := dickmanRho_physicalBuchstab hy3 hyx
        change |(∑ p ∈ primes, modelTerm p) - physicalIntegral| < ε / 2
          at hmodel'
        rw [hcastBuchstab, hphysical]
        calc
          |(1 - ∑ p ∈ primes, actualTerm p) -
              (1 - physicalIntegral)| =
              |(∑ p ∈ primes, actualTerm p) - physicalIntegral| := by
            rw [show (1 - ∑ p ∈ primes, actualTerm p) -
                (1 - physicalIntegral) =
              -((∑ p ∈ primes, actualTerm p) - physicalIntegral) by ring,
              abs_neg]
          _ ≤
              |(∑ p ∈ primes, actualTerm p) -
                  ∑ p ∈ primes, modelTerm p| +
                |(∑ p ∈ primes, modelTerm p) - physicalIntegral| := by
            exact abs_sub_le _ _ _
          _ < ε / 2 + ε / 2 :=
            add_lt_add_of_le_of_lt hsubError hmodel'
          _ = ε := by ring

theorem tendsto_smoothParameter_powerCutoff
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun N : ℕ => smoothParameter N (powerCutoff a N))
      atTop (nhds a⁻¹) := by
  have hratio := tendsto_log_powerCutoff_div_log ha
  have hinv := hratio.inv₀ ha.ne'
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 2,
      (tendsto_powerCutoff_atTop ha).eventually (Ici_mem_atTop 2)]
      with N hN hy
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogY : Real.log (powerCutoff a N : ℝ) ≠ 0 :=
    (Real.log_pos
      (by exact_mod_cast (show 1 < powerCutoff a N by omega))).ne'
  unfold smoothParameter
  field_simp [hlogN, hlogY]

/-- The fixed-parameter smooth-number theorem in exactly the specialization
needed by the power-cutoff terminal block. -/
def PowerCutoffSmoothAsymptotic (ρ : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 →
    Tendsto
      (fun N : ℕ =>
        ((N.smoothNumbersUpTo (powerCutoff a N + 1)).card : ℝ) /
          (N : ℝ))
      atTop (nhds (ρ a⁻¹))

/-- The unconditional fixed-parameter smooth-number theorem required by the
terminal-prime construction. -/
theorem powerCutoffSmoothAsymptotic_dickmanRho :
    PowerCutoffSmoothAsymptotic dickmanRho := by
  intro a ha ha1
  have hyTop := tendsto_powerCutoff_atTop ha
  have hparam := tendsto_smoothParameter_powerCutoff ha
  have huPos : 0 < a⁻¹ := inv_pos.mpr ha
  have hRho :
      Tendsto
        (fun N : ℕ => dickmanRho
          (smoothParameter N (powerCutoff a N)))
        atTop (nhds (dickmanRho a⁻¹)) :=
    (continuousAt_dickmanRho_of_pos huPos).tendsto.comp hparam
  obtain ⟨k, hk⟩ := exists_nat_gt a⁻¹
  have huUpper :
      ∀ᶠ N : ℕ in atTop,
        smoothParameter N (powerCutoff a N) ≤ (k : ℝ) + 1 :=
    hparam.eventually (Iio_mem_nhds (by linarith)) |>.mono
      (fun _ h ↦ h.le)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huniform :=
    uniformSmoothApproximationUpTo k (ε / 2) (half_pos hε)
  have huniform' := hyTop.eventually huniform
  have hRho' := hRho.eventually
    (Metric.ball_mem_nhds (dickmanRho a⁻¹) (half_pos hε))
  have hall :
      ∀ᶠ N : ℕ in atTop,
        dist
          (((N.smoothNumbersUpTo (powerCutoff a N + 1)).card : ℝ) /
            (N : ℝ))
          (dickmanRho a⁻¹) < ε := by
    filter_upwards [huniform', hRho', huUpper, eventually_ge_atTop 1]
        with N huniform hRho huUpper hN
    have hyN : powerCutoff a N ≤ N := powerCutoff_le_self ha1 hN
    have happrox := huniform N hyN huUpper
    rw [Real.dist_eq] at hRho ⊢
    change
      |((smoothCountingFunction N (powerCutoff a N) : ℝ) / (N : ℝ)) -
        dickmanRho a⁻¹| < ε
    calc
      |((smoothCountingFunction N (powerCutoff a N) : ℝ) / (N : ℝ)) -
          dickmanRho a⁻¹| ≤
          |((smoothCountingFunction N (powerCutoff a N) : ℝ) / (N : ℝ)) -
            dickmanRho (smoothParameter N (powerCutoff a N))| +
          |dickmanRho (smoothParameter N (powerCutoff a N)) -
            dickmanRho a⁻¹| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add happrox hRho
      _ = ε := by ring
  rw [eventually_atTop] at hall
  exact hall

/-- Tao's uniform lower bound in epsilon form. -/
def TaoLowerBound (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      Admissible C N A → ρ (Real.exp C) - ε < sieveDensity N A

/-- Hildebrand's uniform lower theorem for a varying finite set of prime
moduli.  The quantifier order is essential: the endpoint threshold is
independent of the prime set. -/
def PrimeOnlyLowerBound (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      Admissible C N P →
      (∀ p ∈ P, p.Prime) →
      ρ (Real.exp (reciprocalMass P)) - ε < sieveDensity N P

/-- The lower bound after reducing to primes and composite moduli below a
fixed cutoff.  The cutoff is fixed before the endpoint tends to infinity. -/
def BoundedCompositeLowerBound (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ z : ℕ, 0 < z →
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      Admissible C N A →
      (∀ a ∈ A, ¬a.Prime → a < z) →
      ρ (Real.exp C) - ε < sieveDensity N A

/-- Tao's scale-gap reduction, conditional only on the prime-only theorem
and the Dickman product inequality.  All finite sieve and error estimates in
this step are proved above. -/
theorem boundedCompositeLowerBound_of_primeOnly_of_product
    (hprime : PrimeOnlyLowerBound dickmanRho)
    (hprod : DickmanProductInequality dickmanRho) :
    BoundedCompositeLowerBound dickmanRho := by
  intro C hC ε hε z₀ hz₀
  let η : ℝ := min (ε / 100) (1 / 100)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (div_pos hε (by norm_num)) (by norm_num)
  have hηε : η ≤ ε / 100 := min_le_left _ _
  have hηone : η ≤ 1 / 100 := min_le_right _ _
  obtain ⟨r, hr⟩ := exists_factorialTail_lt hη
  have hlayer : C ^ (r + 1) / (r + 1).factorial < η :=
    (factorialLayer_le_factorialTail hC.le r).trans_lt hr
  obtain ⟨k, hklarge⟩ := exists_nat_gt (C / η)
  have hkR : 0 < (k : ℝ) :=
    (div_pos hC hη).trans hklarge
  have hk : 0 < k := by exact_mod_cast hkR
  have hCdivk : C / (k : ℝ) < η := by
    rw [div_lt_iff₀ hkR]
    have := (div_lt_iff₀ hη).mp hklarge
    nlinarith
  let zs : ℕ → ℕ := splittingScaleSeq C η r z₀
  have hzs : StrictMono zs := strictMono_splittingScaleSeq C η r z₀
  have hzspos (j : ℕ) : 0 < zs j := splittingScaleSeq_pos hz₀ j
  have hbonf := eventually_sieveDensity_truncated_abs_lt
    hC.le hη (zs k + 1) r
  have hp := hprime C hC η hη
  filter_upwards [hbonf, hp, eventually_ge_atTop ((zs k) ^ r),
      eventually_ge_atTop 1]
      with N hbonfN hpN hpowN hN
  intro A hA hcomp
  obtain ⟨j, hjk, hgap⟩ :=
    exists_scaleGap_mass_le hA.mass_le zs hzs hk
  have hgapη : reciprocalMass (scaleGap A zs j) < η :=
    hgap.trans_lt hCdivk
  let A₁ := lowScalePart A (zs j)
  let A₂ := highScalePart A (zs (j + 1))
  let B := A₁ ∪ A₂
  have hzsjj : zs j < zs (j + 1) := hzs (Nat.lt_succ_self j)
  have hdisj : Disjoint A₁ A₂ := by
    exact disjoint_lowScalePart_highScalePart A hzsjj
  have hA₁sub : A₁ ⊆ A := lowScalePart_subset A (zs j)
  have hA₂sub : A₂ ⊆ A := highScalePart_subset A (zs (j + 1))
  have hBsub : B ⊆ A := by
    exact union_lowScalePart_highScalePart_subset A (zs j) (zs (j + 1))
  have hA₁ : Admissible C N A₁ := hA.mono hA₁sub
  have hA₂ : Admissible C N A₂ := hA.mono hA₂sub
  have hB : Admissible C N B := hA.mono hBsub
  have hA₁small : ∀ a ∈ A₁, a ≤ zs j := by
    intro a ha
    exact (mem_lowScalePart.mp ha).2
  have hA₂large : ∀ a ∈ A₂, zs (j + 1) < a := by
    intro a ha
    exact (mem_highScalePart.mp ha).2
  have hA₂prime : ∀ a ∈ A₂, a.Prime := by
    intro a ha
    by_contra hnot
    have halt : a < z₀ := hcomp a (hA₂sub ha) hnot
    have hzle : z₀ ≤ zs (j + 1) :=
      hzs.monotone (Nat.zero_le (j + 1))
    exact (not_lt_of_ge hzle) ((hA₂large a ha).trans halt)
  have hBcomp : ∀ a ∈ B, ¬a.Prime → a < zs k + 1 := by
    intro a ha hnot
    have halt : a < z₀ := hcomp a (hBsub ha) hnot
    have hzle : z₀ ≤ zs k := hzs.monotone (Nat.zero_le k)
    omega
  have hA₂comp : ∀ a ∈ A₂, ¬a.Prime → a < zs k + 1 := by
    intro a ha hnot
    exact (hnot (hA₂prime a ha)).elim
  have hposB : ∀ a ∈ B, 0 < a := by
    intro a ha
    have := hA.two_le (hBsub ha)
    omega
  have hA₂endpoint : ∀ a ∈ A₂, a ≤ N := by
    intro a ha
    exact hA.le_endpoint (hA₂sub ha)
  have hpowj : (zs j) ^ r ≤ N := by
    exact (Nat.pow_le_pow_left (hzs.monotone hjk.le) r).trans hpowN
  have hsplit :
      |truncatedSieveApprox N B r -
          truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| ≤
        factorialTail C r + η := by
    exact splittingScaleSeq_spec hC.le hη r z₀ j hz₀ hdisj hposB
      hB.mass_le hA₁small hA₂prime hA₂large hA₂endpoint
  have hbrun :
      |truncatedSieveApprox N A₁ r - periodicDensity A₁| ≤
        factorialTail C r := by
    exact pureBrunApproximation hC.le hA₁.mass_le (hzspos j)
      hA₁small hpowj
  have hbonfB :
      |sieveDensity N B - truncatedSieveApprox N B r| <
        C ^ (r + 1) / (r + 1).factorial + η := by
    exact hbonfN B hB hBcomp
  have hbonfA₂ :
      |sieveDensity N A₂ - truncatedSieveApprox N A₂ r| <
        C ^ (r + 1) / (r + 1).factorial + η := by
    exact hbonfN A₂ hA₂ hA₂comp
  have hpA₂ :
      dickmanRho (Real.exp (reciprocalMass A₂)) - η <
        sieveDensity N A₂ := hpN A₂ hA₂ hA₂prime
  have hNpos : 0 < N := by omega
  have hsdiff : A \ B = scaleGap A zs j := by
    dsimp only [B, A₁, A₂]
    exact sdiff_union_low_high_eq_scaleGap A zs j
  have hlipschitz :
      sieveDensity N B - reciprocalMass (scaleGap A zs j) ≤
        sieveDensity N A := by
    rw [← hsdiff]
    exact sieveDensity_sub_mass_sdiff_le hNpos B A
  have hA₁two : ∀ a ∈ A₁, 2 ≤ a := by
    intro a ha
    exact hA.two_le (hA₁sub ha)
  have hp1nonneg : 0 ≤ periodicDensity A₁ :=
    periodicDensity_nonneg hA₁two
  have hp1le : periodicDensity A₁ ≤ 1 :=
    periodicDensity_le_one hA₁two
  have hd2nonneg : 0 ≤ sieveDensity N A₂ := sieveDensity_nonneg N A₂
  have hd2le : sieveDensity N A₂ ≤ 1 := sieveDensity_le_one hNpos A₂
  have ht2diff :
      |truncatedSieveApprox N A₂ r - sieveDensity N A₂| < 2 * η := by
    rw [abs_sub_comm]
    linarith
  have ht2abs : |truncatedSieveApprox N A₂ r| < 2 := by
    calc
      |truncatedSieveApprox N A₂ r| ≤
          |truncatedSieveApprox N A₂ r - sieveDensity N A₂| +
            |sieveDensity N A₂| := by
          simpa using
            (abs_add_le (truncatedSieveApprox N A₂ r - sieveDensity N A₂)
              (sieveDensity N A₂))
      _ < 2 * η + 1 := by
        rw [abs_of_nonneg hd2nonneg]
        linarith
      _ ≤ 2 := by linarith
  have hprodApprox :
      |truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r -
          periodicDensity A₁ * sieveDensity N A₂| < 4 * η := by
    rw [show truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r -
          periodicDensity A₁ * sieveDensity N A₂ =
        (truncatedSieveApprox N A₁ r - periodicDensity A₁) *
            truncatedSieveApprox N A₂ r +
          periodicDensity A₁ *
            (truncatedSieveApprox N A₂ r - sieveDensity N A₂) by ring]
    calc
      |(truncatedSieveApprox N A₁ r - periodicDensity A₁) *
            truncatedSieveApprox N A₂ r +
          periodicDensity A₁ *
            (truncatedSieveApprox N A₂ r - sieveDensity N A₂)| ≤
          |truncatedSieveApprox N A₁ r - periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r| +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        calc
          _ ≤ |(truncatedSieveApprox N A₁ r - periodicDensity A₁) *
                  truncatedSieveApprox N A₂ r| +
                |periodicDensity A₁ *
                  (truncatedSieveApprox N A₂ r - sieveDensity N A₂)| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ η * |truncatedSieveApprox N A₂ r| +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (hbrun.trans (le_of_lt hr)) (abs_nonneg _)
        · exact le_rfl
      _ < η * 2 +
            |periodicDensity A₁| *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left ht2abs hη) le_rfl
      _ ≤ η * 2 + 1 *
              |truncatedSieveApprox N A₂ r - sieveDensity N A₂| := by
        rw [abs_of_nonneg hp1nonneg]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hp1le (abs_nonneg _))
      _ < η * 2 + 1 * (2 * η) := by
        exact add_lt_add_of_le_of_lt le_rfl
          (mul_lt_mul_of_pos_left ht2diff zero_lt_one)
      _ = 4 * η := by ring
  have hBproduct :
      periodicDensity A₁ * sieveDensity N A₂ - 8 * η <
        sieveDensity N B := by
    have hsplit' :
        |truncatedSieveApprox N B r -
            truncatedSieveApprox N A₁ r * truncatedSieveApprox N A₂ r| <
          2 * η := hsplit.trans_lt (by linarith)
    have hbonfB' :
        |sieveDensity N B - truncatedSieveApprox N B r| < 2 * η := by
      linarith
    rw [abs_lt] at hsplit' hbonfB' hprodApprox
    rcases hsplit' with ⟨hsplitLower, hsplitUpper⟩
    rcases hbonfB' with ⟨hbonfLower, hbonfUpper⟩
    rcases hprodApprox with ⟨hprodLower, hprodUpper⟩
    linarith
  have hprimeProduct :
      periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) - η <
        periodicDensity A₁ * sieveDensity N A₂ := by
    by_cases hp1zero : periodicDensity A₁ = 0
    · rw [hp1zero]
      simp only [zero_mul]
      linarith
    · have hp1pos : 0 < periodicDensity A₁ :=
        lt_of_le_of_ne hp1nonneg (Ne.symm hp1zero)
      have hm := mul_lt_mul_of_pos_left hpA₂ hp1pos
      have hηscale : periodicDensity A₁ * η ≤ η := by
        nlinarith
      calc
        periodicDensity A₁ *
              dickmanRho (Real.exp (reciprocalMass A₂)) - η ≤
            periodicDensity A₁ *
              dickmanRho (Real.exp (reciprocalMass A₂)) -
                periodicDensity A₁ * η := by linarith
        _ = periodicDensity A₁ *
              (dickmanRho (Real.exp (reciprocalMass A₂)) - η) := by ring
        _ < periodicDensity A₁ * sieveDensity N A₂ := hm
  have hbridge :
      dickmanRho
          (Real.exp (reciprocalMass A₁ + reciprocalMass A₂)) ≤
        periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) :=
    periodicDensity_mul_dickmanRho_ge hprod hA₁two
      (reciprocalMass_nonneg A₂)
  have hmassB :
      reciprocalMass B = reciprocalMass A₁ + reciprocalMass A₂ := by
    dsimp only [B, reciprocalMass]
    exact Finset.sum_union hdisj
  have hCbridge :
      dickmanRho (Real.exp C) ≤
        dickmanRho
          (Real.exp (reciprocalMass A₁ + reciprocalMass A₂)) := by
    rw [← hmassB]
    exact antitoneOn_dickmanRho_Ici_zero
      (Real.exp_pos _).le (Real.exp_pos _).le
      (Real.exp_le_exp.mpr hB.mass_le)
  calc
    dickmanRho (Real.exp C) - ε <
        dickmanRho (Real.exp C) - 10 * η := by
      have : 10 * η < ε := by linarith
      linarith
    _ ≤ periodicDensity A₁ *
          dickmanRho (Real.exp (reciprocalMass A₂)) - 10 * η := by
      linarith
    _ < periodicDensity A₁ * sieveDensity N A₂ - 9 * η := by
      linarith
    _ < sieveDensity N B - η := by
      linarith
    _ < sieveDensity N B - reciprocalMass (scaleGap A zs j) := by
      linarith
    _ ≤ sieveDensity N A := hlipschitz

/-- Tao's composite-removal step: an endpoint-uniform estimate with bounded
composite moduli implies the unrestricted estimate. -/
theorem taoLowerBound_of_boundedComposite { ρ : ℝ → ℝ }
    (hBounded : BoundedCompositeLowerBound ρ) :
    TaoLowerBound ρ := by
  intro C hC ε hε
  have heventuallyTail :
      ∀ᶠ z : ℕ in atTop, 2 / (z.sqrt : ℝ) < ε / 2 :=
    tendsto_uniformCompositeTailBound
      (Iio_mem_nhds (half_pos hε))
  rw [eventually_atTop] at heventuallyTail
  obtain ⟨z₀, hz₀⟩ := heventuallyTail
  let z := max z₀ 1
  have hz₀z : z₀ ≤ z := le_max_left _ _
  have hz : 0 < z := zero_lt_one.trans_le (le_max_right _ _)
  have htail : 2 / (z.sqrt : ℝ) < ε / 2 := hz₀ z hz₀z
  have hbounded := hBounded C hC (ε / 2) (half_pos hε) z hz
  rw [eventually_atTop] at hbounded
  obtain ⟨N₀, hN₀⟩ := hbounded
  rw [eventually_atTop]
  refine ⟨max N₀ 1, ?_⟩
  intro N hN A hA
  have hN₀N : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hNpos : 0 < N := zero_lt_one.trans_le
    ((le_max_right N₀ 1).trans hN)
  let B := primeOrSmallCompositePart A z
  have hB : Admissible C N B := admissible_primeOrSmallCompositePart hA
  have hBcomp : ∀ a ∈ B, ¬a.Prime → a < z := by
    intro a ha hprime
    have ha' := (Finset.mem_filter.mp ha).2
    exact ha'.resolve_left hprime
  have hlowerB : ρ (Real.exp C) - ε / 2 < sieveDensity N B :=
    hN₀ N hN₀N B hB hBcomp
  have hreduce := sieveDensity_primeOrSmallCompositePart_sub_le
    hA hNpos hz
  dsimp only [B] at hlowerB hreduce
  linarith

/-- The matching upper bound, stated as the existence of an admissible
family at every sufficiently large endpoint.  The terminal block of primes
is the canonical witness in the proof. -/
def TerminalPrimeAchievability (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
      Admissible C N A ∧ sieveDensity N A < ρ (Real.exp C) + ε

/-- The fixed-parameter smooth-number theorem plus Mertens' theorem yields
the matching terminal-prime upper bound.  A vanishing positive underspend
keeps the finite reciprocal mass on the admissible side of the budget. -/
theorem terminalPrimeAchievability_of_powerCutoffSmooth
    (hSmooth : PowerCutoffSmoothAsymptotic dickmanRho) :
    TerminalPrimeAchievability dickmanRho := by
  intro C hC ε hε
  let η : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hη : Tendsto η atTop (nhds 0) := by
    simpa [η, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have harg :
      Tendsto (fun n : ℕ => Real.exp (C - η n)) atTop
        (nhds (Real.exp C)) := by
    change Tendsto (Real.exp ∘ fun n : ℕ => C - η n) atTop
      (nhds (Real.exp C))
    have hsub :
        Tendsto (fun n : ℕ => C - η n) atTop (nhds (C - 0)) :=
      tendsto_const_nhds.sub hη
    have hcomp := Real.continuous_exp.continuousAt.tendsto.comp hsub
    simpa only [sub_zero] using hcomp
  have hρ :
      Tendsto (fun n : ℕ => dickmanRho (Real.exp (C - η n))) atTop
        (nhds (dickmanRho (Real.exp C))) :=
    (continuousAt_dickmanRho_of_pos (Real.exp_pos C)).tendsto.comp harg
  have hρEventually :
      ∀ᶠ n : ℕ in atTop,
        dickmanRho (Real.exp (C - η n)) <
          dickmanRho (Real.exp C) + ε / 2 :=
    hρ.eventually (Iio_mem_nhds (by linarith))
  have hηEventually : ∀ᶠ n : ℕ in atTop, η n < C := by
    exact hη.eventually (Iio_mem_nhds hC)
  obtain ⟨k, hkρ, hkη⟩ := (hρEventually.and hηEventually).exists
  let δ := η k
  have hδ : 0 < δ := by positivity
  have hδC : δ < C := hkη
  let a := Real.exp (-(C - δ))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hloginv : a⁻¹ = Real.exp (C - δ) := by
    dsimp only [a]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hmassLimit :=
    tendsto_reciprocalMass_terminalPrimeBlock_powerCutoff ha ha1
  have hmassValue : -Real.log a = C - δ := by
    rw [show a = Real.exp (-(C - δ)) by rfl, Real.log_exp]
    ring
  rw [hmassValue] at hmassLimit
  have hmassEventually :
      ∀ᶠ N : ℕ in atTop,
        reciprocalMass (terminalPrimeBlock N (powerCutoff a N)) ≤ C :=
    hmassLimit.eventually (Iio_mem_nhds (by linarith [hδ])) |>.mono
      (fun _ h => h.le)
  have hdensityLimit := hSmooth a ha ha1
  rw [hloginv] at hdensityLimit
  have hdensityEventually :
      ∀ᶠ N : ℕ in atTop,
        ((N.smoothNumbersUpTo (powerCutoff a N + 1)).card : ℝ) /
            (N : ℝ) <
          dickmanRho (Real.exp C) + ε := by
    have htarget :
        dickmanRho (Real.exp (C - δ)) <
          dickmanRho (Real.exp C) + ε / 2 := hkρ
    exact hdensityLimit.eventually
      (Iio_mem_nhds (by linarith [hε]))
  filter_upwards [hmassEventually, hdensityEventually] with N hmass hdensity
  refine ⟨terminalPrimeBlock N (powerCutoff a N),
    admissible_terminalPrimeBlock hmass, ?_⟩
  rw [sieveDensity_terminalPrimeBlock]
  exact hdensity

/-- The smooth-number theorem proved above discharges every analytic
hypothesis in the terminal-prime construction. -/
theorem terminalPrimeAchievability_dickmanRho :
    TerminalPrimeAchievability dickmanRho :=
  terminalPrimeAchievability_of_powerCutoffSmooth
    powerCutoffSmoothAsymptotic_dickmanRho

/-- The exact asymptotic resolution of Problem 783. -/
def AsymptoticResolution (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C →
    Tendsto (minimumDensity C) atTop (nhds (ρ (Real.exp C)))

/-- Once the uniform Tao lower bound and the terminal-prime construction
are established, the literal finite minima converge by squeezing. -/
theorem asymptoticResolution_of_lower_of_achievable {ρ : ℝ → ℝ}
    (hLower : TaoLowerBound ρ)
    (hUpper : TerminalPrimeAchievability ρ) :
    AsymptoticResolution ρ := by
  intro C hC
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hL := hLower C hC ε hε
  have hU := hUpper C hC ε hε
  rw [eventually_atTop] at hL hU
  obtain ⟨NL, hL⟩ := hL
  obtain ⟨NU, hU⟩ := hU
  refine ⟨max NL NU, ?_⟩
  intro N hN
  have hLN := hL N ((le_max_left NL NU).trans hN)
  have hUN := hU N ((le_max_right NL NU).trans hN)
  obtain ⟨Amin, hAmin, hmin⟩ :=
    exists_admissible_minimizer hC.le N
  have hlower : ρ (Real.exp C) - ε < minimumDensity C N := by
    simpa [hmin] using hLN Amin hAmin
  obtain ⟨A, hA, hAdensity⟩ := hUN
  have hupper : minimumDensity C N < ρ (Real.exp C) + ε :=
    (minimumDensity_le hC.le hA).trans_lt hAdensity
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end

end Erdos783
