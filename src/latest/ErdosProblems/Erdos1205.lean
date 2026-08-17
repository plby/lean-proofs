/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1205

For every modulus `1 ≤ n ≤ x`, choose one residue class modulo `n`.
The function `coveringNumber x` is the largest number of those congruences
that can be satisfied simultaneously by every integer in `{1, ..., x}`.

This file proves that `coveringNumber x ∼ log x`.  A detailed mathematical
proof and Leanization plan are in `tex/1205.tex`.
-/

open Filter Finset Set
open scoped Asymptotics BigOperators Topology

namespace Erdos1205

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A choice of one residue for each modulus `1, ..., x`.
The index `i : Fin x` represents modulus `i + 1`. -/
abbrev Assignment (x : ℕ) := (i : Fin x) → Fin (i.1 + 1)

/-- Whether the positive integer represented by `m` lies in the residue
chosen at the modulus represented by `i`. -/
def Covers {x : ℕ} (a : Assignment x) (m i : Fin x) : Prop :=
  (m.1 + 1) % (i.1 + 1) = (a i).1

/-- The number of chosen congruences satisfied by a point. -/
def coverage {x : ℕ} (a : Assignment x) (m : Fin x) : ℕ :=
  ((Finset.univ : Finset (Fin x)).filter fun i ↦ Covers a m i).card

/-- There is an assignment giving every point at least `k` incidences.
The explicit bound `k ≤ x` makes the empty interval behave correctly. -/
def IsCovering (x k : ℕ) : Prop :=
  k ≤ x ∧ ∃ a : Assignment x, ∀ m : Fin x, k ≤ coverage a m

/-- Erdős's extremal function `F(x)`. -/
def coveringNumber (x : ℕ) : ℕ :=
  Nat.findGreatest (IsCovering x) x

/-- The all-zero residue assignment. -/
def zeroAssignment (x : ℕ) : Assignment x :=
  fun i ↦ ⟨0, Nat.succ_pos i.1⟩

lemma isCovering_zero (x : ℕ) : IsCovering x 0 := by
  refine ⟨Nat.zero_le x, zeroAssignment x, ?_⟩
  intro m
  exact Nat.zero_le _

lemma coveringNumber_le (x : ℕ) : coveringNumber x ≤ x :=
  Nat.findGreatest_le x

lemma coveringNumber_spec (x : ℕ) : IsCovering x (coveringNumber x) := by
  exact Nat.findGreatest_spec (Nat.zero_le x) (isCovering_zero x)

lemma le_coveringNumber {x k : ℕ} (h : IsCovering x k) :
    k ≤ coveringNumber x := by
  exact Nat.le_findGreatest h.1 h

/-! ## The average-incidence upper bound -/

/-- A set contained in one residue class modulo `d` has at most `x / d + 1`
members in `{1, ..., x}`. -/
lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {x d : ℕ}
    (hsx : s ⊆ Finset.Icc 1 x) (_hd : 0 < d)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD d]) :
    s.card ≤ x / d + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / d
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % d = b % d := hmod a ha b hb
    have hda : d * (a / d) + a % d = a := Nat.div_add_mod a d
    have hdb : d * (b / d) + b % d = b := Nat.div_add_mod b d
    dsimp [f] at hab
    calc
      a = d * (a / d) + a % d := hda.symm
      _ = d * (b / d) + b % d := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (x / d + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp (hsx ha)).2)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (x / d + 1)).card := Finset.card_le_card himage
    _ = x / d + 1 := Finset.card_range _

/-- The fibre of one selected congruence among the positive points. -/
def congruenceFiber {x : ℕ} (a : Assignment x) (i : Fin x) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun m ↦ m % (i.1 + 1) = (a i).1

lemma card_congruenceFiber_le {x : ℕ} (a : Assignment x) (i : Fin x) :
    (congruenceFiber a i).card ≤ x / (i.1 + 1) + 1 := by
  apply card_le_div_add_one_of_pairwise_modEq (Finset.filter_subset _ _)
    (Nat.succ_pos i.1)
  intro m hm n hn
  exact (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm

/-- The `Fin x` fibre and its positive-natural-number version have the same
cardinality. -/
lemma card_filter_covers_eq_fiber {x : ℕ} (a : Assignment x) (i : Fin x) :
    ((Finset.univ : Finset (Fin x)).filter fun m ↦ Covers a m i).card =
      (congruenceFiber a i).card := by
  let f : Fin x → ℕ := fun m ↦ m.1 + 1
  refine Finset.card_bij (fun m _ ↦ f m) ?_ ?_ ?_
  · intro m hm
    rw [congruenceFiber, Finset.mem_filter]
    rw [Finset.mem_filter] at hm
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _), m.2⟩, hm.2⟩
  · intro m₁ hm₁ m₂ hm₂ h
    dsimp [f] at h
    apply Fin.ext
    omega
  · intro n hn
    rw [congruenceFiber, Finset.mem_filter] at hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn.1
    let m₀ : Fin x := ⟨n - 1, by omega⟩
    have hm₀ : m₀ ∈ (Finset.univ : Finset (Fin x)).filter fun m ↦ Covers a m i := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (n - 1 + 1) % (i.1 + 1) = (a i).1
      have hnback : n - 1 + 1 = n := by omega
      rw [hnback]
      exact hn.2
    refine ⟨m₀, hm₀, ?_⟩
    dsimp [f, m₀]
    omega

/-- Double-count incidences by points or by moduli. -/
lemma sum_coverage_eq_sum_fibers {x : ℕ} (a : Assignment x) :
    ∑ m : Fin x, coverage a m = ∑ i : Fin x, (congruenceFiber a i).card := by
  simp only [coverage, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← card_filter_covers_eq_fiber a i, Finset.card_filter]

lemma sum_congruenceFiber_le {x : ℕ} (a : Assignment x) :
    (∑ i : Fin x, (congruenceFiber a i).card : ℝ) ≤
      (x : ℝ) * (harmonic x : ℝ) + x := by
  calc
    (∑ i : Fin x, (congruenceFiber a i).card : ℝ)
        ≤ ∑ i : Fin x, ((x : ℝ) / (i.1 + 1) + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            ((congruenceFiber a i).card : ℝ)
                ≤ ((x / (i.1 + 1) + 1 : ℕ) : ℝ) := by
                  exact_mod_cast card_congruenceFiber_le a i
            _ ≤ (x : ℝ) / (i.1 + 1) + 1 := by
                  have hdiv : ((x / (i.1 + 1) : ℕ) : ℝ) ≤
                      (x : ℝ) / ((i.1 + 1 : ℕ) : ℝ) := Nat.cast_div_le
                  norm_num at hdiv ⊢
                  linarith
    _ = (x : ℝ) * (harmonic x : ℝ) + x := by
      calc
        (∑ i : Fin x, ((x : ℝ) / (i.1 + 1) + 1)) =
            (∑ i : Fin x, (x : ℝ) / (i.1 + 1)) + x := by
              rw [Finset.sum_add_distrib]
              simp
        _ = (∑ i ∈ Finset.range x,
              (x : ℝ) / (((i + 1 : ℕ) : ℝ))) + x := by
              congr 1
              simpa [Nat.cast_add, Nat.cast_one] using
                Fin.sum_univ_eq_sum_range
                  (fun i : ℕ ↦ (x : ℝ) / (((i + 1 : ℕ) : ℝ))) x
        _ = (x : ℝ) * (harmonic x : ℝ) + x := by
              rw [harmonic, Rat.cast_sum]
              simp only [Rat.cast_inv, Rat.cast_natCast]
              rw [Finset.mul_sum]
              simp only [div_eq_mul_inv]

/-- Every feasible common coverage is bounded by the average incidence. -/
lemma isCovering_real_le_harmonic_add_one {x k : ℕ} (hx : 0 < x)
    (h : IsCovering x k) :
    (k : ℝ) ≤ (harmonic x : ℝ) + 1 := by
  obtain ⟨hkx, a, ha⟩ := h
  have hlower : (x : ℝ) * k ≤ ∑ m : Fin x, (coverage a m : ℝ) := by
    calc
      (x : ℝ) * k = ∑ _m : Fin x, (k : ℝ) := by simp
      _ ≤ ∑ m : Fin x, (coverage a m : ℝ) := by
        gcongr with m
        exact_mod_cast ha m
  have hupper : (∑ m : Fin x, (coverage a m : ℝ)) ≤
      (x : ℝ) * (harmonic x : ℝ) + x := by
    have heq : (∑ m : Fin x, (coverage a m : ℝ)) =
        ∑ i : Fin x, ((congruenceFiber a i).card : ℝ) := by
      exact_mod_cast sum_coverage_eq_sum_fibers a
    rw [heq]
    exact sum_congruenceFiber_le a
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  nlinarith [hlower.trans hupper]

/-- Exact finite upper bound, including the endpoint term. -/
theorem coveringNumber_le_harmonic_add_one (x : ℕ) :
    (coveringNumber x : ℝ) ≤ (harmonic x : ℝ) + 1 := by
  obtain rfl | hx := x.eq_zero_or_pos
  · simp [coveringNumber]
  · exact isCovering_real_le_harmonic_add_one hx (coveringNumber_spec x)

/-! ## A finite Chernoff argument

The proof is carried out by summing exponential weights over the finite type
of all assignments.  Thus the probabilistic method below has no measure-space
or measurability overhead: division by the number of assignments is postponed
until the final averaging step.
-/

/-- Coverage of an arbitrary positive integer by an assignment on the first
`N` moduli.  In the application the integer may be larger than `N`. -/
def partialCoverage {N : ℕ} (a : Assignment N) (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter fun i ↦
    m % (i.1 + 1) = (a i).1).card

/-- The real-valued indicator of one congruence incidence. -/
def hitIndicator {N : ℕ} (a : Assignment N) (m : ℕ) (i : Fin N) : ℝ :=
  if m % (i.1 + 1) = (a i).1 then 1 else 0

lemma cast_partialCoverage {N : ℕ} (a : Assignment N) (m : ℕ) :
    (partialCoverage a m : ℝ) = ∑ i : Fin N, hitIndicator a m i := by
  rw [partialCoverage, Finset.card_eq_sum_ones, Nat.cast_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hitIndicator]

/-- The only analytic estimate needed for the finite Chernoff calculation. -/
lemma exp_neg_le_one_sub_add_sq {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 := by
  have habs : |Real.exp (-t) - 1 - (-t)| ≤ (-t) ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by simpa [abs_of_nonneg ht₀] using ht₁)
  have hself : Real.exp (-t) - 1 - (-t) ≤
      |Real.exp (-t) - 1 - (-t)| := le_abs_self _
  nlinarith

/-- Moment-generating-function bound for one Bernoulli variable of mean `p`.
The form used here is deliberately slightly weaker than the usual `t²/2`
bound, which keeps the elementary proof short. -/
lemma bernoulli_centered_factor_le {p t : ℝ} (hp₀ : 0 ≤ p) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    Real.exp (t * p) * (1 + p * (Real.exp (-t) - 1)) ≤
      Real.exp (p * t ^ 2) := by
  have he : Real.exp (-t) - 1 ≤ -t + t ^ 2 := by
    linarith [exp_neg_le_one_sub_add_sq ht₀ ht₁]
  have hlin : 1 + p * (Real.exp (-t) - 1) ≤ 1 + p * (-t + t ^ 2) := by
    gcongr
  have hexp : 1 + p * (-t + t ^ 2) ≤ Real.exp (p * (-t + t ^ 2)) := by
    simpa [add_comm] using Real.add_one_le_exp (p * (-t + t ^ 2))
  calc
    Real.exp (t * p) * (1 + p * (Real.exp (-t) - 1))
        ≤ Real.exp (t * p) * (1 + p * (-t + t ^ 2)) := by
          gcongr
    _ ≤ Real.exp (t * p) * Real.exp (p * (-t + t ^ 2)) := by
          gcongr
    _ = Real.exp (p * t ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- The sum of the centered exponential weight over all residues modulo `d`.
Exactly one residue is a hit. -/
lemma sum_exp_centered_indicator_le (d m : ℕ) (hd : 0 < d) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∑ r : Fin d, Real.exp
      (t * (((d : ℝ)⁻¹) - if m % d = r.1 then 1 else 0))) ≤
      (d : ℝ) * Real.exp ((d : ℝ)⁻¹ * t ^ 2) := by
  let q : Fin d := ⟨m % d, Nat.mod_lt _ hd⟩
  have hsum :
      (∑ r : Fin d, Real.exp
        (t * (((d : ℝ)⁻¹) - if m % d = r.1 then 1 else 0))) =
        Real.exp (t * ((d : ℝ)⁻¹ - 1)) +
          (d - 1 : ℕ) * Real.exp (t * (d : ℝ)⁻¹) := by
    calc
      (∑ r : Fin d, Real.exp
          (t * (((d : ℝ)⁻¹) - if m % d = r.1 then 1 else 0))) =
          Real.exp (t * ((d : ℝ)⁻¹ - 1)) +
            ∑ r ∈ (Finset.univ : Finset (Fin d)).erase q,
              Real.exp (t * ((d : ℝ)⁻¹ - if m % d = r.1 then 1 else 0)) := by
                symm
                calc
                  _ = (∑ r ∈ (Finset.univ : Finset (Fin d)).erase q,
                      Real.exp (t * ((d : ℝ)⁻¹ -
                        if m % d = r.1 then 1 else 0))) +
                        Real.exp (t * ((d : ℝ)⁻¹ - 1)) := by ring
                  _ = _ := by
                    convert Finset.sum_erase_add
                      (Finset.univ : Finset (Fin d))
                      (fun r ↦ Real.exp (t * ((d : ℝ)⁻¹ -
                        if m % d = r.1 then 1 else 0))) (Finset.mem_univ q) using 1
                    simp [q]
      _ = Real.exp (t * ((d : ℝ)⁻¹ - 1)) +
          ∑ _r ∈ (Finset.univ : Finset (Fin d)).erase q,
            Real.exp (t * (d : ℝ)⁻¹) := by
              congr 1
              apply Finset.sum_congr rfl
              intro r hr
              have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
              have hne : m % d ≠ r.1 := by
                intro h
                apply hrq
                apply Fin.ext
                simpa [q] using h.symm
              simp [hne]
      _ = Real.exp (t * ((d : ℝ)⁻¹ - 1)) +
          (d - 1 : ℕ) * Real.exp (t * (d : ℝ)⁻¹) := by
            congr 1
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ q),
              Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp₀ : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hdR)
  have hfactor := bernoulli_centered_factor_le hp₀ ht₀ ht₁
  rw [hsum]
  calc
    Real.exp (t * ((d : ℝ)⁻¹ - 1)) +
          (d - 1 : ℕ) * Real.exp (t * (d : ℝ)⁻¹) =
        (d : ℝ) * (Real.exp (t * (d : ℝ)⁻¹) *
          (1 + (d : ℝ)⁻¹ * (Real.exp (-t) - 1))) := by
            rw [show Real.exp (t * ((d : ℝ)⁻¹ - 1)) =
                Real.exp (t * (d : ℝ)⁻¹) * Real.exp (-t) by
              rw [← Real.exp_add]
              congr 1
              ring]
            have hdcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
              rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne')]
              simp
            rw [hdcast]
            field_simp
            ring
    _ ≤ (d : ℝ) * Real.exp ((d : ℝ)⁻¹ * t ^ 2) := by
          gcongr

lemma harmonic_cast_eq_sum_fin (N : ℕ) :
    (harmonic N : ℝ) = ∑ i : Fin N, ((i.1 + 1 : ℕ) : ℝ)⁻¹ := by
  rw [harmonic, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (((i + 1 : ℕ) : ℝ)⁻¹)) N).symm

/-- The centered exponential weight attached to one assignment and point. -/
def exponentialWeight {N : ℕ} (a : Assignment N) (m : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t * ((harmonic N : ℝ) - partialCoverage a m))

lemma exponentialWeight_eq_prod {N : ℕ} (a : Assignment N) (m : ℕ) (t : ℝ) :
    exponentialWeight a m t =
      ∏ i : Fin N, Real.exp
        (t * (((i.1 + 1 : ℕ) : ℝ)⁻¹ - hitIndicator a m i)) := by
  rw [exponentialWeight, ← Real.exp_sum]
  congr 1
  rw [cast_partialCoverage, harmonic_cast_eq_sum_fin]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Finite-product Chernoff estimate, before normalizing by the number of
assignments. -/
lemma sum_exponentialWeight_le (N m : ℕ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∑ a : Assignment N, exponentialWeight a m t) ≤
      (Fintype.card (Assignment N) : ℝ) *
        Real.exp ((harmonic N : ℝ) * t ^ 2) := by
  calc
    (∑ a : Assignment N, exponentialWeight a m t) =
        ∑ a : Assignment N, ∏ i : Fin N, Real.exp
          (t * (((i.1 + 1 : ℕ) : ℝ)⁻¹ - hitIndicator a m i)) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact exponentialWeight_eq_prod a m t
    _ = ∏ i : Fin N, ∑ r : Fin (i.1 + 1), Real.exp
          (t * (((i.1 + 1 : ℕ) : ℝ)⁻¹ -
            if m % (i.1 + 1) = r.1 then 1 else 0)) := by
            rw [Fintype.prod_sum]
            rfl
    _ ≤ ∏ i : Fin N, ((i.1 + 1 : ℕ) : ℝ) *
          Real.exp (((i.1 + 1 : ℕ) : ℝ)⁻¹ * t ^ 2) := by
            apply Finset.prod_le_prod
            · intro i hi
              positivity
            · intro i hi
              exact sum_exp_centered_indicator_le (i.1 + 1) m
                (Nat.succ_pos i.1) ht₀ ht₁
    _ = (Fintype.card (Assignment N) : ℝ) *
          Real.exp ((harmonic N : ℝ) * t ^ 2) := by
            rw [Finset.prod_mul_distrib, ← Real.exp_sum]
            congr 1
            · simp [Assignment]
            · rw [harmonic_cast_eq_sum_fin]
              rw [Finset.sum_mul]

/-- Assignments for the first `N` moduli which cover `m` fewer than `k`
times. -/
def badAssignments (N m k : ℕ) : Finset (Assignment N) :=
  (Finset.univ : Finset (Assignment N)).filter fun a ↦ partialCoverage a m < k

/-- Chernoff's lower-tail estimate as a cardinality inequality on the finite
set of all assignments. -/
lemma card_badAssignments_le (N m k : ℕ) (_hk : 0 < k) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ((badAssignments N m k).card : ℝ) ≤
      (Fintype.card (Assignment N) : ℝ) *
        Real.exp ((harmonic N : ℝ) * t ^ 2 -
          t * ((harmonic N : ℝ) - (k - 1 : ℕ))) := by
  let L : ℝ := Real.exp
    (t * ((harmonic N : ℝ) - (k - 1 : ℕ)))
  have hpoint : ∀ a ∈ badAssignments N m k, L ≤ exponentialWeight a m t := by
    intro a ha
    have hcov : partialCoverage a m ≤ k - 1 := by
      exact Nat.le_sub_one_of_lt (Finset.mem_filter.mp ha).2
    have hcovR : (partialCoverage a m : ℝ) ≤ (k - 1 : ℕ) := by
      exact_mod_cast hcov
    apply Real.exp_le_exp.mpr
    gcongr
  have hsum_bad : ((badAssignments N m k).card : ℝ) * L ≤
      ∑ a : Assignment N, exponentialWeight a m t := by
    calc
      ((badAssignments N m k).card : ℝ) * L =
          ∑ _a ∈ badAssignments N m k, L := by
            simp [mul_comm]
      _ ≤ ∑ a ∈ badAssignments N m k, exponentialWeight a m t := by
            apply Finset.sum_le_sum
            intro a ha
            exact hpoint a ha
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Assignment N)),
          exponentialWeight a m t := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro a ha hnot
            exact (Real.exp_pos _).le
      _ = ∑ a : Assignment N, exponentialWeight a m t := rfl
  have htotal := hsum_bad.trans (sum_exponentialWeight_le N m ht₀ ht₁)
  have hL : 0 < L := by positivity
  calc
    ((badAssignments N m k).card : ℝ) ≤
        ((Fintype.card (Assignment N) : ℝ) *
          Real.exp ((harmonic N : ℝ) * t ^ 2)) / L :=
      (le_div_iff₀ hL).2 htotal
    _ = (Fintype.card (Assignment N) : ℝ) *
        Real.exp ((harmonic N : ℝ) * t ^ 2 -
          t * ((harmonic N : ℝ) - (k - 1 : ℕ))) := by
      dsimp [L]
      rw [Real.exp_sub, div_eq_mul_inv]
      ring

/-- Points in `{1, ..., x}` which receive fewer than `k` hits from the first
`N` moduli. -/
def badPoints (x N k : ℕ) (a : Assignment N) : Finset (Fin x) :=
  (Finset.univ : Finset (Fin x)).filter fun m ↦ partialCoverage a (m.1 + 1) < k

/-- Averaging the pointwise Chernoff estimate produces one assignment having
few bad points. -/
lemma exists_assignment_card_badPoints_le (x N k : ℕ) (hk : 0 < k) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ∃ a : Assignment N,
      ((badPoints x N k a).card : ℝ) ≤
        (x : ℝ) * Real.exp ((harmonic N : ℝ) * t ^ 2 -
          t * ((harmonic N : ℝ) - (k - 1 : ℕ))) := by
  let C : ℝ := (x : ℝ) * Real.exp ((harmonic N : ℝ) * t ^ 2 -
    t * ((harmonic N : ℝ) - (k - 1 : ℕ)))
  have hdouble :
      (∑ a : Assignment N, ((badPoints x N k a).card : ℝ)) =
        ∑ m : Fin x, ((badAssignments N (m.1 + 1) k).card : ℝ) := by
    simp only [badPoints, badAssignments, Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
  have hsum :
      (∑ a : Assignment N, ((badPoints x N k a).card : ℝ)) ≤
        ∑ _a : Assignment N, C := by
    rw [hdouble]
    calc
      (∑ m : Fin x, ((badAssignments N (m.1 + 1) k).card : ℝ)) ≤
          ∑ _m : Fin x,
            (Fintype.card (Assignment N) : ℝ) *
              Real.exp ((harmonic N : ℝ) * t ^ 2 -
                t * ((harmonic N : ℝ) - (k - 1 : ℕ))) := by
                  apply Finset.sum_le_sum
                  intro m hm
                  exact card_badAssignments_le N (m.1 + 1) k hk ht₀ ht₁
      _ = ∑ _a : Assignment N, C := by
            simp [C]
            ring
  obtain ⟨a, ha_mem, ha⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset (Assignment N)))
      Finset.univ_nonempty hsum
  exact ⟨a, by simpa [C] using ha⟩

/-! ## Deterministic repair of the exceptional points -/

/-- Include the first `N` indices among the first `x` indices. -/
def lowIndex {N x : ℕ} (hNx : N ≤ x) : Fin N ↪ Fin x where
  toFun i := ⟨i.1, lt_of_lt_of_le i.2 hNx⟩
  inj' := by
    intro i j hij
    cases i with
    | mk i hi =>
      cases j with
      | mk j hj => simpa using hij

/-- Put an index from a set of size `x-N` into the unused upper block. -/
def upperIndex {N x : ℕ} (hNx : N ≤ x) : Fin (x - N) ↪ Fin x where
  toFun j := ⟨N + j.1, by omega⟩
  inj' := by
    intro i j hij
    cases i with
    | mk i hi =>
      cases j with
      | mk j hj =>
        simp only [Fin.mk.injEq] at hij ⊢
        omega

/-- The upper modulus reserved for one `(bad point, requested hit)` pair. -/
def requestIndex {x N k : ℕ} {a : Assignment N} (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N)) :
    ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin x :=
  e.trans (upperIndex hNx)

/-- Extend a first-block assignment and prescribe the residue of every upper
modulus reserved by `e` to hit its associated bad point. -/
def repairedAssignment {x N k : ℕ} {a : Assignment N} (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N)) :
    Assignment x := fun i ↦
  if hi : i.1 < N then
    ⟨(a ⟨i.1, hi⟩).1, by simpa using (a ⟨i.1, hi⟩).2⟩
  else if hq : ∃ q : {m // m ∈ badPoints x N k a} × Fin k,
      requestIndex hNx e q = i then
    ⟨((Classical.choose hq).1.1.1 + 1) % (i.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  else
    ⟨0, Nat.succ_pos _⟩

lemma repairedAssignment_low {x N k : ℕ} {a : Assignment N} (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N)) (i : Fin N) :
    (repairedAssignment hNx e (lowIndex hNx i)).1 = (a i).1 := by
  change (if hi : i.1 < N then
      (⟨(a ⟨i.1, hi⟩).1, by simpa using (a ⟨i.1, hi⟩).2⟩ : Fin (i.1 + 1))
    else if hq : ∃ q, requestIndex hNx e q = lowIndex hNx i then
      ⟨((Classical.choose hq).1.1.1 + 1) % (i.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    else ⟨0, Nat.succ_pos _⟩).1 = (a i).1
  simp [i.2]

lemma requestIndex_not_low {x N k : ℕ} {a : Assignment N} (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N))
    (q : {m // m ∈ badPoints x N k a} × Fin k) :
    ¬ (requestIndex hNx e q).1 < N := by
  change ¬ N + (e q).1 < N
  omega

lemma repairedAssignment_covers_request {x N k : ℕ} {a : Assignment N}
    (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N))
    (q : {m // m ∈ badPoints x N k a} × Fin k) :
    Covers (repairedAssignment hNx e) q.1.1 (requestIndex hNx e q) := by
  let hq : ∃ q' : {m // m ∈ badPoints x N k a} × Fin k,
      requestIndex hNx e q' = requestIndex hNx e q := ⟨q, rfl⟩
  have hchosen : Classical.choose hq = q := by
    apply (requestIndex hNx e).injective
    exact Classical.choose_spec hq
  simp only [Covers, repairedAssignment, dif_neg (requestIndex_not_low hNx e q),
    dif_pos hq]
  rw [hchosen]

/-- Adding the upper block never decreases the coverage supplied by the first
block. -/
lemma partialCoverage_le_repaired_coverage {x N k : ℕ} {a : Assignment N}
    (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N)) (m : Fin x) :
    partialCoverage a (m.1 + 1) ≤ coverage (repairedAssignment hNx e) m := by
  let s : Finset (Fin N) := (Finset.univ : Finset (Fin N)).filter fun i ↦
    (m.1 + 1) % (i.1 + 1) = (a i).1
  have hsub : s.map (lowIndex hNx) ⊆
      (Finset.univ : Finset (Fin x)).filter fun i ↦
        Covers (repairedAssignment hNx e) m i := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    change (m.1 + 1) % (i.1 + 1) =
      (repairedAssignment hNx e (lowIndex hNx i)).1
    rw [repairedAssignment_low hNx e i]
    exact hi.2
  calc
    partialCoverage a (m.1 + 1) = s.card := rfl
    _ = (s.map (lowIndex hNx)).card := (Finset.card_map _).symm
    _ ≤ ((Finset.univ : Finset (Fin x)).filter fun i ↦
        Covers (repairedAssignment hNx e) m i).card := Finset.card_le_card hsub
    _ = coverage (repairedAssignment hNx e) m := rfl

/-- Each bad point receives `k` distinct prescribed hits in the upper block. -/
lemma k_le_repaired_coverage_of_bad {x N k : ℕ} {a : Assignment N}
    (hNx : N ≤ x)
    (e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N))
    (m : Fin x) (hm : m ∈ badPoints x N k a) :
    k ≤ coverage (repairedAssignment hNx e) m := by
  let g : Fin k ↪ Fin x := {
    toFun := fun r ↦ requestIndex hNx e (⟨m, hm⟩, r)
    inj' := by
      intro r s hrs
      have hpair := (requestIndex hNx e).injective hrs
      exact congrArg Prod.snd hpair }
  have hsub : (Finset.univ : Finset (Fin k)).map g ⊆
      (Finset.univ : Finset (Fin x)).filter fun i ↦
        Covers (repairedAssignment hNx e) m i := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨r, hr, rfl⟩ := hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact repairedAssignment_covers_request hNx e (⟨m, hm⟩, r)
  calc
    k = ((Finset.univ : Finset (Fin k)).map g).card := by simp
    _ ≤ ((Finset.univ : Finset (Fin x)).filter fun i ↦
        Covers (repairedAssignment hNx e) m i).card := Finset.card_le_card hsub
    _ = coverage (repairedAssignment hNx e) m := rfl

/-- If there are enough unused upper moduli, all exceptional points can be
repaired, with `k` distinct moduli allocated to each one. -/
lemma exists_full_assignment_of_badPoints_mul_le {x N k : ℕ} (hNx : N ≤ x)
    (a : Assignment N) (hcap : (badPoints x N k a).card * k ≤ x - N) :
    ∃ A : Assignment x, ∀ m : Fin x, k ≤ coverage A m := by
  have hcard : Fintype.card ({m // m ∈ badPoints x N k a} × Fin k) ≤
      Fintype.card (Fin (x - N)) := by
    simpa using hcap
  let e : ({m // m ∈ badPoints x N k a} × Fin k) ↪ Fin (x - N) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  refine ⟨repairedAssignment hNx e, ?_⟩
  intro m
  by_cases hm : m ∈ badPoints x N k a
  · exact k_le_repaired_coverage_of_bad hNx e m hm
  · have hgood : k ≤ partialCoverage a (m.1 + 1) := by
      apply Nat.le_of_not_gt
      intro hlt
      exact hm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    exact hgood.trans (partialCoverage_le_repaired_coverage hNx e m)

/-- Quantitative finite lower bound obtained by combining Chernoff averaging
with the deterministic repair. -/
lemma isCovering_of_exponential_capacity {x N k : ℕ} (hNx : N ≤ x)
    (hk : 0 < k) (hkx : k ≤ x) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hcap : (x : ℝ) * Real.exp ((harmonic N : ℝ) * t ^ 2 -
        t * ((harmonic N : ℝ) - (k - 1 : ℕ))) * k ≤ (x - N : ℕ)) :
    IsCovering x k := by
  obtain ⟨a, ha⟩ := exists_assignment_card_badPoints_le x N k hk ht₀ ht₁
  have hmul : ((badPoints x N k a).card : ℝ) * k ≤ (x - N : ℕ) := by
    calc
      ((badPoints x N k a).card : ℝ) * k ≤
          ((x : ℝ) * Real.exp ((harmonic N : ℝ) * t ^ 2 -
            t * ((harmonic N : ℝ) - (k - 1 : ℕ)))) * k := by
              gcongr
      _ ≤ (x - N : ℕ) := hcap
  have hmulNat : (badPoints x N k a).card * k ≤ x - N := by
    exact_mod_cast hmul
  obtain ⟨A, hA⟩ := exists_full_assignment_of_badPoints_mul_le hNx a hmulNat
  exact ⟨hkx, A, hA⟩

/-! ## The eventual lower bound -/

/-- The integer coverage target used for a fixed coefficient `c < 1`. -/
def lowerTarget (c : ℝ) (x : ℕ) : ℕ :=
  ⌊c * (harmonic (x / 2) : ℝ)⌋₊

lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_harmonic_atTop :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp tendsto_log_nat_atTop) b
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn)
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast hnpos
    · exact_mod_cast Nat.le_succ n
  exact (hN n hnN).trans (hlogmono.trans (log_add_one_le_harmonic n))

lemma tendsto_harmonic_half_atTop :
    Tendsto (fun x : ℕ ↦ (harmonic (x / 2) : ℝ)) atTop atTop :=
  tendsto_harmonic_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num : 2 ≠ 0))

/-- A logarithm times any fixed negative exponential tends to zero. -/
lemma tendsto_one_add_log_mul_exp_neg_nat {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℕ ↦ (1 + Real.log x) *
      Real.exp (-a * Real.log x)) atTop (𝓝 0) := by
  have h₀ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) a ha
  have h₁ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha
  have h := (h₀.add h₁).comp tendsto_log_nat_atTop
  have h' : Tendsto
      ((fun x : ℝ ↦ x ^ (0 : ℝ) * Real.exp (-a * x) +
        x ^ (1 : ℝ) * Real.exp (-a * x)) ∘ fun n : ℕ ↦ Real.log (n : ℝ))
      atTop (𝓝 0) := by simpa using h
  refine (tendsto_congr' ?_).mpr h'
  filter_upwards with x
  simp [Function.comp_apply, Real.rpow_zero, Real.rpow_one, add_mul]

/-- The explicit decaying expression which pays for the greedy repair. -/
def repairDecay (c : ℝ) (x : ℕ) : ℝ :=
  let t := (1 - c) / 2
  let A := t * (1 - c) - t ^ 2
  Real.exp (A * Real.log 2) * (1 + Real.log x) *
    Real.exp (-A * Real.log x)

lemma lowerTarget_exponential_capacity {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1)
    {x : ℕ} (hx : 2 ≤ x)
    (_hbase : 1 ≤ c * (harmonic (x / 2) : ℝ))
    (hsmall : repairDecay c x ≤ 1 / 2) :
    (x : ℝ) * Real.exp
        ((harmonic (x / 2) : ℝ) * ((1 - c) / 2) ^ 2 -
          ((1 - c) / 2) * ((harmonic (x / 2) : ℝ) -
            (lowerTarget c x - 1 : ℕ))) * lowerTarget c x ≤
      (x - x / 2 : ℕ) := by
  let N := x / 2
  let H : ℝ := harmonic N
  let k := lowerTarget c x
  let t := (1 - c) / 2
  let A := t * (1 - c) - t ^ 2
  have hH₀ : 0 ≤ H := by
    dsimp [H]
    exact (Real.log_natCast_nonneg (N + 1)).trans (log_add_one_le_harmonic N)
  have ht₀ : 0 ≤ t := by dsimp [t]; linarith
  have hA : 0 < A := by
    dsimp [A, t]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hc₁)]
  have hkR : (k : ℝ) ≤ c * H := by
    dsimp [k, lowerTarget, H, N]
    exact Nat.floor_le (mul_nonneg hc₀.le (by positivity))
  have hkpredR : ((k - 1 : ℕ) : ℝ) ≤ c * H := by
    exact (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hkR
  have harg : H * t ^ 2 - t * (H - (k - 1 : ℕ)) ≤ -A * H := by
    calc
      H * t ^ 2 - t * (H - (k - 1 : ℕ)) =
          H * t ^ 2 - t * H + t * (k - 1 : ℕ) := by ring
      _ ≤ H * t ^ 2 - t * H + t * (c * H) := by gcongr
      _ = -A * H := by dsimp [A]; ring
  have hlogH : Real.log (N + 1 : ℕ) ≤ H := by
    exact log_add_one_le_harmonic N
  have harglog : -A * H ≤ -A * Real.log (N + 1 : ℕ) := by
    simpa only [neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_left hlogH hA.le)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hNpos : 0 < N := by dsimp [N]; omega
  have hxdouble : x ≤ 2 * (N + 1) := by
    have hmod : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hdecomp := Nat.div_add_mod x 2
    dsimp [N]
    omega
  have hxhalf : (x : ℝ) / 2 ≤ (N + 1 : ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      (x : ℝ) ≤ (2 * (N + 1) : ℕ) := by exact_mod_cast hxdouble
      _ = ((N + 1 : ℕ) : ℝ) * 2 := by push_cast; ring
  have hloghalf : Real.log (x : ℝ) - Real.log 2 ≤ Real.log (N + 1 : ℕ) := by
    have hxRne : (x : ℝ) ≠ 0 := by exact_mod_cast hxpos.ne'
    rw [← Real.log_div hxRne (by norm_num : (2 : ℝ) ≠ 0)]
    apply Real.log_le_log
    · positivity
    · exact hxhalf
  have hq : Real.exp (H * t ^ 2 - t * (H - (k - 1 : ℕ))) ≤
      Real.exp (A * Real.log 2) * Real.exp (-A * Real.log x) := by
    calc
      Real.exp (H * t ^ 2 - t * (H - (k - 1 : ℕ))) ≤ Real.exp (-A * H) :=
        Real.exp_le_exp.mpr harg
      _ ≤ Real.exp (-A * Real.log (N + 1 : ℕ)) :=
        Real.exp_le_exp.mpr harglog
      _ ≤ Real.exp (-A * (Real.log x - Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using
          neg_le_neg (mul_le_mul_of_nonneg_left hloghalf hA.le)
      _ = Real.exp (A * Real.log 2) * Real.exp (-A * Real.log x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hNx : N ≤ x := by dsimp [N]; omega
  have hlogNx : Real.log (N : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hNpos
    · exact_mod_cast hNx
  have hklog : (k : ℝ) ≤ 1 + Real.log x := by
    calc
      (k : ℝ) ≤ c * H := hkR
      _ ≤ H := by nlinarith [mul_nonneg (sub_nonneg.mpr hc₁.le) hH₀]
      _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log x := by linarith
  have hxunused : (x : ℝ) / 2 ≤ (x - x / 2 : ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    have hnat : x ≤ 2 * (x - x / 2) := by omega
    calc
      (x : ℝ) ≤ (2 * (x - x / 2) : ℕ) := by exact_mod_cast hnat
      _ = ((x - x / 2 : ℕ) : ℝ) * 2 := by push_cast; ring
  change (x : ℝ) * Real.exp (H * t ^ 2 - t * (H - (k - 1 : ℕ))) * k ≤
    (x - x / 2 : ℕ)
  calc
    (x : ℝ) * Real.exp (H * t ^ 2 - t * (H - (k - 1 : ℕ))) * k ≤
        (x : ℝ) * (Real.exp (A * Real.log 2) * Real.exp (-A * Real.log x)) *
          (1 + Real.log x) := by gcongr
    _ = (x : ℝ) * repairDecay c x := by
      dsimp [repairDecay, A, t]
      ring
    _ ≤ (x : ℝ) * (1 / 2) := by gcongr
    _ = (x : ℝ) / 2 := by ring
    _ ≤ (x - x / 2 : ℕ) := hxunused

lemma lowerTarget_le_self {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1)
    {x : ℕ} (hx : 2 ≤ x) : lowerTarget c x ≤ x := by
  let N := x / 2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hx)
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNx : N ≤ x := by dsimp [N]; omega
  have hH₀ : 0 ≤ (harmonic N : ℝ) :=
    (Real.log_natCast_nonneg (N + 1)).trans (log_add_one_le_harmonic N)
  have hkR : (lowerTarget c x : ℝ) ≤ c * (harmonic N : ℝ) := by
    dsimp [lowerTarget, N]
    exact Nat.floor_le (mul_nonneg hc₀.le hH₀)
  have hlogNx : Real.log (N : ℝ) ≤ Real.log (x : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hNpos
    · exact_mod_cast hNx
  have hreal : (lowerTarget c x : ℝ) ≤ x := by
    calc
      (lowerTarget c x : ℝ) ≤ c * (harmonic N : ℝ) := hkR
      _ ≤ (harmonic N : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hc₁.le) hH₀]
      _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log x := by linarith
      _ ≤ x := by linarith [Real.log_le_sub_one_of_pos hxpos]
  exact_mod_cast hreal

lemma tendsto_repairDecay_zero {c : ℝ} (hc₁ : c < 1) :
    Tendsto (repairDecay c) atTop (𝓝 0) := by
  let t := (1 - c) / 2
  let A := t * (1 - c) - t ^ 2
  have hA : 0 < A := by
    dsimp [A, t]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hc₁)]
  have hconst : Tendsto (fun _x : ℕ ↦ Real.exp (A * Real.log 2)) atTop
      (𝓝 (Real.exp (A * Real.log 2))) := tendsto_const_nhds
  have h := hconst.mul (tendsto_one_add_log_mul_exp_neg_nat hA)
  have h' : Tendsto
      (fun x : ℕ ↦ Real.exp (A * Real.log 2) *
        ((1 + Real.log x) * Real.exp (-A * Real.log x))) atTop (𝓝 0) := by
    simpa using h
  refine (tendsto_congr' ?_).mpr h'
  filter_upwards with x
  dsimp [repairDecay, A, t]
  rw [mul_assoc]

/-- For each fixed `c < 1`, the finite Chernoff construction eventually
achieves `⌊c H_{⌊x/2⌋}⌋` simultaneous incidences. -/
lemma eventually_lowerTarget_le_coveringNumber {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    ∀ᶠ x : ℕ in atTop, lowerTarget c x ≤ coveringNumber x := by
  have hbase : ∀ᶠ x : ℕ in atTop,
      1 ≤ c * (harmonic (x / 2) : ℝ) :=
    (tendsto_harmonic_half_atTop.const_mul_atTop hc₀).eventually
      (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ x : ℕ in atTop, repairDecay c x ≤ 1 / 2 :=
    ((tendsto_order.mp (tendsto_repairDecay_zero hc₁)).2 (1 / 2) (by norm_num)).mono
      fun _ hx ↦ hx.le
  filter_upwards [eventually_ge_atTop 2, hbase, hsmall] with x hx hxbase hxsmall
  have hk : 0 < lowerTarget c x := by
    rw [lowerTarget, Nat.floor_pos]
    exact hxbase
  have hcov : IsCovering x (lowerTarget c x) := by
    apply isCovering_of_exponential_capacity (N := x / 2)
      (k := lowerTarget c x) (by omega) hk (lowerTarget_le_self hc₀ hc₁ hx)
      (t := (1 - c) / 2)
    · linarith
    · linarith
    · exact lowerTarget_exponential_capacity hc₀ hc₁ hx hxbase hxsmall
  exact le_coveringNumber hcov

/-! ## Asymptotic squeeze -/

lemma tendsto_one_div_log_nat :
    Tendsto (fun x : ℕ ↦ (1 : ℝ) / Real.log x) atTop (𝓝 0) :=
  Filter.Tendsto.const_div_atTop tendsto_log_nat_atTop 1

lemma tendsto_harmonic_div_log :
    Tendsto (fun x : ℕ ↦ (harmonic x : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hu : Tendsto (fun x : ℕ ↦ (1 + Real.log x) / Real.log x) atTop (𝓝 1) := by
    have hone : Tendsto (fun _x : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := tendsto_one_div_log_nat.add hone
    have h' : Tendsto (fun x : ℕ ↦ 1 / Real.log x + 1) atTop (𝓝 1) := by
      simpa using h
    refine (tendsto_congr' ?_).mpr h'
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : Real.log (x : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hx)).ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    apply (le_div_iff₀ hlog).2
    have hxRpos : (0 : ℝ) < x := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hx)
    have hxs : (x : ℝ) ≤ (x + 1 : ℕ) := by exact_mod_cast Nat.le_succ x
    simpa using (Real.log_le_log hxRpos hxs).trans (log_add_one_le_harmonic x)
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    apply (div_le_div_iff_of_pos_right hlog).2
    exact harmonic_le_one_add_log x

lemma tendsto_harmonic_half_div_log :
    Tendsto (fun x : ℕ ↦ (harmonic (x / 2) : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hlo : Tendsto
      (fun x : ℕ ↦ 1 - Real.log 2 / Real.log x) atTop (𝓝 1) := by
    have hzero := Filter.Tendsto.const_div_atTop tendsto_log_nat_atTop (Real.log 2)
    simpa using (tendsto_const_nhds.sub hzero)
  have hu : Tendsto (fun x : ℕ ↦ (1 + Real.log x) / Real.log x) atTop (𝓝 1) := by
    have hone : Tendsto (fun _x : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := tendsto_one_div_log_nat.add hone
    have h' : Tendsto (fun x : ℕ ↦ 1 / Real.log x + 1) atTop (𝓝 1) := by
      simpa using h
    refine (tendsto_congr' ?_).mpr h'
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : Real.log (x : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hx)).ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hu ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with x hx
    let N := x / 2
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have hxdouble : x ≤ 2 * (N + 1) := by
      have hmod : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hdecomp := Nat.div_add_mod x 2
      dsimp [N]
      omega
    have hxhalf : (x : ℝ) / 2 ≤ (N + 1 : ℕ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      calc
        (x : ℝ) ≤ (2 * (N + 1) : ℕ) := by exact_mod_cast hxdouble
        _ = ((N + 1 : ℕ) : ℝ) * 2 := by push_cast; ring
    have hloghalf : Real.log (x : ℝ) - Real.log 2 ≤ Real.log (N + 1 : ℕ) := by
      have hxRne : (x : ℝ) ≠ 0 := by exact_mod_cast hxpos.ne'
      rw [← Real.log_div hxRne (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.log_le_log (by positivity) hxhalf
    have hnum : Real.log x - Real.log 2 ≤ (harmonic N : ℝ) :=
      hloghalf.trans (log_add_one_le_harmonic N)
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    rw [show 1 - Real.log 2 / Real.log x =
      (Real.log x - Real.log 2) / Real.log x by field_simp]
    exact (div_le_div_iff_of_pos_right hlog).2 hnum
  · filter_upwards [eventually_ge_atTop 2] with x hx
    let N := x / 2
    have hNpos : 0 < N := by dsimp [N]; omega
    have hNx : N ≤ x := by dsimp [N]; omega
    have hlogNx : Real.log (N : ℝ) ≤ Real.log (x : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hNx)
    have hnum : (harmonic N : ℝ) ≤ 1 + Real.log x :=
      (harmonic_le_one_add_log N).trans (by linarith)
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    exact (div_le_div_iff_of_pos_right hlog).2 hnum

lemma tendsto_lowerTarget_div_log {c : ℝ} (hc₀ : 0 ≤ c) :
    Tendsto (fun x : ℕ ↦ (lowerTarget c x : ℝ) / Real.log x) atTop (𝓝 c) := by
  have hmain : Tendsto
      (fun x : ℕ ↦ c * ((harmonic (x / 2) : ℝ) / Real.log x)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds.mul tendsto_harmonic_half_div_log)
  have hlo : Tendsto
      (fun x : ℕ ↦ c * ((harmonic (x / 2) : ℝ) / Real.log x) -
        1 / Real.log x) atTop (𝓝 c) := by
    simpa using (hmain.sub tendsto_one_div_log_nat)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hmain ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    have hfloor : c * (harmonic (x / 2) : ℝ) < (lowerTarget c x : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    apply (le_div_iff₀ hlog).2
    have := hfloor.le
    field_simp [hlog.ne']
    nlinarith
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hlog).2
    exact Nat.floor_le (mul_nonneg hc₀ (by
      exact (Real.log_natCast_nonneg (x / 2 + 1)).trans
        (log_add_one_le_harmonic (x / 2))))

lemma tendsto_harmonic_add_one_div_log :
    Tendsto (fun x : ℕ ↦ ((harmonic x : ℝ) + 1) / Real.log x) atTop (𝓝 1) := by
  have h := tendsto_harmonic_div_log.add tendsto_one_div_log_nat
  have h' : Tendsto
      (fun x : ℕ ↦ (harmonic x : ℝ) / Real.log x + 1 / Real.log x)
      atTop (𝓝 1) := by simpa using h
  refine (tendsto_congr' ?_).mpr h'
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlog : Real.log (x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hx)).ne'
  field_simp

/-- Quotient form of Erdős Problem 1205: the optimal common coverage divided
by `log x` tends to one. -/
theorem tendsto_coveringNumber_div_log :
    Tendsto (fun x : ℕ ↦ (coveringNumber x : ℝ) / Real.log x) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    let c : ℝ := (max a 0 + 1) / 2
    have hmax₀ : 0 ≤ max a 0 := le_max_right _ _
    have hmax₁ : max a 0 < 1 := max_lt ha zero_lt_one
    have hc₀ : 0 < c := by dsimp [c]; linarith
    have hc₁ : c < 1 := by dsimp [c]; linarith
    have hac : a < c := by
      have hamax : a ≤ max a 0 := le_max_left _ _
      dsimp [c]
      linarith
    have htarget_lt : ∀ᶠ x : ℕ in atTop,
        a < (lowerTarget c x : ℝ) / Real.log x :=
      (tendsto_order.mp (tendsto_lowerTarget_div_log hc₀.le)).1 a hac
    filter_upwards [eventually_ge_atTop 2,
      eventually_lowerTarget_le_coveringNumber hc₀ hc₁, htarget_lt] with x hx htarget hlt
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    exact hlt.trans_le ((div_le_div_iff_of_pos_right hlog).2 (by exact_mod_cast htarget))
  · intro b hb
    have hu : ∀ᶠ x : ℕ in atTop,
        ((harmonic x : ℝ) + 1) / Real.log x < b :=
      (tendsto_order.mp tendsto_harmonic_add_one_div_log).2 b hb
    filter_upwards [eventually_ge_atTop 2, hu] with x hx hxb
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    exact ((div_le_div_iff_of_pos_right hlog).2
      (coveringNumber_le_harmonic_add_one x)).trans_lt hxb

/-- **Resolution of Erdős Problem 1205.**  The maximal common coverage is
asymptotic to `log x`. -/
theorem erdos_1205 :
    (fun x : ℕ ↦ (coveringNumber x : ℝ)) ~[atTop]
      (fun x : ℕ ↦ Real.log x) := by
  have hz : ∀ᶠ x : ℕ in atTop, Real.log x ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact (Real.log_pos (by exact_mod_cast hx)).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hz]
  exact tendsto_coveringNumber_div_log

#print axioms erdos_1205

end

end Erdos1205
