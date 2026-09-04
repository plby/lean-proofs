/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.Basic
import ErdosProblems.Erdos438.Energy
import ErdosProblems.Erdos438.LOSModular
import ErdosProblems.Erdos438.Shifting
import ErdosProblems.Erdos438.SquareProgressions

/-!
# The Khalfalah--Lodha--Szemeredi upper bound for Erdos Problem 438

This file assembles the finite residue-density energy increment, the
Lagarias--Odlyzko--Shearer modular bound, the square-progression count, and
the KLS shifting estimate.  Its public result is the exact eventual upper
bound required to squeeze the extremal density to `11 / 32`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos438

noncomputable section

/-- The least multiple of `q` which is at least `N`.  The KLS argument pads
the ambient interval once to this endpoint, after all moduli have been
chosen. -/
def paddedEndpoint (q N : ℕ) : ℕ := q * (N ⌈/⌉ q)

theorem dvd_paddedEndpoint (q N : ℕ) : q ∣ paddedEndpoint q N := by
  exact dvd_mul_right q (N ⌈/⌉ q)

theorem le_paddedEndpoint {q N : ℕ} (hq : 0 < q) :
    N ≤ paddedEndpoint q N := by
  simpa [paddedEndpoint, nsmul_eq_mul] using
    (le_smul_ceilDiv (a := q) (b := N) hq)

/-- Padding adds fewer than one complete block. -/
theorem paddedEndpoint_lt_add {q N : ℕ} (hq : 0 < q) :
    paddedEndpoint q N < N + q := by
  rw [paddedEndpoint, Nat.ceilDiv_eq_add_pred_div]
  have hmul : q * ((N + q - 1) / q) ≤ N + q - 1 :=
    Nat.mul_div_le (N + q - 1) q
  have hone : N + q - 1 < N + q := by omega
  exact hmul.trans_lt hone

/-- A square-sum-free set remains admissible after padding its endpoint. -/
theorem admissible_padded {q N : ℕ} (hq : 0 < q) {A : Finset ℕ}
    (hA : admissible N A) : admissible (paddedEndpoint q N) A := by
  refine ⟨?_, hA.2⟩
  intro x hx
  have hx' := Finset.mem_Icc.mp (hA.1 hx)
  exact Finset.mem_Icc.mpr ⟨hx'.1, hx'.2.trans (le_paddedEndpoint hq)⟩

/-- The eventual epsilon-form of the KLS upper estimate. -/
def EventuallyUpper : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
      (A.card : ℝ) / (N : ℝ) ≤ (11 : ℝ) / 32 + ε

/-- Converting a linear cardinality estimate to the normalized form. -/
theorem card_div_le_of_card_le_mul {N : ℕ} {A : Finset ℕ} {c : ℝ}
    (hN : 0 < N) (h : (A.card : ℝ) ≤ c * (N : ℝ)) :
    (A.card : ℝ) / (N : ℝ) ≤ c := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr hN)]
  simpa [mul_comm] using h

/-- It is enough to prove a linear estimate eventually. -/
theorem eventuallyUpper_of_eventually_card_le_mul
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, admissible N A →
        (A.card : ℝ) ≤ ((11 : ℝ) / 32 + ε) * (N : ℝ)) :
    EventuallyUpper := by
  intro ε hε
  filter_upwards [h ε hε, eventually_gt_atTop (0 : ℕ)] with N hbound hN
  intro A hA
  exact card_div_le_of_card_le_mul hN (hbound A hA)

/-! ## Quantitative parameter tower -/

/-- Number of energy levels used for an internal reciprocal margin `1 / k`.
The deliberately generous constant leaves room for every strict inequality
in the bad-parent argument. -/
def klsLevelCount (k : ℕ) : ℕ := 8193 * k ^ 3

/-- Denominator threshold at one stage of the KLS tower. -/
def klsThreshold (K k q : ℕ) : ℕ :=
  (8193 * (K + 1) * (k + 1) ^ 2 * q ^ 2) ^ 2 + 1

theorem klsThreshold_sqrt_lower {K k q : ℕ} {C : ℝ}
    (hC : C ≤ K + 1) (hq : 0 < q) :
    320 * C * (k : ℝ) ^ 2 * (q : ℝ) ^ 2 <
      Real.sqrt (klsThreshold K k q : ℝ) := by
  let S : ℕ := 8193 * (K + 1) * (k + 1) ^ 2 * q ^ 2
  have hSpos : (0 : ℝ) < S := by
    dsimp [S]
    positivity
  have hSsqrt : (S : ℝ) < Real.sqrt (klsThreshold K k q : ℝ) := by
    rw [Real.lt_sqrt hSpos.le]
    dsimp only [klsThreshold, S]
    push_cast
    nlinarith
  have hfactor : (0 : ℝ) < (K + 1) * (k + 1) ^ 2 * q ^ 2 := by positivity
  calc
    320 * C * (k : ℝ) ^ 2 * (q : ℝ) ^ 2 ≤
        320 * ((K : ℝ) + 1) * (k : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
      gcongr
    _ ≤ 320 * ((K : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 * (q : ℝ) ^ 2 := by
      gcongr
      nlinarith
    _ < 8193 * ((K : ℝ) + 1) * ((k : ℝ) + 1) ^ 2 * (q : ℝ) ^ 2 := by
      have hconst : (320 : ℝ) < 8193 := by norm_num
      have := mul_lt_mul_of_pos_right hconst hfactor
      simpa only [mul_assoc] using this
    _ = (S : ℝ) := by
      dsimp [S]
      push_cast
      ring
    _ < Real.sqrt (klsThreshold K k q : ℝ) := hSsqrt

/-- The nested moduli.  At a successor stage every denominator at most the
chosen threshold divides the refinement factor. -/
def klsModulus (K k : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => shiftModulus (klsModulus K k i) (klsThreshold K k (klsModulus K k i))

@[simp] theorem klsModulus_zero (K k : ℕ) : klsModulus K k 0 = 1 := rfl

@[simp] theorem klsModulus_succ (K k i : ℕ) :
    klsModulus K k (i + 1) =
      shiftModulus (klsModulus K k i) (klsThreshold K k (klsModulus K k i)) := rfl

theorem klsModulus_pos (K k i : ℕ) : 0 < klsModulus K k i := by
  induction i with
  | zero => simp
  | succ i ih => simpa using shiftModulus_pos ih

theorem klsModulus_dvd_succ (K k i : ℕ) :
    klsModulus K k i ∣ klsModulus K k (i + 1) := by
  simp only [klsModulus_succ, shiftModulus]
  exact dvd_mul_right _ _

theorem klsModulus_dvd_add (K k i d : ℕ) :
    klsModulus K k i ∣ klsModulus K k (i + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      exact ih.trans (by simpa [Nat.add_assoc] using klsModulus_dvd_succ K k (i + d))

theorem klsModulus_dvd_of_le (K k : ℕ) {i j : ℕ} (hij : i ≤ j) :
    klsModulus K k i ∣ klsModulus K k j := by
  have hij' : i + (j - i) = j := Nat.add_sub_of_le hij
  simpa [hij'] using klsModulus_dvd_add K k i (j - i)

/-- The elementary telescoping pigeonhole used to select a level of small
energy increment.  This form keeps the proof independent of the particular
residue-density representation. -/
theorem exists_small_increment (L : ℕ) (hL : 0 < L) (e : ℕ → ℝ)
    (hspan : e L - e 0 ≤ (1 : ℝ) / 4) :
    ∃ i < L, e (i + 1) - e i ≤ (1 : ℝ) / (4 * L) := by
  have hconst :
      (∑ i ∈ Finset.range L, (1 : ℝ) / (4 * L)) = (1 : ℝ) / 4 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hL.ne']
  have hsum :
      (∑ i ∈ Finset.range L, (e (i + 1) - e i)) ≤
        ∑ i ∈ Finset.range L, (1 : ℝ) / (4 * L) := by
    rw [Finset.sum_range_sub, hconst]
    exact hspan
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hL⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

/-! ## Residue-density profiles -/

/-- The part of `A` in a residue class modulo `q`. -/
def residueSlice (A : Finset ℕ) (q : ℕ) (j : Fin q) : Finset ℕ :=
  A.filter fun n ↦ n ≡ j.val [MOD q]

@[simp] theorem mem_residueSlice {A : Finset ℕ} {q : ℕ} {j : Fin q} {n : ℕ} :
    n ∈ residueSlice A q j ↔ n ∈ A ∧ n ≡ j.val [MOD q] := by
  simp [residueSlice]

/-- The residue classes partition `A`. -/
theorem sum_card_residueSlice {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    ∑ j : Fin q, (residueSlice A q j).card = A.card := by
  have hslice : ∀ j : Fin q,
      residueSlice A q j =
        A.filter (fun n ↦ Energy.residueIndex q hq n = j) := by
    intro j
    apply Finset.ext
    intro n
    simp [residueSlice, Energy.residueIndex, Nat.ModEq, Fin.ext_iff,
      Nat.mod_eq_of_lt j.isLt]
  simpa [hslice, Energy.residueClassCard] using
    Energy.sum_residueClassCard A q hq

/-- Normalized density of one residue class. -/
def residueDensity (A : Finset ℕ) (N q : ℕ) (j : Fin q) : ℝ :=
  (q : ℝ) * (residueSlice A q j).card / (N : ℝ)

/-- The mean of the residue-density profile is the density of `A`. -/
theorem mean_residueDensity {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (A : Finset ℕ) :
    Energy.mean (residueDensity A N q) = (A.card : ℝ) / (N : ℝ) := by
  have hsum : (∑ j : Fin q, ((residueSlice A q j).card : ℝ)) = A.card := by
    exact_mod_cast sum_card_residueSlice hq A
  unfold Energy.mean residueDensity
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  field_simp [hN.ne', hq.ne']

/-- A residue slice in a padded interval has the expected capacity. -/
theorem residueSlice_card_le_div {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hdiv : q ∣ N) {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (j : Fin q) :
    (residueSlice A q j).card ≤ N / q := by
  have hsubset : residueSlice A q j ⊆ residueClassIco q 1 (N / q) j := by
    intro n hn
    have hnA := (mem_residueSlice.mp hn).1
    have hnIcc := Finset.mem_Icc.mp (hA hnA)
    have hNdiv : N / q * q = N := Nat.div_mul_cancel hdiv
    simp only [residueClassIco, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨hnIcc.1, ?_⟩, (mem_residueSlice.mp hn).2⟩
    omega
  calc
    (residueSlice A q j).card ≤ (residueClassIco q 1 (N / q) j).card :=
      Finset.card_le_card hsubset
    _ = N / q := card_residueClassIco hq j

/-- After one-time padding, every residue density lies in `[0,1]`. -/
theorem residueDensity_isDensity {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hdiv : q ∣ N) {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    Energy.IsDensity (residueDensity A N q) := by
  intro j
  constructor
  · unfold residueDensity
    positivity
  · have hcard := residueSlice_card_le_div hN hq hdiv hA j
    have hqN : q ≤ N := Nat.le_of_dvd hN hdiv
    have hdivpos : 0 < N / q := Nat.div_pos hqN hq
    have hcancel : q * (N / q) = N := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
    unfold residueDensity
    rw [div_le_one (Nat.cast_pos.mpr hN)]
    exact_mod_cast (Nat.mul_le_mul_left q hcard |>.trans_eq hcancel)

/-- Decomposition of a residue modulo a product into a coarse residue and a
lift index. -/
theorem mod_mul_decompose {n q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    n % (q * r) = n % q + q * ((n / q) % r) := by
  have hdecomp : n % q + q * (n / q) = n := Nat.mod_add_div n q
  calc
    n % (q * r) = (n % q + q * (n / q)) % (q * r) := by rw [hdecomp]
    _ = ((n % q) % (q * r) + (q * (n / q)) % (q * r)) % (q * r) := by
      rw [Nat.add_mod]
    _ = (n % q + q * ((n / q) % r)) % (q * r) := by
      have hlt : n % q < q * r := by
        have hmod := Nat.mod_lt n hq
        nlinarith
      rw [Nat.mod_eq_of_lt hlt, Nat.mul_mod_mul_left]
    _ = n % q + q * ((n / q) % r) := by
      rw [Nat.mod_eq_of_lt]
      have h₁ := Nat.mod_lt n hq
      have h₂ := Nat.mod_lt (n / q) hr
      nlinarith

/-- A residue modulo `q*r` is equivalently a coarse residue and its lift
index. -/
theorem modEq_refinedResidue_iff {n q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (j : Fin q) (k : Fin r) :
    n ≡ j.val + q * k.val [MOD q * r] ↔
      n ≡ j.val [MOD q] ∧ n / q ≡ k.val [MOD r] := by
  simp only [Nat.ModEq, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt]
  have hrefined : j.val + q * k.val < q * r := by
    nlinarith [j.isLt, k.isLt]
  rw [Nat.mod_eq_of_lt hrefined, mod_mul_decompose hq hr]
  constructor
  · intro h
    have hcoarse : n % q = j.val := by
      have hm := congrArg (fun x : ℕ ↦ x % q) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt] using hm
    refine ⟨hcoarse, ?_⟩
    rw [hcoarse] at h
    have hmul : q * ((n / q) % r) = q * k.val := Nat.add_left_cancel h
    exact Nat.mul_left_cancel hq hmul
  · rintro ⟨hj, hk⟩
    rw [hj, hk]

/-- A child of a residue class, indexed without choosing representatives
modulo the product. -/
def refinedSlice (A : Finset ℕ) (q r : ℕ) (j : Fin q) (k : Fin r) : Finset ℕ :=
  (residueSlice A q j).filter fun n ↦ n / q ≡ k.val [MOD r]

@[simp] theorem mem_refinedSlice {A : Finset ℕ} {q r : ℕ}
    {j : Fin q} {k : Fin r} {n : ℕ} :
    n ∈ refinedSlice A q r j k ↔
      n ∈ A ∧ n ≡ j.val [MOD q] ∧ n / q ≡ k.val [MOD r] := by
  rw [refinedSlice, Finset.mem_filter, mem_residueSlice]
  tauto

/-- Children partition their parent class. -/
theorem sum_card_refinedSlice {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (A : Finset ℕ) (j : Fin q) :
    ∑ k : Fin r, (refinedSlice A q r j k).card = (residueSlice A q j).card := by
  let f : ℕ → Fin r := fun n ↦ ⟨(n / q) % r, Nat.mod_lt _ hr⟩
  have hmap : ((residueSlice A q j : Finset ℕ) : Set ℕ).MapsTo f
      (Finset.univ : Finset (Fin r)) := by
    intro n hn
    exact Finset.mem_univ _
  have h := Finset.card_eq_sum_card_fiberwise hmap
  calc
    ∑ k : Fin r, (refinedSlice A q r j k).card =
        ∑ k : Fin r,
          ((residueSlice A q j).filter (fun n ↦ f n = k)).card := by
      congr 1
      funext k
      congr 1
      apply Finset.ext
      intro n
      simp [refinedSlice, f, Nat.ModEq, Fin.ext_iff,
        Nat.mod_eq_of_lt k.isLt]
    _ = (residueSlice A q j).card := h.symm

/-- Normalized child density. -/
def refinedDensity (A : Finset ℕ) (N q r : ℕ) (j : Fin q) (k : Fin r) : ℝ :=
  ((q * r : ℕ) : ℝ) * (refinedSlice A q r j k).card / (N : ℝ)

/-- The residue-density profile is the mean of its child profiles. -/
theorem residueDensity_refines {N q r : ℕ} (hN : 0 < N)
    (hq : 0 < q) (hr : 0 < r) (A : Finset ℕ) :
    Energy.Refines (residueDensity A N q) (refinedDensity A N q r) := by
  intro j
  have hsum : (∑ k : Fin r, ((refinedSlice A q r j k).card : ℝ)) =
      (residueSlice A q j).card := by
    exact_mod_cast sum_card_refinedSlice hq hr A j
  unfold Energy.mean residueDensity refinedDensity
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  field_simp [hN.ne', hq.ne', hr.ne']
  push_cast
  ring

/-- A child slice is the corresponding ordinary class modulo `q*r`. -/
theorem refinedSlice_eq_residueSlice {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (A : Finset ℕ) (j : Fin q) (k : Fin r) :
    refinedSlice A q r j k =
      residueSlice A (q * r) (liftResidueEquiv q r (k, j)) := by
  ext n
  rw [mem_refinedSlice, mem_residueSlice, liftResidueEquiv_val]
  constructor
  · rintro ⟨hn, hj, hk⟩
    exact ⟨hn, (modEq_refinedResidue_iff hq hr j k).2 ⟨hj, hk⟩⟩
  · rintro ⟨hn, hmod⟩
    exact ⟨hn, (modEq_refinedResidue_iff hq hr j k).1 hmod⟩

theorem refinedDensity_eq_residueDensity {N q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (A : Finset ℕ) (j : Fin q) (k : Fin r) :
    refinedDensity A N q r j k =
      residueDensity A N (q * r) (liftResidueEquiv q r (k, j)) := by
  simp [refinedDensity, residueDensity, refinedSlice_eq_residueSlice hq hr]

/-- Reindexing all children identifies their second moment with the energy
of the ordinary profile modulo the product. -/
theorem refinedEnergy_eq_energy_product {N q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (A : Finset ℕ) :
    Energy.refinedEnergy (refinedDensity A N q r) =
      Energy.energy (residueDensity A N (q * r)) := by
  let e : Fin q × Fin r ≃ Fin (q * r) :=
    (Equiv.prodComm (Fin q) (Fin r)).trans (liftResidueEquiv q r)
  have hsum :
      (∑ j : Fin q, ∑ k : Fin r, (refinedDensity A N q r j k) ^ 2) =
        ∑ z : Fin (q * r), (residueDensity A N (q * r) z) ^ 2 := by
    rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv e
    intro x
    rcases x with ⟨j, k⟩
    change (refinedDensity A N q r j k) ^ 2 =
      (residueDensity A N (q * r) (e (j, k))) ^ 2
    rw [refinedDensity_eq_residueDensity hq hr]
    rfl
  unfold Energy.refinedEnergy Energy.energy Energy.mean
  rw [← Finset.sum_div, hsum]
  field_simp [hq.ne', hr.ne']
  push_cast
  ring

/-! ## Good parents and dense children -/

/-- Children whose density differs from their parent by at least `δ/4`. -/
def deviatingChildren {q r : ℕ} (coarse : Fin q → ℝ)
    (fine : Fin q → Fin r → ℝ) (δ : ℝ) (j : Fin q) : Finset (Fin r) :=
  Finset.univ.filter fun u ↦ δ / 4 ≤ |fine j u - coarse j|

@[simp] theorem mem_deviatingChildren {q r : ℕ} {coarse : Fin q → ℝ}
    {fine : Fin q → Fin r → ℝ} {δ : ℝ} {j : Fin q} {u : Fin r} :
    u ∈ deviatingChildren coarse fine δ j ↔
      δ / 4 ≤ |fine j u - coarse j| := by
  simp [deviatingChildren]

/-- Parents with at least one eighth deviating children. -/
def badParents {q r : ℕ} (coarse : Fin q → ℝ)
    (fine : Fin q → Fin r → ℝ) (δ : ℝ) : Finset (Fin q) :=
  Finset.univ.filter fun j ↦
    (r : ℝ) / 8 ≤ ((deviatingChildren coarse fine δ j).card : ℝ)

@[simp] theorem mem_badParents {q r : ℕ} {coarse : Fin q → ℝ}
    {fine : Fin q → Fin r → ℝ} {δ : ℝ} {j : Fin q} :
    j ∈ badParents coarse fine δ ↔
      (r : ℝ) / 8 ≤ ((deviatingChildren coarse fine δ j).card : ℝ) := by
  simp [badParents]

/-- Refined classes with density at least `δ/4`. -/
def denseChildren {q r : ℕ} (fine : Fin q → Fin r → ℝ)
    (δ : ℝ) (j : Fin q) : Finset (Fin r) :=
  Finset.univ.filter fun u ↦ δ / 4 ≤ fine j u

@[simp] theorem mem_denseChildren {q r : ℕ} {fine : Fin q → Fin r → ℝ}
    {δ : ℝ} {j : Fin q} {u : Fin r} :
    u ∈ denseChildren fine δ j ↔ δ / 4 ≤ fine j u := by
  simp [denseChildren]

theorem parentVariance_ge_of_mem_badParents {q r : ℕ} (hr : 0 < r)
    {coarse : Fin q → ℝ} {fine : Fin q → Fin r → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) {j : Fin q}
    (hj : j ∈ badParents coarse fine δ) :
    δ ^ 2 / 128 ≤ Energy.parentVariance coarse fine j := by
  apply Energy.parentVariance_ge_of_many_deviations hr hδ
    (deviatingChildren coarse fine δ j)
  · exact mem_badParents.mp hj
  · intro u hu
    exact mem_deviatingChildren.mp hu

/-- A good parent of density at least `δ/2` has at least seven eighths
dense children. -/
theorem seven_eighths_denseChildren {q r : ℕ} (hr : 0 < r)
    {coarse : Fin q → ℝ} {fine : Fin q → Fin r → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) {j : Fin q}
    (hjgood : j ∉ badParents coarse fine δ)
    (hjdense : δ / 2 ≤ coarse j) :
    7 * r ≤ 8 * (denseChildren fine δ j).card := by
  let E := deviatingChildren coarse fine δ j
  let G := denseChildren fine δ j
  have hE : ((E.card : ℕ) : ℝ) < (r : ℝ) / 8 := by
    have := not_le.mp (fun h ↦ hjgood (mem_badParents.mpr h))
    simpa [E] using this
  have hcomp : (Finset.univ \ G).card ≤ E.card := by
    apply Finset.card_le_card
    intro u hu
    have hu' := Finset.mem_sdiff.mp hu
    have hufine : fine j u < δ / 4 := by
      exact lt_of_not_ge (fun h ↦ hu'.2 (by simpa [G] using h))
    have hdev : δ / 4 ≤ |fine j u - coarse j| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    simpa [E] using hdev
  have hEnat : 8 * E.card < r := by
    exact_mod_cast (show (8 : ℝ) * E.card < r by nlinarith)
  have hGle : G.card ≤ r := by
    simpa [G] using Finset.card_le_card (Finset.subset_univ G)
  have hcompcard : (Finset.univ \ G).card = r - G.card := by
    simp [Finset.card_sdiff]
  rw [hcompcard] at hcomp
  simpa [G] using (show 7 * r ≤ 8 * G.card by omega)

/-! ## Root multiplicities force many short shifted square pairs -/

def childIndex (q r : ℕ) (hr : 0 < r) (n : ℕ) : Fin r :=
  ⟨(n / q) % r, Nat.mod_lt _ hr⟩

def selectedSlice (A : Finset ℕ) (q r : ℕ) (hr : 0 < r)
    (a : Fin q) (G : Finset (Fin r)) : Finset ℕ :=
  (residueSlice A q a).filter fun n ↦ childIndex q r hr n ∈ G

theorem sum_selectedSlice_eq_sum_refinedSlice
    {M : Type*} [AddCommMonoid M] (A : Finset ℕ) (q : ℕ)
    {r : ℕ} (hr : 0 < r) (a : Fin q) (G : Finset (Fin r)) (f : ℕ → M) :
    ∑ x ∈ selectedSlice A q r hr a G, f x =
      ∑ u ∈ G, ∑ x ∈ refinedSlice A q r a u, f x := by
  let S := selectedSlice A q r hr a G
  let idx := childIndex q r hr
  have houter :
      (∑ u ∈ G, ∑ x ∈ S.filter fun x ↦ idx x = u, f x) =
        ∑ u : Fin r, ∑ x ∈ S.filter fun x ↦ idx x = u, f x := by
    apply Finset.sum_subset (Finset.subset_univ G)
    intro u hu hnot
    have hempty : S.filter (fun x ↦ idx x = u) = ∅ := by
      ext x
      simp only [S, selectedSlice, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, hxG⟩, hxu⟩
        exact (hnot (hxu ▸ hxG)).elim
      · intro hx
        simpa using hx
    simp [hempty]
  calc
    ∑ x ∈ selectedSlice A q r hr a G, f x =
        ∑ u : Fin r, ∑ x ∈ S.filter fun x ↦ idx x = u, f x := by
      symm
      exact Finset.sum_fiberwise S idx f
    _ = ∑ u ∈ G, ∑ x ∈ S.filter fun x ↦ idx x = u, f x := houter.symm
    _ = ∑ u ∈ G, ∑ x ∈ refinedSlice A q r a u, f x := by
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      ext x
      simp only [S, selectedSlice, refinedSlice, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx, hxG⟩, hxu⟩
        refine ⟨hx, ?_⟩
        have := congrArg Fin.val hxu
        simpa [idx, childIndex, Nat.ModEq, Nat.mod_eq_of_lt u.isLt] using this
      · rintro ⟨hx, hxu⟩
        have hxu' : childIndex q r hr x = u := by
          apply Fin.ext
          simpa [childIndex, Nat.ModEq, Nat.mod_eq_of_lt u.isLt] using hxu
        exact ⟨⟨hx, hxu'.symm ▸ hu⟩, hxu'⟩

theorem totalShiftedSquarePairCount_eq_sum_pair_indices
    (A : Finset ℕ) (Q J : ℕ) :
    totalShiftedSquarePairCount A Q J =
      ∑ p ∈ A.product A, (shiftedSquareIndices p.1 p.2 Q J).card := by
  calc
    totalShiftedSquarePairCount A Q J =
        ∑ j ∈ Finset.range (J + 1), ∑ p ∈ A.product A,
          if IsSquare (p.1 + p.2 + j * Q) then 1 else 0 := by
      unfold totalShiftedSquarePairCount shiftedSquarePairCount
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.card_filter]
    _ = ∑ p ∈ A.product A, ∑ j ∈ Finset.range (J + 1),
          if IsSquare (p.1 + p.2 + j * Q) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ A.product A, (shiftedSquareIndices p.1 p.2 Q J).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [shiftedSquareIndices, Finset.card_filter]

def carryIndex (q r : ℕ) (hr : 0 < r) (a b : ℕ) : Fin r :=
  ⟨residueCarry q a b % r, Nat.mod_lt _ hr⟩

def sumIndex (r : ℕ) (hr : 0 < r) (k u v : Fin r) : Fin r :=
  ⟨(u.val + v.val + k.val) % r, Nat.mod_lt _ hr⟩

theorem sumIndex_cyclicPartner {r : ℕ} (hr : 0 < r)
    (k w u : Fin r) :
    sumIndex r hr k u (cyclicPartner hr k w u) = w := by
  let : NeZero r := ⟨hr.ne'⟩
  have hsum (v : Fin r) : sumIndex r hr k u v = u + v + k := by
    apply Fin.ext
    simp [sumIndex, Fin.add_def, Nat.add_mod,
      Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt v.isLt,
      Nat.mod_eq_of_lt k.isLt]
  rw [hsum, cyclicPartner]
  abel

theorem liftedRootMultiplicity_le_pair_shiftCount
    {A : Finset ℕ} {N q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q) (hc : c = (a.val + b.val) % q)
    (u v : Fin r) {x y : ℕ}
    (hx : x ∈ refinedSlice A q r a u) (hy : y ∈ refinedSlice A q r b v) :
    liftedRootMultiplicity q r c hq hr
        (sumIndex r hr (carryIndex q r hr a.val b.val) u v) ≤
      (shiftedSquareIndices x y (q * r) (squareShiftCutoff N (q * r))).card := by
  have hx' := mem_refinedSlice.mp hx
  have hy' := mem_refinedSlice.mp hy
  have hxN := (Finset.mem_Icc.mp (hA hx'.1)).2
  have hyN := (Finset.mem_Icc.mp (hA hy'.1)).2
  have hxmod : x % q = a.val := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt] using hx'.2.1
  have hymod : y % q = b.val := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt b.isLt] using hy'.2.1
  have hxchild : (x / q) % r = u.val := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt u.isLt] using hx'.2.2
  have hychild : (y / q) % r = v.val := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt v.isLt] using hy'.2.2
  have hxyres : (x + y) % (q * r) =
      c + q * (sumIndex r hr (carryIndex q r hr a.val b.val) u v).val := by
    rw [Nat.add_mod, mod_mul_decompose (n := x) hq hr,
      mod_mul_decompose (n := y) hq hr,
      hxmod, hymod, hxchild, hychild]
    rw [refinedResidue_add_mod hq hr]
    subst c
    congr 2
    dsimp only [sumIndex, carryIndex]
    rw [Nat.add_mod (u.val + v.val) (residueCarry q a.val b.val) r,
      Nat.add_mod (u.val + v.val) (residueCarry q a.val b.val % r) r,
      Nat.mod_mod]
  have hclt : c < q := hc.trans_lt (Nat.mod_lt _ hq)
  rw [liftedRootMultiplicity_eq_rootMultiplicity hq hr hclt]
  have hsmall : c + q * (sumIndex r hr
      (carryIndex q r hr a.val b.val) u v).val < q * r := by
    nlinarith [(sumIndex r hr (carryIndex q r hr a.val b.val) u v).isLt]
  exact rootMultiplicity_le_card_shiftedSquareIndices_cutoff
    (Nat.mul_pos hq hr) hxN hyN (by simpa [Nat.mod_eq_of_lt hsmall] using hxyres)

theorem sum_selectedPair_shiftCount_le_total
    {A : Finset ℕ} {q r : ℕ} (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (J : ℕ) :
    (∑ p ∈ (selectedSlice A q r hr a G₁).product
        (selectedSlice A q r hr b G₂),
      (shiftedSquareIndices p.1 p.2 (q * r) J).card) ≤
      totalShiftedSquarePairCount A (q * r) J := by
  rw [totalShiftedSquarePairCount_eq_sum_pair_indices]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_product.mp hp
    apply Finset.mem_product.mpr
    exact ⟨(Finset.mem_filter.mp hp'.1).1 |> Finset.mem_filter.mp |>.1,
      (Finset.mem_filter.mp hp'.2).1 |> Finset.mem_filter.mp |>.1⟩
  · intros
    exact Nat.zero_le _

theorem sum_selectedPair_eq_sum_refined
    {M : Type*} [AddCommMonoid M] (A : Finset ℕ) (q : ℕ)
    {r : ℕ} (hr : 0 < r) (a b : Fin q) (G₁ G₂ : Finset (Fin r))
    (F : ℕ → ℕ → M) :
    ∑ p ∈ (selectedSlice A q r hr a G₁).product
        (selectedSlice A q r hr b G₂), F p.1 p.2 =
      ∑ u ∈ G₁, ∑ x ∈ refinedSlice A q r a u,
        ∑ v ∈ G₂, ∑ y ∈ refinedSlice A q r b v, F x y := by
  let S₁ := selectedSlice A q r hr a G₁
  let S₂ := selectedSlice A q r hr b G₂
  have hprod :
      (∑ p ∈ S₁.product S₂, F p.1 p.2) =
        ∑ x ∈ S₁, ∑ y ∈ S₂, F x y := by
    exact Finset.sum_product S₁ S₂ (fun p ↦ F p.1 p.2)
  change (∑ p ∈ S₁.product S₂, F p.1 p.2) = _
  rw [hprod]
  dsimp only [S₁, S₂]
  rw [sum_selectedSlice_eq_sum_refinedSlice A q hr a G₁
    (fun x ↦ ∑ y ∈ selectedSlice A q r hr b G₂, F x y)]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_selectedSlice_eq_sum_refinedSlice A q hr b G₂ (F x)

theorem sum_liftedRoot_le_total
    {A : Finset ℕ} {N q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q) (hc : c = (a.val + b.val) % q)
    (G₁ G₂ : Finset (Fin r)) :
    (∑ u ∈ G₁, ∑ x ∈ refinedSlice A q r a u,
      ∑ v ∈ G₂, ∑ y ∈ refinedSlice A q r b v,
        liftedRootMultiplicity q r c hq hr
          (sumIndex r hr (carryIndex q r hr a.val b.val) u v)) ≤
      totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r)) := by
  let J := squareShiftCutoff N (q * r)
  calc
    (∑ u ∈ G₁, ∑ x ∈ refinedSlice A q r a u,
      ∑ v ∈ G₂, ∑ y ∈ refinedSlice A q r b v,
        liftedRootMultiplicity q r c hq hr
          (sumIndex r hr (carryIndex q r hr a.val b.val) u v)) ≤
        ∑ u ∈ G₁, ∑ x ∈ refinedSlice A q r a u,
          ∑ v ∈ G₂, ∑ y ∈ refinedSlice A q r b v,
            (shiftedSquareIndices x y (q * r) J).card := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro y hy
      exact liftedRootMultiplicity_le_pair_shiftCount hq hr hA a b hc u v hx hy
    _ = ∑ p ∈ (selectedSlice A q r hr a G₁).product
          (selectedSlice A q r hr b G₂),
          (shiftedSquareIndices p.1 p.2 (q * r) J).card := by
      symm
      exact sum_selectedPair_eq_sum_refined A q hr a b G₁ G₂
        (fun x y ↦ (shiftedSquareIndices x y (q * r) J).card)
    _ ≤ totalShiftedSquarePairCount A (q * r) J :=
      sum_selectedPair_shiftCount_le_total hr a b G₁ G₂ J

def pairRootCount
    (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℕ :=
  ∑ u ∈ G₁, ∑ v ∈ G₂,
    liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v)

theorem cyclicPartner_sumIndex {r : ℕ} (hr : 0 < r)
    (κ u v : Fin r) : cyclicPartner hr κ (sumIndex r hr κ u v) u = v := by
  let : NeZero r := ⟨hr.ne'⟩
  have h : u + v + κ = sumIndex r hr κ u v := by
    apply Fin.ext
    simp [sumIndex, Fin.add_def, Nat.add_comm, Nat.add_left_comm]
  have h' : cyclicPartner hr κ (u + v + κ) u = v := by
    simp only [cyclicPartner]
    abel
  rw [← h]
  exact h'

def pairFiber {r : ℕ} (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ w : Fin r) : Finset (Fin r × Fin r) :=
  (G₁.product G₂).filter fun p ↦ sumIndex r hr κ p.1 p.2 = w

theorem card_pairFiber {r : ℕ} (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ w : Fin r) :
    (pairFiber hr G₁ G₂ κ w).card =
      (compatibleIndices hr G₁ G₂ κ w).card := by
  symm
  apply Finset.card_bij (fun u _ ↦ (u, cyclicPartner hr κ w u))
  · intro u hu
    rw [pairFiber, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ?_, sumIndex_cyclicPartner hr κ w u⟩
    exact Finset.mem_filter.mp hu
  · intro u₁ hu₁ u₂ hu₂ h
    exact congrArg Prod.fst h
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    refine ⟨p.1, ?_, ?_⟩
    · rw [compatibleIndices, Finset.mem_filter]
      refine ⟨(Finset.mem_product.mp hp'.1).1, ?_⟩
      have hcyc : cyclicPartner hr κ w p.1 = p.2 :=
        (congrArg (fun z ↦ cyclicPartner hr κ z p.1) hp'.2).symm.trans
          (cyclicPartner_sumIndex hr κ p.1 p.2)
      rw [hcyc]
      exact (Finset.mem_product.mp hp'.1).2
    · apply Prod.ext
      · rfl
      · exact (congrArg (fun z ↦ cyclicPartner hr κ z p.1) hp'.2).symm.trans
          (cyclicPartner_sumIndex hr κ p.1 p.2)

theorem pairRootCount_eq_weightedCompatibleRootCount
    {q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) :
    pairRootCount q r c hq hr G₁ G₂ κ =
      weightedCompatibleRootCount q r c hq hr G₁ G₂ κ := by
  calc
    pairRootCount q r c hq hr G₁ G₂ κ =
        ∑ p ∈ G₁.product G₂,
          liftedRootMultiplicity q r c hq hr (sumIndex r hr κ p.1 p.2) := by
      rw [pairRootCount]
      symm
      exact Finset.sum_product G₁ G₂
        (fun p ↦ liftedRootMultiplicity q r c hq hr
          (sumIndex r hr κ p.1 p.2))
    _ = ∑ w : Fin r, ∑ p ∈ pairFiber hr G₁ G₂ κ w,
          liftedRootMultiplicity q r c hq hr (sumIndex r hr κ p.1 p.2) := by
      symm
      exact Finset.sum_fiberwise (G₁.product G₂)
        (fun p ↦ sumIndex r hr κ p.1 p.2)
        (fun p ↦ liftedRootMultiplicity q r c hq hr
          (sumIndex r hr κ p.1 p.2))
    _ = ∑ w : Fin r,
          (pairFiber hr G₁ G₂ κ w).card * liftedRootMultiplicity q r c hq hr w := by
      apply Finset.sum_congr rfl
      intro w hw
      calc
        (∑ p ∈ pairFiber hr G₁ G₂ κ w,
            liftedRootMultiplicity q r c hq hr (sumIndex r hr κ p.1 p.2)) =
            ∑ _p ∈ pairFiber hr G₁ G₂ κ w,
              liftedRootMultiplicity q r c hq hr w := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = (pairFiber hr G₁ G₂ κ w).card *
              liftedRootMultiplicity q r c hq hr w := by simp
    _ = weightedCompatibleRootCount q r c hq hr G₁ G₂ κ := by
      rw [weightedCompatibleRootCount]
      apply Finset.sum_congr rfl
      intro w hw
      rw [card_pairFiber]

def classWeightedRootCount
    (A : Finset ℕ) (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℕ :=
  ∑ u ∈ G₁, ∑ v ∈ G₂,
    (refinedSlice A q r a u).card * (refinedSlice A q r b v).card *
      liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v)

theorem sum_liftedRoot_eq_classWeightedRootCount
    {A : Finset ℕ} {q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (κ : Fin r) :
    (∑ u ∈ G₁, ∑ x ∈ refinedSlice A q r a u,
      ∑ v ∈ G₂, ∑ y ∈ refinedSlice A q r b v,
        liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v)) =
      classWeightedRootCount A q r c hq hr a b G₁ G₂ κ := by
  rw [classWeightedRootCount]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_const, nsmul_eq_mul]
  ac_rfl

theorem classWeightedRootCount_le_total
    {A : Finset ℕ} {N q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q) (hc : c = (a.val + b.val) % q)
    (G₁ G₂ : Finset (Fin r)) :
    classWeightedRootCount A q r c hq hr a b G₁ G₂
        (carryIndex q r hr a.val b.val) ≤
      totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r)) := by
  rw [← sum_liftedRoot_eq_classWeightedRootCount hq hr a b G₁ G₂]
  exact sum_liftedRoot_le_total hq hr hA a b hc G₁ G₂

theorem mul_sq_pairRootCount_le_classWeightedRootCount
    {A : Finset ℕ} {q r c M : ℕ} (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (κ : Fin r)
    (hG₁ : ∀ u ∈ G₁, M ≤ (refinedSlice A q r a u).card)
    (hG₂ : ∀ v ∈ G₂, M ≤ (refinedSlice A q r b v).card) :
    M * M * pairRootCount q r c hq hr G₁ G₂ κ ≤
      classWeightedRootCount A q r c hq hr a b G₁ G₂ κ := by
  rw [pairRootCount, classWeightedRootCount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (hG₁ u hu) (hG₂ v hv))

theorem global_dense_pair_lower
    {A : Finset ℕ} {N q r c M : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q)
    (hc : c = (a.val + b.val) % q) (hsq : IsSquare (c : ZMod q))
    (G₁ G₂ : Finset (Fin r))
    (hcard₁ : 7 * r ≤ 8 * G₁.card) (hcard₂ : 7 * r ≤ 8 * G₂.card)
    (hG₁ : ∀ u ∈ G₁, M ≤ (refinedSlice A q r a u).card)
    (hG₂ : ∀ v ∈ G₂, M ≤ (refinedSlice A q r b v).card) :
    3 * r * r * M * M ≤
      4 * totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r)) := by
  let κ := carryIndex q r hr a.val b.val
  let W := weightedCompatibleRootCount q r c hq hr G₁ G₂ κ
  let T := totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r))
  have hroot : 1 ≤ rootMultiplicity q c :=
    rootMultiplicity_pos_of_isSquare_zmod hq hsq
  have hweighted : (3 * r) * (r * rootMultiplicity q c) ≤ 4 * W :=
    three_mul_mul_le_four_mul_weightedCompatibleRootCount
      hq hr G₁ G₂ κ hcard₁ hcard₂
  have hW : 3 * r * r ≤ 4 * W := by
    calc
      3 * r * r ≤ (3 * r) * (r * rootMultiplicity q c) := by
        apply Nat.mul_le_mul_left (3 * r)
        simpa using Nat.mul_le_mul_left r hroot
      _ ≤ 4 * W := hweighted
  have hMW : M * M * W ≤ T := by
    calc
      M * M * W = M * M * pairRootCount q r c hq hr G₁ G₂ κ := by
        rw [pairRootCount_eq_weightedCompatibleRootCount]
      _ ≤ classWeightedRootCount A q r c hq hr a b G₁ G₂ κ :=
        mul_sq_pairRootCount_le_classWeightedRootCount hq hr a b G₁ G₂ κ hG₁ hG₂
      _ ≤ T := classWeightedRootCount_le_total hq hr hA a b hc G₁ G₂
  calc
    3 * r * r * M * M = (3 * r * r) * (M * M) := by ring
    _ ≤ (4 * W) * (M * M) := Nat.mul_le_mul_right (M * M) hW
    _ = 4 * (M * M * W) := by ring
    _ ≤ 4 * T := Nat.mul_le_mul_left 4 hMW

theorem denseChild_card_bound
    {A : Finset ℕ} {N q r : ℕ} (hN : 0 < N) {a : Fin q} {δ : ℝ}
    {u : Fin r} (hu : u ∈ denseChildren (refinedDensity A N q r) δ a) :
    δ * (N : ℝ) ≤
      4 * ((q * r : ℕ) : ℝ) * ((refinedSlice A q r a u).card : ℝ) := by
  have hu' : δ / 4 ≤ refinedDensity A N q r a u := mem_denseChildren.mp hu
  unfold refinedDensity at hu'
  have hu'' : (δ / 4) * (N : ℝ) ≤
      ((q * r : ℕ) : ℝ) * ((refinedSlice A q r a u).card : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hN)).mp hu'
  nlinarith

def realPairRootCount
    (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℝ :=
  ∑ u ∈ G₁, ∑ v ∈ G₂,
    (liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v) : ℝ)

def realClassWeightedRootCount
    (A : Finset ℕ) (q r c : ℕ) (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (κ : Fin r) : ℝ :=
  ∑ u ∈ G₁, ∑ v ∈ G₂,
    ((refinedSlice A q r a u).card : ℝ) * ((refinedSlice A q r b v).card : ℝ) *
      (liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v) : ℝ)

theorem realPairRootCount_eq_cast
    {q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (G₁ G₂ : Finset (Fin r)) (κ : Fin r) :
    realPairRootCount q r c hq hr G₁ G₂ κ =
      (pairRootCount q r c hq hr G₁ G₂ κ : ℝ) := by
  unfold realPairRootCount pairRootCount
  push_cast
  rfl

theorem realClassWeightedRootCount_eq_cast
    {A : Finset ℕ} {q r c : ℕ} (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (G₁ G₂ : Finset (Fin r)) (κ : Fin r) :
    realClassWeightedRootCount A q r c hq hr a b G₁ G₂ κ =
      (classWeightedRootCount A q r c hq hr a b G₁ G₂ κ : ℝ) := by
  unfold realClassWeightedRootCount classWeightedRootCount
  push_cast
  rfl

theorem dense_pairRootCount_le_classWeighted
    {A : Finset ℕ} {N q r c : ℕ} (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (a b : Fin q) (δ : ℝ) (hδ : 0 ≤ δ) :
    let G₁ := denseChildren (refinedDensity A N q r) δ a
    let G₂ := denseChildren (refinedDensity A N q r) δ b
    (δ * (N : ℝ)) ^ 2 *
        realPairRootCount q r c hq hr G₁ G₂
          (carryIndex q r hr a.val b.val) ≤
      16 * ((q * r : ℕ) : ℝ) ^ 2 *
        realClassWeightedRootCount A q r c hq hr a b G₁ G₂
          (carryIndex q r hr a.val b.val) := by
  dsimp only
  let G₁ := denseChildren (refinedDensity A N q r) δ a
  let G₂ := denseChildren (refinedDensity A N q r) δ b
  let κ := carryIndex q r hr a.val b.val
  have hD : 0 ≤ δ * (N : ℝ) := mul_nonneg hδ (by positivity)
  calc
    (δ * (N : ℝ)) ^ 2 * realPairRootCount q r c hq hr G₁ G₂ κ =
        ∑ u ∈ G₁, ∑ v ∈ G₂,
          (δ * (N : ℝ)) ^ 2 *
            (liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v) : ℝ) := by
      unfold realPairRootCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
    _ ≤ ∑ u ∈ G₁, ∑ v ∈ G₂,
          16 * ((q * r : ℕ) : ℝ) ^ 2 *
            (((refinedSlice A q r a u).card : ℝ) *
              ((refinedSlice A q r b v).card : ℝ) *
              (liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v) : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hu' := denseChild_card_bound hN (u := u) (a := a) (A := A)
        (q := q) (r := r) (N := N) (by simpa [G₁] using hu)
      have hv' := denseChild_card_bound hN (u := v) (a := b) (A := A)
        (q := q) (r := r) (N := N) (by simpa [G₂] using hv)
      have hprod := mul_le_mul hu' hv' hD (by positivity :
        0 ≤ 4 * ((q * r : ℕ) : ℝ) * ((refinedSlice A q r a u).card : ℝ))
      have hroot : 0 ≤
          (liftedRootMultiplicity q r c hq hr (sumIndex r hr κ u v) : ℝ) := by
        positivity
      have := mul_le_mul_of_nonneg_right hprod hroot
      nlinarith
    _ = 16 * ((q * r : ℕ) : ℝ) ^ 2 *
        realClassWeightedRootCount A q r c hq hr a b G₁ G₂ κ := by
      unfold realClassWeightedRootCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]

theorem global_dense_pair_lower_real
    {A : Finset ℕ} {N q r c : ℕ} (hN : 0 < N) (hq : 0 < q) (hr : 0 < r)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q)
    (hc : c = (a.val + b.val) % q) (hsq : IsSquare (c : ZMod q))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hcard₁ : 7 * r ≤
      8 * (denseChildren (refinedDensity A N q r) δ a).card)
    (hcard₂ : 7 * r ≤
      8 * (denseChildren (refinedDensity A N q r) δ b).card) :
    3 * (δ * (N : ℝ)) ^ 2 ≤
      64 * (q : ℝ) ^ 2 *
        (totalShiftedSquarePairCount A (q * r)
          (squareShiftCutoff N (q * r)) : ℝ) := by
  let G₁ := denseChildren (refinedDensity A N q r) δ a
  let G₂ := denseChildren (refinedDensity A N q r) δ b
  let κ := carryIndex q r hr a.val b.val
  let RP := realPairRootCount q r c hq hr G₁ G₂ κ
  let RC := realClassWeightedRootCount A q r c hq hr a b G₁ G₂ κ
  let T := (totalShiftedSquarePairCount A (q * r)
    (squareShiftCutoff N (q * r)) : ℝ)
  have hroot : 1 ≤ rootMultiplicity q c :=
    rootMultiplicity_pos_of_isSquare_zmod hq hsq
  have hweighted := three_mul_mul_le_four_mul_weightedCompatibleRootCount
    (c := c) hq hr G₁ G₂ κ hcard₁ hcard₂
  have hpairNat : 3 * r * r ≤ 4 * pairRootCount q r c hq hr G₁ G₂ κ := by
    calc
      3 * r * r ≤ (3 * r) * (r * rootMultiplicity q c) := by
        apply Nat.mul_le_mul_left (3 * r)
        simpa using Nat.mul_le_mul_left r hroot
      _ ≤ 4 * weightedCompatibleRootCount q r c hq hr G₁ G₂ κ := hweighted
      _ = 4 * pairRootCount q r c hq hr G₁ G₂ κ := by
        rw [pairRootCount_eq_weightedCompatibleRootCount]
  have hpair : 3 * (r : ℝ) ^ 2 ≤ 4 * RP := by
    have hcast : ((3 * r * r : ℕ) : ℝ) ≤
        ((4 * pairRootCount q r c hq hr G₁ G₂ κ : ℕ) : ℝ) := by
      exact_mod_cast hpairNat
    change 3 * (r : ℝ) ^ 2 ≤
      4 * realPairRootCount q r c hq hr G₁ G₂ κ
    rw [realPairRootCount_eq_cast]
    push_cast at hcast
    nlinarith
  have hclass : (δ * (N : ℝ)) ^ 2 * RP ≤
      16 * ((q * r : ℕ) : ℝ) ^ 2 * RC := by
    exact dense_pairRootCount_le_classWeighted hN hq hr a b δ hδ
  have hRC : RC ≤ T := by
    change realClassWeightedRootCount A q r c hq hr a b G₁ G₂ κ ≤
      (totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r)) : ℝ)
    rw [realClassWeightedRootCount_eq_cast]
    exact_mod_cast classWeightedRootCount_le_total hq hr hA a b hc G₁ G₂
  have hDsq : 0 ≤ (δ * (N : ℝ)) ^ 2 := sq_nonneg _
  have hlarge : 3 * (r : ℝ) ^ 2 * (δ * (N : ℝ)) ^ 2 ≤
      64 * ((q * r : ℕ) : ℝ) ^ 2 * T := by
    calc
      3 * (r : ℝ) ^ 2 * (δ * (N : ℝ)) ^ 2 =
          (δ * (N : ℝ)) ^ 2 * (3 * (r : ℝ) ^ 2) := by ring
      _ ≤ (δ * (N : ℝ)) ^ 2 * (4 * RP) :=
        mul_le_mul_of_nonneg_left hpair hDsq
      _ = 4 * ((δ * (N : ℝ)) ^ 2 * RP) := by ring
      _ ≤ 4 * (16 * ((q * r : ℕ) : ℝ) ^ 2 * RC) :=
        mul_le_mul_of_nonneg_left hclass (by norm_num)
      _ ≤ 4 * (16 * ((q * r : ℕ) : ℝ) ^ 2 * T) := by gcongr
      _ = 64 * ((q * r : ℕ) : ℝ) ^ 2 * T := by ring
  have hr2 : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hr)
  apply le_of_mul_le_mul_left (a := (r : ℝ) ^ 2) _ hr2
  calc
    (r : ℝ) ^ 2 * (3 * (δ * (N : ℝ)) ^ 2) =
        3 * (r : ℝ) ^ 2 * (δ * (N : ℝ)) ^ 2 := by ring
    _ ≤ 64 * ((q * r : ℕ) : ℝ) ^ 2 * T := hlarge
    _ = (r : ℝ) ^ 2 *
        (64 * (q : ℝ) ^ 2 *
          (totalShiftedSquarePairCount A (q * r)
            (squareShiftCutoff N (q * r)) : ℝ)) := by
      dsimp only [T]
      push_cast
      ring

theorem denseChild_div_bound
    {A : Finset ℕ} {N q r k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {a : Fin q} {u : Fin r}
    (hu : u ∈ denseChildren (refinedDensity A N q r) ((1 : ℝ) / k) a) :
    N / (8 * k * (q * r)) ≤ (refinedSlice A q r a u).card := by
  have hreal := denseChild_card_bound hN hu
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmul := mul_le_mul_of_nonneg_left hreal hkR.le
  have hreal' : (N : ℝ) ≤
      (4 * k * (q * r) * (refinedSlice A q r a u).card : ℕ) := by
    calc
      (N : ℝ) = (k : ℝ) * (((1 : ℝ) / k) * (N : ℝ)) := by
        field_simp
      _ ≤ (k : ℝ) *
          (4 * ((q * r : ℕ) : ℝ) * ((refinedSlice A q r a u).card : ℝ)) := hmul
      _ = (4 * k * (q * r) * (refinedSlice A q r a u).card : ℕ) := by
        push_cast
        ring
  have hnat : N ≤ 4 * k * (q * r) * (refinedSlice A q r a u).card := by
    exact_mod_cast hreal'
  apply Nat.div_le_of_le_mul
  calc
    N ≤ 4 * k * (q * r) * (refinedSlice A q r a u).card := hnat
    _ ≤ 8 * k * (q * r) * (refinedSlice A q r a u).card := by
      gcongr
      norm_num
    _ = (8 * k * (q * r)) * (refinedSlice A q r a u).card := by ring

/-- Quantitative lower bound produced by a modular square pair and two good
parents.  All rounding is absorbed by the harmless hypothesis that one
prospective child block fits in the interval. -/
theorem residueProfile_totalShifted_lower
    {A : Finset ℕ} {N q r c k : ℕ}
    (hN : 0 < N) (hq : 0 < q) (hr : 0 < r) (hk : 0 < k)
    (hlarge : 8 * k * (q * r) ≤ N)
    (hA : A ⊆ Finset.Icc 1 N) (a b : Fin q)
    (hc : c = (a.val + b.val) % q) (hsq : IsSquare (c : ZMod q))
    (G₁ G₂ : Finset (Fin r))
    (hcard₁ : 7 * r ≤ 8 * G₁.card) (hcard₂ : 7 * r ≤ 8 * G₂.card)
    (hG₁ : ∀ u ∈ G₁,
      u ∈ denseChildren (refinedDensity A N q r) ((1 : ℝ) / k) a)
    (hG₂ : ∀ v ∈ G₂,
      v ∈ denseChildren (refinedDensity A N q r) ((1 : ℝ) / k) b) :
    (3 : ℝ) * (N : ℝ) ^ 2 ≤
      1024 * (k : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        (totalShiftedSquarePairCount A (q * r)
          (squareShiftCutoff N (q * r)) : ℝ) := by
  let d := 8 * k * (q * r)
  let M := N / d
  let T := totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r))
  have hd : 0 < d := by dsimp [d]; positivity
  have hMpos : 0 < M := Nat.div_pos hlarge hd
  have hNlt : N < d * (M + 1) := by
    simpa [M] using Nat.lt_mul_div_succ N hd
  have hNle : N ≤ 2 * d * M := by
    have hMone : M + 1 ≤ 2 * M := by omega
    calc
      N ≤ d * (M + 1) := hNlt.le
      _ ≤ d * (2 * M) := Nat.mul_le_mul_left d hMone
      _ = 2 * d * M := by ring
  have hlower : 3 * r * r * M * M ≤ 4 * T := by
    apply global_dense_pair_lower hq hr hA a b hc hsq G₁ G₂ hcard₁ hcard₂
    · intro u hu
      exact denseChild_div_bound hN hk (hG₁ u hu)
    · intro v hv
      exact denseChild_div_bound hN hk (hG₂ v hv)
  have hnat : 3 * N * N ≤ 1024 * k ^ 2 * q ^ 2 * T := by
    calc
      3 * N * N ≤ 3 * (2 * d * M) * (2 * d * M) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 hNle) hNle
      _ = 256 * k ^ 2 * q ^ 2 * (3 * r * r * M * M) := by
        dsimp [d]
        ring
      _ ≤ 256 * k ^ 2 * q ^ 2 * (4 * T) :=
        Nat.mul_le_mul_left (256 * k ^ 2 * q ^ 2) hlower
      _ = 1024 * k ^ 2 * q ^ 2 * T := by ring
  dsimp only [T] at hnat
  simp only [pow_two] at hnat ⊢
  have hnat' : 3 * (N * N) ≤
      1024 * (k * k) * (q * q) *
        totalShiftedSquarePairCount A (q * r) (squareShiftCutoff N (q * r)) := by
    simpa only [mul_assoc] using hnat
  exact_mod_cast hnat'

/-! ## The LOS extraction step -/

/-- The sharp modular theorem converts a support of density greater than
`11/32` into a pair whose sum is a square.  This adapter is stated with the
LOS theorem as an argument so the finite combinatorial assembly remains
separately reusable. -/
theorem exists_square_pair_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m)
    {q : ℕ} (hq : 0 < q) (D : Finset (Fin q))
    (hD : (11 : ℝ) / 32 < (D.card : ℝ) / q) :
    ∃ a ∈ D, ∃ b ∈ D,
      IsSquare ((a.val : ZMod q) + (b.val : ZMod q)) := by
  let : NeZero q := ⟨hq.ne'⟩
  let f : Fin q → ZMod q := fun a ↦ (a.val : ZMod q)
  let B : Finset (ZMod q) := D.image f
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg ZMod.val hab
    simpa [f, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt,
      Nat.mod_eq_of_lt b.isLt] using hval
  have hcard : B.card = D.card := by
    dsimp only [B]
    rw [Finset.card_image_iff.mpr hf.injOn]
  by_contra hnone
  push_neg at hnone
  have hB : ∀ x ∈ B, ∀ y ∈ B, ¬ IsSquare (x + y) := by
    intro x hx y hy hsq
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    exact hnone a ha b hb hsq
  have hupper := hLOS q hq (B := B) hB
  rw [hcard] at hupper
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlowerR : (11 : ℝ) * q < 32 * D.card := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 32) hqR] at hD
    nlinarith
  have hlower : 11 * q < 32 * D.card := by exact_mod_cast hlowerR
  omega

/-! ## A short shifting range -/

/-- A shift range of order `sqrt N`.  One complete period of every root
class already suffices for the KLS contradiction, so the longer range in the
published presentation is unnecessary. -/
def shortShiftCutoff (Q N : ℕ) : ℕ :=
  4 * Nat.sqrt (2 * N) + 2 * Q + 4

/-- Starting immediately above `sqrt (x+y)`, one complete block of `Q`
root residues squares into the allowed short shifting window. -/
theorem one_period_square_window {Q N x y : ℕ} (hQ : 0 < Q)
    (hx : x ≤ N) (hy : y ≤ N) :
    let a := Nat.sqrt (x + y) + 1
    x + y < a * a ∧
      (a + Q) * (a + Q) ≤ x + y + shortShiftCutoff Q N * Q := by
  dsimp only
  constructor
  · simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (x + y)
  · have hxy : x + y ≤ 2 * N := by omega
    have hs := Nat.sqrt_le_sqrt hxy
    have hrt := Nat.sqrt_le (x + y)
    have hprod : 0 ≤ (Q - 1) * Nat.sqrt (2 * N) := Nat.zero_le _
    have hQsq : 0 ≤ (Q - 1) ^ 2 := Nat.zero_le _
    dsimp [shortShiftCutoff]
    nlinarith

theorem eventually_squareShiftCutoff_add_one_le (Q : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (squareShiftCutoff N Q + 1 : ℕ) ≤
        (15 : ℝ) * Real.sqrt (N : ℝ) := by
  filter_upwards [eventually_ge_atTop (max (Q ^ 2) 1)] with N hN
  have hQsq : Q * Q ≤ N := by
    have := (le_max_left (Q ^ 2) 1).trans hN
    simpa [pow_two] using this
  have hN1 : 1 ≤ N := (le_max_right (Q ^ 2) 1).trans hN
  have hQsqrtNat : Q ≤ Nat.sqrt N := Nat.le_sqrt.mpr hQsq
  have honeSqrtNat : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by simpa using hN1)
  have hsqrtNat : (Nat.sqrt (2 * N) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    calc
      (Nat.sqrt (2 * N) : ℝ) ≤ Real.sqrt ((2 * N : ℕ) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt (2 : ℝ) * Real.sqrt (N : ℝ) := by
        push_cast
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Real.sqrt (N : ℝ) := by
        gcongr
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg (2 : ℝ)]
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc
      (Q : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hQsqrtNat
      _ ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have honeSqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    calc
      (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast honeSqrtNat
      _ ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
  norm_num [squareShiftCutoff]
  nlinarith

/-! ## Energy along the modulus tower -/

def klsEnergy (K k : ℕ) (A : Finset ℕ) (N i : ℕ) : ℝ :=
  Energy.energy (residueDensity A N (klsModulus K k i))

theorem klsEnergy_step (K k : ℕ) (A : Finset ℕ) {N i : ℕ}
    (hN : 0 < N) :
    klsEnergy K k A N (i + 1) - klsEnergy K k A N i =
      Energy.mean (fun j ↦ Energy.parentVariance
        (residueDensity A N (klsModulus K k i))
        (refinedDensity A N (klsModulus K k i)
          (Nat.lcmUpto (klsThreshold K k (klsModulus K k i)))) j) := by
  let q := klsModulus K k i
  let r := Nat.lcmUpto (klsThreshold K k q)
  have hq : 0 < q := klsModulus_pos K k i
  have hr : 0 < r := Nat.lcmUpto_pos _
  have href : Energy.Refines (residueDensity A N q) (refinedDensity A N q r) :=
    residueDensity_refines hN hq hr A
  have hvar := Energy.refinedEnergy_sub_energy_eq_mean_variance hq hr href
  have hprod := refinedEnergy_eq_energy_product hq hr A (N := N)
  change Energy.energy (residueDensity A N (q * r)) -
      Energy.energy (residueDensity A N q) = _
  rw [← hprod, hvar]

theorem klsEnergy_mono_step (K k : ℕ) (A : Finset ℕ) {N i : ℕ}
    (hN : 0 < N) : klsEnergy K k A N i ≤ klsEnergy K k A N (i + 1) := by
  rw [← sub_nonneg, klsEnergy_step K k A hN]
  exact Energy.mean_nonneg (klsModulus_pos K k i) fun j ↦
    Energy.parentVariance_nonneg (Nat.lcmUpto_pos _)
      (residueDensity A N (klsModulus K k i))
      (refinedDensity A N (klsModulus K k i)
        (Nat.lcmUpto (klsThreshold K k (klsModulus K k i)))) j

/-- Every tower profile is a genuine density after padding by the final
modulus. -/
theorem klsResidueDensity_isDensity (K k L : ℕ) {N : ℕ} (hN : 0 < N)
    (hfinal : klsModulus K k L ∣ N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) {i : ℕ} (hi : i ≤ L) :
    Energy.IsDensity (residueDensity A N (klsModulus K k i)) := by
  have hqi : 0 < klsModulus K k i := klsModulus_pos K k i
  have hdiv : klsModulus K k i ∣ N :=
    (klsModulus_dvd_of_le K k hi).trans hfinal
  exact residueDensity_isDensity hN hqi hdiv hA

theorem exists_kls_small_increment
    (K k : ℕ) (hk : 0 < k) {N : ℕ} (hN : 0 < N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hfinal : klsModulus K k (klsLevelCount k) ∣ N) :
    ∃ i < klsLevelCount k,
      klsEnergy K k A N (i + 1) - klsEnergy K k A N i ≤
        (1 : ℝ) / (4 * klsLevelCount k) := by
  let L := klsLevelCount k
  let x₀ := residueDensity A N (klsModulus K k 0)
  let xL := residueDensity A N (klsModulus K k L)
  have hL : 0 < L := by dsimp [L, klsLevelCount]; positivity
  have hx₀ : Energy.IsDensity x₀ := by
    exact klsResidueDensity_isDensity K k L hN hfinal hA (i := 0) (by omega)
  have hxL : Energy.IsDensity xL := by
    exact klsResidueDensity_isDensity K k L hN hfinal hA (i := L) le_rfl
  let ρ := (A.card : ℝ) / (N : ℝ)
  have hmean₀ : Energy.mean x₀ = ρ := by
    exact mean_residueDensity hN (klsModulus_pos K k 0) A
  have hmeanL : Energy.mean xL = ρ := by
    exact mean_residueDensity hN (klsModulus_pos K k L) A
  have hρnonneg : 0 ≤ ρ := by
    rw [← hmean₀]
    exact Energy.mean_nonneg (klsModulus_pos K k 0) fun j ↦ (hx₀ j).1
  have hρle : ρ ≤ 1 := by
    rw [← hmean₀]
    calc
      Energy.mean x₀ ≤ Energy.mean (fun _ : Fin (klsModulus K k 0) ↦ (1 : ℝ)) :=
        Energy.mean_le_mean (klsModulus_pos K k 0) fun j ↦ (hx₀ j).2
      _ = 1 := Energy.mean_const (klsModulus_pos K k 0) 1
  have hspan : klsEnergy K k A N L - klsEnergy K k A N 0 ≤ (1 : ℝ) / 4 := by
    have hupper := (Energy.energy_bounds (klsModulus_pos K k L) hxL).2
    have hlower := (Energy.energy_bounds (klsModulus_pos K k 0) hx₀).1
    change Energy.energy xL - Energy.energy x₀ ≤ (1 : ℝ) / 4
    rw [hmeanL] at hupper
    rw [hmean₀] at hlower
    nlinarith [sq_nonneg (ρ - (1 : ℝ) / 2)]
  simpa only [L] using exists_small_increment L hL (klsEnergy K k A N) hspan

theorem kls_small_increment_lt {k : ℕ} (hk : 0 < k) :
    (1 : ℝ) / (4 * klsLevelCount k) <
      ((1 : ℝ) / k) ^ 3 / 8192 := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  dsimp only [klsLevelCount]
  push_cast
  rw [div_pow]
  field_simp
  nlinarith

/-- The complete finite KLS extraction: at one level of the tower, the
energy increment is small; LOS supplies two dense good parents; root
multiplicity then gives the quantitative shifted-pair lower bound. -/
theorem exists_level_totalShifted_lower_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m)
    (K k : ℕ) (hk : 0 < k) {N : ℕ} (hN : 0 < N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hfinal : klsModulus K k (klsLevelCount k) ∣ N)
    (hmass : (11 : ℝ) / 32 + (1 : ℝ) / k ≤
      (A.card : ℝ) / (N : ℝ)) :
    ∃ i < klsLevelCount k,
      let q := klsModulus K k i
      let r := Nat.lcmUpto (klsThreshold K k q)
      3 * (((1 : ℝ) / k) * (N : ℝ)) ^ 2 ≤
        64 * (q : ℝ) ^ 2 *
          (totalShiftedSquarePairCount A (q * r)
            (squareShiftCutoff N (q * r)) : ℝ) := by
  obtain ⟨i, hi, hinc⟩ := exists_kls_small_increment K k hk hN hA hfinal
  let q := klsModulus K k i
  let r := Nat.lcmUpto (klsThreshold K k q)
  let δ : ℝ := (1 : ℝ) / k
  let coarse := residueDensity A N q
  let fine := refinedDensity A N q r
  let B := badParents coarse fine δ
  let D := Energy.denseGoodSupport B δ coarse
  have hq : 0 < q := klsModulus_pos K k i
  have hr : 0 < r := Nat.lcmUpto_pos _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact (div_le_one (by positivity)).2 this
  have hcoarse : Energy.IsDensity coarse := by
    exact klsResidueDensity_isDensity K k (klsLevelCount k) hN hfinal hA
      (i := i) hi.le
  have hglobal : Energy.mean (fun j ↦ Energy.parentVariance coarse fine j) ≤
      (1 : ℝ) / (4 * klsLevelCount k) := by
    rw [← klsEnergy_step K k A hN]
    exact hinc
  have hBvar : ∀ j ∈ B, δ ^ 2 / 128 ≤
      Energy.parentVariance coarse fine j := by
    intro j hj
    exact parentVariance_ge_of_mem_badParents hr hδ.le hj
  have hBcard : (B.card : ℝ) < δ * q / 2 := by
    apply Energy.badParents_card_lt_half hq
      (fun j ↦ Energy.parentVariance coarse fine j) B hδ
    · intro j
      exact Energy.parentVariance_nonneg hr coarse fine j
    · exact hBvar
    · exact hglobal
    · exact kls_small_increment_lt hk
  have hmean : (11 : ℝ) / 32 + δ ≤ Energy.mean coarse := by
    rw [mean_residueDensity hN hq A]
    exact hmass
  have hD : (11 : ℝ) / 32 < (D.card : ℝ) / q := by
    exact Energy.eleven_thirtytwo_lt_denseGoodSupport hq hcoarse B
      hδ hδ1 hmean hBcard
  obtain ⟨a, haD, b, hbD, habsq⟩ := exists_square_pair_of_los hLOS hq D hD
  let c := (a.val + b.val) % q
  have hcsq : IsSquare (c : ZMod q) := by
    simpa [c, Nat.cast_add] using habsq
  have haGood : a ∉ B ∧ δ / 2 ≤ coarse a := by
    simpa [D, Energy.denseGoodSupport] using haD
  have hbGood : b ∉ B ∧ δ / 2 ≤ coarse b := by
    simpa [D, Energy.denseGoodSupport] using hbD
  have haChildren : 7 * r ≤ 8 * (denseChildren fine δ a).card :=
    seven_eighths_denseChildren hr hδ.le haGood.1 haGood.2
  have hbChildren : 7 * r ≤ 8 * (denseChildren fine δ b).card :=
    seven_eighths_denseChildren hr hδ.le hbGood.1 hbGood.2
  refine ⟨i, hi, ?_⟩
  dsimp only
  exact global_dense_pair_lower_real hN hq hr hA a b rfl hcsq δ hδ.le
    haChildren hbChildren

/-- The finite contradiction, with the analytic shifting bounds supplied at
every possible small-increment level. -/
theorem kls_divisible_density_upper_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m)
    (Knat k : ℕ) (hk : 0 < k) {C : ℝ} (hC : 0 < C)
    (hCnat : C ≤ Knat + 1)
    {N : ℕ} (hN : 0 < N) {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N)
    (hfinal : klsModulus Knat k (klsLevelCount k) ∣ N)
    (hshift : ∀ i < klsLevelCount k,
      let q := klsModulus Knat k i
      let P := klsThreshold Knat k q
      let r := Nat.lcmUpto P
      ∀ j ≤ squareShiftCutoff N (q * r),
        (shiftedSquarePairCount A (j * (q * r)) : ℝ) ≤
          C * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ))
    (hcut : ∀ i < klsLevelCount k,
      let q := klsModulus Knat k i
      let r := Nat.lcmUpto (klsThreshold Knat k q)
      (squareShiftCutoff N (q * r) + 1 : ℕ) ≤
        (15 : ℝ) * Real.sqrt (N : ℝ)) :
    (A.card : ℝ) / (N : ℝ) ≤ (11 : ℝ) / 32 + (1 : ℝ) / k := by
  by_contra hnot
  have hmass : (11 : ℝ) / 32 + (1 : ℝ) / k ≤
      (A.card : ℝ) / (N : ℝ) := (not_le.mp hnot).le
  obtain ⟨i, hi, hlower⟩ :=
    exists_level_totalShifted_lower_of_los hLOS Knat k hk hN hA hfinal hmass
  let q := klsModulus Knat k i
  let P := klsThreshold Knat k q
  let r := Nat.lcmUpto P
  let J := squareShiftCutoff N (q * r)
  let T := (totalShiftedSquarePairCount A (q * r) J : ℝ)
  have hq : 0 < q := klsModulus_pos Knat k i
  have hP : 0 < P := by dsimp [P, klsThreshold]; positivity
  have hsqrtP : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hP)
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hN)
  have hpoint : ∀ j ≤ J,
      (shiftedSquarePairCount A (j * (q * r)) : ℝ) ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ) := by
    exact hshift i hi
  have htotal : T ≤ (J + 1 : ℕ) *
      (C * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ)) := by
    exact totalShiftedSquarePairCount_cast_le_of_pointwise hpoint
  have hpow : (N : ℝ) ^ ((3 : ℝ) / 2) =
      (N : ℝ) * Real.sqrt (N : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by norm_num,
      Real.rpow_add (Nat.cast_pos.mpr hN), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hTupper : T ≤ 15 * C * (N : ℝ) ^ 2 / Real.sqrt (P : ℝ) := by
    calc
      T ≤ (J + 1 : ℕ) *
          (C * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ)) := htotal
      _ ≤ (15 * Real.sqrt (N : ℝ)) *
          (C * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ)) := by
        gcongr
        exact hcut i hi
      _ = 15 * C * (N : ℝ) ^ 2 / Real.sqrt (P : ℝ) := by
        rw [hpow, pow_two]
        field_simp [hsqrtP.ne']
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  change 3 * (((1 : ℝ) / k) * (N : ℝ)) ^ 2 ≤
      64 * (q : ℝ) ^ 2 * T at hlower
  have hcombine : 3 * (((1 : ℝ) / k) * (N : ℝ)) ^ 2 ≤
      64 * (q : ℝ) ^ 2 *
        (15 * C * (N : ℝ) ^ 2 / Real.sqrt (P : ℝ)) :=
    hlower.trans (mul_le_mul_of_nonneg_left hTupper (by positivity))
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hN)
  have hcancel : (3 : ℝ) / (k : ℝ) ^ 2 ≤
      (960 * C * (q : ℝ) ^ 2) / Real.sqrt (P : ℝ) := by
    apply le_of_mul_le_mul_left (a := (N : ℝ) ^ 2) _ hN2
    calc
      (N : ℝ) ^ 2 * (3 / (k : ℝ) ^ 2) =
          3 * (((1 : ℝ) / k) * (N : ℝ)) ^ 2 := by
        field_simp
      _ ≤ 64 * (q : ℝ) ^ 2 *
          (15 * C * (N : ℝ) ^ 2 / Real.sqrt (P : ℝ)) := hcombine
      _ = (N : ℝ) ^ 2 *
          ((960 * C * (q : ℝ) ^ 2) / Real.sqrt (P : ℝ)) := by ring
  have hrearrange : 3 * Real.sqrt (P : ℝ) ≤
      (960 * C * (q : ℝ) ^ 2) * (k : ℝ) ^ 2 := by
    exact (div_le_div_iff₀ (sq_pos_of_pos hkR) hsqrtP).mp hcancel
  have hthreshold : 320 * C * (k : ℝ) ^ 2 * (q : ℝ) ^ 2 <
      Real.sqrt (P : ℝ) := by
    exact klsThreshold_sqrt_lower hCnat hq
  nlinarith

/-- Eventual upper bound on endpoints divisible by one fixed terminal
modulus. -/
theorem eventually_divisible_density_upper_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m)
    (k : ℕ) (hk : 0 < k) :
    ∃ Q : ℕ, 0 < Q ∧
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
        A ⊆ Finset.Icc 1 N → SquareSumFree A → Q ∣ N →
          (A.card : ℝ) / (N : ℝ) ≤
            (11 : ℝ) / 32 + (1 : ℝ) / k := by
  rcases klsShortShiftingStatement with ⟨C, hC, hshift⟩
  obtain ⟨Knat, hKnat⟩ := exists_nat_gt C
  let L := klsLevelCount k
  let Q := klsModulus Knat k L
  refine ⟨Q, klsModulus_pos Knat k L, ?_⟩
  let Good : ℕ → ℕ → Prop := fun i N ↦
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → SquareSumFree A →
      (∀ j ≤ squareShiftCutoff N
          (klsModulus Knat k i * Nat.lcmUpto
            (klsThreshold Knat k (klsModulus Knat k i))),
        (shiftedSquarePairCount A
          (j * (klsModulus Knat k i * Nat.lcmUpto
            (klsThreshold Knat k (klsModulus Knat k i)))) : ℝ) ≤
          C * (N : ℝ) ^ ((3 : ℝ) / 2) /
            Real.sqrt (klsThreshold Knat k (klsModulus Knat k i) : ℝ)) ∧
      ((squareShiftCutoff N
          (klsModulus Knat k i * Nat.lcmUpto
            (klsThreshold Knat k (klsModulus Knat k i))) + 1 : ℕ) ≤
        (15 : ℝ) * Real.sqrt (N : ℝ))
  have hlevel : ∀ i ∈ Finset.range L, ∀ᶠ N : ℕ in atTop, Good i N := by
    intro i hi
    let q := klsModulus Knat k i
    let P := klsThreshold Knat k q
    let r := Nat.lcmUpto P
    have hq : 0 < q := klsModulus_pos Knat k i
    have hP : 0 < P := by dsimp [P, klsThreshold]; positivity
    have hs := hshift q P hq hP
    have hc := eventually_squareShiftCutoff_add_one_le (q * r)
    filter_upwards [hs, hc] with N hsN hcN
    intro A hA hfree
    constructor
    · intro j hj
      have := hsN A hA hfree j
      simpa [Good, q, P, r, shiftModulus, klsShortShiftCutoff,
        squareShiftCutoff] using this hj
    · simpa [Good, q, P, r] using hcN
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.range L, Good i N :=
    (Finset.eventually_all (Finset.range L)).2 hlevel
  filter_upwards [hall, eventually_gt_atTop (0 : ℕ)] with N hallN hN
  intro A hA hfree hdiv
  apply kls_divisible_density_upper_of_los hLOS Knat k hk hC
    (show C ≤ (Knat : ℝ) + 1 by linarith) hN hA
  · simpa [Q, L] using hdiv
  · intro i hi
    exact (hallN i (Finset.mem_range.mpr hi) A hA hfree).1
  · intro i hi
    exact (hallN i (Finset.mem_range.mpr hi) A hA hfree).2

/-- One-time padding removes the divisibility restriction at the cost of one
additional reciprocal margin. -/
theorem eventually_density_upper_two_reciprocal_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m)
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → SquareSumFree A →
        (A.card : ℝ) / (N : ℝ) ≤
          (11 : ℝ) / 32 + (2 : ℝ) / k := by
  obtain ⟨Q, hQ, hdivisible⟩ := eventually_divisible_density_upper_of_los hLOS k hk
  have htend : Tendsto (paddedEndpoint Q) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ le_paddedEndpoint hQ) tendsto_id
  have hpadded : ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 (paddedEndpoint Q N) → SquareSumFree A →
        Q ∣ paddedEndpoint Q N →
          (A.card : ℝ) / (paddedEndpoint Q N : ℝ) ≤
            (11 : ℝ) / 32 + (1 : ℝ) / k :=
    htend.eventually hdivisible
  filter_upwards [hpadded, eventually_ge_atTop (2 * Q * k),
    eventually_gt_atTop (0 : ℕ)] with N hpN hlarge hN
  intro A hA hfree
  let M := paddedEndpoint Q N
  let c : ℝ := (11 : ℝ) / 32 + (1 : ℝ) / k
  have hNM : N ≤ M := le_paddedEndpoint hQ
  have hM : 0 < M := hN.trans_le hNM
  have hAM : A ⊆ Finset.Icc 1 M := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hA hx)
    exact Finset.mem_Icc.mpr ⟨hx'.1, hx'.2.trans hNM⟩
  have hp : (A.card : ℝ) / (M : ℝ) ≤ c := by
    exact hpN A hAM hfree (dvd_paddedEndpoint Q N)
  have hcard : (A.card : ℝ) ≤ c * (M : ℝ) := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hM)] at hp
    simpa [mul_comm] using hp
  have hMlt : (M : ℝ) < (N : ℝ) + Q := by
    exact_mod_cast paddedEndpoint_lt_add hQ (N := N)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc2 : c ≤ 2 := by
    dsimp [c]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hone : (1 : ℝ) / k ≤ 1 := (div_le_one hkR).2 hk1
    norm_num at hone ⊢
    linarith
  have hlargeR : (2 : ℝ) * Q * k ≤ N := by exact_mod_cast hlarge
  have herr : c * (Q : ℝ) ≤ (N : ℝ) / k := by
    rw [le_div_iff₀ hkR]
    calc
      c * (Q : ℝ) * (k : ℝ) ≤ 2 * Q * k := by gcongr
      _ ≤ N := hlargeR
  have hlinear : (A.card : ℝ) ≤
      ((11 : ℝ) / 32 + (2 : ℝ) / k) * (N : ℝ) := by
    calc
      (A.card : ℝ) ≤ c * (M : ℝ) := hcard
      _ ≤ c * ((N : ℝ) + Q) :=
        mul_le_mul_of_nonneg_left hMlt.le hc0
      _ ≤ ((11 : ℝ) / 32 + (2 : ℝ) / k) * (N : ℝ) := by
        calc
          c * ((N : ℝ) + Q) = c * (N : ℝ) + c * (Q : ℝ) := by ring
          _ ≤ c * (N : ℝ) + (N : ℝ) / k := by
            simpa only [add_comm] using add_le_add_left herr (c * (N : ℝ))
          _ = ((11 : ℝ) / 32 + (2 : ℝ) / k) * (N : ℝ) := by
            dsimp [c]
            ring
  exact card_div_le_of_card_le_mul hN hlinear

/-- Conditional final form, isolating the exact modular theorem consumed by
the KLS argument. -/
theorem kls_eventuallyUpper_of_los
    (hLOS : ∀ (m : ℕ), 1 ≤ m → ∀ B : Finset (ZMod m),
      (∀ a ∈ B, ∀ b ∈ B, ¬ IsSquare (a + b)) →
        32 * B.card ≤ 11 * m) :
    EventuallyUpper := by
  intro ε hε
  obtain ⟨k, hklarge⟩ := exists_nat_gt ((2 : ℝ) / ε)
  have htwoeps : (0 : ℝ) < 2 / ε := by positivity
  have hk : 0 < k := by
    have : (0 : ℝ) < k := htwoeps.trans hklarge
    exact_mod_cast this
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hmargin : (2 : ℝ) / k < ε := by
    rw [div_lt_iff₀ hkR]
    have := (div_lt_iff₀ hε).mp hklarge
    nlinarith
  have hbound := eventually_density_upper_two_reciprocal_of_los hLOS k hk
  filter_upwards [hbound] with N hN
  intro A hA
  exact (hN A hA.1 hA.2).trans (by linarith)

/-- The Khalfalah--Lodha--Szemeredi asymptotic upper bound: every sufficiently
large square-sum-free subset of `Icc 1 N` has density at most
`11 / 32 + ε`. -/
theorem kls_eventuallyUpper : EventuallyUpper := by
  apply kls_eventuallyUpper_of_los
  intro m hm B hB
  exact los_modular hm B hB

end

end Erdos438
