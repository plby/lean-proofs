/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import ErdosProblems.Erdos874.RestrictedSums
import ErdosProblems.Erdos874.Structure

/-!
# The central-span calculation for Erdős Problem 874

This file isolates the finite arithmetic core of Deshouillers--Freiman's
Theorem 3.  The long progression supplied by the structure theorem orders
restricted-sum layers whose cardinalities differ by the structural step.
After choosing `k` with `2*k+q` equal to the size of the regular part (up to
one unused point), the endpoint comparison gives the exact inequality proved
below.  It is the integer, constant-explicit form of the paper's estimate

`b_(2k+q-t) - b_(t+1) = q * (2k + O(N^(11/24)))`.

The definitions of common difference and difference gcd also record the
first step of the published proof: the structural difference is the gcd of
all pairwise differences once the exceptional elements have been shown to
lie in the regular residue class.
-/

open scoped BigOperators Pointwise

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The common gcd step -/

/-- A positive integer dividing every pairwise difference in `A`. -/
def HasCommonDifference (A : Finset ℤ) (q : ℕ) : Prop :=
  0 < q ∧ ∀ x ∈ A, ∀ y ∈ A, (q : ℤ) ∣ x - y

/-- Divisibility characterization of the gcd of all differences of `A`. -/
def IsCommonDifferenceGCD (A : Finset ℤ) (q : ℕ) : Prop :=
  HasCommonDifference A q ∧
    ∀ d : ℕ, HasCommonDifference A d → d ∣ q

/-- Containment in a positive-step progression gives a common difference. -/
lemma hasCommonDifference_of_containedInAP
    {A : Finset ℤ} {start : ℤ} {q L : ℕ} (hq : 0 < q)
    (hA : ContainedInAP A start q L) :
    HasCommonDifference A q := by
  refine ⟨hq, ?_⟩
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := hA.exists_coordinate hx
  obtain ⟨j, hj, hyj⟩ := hA.exists_coordinate hy
  rw [hxi, hyj]
  refine ⟨(i : ℤ) - j, ?_⟩
  ring

/-- Equal-cardinality restricted sums are congruent modulo every common
difference of the underlying set. -/
lemma HasCommonDifference.dvd_sub_restrictedSumset
    {A : Finset ℤ} {q r : ℕ} (hA : HasCommonDifference A q)
    {x y : ℤ} (hx : x ∈ restrictedSumset r A)
    (hy : y ∈ restrictedSumset r A) :
    (q : ℤ) ∣ x - y := by
  obtain ⟨X, hXA, hXcard, hXsum⟩ := mem_restrictedSumset.mp hx
  obtain ⟨Y, hYA, hYcard, hYsum⟩ := mem_restrictedSumset.mp hy
  by_cases hAempty : A = ∅
  · subst A
    have hXempty : X = ∅ := Finset.subset_empty.mp hXA
    have hYempty : Y = ∅ := Finset.subset_empty.mp hYA
    subst X
    subst Y
    simp at hXsum hYsum
    subst x
    subst y
    simp
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
    have hmodX : x ≡ (r : ℤ) * a [ZMOD (q : ℤ)] := by
      rw [← hXsum]
      have hsum := Int.ModEq.sum (s := X) (f := fun z : ℤ ↦ z)
        (g := fun _ : ℤ ↦ a) (fun z hz ↦
          Int.modEq_iff_dvd.mpr (hA.2 a ha z (hXA hz)))
      simpa [Finset.sum_const, hXcard, nsmul_eq_mul, mul_comm] using hsum
    have hmodY : y ≡ (r : ℤ) * a [ZMOD (q : ℤ)] := by
      rw [← hYsum]
      have hsum := Int.ModEq.sum (s := Y) (f := fun z : ℤ ↦ z)
        (g := fun _ : ℤ ↦ a) (fun z hz ↦
          Int.modEq_iff_dvd.mpr (hA.2 a ha z (hYA hz)))
      simpa [Finset.sum_const, hYcard, nsmul_eq_mul, mul_comm] using hsum
    have hxy : x ≡ y [ZMOD (q : ℤ)] := hmodX.trans hmodY.symm
    rw [← neg_sub]
    exact dvd_neg.mpr (Int.modEq_iff_dvd.mp hxy)

/-- A two-term progression in one equal-cardinality layer identifies a
common structural step with the gcd of all differences. -/
theorem isCommonDifferenceGCD_of_commonDifference_of_progression
    {A C : Finset ℤ} {q t L : ℕ}
    (hcommon : HasCommonDifference A q) (hCA : C ⊆ A)
    (hL : 2 ≤ L)
    (hprog : ContainsAP (restrictedSumset t C) (q : ℤ) L) :
    IsCommonDifferenceGCD A q := by
  refine ⟨hcommon, ?_⟩
  intro d hd
  obtain ⟨a, ha⟩ := hprog
  have hzero : a ∈ restrictedSumset t C :=
    ha (mem_arithmeticProgression.mpr ⟨0, by omega, by simp⟩)
  have hone : a + (q : ℤ) ∈ restrictedSumset t C := by
    apply ha
    exact mem_arithmeticProgression.mpr ⟨1, by omega, by simp⟩
  have hzeroA : a ∈ restrictedSumset t A :=
    restrictedSumset_mono hCA hzero
  have honeA : a + (q : ℤ) ∈ restrictedSumset t A :=
    restrictedSumset_mono hCA hone
  have hdq : (d : ℤ) ∣ (q : ℤ) := by
    simpa using hd.dvd_sub_restrictedSumset honeA hzeroA
  exact_mod_cast hdq

/-! ## Ordering translated layers -/

/-- Convexity inside one residue class: every intermediate term of the
`q`-progression is present.  Adding the long progression in the structure
theorem to a restricted layer of the regular part produces this property. -/
def IsStepInterval (q : ℕ) (S : Finset ℤ) : Prop :=
  ∀ {x y z : ℤ}, x ∈ S → y ∈ S → x ≤ z → z ≤ y →
    (q : ℤ) ∣ z - x → z ∈ S

/-- Two disjoint convex pieces of the same residue class cannot cross. -/
theorem lt_of_disjoint_stepIntervals
    {q : ℕ} {P Q : Finset ℤ}
    (hP : IsStepInterval q P) (hQ : IsStepInterval q Q)
    (hPQ : Disjoint P Q)
    (hres : ∀ p ∈ P, ∀ z ∈ Q, (q : ℤ) ∣ p - z)
    {p₀ z₀ : ℤ} (hp₀ : p₀ ∈ P) (hz₀ : z₀ ∈ Q) (hpz : p₀ < z₀) :
    ∀ {p : ℤ}, p ∈ P → ∀ {z : ℤ}, z ∈ Q → p < z := by
  intro p hp z hz
  by_contra hn
  have hzp : z ≤ p := le_of_not_gt hn
  by_cases hzp₀ : z ≤ p₀
  · have hdiv : (q : ℤ) ∣ p₀ - z := hres p₀ hp₀ z hz
    have hp₀Q : p₀ ∈ Q := hQ hz hz₀ hzp₀ hpz.le (by
      simpa [sub_eq_add_neg, add_comm] using hdiv)
    exact (Finset.disjoint_left.mp hPQ hp₀ hp₀Q)
  · have hp₀z : p₀ ≤ z := by omega
    have hdiv : (q : ℤ) ∣ z - p₀ := by
      rw [← neg_sub]
      exact dvd_neg.mpr (hres p₀ hp₀ z hz)
    have hzP : z ∈ P := hP hp₀ hp hp₀z hzp hdiv
    exact (Finset.disjoint_left.mp hPQ hzP hz)

/-- Restricted sums on disjoint supports add to the corresponding layer of
their union. -/
lemma add_disjoint_restrictedSumsets_subset_union_layer
    {B C : Finset ℤ} {r s : ℕ} (hBC : Disjoint B C) :
    restrictedSumset r B + restrictedSumset s C ⊆
      restrictedSumset (r + s) (B ∪ C) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨X, hXB, hXcard, hXsum⟩ := mem_restrictedSumset.mp hx
  obtain ⟨Y, hYC, hYcard, hYsum⟩ := mem_restrictedSumset.mp hy
  have hXY : Disjoint X Y := hBC.mono hXB hYC
  apply mem_restrictedSumset.mpr
  refine ⟨X ∪ Y, Finset.union_subset (hXB.trans Finset.subset_union_left)
    (hYC.trans Finset.subset_union_right), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hXY, hXcard, hYcard]
  · rw [Finset.sum_union hXY, hXsum, hYsum]

/-- The two translated regular layers used in DF99 lie in different
admissible layers and hence are disjoint. -/
theorem LargeSetStructure.translated_layers_disjoint
    {N : ℕ} {A : Finset ℤ} (S : LargeSetStructure N A)
    (hA : IsAdmissible A) {r : ℕ} (hr : 0 < r) :
    Disjoint
      (restrictedSumset r (A \ S.exceptional) +
        restrictedSumset S.layer S.exceptional)
      (restrictedSumset (r + S.step) (A \ S.exceptional) +
        restrictedSumset S.layer S.exceptional) := by
  let B := A \ S.exceptional
  let C := S.exceptional
  have hCB : Disjoint C B := S.exceptional_disjoint_regular
  have hBC : Disjoint B C := hCB.symm
  have hU : B ∪ C = A := by
    simpa [B, C, Finset.union_comm] using S.exceptional_union_regular
  have hsub₁ :
      restrictedSumset r B + restrictedSumset S.layer C ⊆
        restrictedSumset (r + S.layer) A := by
    simpa [hU] using
      (add_disjoint_restrictedSumsets_subset_union_layer
        (B := B) (C := C) (r := r) (s := S.layer) hBC)
  have hsub₂ :
      restrictedSumset (r + S.step) B + restrictedSumset S.layer C ⊆
        restrictedSumset (r + S.step + S.layer) A := by
    simpa [hU] using
      (add_disjoint_restrictedSumsets_subset_union_layer
        (B := B) (C := C) (r := r + S.step) (s := S.layer) hBC)
  have hstep := S.step_pos
  have hleftPos : 0 < r + S.layer := by omega
  have hrightPos : 0 < r + S.step + S.layer := by omega
  have hne : r + S.layer ≠ r + S.step + S.layer := by omega
  exact (hA hleftPos hrightPos hne).mono hsub₁ hsub₂

/-! ## Exact endpoint calculation -/

private lemma sum_initial_gap_formula (m : ℕ) (q : ℤ) :
    ∑ i ∈ Finset.range m, q * (q + 1 + 2 * (i : ℤ)) =
      q * (m : ℤ) * (q + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma sum_terminal_gap_formula (t : ℕ) (q D : ℤ) :
    ∑ h ∈ Finset.range (t + 1), (D + 2 * (h : ℤ) * q) =
      (t + 1 : ℕ) * D + q * (t : ℤ) * (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The exact endpoint calculation in the refinement step of DF99,
Theorem 3.  `b` is the increasing, zero-based enumeration of the regular
part.  The gap hypothesis is what congruence modulo `q` supplies, and
`hcompare` is the ordered `k` versus `k+q` layer inequality. -/
theorem central_pair_bound
    {N k q t : ℕ} {b : ℕ → ℤ}
    (hq : 0 < q) (ht : t < k)
    (hgap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (q : ℤ) ≤ b j)
    (hN : b (2 * k + q - 1) ≤ (N : ℤ))
    (hcompare :
      ∑ i ∈ Finset.range k, b (k + q + i) <
        ∑ i ∈ Finset.range (k + q), b i) :
    ((t + 1 : ℕ) : ℤ) *
          (b (2 * k + q - t - 1) - b t) +
        (q : ℤ) * (k - t - 1 : ℕ) *
          ((q : ℤ) + (k - t - 1 : ℕ)) +
        (q : ℤ) * t * (t + 1) <
      (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
  let pair : ℕ → ℤ := fun i => b (k + q + i) - b (k - 1 - i)
  let m := k - t - 1
  have hkm : k = m + (t + 1) := by
    dsimp [m]
    omega
  have hpair :
      ∑ i ∈ Finset.range k, pair i <
        ∑ h ∈ Finset.range q, b (k + h) := by
    have hreflect :
        ∑ i ∈ Finset.range k, b (k - 1 - i) =
          ∑ i ∈ Finset.range k, b i :=
      Finset.sum_range_reflect b k
    rw [Finset.sum_range_add] at hcompare
    simp only [pair, Finset.sum_sub_distrib, hreflect]
    omega
  have hmidIndex : k + q - 1 ≤ 2 * k + q - 1 := by omega
  have hlastGap := hgap (k + q - 1) (2 * k + q - 1) hmidIndex
  have hlastDiff : 2 * k + q - 1 - (k + q - 1) = k := by omega
  rw [hlastDiff] at hlastGap
  have hmiddle :
      ∑ h ∈ Finset.range q, b (k + h) ≤
        (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
    have hterm : ∀ h ∈ Finset.range q, b (k + h) ≤ b (k + q - 1) := by
      intro h hh
      have hle : k + h ≤ k + q - 1 := by
        simp only [Finset.mem_range] at hh
        omega
      have hg := hgap _ _ hle
      have hnonneg : (0 : ℤ) ≤ (k + q - 1 - (k + h) : ℕ) * (q : ℤ) := by
        positivity
      omega
    have hsum := Finset.sum_le_sum hterm
    have hmid : b (k + q - 1) ≤ (N : ℤ) - (k : ℤ) * q := by
      omega
    calc
      ∑ h ∈ Finset.range q, b (k + h)
          ≤ ∑ _h ∈ Finset.range q, b (k + q - 1) := hsum
      _ = (q : ℤ) * b (k + q - 1) := by simp
      _ ≤ (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
        exact mul_le_mul_of_nonneg_left hmid (by positivity)
  have hpairsUpper :
      ∑ i ∈ Finset.range k, pair i <
        (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) :=
    hpair.trans_le hmiddle
  have hfirst : ∀ i ∈ Finset.range m,
      (q : ℤ) * ((q : ℤ) + 1 + 2 * (i : ℤ)) ≤ pair i := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hindices : k - 1 - i ≤ k + q + i := by omega
    have hg := hgap (k - 1 - i) (k + q + i) hindices
    have hdiff : k + q + i - (k - 1 - i) = q + 1 + 2 * i := by
      dsimp [m] at hi'
      omega
    rw [hdiff] at hg
    dsimp [pair]
    push_cast at hg ⊢
    nlinarith
  let D := b (2 * k + q - t - 1) - b t
  have hsecond : ∀ h ∈ Finset.range (t + 1),
      D + 2 * (h : ℤ) * q ≤ pair (m + h) := by
    intro h hh
    have hh' : h < t + 1 := Finset.mem_range.mp hh
    have hmi : m + h ≤ k - 1 := by omega
    have htopLe : 2 * k + q - t - 1 ≤ k + q + (m + h) := by
      dsimp [m]
      omega
    have hbottomLe : k - 1 - (m + h) ≤ t := by
      dsimp [m]
      omega
    have htop := hgap (2 * k + q - t - 1) (k + q + (m + h)) htopLe
    have hbottom := hgap (k - 1 - (m + h)) t hbottomLe
    have htopDiff : k + q + (m + h) - (2 * k + q - t - 1) = h := by
      dsimp [m]
      omega
    have hbottomDiff : t - (k - 1 - (m + h)) = h := by
      dsimp [m]
      omega
    rw [htopDiff] at htop
    rw [hbottomDiff] at hbottom
    dsimp [pair, D]
    nlinarith
  have hlowerFirst := Finset.sum_le_sum hfirst
  have hlowerSecond := Finset.sum_le_sum hsecond
  have hsplit :
      ∑ i ∈ Finset.range k, pair i =
        (∑ i ∈ Finset.range m, pair i) +
          ∑ i ∈ Finset.range (t + 1), pair (m + i) := by
    conv_lhs => rw [hkm, Finset.sum_range_add]
  rw [hsplit] at hpairsUpper
  rw [sum_initial_gap_formula] at hlowerFirst
  rw [sum_terminal_gap_formula] at hlowerSecond
  dsimp [D] at hlowerSecond
  have hcombined :
      (q : ℤ) * (m : ℤ) * ((q : ℤ) + m) +
          (((t : ℤ) + 1) * (b (2 * k + q - t - 1) - b t) +
            (q : ℤ) * t * (t + 1)) <
        (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
    exact lt_of_le_of_lt (add_le_add hlowerFirst hlowerSecond) hpairsUpper
  simpa [m, add_assoc, add_left_comm, add_comm] using hcombined

/-- The matching lower estimate for the central pair.  This is the part of
the asymptotic equality that comes for free from the fact that consecutive
members of the regular residue class are separated by at least `q`. -/
theorem central_pair_lower_bound
    {k q t : ℕ} {b : ℕ → ℤ}
    (ht : t < k)
    (hgap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (q : ℤ) ≤ b j) :
    (q : ℤ) *
          (2 * (k : ℤ) + (q : ℤ) - 2 * (t : ℤ) - 1) ≤
      b (2 * k + q - t - 1) - b t := by
  have hindex : t ≤ 2 * k + q - t - 1 := by omega
  have hg := hgap t (2 * k + q - t - 1) hindex
  have hdiff : 2 * k + q - t - 1 - t = 2 * k + q - 2 * t - 1 := by
    omega
  rw [hdiff] at hg
  have hcast : ((2 * k + q - 2 * t - 1 : ℕ) : ℤ) =
      2 * (k : ℤ) + (q : ℤ) - 2 * (t : ℤ) - 1 := by
    omega
  rw [hcast] at hg
  nlinarith

/-- A convenient consequence of `central_pair_bound` with all manifestly
nonnegative correction terms discarded.  Dividing by `t+1` gives

`central gap < q * (2*k + (N-k^2)/(t+1))`,

which is the form used with `t` of order `N^(11/24)`. -/
theorem central_pair_bound_simplified
    {N k q t : ℕ} {b : ℕ → ℤ}
    (hq : 0 < q) (ht : t < k)
    (hgap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (q : ℤ) ≤ b j)
    (hN : b (2 * k + q - 1) ≤ (N : ℤ))
    (hcompare :
      ∑ i ∈ Finset.range k, b (k + q + i) <
        ∑ i ∈ Finset.range (k + q), b i) :
    ((t + 1 : ℕ) : ℤ) *
          (b (2 * k + q - t - 1) - b t) <
      (q : ℤ) *
        ((N : ℤ) - (k : ℤ) ^ 2 +
          2 * (k : ℤ) * ((t : ℤ) + 1)) := by
  have hcentral := central_pair_bound hq ht hgap hN hcompare
  let m := k - t - 1
  have hm : (m : ℤ) = (k : ℤ) - (t : ℤ) - 1 := by
    dsimp [m]
    omega
  have hindex : (0 : ℤ) ≤ 2 * (k : ℤ) - (t : ℤ) - 1 := by
    omega
  have hqnonneg : (0 : ℤ) ≤ q := by positivity
  have hcorrection :
      0 ≤ (q : ℤ) *
        ((q : ℤ) * (2 * (k : ℤ) - (t : ℤ) - 1) +
          2 * (t : ℤ) ^ 2 + 3 * (t : ℤ) + 1) := by
    positivity
  have hidentity :
      (q : ℤ) *
          ((N : ℤ) - (k : ℤ) ^ 2 +
            2 * (k : ℤ) * ((t : ℤ) + 1)) +
          (q : ℤ) * (m : ℤ) * ((q : ℤ) + (m : ℤ)) +
          (q : ℤ) * (t : ℤ) * ((t : ℤ) + 1) -
          (q : ℤ) * ((N : ℤ) - (k : ℤ) * (q : ℤ)) =
        (q : ℤ) *
          ((q : ℤ) * (2 * (k : ℤ) - (t : ℤ) - 1) +
            2 * (t : ℤ) ^ 2 + 3 * (t : ℤ) + 1) := by
    rw [hm]
    ring
  have hright :
      (q : ℤ) * ((N : ℤ) - (k : ℤ) * (q : ℤ)) ≤
        (q : ℤ) *
            ((N : ℤ) - (k : ℤ) ^ 2 +
              2 * (k : ℤ) * ((t : ℤ) + 1)) +
          (q : ℤ) * (m : ℤ) * ((q : ℤ) + (m : ℤ)) +
          (q : ℤ) * (t : ℤ) * ((t : ℤ) + 1) := by
    nlinarith [hidentity, hcorrection]
  have hmn : k - t - 1 = m := by rfl
  rw [hmn] at hcentral
  nlinarith

/-- The first quantitative consequence of the ordered-layer comparison.
This is the exact finite inequality from which DF99 obtains
`q = O(N^(5/12))` after inserting `2*k+q = 2*sqrt N + O(N^(5/12))`.

The formulation over `ℤ` deliberately avoids truncated subtraction. -/
theorem central_step_quadratic_bound
    {N k q : ℕ} {b : ℕ → ℤ}
    (hq : 0 < q) (hk : 0 < k)
    (hgap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (q : ℤ) ≤ b j)
    (hN : b (2 * k + q - 1) ≤ (N : ℤ))
    (hcompare :
      ∑ i ∈ Finset.range k, b (k + q + i) <
        ∑ i ∈ Finset.range (k + q), b i) :
    (k : ℤ) ^ 2 + 2 * k * q < N := by
  have hcentral := central_pair_bound
    (N := N) (k := k) (q := q) (t := 0) hq hk hgap hN hcompare
  have hindex : 0 ≤ 2 * k + q - 1 := by omega
  have hwide := hgap 0 (2 * k + q - 1) hindex
  have hcastq : (0 : ℤ) < q := by exact_mod_cast hq
  have hkcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
  have hTcast : ((2 * k + q - 1 : ℕ) : ℤ) =
      2 * (k : ℤ) + q - 1 := by omega
  have hkzero : k - 0 - 1 = k - 1 := by omega
  have htopzero : 2 * k + q - 0 - 1 = 2 * k + q - 1 := by omega
  rw [hkzero, htopzero] at hcentral
  norm_num at hcentral
  rw [hkcast] at hcentral
  simp only [Nat.sub_zero] at hwide
  rw [hTcast] at hwide
  have hD :
      (q : ℤ) * (2 * (k : ℤ) + q - 1) ≤
        b (2 * k + q - 1) - b 0 := by
    nlinarith
  have hprod :
      (q : ℤ) * ((k : ℤ) * ((k : ℤ) + q)) <
        (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
    calc
      (q : ℤ) * ((k : ℤ) * ((k : ℤ) + q)) =
          (q : ℤ) * (2 * (k : ℤ) + q - 1) +
            (q : ℤ) * ((k : ℤ) - 1) *
              ((q : ℤ) + ((k : ℤ) - 1)) := by ring
      _ ≤ (b (2 * k + q - 1) - b 0) +
            (q : ℤ) * ((k : ℤ) - 1) *
              ((q : ℤ) + ((k : ℤ) - 1)) := by gcongr
      _ < (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
        exact hcentral
  by_contra hn
  have hreverse :
      (N : ℤ) - (k : ℤ) * q ≤
        (k : ℤ) * ((k : ℤ) + q) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hreverse hcastq.le
  exact (not_lt_of_ge hmul) hprod

/-- The finite central-span engine combines the step estimate with the exact
refined endpoint estimate.  In the application one takes
`t = ⌊(3/2) N^(11/24)⌋`; the two conjuncts then give, respectively,
`q = O(N^(5/12))` and the central span
`q * (2 * sqrt N + O(N^(11/24)))`. -/
theorem central_span_finite
    {N k q t : ℕ} {b : ℕ → ℤ}
    (hq : 0 < q) (ht : t < k)
    (hgap : ∀ i j : ℕ, i ≤ j →
      b i + (j - i : ℕ) * (q : ℤ) ≤ b j)
    (hN : b (2 * k + q - 1) ≤ (N : ℤ))
    (hcompare :
      ∑ i ∈ Finset.range k, b (k + q + i) <
        ∑ i ∈ Finset.range (k + q), b i) :
    (k : ℤ) ^ 2 + 2 * k * q < N ∧
      ((t + 1 : ℕ) : ℤ) *
            (b (2 * k + q - t - 1) - b t) +
          (q : ℤ) * (k - t - 1 : ℕ) *
            ((q : ℤ) + (k - t - 1 : ℕ)) +
          (q : ℤ) * t * (t + 1) <
        (q : ℤ) * ((N : ℤ) - (k : ℤ) * q) := by
  exact ⟨central_step_quadratic_bound hq (by omega) hgap hN hcompare,
    central_pair_bound hq ht hgap hN hcompare⟩

end

end Erdos874
