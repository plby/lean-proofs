/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.OuterAssembly

/-!
# Rounded parameters in the Kwan--Sudakov outer assembly

This file discharges the elementary, but pervasive, floor bookkeeping in
the proof of Erdős Problem 636.  The constants are fixed before `n`; the
main theorem then supplies one threshold which works simultaneously for
every outer parameter and every structural value `1 ≤ k ≤ K`.

The Boolean `double` records the two branches of the structural lemma.  In
the first branch `|U₀| = ell` and `nD = f`; in the second they are both
doubled.  Keeping the common scale explicit makes the identity of their
density ratios a finite theorem rather than an informal cancellation.
-/

open scoped BigOperators

namespace Erdos636.RoundedParameters

open OuterAssembly

/-- The integer outer parameters `ceil (c n) ≤ ell ≤ floor (2 c n)`. -/
noncomputable def outerParameterInterval (c : ℝ) (n : ℕ) : Finset ℕ :=
  Finset.Icc ⌈c * (n : ℝ)⌉₊ ⌊2 * c * (n : ℝ)⌋₊

/-- The common one-copy/two-copy scaling used for `U₀` and `D`. -/
def branchScale (double : Bool) (m : ℕ) : ℕ :=
  if double then 2 * m else m

@[simp] lemma branchScale_false (m : ℕ) : branchScale false m = m := rfl

@[simp] lemma branchScale_true (m : ℕ) : branchScale true m = 2 * m := rfl

lemma branchScale_pos {double : Bool} {m : ℕ} (hm : 0 < m) :
    0 < branchScale double m := by
  cases double <;> simp_all [branchScale]

lemma branchScale_mono {double : Bool} {a b : ℕ} (hab : a ≤ b) :
    branchScale double a ≤ branchScale double b := by
  cases double <;> simp_all [branchScale]

lemma branchScale_le_two_mul (double : Bool) (m : ℕ) :
    branchScale double m ≤ 2 * m := by
  cases double
  · simp only [branchScale_false]
    omega
  · simp [branchScale]

lemma branchScale_mul_real (double : Bool) (a : ℝ) (m : ℕ) :
    a * branchScale double m =
      (if double then 2 else 1) * (a * m) := by
  cases double
  · simp [branchScale]
  · simp [branchScale]
    ring

@[simp] lemma mem_outerParameterInterval {c : ℝ} {n ell : ℕ}
    (hc : 0 ≤ c) :
    ell ∈ outerParameterInterval c n ↔
      c * n ≤ ell ∧ (ell : ℝ) ≤ 2 * c * n := by
  rw [outerParameterInterval, Finset.mem_Icc]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (by exact_mod_cast hhi : (ell : ℝ) ≤ (⌊2 * c * (n : ℝ)⌋₊ : ℝ)).trans
        (Nat.floor_le (by positivity))⟩
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact_mod_cast (Nat.ceil_le.mpr hlo)
    · exact_mod_cast (Nat.le_floor hhi)

/-- Once `c n ≥ 4`, the integer interval `[ceil(cn), floor(2cn)]`
still contains at least `(c/2)n` values. -/
lemma half_linear_le_card_outerParameterInterval {c : ℝ} {n : ℕ}
    (hc : 0 < c) (hn : 4 ≤ c * n) :
    c / 2 * n ≤ ((outerParameterInterval c n).card : ℝ) := by
  let a : ℕ := ⌈c * (n : ℝ)⌉₊
  let b : ℕ := ⌊2 * c * (n : ℝ)⌋₊
  have hcn : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
  have htwo : 0 ≤ 2 * c * (n : ℝ) := by positivity
  have ha : (a : ℝ) < c * n + 1 := by
    simpa [a] using Nat.ceil_lt_add_one hcn
  have hb : 2 * c * n < (b : ℝ) + 1 := by
    simpa [b] using Nat.lt_floor_add_one (2 * c * (n : ℝ))
  have hab : a ≤ b := by
    exact_mod_cast (show (a : ℝ) ≤ (b : ℝ) by linarith)
  have hcast : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
    rw [Nat.cast_sub (by omega : a ≤ b + 1)]
    norm_num
  rw [outerParameterInterval, Nat.card_Icc]
  change c / 2 * (n : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ)
  rw [hcast]
  linarith

/-- The floor `f = floor(c₀ n)` loses at most half its main term after
`c₀ n ≥ 2`. -/
lemma deletionSize_half_le {c₀ : ℝ} {n : ℕ} (_hc₀ : 0 < c₀)
    (hn : 2 ≤ c₀ * n) :
    c₀ / 2 * n ≤ (deletionSize c₀ n : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (c₀ * (n : ℝ))
  dsimp [deletionSize] at hfloor ⊢
  linarith

/-- The elementary upper floor bound for the deletion size. -/
lemma deletionSize_le {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (n : ℕ) :
    (deletionSize c₀ n : ℝ) ≤ c₀ * n :=
  deletionSize_cast_le hc₀ n

/-- The sampling density `alpha = 1 - f/ell` belongs to `[1/2,1]`.
The stronger constant assumption used by the assembly is left to the
eventual wrapper below; this pointwise lemma needs only `2c₀ ≤ c`. -/
lemma alpha_mem_Icc {c c₀ : ℝ} {n ell : ℕ}
    (hc : 0 < c) (hc₀ : 0 ≤ c₀) (hconstants : 2 * c₀ ≤ c)
    (hn : 0 < n)
    (hell : ell ∈ outerParameterInterval c n) :
    1 / 2 ≤ 1 - (deletionSize c₀ n : ℝ) / ell ∧
      1 - (deletionSize c₀ n : ℝ) / ell ≤ 1 := by
  have hell' := (mem_outerParameterInterval hc.le).mp hell
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hellpos : (0 : ℝ) < ell :=
    (mul_pos hc hnreal).trans_le hell'.1
  have hfnonneg : (0 : ℝ) ≤ deletionSize c₀ n := by positivity
  have hfle : (deletionSize c₀ n : ℝ) ≤ (ell : ℝ) / 2 := by
    have hf := deletionSize_cast_le hc₀ n
    nlinarith [hell'.1]
  constructor
  · have hquot : (deletionSize c₀ n : ℝ) / ell ≤ 1 / 2 := by
      rw [div_le_iff₀ hellpos]
      nlinarith
    linarith
  · exact sub_le_self 1 (div_nonneg hfnonneg hellpos.le)

/-- The complete collection of rounded inequalities needed downstream. -/
structure Bounds (c c₀ δ₀ δZ : ℝ) (K n : ℕ) : Prop where
  parameter_linear :
    c / 2 * n ≤ ((outerParameterInterval c n).card : ℝ)
  deletion_lower :
    c₀ / 2 * n ≤ (deletionSize c₀ n : ℝ)
  deletion_upper :
    (deletionSize c₀ n : ℝ) ≤ c₀ * n
  alpha_bounds : ∀ ell ∈ outerParameterInterval c n,
    1 / 2 ≤ 1 - (deletionSize c₀ n : ℝ) / ell ∧
      1 - (deletionSize c₀ n : ℝ) / ell ≤ 1
  branch_linear_lower : ∀ double,
    c₀ / 2 * n ≤ (branchScale double (deletionSize c₀ n) : ℝ)
  branch_linear_upper : ∀ double,
    (branchScale double (deletionSize c₀ n) : ℝ) ≤ 2 * c₀ * n
  density_lower : ∀ double ell, ell ∈ outerParameterInterval c n →
    c₀ / (4 * c) * branchScale double ell ≤
      branchScale double (deletionSize c₀ n)
  reservoir_large : ∀ double ell, ell ∈ outerParameterInterval c n →
    3 * branchScale double (deletionSize c₀ n) ≤ branchScale double ell
  augmentation_two : ∀ k, 1 ≤ k → k ≤ K →
    2 ≤ augmentationSize δ₀ (deletionSize c₀ n) k
  augmentation_lower : ∀ k, 1 ≤ k → k ≤ K →
    δ₀ / (2 * K) * Real.sqrt (deletionSize c₀ n) ≤
      (augmentationSize δ₀ (deletionSize c₀ n) k : ℝ)
  augmentation_upper : ∀ double k, 1 ≤ k → k ≤ K →
    (augmentationSize δ₀ (deletionSize c₀ n) k : ℝ) ≤
      δZ * Real.sqrt (branchScale double (deletionSize c₀ n))

/-! ## Capacity inside the rich induced subgraph -/

/-- All ambient-scale rounded sets fit inside a rich induced subgraph of
order `m`.  Besides the individual bounds, `base_cells_le` is the exact
capacity estimate for two switching cells of size `floor(cW n)` together
with the one-copy/two-copy structural reservoir.

The only loss is downward rounding.  In particular, the switching size is
defined against the original order `n`, so it agrees definitionally with
the offset used by `OuterAssembly.assemblyOffset`; it does not depend on the
possibly varying rich-subgraph order `m`. -/
structure AmbientFit (cW cS c₀ : ℝ) (n m ell : ℕ) : Prop where
  subgraph_le_ambient : m ≤ n
  ell_le : ell ≤ m
  switching_le : deletionSize cW n ≤ m
  deletion_le : deletionSize c₀ n ≤ m
  branch_deletion_le : ∀ double,
    branchScale double (deletionSize c₀ n) ≤ m
  base_cells_le : ∀ double,
    2 * deletionSize cW n + branchScale double ell ≤ m

/-- Fixed-ambient capacity calculation used after rich-subgraph extraction.
The constant budget `2*cW + 4*cS ≤ cR` reserves space for `W⁻`, `W⁺`
and the larger (`2*ell`) structural branch.  The separate inequality
`2*c₀ ≤ cR` makes both possible deletion sizes fit as well. -/
lemma ambientFit_of_linear_rich_subgraph
    {cR cW cS c₀ : ℝ} {n m ell : ℕ}
    (hcW : 0 ≤ cW) (hcS : 0 < cS) (hc₀ : 0 ≤ c₀)
    (hbaseBudget : 2 * cW + 4 * cS ≤ cR)
    (hdeletionBudget : 2 * c₀ ≤ cR)
    (hmLower : cR * n ≤ (m : ℝ)) (hmUpper : m ≤ n)
    (hell : ell ∈ outerParameterInterval cS n) :
    AmbientFit cW cS c₀ n m ell := by
  have hellBounds := (mem_outerParameterInterval hcS.le).mp hell
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmLower' : cR * (n : ℝ) ≤ (m : ℝ) := hmLower
  have hnW : (deletionSize cW n : ℝ) ≤ cW * n :=
    deletionSize_cast_le hcW n
  have hf : (deletionSize c₀ n : ℝ) ≤ c₀ * n :=
    deletionSize_cast_le hc₀ n
  have hellmReal : (ell : ℝ) ≤ m := by
    calc
      (ell : ℝ) ≤ 2 * cS * n := hellBounds.2
      _ ≤ cR * n := by
        apply mul_le_mul_of_nonneg_right _ hnnonneg
        nlinarith
      _ ≤ m := hmLower'
  have hnWmReal : (deletionSize cW n : ℝ) ≤ m := by
    calc
      (deletionSize cW n : ℝ) ≤ cW * n := hnW
      _ ≤ cR * n := by
        apply mul_le_mul_of_nonneg_right _ hnnonneg
        nlinarith
      _ ≤ m := hmLower'
  have hfmReal : (deletionSize c₀ n : ℝ) ≤ m := by
    calc
      (deletionSize c₀ n : ℝ) ≤ c₀ * n := hf
      _ ≤ cR * n := by
        apply mul_le_mul_of_nonneg_right _ hnnonneg
        nlinarith
      _ ≤ m := hmLower'
  refine
    { subgraph_le_ambient := hmUpper
      ell_le := by exact_mod_cast hellmReal
      switching_le := by exact_mod_cast hnWmReal
      deletion_le := by exact_mod_cast hfmReal
      branch_deletion_le := ?_
      base_cells_le := ?_ }
  · intro double
    have hbranchReal :
        (branchScale double (deletionSize c₀ n) : ℝ) ≤ m := by
      calc
        (branchScale double (deletionSize c₀ n) : ℝ)
            ≤ 2 * deletionSize c₀ n := by
              exact_mod_cast branchScale_le_two_mul double (deletionSize c₀ n)
        _ ≤ 2 * c₀ * n := by nlinarith
        _ ≤ cR * n :=
          mul_le_mul_of_nonneg_right hdeletionBudget hnnonneg
        _ ≤ m := hmLower'
    exact_mod_cast hbranchReal
  · intro double
    have hbranchEll :
        (branchScale double ell : ℝ) ≤ 2 * ell := by
      exact_mod_cast branchScale_le_two_mul double ell
    have hcapacityReal :
        ((2 * deletionSize cW n + branchScale double ell : ℕ) : ℝ) ≤ m := by
      push_cast
      calc
        2 * (deletionSize cW n : ℝ) + branchScale double ell
            ≤ 2 * (cW * n) + 2 * ell := by gcongr
        _ ≤ (2 * cW + 4 * cS) * n := by
          nlinarith [hellBounds.2]
        _ ≤ cR * n :=
          mul_le_mul_of_nonneg_right hbaseBudget hnnonneg
        _ ≤ m := hmLower'
    exact_mod_cast hcapacityReal

/-! The pointwise construction below isolates the nonlinear square-root
step.  Its assumptions are the three scalar threshold inequalities which
the final Archimedean argument arranges uniformly. -/

lemma bounds_of_thresholds {c c₀ δ₀ δZ : ℝ} {K n : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ) (hK : 0 < K)
    (hcn : 4 ≤ c * n) (hc₀n : 2 ≤ c₀ * n)
    (hsqrt : (4 * (K : ℝ) / δ₀) ^ 2 ≤ c₀ / 2 * n) :
    Bounds c c₀ δ₀ δZ K n := by
  have hflo := deletionSize_half_le hc₀ hc₀n
  have hfhi := deletionSize_cast_le hc₀.le n
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hfroot : 4 * (K : ℝ) / δ₀ ≤ Real.sqrt (deletionSize c₀ n) := by
    have hleft : 0 ≤ 4 * (K : ℝ) / δ₀ := by positivity
    calc
      4 * (K : ℝ) / δ₀ = Real.sqrt ((4 * (K : ℝ) / δ₀) ^ 2) :=
        (Real.sqrt_sq hleft).symm
      _ ≤ Real.sqrt (deletionSize c₀ n) := Real.sqrt_le_sqrt (hsqrt.trans hflo)
  refine
    { parameter_linear := half_linear_le_card_outerParameterInterval hc hcn
      deletion_lower := hflo
      deletion_upper := hfhi
      alpha_bounds := ?_
      branch_linear_lower := ?_
      branch_linear_upper := ?_
      density_lower := ?_
      reservoir_large := ?_
      augmentation_two := ?_
      augmentation_lower := ?_
      augmentation_upper := ?_ }
  · intro ell hell
    exact alpha_mem_Icc hc hc₀.le (by nlinarith) (by
      have hnreal : (0 : ℝ) < n := by nlinarith [hcn]
      exact_mod_cast hnreal) hell
  · intro double
    cases double
    · simpa using hflo
    · simp only [branchScale_true, Nat.cast_mul, Nat.cast_ofNat]
      linarith
  · intro double
    cases double
    · simpa using hfhi.trans (by nlinarith)
    · simp only [branchScale_true, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
  · intro double ell hell
    have hell' := (mem_outerParameterInterval hc.le).mp hell
    have hbase : c₀ / (4 * c) * (ell : ℝ) ≤ deletionSize c₀ n := by
      have hcpos : 0 < 4 * c := by positivity
      have hellhi := hell'.2
      rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
      nlinarith
    cases double
    · simpa using hbase
    · simp only [branchScale_true, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
  · intro double ell hell
    have hell' := (mem_outerParameterInterval hc.le).mp hell
    have hbaseReal : (3 * deletionSize c₀ n : ℕ) ≤ ell := by
      exact_mod_cast (show (3 : ℝ) * deletionSize c₀ n ≤ ell by
        nlinarith [hell'.1])
    cases double
    · simpa using hbaseReal
    · simp only [branchScale_true]
      omega
  · intro k hk1 hkK
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
    have hkreal : (k : ℝ) ≤ K := by exact_mod_cast hkK
    rw [augmentationSize, Nat.le_floor_iff' (by omega : (2 : ℕ) ≠ 0)]
    rw [le_div_iff₀ hkpos]
    have hscaled := mul_le_mul_of_nonneg_left hfroot hδ₀.le
    have hid : δ₀ * (4 * (K : ℝ) / δ₀) = 4 * K := by
      field_simp
    rw [hid] at hscaled
    have h2k : (2 : ℝ) * k ≤ 4 * K := by nlinarith
    exact h2k.trans hscaled
  · intro k hk1 hkK
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
    have hkreal : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hraw := sub_one_le_augmentationSize
      (δ₀ := δ₀) (deletionSize c₀ n) k
    let A : ℝ := δ₀ * Real.sqrt (deletionSize c₀ n)
    have hAnonneg : 0 ≤ A := mul_nonneg hδ₀.le (Real.sqrt_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_left hfroot hδ₀.le
    have hid : δ₀ * (4 * (K : ℝ) / δ₀) = 4 * K := by
      field_simp
    rw [hid] at hscaled
    have h2kA : (2 : ℝ) * k ≤ A := by
      dsimp [A]
      exact (by nlinarith : (2 : ℝ) * k ≤ 4 * K).trans hscaled
    have htwoKpos : (0 : ℝ) < 2 * K := by positivity
    have htwokpos : (0 : ℝ) < 2 * k := by positivity
    have hone : (1 : ℝ) ≤ A / (2 * k) := by
      rw [le_div_iff₀ htwokpos]
      simpa [mul_comm] using h2kA
    have hdenmono : A / (2 * K) ≤ A / (2 * k) := by
      exact div_le_div_of_nonneg_left hAnonneg htwokpos
        (by nlinarith : (2 : ℝ) * k ≤ 2 * K)
    have hdouble : A / (2 * k) + 1 ≤ A / k := by
      have hidouble : A / k = 2 * (A / (2 * k)) := by
        field_simp
      rw [hidouble]
      linarith
    have hhalf :
        δ₀ / (2 * K) * Real.sqrt (deletionSize c₀ n) ≤
          δ₀ * Real.sqrt (deletionSize c₀ n) / k - 1 := by
      have hleft : δ₀ / (2 * K) * Real.sqrt (deletionSize c₀ n) =
          A / (2 * K) := by dsimp [A]; ring
      have hright : δ₀ * Real.sqrt (deletionSize c₀ n) / k = A / k := by
        rfl
      rw [hleft, hright, le_sub_iff_add_le]
      have hadd : A / (2 * K) + 1 ≤ A / (2 * k) + 1 := by
        simpa [add_comm] using add_le_add_right hdenmono 1
      exact hadd.trans hdouble
    exact hhalf.trans hraw
  · intro double k hk1 _hkK
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
    have haug := augmentationSize_cast_le hδ₀.le (deletionSize c₀ n) k
    have hfbranch : (deletionSize c₀ n : ℝ) ≤
        branchScale double (deletionSize c₀ n) := by
      cases double
      · simp [branchScale]
      · simp only [branchScale_true, Nat.cast_mul, Nat.cast_ofNat]
        have : (0 : ℝ) ≤ deletionSize c₀ n := by positivity
        linarith
    have hsqrtmono : Real.sqrt (deletionSize c₀ n) ≤
        Real.sqrt (branchScale double (deletionSize c₀ n)) :=
      Real.sqrt_le_sqrt hfbranch
    calc
      (augmentationSize δ₀ (deletionSize c₀ n) k : ℝ)
          ≤ δ₀ * Real.sqrt (deletionSize c₀ n) / k := haug
      _ ≤ δ₀ * Real.sqrt (deletionSize c₀ n) := by
        exact div_le_self (mul_nonneg hδ₀.le (Real.sqrt_nonneg _))
          (by exact_mod_cast hk1)
      _ ≤ δ₀ * Real.sqrt (branchScale double (deletionSize c₀ n)) :=
        mul_le_mul_of_nonneg_left hsqrtmono hδ₀.le
      _ ≤ δZ * Real.sqrt (branchScale double (deletionSize c₀ n)) :=
        mul_le_mul_of_nonneg_right hδZ (Real.sqrt_nonneg _)

/-- A single threshold works for the full outer interval, both structural
branches, and all finitely many values `1 ≤ k ≤ K`. -/
theorem exists_uniform_rounding_threshold {c c₀ δ₀ δZ : ℝ} {K : ℕ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hsmall : 6 * c₀ ≤ c)
    (hδ₀ : 0 < δ₀) (hδZ : δ₀ ≤ δZ) (hK : 0 < K) :
    ∃ N : ℕ, ∀ n ≥ N, Bounds c c₀ δ₀ δZ K n := by
  let T : ℝ := max (4 / c) <|
    max (2 / c₀) (2 / c₀ * (4 * (K : ℝ) / δ₀) ^ 2)
  obtain ⟨N, hN⟩ := exists_nat_gt T
  refine ⟨N, ?_⟩
  intro n hn
  have hTn : T < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hcN : 4 / c < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hTn
  have hc₀N : 2 / c₀ < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _ ) (le_max_right _ _)) hTn
  have hsqrtN : 2 / c₀ * (4 * (K : ℝ) / δ₀) ^ 2 < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hTn
  apply bounds_of_thresholds hc hc₀ hsmall hδ₀ hδZ hK
  · rw [div_lt_iff₀ hc] at hcN
    simpa [mul_comm] using hcN.le
  · rw [div_lt_iff₀ hc₀] at hc₀N
    simpa [mul_comm] using hc₀N.le
  · have hid :
        2 / c₀ * (4 * (K : ℝ) / δ₀) ^ 2 =
          (2 * (4 * (K : ℝ) / δ₀) ^ 2) / c₀ := by ring
    rw [hid, div_lt_iff₀ hc₀] at hsqrtN
    nlinarith

end Erdos636.RoundedParameters
