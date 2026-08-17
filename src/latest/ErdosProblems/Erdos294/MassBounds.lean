/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos297.LocalLimit
import ErdosProblems.Erdos285.Analytic

/-!
# Reciprocal-mass bounds for the Liu--Sawhney good set

The source good set has density at least `89 / 100` in `[1,N]`.  A decreasing
rearrangement therefore bounds its reciprocal mass below by the terminal
harmonic interval of the same cardinality.  Its lower endpoint `M` gives the
matching (much smaller than `log log N`) upper bound.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.MassBounds

open Erdos285
open Erdos297
open Erdos297.GoodSetDensity Erdos297.FactorDensity
open Erdos297.LogisticNormalization
open Erdos285.RoughCounts

noncomputable section

attribute [local instance] Classical.propDecidable

lemma card_filter_gt_orderIso (A : Finset ℕ) (i : Fin A.card) :
    (A.filter fun n ↦ (A.orderIsoOfFin rfl i : ℕ) < n).card =
      A.card - (i : ℕ) - 1 := by
  let e := A.orderIsoOfFin rfl
  have heq : A.filter (fun n ↦ (e i : ℕ) < n) =
      (Finset.univ.filter fun j : Fin A.card ↦ i < j).image
        (fun j ↦ (e j : ℕ)) := by
    ext n
    constructor
    · intro hn
      simp only [Finset.mem_filter] at hn
      let x : A := ⟨n, hn.1⟩
      let j : Fin A.card := e.symm x
      have hij : i < j := by
        apply e.lt_iff_lt.mp
        change (e i : ℕ) < (e j : ℕ)
        simpa [j, x] using hn.2
      apply Finset.mem_image.mpr
      refine ⟨j, by simp [hij], ?_⟩
      simp [j, x]
    · intro hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_filter.mpr ⟨(e j).property, e.strictMono hj⟩
  rw [heq]
  have hinj : Function.Injective (fun j ↦ (e j : ℕ)) :=
    Subtype.val_injective.comp e.injective
  calc
    ((Finset.univ.filter fun j : Fin A.card ↦ i < j).image
        (fun j ↦ (e j : ℕ))).card =
        (Finset.univ.filter fun j : Fin A.card ↦ i < j).card :=
      Finset.card_image_iff.mpr hinj.injOn
    _ = A.card - (i : ℕ) - 1 := by
      rw [show (Finset.univ.filter fun j : Fin A.card ↦ i < j) =
        Finset.Ioi i by ext; simp]
      rw [Fin.card_Ioi]
      omega

lemma orderIso_apply_le_terminal (A : Finset ℕ) {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (i : Fin A.card) :
    (A.orderIsoOfFin rfl i : ℕ) ≤ N - A.card + 1 + i := by
  let e := A.orderIsoOfFin rfl
  let a : ℕ := e i
  have haN : a ≤ N := (Finset.mem_Icc.mp (hA (e i).property)).2
  have htailSub : A.filter (fun n ↦ a < n) ⊆ Finset.Icc (a + 1) N := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨Nat.add_one_le_iff.mpr hn.2,
      (Finset.mem_Icc.mp (hA hn.1)).2⟩
  have hcard := Finset.card_le_card htailSub
  have hformula : (A.filter fun n ↦ a < n).card = A.card - i - 1 := by
    simpa [a, e] using card_filter_gt_orderIso A i
  rw [hformula] at hcard
  simp at hcard
  change a ≤ N - A.card + 1 + i
  omega

/-- Decreasing rearrangement for reciprocal mass on `[1,N]`. -/
lemma terminalReciprocalSum_le_reciprocalMass (A : Finset ℕ) {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    Analytic.terminalReciprocalSum (N - A.card + 1) A.card ≤
      reciprocalMass A := by
  let e := A.orderIsoOfFin rfl
  have hpoint : ∀ i : Fin A.card,
      (1 : ℝ) / ((N - A.card + 1 + (i : ℕ) : ℕ) : ℝ) ≤
        (1 : ℝ) / (e i : ℕ) := by
    intro i
    apply one_div_le_one_div_of_le
    · exact_mod_cast (Finset.mem_Icc.mp (hA (e i).property)).1
    · exact_mod_cast orderIso_apply_le_terminal A hA i
  calc
    Analytic.terminalReciprocalSum (N - A.card + 1) A.card =
        ∑ i : Fin A.card,
          (1 : ℝ) / ((N - A.card + 1 + (i : ℕ) : ℕ) : ℝ) := by
      rw [Analytic.terminalReciprocalSum]
      exact (Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦
          (1 : ℝ) / ((N - A.card + 1 + i : ℕ) : ℝ)) A.card).symm
    _ ≤ ∑ i : Fin A.card, (1 : ℝ) / (e i : ℕ) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = ∑ n ∈ A, (1 : ℝ) / n := by
      calc
        ∑ i : Fin A.card, (1 : ℝ) / (e i : ℕ) =
            ∑ n : A, (1 : ℝ) / (n : ℕ) := by
          exact Fintype.sum_equiv e.toEquiv _ _ (fun _ ↦ rfl)
        _ = ∑ n ∈ A, (1 : ℝ) / n := by
          simpa using Finset.sum_attach A (fun n : ℕ ↦ (1 : ℝ) / n)
    _ = reciprocalMass A := by
      simp only [reciprocalMass, one_div]

/-- The dense source good set has reciprocal mass at least two. -/
theorem eventually_two_le_goodSet_reciprocalMass :
    ∀ᶠ N : ℕ in atTop, 2 ≤ reciprocalMass (goodSet N) := by
  filter_upwards [eventually_sourceGoodDenominators_card_ge,
    eventually_sourceGoodDenominators_subset_denominators,
    eventually_ge_atTop (900 : ℕ)] with N hcard hsub hN
  let A := sourceGoodDenominators N
  let L := N - A.card + 1
  have hcardN : A.card ≤ N := by
    calc
      A.card ≤ (Icc 1 N).card := Finset.card_le_card hsub
      _ = N := by simp
  have hLpos : 0 < L := by simp [L]
  have hLupper : (L : ℝ) ≤ (11 / 100 : ℝ) * N + 1 := by
    change (((N - A.card) + 1 : ℕ) : ℝ) ≤
      (11 / 100 : ℝ) * N + 1
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hcardN]
    linarith
  have hsum : Analytic.terminalReciprocalSum L A.card ≤ reciprocalMass A :=
    terminalReciprocalSum_le_reciprocalMass A hsub
  have hendpoint : L + A.card = N + 1 := by
    dsimp [L]
    omega
  have hexpTwo : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hexpRatio : Real.exp 2 ≤ (((L + A.card : ℕ) : ℝ) / L) := by
    rw [hendpoint]
    apply (le_div_iff₀ (by exact_mod_cast hLpos)).2
    have hNreal : (900 : ℝ) ≤ N := by exact_mod_cast hN
    have hmul : Real.exp 2 * (L : ℝ) ≤
        9 * ((11 / 100 : ℝ) * N + 1) := by
      calc
        Real.exp 2 * (L : ℝ) ≤
            Real.exp 2 * ((11 / 100 : ℝ) * N + 1) := by
          gcongr
        _ ≤ 9 * ((11 / 100 : ℝ) * N + 1) := by
          gcongr
    push_cast
    nlinarith
  have hlog : 2 ≤ Real.log ((((L + A.card : ℕ) : ℝ) / L)) := by
    rw [← Real.log_exp (2 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 2) hexpRatio
  calc
    2 ≤ Real.log ((((L + A.card : ℕ) : ℝ) / L)) := hlog
    _ ≤ Analytic.terminalReciprocalSum L A.card :=
      Analytic.log_div_le_terminalReciprocalSum hLpos
    _ ≤ reciprocalMass A := hsum
    _ = reciprocalMass (goodSet N) := by
      rfl

/-- The source good set has reciprocal mass at most one third of
`log log N`. -/
theorem eventually_goodSet_reciprocalMass_le_logLog_div_three :
    ∀ᶠ N : ℕ in atTop,
      reciprocalMass (goodSet N) ≤ logLogScale N / 3 := by
  have hratio : ∀ᶠ N : ℕ in atTop,
      Real.sqrt (logLogLogScale N) / logLogScale N ≤ (1 / 6 : ℝ) :=
    (tendsto_sqrt_logLogLog_div_logLog.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 6)).mono fun _ h ↦ h.le
  filter_upwards [hratio, eventually_real_scales_ge_two, eventually_pos_scales,
    tendsto_nat_M_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      N hratioN hscales hpos hMpos
  have hMhalf : MReal N / 2 ≤ (Erdos297.M N : ℝ) :=
    half_le_floor hscales.2.2
  have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) :=
    Real.sqrt_pos.2 hpos.2.2.2
  have hNM : (N : ℝ) / (Erdos297.M N : ℝ) ≤
      2 * Real.sqrt (logLogLogScale N) := by
    rw [div_le_iff₀ hMpos]
    have h := mul_le_mul_of_nonneg_left hMhalf
      (show 0 ≤ 2 * Real.sqrt (logLogLogScale N) by positivity)
    dsimp [MReal] at h
    field_simp [hsqrtpos.ne'] at h
    nlinarith
  have hmass : reciprocalMass (goodSet N) ≤
      ((goodSet N).card : ℝ) / Erdos297.M N := by
    apply reciprocalMass_le_card_div
    · have : (1 : ℝ) ≤ MReal N / 2 := by linarith [hscales.2.2]
      exact_mod_cast this.trans hMhalf
    · intro n hn
      have hn' : n ∈ sourceGoodDenominators N := by
        exact hn
      exact (Finset.mem_Icc.mp ((sourceGoodDenominators_subset_Icc N) hn')).1
  have hMone : 1 ≤ Erdos297.M N := by
    have : (1 : ℝ) ≤ MReal N / 2 := by linarith [hscales.2.2]
    exact_mod_cast this.trans hMhalf
  have hcard : ((goodSet N).card : ℝ) ≤ N := by
    have hsub : goodSet N ⊆ Icc 1 N :=
      (sourceGoodDenominators_subset_Icc N).trans
        (Icc_subset_Icc_left hMone)
    calc
      ((goodSet N).card : ℝ) ≤ ((Icc 1 N).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ = N := by simp
  calc
    reciprocalMass (goodSet N) ≤
        ((goodSet N).card : ℝ) / Erdos297.M N := hmass
    _ ≤ (N : ℝ) / Erdos297.M N :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ ≤ 2 * Real.sqrt (logLogLogScale N) := hNM
    _ ≤ logLogScale N / 3 := by
      have hLLpos : 0 < logLogScale N := zero_lt_one.trans hpos.2.2.1
      rw [div_le_iff₀ hLLpos] at hratioN
      nlinarith

end

end Erdos294.MassBounds
