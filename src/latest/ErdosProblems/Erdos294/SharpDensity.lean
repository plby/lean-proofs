/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpSupply
import ErdosProblems.Erdos294.MassBounds

/-! # Density and reciprocal mass of the constant-width good set -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpDensity

open Erdos285.RoughCounts Erdos294.MassBounds Erdos294.SharpParameters
open Erdos294.SharpSupply
open Erdos297 Erdos297.GoodFactorization Erdos297.GoodSetDensity
open Erdos297.LogisticNormalization

noncomputable section

attribute [local instance] Classical.propDecidable

def oldHighSet (N : ℕ) : Finset ℕ :=
  goodSet N ∩ Icc (sharpM N) N

lemma eventually_oldHighSet_subset_sharpGoodSet :
    ∀ᶠ N : ℕ in atTop, oldHighSet N ⊆ sharpGoodSet N := by
  filter_upwards [eventually_S_le_sharpS] with N hS
  intro n hn
  rw [oldHighSet, mem_inter, mem_Icc] at hn
  rw [sharpGoodSet, mem_goodDenominators]
  have hold := mem_goodDenominators.mp hn.1
  exact ⟨hn.2.1, hn.2.2,
    Erdos285.PrimePowers.primePowerSmooth_mono hS hold.2.2.1,
    hold.2.2.2.1, hold.2.2.2.2⟩

lemma eventually_goodSet_subset_oldHigh_union_initial :
    ∀ᶠ N : ℕ in atTop,
      goodSet N ⊆ oldHighSet N ∪ Ico 0 (sharpM N) := by
  filter_upwards [eventually_sourceGoodDenominators_pos] with N hpos
  intro n hn
  by_cases hlow : sharpM N ≤ n
  · exact mem_union_left _ (mem_inter.mpr ⟨hn,
      mem_Icc.mpr ⟨hlow, (mem_goodDenominators.mp hn).2.1⟩⟩)
  · exact mem_union_right _ (mem_Ico.mpr ⟨by
      exact (hpos n hn).le, Nat.lt_of_not_ge hlow⟩)

/-- At most the first `N/100` source denominators are discarded. -/
theorem eventually_sharpGoodSet_card_ge :
    ∀ᶠ N : ℕ in atTop,
      ((87 : ℝ) / 100) * N ≤ (sharpGoodSet N).card := by
  filter_upwards [eventually_sourceGoodDenominators_card_ge,
      eventually_goodSet_subset_oldHigh_union_initial,
      eventually_oldHighSet_subset_sharpGoodSet] with N hcard hcover hsub
  have hcard' : ((89 : ℝ) / 100) * N ≤ (goodSet N).card := by
    simpa [goodSet, sourceGoodDenominators] using hcard
  have hcardNat : (goodSet N).card ≤ (oldHighSet N).card + sharpM N := by
    calc
      (goodSet N).card ≤ (oldHighSet N ∪ Ico 0 (sharpM N)).card :=
        card_le_card hcover
      _ ≤ (oldHighSet N).card + (Ico 0 (sharpM N)).card := card_union_le _ _
      _ = (oldHighSet N).card + sharpM N := by simp
  have hhigh : ((88 : ℝ) / 100) * N ≤ (oldHighSet N).card := by
    have hM : ((sharpM N : ℕ) : ℝ) ≤ (N : ℝ) / 100 := by
      simpa [sharpM] using (Nat.cast_div_le (α := ℝ) (m := N) (n := 100))
    have hcardNat' : ((goodSet N).card : ℝ) ≤
        ((oldHighSet N).card : ℝ) + sharpM N := by exact_mod_cast hcardNat
    linarith
  have hhighSharp : ((oldHighSet N).card : ℝ) ≤ (sharpGoodSet N).card := by
    exact_mod_cast card_le_card hsub
  exact (by linarith : ((87 : ℝ) / 100) * N ≤ (oldHighSet N).card).trans
    hhighSharp

theorem eventually_nineteenTwentiethPower_le_sharpGoodSet_card :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((19 : ℝ) / 20) ≤ ((sharpGoodSet N).card : ℝ) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-((1 : ℝ) / 20)) ≤ (87 / 100 : ℝ) :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_le_const (by norm_num)
  filter_upwards [hsmall, eventually_sharpGoodSet_card_ge,
      eventually_ge_atTop (1 : ℕ)] with N hsmallN hcard hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    (N : ℝ) ^ ((19 : ℝ) / 20) =
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-((1 : ℝ) / 20)) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      norm_num
    _ = (N : ℝ) * (N : ℝ) ^ (-((1 : ℝ) / 20)) := by
      rw [Real.rpow_one]
    _ ≤ (N : ℝ) * (87 / 100 : ℝ) := by gcongr
    _ = ((87 : ℝ) / 100) * N := by ring
    _ ≤ ((sharpGoodSet N).card : ℝ) := hcard

theorem eventually_two_le_sharpGoodSet_reciprocalMass :
    ∀ᶠ N : ℕ in atTop, 2 ≤ reciprocalMass (sharpGoodSet N) := by
  filter_upwards [eventually_sharpGoodSet_card_ge,
      eventually_one_le_sharpM_and_sharpM_le_N,
      eventually_ge_atTop (1000 : ℕ)] with N hcard hM hN
  let A := sharpGoodSet N
  let L := N - A.card + 1
  have hsub : A ⊆ Icc 1 N :=
    (sharpGoodSet_subset_Icc N).trans (Icc_subset_Icc_left hM.1)
  have hcardN : A.card ≤ N := by
    calc A.card ≤ (Icc 1 N).card := card_le_card hsub
      _ = N := by simp
  have hLpos : 0 < L := by simp [L]
  have hLupper : (L : ℝ) ≤ (13 / 100 : ℝ) * N + 1 := by
    dsimp [L]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hcardN]
    linarith
  have hsum : Erdos285.Analytic.terminalReciprocalSum L A.card ≤
      reciprocalMass A := terminalReciprocalSum_le_reciprocalMass A hsub
  have hendpoint : L + A.card = N + 1 := by dsimp [L]; omega
  have hexpTwo : Real.exp 2 < (15 / 2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hexpRatio : Real.exp 2 ≤ (((L + A.card : ℕ) : ℝ) / L) := by
    rw [hendpoint]
    apply (le_div_iff₀ (by exact_mod_cast hLpos)).2
    have hNreal : (1000 : ℝ) ≤ N := by exact_mod_cast hN
    have hmul : Real.exp 2 * (L : ℝ) ≤
        (15 / 2 : ℝ) * ((13 / 100 : ℝ) * N + 1) := by
      calc
        Real.exp 2 * (L : ℝ) ≤
            Real.exp 2 * ((13 / 100 : ℝ) * N + 1) := by gcongr
        _ ≤ (15 / 2 : ℝ) * ((13 / 100 : ℝ) * N + 1) := by gcongr
    push_cast
    nlinarith
  have hlog : 2 ≤ Real.log ((((L + A.card : ℕ) : ℝ) / L)) := by
    rw [← Real.log_exp (2 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 2) hexpRatio
  exact hlog.trans (Erdos285.Analytic.log_div_le_terminalReciprocalSum hLpos)
    |>.trans hsum

theorem eventually_sharpGoodSet_reciprocalMass_le_two_hundred :
    ∀ᶠ N : ℕ in atTop, reciprocalMass (sharpGoodSet N) ≤ 200 := by
  filter_upwards [eventually_ge_atTop (200 : ℕ)] with N hN
  have hMone : 1 ≤ sharpM N := by simp [sharpM]; omega
  have hNM : N ≤ 200 * sharpM N := by simp [sharpM]; omega
  have hmass : reciprocalMass (sharpGoodSet N) ≤
      ((sharpGoodSet N).card : ℝ) / sharpM N := by
    apply reciprocalMass_le_card_div hMone
    intro n hn
    exact (mem_Icc.mp (sharpGoodSet_subset_Icc N hn)).1
  have hcard : (sharpGoodSet N).card ≤ N := by
    calc
      (sharpGoodSet N).card ≤ (Icc (sharpM N) N).card :=
        card_le_card (sharpGoodSet_subset_Icc N)
      _ ≤ N := by simp; omega
  have hMpos : (0 : ℝ) < sharpM N := by exact_mod_cast hMone
  calc
    reciprocalMass (sharpGoodSet N) ≤
        ((sharpGoodSet N).card : ℝ) / sharpM N := hmass
    _ ≤ (N : ℝ) / sharpM N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hMpos.le
    _ ≤ 200 := by
      rw [div_le_iff₀ hMpos]
      exact_mod_cast hNM

end

end Erdos294.SharpDensity
