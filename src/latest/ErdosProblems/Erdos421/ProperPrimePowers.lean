import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Prod

/-! # An elementary count of proper prime powers -/

namespace Erdos421

noncomputable def properPrimePowers (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter (fun n ↦ IsPrimePow n ∧ ¬n.Prime)

theorem properPrimePowers_representation {B n : ℕ} (hn : n ∈ properPrimePowers B) :
    ∃ p k : ℕ, p ≤ Nat.sqrt B ∧ k ≤ Nat.log 2 B ∧ p ^ k = n := by
  classical
  obtain ⟨hnB, hpp, hnp⟩ := Finset.mem_filter.mp hn
  have hnle : n ≤ B := by have := Finset.mem_range.mp hnB; omega
  obtain ⟨p, k, hp, hk, hpk⟩ := hpp
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    rw [hk1, pow_one] at hpk
    exact hnp (hpk ▸ hp')
  have hpsq : p ^ 2 ≤ B :=
    (Nat.pow_le_pow_right hp'.pos hk2).trans (hpk ▸ hnle)
  have htwo : 2 ^ k ≤ B := (Nat.pow_le_pow_left hp'.two_le k).trans (hpk ▸ hnle)
  exact ⟨p, k, Nat.le_sqrt'.mpr hpsq, Nat.le_log_of_pow_le (by omega) htwo, hpk⟩

theorem properPrimePowers_card_le (B : ℕ) :
    (properPrimePowers B).card ≤ (Nat.sqrt B + 1) * (Nat.log 2 B + 1) := by
  classical
  let S := (Finset.range (Nat.sqrt B + 1)) ×ˢ (Finset.range (Nat.log 2 B + 1))
  have hsub : properPrimePowers B ⊆ S.image (fun a : ℕ × ℕ ↦ a.1 ^ a.2) := by
    intro n hn
    obtain ⟨p, k, hp, hk, hpk⟩ := properPrimePowers_representation hn
    exact Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hpk⟩
  exact (Finset.card_le_card hsub).trans
    (by simpa only [S, Finset.card_product, Finset.card_range] using
      (Finset.card_image_le (s := S) (f := fun a : ℕ × ℕ ↦ a.1 ^ a.2)))

theorem natSqrt_cast_le_sqrt (B : ℕ) : (Nat.sqrt B : ℝ) ≤ Real.sqrt B := by
  have hsq : (Nat.sqrt B : ℝ) ^ 2 ≤ (B : ℝ) := by exact_mod_cast Nat.sqrt_le' B
  exact (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hsq

theorem properPrimePowers_card_real_bound (B : ℕ) :
    ((properPrimePowers B).card : ℝ) ≤
      (Real.sqrt B + 1) * (Real.log B / Real.log 2 + 1) := by
  have hc : ((properPrimePowers B).card : ℝ) ≤
      ((Nat.sqrt B : ℝ) + 1) * ((Nat.log 2 B : ℝ) + 1) := by
    exact_mod_cast properPrimePowers_card_le B
  have hlog : (Nat.log 2 B : ℝ) ≤ Real.log B / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat] using Real.natLog_le_logb B 2
  exact hc.trans (mul_le_mul (add_le_add (natSqrt_cast_le_sqrt B) le_rfl)
    (add_le_add hlog le_rfl) (by positivity) (by positivity))

end Erdos421
