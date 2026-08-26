import ErdosProblems.Erdos380.ScaleDivision
import Mathlib.Analysis.PSeries

/-! # Upper bounds for singleton anchors in prime-size bands -/

open Filter
open scoped Topology BigOperators

namespace Erdos380

noncomputable def singletonPrimeBand (N a b : ℕ) : Finset ℕ :=
  (singletonBadUpTo N).filter fun n => a < largestPrimeFactor n ∧ largestPrimeFactor n ≤ b

lemma singletonPrimeBand_card_le_sum (N a b : ℕ) :
    (singletonPrimeBand N a b).card ≤
      ∑ p ∈ Finset.Ioc a b, smoothCount (N / p ^ 2) b := by
  classical
  let S := (Finset.Ioc a b).biUnion fun p =>
    (Nat.smoothNumbersUpTo (N / p ^ 2) (b + 1)).image (fun m => p ^ 2 * m)
  have hsub : singletonPrimeBand N a b ⊆ S := by
    intro n hn
    obtain ⟨hn, hap, hpb⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN, hbad⟩ := mem_singletonBadUpTo.mp hn
    obtain ⟨m, hnm⟩ := hbad.2
    have hp : (largestPrimeFactor n).Prime := largestPrimeFactor_prime (by have := hbad.1; omega)
    have hm0 : m ≠ 0 := by intro hm; simp [hm] at hnm; omega
    have hmb : largestPrimeFactor m ≤ b :=
      (largestPrimeFactor_mono_dvd (by omega : n ≠ 0)
        ⟨largestPrimeFactor n ^ 2, by simpa only [mul_comm] using hnm⟩).trans hpb
    have hmN : m ≤ N / largestPrimeFactor n ^ 2 := by
      apply (Nat.le_div_iff_mul_le (pow_pos hp.pos 2)).mpr
      calc
        m * largestPrimeFactor n ^ 2 = largestPrimeFactor n ^ 2 * m := Nat.mul_comm _ _
        _ = n := hnm.symm
        _ ≤ N := hnN
    apply Finset.mem_biUnion.mpr
    refine ⟨largestPrimeFactor n, Finset.mem_Ioc.mpr ⟨hap, hpb⟩, Finset.mem_image.mpr ⟨m, ?_, hnm.symm⟩⟩
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨hmN,
      (mem_smoothNumbers_iff_largestPrimeFactor (hp.one_le.trans hpb)).mpr ⟨hm0, hmb⟩⟩
  calc
    _ ≤ S.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.Ioc a b,
        ((Nat.smoothNumbersUpTo (N / p ^ 2) (b + 1)).image (fun m => p ^ 2 * m)).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun p _ => Finset.card_image_le)

lemma singletonPrimeBand_card_bound {N a b : ℕ} {F : ℝ} (ha : 1 ≤ a) (hF : 0 < F)
    (hbound : ∀ p ∈ Finset.Ioc a b,
      (smoothCount (N / p ^ 2) b : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ 2 / F) :
    ((singletonPrimeBand N a b).card : ℝ) ≤ 2 * N / a / F := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hsum : (∑ p ∈ Finset.Ioc a b, ((p : ℝ) ^ 2)⁻¹) ≤ 2 / (a : ℝ) := by
    have hset : Finset.Ioc a b = Finset.Ioo a (b + 1) := by
      ext p
      simp only [Finset.mem_Ioc, Finset.mem_Ioo]
      omega
    rw [hset]
    exact (sum_Ioo_inv_sq_le (α := ℝ) a (b + 1)).trans
      (div_le_div_of_nonneg_left (by norm_num) haR (by linarith))
  calc
    ((singletonPrimeBand N a b).card : ℝ) ≤ ∑ p ∈ Finset.Ioc a b, (smoothCount (N / p ^ 2) b : ℝ) := by
      exact_mod_cast singletonPrimeBand_card_le_sum N a b
    _ ≤ ∑ p ∈ Finset.Ioc a b, (N : ℝ) / (p : ℝ) ^ 2 / F := Finset.sum_le_sum hbound
    _ = ((N : ℝ) / F) * ∑ p ∈ Finset.Ioc a b, ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ((N : ℝ) / F) * (2 / a) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem eventually_singletonPrimeBand_scale_bound (j r : ℕ)
    (hjr : (j + 1) * r < 1000000) : ∀ᶠ N : ℕ in atTop,
    ((singletonPrimeBand N (scaleBase N ^ j) (scaleBase N ^ (j + 1))).card : ℝ) ≤
      2 * N / (scaleBase N : ℝ) ^ (j + r) := by
  filter_upwards [eventually_smoothCount_div_scale_upper (Nat.succ_pos j) hjr (2 * (j + 1))]
    with N hbound
  have hS1 := one_le_scaleBase N
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast (by omega : 0 < scaleBase N)
  have h := singletonPrimeBand_card_bound (N := N) (a := scaleBase N ^ j)
    (b := scaleBase N ^ (j + 1)) (F := (scaleBase N : ℝ) ^ r)
    (one_le_pow₀ hS1) (pow_pos hSpos r) ?_
  · simpa only [Nat.cast_pow, div_div, ← pow_add] using h
  · intro p hp
    obtain ⟨hap, hpb⟩ := Finset.mem_Ioc.mp hp
    have hp0 : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hap
    have hpsize : p ^ 2 ≤ scaleBase N ^ (2 * (j + 1)) := by
      calc
        p ^ 2 ≤ (scaleBase N ^ (j + 1)) ^ 2 := Nat.pow_le_pow_left hpb 2
        _ = _ := by rw [← pow_mul, Nat.mul_comm (j + 1) 2]
    have hh := hbound (p ^ 2) (pow_pos hp0 2) hpsize
    simpa only [Nat.cast_pow] using hh

end Erdos380
