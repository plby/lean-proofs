import ErdosProblems.Erdos964.SemiprimeWeightedMultiples
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy
import BoundedGaps.BombieriVinogradov.Analytic.PrimeLevelCutoff

/-!
# Weighted prime distribution with a fixed modulus factor

The variable part of the modulus is squarefree; its fixed multiplier need
not be. Cauchy's inequality and the unconditional prime level give every
logarithmic saving below level one half.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem weighted_prime_sqrt_envelope_le {C X l t : ℝ}
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hl : 0 < l) (ht : 0 ≤ t) (htl : t ≤ 2 * l)
    (a k : ℕ) :
    Real.sqrt (6 * X * t ^ (2 * k)) *
        Real.sqrt (C * X / l ^ (2 * (a + k))) ≤
      (6 * 2 ^ k * Real.sqrt C) * X / l ^ a := by
  have hbase := weighted_semiprime_sqrt_envelope_le hC (Real.sqrt_nonneg X)
    hl ht htl a k
  rw [Real.sq_sqrt hX] at hbase
  have hid : 6 * X * t ^ (2 * k) = 3 * (2 * X * t ^ (2 * k)) := by ring
  rw [hid, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), mul_assoc]
  have hthree : Real.sqrt 3 ≤ (3 : ℝ) :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  calc
    _ ≤ 3 * (Real.sqrt (2 * X * t ^ (2 * k)) *
        Real.sqrt (C * X / l ^ (2 * (a + k)))) :=
      mul_le_mul_of_nonneg_right hthree (by positivity)
    _ ≤ 3 * ((2 * 2 ^ k * Real.sqrt C) * X / l ^ a) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = _ := by ring

theorem prime_weighted_multiples_cauchy (x m d : ℕ) (hx : 1 ≤ x) (hm : 0 < m)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 x) (hsq : ∀ q ∈ S, Squarefree q)
    (hcut : ∀ q ∈ S, m * q ≤ x) :
    (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy x (m * q)) ≤
      Real.sqrt (6 * (x : ℝ) * (1 + Real.log x) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, maxProgressionDiscrepancy x (m * q)) := by
  have hqpos (q : ℕ) (hq : q ∈ S) : 0 < q := (Finset.mem_Icc.mp (hS hq)).1
  have htau : (∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) ^ 2) / (m * q).totient) ≤
      (1 + Real.log x) ^ (2 * d ^ 2) := by
    apply le_trans _ (sum_tauPow_sq_div_totient_le_one_add_log d x S hS hsq)
    apply Finset.sum_le_sum
    intro q hq
    have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (hqpos q hq)
    have hφle : (q.totient : ℝ) ≤ (m * q).totient := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.mul_pos hm (hqpos q hq)))
        (Nat.totient_dvd_of_dvd (dvd_mul_left q m))
    exact div_le_div_of_nonneg_left (sq_nonneg _) hφq hφle
  have htriv (q : ℕ) (hq : q ∈ S) :
      maxProgressionDiscrepancy x (m * q) ≤ 6 * (x : ℝ) / (m * q).totient := by
    apply (maxProgressionDiscrepancy_le_three_mul_div (Nat.mul_pos hm (hqpos q hq))
      ((hcut q hq).trans (Nat.le_succ x))).trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
    push_cast
    linarith
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ)) (fun q => maxProgressionDiscrepancy x (m * q))
    (fun q => ((m * q).totient : ℝ)) (6 * (x : ℝ))
    (fun q _ => maxProgressionDiscrepancy_nonneg x (m * q)) htriv
  apply hweighted.trans
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htau (by positivity))) (Real.sqrt_nonneg _)

theorem exists_prime_weighted_multiples_logSaving (a d m : ℕ) (hm : 0 < m)
    (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x → ∀ S : Finset ℕ,
        S ⊆ Finset.Ioc 0 (modulusCutoff θ x) → (∀ q ∈ S, Squarefree q) →
      (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy x (m * q)) ≤
        C * (x : ℝ) / (Real.log (x : ℝ)) ^ a := by
  let θ' := (θ + 1 / 2) / 2
  have hθθ' : θ < θ' := by dsimp [θ']; linarith
  have hθ'half : θ' < 1 / 2 := by dsimp [θ']; linarith
  let b := 2 * (a + d ^ 2 + 1)
  have hb : (0 : ℝ) < b := by dsimp [b]; positivity
  obtain ⟨C, hC, X₁, hX₁, hbound⟩ := hasPrimeLevel_of_lt_half hθ'half (b : ℝ) hb
  obtain ⟨X₂, hX₂, hmul⟩ := exists_mul_modulusCutoff_le m hm θ θ' hθθ'
  refine ⟨6 * 2 ^ (d ^ 2) * Real.sqrt C, by positivity, max X₁ X₂,
    hX₂.trans (le_max_right _ _), ?_⟩
  intro x hx S hS hsq
  have hx4 : 4 ≤ x := hX₂.trans ((le_max_right _ _).trans hx)
  have hcut : modulusCutoff θ' x ≤ x := by
    have hreal : (modulusCutoff θ' x : ℝ) ≤ x :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) θ')).trans
        (Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ x by omega))
          (by linarith : θ' ≤ 1))
    exact_mod_cast hreal
  have hmulticut := hmul x ((le_max_right _ _).trans hx)
  have hqcut (q : ℕ) (hq : q ∈ S) : m * q ≤ modulusCutoff θ' x :=
    (Nat.mul_le_mul_left m (Finset.mem_Ioc.mp (hS hq)).2).trans hmulticut
  have hSx : S ⊆ Finset.Icc 1 x := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp (hS hq)).1,
      (Nat.le_mul_of_pos_left q hm).trans ((hqcut q hq).trans hcut)⟩
  have hsum : (∑ q ∈ S, maxProgressionDiscrepancy x (m * q)) ≤
      C * (x : ℝ) / (Real.log (x : ℝ)) ^ b := by
    have himage : S.image (fun q => m * q) ⊆ Finset.Icc 1 (modulusCutoff θ' x) := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hm (Finset.mem_Ioc.mp (hS ht)).1, hqcut t ht⟩
    have hsumimage : (∑ q ∈ S.image (fun q => m * q), maxProgressionDiscrepancy x q) =
        ∑ q ∈ S, maxProgressionDiscrepancy x (m * q) := by
      apply Finset.sum_image
      intro q _ t _ heq
      exact Nat.eq_of_mul_eq_mul_left hm heq
    rw [← hsumimage]
    have h := (Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun q _ _ => maxProgressionDiscrepancy_nonneg x q)).trans
      (hbound x ((le_max_left _ _).trans hx))
    change (∑ q ∈ S.image (fun q => m * q), maxProgressionDiscrepancy x q) ≤
      C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) (b : ℝ) at h
    rw [Real.rpow_eq_pow, Real.rpow_natCast] at h
    exact h
  have hlogone := one_le_log_natCast hx4
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hpow : (Real.log (x : ℝ)) ^ (2 * (a + d ^ 2)) ≤ (Real.log (x : ℝ)) ^ b := by
    apply pow_le_pow_right₀ hlogone
    dsimp [b]
    omega
  have hsum' : (∑ q ∈ S, maxProgressionDiscrepancy x (m * q)) ≤
      C * (x : ℝ) / (Real.log (x : ℝ)) ^ (2 * (a + d ^ 2)) :=
    hsum.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
  calc
    _ ≤ Real.sqrt (6 * (x : ℝ) * (1 + Real.log x) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, maxProgressionDiscrepancy x (m * q)) :=
      prime_weighted_multiples_cauchy x m d (by omega) hm S hSx hsq
        (fun q hq => (hqcut q hq).trans hcut)
    _ ≤ Real.sqrt (6 * (x : ℝ) * (1 + Real.log x) ^ (2 * d ^ 2)) *
        Real.sqrt (C * (x : ℝ) / (Real.log (x : ℝ)) ^ (2 * (a + d ^ 2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum') (Real.sqrt_nonneg _)
    _ ≤ _ := weighted_prime_sqrt_envelope_le hC (Nat.cast_nonneg x) hlogpos
      (by linarith) (by linarith) a (d ^ 2)

end Erdos964
