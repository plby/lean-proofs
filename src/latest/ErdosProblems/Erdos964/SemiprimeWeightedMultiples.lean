import ErdosProblems.Erdos964.SemiprimeWeightedSaving

/-!
# Fixed factors in the progression modulus

The affine sieve produces moduli `m*q` with `m` fixed and `q` squarefree.
The full modulus need not be squarefree. The unweighted distribution
theorem and the squarefree moment in `q` still give every logarithmic saving.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem exists_mul_modulusCutoff_le (m : ℕ) (hm : 0 < m) (θ θ' : ℝ) (hθ : θ < θ') :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧ ∀ L : ℕ, L₀ ≤ L →
      m * modulusCutoff θ L ≤ modulusCutoff θ' L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨L₀, hL₀, hbound⟩ := exists_log_pow_le_mul_rpow_nat 0 (θ' - θ)
    (1 / (m : ℝ)) (sub_pos.mpr hθ) (by positivity)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hmPow : (m : ℝ) ≤ Real.rpow (L : ℝ) (θ' - θ) := by
    have h := hbound L hL
    rw [pow_zero, one_div_mul_eq_div] at h
    exact (one_le_div₀ hmR).mp h
  have hproduct : Real.rpow (L : ℝ) (θ' - θ) * Real.rpow (L : ℝ) θ =
      Real.rpow (L : ℝ) θ' := by
    calc
      _ = Real.rpow (L : ℝ) ((θ' - θ) + θ) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by rw [sub_add_cancel]
  apply Nat.le_floor
  push_cast
  calc
    (m : ℝ) * (modulusCutoff θ L : ℝ) ≤ (m : ℝ) * Real.rpow (L : ℝ) θ :=
      mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg L) θ)) hmR.le
    _ ≤ Real.rpow (L : ℝ) (θ' - θ) * Real.rpow (L : ℝ) θ :=
      mul_le_mul_of_nonneg_right hmPow (Real.rpow_nonneg (Nat.cast_nonneg L) θ)
    _ = _ := hproduct

theorem semiprimeScale_weighted_multiples_cauchy
    (P : Finset ℕ) (L m d : ℕ) (S : Finset ℕ) (hm : 0 < m)
    (hP : ∀ p ∈ P, 0 < p) (hS : S ⊆ Finset.Icc 1 L)
    (hsq : ∀ q ∈ S, Squarefree q) (hcut : ∀ q ∈ S, m * q ≤ L ^ 2) :
    (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleMaxDiscrepancy P L (m * q)) ≤
      Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log L) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L (m * q)) := by
  have hqpos (q : ℕ) (hq : q ∈ S) : 0 < q := (Finset.mem_Icc.mp (hS hq)).1
  have htau : (∑ q ∈ S, (((d ^ ω q : ℕ) : ℝ) ^ 2) / (m * q).totient) ≤
      (1 + Real.log L) ^ (2 * d ^ 2) := by
    apply le_trans _ (sum_tauPow_sq_div_totient_le_one_add_log d L S hS hsq)
    apply Finset.sum_le_sum
    intro q hq
    have hφq : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (hqpos q hq)
    have hφle : (q.totient : ℝ) ≤ (m * q).totient := by
      exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.mul_pos hm (hqpos q hq)))
        (Nat.totient_dvd_of_dvd (dvd_mul_left q m))
    exact div_le_div_of_nonneg_left (sq_nonneg _) hφq hφle
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ)) (fun q => semiprimeScaleMaxDiscrepancy P L (m * q))
    (fun q => ((m * q).totient : ℝ)) (2 * (L : ℝ) ^ 2)
    (fun q _ => semiprimeScaleMaxDiscrepancy_nonneg P L (m * q))
    (fun q hq => semiprimeScaleMaxDiscrepancy_le_two_mul_div P L (m * q) hP
      (Nat.mul_pos hm (hqpos q hq)) (hcut q hq))
  apply hweighted.trans
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htau (by positivity))) (Real.sqrt_nonneg _)

theorem exists_semiprimesAtScale_weighted_multiples_logSaving (a d m : ℕ) (hm : 0 < m)
    (η θ : ℝ) (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ S : Finset ℕ, S ⊆ Finset.Ioc 0 (modulusCutoff θ L) →
        (∀ q ∈ S, Squarefree q) →
      (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleMaxDiscrepancy P L (m * q)) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  classical
  let θ' := (θ + 1) / 2
  have hθθ' : θ < θ' := by dsimp [θ']; linarith
  have hθ'pos : 0 < θ' := hθ.trans hθθ'
  have hθ'one : θ' < 1 := by dsimp [θ']; linarith
  obtain ⟨C, hC, L₁, hL₁, hbound⟩ :=
    exists_semiprimesAtScale_max_logSaving (2 * (a + d ^ 2)) η θ' hη hθ'pos hθ'one
  obtain ⟨L₂, _, hmul⟩ := exists_mul_modulusCutoff_le m hm θ θ' hθθ'
  refine ⟨2 * 2 ^ (d ^ 2) * Real.sqrt C, by positivity, max L₁ L₂,
    hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL P hP hPL hPlower S hS hsq
  have hLbound : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL16 : 16 ≤ L := hL₁.trans hLbound
  have hcut : modulusCutoff θ' L ≤ L := by
    have hreal : (modulusCutoff θ' L : ℝ) ≤ L :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg L) θ')).trans
        (Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ L by omega)) hθ'one.le)
    exact_mod_cast hreal
  have hmulticut : m * modulusCutoff θ L ≤ modulusCutoff θ' L :=
    hmul L ((le_max_right _ _).trans hL)
  have hqcut (q : ℕ) (hq : q ∈ S) : m * q ≤ modulusCutoff θ' L :=
    (Nat.mul_le_mul_left m (Finset.mem_Ioc.mp (hS hq)).2).trans hmulticut
  have hSL : S ⊆ Finset.Icc 1 L := by
    intro q hq
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioc.mp (hS hq)).1,
      (Nat.le_mul_of_pos_left q hm).trans ((hqcut q hq).trans hcut)⟩
  have hsum : (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L (m * q)) ≤
      C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (2 * (a + d ^ 2)) := by
    have himage : S.image (fun q => m * q) ⊆ Finset.Ioc 0 (modulusCutoff θ' L) := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hm (Finset.mem_Ioc.mp (hS ht)).1, hqcut t ht⟩
    have hsumimage : (∑ q ∈ S.image (fun q => m * q), semiprimeScaleMaxDiscrepancy P L q) =
        ∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L (m * q) := by
      apply Finset.sum_image
      intro q _ t _ heq
      exact Nat.eq_of_mul_eq_mul_left hm heq
    rw [← hsumimage]
    exact (Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun q _ _ => semiprimeScaleMaxDiscrepancy_nonneg P L q)).trans
      (hbound L hLbound P hP hPL hPlower)
  have hlogone := one_le_log_natCast (show 4 ≤ L by omega)
  calc
    _ ≤ Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log L) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L (m * q)) :=
      semiprimeScale_weighted_multiples_cauchy P L m d S hm (fun p hp => (hP p hp).pos)
        hSL hsq (fun q hq => ((hqcut q hq).trans hcut).trans (by nlinarith))
    _ ≤ Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log L) ^ (2 * d ^ 2)) *
        Real.sqrt (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (2 * (a + d ^ 2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)
    _ ≤ _ := weighted_semiprime_sqrt_envelope_le hC (Nat.cast_nonneg L)
      (by linarith) (by linarith) (by linarith) a (d ^ 2)

end Erdos964
