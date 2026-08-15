/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SubpowerAnalytic

/-!
# The large-component estimate on the subpower scale

This module assembles the localized switched-class sieve with the odd/even
logarithmic Brun depths.  All three normalized contributions (reciprocal
main term, certificate count, and certificate-times-CRT endpoint) tend to
zero.
-/

namespace Erdos387

open Filter
open scoped Topology

namespace SubpowerScale

theorem tendsto_refinedLargeErrors_normalized_zero
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N : ℕ =>
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) /
        ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p))) atTop (𝓝 0) := by
  obtain ⟨Cπ, hCπ, hcheb⟩ :=
    PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨a, b, hdepth⟩ :=
    CoverBPZ.exists_refined_tail_and_euler_reciprocal_depth hCπ hcheb S
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  let R : ℕ → ℝ := fun N =>
    CoverBPZ.localizedSwitchedReciprocalEnvelope S Cπ
      (X N S.k) (z N S.k) (large N S.k)
  let Ccert : ℕ → ℝ := fun N =>
    CoverBPZ.switchedCertificateCountEnvelope S
      (X N S.k) (z N S.k) (large N S.k)
  let Eeven : ℕ → ℝ := fun N =>
    (4 : ℝ) *
      (z N S.k ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k) + 1 : ℕ) *
      (S.k : ℝ) ^ CoverBPZ.refinedEvenBrunDepth a b (z N S.k)
  let Q : ℕ → ℝ := fun N =>
    (3 / 2 : ℝ) * R N + 3 * (Ccert N / X N S.k) +
      (Ccert N / X N S.k) * Eeven N *
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)
  have hR0 : Tendsto R atTop (𝓝 0) := by
    simpa [R] using tendsto_localizedSwitchedReciprocalEnvelope_zero
      hCπ S hB
  have hC0 : Tendsto (fun N => Ccert N / X N S.k) atTop (𝓝 0) := by
    simpa [Ccert] using
      tendsto_switchedCertificateCountEnvelope_div_X_zero S hB
  have hendpoint0 : Tendsto (fun N =>
      (Ccert N / X N S.k) * Eeven N *
        (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k))
      atTop (𝓝 0) := by
    simpa [Ccert, Eeven, mul_assoc] using
      tendsto_certificateBrunEndpoint_normalized_zero S hB a b
  have hQ0 : Tendsto Q atTop (𝓝 0) := by
    dsimp [Q]
    convert ((tendsto_const_nhds.mul hR0).add
      (tendsto_const_nhds.mul hC0)).add hendpoint0 using 1 <;> norm_num
  let gmax : ℕ := (Finset.univ : Finset (Fin S.k)).sup (fun i => 6 * S.g i)
  have hgEv : ∀ᶠ N : ℕ in atTop, ∀ i : Fin S.k, 6 * S.g i ≤ z N S.k := by
    filter_upwards [eventually_const_le_z (k := S.k)
      (by have := S.hk3; omega) gmax]
      with N hN
    intro i
    exact (Finset.le_sup (f := fun i : Fin S.k => 6 * S.g i)
      (Finset.mem_univ i)).trans hN
  have hzEv : ∀ᶠ N : ℕ in atTop, 2 * S.k ≤ z N S.k :=
    eventually_const_le_z (k := S.k) (by have := S.hk3; omega) (2 * S.k)
  have hXEv : ∀ᶠ N : ℕ in atTop, 6 * S.k ≤ X N S.k :=
    eventually_const_le_X (k := S.k) (by have := S.hk3; omega) (6 * S.k)
  have hfinite : ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) /
          ((X N S.k : ℝ) * V N) ≤ Q N := by
    filter_upwards [hgEv, hzEv, hXEv, eventually_ge_atTop (1 : ℕ)] with
      N hzg hz2k hXwide hN
    have hNpos : 0 < N := by omega
    have hk : 0 < S.k := by have := S.hk3; omega
    have hzTwo : 2 ≤ z N S.k := (show 2 ≤ 2 * S.k by omega).trans hz2k
    have hscale := large_switch_square_scale S.hk3 (by omega : 1 ≤ N)
    have hXhalf : S.k ≤ X N S.k / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      simpa [mul_comm] using
        (show 2 * S.k ≤ 6 * S.k by omega).trans hXwide
    have htailEven := (hdepth (z N S.k)).2.1
    have hwindow := boundingSieve_brunMainSums_half_threeHalves
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
      (CoverBPZ.refinedEvenBrunDepth a b (z N S.k)) htailEven
    have hVpos : 0 < V N := by
      have hv := boundingSieve_finiteEulerProduct_pos
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
      simpa [V, refinedBinomialBoundingSieve] using hv
    have hmainNonneg : 0 ≤
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
          (brunUpperWeight
            (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) := by
      change 0 ≤
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
          (brunLowerWeight
            (CoverBPZ.refinedEvenBrunDepth a b (z N S.k)))
      have hlower := hwindow.1
      have hVnonneg : 0 ≤ V N := hVpos.le
      change V N / 2 ≤ _ at hlower
      linarith
    have hlarge := CoverBPZ.refinedLargeErrors_card_le_brun_localized_endpoint
      (C := Cπ) (N := 2) S hCπ hcheb (by omega) hzTwo hB hzg hz2k
      hXwide hscale hXhalf (CoverBPZ.refinedEvenBrunDepth_even a b _)
      hmainNonneg
    have hmainUpper :
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
            (brunUpperWeight
              (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) ≤
          3 * V N / 2 := by
      simpa [V, refinedBinomialBoundingSieve] using hwindow.2
    have hEulerRecip := (hdepth (z N S.k)).2.2
    change 1 ≤ (2 : ℝ) ^
      PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) * V N at hEulerRecip
    let A0 : ℝ := ((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
      CoverBPZ.refinementModulus S
    have hA0nonneg : 0 ≤ A0 := by dsimp [A0]; positivity
    have hMpos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
      exact_mod_cast CoverBPZ.refinementModulus_pos S
    have hMone : (1 : ℝ) ≤ CoverBPZ.refinementModulus S := by
      exact_mod_cast CoverBPZ.refinementModulus_pos S
    have hA0X : A0 ≤ X N S.k := by
      dsimp [A0]
      rw [div_le_iff₀ hMpos]
      have hsub : ((X N S.k - X N S.k / 2 : ℕ) : ℝ) ≤ X N S.k := by
        exact_mod_cast Nat.sub_le (X N S.k) (X N S.k / 2)
      exact hsub.trans (by
        calc
          (X N S.k : ℝ) = (X N S.k : ℝ) * 1 := by ring
          _ ≤ (X N S.k : ℝ) * CoverBPZ.refinementModulus S := by gcongr)
    have hzLog : 0 < Real.log (z N S.k : ℝ) :=
      Real.log_pos (by exact_mod_cast hzTwo)
    have hRnonneg : 0 ≤ R N := by
      exact localizedSwitchedReciprocalEnvelope_nonneg S hCπ.le hzLog.le
    have hCcertNonneg : 0 ≤ Ccert N :=
      switchedCertificateCountEnvelope_nonneg S _ _ _
    have hEevenNonneg : 0 ≤ Eeven N :=
      refinedEvenEndpoint_nonneg a b (z N S.k) S.k
    have hcoefNonneg : 0 ≤ A0 * R N + 2 * Ccert N :=
      add_nonneg (mul_nonneg hA0nonneg hRnonneg)
        (mul_nonneg (by norm_num) hCcertNonneg)
    have hXrealPos : (0 : ℝ) < X N S.k := by exact_mod_cast X_pos N S.k
    have hdenPos : 0 < (X N S.k : ℝ) * V N := mul_pos hXrealPos hVpos
    rw [div_le_iff₀ hdenPos]
    change ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
      (large N S.k)).card : ℝ) ≤ _
    calc
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) ≤
          ((A0 * R N + 2 * Ccert N) *
              (refinedBinomialBoundingSieve S (X N S.k) (z N S.k)).mainSum
                (brunUpperWeight
                  (CoverBPZ.refinedEvenBrunDepth a b (z N S.k))) +
            Ccert N * Eeven N) := by
        simpa [A0, R, Ccert, Eeven] using hlarge
      _ ≤ (A0 * R N + 2 * Ccert N) * (3 * V N / 2) +
            Ccert N * Eeven N := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_left hmainUpper hcoefNonneg)
          (Ccert N * Eeven N)
      _ ≤ ((X N S.k : ℝ) * R N + 2 * Ccert N) * (3 * V N / 2) +
            Ccert N * Eeven N := by
        have hcoefLe : A0 * R N + 2 * Ccert N ≤
            (X N S.k : ℝ) * R N + 2 * Ccert N :=
          add_le_add_left (mul_le_mul_of_nonneg_right hA0X hRnonneg)
            (2 * Ccert N)
        have hVfactorNonneg : 0 ≤ 3 * V N / 2 := by positivity
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right hcoefLe hVfactorNonneg)
          (Ccert N * Eeven N)
      _ ≤ ((X N S.k : ℝ) * R N + 2 * Ccert N) * (3 * V N / 2) +
            Ccert N * Eeven N *
              ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) *
                V N) := by
        have hendpointNonneg : 0 ≤ Ccert N * Eeven N :=
          mul_nonneg hCcertNonneg hEevenNonneg
        exact add_le_add_right
          (calc
            Ccert N * Eeven N = (Ccert N * Eeven N) * 1 := by ring
            _ ≤ (Ccert N * Eeven N) *
                ((2 : ℝ) ^
                    PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) * V N) :=
              mul_le_mul_of_nonneg_left hEulerRecip hendpointNonneg)
          (((X N S.k : ℝ) * R N + 2 * Ccert N) * (3 * V N / 2))
      _ = Q N * ((X N S.k : ℝ) * V N) := by
        dsimp [Q]
        field_simp
  apply squeeze_zero' (g := Q)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hVpos : 0 < V N := by
      have hv := boundingSieve_finiteEulerProduct_pos
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
      simpa [V, refinedBinomialBoundingSieve] using hv
    positivity
  · exact hfinite
  · exact hQ0

end SubpowerScale

end Erdos387
