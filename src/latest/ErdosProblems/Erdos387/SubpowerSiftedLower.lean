/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SubpowerLargeError

/-!
# The lower sifted density on the subpower scale

This module combines the odd logarithmic Brun truncation with the same Euler
reciprocal envelope used by the large-error estimate.  The CRT remainder is
negligible, so the refined sifted set eventually contains a fixed positive
multiple of its natural scale `X * V`.  Consequently the already-normalized
large exceptional set is eventually strictly smaller than the sifted set.
-/

namespace Erdos387

open Filter
open scoped Topology

namespace SubpowerScale

theorem eventually_refinedSiftedCandidates_card_ge_scale
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p)) /
          (16 * CoverBPZ.refinementModulus S : ℝ) ≤
        ((RefinedSiftedCandidates S (X N S.k) (z N S.k)).card : ℝ) := by
  obtain ⟨Cπ, hCπ, hcheb⟩ :=
    PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨a, b, hdepth⟩ :=
    CoverBPZ.exists_refined_tail_and_euler_reciprocal_depth hCπ hcheb S
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  let E : ℕ → ℝ := fun N =>
    (4 : ℝ) *
      (z N S.k ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) + 1 : ℕ) *
      (S.k : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)
  have hE0 : Tendsto (fun N : ℕ =>
      (E N *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) /
        X N S.k) atTop (𝓝 0) := by
    simpa [E, mul_assoc] using
      tendsto_lowerBrunError_eulerNormalized_zero S a b
  have hMposNat : 0 < CoverBPZ.refinementModulus S :=
    CoverBPZ.refinementModulus_pos S
  have hMpos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast hMposNat
  have hEsmall : ∀ᶠ N : ℕ in atTop,
      (E N *
          (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) /
          X N S.k <
        1 / (16 * CoverBPZ.refinementModulus S : ℝ) :=
    (tendsto_order.1 hE0).2 _ (by positivity)
  have hXmod : ∀ᶠ N : ℕ in atTop,
      8 * CoverBPZ.refinementModulus S ≤ X N S.k :=
    eventually_const_le_X (k := S.k) (by have := S.hk3; omega)
      (8 * CoverBPZ.refinementModulus S)
  have hXk : ∀ᶠ N : ℕ in atTop, 2 * S.k ≤ X N S.k :=
    eventually_const_le_X (k := S.k) (by have := S.hk3; omega) (2 * S.k)
  filter_upwards [hEsmall, hXmod, hXk, eventually_ge_atTop (1 : ℕ)] with
    N hsmall hXmodN hXkN hN
  have hNpos : 0 < N := by omega
  have hk : 0 < S.k := by have := S.hk3; omega
  have hzTwo : 2 ≤ z N S.k := two_le_z hNpos hk
  have hXhalf : S.k ≤ X N S.k / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [mul_comm] using hXkN
  have hVpos : 0 < V N := by
    have hv := boundingSieve_finiteEulerProduct_pos
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    simpa [V, refinedBinomialBoundingSieve] using hv
  have hXrealPos : (0 : ℝ) < X N S.k := by
    exact_mod_cast X_pos N S.k
  have hEnonneg : 0 ≤ E N := by
    exact brunEndpointTerm_nonneg (z N S.k) S.k _
  have hEulerRecip := (hdepth (z N S.k)).2.2
  change 1 ≤ (2 : ℝ) ^
    PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) * V N at hEulerRecip
  have hEX :
      E N * (2 : ℝ) ^
          PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) <
        (X N S.k : ℝ) / (16 * CoverBPZ.refinementModulus S) := by
    rw [div_lt_iff₀ hXrealPos] at hsmall
    calc
      E N * (2 : ℝ) ^
          PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) <
          (1 / (16 * CoverBPZ.refinementModulus S : ℝ)) * X N S.k := hsmall
      _ = (X N S.k : ℝ) / (16 * CoverBPZ.refinementModulus S) := by ring
  have hEbound :
      E N ≤ (X N S.k : ℝ) * V N /
        (16 * CoverBPZ.refinementModulus S) := by
    exact (calc
        E N = E N * 1 := by ring
        _ ≤ E N *
            ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) *
              V N) := mul_le_mul_of_nonneg_left hEulerRecip hEnonneg
        _ = (E N * (2 : ℝ) ^
            PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) * V N := by ring
        _ < ((X N S.k : ℝ) / (16 * CoverBPZ.refinementModulus S)) * V N :=
          mul_lt_mul_of_pos_right hEX hVpos
        _ = (X N S.k : ℝ) * V N /
            (16 * CoverBPZ.refinementModulus S) := by ring).le
  have hXeven : 2 ∣ X N S.k := by
    rw [X_eq_pow_two]
    exact dvd_pow_self 2 (by
      have hx : 0 < BPZScale.xExp S.k := by
        unfold BPZScale.xExp
        positivity
      positivity)
  have hhalfMul : X N S.k / 2 * 2 = X N S.k :=
    Nat.div_mul_cancel hXeven
  have hsubHalf : X N S.k - X N S.k / 2 = X N S.k / 2 := by omega
  have hhalfReal :
      ((X N S.k - X N S.k / 2 : ℕ) : ℝ) = (X N S.k : ℝ) / 2 := by
    rw [hsubHalf]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    exact_mod_cast hhalfMul
  have hXmodReal :
      (8 : ℝ) * CoverBPZ.refinementModulus S ≤ X N S.k := by
    exact_mod_cast hXmodN
  have hprefactor :
      (X N S.k : ℝ) / (4 * CoverBPZ.refinementModulus S) ≤
        ((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
            CoverBPZ.refinementModulus S - 2 := by
    rw [hhalfReal]
    field_simp
    linarith
  have hmain :
      (X N S.k : ℝ) * V N / (8 * CoverBPZ.refinementModulus S) ≤
        (((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
            CoverBPZ.refinementModulus S - 2) * (V N / 2) := by
    calc
      (X N S.k : ℝ) * V N / (8 * CoverBPZ.refinementModulus S) =
          ((X N S.k : ℝ) / (4 * CoverBPZ.refinementModulus S)) *
            (V N / 2) := by ring
      _ ≤ (((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
            CoverBPZ.refinementModulus S - 2) * (V N / 2) :=
        mul_le_mul_of_nonneg_right hprefactor (by positivity)
  have hlower := CoverBPZ.refinedSiftedCandidates_card_lowerBound_density
    S hXhalf (by omega : 1 ≤ z N S.k)
    (PrimeReciprocal.logarithmicBrunDepth_odd a b (z N S.k))
    (hdepth (z N S.k)).1
  change ((((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
      CoverBPZ.refinementModulus S - 2) * (V N / 2) - E N) ≤
    ((RefinedSiftedCandidates S (X N S.k) (z N S.k)).card : ℝ) at hlower
  calc
    (X N S.k : ℝ) * V N / (16 * CoverBPZ.refinementModulus S) ≤
        (X N S.k : ℝ) * V N / (8 * CoverBPZ.refinementModulus S) - E N := by
      have hdouble :
          (X N S.k : ℝ) * V N / (8 * CoverBPZ.refinementModulus S) =
            2 * ((X N S.k : ℝ) * V N /
              (16 * CoverBPZ.refinementModulus S)) := by ring
      rw [hdouble]
      linarith
    _ ≤ (((X N S.k - X N S.k / 2 : ℕ) : ℝ) /
          CoverBPZ.refinementModulus S - 2) * (V N / 2) - E N :=
      sub_le_sub_right hmain (E N)
    _ ≤ ((RefinedSiftedCandidates S (X N S.k) (z N S.k)).card : ℝ) :=
      hlower

theorem eventually_refinedLargeErrors_card_lt_refinedSiftedCandidates
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      (CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card <
        (RefinedSiftedCandidates S (X N S.k) (z N S.k)).card := by
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  have hlarge0 := tendsto_refinedLargeErrors_normalized_zero S hB
  have hMpos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hlargeSmall : ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) /
          ((X N S.k : ℝ) * V N) <
        1 / (32 * CoverBPZ.refinementModulus S : ℝ) := by
    simpa [V] using (tendsto_order.1 hlarge0).2
      (1 / (32 * CoverBPZ.refinementModulus S : ℝ)) (by positivity)
  have hlower := eventually_refinedSiftedCandidates_card_ge_scale S
  filter_upwards [hlargeSmall, hlower] with N hsmall hsifted
  have hVpos : 0 < V N := by
    have hv := boundingSieve_finiteEulerProduct_pos
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    simpa [V, refinedBinomialBoundingSieve] using hv
  have hXrealPos : (0 : ℝ) < X N S.k := by
    exact_mod_cast X_pos N S.k
  have hdenPos : 0 < (X N S.k : ℝ) * V N :=
    mul_pos hXrealPos hVpos
  have hlargeBound :
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) <
        (X N S.k : ℝ) * V N /
          (32 * CoverBPZ.refinementModulus S) := by
    rw [div_lt_iff₀ hdenPos] at hsmall
    calc
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) <
          (1 / (32 * CoverBPZ.refinementModulus S : ℝ)) *
            ((X N S.k : ℝ) * V N) := hsmall
      _ = (X N S.k : ℝ) * V N /
          (32 * CoverBPZ.refinementModulus S) := by ring
  have hscaleStrict :
      (X N S.k : ℝ) * V N / (32 * CoverBPZ.refinementModulus S) <
        (X N S.k : ℝ) * V N / (16 * CoverBPZ.refinementModulus S) := by
    have hXV : 0 < (X N S.k : ℝ) * V N := mul_pos hXrealPos hVpos
    apply div_lt_div_of_pos_left hXV (by positivity)
    nlinarith
  have hreal :
      ((CoverBPZ.RefinedLargeErrors S (X N S.k) (z N S.k)
          (large N S.k)).card : ℝ) <
        ((RefinedSiftedCandidates S (X N S.k) (z N S.k)).card : ℝ) :=
    hlargeBound.trans (hscaleStrict.trans_le (by simpa [V] using hsifted))
  exact_mod_cast hreal

end SubpowerScale

end Erdos387
