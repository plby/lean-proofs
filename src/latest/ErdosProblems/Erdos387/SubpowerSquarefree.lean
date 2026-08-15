/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SquarefreeCandidates
import ErdosProblems.Erdos387.SubpowerSiftedLower

/-!
# The squarefree restriction has zero normalized density

On the subpower scale the prime-square union bound is much smaller than the
Brun-sieve main scale.  This permits all subsequent variable Kloosterman
moduli to be squarefree; fixed factors of the progression modulus may then be
absorbed into constants.
-/

namespace Erdos387

open Filter
open scoped Topology

namespace SubpowerScale

theorem z_sq_le_X {N k : ℕ} (hN : 2 ≤ N) :
    z N k ^ 2 ≤ X N k := by
  rw [X_eq_pow_two]
  unfold z
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  unfold roughPower
  have hN2 : 2 ≤ N ^ 2 := by nlinarith
  calc
    BPZScale.xExp k * N ^ (2 * k + 3) * 2 ≤
        BPZScale.xExp k * N ^ (2 * k + 3) * N ^ 2 := by gcongr
    _ = BPZScale.xExp k * N ^ (2 * k + 5) := by
      rw [show N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 by
        simpa using pow_add N (2 * k + 3) 2]
      ring

theorem eventually_depth_add_le_roughPower
    (a b k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop,
      PrimeReciprocal.logarithmicBrunDepth a b (z N k) + N ≤
        roughPower N k := by
  filter_upwards [eventually_ge_atTop
      (max 2 (2 * (depthSlope a b k + 1) + 1))] with N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hdepthArg : 2 * (depthSlope a b k + 1) + 1 ≤ N :=
    (le_max_right _ _).trans hN
  have hdepth := logarithmicBrunDepth_succ_le_square hdepthArg
  have hsum : N ^ 2 + N ≤ N ^ 3 := by nlinarith
  have hpow : N ^ 3 ≤ N ^ (2 * k + 3) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hcoef : N ^ (2 * k + 3) ≤ roughPower N k := by
    unfold roughPower
    have hx : 0 < BPZScale.xExp k := by
      unfold BPZScale.xExp
      positivity
    simpa [mul_comm] using
      Nat.le_mul_of_pos_left (N ^ (2 * k + 3)) hx
  exact (by omega :
      PrimeReciprocal.logarithmicBrunDepth a b (z N k) + N ≤
        N ^ 2 + N).trans (hsum.trans (hpow.trans hcoef))

theorem tendsto_two_pow_depth_div_z_zero
    (a b k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun N : ℕ =>
      (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) /
        z N k) atTop (nhds 0) := by
  have hmajorant : Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  apply squeeze_zero' (g := fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_depth_add_le_roughPower a b k hk] with N hExp
    unfold z
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul, ← pow_add]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hExp
  · exact hmajorant

/-- Normalized squarefree-exception estimate using an explicit reciprocal
Euler-product envelope. -/
theorem eventually_refinedNonSquarefree_normalized_le
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (a b : ℕ)
    (hEuler : ∀ Z : ℕ,
      1 ≤ (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b Z *
        finiteEulerProduct
          (CoverBPZ.refinedSievePrimeProduct S Z).primeFactors
          (fun p => binomialSieveNu S.k p)) :
    ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedNonSquarefreeCandidates S (X N S.k) (z N S.k)).card : ℝ) /
          ((X N S.k : ℝ) *
            finiteEulerProduct
              (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
              (fun p => binomialSieveNu S.k p)) ≤
        6 * (S.k : ℝ) *
          ((2 : ℝ) ^
              PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) /
            z N S.k) := by
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNpos : 0 < N := by omega
  have hk : 0 < S.k := by have := S.hk3; omega
  have hzPosNat : 0 < z N S.k := z_pos N S.k
  have hzPos : (0 : ℝ) < z N S.k := by exact_mod_cast hzPosNat
  have hXPosNat : 0 < X N S.k := X_pos N S.k
  have hXPos : (0 : ℝ) < X N S.k := by exact_mod_cast hXPosNat
  have hVPos : 0 < V N := by
    have hv := boundingSieve_finiteEulerProduct_pos
      (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    simpa [V, refinedBinomialBoundingSieve] using hv
  let R := Nat.sqrt (X N S.k)
  have hzRNat : z N S.k ≤ R := by
    dsimp [R]
    rw [Nat.le_sqrt']
    exact z_sq_le_X hN
  have hzR : (z N S.k : ℝ) ≤ R := by exact_mod_cast hzRNat
  have hRPosNat : 0 < R := lt_of_lt_of_le hzPosNat hzRNat
  have hRPos : (0 : ℝ) < R := by exact_mod_cast hRPosNat
  have hRsq : R ^ 2 ≤ X N S.k := by
    dsimp [R]
    exact Nat.sqrt_le' _
  have hzRMul : (z N S.k : ℝ) * R ≤ X N S.k := by
    calc
      (z N S.k : ℝ) * R ≤ (R : ℝ) * R := by gcongr
      _ = (R ^ 2 : ℕ) := by norm_cast; ring
      _ ≤ X N S.k := by exact_mod_cast hRsq
  have hXOne : ((X N S.k + 1 : ℕ) : ℝ) ≤ 2 * X N S.k := by
    exact_mod_cast (by omega : X N S.k + 1 ≤ 2 * X N S.k)
  have hROne : ((R + 1 : ℕ) : ℝ) ≤ 2 * R := by
    exact_mod_cast (by omega : R + 1 ≤ 2 * R)
  have hinside :
      ((((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
          (R + 1 : ℕ)) / (X N S.k : ℝ)) ≤
        6 / (z N S.k : ℝ) := by
    rw [div_le_iff₀ hXPos]
    have hnormalize :
        (6 / (z N S.k : ℝ)) * (X N S.k : ℝ) =
          (6 * (X N S.k : ℝ)) / (z N S.k : ℝ) := by
      field_simp
    rw [hnormalize, le_div_iff₀ hzPos]
    calc
      (((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
          (R + 1 : ℕ)) * (z N S.k : ℝ) =
        2 * (X N S.k + 1 : ℕ) + (z N S.k : ℝ) * (R + 1 : ℕ) := by
          field_simp
      _ ≤ 2 * (2 * (X N S.k : ℝ)) +
          (z N S.k : ℝ) * (2 * R) := by gcongr
      _ ≤ 4 * (X N S.k : ℝ) + 2 * X N S.k := by
        nlinarith
      _ = 6 * (X N S.k : ℝ) := by ring
  have hraw := CoverBPZ.card_refinedNonSquarefreeCandidates_real_le
    (X := X N S.k) (z := z N S.k) S hzPosNat
  change ((CoverBPZ.RefinedNonSquarefreeCandidates S
      (X N S.k) (z N S.k)).card : ℝ) ≤
    (S.k : ℝ) *
      ((((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
        (R + 1 : ℕ))) at hraw
  have hInvV : 1 / V N ≤
      (2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) := by
    rw [div_le_iff₀ hVPos]
    simpa [V, mul_comm] using hEuler (z N S.k)
  change _ / ((X N S.k : ℝ) * V N) ≤ _
  calc
    ((CoverBPZ.RefinedNonSquarefreeCandidates S
        (X N S.k) (z N S.k)).card : ℝ) /
          ((X N S.k : ℝ) * V N) ≤
      ((S.k : ℝ) *
        ((((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
          (R + 1 : ℕ)))) / ((X N S.k : ℝ) * V N) := by
      exact div_le_div_of_nonneg_right hraw (by positivity)
    _ = (S.k : ℝ) *
        (((((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
          (R + 1 : ℕ))) / X N S.k) * (1 / V N) := by ring
    _ ≤ (S.k : ℝ) * ((6 / (z N S.k : ℝ)) *
          ((2 : ℝ) ^
            PrimeReciprocal.logarithmicBrunDepth a b (z N S.k))) := by
      have hprod :
          (((((X N S.k + 1 : ℕ) : ℝ) * (2 / (z N S.k : ℝ)) +
              (R + 1 : ℕ))) / X N S.k) * (1 / V N) ≤
            (6 / (z N S.k : ℝ)) *
              ((2 : ℝ) ^
                PrimeReciprocal.logarithmicBrunDepth a b (z N S.k)) :=
        mul_le_mul hinside hInvV (by positivity) (by positivity)
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ S.k)
    _ = 6 * (S.k : ℝ) *
          ((2 : ℝ) ^
              PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) /
            z N S.k) := by ring

theorem tendsto_refinedNonSquarefree_normalized_zero
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) :
    Tendsto (fun N : ℕ =>
      ((CoverBPZ.RefinedNonSquarefreeCandidates S (X N S.k) (z N S.k)).card : ℝ) /
        ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p))) atTop (nhds 0) := by
  obtain ⟨Cπ, hCπ, hcheb⟩ :=
    PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨a, b, hdepth⟩ :=
    CoverBPZ.exists_refined_tail_and_euler_reciprocal_depth hCπ hcheb S
  have hbound := eventually_refinedNonSquarefree_normalized_le S a b
    (fun Z => (hdepth Z).2.2)
  have hzero := (tendsto_two_pow_depth_div_z_zero a b S.k S.hk3).const_mul
    (6 * (S.k : ℝ))
  apply squeeze_zero' (g := fun N : ℕ =>
      6 * (S.k : ℝ) *
        ((2 : ℝ) ^ PrimeReciprocal.logarithmicBrunDepth a b (z N S.k) /
          z N S.k))
  · filter_upwards with N
    have hX : (0 : ℝ) < X N S.k := by
      exact_mod_cast X_pos N S.k
    have hV : (0 : ℝ) <
        finiteEulerProduct
          (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
          (fun p => binomialSieveNu S.k p) := by
      simpa [refinedBinomialBoundingSieve] using
        boundingSieve_finiteEulerProduct_pos
          (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
    exact div_nonneg (Nat.cast_nonneg _) (mul_pos hX hV).le
  · exact hbound
  · simpa [mul_assoc] using hzero

/-- The nonsquarefree exceptional set eventually costs less than half of the
already-established sifted lower bound. -/
theorem eventually_refinedNonSquarefreeCandidates_card_lt_scale
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedNonSquarefreeCandidates S
          (X N S.k) (z N S.k)).card : ℝ) <
        ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p)) /
          (32 * CoverBPZ.refinementModulus S : ℝ) := by
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  have hzero := tendsto_refinedNonSquarefree_normalized_zero S
  have hMpos : (0 : ℝ) < CoverBPZ.refinementModulus S := by
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ((CoverBPZ.RefinedNonSquarefreeCandidates S
          (X N S.k) (z N S.k)).card : ℝ) /
          ((X N S.k : ℝ) * V N) <
        1 / (32 * CoverBPZ.refinementModulus S : ℝ) := by
    simpa [V] using (tendsto_order.1 hzero).2
      (1 / (32 * CoverBPZ.refinementModulus S : ℝ)) (by positivity)
  filter_upwards [hsmall] with N hN
  have hX : (0 : ℝ) < X N S.k := by
    exact_mod_cast X_pos N S.k
  have hV : 0 < V N := by
    simpa [V, refinedBinomialBoundingSieve] using
      boundingSieve_finiteEulerProduct_pos
        (refinedBinomialBoundingSieve S (X N S.k) (z N S.k))
  have hden : 0 < (X N S.k : ℝ) * V N := mul_pos hX hV
  rw [div_lt_iff₀ hden] at hN
  change _ < (X N S.k : ℝ) * V N /
    (32 * CoverBPZ.refinementModulus S : ℝ)
  calc
    ((CoverBPZ.RefinedNonSquarefreeCandidates S
        (X N S.k) (z N S.k)).card : ℝ) <
        (1 / (32 * CoverBPZ.refinementModulus S : ℝ)) *
          ((X N S.k : ℝ) * V N) := hN
    _ = (X N S.k : ℝ) * V N /
        (32 * CoverBPZ.refinementModulus S : ℝ) := by ring

/-- Restricting every residual cover quotient to be squarefree preserves a
fixed positive fraction of the natural sifted scale. -/
theorem eventually_refinedSquarefreeCandidates_card_ge_scale
    {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop,
      ((X N S.k : ℝ) *
          finiteEulerProduct
            (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
            (fun p => binomialSieveNu S.k p)) /
          (32 * CoverBPZ.refinementModulus S : ℝ) ≤
        ((CoverBPZ.RefinedSquarefreeCandidates S
          (X N S.k) (z N S.k)).card : ℝ) := by
  let V : ℕ → ℝ := fun N =>
    finiteEulerProduct
      (CoverBPZ.refinedSievePrimeProduct S (z N S.k)).primeFactors
      (fun p => binomialSieveNu S.k p)
  have hsifted := eventually_refinedSiftedCandidates_card_ge_scale S
  have hnonsq := eventually_refinedNonSquarefreeCandidates_card_lt_scale S
  filter_upwards [hsifted, hnonsq] with N hsiftedN hnonsqN
  have hcardNat :
      (RefinedSiftedCandidates S (X N S.k) (z N S.k)).card =
        (CoverBPZ.RefinedSquarefreeCandidates S
            (X N S.k) (z N S.k)).card +
          (CoverBPZ.RefinedNonSquarefreeCandidates S
            (X N S.k) (z N S.k)).card := by
    rw [CoverBPZ.refinedSiftedCandidates_eq_squarefree_union_nonSquarefree]
    exact Finset.card_union_of_disjoint
      (CoverBPZ.disjoint_refinedSquarefree_nonSquarefree S)
  have hcardReal :
      ((RefinedSiftedCandidates S (X N S.k) (z N S.k)).card : ℝ) =
        (CoverBPZ.RefinedSquarefreeCandidates S
            (X N S.k) (z N S.k)).card +
          (CoverBPZ.RefinedNonSquarefreeCandidates S
            (X N S.k) (z N S.k)).card := by
    exact_mod_cast hcardNat
  change ((X N S.k : ℝ) * V N) /
      (16 * CoverBPZ.refinementModulus S : ℝ) ≤ _ at hsiftedN
  change ((CoverBPZ.RefinedNonSquarefreeCandidates S
      (X N S.k) (z N S.k)).card : ℝ) <
    ((X N S.k : ℝ) * V N) /
      (32 * CoverBPZ.refinementModulus S : ℝ) at hnonsqN
  change ((X N S.k : ℝ) * V N) /
      (32 * CoverBPZ.refinementModulus S : ℝ) ≤ _
  have hdouble :
      ((X N S.k : ℝ) * V N) /
          (16 * CoverBPZ.refinementModulus S : ℝ) =
        2 * (((X N S.k : ℝ) * V N) /
          (32 * CoverBPZ.refinementModulus S : ℝ)) := by ring
  rw [hdouble] at hsiftedN
  linarith

end SubpowerScale

end Erdos387
