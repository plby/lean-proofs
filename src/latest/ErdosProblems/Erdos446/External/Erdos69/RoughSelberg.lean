/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos851.EulerMass
import ErdosProblems.Erdos851.ScaleErrors

/-!
# A quantitative upper-bound sieve for rough integers

This file specializes the finite beta sieve already built on top of
Mathlib's `BoundingSieve`.  Unlike truncating inclusion--exclusion after one
level, the beta weights have a fixed (but arbitrarily large) depth.  Thus the
main term is the Mertens product and the remainder is a fixed power of the
sieving endpoint.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos69

/-- Positive integers at most `X` having no prime divisor at most `z`. -/
noncomputable def roughNumbers (z X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 X).filter fun n ↦
      ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ n

namespace RoughSelberg

open Erdos851 Erdos851.ShiftSieve

/-- A fixed-power, dyadically rounded sieve cutoff.  For fixed `S` it is
comparable to `X^(1/(8*S))`; the dyadic definition makes all power-remainder
estimates exact in `ℕ`. -/
def fixedPowerCutoff (S X : ℕ) : ℕ :=
  roughCutoff S (logIndex X)

theorem three_le_fixedPowerCutoff {S X : ℕ} (hS : 0 < S)
    (hJ : 16 * S ≤ logIndex X) :
    3 ≤ fixedPowerCutoff S X := by
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  have hq : 2 ≤ logIndex X / (8 * S) := by
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  rw [fixedPowerCutoff, roughCutoff]
  exact (by norm_num : 3 ≤ 2 ^ 2) |>.trans
    (Nat.pow_le_pow_right (by norm_num) hq)

/-- The logarithm of the rounded fixed-power cutoff loses only the explicit
factor `16*S` compared with the ambient logarithm. -/
theorem log_le_mul_log_fixedPowerCutoff {S X : ℕ} (hS : 0 < S)
    (hX : 0 < X) (hJ : 16 * S ≤ logIndex X) :
    Real.log (X : ℝ) ≤
      (16 * S : ℕ) * Real.log (fixedPowerCutoff S X : ℝ) := by
  let J := logIndex X
  let q := J / (8 * S)
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  have hq : 2 ≤ q := by
    dsimp [q, J]
    apply (Nat.le_div_iff_mul_le hden).2
    simpa only [show 2 * (8 * S) = 16 * S by ring] using hJ
  have hJq : J + 1 ≤ 16 * S * q := by
    have hlt : J < 8 * S * (q + 1) := by
      dsimp [q]
      exact Nat.lt_mul_div_succ J hden
    nlinarith
  have hXupper := lt_pow_logIndex_succ hX
  have hXupperR : (X : ℝ) ≤ ((2 ^ (J + 1) : ℕ) : ℝ) := by
    exact_mod_cast hXupper.le
  calc
    Real.log (X : ℝ) ≤ Real.log (((2 ^ (J + 1) : ℕ) : ℝ)) :=
      Real.log_le_log (by exact_mod_cast hX) hXupperR
    _ = ((J + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    _ ≤ ((16 * S * q : ℕ) : ℝ) * Real.log 2 := by
      gcongr
    _ = (16 * S : ℕ) * Real.log (fixedPowerCutoff S X : ℝ) := by
      simp only [fixedPowerCutoff, roughCutoff, J, q, Nat.cast_pow,
        Real.log_pow, Nat.cast_ofNat, Nat.cast_mul]
      ring

/-- At the fixed-power cutoff the beta-sieve remainder is eventually no
larger than `X / log X`. -/
theorem fixedPowerCutoff_remainder_le {S X : ℕ} (hS : 0 < S)
    (hX : 1 < X) (hJ : 192 ≤ logIndex X) :
    (((fixedPowerCutoff S X) ^ S : ℕ) : ℝ) ^ 2 ≤
      (X : ℝ) / Real.log (X : ℝ) := by
  let J := logIndex X
  let D := distributionLevel J
  have hXpos : 0 < X := hX.trans' Nat.zero_lt_one
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcut : fixedPowerCutoff S X ^ S ≤ D := by
    simpa only [fixedPowerCutoff, J, D] using
      (roughCutoff_pow_le_distributionLevel (J := J) hS)
  have hcutSq : (fixedPowerCutoff S X ^ S) ^ 2 ≤ D ^ 2 :=
    Nat.pow_le_pow_left hcut 2
  have hscale : J ^ 2 * D ^ 2 ≤ X := by
    simpa only [D, pow_zero, one_mul] using
      (pow_mul_sq_mul_distributionLevel_sq_le_scale
        (N := 0) (J := J) (X := X) (by simpa [J] using hJ)
        (by omega) (by simpa [J] using pow_logIndex_le hXpos))
  have hXupperR : (X : ℝ) ≤ ((2 ^ (J + 1) : ℕ) : ℝ) := by
    exact_mod_cast (lt_pow_logIndex_succ hXpos).le
  have hlogBound : Real.log (X : ℝ) ≤ (J : ℝ) ^ 2 := by
    calc
      Real.log (X : ℝ) ≤ Real.log (((2 ^ (J + 1) : ℕ) : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hXpos) hXupperR
      _ = ((J + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      _ ≤ ((J + 1 : ℕ) : ℝ) := by
        have hlogTwo : Real.log 2 ≤ 1 :=
          Real.log_two_lt_d9.le.trans (by norm_num)
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hlogTwo (by positivity :
            (0 : ℝ) ≤ ((J + 1 : ℕ) : ℝ))
      _ ≤ (J : ℝ) ^ 2 := by
        have hJnat : 2 ≤ J := by omega
        exact_mod_cast (show J + 1 ≤ J ^ 2 by nlinarith)
  rw [le_div_iff₀ hlogX]
  have hcutSqR : ((((fixedPowerCutoff S X) ^ S : ℕ) : ℝ) ^ 2) ≤
      ((D ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcutSq
  have hscaleR : (((J ^ 2 * D ^ 2 : ℕ) : ℝ)) ≤ (X : ℝ) := by
    exact_mod_cast hscale
  calc
    (((fixedPowerCutoff S X) ^ S : ℕ) : ℝ) ^ 2 *
          Real.log (X : ℝ) ≤
        ((D ^ 2 : ℕ) : ℝ) * (J : ℝ) ^ 2 := by
      exact mul_le_mul hcutSqR hlogBound hlogX.le (by positivity)
    _ = ((J ^ 2 * D ^ 2 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (X : ℝ) := hscaleR

/-- Translation identifies `[1,X]` with the dyadic interval `(X,2X]`. -/
private def translateToDyadic (X n : ℕ) : ℕ := X + n

private theorem translateToDyadic_injective (X : ℕ) :
    Function.Injective (translateToDyadic X) := by
  intro a b hab
  simp only [translateToDyadic] at hab
  omega

/-- A `z`-rough integer, translated into `(X,2X]`, survives the singleton
shift sieve by all primes in `(2,z]`.  Omitting the prime `2` only enlarges
the sieve set, which is the correct direction for an upper bound. -/
theorem image_roughNumbers_subset_siftedShiftCandidates (X z : ℕ) :
    (roughNumbers z X).image (translateToDyadic X) ⊆
      siftedShiftCandidates {X} X 2 (z + 1) := by
  classical
  intro a ha
  rw [Finset.mem_image] at ha
  obtain ⟨n, hn, rfl⟩ := ha
  change X + n ∈ siftedShiftCandidates {X} X 2 (z + 1)
  rw [siftedShiftCandidates, Finset.mem_filter]
  constructor
  · rw [Finset.mem_Ioc]
    have hnIcc := (Finset.mem_filter.mp (show n ∈
      (Finset.Icc 1 X).filter fun n ↦
        ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ n by simpa [roughNumbers] using hn)).1
    rw [Finset.mem_Icc] at hnIcc
    omega
  · rw [Nat.coprime_iff_gcd_eq_one]
    rw [← Nat.coprime_iff_gcd_eq_one]
    apply Nat.coprime_of_dvd
    intro p hpPrime hpProd
    have hpMem := Erdos387.prime_mem_sievePrimes_of_dvd_product hpPrime hpProd
    have hpz : p ≤ z := by
      have := (Erdos387.mem_sievePrimes.mp hpMem).2.2
      omega
    have hrough : ¬ p ∣ n := by
      have hn' : n ∈ (Finset.Icc 1 X).filter fun n ↦
          ∀ p : ℕ, p.Prime → p ≤ z → ¬ p ∣ n := by
        simpa [roughNumbers] using hn
      exact (Finset.mem_filter.mp hn').2 p hpPrime hpz
    simpa [shiftedProduct] using hrough

/-- Cardinal form of the translation embedding. -/
theorem roughNumbers_card_le_siftedShiftCandidates (X z : ℕ) :
    (roughNumbers z X).card ≤
      (siftedShiftCandidates {X} X 2 (z + 1)).card := by
  classical
  rw [← Finset.card_image_of_injective _ (translateToDyadic_injective X)]
  exact Finset.card_le_card (image_roughNumbers_subset_siftedShiftCandidates X z)

/-- A direct specialization of the beta sieve.  The constants and all
side conditions are explicit; in particular the only error is `z^(2*S)`.
The existential constant `A` is absolute. -/
theorem exists_roughNumbers_beta_upper_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ X z S : ℕ, 3 ≤ z → 101 ≤ S →
        Real.log A ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := localEulerProduct oneShiftDensity 2 z
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((roughNumbers z X).card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * V) + ((z ^ S : ℕ) : ℝ) ^ 2 := by
  classical
  obtain ⟨A, hA, hbeta⟩ := exists_oneShift_concrete_cardinality_bounds
  refine ⟨A, hA, ?_⟩
  intro X z S hz hS hlog
  dsimp only
  have hraw := hbeta X X 2 z S (by rfl) (by norm_num) (by omega)
    (by omega) hS hlog
  dsimp only at hraw
  have hcardR : ((roughNumbers z X).card : ℝ) ≤
      ((siftedShiftCandidates {X} X 2 (z + 1)).card : ℝ) := by
    exact_mod_cast roughNumbers_card_le_siftedShiftCandidates X z
  exact hcardR.trans hraw.2

/-- Mertens' third theorem turns the one-dimensional local product into the
usual reciprocal logarithm, with an absolute positive constant. -/
theorem exists_oneShift_localEulerProduct_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℕ, 3 ≤ z →
      localEulerProduct oneShiftDensity 2 z ≤ C / Real.log (z : ℝ) := by
  obtain ⟨c, hc, hmertens⟩ := weak_mertens_third_lower_all
  let C : ℝ := partial_euler_product 2 / c
  have hpep2 : 0 < partial_euler_product 2 :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hC : 0 < C := div_pos hpep2 hc
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hzOne : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hpepz : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hmertens' : c * Real.log (z : ℝ) ≤ partial_euler_product z := by
    simpa [Real.norm_eq_abs, abs_of_pos hlogz, abs_of_pos hpepz]
      using hmertens (z : ℝ) hzOne
  let V := localEulerProduct oneShiftDensity 2 z
  have hV : 0 < V := oneShift_localEulerProduct_pos
  have hinv : V⁻¹ = partial_euler_product z / partial_euler_product 2 := by
    rw [← inverseLocalEulerProduct_eq_inv]
    exact oneShift_inverseLocalEulerProduct_eq (by omega)
  have hidentity : V * partial_euler_product z = partial_euler_product 2 := by
    field_simp [hV.ne', hpep2.ne'] at hinv
    nlinarith
  rw [show C / Real.log (z : ℝ) =
      partial_euler_product 2 / (c * Real.log (z : ℝ)) by
    dsimp [C]
    field_simp [hc.ne', hlogz.ne']]
  rw [le_div_iff₀ (mul_pos hc hlogz)]
  calc
    V * (c * Real.log (z : ℝ)) ≤ V * partial_euler_product z :=
      mul_le_mul_of_nonneg_left hmertens' hV.le
    _ = partial_euler_product 2 := hidentity

/-- A fixed beta-sieve depth can absorb the absolute construction constant. -/
theorem exists_upper_sieve_depth {A : ℝ} (hA : 1 ≤ A) :
    ∃ S : ℕ, 101 ≤ S ∧
      Real.log A ≤ 2 * (S - 100 : ℕ) / 99 := by
  obtain ⟨S, hS⟩ := exists_nat_gt (Real.log A * 99 / 2 + 101)
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hSR : (101 : ℝ) < S := by nlinarith
  have hSNat : 101 ≤ S := by exact_mod_cast hSR.le
  refine ⟨S, hSNat, ?_⟩
  rw [Nat.cast_sub (by omega : 100 ≤ S)]
  norm_num at hS ⊢
  nlinarith

/-- Hypothesis-free upper-bound sieve with a fixed absolute depth.  This is
the convenient interface for applications: the first term is
`O(X / log z)`, and the fully explicit remainder is `z^(2*S)`. -/
theorem exists_roughNumbers_log_upper_bound :
    ∃ B : ℝ, ∃ S : ℕ, 0 < B ∧ 101 ≤ S ∧
      ∀ X z : ℕ, 3 ≤ z →
        ((roughNumbers z X).card : ℝ) ≤
          B * (X : ℝ) / Real.log (z : ℝ) +
            ((z ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbeta⟩ := exists_roughNumbers_beta_upper_bound
  obtain ⟨C, hC, hprod⟩ := exists_oneShift_localEulerProduct_upper_bound
  obtain ⟨S, hS, hlog⟩ := exists_upper_sieve_depth hA
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let B : ℝ := (1 + eta) * C
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hB : 0 < B := mul_pos (by linarith) hC
  refine ⟨B, S, hB, hS, ?_⟩
  intro X z hz
  have hraw := hbeta X z S hz hS hlog
  dsimp only at hraw
  have hV := hprod z hz
  have hmain :
      (X : ℝ) * ((1 + eta) * localEulerProduct oneShiftDensity 2 z) ≤
        (X : ℝ) * ((1 + eta) * (C / Real.log (z : ℝ))) := by
    gcongr
  calc
    ((roughNumbers z X).card : ℝ) ≤
        (X : ℝ) * ((1 + eta) * localEulerProduct oneShiftDensity 2 z) +
          ((z ^ S : ℕ) : ℝ) ^ 2 := by simpa [eta] using hraw
    _ ≤ (X : ℝ) * ((1 + eta) * (C / Real.log (z : ℝ))) +
          ((z ^ S : ℕ) : ℝ) ^ 2 := add_le_add hmain le_rfl
    _ = B * (X : ℝ) / Real.log (z : ℝ) +
          ((z ^ S : ℕ) : ℝ) ^ 2 := by
      dsimp [B]
      ring

/-- TT-ready fixed-power specialization.  The sieve endpoint is the explicit
dyadic rounding `2^(floor(log₂ X /(8*S)))`; for all sufficiently large `X`
the rough-number density is at most an absolute constant divided by `log X`.
-/
theorem exists_eventually_fixedPowerCutoff_roughNumbers_log_upper_bound :
    ∃ C : ℝ, ∃ S : ℕ, 0 < C ∧ 101 ≤ S ∧
      ∀ᶠ X : ℕ in atTop,
        ((roughNumbers (fixedPowerCutoff S X) X).card : ℝ) ≤
          C * (X : ℝ) / Real.log (X : ℝ) := by
  obtain ⟨B, S, hB, hS, hrough⟩ := exists_roughNumbers_log_upper_bound
  have hSpos : 0 < S := by omega
  let K : ℝ := (16 * S : ℕ)
  let C : ℝ := K * B + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, S, hC, hS, ?_⟩
  filter_upwards
      [eventually_gt_atTop (1 : ℕ),
       tendsto_logIndex_atTop.eventually (eventually_ge_atTop 192),
       tendsto_logIndex_atTop.eventually (eventually_ge_atTop (16 * S))]
      with X hX hJlarge hJcut
  let z := fixedPowerCutoff S X
  have hz : 3 ≤ z := by
    exact three_le_fixedPowerCutoff hSpos hJcut
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogCompare : Real.log (X : ℝ) ≤ K * Real.log (z : ℝ) := by
    simpa only [K, z, Nat.cast_mul, Nat.cast_ofNat] using
      (log_le_mul_log_fixedPowerCutoff hSpos (by omega : 0 < X) hJcut)
  have hmain : B * (X : ℝ) / Real.log (z : ℝ) ≤
      K * B * (X : ℝ) / Real.log (X : ℝ) := by
    apply (div_le_div_iff₀ hlogz hlogX).2
    calc
      (B * (X : ℝ)) * Real.log (X : ℝ) ≤
          (B * (X : ℝ)) * (K * Real.log (z : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogCompare
          (mul_nonneg hB.le (by positivity))
      _ = (K * B * (X : ℝ)) * Real.log (z : ℝ) := by ring
  have hrem : (((z ^ S : ℕ) : ℝ) ^ 2) ≤
      (X : ℝ) / Real.log (X : ℝ) := by
    simpa only [z] using
      fixedPowerCutoff_remainder_le hSpos hX hJlarge
  calc
    ((roughNumbers z X).card : ℝ) ≤
        B * (X : ℝ) / Real.log (z : ℝ) +
          ((z ^ S : ℕ) : ℝ) ^ 2 := hrough X z hz
    _ ≤ K * B * (X : ℝ) / Real.log (X : ℝ) +
          (X : ℝ) / Real.log (X : ℝ) := add_le_add hmain hrem
    _ = C * (X : ℝ) / Real.log (X : ℝ) := by
      dsimp [C]
      ring

end RoughSelberg

end Erdos69
