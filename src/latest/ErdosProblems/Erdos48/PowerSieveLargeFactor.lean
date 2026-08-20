/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveParameters
import ErdosProblems.Erdos48.LargeFactorSieveSharp

/-!
# The large-factor sieve at the tunable integer-power FLP scales

This file discharges the elementary parameter inequalities needed to apply
the pointwise large-factor sieve on a dyadic root block.  The smoothness and
root-product scales approach the square root of `n^(240*L)` as `L` grows,
whereas the leftover cofactor has the fixed bound `n^14`.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

/-- A safe integral cofactor bound after removing a dyadic root, an
auxiliary prime, and a prime above the smoothness threshold. -/
def powerSieveCofactorBound (n _L : ℕ) : ℕ := n ^ 14

/-- The residual-prime beta-sieve scale. -/
def powerSieveResidualCutoff (n L : ℕ) : ℕ := n ^ (100 * L)

/-- The tunable small-prime cutoff.  Its exponent decreases when the
Rosser depth `S` increases. -/
def powerSieveSmallPrimeBound (n L S : ℕ) : ℕ := n ^ (L / (S + 1))

theorem powerSieveResidualCutoff_le_smoothBound
    {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    powerSieveResidualCutoff n L ≤ powerSieveSmoothBound n L := by
  unfold powerSieveResidualCutoff powerSieveSmoothBound
  exact pow_le_pow_right' hn (by omega)

theorem powerSieveAuxCore_mul_block_le
    {n L Q : ℕ} :
    Q * powerSieveAuxCore n L Q ≤
      powerSieveProductBase n L + Q * powerSieveAuxScale n L := by
  rw [powerSieveAuxCore]
  calc
    Q * max (powerSieveProductBase n L / Q) (powerSieveAuxScale n L) ≤
        Q * (powerSieveProductBase n L / Q +
          powerSieveAuxScale n L) := by
      exact Nat.mul_le_mul_left Q
        (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    _ = Q * (powerSieveProductBase n L / Q) +
        Q * powerSieveAuxScale n L := by rw [Nat.mul_add]
    _ ≤ powerSieveProductBase n L + Q * powerSieveAuxScale n L :=
      Nat.add_le_add_right (Nat.mul_div_le _ _) _

/-- Every root--auxiliary product in the dyadic block is below a fixed
power just above the square-root scale.  This sharp form uses the actual
root bound `q ≤ u`, so it also covers the final partial dyadic shell. -/
theorem powerSieve_root_mul_aux_le_of_root_le
    {n L Q q r : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hqSmooth : q ≤ powerSieveSmoothBound n L)
    (hqUpper : q ≤ 2 * Q) (hr : r ∈ powerSieveAuxPrimes n L Q) :
    q * r ≤ n ^ (120 * L - 2) := by
  have hrUpper : r ≤
      powerSieveAuxCore n L Q * powerSieveAuxScale n L := by
    simpa only [powerSieveAuxUpper] using
      (mem_powerSieveAuxPrimes.mp hr).2.1
  have hcore : powerSieveAuxCore n L Q ≤
      powerSieveProductBase n L / Q + powerSieveAuxScale n L := by
    unfold powerSieveAuxCore
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hrootCore : q * powerSieveAuxCore n L Q ≤
      2 * powerSieveProductBase n L + q * powerSieveAuxScale n L := by
    calc
      q * powerSieveAuxCore n L Q ≤
          q * (powerSieveProductBase n L / Q +
            powerSieveAuxScale n L) := Nat.mul_le_mul_left q hcore
      _ = q * (powerSieveProductBase n L / Q) +
          q * powerSieveAuxScale n L := by ring
      _ ≤ (2 * Q) * (powerSieveProductBase n L / Q) +
          q * powerSieveAuxScale n L :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (powerSieveProductBase n L / Q) hqUpper) _
      _ ≤ 2 * powerSieveProductBase n L +
          q * powerSieveAuxScale n L := by
        exact Nat.add_le_add_right
          (by
            calc
              (2 * Q) * (powerSieveProductBase n L / Q) =
                  2 * (Q * (powerSieveProductBase n L / Q)) := by ring
              _ ≤ 2 * powerSieveProductBase n L :=
                Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)) _
  have hprod : q * r ≤
      (2 * powerSieveProductBase n L +
        q * powerSieveAuxScale n L) * powerSieveAuxScale n L := by
    calc
      q * r ≤ q *
          (powerSieveAuxCore n L Q * powerSieveAuxScale n L) :=
        Nat.mul_le_mul_left q hrUpper
      _ = (q * powerSieveAuxCore n L Q) *
          powerSieveAuxScale n L := by ring
      _ ≤ (2 * powerSieveProductBase n L +
          q * powerSieveAuxScale n L) * powerSieveAuxScale n L :=
        Nat.mul_le_mul_right _ hrootCore
  have hsmoothTimesSq :
      powerSieveSmoothBound n L * powerSieveAuxScale n L ^ 2 =
        n ^ (120 * L - 4) := by
    change n ^ (120 * L - 6) * n ^ 2 = n ^ (120 * L - 4)
    rw [← pow_add]
    congr 1
    omega
  have htwo : 2 ≤ n ^ 2 :=
    (by omega : 2 ≤ n).trans (Nat.le_pow (by omega))
  have hfirst :
      2 * powerSieveProductBase n L * powerSieveAuxScale n L ≤
        n ^ (120 * L - 4) := by
    rw [mul_assoc, powerSieveProductBase_mul_auxScale hL]
    calc
      2 * powerSieveSmoothBound n L ≤
          n ^ 2 * powerSieveSmoothBound n L :=
        Nat.mul_le_mul_right _ htwo
      _ = n ^ (120 * L - 4) := by
        change n ^ 2 * n ^ (120 * L - 6) = n ^ (120 * L - 4)
        rw [← pow_add]
        congr 1
        omega
  have hsecond :
      q * powerSieveAuxScale n L ^ 2 ≤ n ^ (120 * L - 4) := by
    calc
      q * powerSieveAuxScale n L ^ 2 ≤
          powerSieveSmoothBound n L * powerSieveAuxScale n L ^ 2 :=
        Nat.mul_le_mul_right _ hqSmooth
      _ = n ^ (120 * L - 4) := hsmoothTimesSq
  have hsum : q * r ≤ 2 * n ^ (120 * L - 4) := by
    calc
      q * r ≤ 2 * powerSieveProductBase n L * powerSieveAuxScale n L +
          q * powerSieveAuxScale n L ^ 2 := by
        calc
          q * r ≤ (2 * powerSieveProductBase n L +
              q * powerSieveAuxScale n L) * powerSieveAuxScale n L := hprod
          _ = _ := by ring
      _ ≤ n ^ (120 * L - 4) + n ^ (120 * L - 4) :=
        Nat.add_le_add hfirst hsecond
      _ = 2 * n ^ (120 * L - 4) := by ring
  calc
    q * r ≤ 2 * n ^ (120 * L - 4) := hsum
    _ ≤ n ^ 2 * n ^ (120 * L - 4) := Nat.mul_le_mul_right _ htwo
    _ = n ^ (120 * L - 2) := by
      rw [← pow_add]
      congr 1
      omega

/-- Compatibility wrapper for complete dyadic shells. -/
theorem powerSieve_root_mul_aux_le
    {n L Q q r : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hQupper : 2 * Q ≤ powerSieveSmoothBound n L)
    (hqUpper : q ≤ 2 * Q) (hr : r ∈ powerSieveAuxPrimes n L Q) :
    q * r ≤ n ^ (120 * L - 2) :=
  powerSieve_root_mul_aux_le_of_root_le hn hL
    (hqUpper.trans hQupper) hqUpper hr

/-- After the maximal allowed cofactor is inserted, a residual factor
`n^(100*L)` still fits below the main endpoint, using the actual root
cutoff rather than completeness of its dyadic shell. -/
theorem powerSieve_largeFactor_denominator_le_of_root_le
    {n L Q q r b : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hqSmooth : q ≤ powerSieveSmoothBound n L)
    (hqUpper : q ≤ 2 * Q) (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hb : b ∈ Finset.Icc 1 (powerSieveCofactorBound n L)) :
    q * r * b * powerSieveResidualCutoff n L ≤ powerSieveX n L := by
  have hqr := powerSieve_root_mul_aux_le_of_root_le
    hn hL hqSmooth hqUpper hr
  have hbUpper := (Finset.mem_Icc.mp hb).2
  have hexp : (120 * L - 2) + 14 + 100 * L ≤ 240 * L := by omega
  calc
    q * r * b * powerSieveResidualCutoff n L ≤
        n ^ (120 * L - 2) * n ^ 14 * n ^ (100 * L) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul hqr
          (by simpa only [powerSieveCofactorBound] using hbUpper))
        (by rfl)
    _ = n ^ ((120 * L - 2) + 14 + 100 * L) := by
      rw [← pow_add, ← pow_add]
    _ ≤ n ^ (240 * L) := pow_le_pow_right' (by omega) hexp
    _ = powerSieveX n L := by rfl

/-- Compatibility wrapper for complete dyadic shells. -/
theorem powerSieve_largeFactor_denominator_le
    {n L Q q r b : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hQupper : 2 * Q ≤ powerSieveSmoothBound n L)
    (hqUpper : q ≤ 2 * Q) (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hb : b ∈ Finset.Icc 1 (powerSieveCofactorBound n L)) :
    q * r * b * powerSieveResidualCutoff n L ≤ powerSieveX n L :=
  powerSieve_largeFactor_denominator_le_of_root_le hn hL
    (hqUpper.trans hQupper) hqUpper hr hb

/-- The multiplicative denominator bound in the quotient form consumed by
the pointwise beta sieve, valid in a partial top shell. -/
theorem powerSieve_residualCutoff_le_quotient_of_root_le
    {n L Q q r b : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hqSmooth : q ≤ powerSieveSmoothBound n L)
    (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hb : b ∈ Finset.Icc 1 (powerSieveCofactorBound n L)) :
    powerSieveResidualCutoff n L ≤
      (powerSieveX n L + 1) / (q * r * b) := by
  have hqPos : 0 < q := by omega
  have hrPos : 0 < r := (mem_powerSieveAuxPrimes.mp hr).2.2.pos
  have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos hqPos hrPos) hbPos)]
  have hden := powerSieve_largeFactor_denominator_le_of_root_le
    hn hL hqSmooth hqUpper hr hb
  calc
    powerSieveResidualCutoff n L * (q * r * b) =
        q * r * b * powerSieveResidualCutoff n L := by ring
    _ ≤ powerSieveX n L := hden
    _ ≤ powerSieveX n L + 1 := Nat.le_succ _

/-- Compatibility wrapper for complete dyadic shells. -/
theorem powerSieve_residualCutoff_le_quotient
    {n L Q q r b : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L)
    (hQupper : 2 * Q ≤ powerSieveSmoothBound n L)
    (hqLower : Q < q) (hqUpper : q ≤ 2 * Q)
    (hr : r ∈ powerSieveAuxPrimes n L Q)
    (hb : b ∈ Finset.Icc 1 (powerSieveCofactorBound n L)) :
    powerSieveResidualCutoff n L ≤
      (powerSieveX n L + 1) / (q * r * b) :=
  powerSieve_residualCutoff_le_quotient_of_root_le hn hL
    (hqUpper.trans hQupper) hqLower hqUpper hr hb

/-- The product-base scale is strictly below every root--auxiliary product
in the stated dyadic block. -/
theorem powerSieveProductBase_lt_root_mul_aux
    {n L Q q r : ℕ}
    (hn : 4 ≤ n) (hQ : 1 ≤ Q) (hqLower : Q < q)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    powerSieveProductBase n L < q * r := by
  let P := powerSieveProductBase n L
  let C := powerSieveAuxCore n L Q
  have hCpos : 0 < C := powerSieveAuxCore_pos (by omega)
  have hdivC : P / Q ≤ C := by
    dsimp only [P, C, powerSieveAuxCore]
    exact le_max_left _ _
  have hrem : P % Q < Q := Nat.mod_lt _ (by omega)
  have hPdiv : P < Q * (P / Q + 1) := by
    calc
      P = Q * (P / Q) + P % Q := (Nat.div_add_mod P Q).symm
      _ < Q * (P / Q) + Q := Nat.add_lt_add_left hrem _
      _ = Q * (P / Q + 1) := by ring
  have hsuccCore : P / Q + 1 ≤ 2 * C := by omega
  have hrLower : 2 * C < r := by
    simpa only [C, powerSieveAuxLower] using
      (mem_powerSieveAuxPrimes.mp hr).1
  calc
    P < Q * (P / Q + 1) := hPdiv
    _ < q * (P / Q + 1) :=
      Nat.mul_lt_mul_of_pos_right hqLower (Nat.zero_lt_succ _)
    _ ≤ q * (2 * C) := Nat.mul_le_mul_left q hsuccCore
    _ < q * r := Nat.mul_lt_mul_of_pos_left hrLower (by omega)

/-- The small-prime cutoff plus one is below the root--auxiliary product,
as required by the residual-fibre decomposition. -/
theorem powerSieveSmallPrimeBound_add_one_lt_root_mul_aux
    {n L S Q q r : ℕ}
    (hn : 4 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) (hqLower : Q < q)
    (hr : r ∈ powerSieveAuxPrimes n L Q) :
    powerSieveSmallPrimeBound n L S + 1 < q * r := by
  have hdL : L / (S + 1) ≤ L := Nat.div_le_self _ _
  have hexp : L / (S + 1) + 1 ≤ 120 * L - 7 := by omega
  have hone : 1 ≤ n ^ (L / (S + 1)) :=
    Nat.one_le_pow (L / (S + 1)) n (by omega)
  have hstep : n ^ (L / (S + 1)) + 1 < n ^ (L / (S + 1) + 1) := by
    rw [pow_succ]
    nlinarith
  have hbase : powerSieveSmallPrimeBound n L S + 1 <
      powerSieveProductBase n L := by
    unfold powerSieveSmallPrimeBound powerSieveProductBase
    exact hstep.trans_le (pow_le_pow_right' (by omega) hexp)
  exact hbase.trans (powerSieveProductBase_lt_root_mul_aux hn hQ hqLower hr)

/-- The tunable cutoff is nontrivial once its denominator fits into `L`. -/
theorem one_lt_powerSieveSmallPrimeBound
    {n L S : ℕ} (hn : 2 ≤ n) (hSL : S + 1 ≤ L) :
    1 < powerSieveSmallPrimeBound n L S := by
  unfold powerSieveSmallPrimeBound
  have hd : 0 < L / (S + 1) := by
    rw [Nat.div_pos_iff]
    omega
  exact one_lt_pow₀ (by omega) hd.ne'

/-- The Rosser power of the tunable small-prime cutoff lies below the
quarter-level modulus cutoff at the residual scale. -/
theorem powerSieve_smallPrimePower_le_quarterCutoff
    {n L S : ℕ} (hn : 1 ≤ n) :
    (powerSieveSmallPrimeBound n L S) ^ S ≤
      modulusCutoff (1 / 4 : ℝ) (powerSieveResidualCutoff n L) := by
  have hdiv : (L / (S + 1)) * S ≤ L := by
    calc
      (L / (S + 1)) * S ≤ (L / (S + 1)) * (S + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ ≤ L := Nat.div_mul_le_self _ _
  have hsmall : (powerSieveSmallPrimeBound n L S) ^ S ≤ n ^ (25 * L) := by
    unfold powerSieveSmallPrimeBound
    rw [← pow_mul]
    exact pow_le_pow_right' hn (hdiv.trans (by omega))
  apply hsmall.trans
  unfold modulusCutoff powerSieveResidualCutoff
  apply Nat.le_floor
  simp only [Nat.cast_pow]
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 4)).2
  exact_mod_cast (show (n ^ (25 * L)) ^ 4 ≤ n ^ (100 * L) by
    rw [← pow_mul]
    exact pow_le_pow_right' hn (by omega))

/-- A reusable specialization of the sharp pointwise large-factor sieve to
the tunable integer-power FLP parameters and one possibly partial dyadic root
block.  The literal root bound is the only upper-cutoff hypothesis. -/
theorem exists_powerSieve_representedLargeFactorPrimes_pointwise_upper_bound_of_root_le :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {Bexp CBV : ℝ} {X₀ n L S Q q r : ℕ},
        4 ≤ n → 101 ≤ S → S + 1 ≤ L → 1 ≤ Q →
        Q < q → q ≤ 2 * Q →
        q ≤ powerSieveSmoothBound n L →
        r ∈ powerSieveAuxPrimes n L Q →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        PrimeLevelWitness (1 / 4 : ℝ) Bexp CBV X₀ →
        X₀ ≤ n ^ L →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((representedLargeFactorPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) ≤
          ∑ b ∈ Finset.Icc 1 (powerSieveCofactorBound n L),
            ((Cπ * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
                Real.log ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) *
              ((1 + eta) *
                (CV * ((q * r * b : ℕ) : ℝ) /
                    (Nat.totient (q * r * b) : ℝ) /
                  Real.log (powerSieveSmallPrimeBound n L S : ℝ)))) +
              CBV * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
                Real.rpow
                  (Real.log ((((powerSieveX n L + 1) /
                    (q * r * b) : ℕ) : ℝ))) Bexp +
              CBV * (powerSieveResidualCutoff n L : ℝ) /
                Real.rpow
                  (Real.log (powerSieveResidualCutoff n L : ℝ)) Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hbound⟩ :=
    exists_representedLargeFactorPrimes_pointwise_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro Bexp CBV X₀ n L S Q q r hn hS hSL hQ hqLower hqUpper
    hqSmooth hr hlogAβ hw hX₀
  have hL : 1 ≤ L := by omega
  have hnOne : 1 ≤ n := by omega
  have hzTwo : 2 ≤ powerSieveResidualCutoff n L := by
    unfold powerSieveResidualCutoff
    exact (by omega : 2 ≤ n).trans (Nat.le_pow (by omega))
  have hzu : powerSieveResidualCutoff n L ≤
      powerSieveSmoothBound n L :=
    powerSieveResidualCutoff_le_smoothBound hnOne hL
  have hy : 1 < powerSieveSmallPrimeBound n L S :=
    one_lt_powerSieveSmallPrimeBound (by omega) hSL
  have hqr : powerSieveSmallPrimeBound n L S + 1 < q * r :=
    powerSieveSmallPrimeBound_add_one_lt_root_mul_aux
      hn hL hQ hqLower hr
  have hB : 1 ≤ powerSieveCofactorBound n L := by
    unfold powerSieveCofactorBound
    exact Nat.one_le_pow 14 n (by omega)
  have hXz : X₀ ≤ powerSieveResidualCutoff n L := by
    apply hX₀.trans
    unfold powerSieveResidualCutoff
    exact pow_le_pow_right' hnOne (by omega)
  have hDz : (powerSieveSmallPrimeBound n L S) ^ S ≤
      modulusCutoff (1 / 4 : ℝ) (powerSieveResidualCutoff n L) :=
    powerSieve_smallPrimePower_le_quarterCutoff hnOne
  have hparams : ∀ b ∈ Finset.Icc 1 (powerSieveCofactorBound n L),
      powerSieveResidualCutoff n L ≤
          (powerSieveX n L + 1) / (q * r * b) ∧
        X₀ ≤ (powerSieveX n L + 1) / (q * r * b) ∧
        (powerSieveSmallPrimeBound n L S) ^ S ≤
          modulusCutoff (1 / 4 : ℝ)
            ((powerSieveX n L + 1) / (q * r * b)) ∧
        2 ≤ (powerSieveX n L + 1) / (q * r * b) := by
    intro b hb
    have hquot := powerSieve_residualCutoff_le_quotient_of_root_le
      hn hL hqSmooth hqLower hqUpper hr hb
    refine ⟨hquot, hXz.trans hquot, ?_, hzTwo.trans hquot⟩
    exact hDz.trans
      (modulusCutoff_mono (by norm_num : (0 : ℝ) ≤ 1 / 4) hquot)
  exact hbound hzTwo hzu hy hqr hB hS hlogAβ hw hXz hDz hparams

/-- Compatibility specialization for complete dyadic shells. -/
theorem exists_powerSieve_representedLargeFactorPrimes_pointwise_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {Bexp CBV : ℝ} {X₀ n L S Q q r : ℕ},
        4 ≤ n → 101 ≤ S → S + 1 ≤ L → 1 ≤ Q →
        Q < q → q ≤ 2 * Q →
        2 * Q ≤ powerSieveSmoothBound n L →
        r ∈ powerSieveAuxPrimes n L Q →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        PrimeLevelWitness (1 / 4 : ℝ) Bexp CBV X₀ →
        X₀ ≤ n ^ L →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((representedLargeFactorPrimes
          (powerSieveX n L) (powerSieveSmoothBound n L) q r
          (powerSieveCofactorBound n L)).card : ℝ) ≤
          ∑ b ∈ Finset.Icc 1 (powerSieveCofactorBound n L),
            ((Cπ * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
                Real.log ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) *
              ((1 + eta) *
                (CV * ((q * r * b : ℕ) : ℝ) /
                    (Nat.totient (q * r * b) : ℝ) /
                  Real.log (powerSieveSmallPrimeBound n L S : ℝ)))) +
              CBV * ((((powerSieveX n L + 1) / (q * r * b) : ℕ) : ℝ)) /
                Real.rpow
                  (Real.log ((((powerSieveX n L + 1) /
                    (q * r * b) : ℕ) : ℝ))) Bexp +
              CBV * (powerSieveResidualCutoff n L : ℝ) /
                Real.rpow
                  (Real.log (powerSieveResidualCutoff n L : ℝ)) Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hbound⟩ :=
    exists_powerSieve_representedLargeFactorPrimes_pointwise_upper_bound_of_root_le
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro Bexp CBV X₀ n L S Q q r hn hS hSL hQ hqLower hqUpper
    hQupper hr hlogAβ hw hX₀
  exact hbound hn hS hSL hQ hqLower hqUpper (hqUpper.trans hQupper)
    hr hlogAβ hw hX₀

end

end Erdos48
