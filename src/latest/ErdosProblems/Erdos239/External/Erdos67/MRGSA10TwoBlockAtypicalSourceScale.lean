import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TwoBlockAtypicalLargeScalar
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceYSchedule

/-!
# Source-scale canonical A.10 blocks

The maximal diagonal block exponent used by the first canonical schedule
makes `log y / log Z` a fixed positive constant.  For the ordinary-prefix
A.10 argument we instead take one more square root.  Thus the upper cutoff
`y = 2^(K^2)` has logarithm of square-root size, while the two-block
exceptional density still has a fixed negative logarithmic power.
-/

open scoped BigOperators
open Finset Filter

namespace Erdos67

noncomputable section

/-- The source-scale block exponent is the square root of the maximal
diagonal exponent. -/
def gsA10SourceBlockExponent (S Z : ℕ) : ℕ :=
  Nat.sqrt (gsA10CanonicalBlockExponent S Z)

theorem tendsto_natLog_two_natCast_atTop :
    Tendsto (fun Z : ℕ ↦ (Nat.log 2 Z : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  obtain ⟨N : ℕ, hN : R ≤ N⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop (2 ^ N)] with Z hZ
  have hlog : N ≤ Nat.log 2 Z := Nat.le_log_of_pow_le (by omega) hZ
  exact hN.trans (by exact_mod_cast hlog)

theorem tendsto_sqrt_natLog_two_atTop :
    Tendsto (fun Z : ℕ ↦ Real.sqrt (Nat.log 2 Z : ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natLog_two_natCast_atTop

/-- The beta-sieve power remainder only needs the displayed exponent
inequality; it does not require the maximal canonical choice of `K`. -/
theorem sum_gsA10CanonicalLarge_betaRemainder_le_density_of_exponent
    {S K Z : ℕ} (hS : 1 ≤ S) (hK : 5 ≤ K)
    (hExp : 4 * S * K ^ 2 ≤ Nat.log 2 Z) :
    (∑ I ∈ ({gsA10CanonicalLargeFirstBlock K,
        gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
        (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
  let L := Nat.log 2 Z
  let E : ℕ := (2 ^ (K ^ 2 * S)) ^ 2
  have hpowLog : 2 ^ L ≤ Z := by
    have hZ : Z ≠ 0 := by
      intro hZ
      subst Z
      have hpos : 0 < 4 * S * K ^ 2 := by positivity
      have hzero : 4 * S * K ^ 2 ≤ 0 := by simpa using hExp
      omega
    exact Nat.pow_log_le_self 2 hZ
  have hEeq : E ^ 2 = 2 ^ (4 * S * K ^ 2) := by
    dsimp only [E]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have hE2 : E ^ 2 ≤ Z := by
    rw [hEeq]
    exact (Nat.pow_le_pow_right (by omega) hExp).trans hpowLog
  have hKsq : 4 * K ^ 2 ≤ L := by
    calc
      4 * K ^ 2 ≤ 4 * S * K ^ 2 := by
        have hm := Nat.mul_le_mul_right (4 * K ^ 2) hS
        simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using hm
      _ ≤ L := hExp
  have hLZ : L ≤ Z := Nat.log_le_self 2 Z
  have htwoK2 : (2 * K) ^ 2 ≤ Z := by
    calc
      (2 * K) ^ 2 = 4 * K ^ 2 := by ring
      _ ≤ L := hKsq
      _ ≤ Z := hLZ
  have hEroot : E ≤ Nat.sqrt Z := (Nat.le_sqrt').2 hE2
  have hKroot : 2 * K ≤ Nat.sqrt Z := (Nat.le_sqrt').2 htwoK2
  have hproductNat : 2 * E * K ≤ Z := by
    calc
      2 * E * K = E * (2 * K) := by ring
      _ ≤ Nat.sqrt Z * Nat.sqrt Z := Nat.mul_le_mul hEroot hKroot
      _ ≤ Z := Nat.sqrt_le Z
  have hKpos : (0 : ℝ) < K := by positivity
  have hEcast : (2 : ℝ) * E ≤ (1 / (K : ℝ)) * Z := by
    have hproductReal : (2 : ℝ) * E * K ≤ Z := by
      exact_mod_cast hproductNat
    calc
      (2 : ℝ) * E ≤ (Z : ℝ) / K :=
        (le_div_iff₀ hKpos).2 hproductReal
      _ = (1 / (K : ℝ)) * Z := by ring
  have hconst : (1 : ℝ) ≤ gsA10CanonicalLargeLogRatioConstant :=
    one_le_gsA10CanonicalLargeLogRatioConstant
  calc
    (∑ I ∈ ({gsA10CanonicalLargeFirstBlock K,
        gsA10CanonicalLargeSecondBlock K} : Finset (ℕ × ℕ)),
      (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤ 2 * (E : ℝ) := by
      simpa only [E, Nat.cast_pow] using
        (sum_gsA10CanonicalLarge_betaRemainder_le (S := S) hK)
    _ ≤ (1 / (K : ℝ)) * Z := hEcast
    _ ≤ (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
      apply mul_le_mul_of_nonneg_right
      · exact div_le_div_of_nonneg_right hconst (by positivity)
      · positivity

/-- The source exponent automatically satisfies the beta-remainder
exponent condition once the maximal exponent is nonzero. -/
theorem four_mul_sourceBlockExponent_sq_le_log
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK0 : 1 ≤ gsA10CanonicalBlockExponent S Z) :
    4 * S * (gsA10SourceBlockExponent S Z) ^ 2 ≤ Nat.log 2 Z := by
  let K0 := gsA10CanonicalBlockExponent S Z
  let K := gsA10SourceBlockExponent S Z
  have hsqrt : K ^ 2 ≤ K0 := by
    dsimp only [K, gsA10SourceBlockExponent]
    exact Nat.sqrt_le' _
  have hself : K0 ≤ K0 ^ 2 := by nlinarith
  calc
    4 * S * K ^ 2 ≤ 4 * S * K0 := by gcongr
    _ ≤ 4 * S * K0 ^ 2 := by gcongr
    _ ≤ Nat.log 2 Z := by
      simpa only [K0] using
        (four_mul_mul_canonicalBlockExponent_sq_le_log (S := S) (Z := Z))

/-- Conversely, the binary logarithm is bounded by the fourth power of the
source exponent.  This is the floor-safe quantitative statement behind
`K ≍ (log Z)^(1/4)`. -/
theorem log_le_twoFiftySix_mul_sourceBlockExponent_fourth
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 1 ≤ gsA10SourceBlockExponent S Z) :
    Nat.log 2 Z ≤
      256 * S * (gsA10SourceBlockExponent S Z) ^ 4 := by
  let K0 := gsA10CanonicalBlockExponent S Z
  let K := gsA10SourceBlockExponent S Z
  have hK0log : Nat.log 2 Z ≤ 16 * S * K0 ^ 2 := by
    simpa only [K0] using
      (log_le_sixteen_mul_canonicalBlockExponent_sq
        (S := S) (Z := Z) hS (by
          have hsqrt : K ^ 2 ≤ K0 := by
            dsimp only [K, gsA10SourceBlockExponent]
            exact Nat.sqrt_le' _
          nlinarith [show 1 ≤ K by simpa only [K] using hK]))
  have hK0lt : K0 < (K + 1) ^ 2 := by
    dsimp only [K, gsA10SourceBlockExponent]
    exact Nat.lt_succ_sqrt' K0
  have hKsucc : K + 1 ≤ 2 * K := by
    simpa only [K] using (show
      gsA10SourceBlockExponent S Z + 1 ≤
        2 * gsA10SourceBlockExponent S Z by omega)
  have hK0 : K0 ≤ 4 * K ^ 2 := by
    calc
      K0 ≤ (K + 1) ^ 2 := hK0lt.le
      _ ≤ (2 * K) ^ 2 := by gcongr
      _ = 4 * K ^ 2 := by ring
  calc
    Nat.log 2 Z ≤ 16 * S * K0 ^ 2 := hK0log
    _ ≤ 16 * S * (4 * K ^ 2) ^ 2 := by gcongr
    _ = 256 * S * K ^ 4 := by ring

/-- The reciprocal source exponent has the expected negative quarter
power on the binary-logarithm scale.  The constant is deliberately loose
to keep all floor effects explicit. -/
theorem one_div_sourceBlockExponent_le_natLog_rpow_neg_quarter
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 1 ≤ gsA10SourceBlockExponent S Z) :
    (1 : ℝ) / gsA10SourceBlockExponent S Z ≤
      (256 * S : ℝ) *
        ((Nat.log 2 Z : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let L : ℝ := Nat.log 2 Z
  let K : ℝ := gsA10SourceBlockExponent S Z
  let c : ℝ := 256 * S
  have hLnat := log_le_twoFiftySix_mul_sourceBlockExponent_fourth
    (S := S) (Z := Z) hS hK
  have hL : L ≤ c * K ^ 4 := by
    dsimp only [L, c, K]
    exact_mod_cast hLnat
  have hExp := four_mul_sourceBlockExponent_sq_le_log
    (S := S) (Z := Z) hS (by
      have hsqrt : (gsA10SourceBlockExponent S Z) ^ 2 ≤
          gsA10CanonicalBlockExponent S Z := by
        unfold gsA10SourceBlockExponent
        exact Nat.sqrt_le' _
      nlinarith)
  have hLposNat : 0 < Nat.log 2 Z := by
    have hleft : 0 < 4 * S * (gsA10SourceBlockExponent S Z) ^ 2 := by
      positivity
    exact hleft.trans_le hExp
  have hLpos : 0 < L := by
    dsimp only [L]
    exact_mod_cast hLposNat
  have hKpos : 0 < K := by
    dsimp only [K]
    exact_mod_cast (show 0 < gsA10SourceBlockExponent S Z by omega)
  have hcgt : 1 < c := by
    dsimp only [c]
    have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
    norm_num
    nlinarith
  have hc0 : 0 ≤ c := zero_le_one.trans hcgt.le
  let w : ℝ := Real.sqrt (Real.sqrt L)
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwpos : 0 < w := Real.sqrt_pos.2 (Real.sqrt_pos.2 hLpos)
  have hw4 : w ^ 4 = L := by
    have houter : w ^ 2 = Real.sqrt L := by
      dsimp only [w]
      exact Real.sq_sqrt (Real.sqrt_nonneg L)
    have hinner : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    calc
      w ^ 4 = (w ^ 2) ^ 2 := by ring
      _ = (Real.sqrt L) ^ 2 := by rw [houter]
      _ = L := hinner
  have hcPow : c ≤ c ^ 4 := by
    simpa only [pow_one] using
      ((pow_le_pow_iff_right₀ hcgt).2 (by norm_num : (1 : ℕ) ≤ 4))
  have hwPow : w ^ 4 ≤ (c * K) ^ 4 := by
    calc
      w ^ 4 = L := hw4
      _ ≤ c * K ^ 4 := hL
      _ ≤ c ^ 4 * K ^ 4 := by
        exact mul_le_mul_of_nonneg_right hcPow (pow_nonneg hKpos.le _)
      _ = (c * K) ^ 4 := by ring
  have hw : w ≤ c * K :=
    le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (mul_nonneg hc0 hKpos.le) hwPow
  have hinv : (1 : ℝ) / K ≤ c / w := by
    apply (div_le_div_iff₀ hKpos hwpos).2
    simpa only [one_mul] using hw
  have hwRpow : w = L ^ (1 / 4 : ℝ) := by
    dsimp only [w]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hLpos.le]
    norm_num
  have hrewrite : c / w = c * L ^ (-(1 / 4 : ℝ)) := by
    rw [hwRpow, Real.rpow_neg hLpos.le]
    ring
  simpa only [L, K, c, Nat.cast_ofNat, Nat.cast_mul] using
    hinv.trans_eq hrewrite

/-- Binary and natural logarithms differ by an absolute factor also at
the negative-quarter-power scale needed by the source blocks. -/
theorem natLog_two_rpow_neg_quarter_le_realLog_rpow_neg_quarter
    {Z : ℕ} (hZ : 4 ≤ Z) :
    ((Nat.log 2 Z : ℝ) ^ (-(1 / 4 : ℝ))) ≤
      (1 + Real.sqrt (2 * Real.log 2)) *
        ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) := by
  let L : ℝ := Nat.log 2 Z
  let R : ℝ := Real.log (Z : ℝ)
  let d : ℝ := Real.sqrt (2 * Real.log 2)
  let c : ℝ := 1 + d
  have hLnat : 1 ≤ Nat.log 2 Z := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hL : 0 < L := by
    dsimp only [L]
    exact_mod_cast (show 0 < Nat.log 2 Z by omega)
  have hR : 0 < R := by
    dsimp only [R]
    exact Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcSq : d ≤ c ^ 2 := by
    dsimp only [c]
    nlinarith [sq_nonneg d]
  have hhalf := natLog_two_rpow_neg_half_le_realLog_rpow_neg_half hZ
  have hnegR : 0 ≤ R ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hR.le _
  have hsquares :
      (L ^ (-(1 / 4 : ℝ))) ^ 2 ≤
        (c * R ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have hleft : (L ^ (-(1 / 4 : ℝ))) ^ 2 =
        L ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      norm_num
    have hright : (c * R ^ (-(1 / 4 : ℝ))) ^ 2 =
        c ^ 2 * R ^ (-(1 / 2 : ℝ)) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
      norm_num
    rw [hleft, hright]
    calc
      L ^ (-(1 / 2 : ℝ)) ≤ d * R ^ (-(1 / 2 : ℝ)) := by
        simpa only [L, R, d] using hhalf
      _ ≤ c ^ 2 * R ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcSq hnegR
  have ha0 : 0 ≤ L ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hL.le _
  have hb0 : 0 ≤ c * R ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg hc0 (Real.rpow_nonneg hR.le _)
  have := (sq_le_sq₀ ha0 hb0).1 hsquares
  simpa only [L, R, c, d] using this

/-- The logarithmic width of the source-scale upper cutoff is bounded by
the reciprocal square root of the binary logarithm. -/
theorem log_sourceBlockCutoff_div_log_le_natLog_rpow_neg_half
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 1 ≤ gsA10SourceBlockExponent S Z) (hZ : 4 ≤ Z) :
    Real.log
          ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
        Real.log (Z : ℝ) ≤
      ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let L : ℕ := Nat.log 2 Z
  let K0 : ℕ := gsA10CanonicalBlockExponent S Z
  let K : ℕ := gsA10SourceBlockExponent S Z
  have hroot : K ^ 2 ≤ K0 := by
    dsimp only [K, gsA10SourceBlockExponent]
    exact Nat.sqrt_le' _
  have hExp0 := four_mul_mul_canonicalBlockExponent_sq_le_log
    (S := S) (Z := Z)
  have hK0sq : K0 ^ 2 ≤ L := by
    calc
      K0 ^ 2 ≤ 4 * S * K0 ^ 2 := by
        have hcoef : 1 ≤ 4 * S := by omega
        nlinarith
      _ ≤ L := by simpa only [K0, L] using hExp0
  have hK0sqrt : K0 ≤ Nat.sqrt L := (Nat.le_sqrt').2 hK0sq
  have hKsqrt : K ^ 2 ≤ Nat.sqrt L := hroot.trans hK0sqrt
  have hLnat : 1 ≤ L := by
    dsimp only [L]
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hnum :
      Real.log (((2 ^ (K ^ 2) : ℕ) : ℝ)) ≤
        Real.sqrt (L : ℝ) * Real.log 2 := by
    have hcast : ((K ^ 2 : ℕ) : ℝ) ≤ Real.sqrt (L : ℝ) := by
      calc
        ((K ^ 2 : ℕ) : ℝ) ≤ (Nat.sqrt L : ℕ) := by
          exact_mod_cast hKsqrt
        _ ≤ Real.sqrt (L : ℝ) := Real.nat_sqrt_le_real_sqrt
    rw [Nat.cast_pow, Real.log_pow]
    exact mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_pow] using hcast)
      hlogTwo.le
  have hden : (L : ℝ) * Real.log 2 ≤ Real.log (Z : ℝ) := by
    have hpow : 2 ^ L ≤ Z := Nat.pow_log_le_self 2 (by omega)
    calc
      (L : ℝ) * Real.log 2 = Real.log (((2 ^ L : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      _ ≤ Real.log (Z : ℝ) := by
        apply Real.strictMonoOn_log.monotoneOn
        · show (0 : ℝ) < (2 ^ L : ℕ)
          positivity
        · show (0 : ℝ) < Z
          positivity
        · exact_mod_cast hpow
  have hsqrtL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hLpos
  have hquot :
      Real.log (((2 ^ (K ^ 2) : ℕ) : ℝ)) / Real.log (Z : ℝ) ≤
        (Real.sqrt (L : ℝ) * Real.log 2) /
          ((L : ℝ) * Real.log 2) := by
    calc
      Real.log (((2 ^ (K ^ 2) : ℕ) : ℝ)) / Real.log (Z : ℝ) ≤
          (Real.sqrt (L : ℝ) * Real.log 2) / Real.log (Z : ℝ) :=
        div_le_div_of_nonneg_right hnum hlogZ.le
      _ ≤ (Real.sqrt (L : ℝ) * Real.log 2) /
          ((L : ℝ) * Real.log 2) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (Real.sqrt_nonneg _) hlogTwo.le)
          (mul_pos hLpos hlogTwo) hden
  calc
    Real.log
          ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
        Real.log (Z : ℝ) =
        Real.log (((2 ^ (K ^ 2) : ℕ) : ℝ)) / Real.log (Z : ℝ) := by rfl
    _ ≤ (Real.sqrt (L : ℝ) * Real.log 2) /
          ((L : ℝ) * Real.log 2) := hquot
    _ = 1 / Real.sqrt (L : ℝ) := by
      field_simp [hlogTwo.ne', hsqrtL.ne']
      exact Real.sq_sqrt hLpos.le
    _ = ((L : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hLpos.le]
      ring
    _ = ((Nat.log 2 Z : ℝ) ^ (-(1 / 2 : ℝ))) := by rfl

/-- Natural-log form of the source-cutoff width estimate. -/
theorem log_sourceBlockCutoff_div_log_le_realLog_rpow_neg_half
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 1 ≤ gsA10SourceBlockExponent S Z) (hZ : 4 ≤ Z) :
    Real.log
          ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
        Real.log (Z : ℝ) ≤
      Real.sqrt (2 * Real.log 2) *
        ((Real.log (Z : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  exact (log_sourceBlockCutoff_div_log_le_natLog_rpow_neg_half
    hS hK hZ).trans
      (natLog_two_rpow_neg_half_le_realLog_rpow_neg_half hZ)

/-- The joint near-projection scalar and any nonnegative multiple of the
global-secondary ratio are uniformly of negative-quarter logarithmic
size at the source-scale blocks. -/
theorem jointNearProjection_add_secondary_sourceBlock_le_realLog_quarter
    {S Z : ℕ} {Csecondary : ℝ} (hCsecondary : 0 ≤ Csecondary)
    (hS : 1 ≤ S) (hK : 1 ≤ gsA10SourceBlockExponent S Z)
    (hZ : 4 ≤ Z) :
    4 * (harmonic Z : ℝ) *
          Real.log
            ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
          (Real.log (Z : ℝ)) ^ 2 +
        Real.log
            ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
          (2 * (Z : ℝ)) +
        Csecondary *
          (Real.log
              ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) /
            Real.log (Z : ℝ)) ≤
      (9 + Csecondary) * Real.sqrt (2 * Real.log 2) *
        ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) := by
  let y : ℕ := 2 ^ ((gsA10SourceBlockExponent S Z) ^ 2)
  let R : ℝ := Real.log (Z : ℝ)
  let L : ℝ := Real.log (y : ℝ)
  let d : ℝ := Real.sqrt (2 * Real.log 2)
  have hRpos : 0 < R := by
    dsimp only [R]
    exact Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hRone : 1 ≤ R := by
    have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
      exact ((Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).2
        (Real.exp_one_lt_three.trans (by norm_num))).le
    exact hlog4.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num [Set.mem_Ioi]) (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hZ))
  have hL0 : 0 ≤ L := by
    dsimp only [L, y]
    exact Real.log_nonneg (by
      norm_cast
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
  have hratio0 : 0 ≤ L / R := div_nonneg hL0 hRpos.le
  have hratio : L / R ≤ d * R ^ (-(1 / 2 : ℝ)) := by
    simpa only [L, R, d, y] using
      (log_sourceBlockCutoff_div_log_le_realLog_rpow_neg_half hS hK hZ)
  have hharmonic : (harmonic Z : ℝ) ≤ 2 * R := by
    calc
      (harmonic Z : ℝ) ≤ 1 + Real.log (Z : ℝ) := harmonic_le_one_add_log Z
      _ ≤ 2 * R := by dsimp only [R]; linarith
  have hfirst :
      4 * (harmonic Z : ℝ) * L / R ^ 2 ≤ 8 * (L / R) := by
    have hRne : R ≠ 0 := hRpos.ne'
    rw [show 4 * (harmonic Z : ℝ) * L / R ^ 2 =
      4 * ((harmonic Z : ℝ) / R) * (L / R) by field_simp]
    have hHR : (harmonic Z : ℝ) / R ≤ 2 :=
      (div_le_iff₀ hRpos).2 (by simpa only [mul_comm] using hharmonic)
    have hfour : 4 * ((harmonic Z : ℝ) / R) ≤ 8 := by nlinarith
    exact mul_le_mul_of_nonneg_right hfour hratio0
  have hRZ : R ≤ 2 * (Z : ℝ) := by
    have hZR : R ≤ (Z : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Z)
      linarith
    exact hZR.trans (by
      have hZ0 : (0 : ℝ) ≤ Z := by positivity
      linarith)
  have hsecond : L / (2 * (Z : ℝ)) ≤ L / R := by
    exact div_le_div_of_nonneg_left hL0 hRpos hRZ
  have hnear :
      4 * (harmonic Z : ℝ) * L / R ^ 2 + L / (2 * (Z : ℝ)) ≤
        9 * (L / R) := by
    calc
      4 * (harmonic Z : ℝ) * L / R ^ 2 + L / (2 * (Z : ℝ)) ≤
          8 * (L / R) + L / R := add_le_add hfirst hsecond
      _ = 9 * (L / R) := by ring
  have hcombined :
      4 * (harmonic Z : ℝ) * L / R ^ 2 + L / (2 * (Z : ℝ)) +
          Csecondary * (L / R) ≤
        (9 + Csecondary) * (d * R ^ (-(1 / 2 : ℝ))) := by
    calc
      4 * (harmonic Z : ℝ) * L / R ^ 2 + L / (2 * (Z : ℝ)) +
          Csecondary * (L / R) ≤
          9 * (L / R) + Csecondary * (L / R) :=
        add_le_add hnear le_rfl
      _ = (9 + Csecondary) * (L / R) := by ring
      _ ≤ (9 + Csecondary) * (d * R ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
  have hweaken : R ^ (-(1 / 2 : ℝ)) ≤ R ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hRone (by norm_num)
  have hcoef0 : 0 ≤ (9 + Csecondary) * d := by
    dsimp only [d]
    positivity
  have hfinal := hcombined.trans (by
    calc
      (9 + Csecondary) * (d * R ^ (-(1 / 2 : ℝ))) =
          ((9 + Csecondary) * d) * R ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ ((9 + Csecondary) * d) * R ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hweaken hcoef0
      _ = (9 + Csecondary) * d * R ^ (-(1 / 4 : ℝ)) := by ring)
  simpa only [L, R, d, y] using hfinal

/-- The reciprocal alpha--beta window width is also of negative-quarter
logarithmic size at the source-scale blocks. -/
theorem inv_log_sourceBlockCutoff_le_realLog_quarter
    {S Z : ℕ} (hS : 1 ≤ S)
    (hK : 5 ≤ gsA10SourceBlockExponent S Z) (hZ : 4 ≤ Z) :
    (Real.log
      ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ))⁻¹ ≤
      (256 * S : ℝ) * (1 + Real.sqrt (2 * Real.log 2)) *
        ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) := by
  let K : ℕ := gsA10SourceBlockExponent S Z
  let L : ℝ := Nat.log 2 Z
  let y : ℕ := 2 ^ (K ^ 2)
  have hKpos : (0 : ℝ) < K := by positivity
  have hlogTwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hone : (1 : ℝ) ≤ K * Real.log 2 := by
    have hKR : (5 : ℝ) ≤ K := by exact_mod_cast (show 5 ≤ K by simpa only [K] using hK)
    nlinarith [Real.log_two_gt_d9]
  have hlogy : (K : ℝ) ≤ Real.log (y : ℝ) := by
    dsimp only [y]
    rw [Nat.cast_pow, Real.log_pow]
    have hfactor : (K : ℝ) ≤ K * (K * Real.log 2) := by
      calc
        (K : ℝ) = K * 1 := by ring
        _ ≤ K * (K * Real.log 2) :=
          mul_le_mul_of_nonneg_left hone hKpos.le
    norm_num
    simpa only [Nat.cast_pow, pow_two, mul_assoc] using hfactor
  have hloginv : (Real.log (y : ℝ))⁻¹ ≤ (1 : ℝ) / K := by
    simpa only [one_div] using inv_anti₀ hKpos hlogy
  have honeK := one_div_sourceBlockExponent_le_natLog_rpow_neg_quarter
    (S := S) (Z := Z) hS (by omega)
  have hconvert := natLog_two_rpow_neg_quarter_le_realLog_rpow_neg_quarter hZ
  have hcoef : 0 ≤ (256 * S : ℝ) := by positivity
  calc
    (Real.log
      ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ))⁻¹ =
        (Real.log (y : ℝ))⁻¹ := by rfl
    _ ≤ (1 : ℝ) / K := hloginv
    _ ≤ (256 * S : ℝ) * (L ^ (-(1 / 4 : ℝ))) := by
      simpa only [K, L] using honeK
    _ ≤ (256 * S : ℝ) *
        ((1 + Real.sqrt (2 * Real.log 2)) *
          (Real.log (Z : ℝ) ^ (-(1 / 4 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (by simpa only [L] using hconvert) hcoef
    _ = (256 * S : ℝ) * (1 + Real.sqrt (2 * Real.log 2)) *
        (Real.log (Z : ℝ) ^ (-(1 / 4 : ℝ))) := by ring

/-- A concrete threshold guaranteeing that the source exponent is at
least five. -/
theorem five_le_gsA10SourceBlockExponent
    {S Z : ℕ} (hS : 1 ≤ S) (hZ : 2 ^ (2500 * S) ≤ Z) :
    5 ≤ gsA10SourceBlockExponent S Z := by
  have hK0 : 25 ≤ gsA10CanonicalBlockExponent S Z := by
    have hlog : 2500 * S ≤ Nat.log 2 Z :=
      Nat.le_log_of_pow_le (by omega) hZ
    have hden : 0 < 4 * S := by positivity
    have hdiv : 625 ≤ Nat.log 2 Z / (4 * S) := by
      rw [Nat.le_div_iff_mul_le hden]
      nlinarith
    rw [gsA10CanonicalBlockExponent, Nat.le_sqrt']
    norm_num
    exact hdiv
  rw [gsA10SourceBlockExponent, Nat.le_sqrt']
  norm_num
  exact hK0

/-- The source-scale upper cutoff dominates every fourth logarithmic power,
the exact size hypothesis in the joint Perron projection theorem. -/
theorem eventually_log_pow_four_le_gsA10SourceBlockCutoff (S : ℕ)
    (hS : 1 ≤ S) :
    ∀ᶠ Z : ℕ in atTop,
      Real.log (Z : ℝ) ^ 4 ≤
        ((2 ^ ((gsA10SourceBlockExponent S Z) ^ 2) : ℕ) : ℝ) := by
  let c : ℝ := Real.log 2 / (16 * S)
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hpoly := isLittleO_rpow_exp_pos_mul_atTop 8 hc
  have hpolyNat : (fun r : ℝ ↦ r ^ (8 : ℕ)) =o[atTop]
      (fun r : ℝ ↦ Real.exp (c * r)) := by
    convert hpoly using 1
    funext r
    exact (Real.rpow_natCast r 8).symm
  have hcomp := hpolyNat.comp_tendsto tendsto_sqrt_natLog_two_atTop
  have hbound := hcomp.bound (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards
      [hbound,
       tendsto_natLog_two_natCast_atTop.eventually (eventually_ge_atTop 1),
       eventually_ge_atTop (2 ^ (2500 * S))]
      with Z hsmall hLone hcut
  let L : ℕ := Nat.log 2 Z
  let K : ℕ := gsA10SourceBlockExponent S Z
  let r : ℝ := Real.sqrt (L : ℝ)
  have hLnat : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast hLone
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = (L : ℝ) := by
    dsimp only [r]
    exact Real.sq_sqrt hLpos.le
  have hKfive : 5 ≤ K := by
    simpa only [K] using five_le_gsA10SourceBlockExponent hS hcut
  have hK : 1 ≤ K := by omega
  have hlogUpper := log_le_twoFiftySix_mul_sourceBlockExponent_fourth
    (S := S) (Z := Z) hS (by simpa only [K] using hK)
  have hrK : r ≤ (16 * S : ℝ) * K ^ 2 := by
    have hreal : (L : ℝ) ≤ (256 * S : ℝ) * (K : ℝ) ^ 4 := by
      exact_mod_cast hlogUpper
    have hright0 : 0 ≤ (16 * S : ℝ) * (K : ℝ) ^ 2 := by positivity
    apply (sq_le_sq₀ hr0 hright0).1
    rw [hrSq]
    calc
      (L : ℝ) ≤ (256 * S : ℝ) * (K : ℝ) ^ 4 := hreal
      _ ≤ ((16 * S : ℝ) * (K : ℝ) ^ 2) ^ 2 := by
        have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
        nlinarith [sq_nonneg ((K : ℝ) ^ 2)]
  have hcr : c * r ≤ (K : ℝ) ^ 2 * Real.log 2 := by
    calc
      c * r ≤ c * ((16 * S : ℝ) * (K : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hrK hc.le
      _ = (K : ℝ) ^ 2 * Real.log 2 := by
        dsimp only [c]
        have hden : (16 * (S : ℝ)) ≠ 0 := by positivity
        field_simp [hden]
  have hZne : Z ≠ 0 := by
    intro hZ
    subst Z
    simp [L] at hLnat
  have hpowUpper : Z < 2 ^ (L + 1) := by
    simpa only [L, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) Z)
  have hlogZ : Real.log (Z : ℝ) ≤ 2 * (L : ℝ) := by
    have hmono : Real.log (Z : ℝ) ≤
        Real.log (((2 ^ (L + 1) : ℕ) : ℝ)) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        exact_mod_cast (Nat.pos_of_ne_zero hZne)
      · simp only [Set.mem_Ioi]
        positivity
      · exact_mod_cast hpowUpper.le
    calc
      Real.log (Z : ℝ) ≤ Real.log (((2 ^ (L + 1) : ℕ) : ℝ)) := hmono
      _ = ((L + 1 : ℕ) : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      _ ≤ 2 * (L : ℝ) := by
        have hlogTwo : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          norm_num at h ⊢
          exact h
        have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hLnat
        norm_num
        nlinarith
  have hlogPow : Real.log (Z : ℝ) ^ 4 ≤ 16 * r ^ 8 := by
    have hlog0 : 0 ≤ Real.log (Z : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by omega))
    have hp := pow_le_pow_left₀ hlog0 hlogZ 4
    calc
      Real.log (Z : ℝ) ^ 4 ≤ (2 * (L : ℝ)) ^ 4 := hp
      _ = 16 * r ^ 8 := by rw [← hrSq]; ring
  have hsmall' : 16 * r ^ 8 ≤ Real.exp (c * r) := by
    have hnorm : r ^ 8 ≤ (1 / 16 : ℝ) * Real.exp (c * r) := by
      simpa only [Function.comp_apply, L, r, Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg hr0 _), abs_of_pos (Real.exp_pos _)] using hsmall
    nlinarith
  have hexp : Real.exp (c * r) ≤ ((2 ^ (K ^ 2) : ℕ) : ℝ) := by
    calc
      Real.exp (c * r) ≤ Real.exp ((K : ℝ) ^ 2 * Real.log 2) :=
        Real.exp_le_exp.mpr hcr
      _ = ((2 ^ (K ^ 2) : ℕ) : ℝ) := by
        rw [show (K : ℝ) ^ 2 = ((K ^ 2 : ℕ) : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  exact hlogPow.trans (hsmall'.trans (by simpa only [K] using hexp))

/-- Eventually the reciprocal-prime prefix is smaller than the natural
logarithm.  This elementary corollary of the explicit Mertens upper bound is
the exact prime-mass hypothesis used by the joint A.10 projection. -/
theorem eventually_primeReciprocals_le_realLog :
    ∀ᶠ Z : ℕ in atTop,
      PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) := by
  filter_upwards
      [PrimeEstimates.eventually_primeReciprocals_le_139,
       Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 16)] with Z hprime hlog
  let L : ℝ := Real.log (Z : ℝ)
  have hL : 16 ≤ L := by simpa only [L] using hlog
  have hL0 : 0 ≤ L := by linarith
  have hsqrtSq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hsqrt : 4 ≤ Real.sqrt L := by
    nlinarith [Real.sqrt_nonneg L]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have h := Real.log_le_rpow_div hL0 (by norm_num : (0 : ℝ) < 1 / 2)
    calc
      Real.log L ≤ L ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt L := by rw [Real.sqrt_eq_rpow]; ring
  calc
    PrimeEstimates.primeReciprocals Z ≤
        (139 / 100 : ℝ) * Real.log L := by simpa only [L] using hprime
    _ ≤ L := by nlinarith [sq_nonneg (Real.sqrt L - 4)]
    _ = Real.log (Z : ℝ) := rfl

/-- A single eventual threshold supplies every source-scale size hypothesis
needed by the generic real ordinary-prefix A.10 theorem. -/
theorem eventually_gsA10SourceBlock_structural (S : ℕ) (hS : 1 ≤ S) :
    ∀ᶠ Z : ℕ in atTop,
      let K := gsA10SourceBlockExponent S Z
      let y := 2 ^ (K ^ 2)
      5 ≤ K ∧ 23 ≤ y ∧ y ≤ Z ∧
        1 ≤ Real.log (Z : ℝ) ∧
        6 ≤ Real.log (y : ℝ) ∧
        Real.log (Z : ℝ) ^ 2 ≤ Z ∧
        PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) ∧
        Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) := by
  filter_upwards
      [eventually_ge_atTop (2 ^ (2500 * S)),
       Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
        (eventually_ge_atTop 16),
       MRHalaszBands.eventually_log_pow_div_self_le 2
        (by norm_num : (0 : ℝ) < 1),
       eventually_primeReciprocals_le_realLog,
       eventually_log_pow_four_le_gsA10SourceBlockCutoff S hS]
      with Z hcut hlog hlogSqRatio hprime hlogFour
  let K := gsA10SourceBlockExponent S Z
  let y := 2 ^ (K ^ 2)
  have hK : 5 ≤ K := by
    simpa only [K] using five_le_gsA10SourceBlockExponent hS hcut
  have hK0 : 1 ≤ gsA10CanonicalBlockExponent S Z := by
    have hsqrt : K ^ 2 ≤ gsA10CanonicalBlockExponent S Z := by
      dsimp only [K, gsA10SourceBlockExponent]
      exact Nat.sqrt_le' _
    nlinarith
  have hExp := four_mul_sourceBlockExponent_sq_le_log hS hK0
  have hKsqLog : K ^ 2 ≤ Nat.log 2 Z := by
    have hle : K ^ 2 ≤ 4 * S * K ^ 2 := by
      have hS' : 1 ≤ S := hS
      nlinarith
    exact hle.trans (by simpa only [K] using hExp)
  have hZne : Z ≠ 0 := by
    intro hZ
    subst Z
    norm_num at hcut
  have hyZ : y ≤ Z := by
    calc
      y = 2 ^ (K ^ 2) := rfl
      _ ≤ 2 ^ (Nat.log 2 Z) := Nat.pow_le_pow_right (by omega) hKsqLog
      _ ≤ Z := Nat.pow_log_le_self 2 hZne
  have hy : 23 ≤ y := by
    have hpow : 2 ^ 25 ≤ y := by
      dsimp only [y]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    norm_num at hpow ⊢
    omega
  have hlogy : 6 ≤ Real.log (y : ℝ) := by
    have hpow : 2 ^ 25 ≤ y := by
      dsimp only [y]
      exact Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hmono : Real.log (((2 ^ 25 : ℕ) : ℝ)) ≤ Real.log (y : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        positivity
      · simp only [Set.mem_Ioi]
        positivity
      · exact_mod_cast hpow
    have hleft : (6 : ℝ) ≤ Real.log (((2 ^ 25 : ℕ) : ℝ)) := by
      rw [show (((2 ^ 25 : ℕ) : ℝ)) = (2 : ℝ) ^ 25 by norm_num,
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hleft.trans hmono
  have hlogSq : Real.log (Z : ℝ) ^ 2 ≤ Z := by
    exact (div_le_one (by positivity : (0 : ℝ) < Z)).mp hlogSqRatio
  exact ⟨hK, hy, hyZ, by linarith, hlogy, hlogSq, hprime,
    by simpa only [y, K] using hlogFour⟩

/-- Scheduled exceptional-density theorem at the genuine A.10 source
scale.  No desired-density premise remains. -/
theorem exists_gsA10SourceScale_scheduled_atypicalFactorizationSet_le :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (2500 * S) ≤ Z →
        let K := gsA10SourceBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
  obtain ⟨C, hC, S, hS, hcard⟩ :=
    exists_gsA10CanonicalLarge_atypicalFactorizationSet_le
  refine ⟨C, hC, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10SourceBlockExponent S Z
  have hK : 5 ≤ K := by
    simpa only [K] using five_le_gsA10SourceBlockExponent
      (S := S) (Z := Z) (by omega) hZ
  have hK0 : 1 ≤ gsA10CanonicalBlockExponent S Z := by
    have hsqrt : K ^ 2 ≤ gsA10CanonicalBlockExponent S Z := by
      dsimp only [K, gsA10SourceBlockExponent]
      exact Nat.sqrt_le' _
    nlinarith
  have hExp := four_mul_sourceBlockExponent_sq_le_log
    (S := S) (Z := Z) (by omega) hK0
  exact hcard K Z hK
    (sum_gsA10CanonicalLarge_betaRemainder_le_density_of_exponent
      (S := S) (K := K) (Z := Z) (by omega) hK (by simpa only [K] using hExp))

/-- Source-scale canonical blocks have negative-quarter-power exceptional
density in the natural logarithm. -/
theorem exists_gsA10SourceScale_scheduled_atypicalFactorizationSet_le_realLog_quarter :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ Z : ℕ, 2 ^ (2500 * S) ≤ Z →
        let K := gsA10SourceBlockExponent S Z
        ((atypicalFactorizationSet
            {gsA10CanonicalLargeFirstBlock K,
              gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
          C * ((Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) * Z := by
  obtain ⟨C0, hC0, S, hS, hbase⟩ :=
    exists_gsA10SourceScale_scheduled_atypicalFactorizationSet_le
  let F : ℝ := gsA10CanonicalLargeLogRatioConstant * (256 * S) *
    (1 + Real.sqrt (2 * Real.log 2))
  let C : ℝ := C0 * F
  have hlarge : 0 < gsA10CanonicalLargeLogRatioConstant :=
    zero_lt_one.trans_le one_le_gsA10CanonicalLargeLogRatioConstant
  have hF : 0 < F := by
    dsimp only [F]
    positivity
  refine ⟨C, mul_pos hC0 hF, S, hS, ?_⟩
  intro Z hZ
  dsimp only
  let K := gsA10SourceBlockExponent S Z
  have hK : 5 ≤ K := by
    simpa only [K] using five_le_gsA10SourceBlockExponent
      (S := S) (Z := Z) (by omega) hZ
  have hZfour : 4 ≤ Z := by
    have hpow : 4 ≤ 2 ^ (2500 * S) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2500 * S) := Nat.pow_le_pow_right (by omega) (by omega)
    exact hpow.trans hZ
  have hone := one_div_sourceBlockExponent_le_natLog_rpow_neg_quarter
    (S := S) (Z := Z) (by omega) (by simpa only [K] using (show 1 ≤ K by omega))
  have hconvert := natLog_two_rpow_neg_quarter_le_realLog_rpow_neg_quarter hZfour
  have hratio : gsA10CanonicalLargeLogRatioConstant / K ≤
      F * (Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ)) := by
    have hnat0 : 0 ≤ (Nat.log 2 Z : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have hreal0 : 0 ≤ Real.log (Z : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_nonneg (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ Z by omega))) _
    calc
      gsA10CanonicalLargeLogRatioConstant / K =
          gsA10CanonicalLargeLogRatioConstant * ((1 : ℝ) / K) := by ring
      _ ≤ gsA10CanonicalLargeLogRatioConstant *
          ((256 * S : ℝ) *
            ((Nat.log 2 Z : ℝ) ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (by simpa only [K] using hone) hlarge.le
      _ ≤ gsA10CanonicalLargeLogRatioConstant *
          ((256 * S : ℝ) *
            ((1 + Real.sqrt (2 * Real.log 2)) *
              (Real.log (Z : ℝ) ^ (-(1 / 4 : ℝ))))) := by
        gcongr
      _ = F * (Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ)) := by
        dsimp only [F]
        ring
  have hcard := hbase Z hZ
  dsimp only at hcard
  calc
    ((atypicalFactorizationSet
        {gsA10CanonicalLargeFirstBlock K,
          gsA10CanonicalLargeSecondBlock K} Z).card : ℝ) ≤
        C0 * (gsA10CanonicalLargeLogRatioConstant / K) * Z := by
      simpa only [K] using hcard
    _ ≤ C0 *
        (F * (Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ))) * Z := by
      gcongr
    _ = C * (Real.log (Z : ℝ)) ^ (-(1 / 4 : ℝ)) * Z := by
      dsimp only [C]
      ring

end

end Erdos67

#print axioms Erdos67.sum_gsA10CanonicalLarge_betaRemainder_le_density_of_exponent
#print axioms Erdos67.exists_gsA10SourceScale_scheduled_atypicalFactorizationSet_le
