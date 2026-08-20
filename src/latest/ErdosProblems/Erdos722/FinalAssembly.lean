import ErdosProblems.Erdos722.AsymptoticAssembly

namespace Erdos722

open Finset Filter
open Erdos722.GeneratorAsymptotic

noncomputable section

/-- The edge multiplicity of the simultaneous rotation certificate has a
very small positive exponent. -/
theorem eventually_twoCapMultiplicity_cast_le_rpow
    (k r b : ℕ) (hrk : r < k) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      ∀ u : ℕ,
        u ≤ sectionSixColorLoadCoefficient hrk *
          SlowRotationBanks.rotationBankCount (2 * b) n →
        (twoCapDecoderInputMultiplicity k r
          (generatorEdgeCap (2 * b) n) u : ℝ) ≤
            (n : ℝ) ^ (1 / (1000 * b : ℕ) : ℝ) := by
  let C := sectionSixColorLoadCoefficient hrk + 1 + 2 ^ (k + r)
  let a : ℝ := 1 / (10000 * (2 * b) : ℕ) +
    1 / (1000 * (2 * b) : ℕ)
  let target : ℝ := 1 / (1000 * b : ℕ)
  have hat : a < target := by
    dsimp [a, target]
    push_cast
    field_simp
    nlinarith
  have hconst := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (C : ℝ)) hat (by positivity : (0 : ℝ) ≤ (C : ℕ))
  have hbankPos : ∀ᶠ n : ℕ in atTop,
      0 < SlowRotationBanks.rotationBankCount (2 * b) n := by
    have ht := Asymptotics.rationalPowerThreshold_tendsto_atTop
      (show 0 < (1 : ℕ) by omega)
      (show 0 < 10000 * (2 * b) by positivity)
    simpa [SlowRotationBanks.rotationBankCount] using
      ht.eventually (eventually_gt_atTop 0)
  have hedgePos := generatorEdgeCap_pos_eventually
    (show 0 < 2 * b by positivity)
  filter_upwards [hconst, hbankPos, hedgePos,
      eventually_ge_atTop 1] with n hconst hbankPos hedgePos hn
  intro u hu
  let g := SlowRotationBanks.rotationBankCount (2 * b) n
  let e := generatorEdgeCap (2 * b) n
  let c := 1 + 2 ^ (k + r)
  have hxnat : twoCapDecoderInputMultiplicity k r e u ≤ C * g * e := by
    calc
      twoCapDecoderInputMultiplicity k r e u = u * e + c := by
        unfold twoCapDecoderInputMultiplicity
        dsimp [c]
        omega
      _ ≤ sectionSixColorLoadCoefficient hrk * g * e + c := by
        gcongr
      _ ≤ sectionSixColorLoadCoefficient hrk * g * e + c * (g * e) := by
        apply Nat.add_le_add_left
        calc
          c = c * 1 := by simp
          _ ≤ c * (g * e) := Nat.mul_le_mul_left c
            (Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (Nat.ne_of_gt hbankPos)
                (Nat.ne_of_gt hedgePos)))
      _ = C * g * e := by
        dsimp [C]
        ring
  have hbank : (g : ℝ) ≤
      (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) := by
    simpa [g, SlowRotationBanks.rotationBankCount] using
      Asymptotics.rationalPowerThreshold_cast_le 1 (10000 * (2 * b)) n
  have hedge : (e : ℝ) ≤
      (n : ℝ) ^ (1 / (1000 * (2 * b) : ℕ) : ℝ) := by
    simpa [e, generatorEdgeCap] using
      Asymptotics.rationalPowerThreshold_cast_le 1 (1000 * (2 * b)) n
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (twoCapDecoderInputMultiplicity k r e u : ℝ) ≤ (C * g * e : ℕ) := by
      exact_mod_cast hxnat
    _ = (C : ℝ) * g * e := by norm_num
    _ ≤ (C : ℝ) *
        (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) *
        (n : ℝ) ^ (1 / (1000 * (2 * b) : ℕ) : ℝ) := by
      gcongr
    _ = (C : ℝ) *
        ((n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) *
          (n : ℝ) ^ (1 / (1000 * (2 * b) : ℕ) : ℝ)) := by ring
    _ = (C : ℝ) * (n : ℝ) ^ a := by
      rw [← Real.rpow_add hnpos]
    _ ≤ (n : ℝ) ^ target := hconst

/-- The source-boundary cap and the first exchange's free-edge cap fit
under the slightly more permissive stage path cap. -/
theorem eventually_decoderInputCap_add_exchangePathCap_le_stagePathCap
    (k r v F b : ℕ) (hr : 0 < r) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      LocalDecoderAsymptotic.decoderInputCap (9 * b) n +
          F * LocalDecoderAsymptotic.decoderPathCap v r (9 * b) n ≤
        LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n := by
  let Mv := LocalDecoderAsymptotic.decoderPathMultiplier v r
  let C := 1 + F * Mv
  let source : ℝ := ((18 * b - 1 : ℕ) : ℝ) / (18 * b : ℕ)
  let target : ℝ := ((20 * b - 1 : ℕ) : ℝ) / (20 * b : ℕ)
  have hsourceTarget : source < target := by
    dsimp [source, target]
    rw [Nat.cast_sub (by omega : 1 ≤ 18 * b),
      Nat.cast_sub (by omega : 1 ≤ 20 * b)]
    push_cast
    field_simp
    nlinarith
  have hconst := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (2 * C : ℕ)) hsourceTarget
      (by positivity : (0 : ℝ) ≤ (2 * C : ℕ))
  have htargetFloor :=
    Asymptotics.eventually_half_rpow_le_rationalPowerThreshold
      (E := 20 * b - 1) (d := 20 * b) (by omega) (by positivity)
  filter_upwards [hconst, htargetFloor,
      eventually_ge_atTop 1] with n hconst htargetFloor hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hinput := LocalDecoderAsymptotic.decoderInputCap_cast_le (9 * b) n
  have hpath := LocalDecoderAsymptotic.decoderPathScale_cast_le (9 * b) n
  have hpathSource :
      (LocalDecoderAsymptotic.decoderPathScale (9 * b) n : ℝ) ≤
        (n : ℝ) ^ source := by
    simpa only [source, show 2 * (9 * b) = 18 * b by omega] using hpath
  have hinputSource :
      (LocalDecoderAsymptotic.decoderInputCap (9 * b) n : ℝ) ≤
        (n : ℝ) ^ source := by
    calc
      (LocalDecoderAsymptotic.decoderInputCap (9 * b) n : ℝ) ≤
          (n : ℝ) ^ (((9 * b - 1 : ℕ) : ℝ) / (9 * b : ℕ)) := hinput
      _ ≤ (n : ℝ) ^ source := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        dsimp [source]
        rw [Nat.cast_sub (by omega : 1 ≤ 9 * b),
          Nat.cast_sub (by omega : 1 ≤ 18 * b)]
        push_cast
        field_simp
        nlinarith
  have hsum :
      (LocalDecoderAsymptotic.decoderInputCap (9 * b) n +
          F * LocalDecoderAsymptotic.decoderPathCap v r (9 * b) n : ℕ) ≤
        (n : ℝ) ^ target / 2 := by
    norm_num only [Nat.cast_add, Nat.cast_mul]
    calc
      (LocalDecoderAsymptotic.decoderInputCap (9 * b) n : ℝ) +
          (F : ℝ) * LocalDecoderAsymptotic.decoderPathCap v r (9 * b) n ≤
        (n : ℝ) ^ source + (F * Mv : ℕ) * (n : ℝ) ^ source := by
          simp only [LocalDecoderAsymptotic.decoderPathCap,
            Mv, Nat.cast_mul]
          apply add_le_add hinputSource
          calc
            (F : ℝ) * ((Mv : ℝ) *
                LocalDecoderAsymptotic.decoderPathScale (9 * b) n) ≤
              (F : ℝ) * ((Mv : ℝ) * (n : ℝ) ^ source) := by
                gcongr
            _ = (F : ℝ) * (Mv : ℝ) * (n : ℝ) ^ source := by ring
      _ = (C : ℝ) * (n : ℝ) ^ source := by
        dsimp [C]
        push_cast
        ring
      _ ≤ (n : ℝ) ^ target / 2 := by
        have h := hconst
        norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
        linarith
  have htarget : (n : ℝ) ^ target / 2 ≤
      (LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n : ℝ) := by
    calc
      (n : ℝ) ^ target / 2 ≤
          (Asymptotics.rationalPowerThreshold
            (20 * b - 1) (20 * b) n : ℝ) := by
        simpa [target] using htargetFloor
      _ ≤ (LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n : ℝ) := by
        simp only [LocalDecoderAsymptotic.decoderPathCap,
          LocalDecoderAsymptotic.decoderPathScale]
        have hM : 1 ≤ LocalDecoderAsymptotic.decoderPathMultiplier k r := by
          apply Nat.one_le_iff_ne_zero.mpr
          simp [LocalDecoderAsymptotic.decoderPathMultiplier,
            LocalDecoderAsymptotic.decoderBaselineConstant,
            LocalDecoderAsymptotic.decoderScheduleConstant,
            Nat.ne_of_gt hr]
        have hnat :
            Asymptotics.rationalPowerThreshold
                (20 * b - 1) (20 * b) n ≤
              LocalDecoderAsymptotic.decoderPathMultiplier k r *
                Asymptotics.rationalPowerThreshold
                  (20 * b - 1) (20 * b) n :=
          Nat.le_mul_of_pos_left _ hM
        simpa only [show 2 * (10 * b) = 20 * b by omega] using
          (show
            (Asymptotics.rationalPowerThreshold
                (20 * b - 1) (20 * b) n : ℝ) ≤
              (LocalDecoderAsymptotic.decoderPathMultiplier k r *
                Asymptotics.rationalPowerThreshold
                  (20 * b - 1) (20 * b) n : ℕ) by exact_mod_cast hnat)
  exact_mod_cast hsum.trans htarget

/-- Uniform version of the subpolynomial flattening-round loss for every
input bounded by the crude ground-set power. -/
theorem eventually_pow_flattenRoundCount_of_le_ground_pow
    (A k : ℕ) (hA : 0 < A) (hk : 0 < k)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : ℕ, x ≤ n ^ k →
        (A ^ flattenRoundCount x : ℝ) ≤ (n : ℝ) ^ s := by
  let C : ℝ := (A : ℝ) * ((8 : ℝ) * k) ^ A
  have hC : 0 < C := by positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (A : ℝ) hs).bound
      (show 0 < C⁻¹ by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 2] with n hsmall hn
  intro x hx
  have hnpos : 0 < n := by omega
  let L := Nat.log 2 (n ^ k)
  have hLpos : 0 < L := by
    rw [Nat.log_pos_iff]
    constructor
    · have hnk : 2 ≤ n ^ k := by
        calc
          2 = 2 ^ 1 := by simp
          _ ≤ n ^ 1 := Nat.pow_le_pow_left hn 1
          _ ≤ n ^ k := Nat.pow_le_pow_right hnpos hk
      exact hnk
    · omega
  have hround : flattenRoundCount x ≤ Nat.clog 2 L + 1 := by
    apply (flattenRoundCount_le_clog_log x).trans
    apply Nat.add_le_add_right
    apply Nat.clog_mono_right
    exact Nat.log_mono_right hx
  have hnat : A ^ flattenRoundCount x ≤
      A * (2 * (k * (Nat.log 2 n + 1))) ^ A := by
    calc
      A ^ flattenRoundCount x ≤ A ^ (Nat.clog 2 L + 1) :=
        Nat.pow_le_pow_right hA hround
      _ ≤ A * (2 * L) ^ A := pow_clog_succ_le_poly A L hA hLpos
      _ ≤ A * (2 * (k * (Nat.log 2 n + 1))) ^ A := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        exact Nat.mul_le_mul_left 2 (log_pow_le_mul_succ_log n k hnpos)
  have hcast : (A * (2 * (k * (Nat.log 2 n + 1))) ^ A : ℕ) ≤
      C * Real.log n ^ A := by
    have hlog := natLog_two_add_one_cast_le_four_log hn
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
      at hlog ⊢
    dsimp [C]
    have hbase :
        (2 : ℝ) * ((k : ℝ) * ((Nat.log 2 n : ℝ) + 1)) ≤
          (8 : ℝ) * k * Real.log n := by
      have hkreal : (0 : ℝ) ≤ k := by positivity
      calc
        (2 : ℝ) * ((k : ℝ) * ((Nat.log 2 n : ℝ) + 1)) ≤
            2 * ((k : ℝ) * (4 * Real.log n)) := by gcongr
        _ = (8 : ℝ) * k * Real.log n := by ring
    calc
      (A : ℝ) *
          ((2 : ℝ) * ((k : ℝ) * ((Nat.log 2 n : ℝ) + 1))) ^ A ≤
          (A : ℝ) * ((8 : ℝ) * k * Real.log n) ^ A := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hbase A) (by positivity)
      _ = C * Real.log n ^ A := by
        dsimp [C]
        rw [mul_pow]
        ring
  have hsmall' : C * Real.log (n : ℝ) ^ (A : ℝ) ≤ (n : ℝ) ^ s := by
    have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hnormLog : ‖Real.log (n : ℝ) ^ (A : ℝ)‖ =
        Real.log (n : ℝ) ^ (A : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlognonneg _)]
    have hnormN : ‖(n : ℝ) ^ s‖ = (n : ℝ) ^ s := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    rw [hnormLog, hnormN] at hsmall
    have hmul := mul_le_mul_of_nonneg_left hsmall hC.le
    calc
      C * Real.log (n : ℝ) ^ (A : ℝ) ≤
          C * (C⁻¹ * (n : ℝ) ^ s) := hmul
      _ = (n : ℝ) ^ s := by
        rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  have hnatReal : (A ^ flattenRoundCount x : ℕ) ≤
      (A * (2 * (k * (Nat.log 2 n + 1))) ^ A : ℕ) := hnat
  have hnatReal' : (A ^ flattenRoundCount x : ℝ) ≤
      (A * (2 * (k * (Nat.log 2 n + 1))) ^ A : ℕ) := by
    exact_mod_cast hnatReal
  have hsmallNatExp : C * Real.log (n : ℝ) ^ A ≤ (n : ℝ) ^ s := by
    simpa only [Real.rpow_natCast] using hsmall'
  exact hnatReal'.trans (hcast.trans hsmallNatExp)

/-- The initial multiplicity, all fourth-power flattening losses, and every
round coefficient fit inside the explicit flattening stage budget. -/
theorem eventually_twoCapMultiplicity_flattenBudget
    (k r b : ℕ) (hr : 0 < r) (hrk : r < k) (hb : 0 < b) :
    let B := 16 * flattenCoefficientLoss hrk
    ∀ᶠ n : ℕ in atTop,
      ∀ u : ℕ,
        u ≤ sectionSixColorLoadCoefficient hrk *
          SlowRotationBanks.rotationBankCount (2 * b) n →
        let x := twoCapDecoderInputMultiplicity k r
          (generatorEdgeCap (2 * b) n) u
        B ^ flattenRoundCount x * x * x ^ 4 ≤
          flattenStageBudget B k (10 * b) n := by
  let B := 16 * flattenCoefficientLoss hrk
  let s : ℝ := 1 / (1000 * b : ℕ)
  let target : ℝ := 1 / (80 * b : ℕ)
  have hB : 0 < B := Nat.mul_pos (by omega) (flattenCoefficientLoss_pos hrk)
  have hk : 0 < k := by omega
  have hs : 0 < s := by dsimp [s]; positivity
  have hmult := eventually_twoCapMultiplicity_cast_le_rpow
    k r b hrk hb
  have hround := eventually_pow_flattenRoundCount_of_le_ground_pow
    B k hB hk hs
  have hgap : 6 * s < target := by
    dsimp [s, target]
    push_cast
    field_simp
    nlinarith
  have hsmall := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (2 : ℝ)) hgap (by norm_num : (0 : ℝ) ≤ 2)
  have hfloor := Asymptotics.eventually_half_rpow_le_rationalPowerThreshold
    (E := 1) (d := 80 * b) (by omega) (by positivity)
  filter_upwards [hmult, hround, hsmall, hfloor,
      eventually_ge_atTop 1] with n hmult hround hsmall hfloor hn
  intro u hu
  let x := twoCapDecoderInputMultiplicity k r
    (generatorEdgeCap (2 * b) n) u
  have hxreal : (x : ℝ) ≤ (n : ℝ) ^ s := by
    simpa [x, s] using hmult u hu
  have hsK : s ≤ (k : ℝ) := by
    dsimp [s]
    have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsmallOne : (1 : ℝ) / (1000 * b : ℕ) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (1000 * b : ℕ))]
      exact_mod_cast (show 1 ≤ 1000 * b by omega)
    exact hsmallOne.trans hkReal
  have hxground : x ≤ n ^ k := by
    have hpow : (n : ℝ) ^ s ≤ (n : ℝ) ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hsK
    have : (x : ℝ) ≤ (n ^ k : ℕ) := by
      simpa only [Nat.cast_pow, Real.rpow_natCast] using hxreal.trans hpow
    exact_mod_cast this
  have hroundx : (B ^ flattenRoundCount x : ℝ) ≤ (n : ℝ) ^ s :=
    hround x hxground
  have hnpos : (0 : ℝ) < n := by positivity
  have hlhs :
      (B ^ flattenRoundCount x * x * x ^ 4 : ℕ) ≤
        (n : ℝ) ^ target / 2 := by
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    calc
      (B : ℝ) ^ flattenRoundCount x * (x : ℝ) * (x : ℝ) ^ 4 ≤
          (n : ℝ) ^ s * (n : ℝ) ^ s * ((n : ℝ) ^ s) ^ 4 := by
        gcongr
      _ = (n : ℝ) ^ (6 * s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
          ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
        congr 1
        ring
      _ ≤ (n : ℝ) ^ target / 2 := by
        linarith
  have hthreshold : B ^ flattenRoundCount x * x * x ^ 4 ≤
      Asymptotics.rationalPowerThreshold 1 (80 * b) n := by
    have hreal :
        (B ^ flattenRoundCount x * x * x ^ 4 : ℕ) ≤
          (Asymptotics.rationalPowerThreshold 1 (80 * b) n : ℝ) :=
      hlhs.trans (by simpa [target] using hfloor)
    exact_mod_cast hreal
  calc
    B ^ flattenRoundCount x * x * x ^ 4 ≤
        Asymptotics.rationalPowerThreshold 1 (80 * b) n := hthreshold
    _ ≤ B ^ flattenRoundCount (n ^ k) *
        Asymptotics.rationalPowerThreshold 1 (80 * b) n := by
      exact Nat.le_mul_of_pos_left _
        (Nat.one_le_pow _ _ hB)
    _ = flattenStageBudget B k (10 * b) n := by
      unfold flattenStageBudget
      rw [show 8 * (10 * b) = 80 * b by omega]

/-- Complete asymptotic Section 6 construction: the rainbow focusing
certificate, separated local decoders, first splitting exchanges, and all
quantitative flattening rounds produce a sparse integral generator. -/
theorem eventually_hasSparseIntegralGeneratorData
    (k r : ℕ) (hr : 1 < r) (hrk : r < k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ reserve : Finset (Finset (Fin n)),
        HasReserveProperty n k r reserve →
        HasSparseIntegralGeneratorData n k r reserve := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let b := sectionSixSampleDen hrk
  let B := 16 * flattenCoefficientLoss hrk
  let cBoundary := 2 * max 1
    ((CoverClique.coverPattern (k + r) r).freeEdges.card *
      LocalDecoderAsymptotic.decoderPathMultiplier (k + r) r)
  have hb : 0 < b := by
    have hchoose : 0 < Nat.choose k r := Nat.choose_pos hrk.le
    have hbound := sectionSixSampleDen_bounds hr hrk
    exact hchoose.trans hbound.1
  have hB : 0 < B :=
    Nat.mul_pos (by omega) (flattenCoefficientLoss_pos hrk)
  have hk : 0 < k := by omega
  have hcert := eventually_exists_rainbowTwoCapFocusingCertificate
    k r hr hrk
  have hdecoder :=
    eventually_exists_boundedLocalDecoderPlacementForRoots_of_powerBounded
      (k := k) (r := r) (d := 4 * b) (by omega) hrk (by positivity)
  have hinput := eventually_rainbowDecoderInput_powerBounded
    k r b (by omega) hrk hb
  have hboundaryRebase := eventually_rebase_powerBounded_constant
    (r := r) (8 * b) (9 * b) cBoundary (by positivity) (by omega)
  have hsplit := ExchangeEmbedding.eventually_exists_boundedFullExchangeEmbeddings
    (k := k) (r := r) (d := 9 * b) (by omega) hrk (by positivity)
  have hstage := eventually_decoderInputCap_add_exchangePathCap_le_stagePathCap
    k r E.v E.pattern.freeEdges.card b (by omega) hb
  have hbudget := eventually_twoCapMultiplicity_flattenBudget
    k r b (by omega) hrk hb
  have hround := eventually_hasQuantitativeFlattenRounds
    k r (10 * b) B (by omega) hrk (by positivity) hB
  have hgap : 4 * (10 * b) < generatorDen k r := by
    have hb' : 0 < sectionSixPatternDen k r := by
      simpa [b, sectionSixSampleDen] using hb
    simp only [b, sectionSixSampleDen, generatorDen]
    omega
  have hterminal := eventually_linearStageBudget_powerBounded
    k r B k (10 * b) (generatorDen k r) hB hk (by positivity) hgap
  filter_upwards [hcert, hdecoder, hinput, hboundaryRebase, hsplit,
      hstage, hbudget, hround, hterminal, eventually_ge_atTop 1] with
      n hcert hdecoder hinput hboundaryRebase hsplit hstage hbudget hround
        hterminal hn
  intro reserve hreserve
  obtain ⟨u, huGround, huBank, C, hrootPower, hmodularPower⟩ :=
    hcert reserve hreserve
  have hrootUniform : ∀ e ∈ C.decoderRoots, e.card = r := by
    intro e he
    change e ∈ reserve ∪ cliqueBoundarySupport C.modular r at he
    rcases Finset.mem_union.mp he with he | he
    · exact mem_completeUniform.mp (hreserve.1 he)
    · exact mem_completeUniform.mp
        (cliqueBoundarySupport_subset_complete C.modular_uniform he)
  have hmodularBoundary : cliqueBoundarySupport C.modular r ⊆
      C.decoderRoots := by
    intro e he
    change e ∈ reserve ∪ cliqueBoundarySupport C.modular r
    exact Finset.mem_union_right _ he
  obtain ⟨P⟩ := hdecoder C.decoderRoots C.modular hrootUniform
    C.modular_uniform hmodularBoundary hrootPower
  have hinputPower : IsPowerBounded n r (9 * b) 1
      (C.decoderInput P.Z) :=
    hinput reserve _ _ u C P hrootPower hmodularPower
  have hinputBoundary8 : IsPowerBounded n r (8 * b) cBoundary
      (cliqueBoundarySupport (C.decoderInput P.Z) r) := by
    have hmain := P.input_powerBounded (by positivity : 0 < 4 * b) hn
      hrootPower
    change IsPowerBounded n r (8 * b)
      (2 * max 1
        ((CoverClique.coverPattern (k + r) r).freeEdges.card *
          LocalDecoderAsymptotic.decoderPathMultiplier (k + r) r))
      (cliqueBoundarySupport
        (C.modular ∪ localDecoderCliques C.decoderRoots P.Z k) r)
    rw [show 8 * b = 2 * (4 * b) by omega]
    exact hmain
  have hinputBoundaryPower : IsPowerBounded n r (9 * b) 1
      (cliqueBoundarySupport (C.decoderInput P.Z) r) :=
    hboundaryRebase _ hinputBoundary8
  have hinputUniform : ∀ Q ∈ C.decoderInput P.Z, Q.card = k := by
    simpa [RainbowTwoCapFocusingCertificate.decoderInput,
      RainbowTwoCapFocusingCertificate.decoderRoots] using
      modular_union_localDecoderCliques_uniform
        (reserve := reserve) C.modular_uniform P.Z
  have hboundaryUniform : ∀ e ∈
      cliqueBoundarySupport (C.decoderInput P.Z) r, e.card = r := by
    intro e he
    exact mem_completeUniform.mp
      (cliqueBoundarySupport_subset_complete hinputUniform he)
  have hinputDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree (C.decoderInput P.Z) J ^ (9 * b) ≤
        n ^ (9 * b - 1) := by
    intro J hJ
    simpa [localDegree, Reserve.localDegree] using
      hinputPower J (mem_completeUniform.mpr hJ)
  have hboundaryDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree
          (cliqueBoundarySupport (C.decoderInput P.Z) r) J ^ (9 * b) ≤
        n ^ (9 * b - 1) := by
    intro J hJ
    simpa [localDegree, Reserve.localDegree] using
      hinputBoundaryPower J (mem_completeUniform.mpr hJ)
  obtain ⟨S⟩ := hsplit (C.decoderInput P.Z)
    (cliqueBoundarySupport (C.decoderInput P.Z) r)
      hinputUniform hboundaryUniform hinputDegree hboundaryDegree
  let x := twoCapDecoderInputMultiplicity k r
    (generatorEdgeCap (2 * b) n) u
  let D := LocalDecoderAsymptotic.decoderInputCap (9 * b) n
  let F := E.pattern.freeEdges.card *
    LocalDecoderAsymptotic.decoderPathCap E.v r (9 * b) n
  have hsourceBoundary : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree
        (cliqueBoundarySupport (C.decoderInput P.Z) r) J ≤ D := by
    intro J hJ
    apply LocalDecoderAsymptotic.le_decoderInputCap_of_pow_le
      (9 * b) n _ (by positivity)
    simpa [localDegree, Reserve.localDegree] using
      hinputBoundaryPower J (mem_completeUniform.mpr hJ)
  have hfreeDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree S.freeUnion J ≤ F := by
    intro J hJ
    simpa [F, E] using S.free_degree_le J hJ
  have hxTwo : 2 ≤ x := by
    have hpow : 1 ≤ 2 ^ (k + r) := Nat.one_le_pow _ _ (by omega)
    simp only [x, twoCapDecoderInputMultiplicity]
    omega
  have hstageBase : D + F ≤
      LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n := by
    simpa [D, F, E] using hstage
  have hboundaryStage : D + F ≤ linearStageDegree x k r (10 * b) n := by
    calc
      D + F ≤ LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n :=
        hstageBase
      _ ≤ x * LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = linearStageDegree x k r (10 * b) n := rfl
  have hfamilyStage : (D + F) * max x 2 ≤
      linearStageDegree x k r (10 * b) n := by
    rw [max_eq_left hxTwo]
    calc
      (D + F) * x ≤
          LocalDecoderAsymptotic.decoderPathCap k r (10 * b) n * x :=
        Nat.mul_le_mul_right x hstageBase
      _ = linearStageDegree x k r (10 * b) n := by
        simp [linearStageDegree, Nat.mul_comm]
  apply C.hasSparseIntegralGeneratorData (d := 10 * b) (A := B)
    (z := x) (D := D) (F := F) (by omega) hrk hreserve.1 P S
      hsourceBoundary hfreeDegree hboundaryStage hfamilyStage hround
  · simpa [x, B] using hbudget u huBank
  · omega
  · exact hterminal

end

end Erdos722
