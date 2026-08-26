import ErdosProblems.Erdos796.ModelPositiveTail
import ErdosProblems.Erdos796.ModelLimitFinite
import ErdosProblems.Erdos796.ModelScoreExcess
import ErdosProblems.Erdos796.CanonicalModelLimit
import ErdosProblems.Erdos796.GammaFinite

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The cofactor-model limit

This file assembles the finite-prefix variational inequality, the uniform
positive-tail estimate, and canonical near-maximizers into the full limit for
`G(n)` around its prime--semiprime baseline.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- The finite-prefix error appearing in the variational upper bound. -/
noncomputable def primePrefixError (J : ℕ) : ℝ :=
  ((1 : ℝ) + Nat.primeCounting J) / (J + 1 : ℕ)

/-- The scale `J/log J`, divided by `J+1`, tends to zero. -/
theorem secondOrderScale_div_succ_tendsto_zero :
    Tendsto
      (fun J : ℕ => secondOrderScale J / (J + 1 : ℕ))
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun J : ℕ => (J : ℝ) / ((J : ℝ) + 1))
      atTop (nhds 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hlog : Tendsto (fun J : ℕ => Real.log (J : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Tendsto
      (fun J : ℕ => (1 : ℝ) / Real.log (J : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
  have hprod := hratio.mul hinvlog
  have heq : ∀ J : ℕ,
      secondOrderScale J / (J + 1 : ℕ) =
        ((J : ℝ) / ((J : ℝ) + 1)) *
          ((1 : ℝ) / Real.log (J : ℝ)) := by
    intro J
    simp only [secondOrderScale, Nat.cast_add, Nat.cast_one]
    ring
  simpa using! hprod.congr' (Eventually.of_forall fun J => (heq J).symm)

/-- PNT implies that the prime error in the finite-prefix inequality vanishes. -/
theorem primePrefixError_tendsto_zero (hPNT : PrimeNumberTheorem) :
    Tendsto primePrefixError atTop (nhds 0) := by
  have hprime : Tendsto
      (fun J : ℕ => (Nat.primeCounting J : ℝ) / (J + 1 : ℕ))
      atTop (nhds 0) := by
    have hprod := hPNT.mul secondOrderScale_div_succ_tendsto_zero
    have heq : ∀ᶠ J : ℕ in atTop,
        (Nat.primeCounting J : ℝ) / (J + 1 : ℕ) =
          ((Nat.primeCounting J : ℝ) / secondOrderScale J) *
            (secondOrderScale J / (J + 1 : ℕ)) := by
      filter_upwards [eventually_ge_atTop 2] with J hJ
      have hscale : secondOrderScale J ≠ 0 := by
        rw [secondOrderScale]
        exact div_ne_zero (by positivity)
          (Real.log_pos (by exact_mod_cast (show 1 < J by omega))).ne'
      field_simp
    simpa using! hprod.congr' (heq.mono fun _ h => h.symm)
  have hone : Tendsto
      (fun J : ℕ => (1 : ℝ) / (J + 1 : ℕ))
      atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsum := hone.add hprime
  have heq : ∀ J : ℕ,
      primePrefixError J =
        (1 : ℝ) / (J + 1 : ℕ) +
          (Nat.primeCounting J : ℝ) / (J + 1 : ℕ) := by
    intro J
    rw [primePrefixError, add_div]
  simpa only [zero_add] using!
    hsum.congr' (Eventually.of_forall fun J => (heq J).symm)

/-- The positive Sidon correction divided by `J+1` tends to zero. -/
theorem sidonMajorant_div_succ_tendsto_zero :
    Tendsto
      (fun J : ℕ => sidonMajorant J / (J + 1 : ℕ))
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun J : ℕ => (J : ℝ) / ((J : ℝ) + 1))
      atTop (nhds 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hpow : Tendsto
      (fun J : ℕ => (J : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 6 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hthree : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3) :=
    tendsto_const_nhds
  have hprod : Tendsto
      (fun J : ℕ =>
        (3 * ((J : ℝ) / ((J : ℝ) + 1))) *
          (J : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds ((3 * 1) * 0)) := (hthree.mul hratio).mul hpow
  have heq : ∀ᶠ J : ℕ in atTop,
      sidonMajorant J / (J + 1 : ℕ) =
        (3 * ((J : ℝ) / ((J : ℝ) + 1))) *
          (J : ℝ) ^ (-(1 / 6 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with J hJ
    have hJ0 : (J : ℝ) ≠ 0 := by positivity
    rw [sidonMajorant,
      show -(1 / 6 : ℝ) = 5 / 6 - 1 by norm_num,
      Real.rpow_sub_one hJ0]
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp
  simpa using! hprod.congr' (heq.mono fun _ h => h.symm)

/-- For every compatible family, the exact canonical cutoff correction tends
to zero.  PNT is used only for the possible negative prime-counting part. -/
theorem canonicalCorrection_tendsto_zero
    (hPNT : PrimeNumberTheorem) {U : ℕ → Finset ℕ} (hU : Compatible U) :
    Tendsto (fun J : ℕ => excess U J / (J + 1 : ℕ))
      atTop (nhds 0) := by
  have hlower : Tendsto (fun J : ℕ => -primePrefixError J)
      atTop (nhds 0) := by
    simpa using! (primePrefixError_tendsto_zero hPNT).neg
  have hupper := sidonMajorant_div_succ_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 8] with J hJ
    have hden : (0 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by positivity
    have h := div_le_div_of_nonneg_right
      (neg_one_add_primeCounting_le_excess U J) hden
    change -primePrefixError J ≤ excess U J / (J + 1 : ℕ)
    rw [primePrefixError]
    convert! h using 1
    push_cast
    ring
  · filter_upwards [eventually_ge_atTop 8] with J hJ
    have hexcess : excess U J ≤ sidonMajorant J :=
      (SidonCardBound.compatible_fiber_excess_le hU hJ).trans
        (explicitSidonMajorant_le_sidonMajorant (by omega))
    exact div_le_div_of_nonneg_right hexcess (by positivity)

/-- Canonical truncations of a summable compatible family recover its full
cofactor value. -/
theorem cofactorValue_canonicalExtension_tendsto
    (hPNT : PrimeNumberTheorem) {U : ℕ → Finset ℕ}
    (hU : Compatible U) (hValue : HasCofactorValue U) :
    Tendsto
      (fun J : ℕ => cofactorValue (canonicalExtension J U))
      atTop (nhds (cofactorValue U)) := by
  have hcanonicalAbs : Tendsto
      (fun J : ℕ => |excess U J / (J + 1 : ℕ)|)
      atTop (nhds 0) := by
    simpa using! (canonicalCorrection_tendsto_zero hPNT hU).abs
  have htailAbs : Tendsto
      (fun J : ℕ => |∑' k : ℕ, cofactorTerm U (k + J)|)
      atTop (nhds 0) := by
    simpa using! (tendsto_cofactorTail_zero U hValue).abs
  have hbound := hcanonicalAbs.add htailAbs
  have habsDiff : Tendsto
      (fun J : ℕ =>
        |cofactorValue (canonicalExtension J U) - cofactorValue U|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun J => abs_nonneg _
    · exact Eventually.of_forall fun J =>
        abs_cofactorValue_canonicalExtension_sub_le hU hValue J
    · simpa using! hbound
  have hdiff : Tendsto
      (fun J : ℕ =>
        cofactorValue (canonicalExtension J U) - cofactorValue U)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using! habsDiff
  have hsum := hdiff.add
    (show Tendsto (fun _ : ℕ => cofactorValue U) atTop
      (nhds (cofactorValue U)) from tendsto_const_nhds)
  have heq : ∀ J : ℕ,
      (cofactorValue (canonicalExtension J U) - cofactorValue U) +
          cofactorValue U = cofactorValue (canonicalExtension J U) := by
    intro J
    ring
  have hsum' : Tendsto
      (fun J : ℕ =>
        (cofactorValue (canonicalExtension J U) - cofactorValue U) +
          cofactorValue U)
      atTop (nhds (cofactorValue U)) := by
    simpa using! hsum
  exact hsum'.congr' (Eventually.of_forall heq)

/-- Every strict lower bound for `Gamma` is exceeded by the value of a fixed
canonical extension.  This is the rigorous supremum-approximation step used
for the model-limit lower bound. -/
theorem exists_canonicalExtension_value_gt
    (hPNT : PrimeNumberTheorem) {a : ℝ} (ha : a < Gamma) :
    ∃ (J : ℕ) (U : ℕ → Finset ℕ), CompatiblePrefix J U ∧
      a < cofactorValue (canonicalExtension J U) := by
  have haSup : a < sSup gammaScores := by
    simpa [Gamma_eq_sSup_gammaScores] using! ha
  obtain ⟨x, hxScores, hax⟩ :=
    exists_lt_of_lt_csSup gammaScores_nonempty haSup
  rcases hxScores with ⟨U, hU, hValue, rfl⟩
  have hlimit := cofactorValue_canonicalExtension_tendsto hPNT hU hValue
  have hevent : ∀ᶠ J : ℕ in atTop,
      a < cofactorValue (canonicalExtension J U) :=
    (tendsto_order.1 hlimit).1 a hax
  obtain ⟨J, hJ⟩ := hevent.exists
  exact ⟨J, U, compatible_compatiblePrefix hU, hJ⟩

/-- Normalized contribution of the first `J` positive cofactor fibres. -/
noncomputable def normalizedModelPrefix
    (J n : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.range J,
    ((bucketCount n (k + 1) : ℝ) / secondOrderScale n) *
      excess U (k + 1)

/-- Uniform finite-prefix error caused by replacing normalized bucket counts
with their limiting cofactor weights. -/
noncomputable def prefixApproximationError (J n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range J,
    |(bucketCount n (k + 1) : ℝ) / secondOrderScale n -
        cofactorWeight (k + 1)| *
      (((k + 1 : ℕ) : ℝ) + 1 + Nat.primeCounting (k + 1))

/-- A fixed compatible fibre has a uniform two-sided elementary excess bound. -/
theorem abs_excess_le_index_add_prime
    {U : ℕ → Finset ℕ} (hU : Compatible U) (j : ℕ) :
    |excess U j| ≤ (j : ℝ) + 1 + Nat.primeCounting j := by
  rw [abs_le]
  constructor
  · have hlower := neg_one_add_primeCounting_le_excess U j
    have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  · have hupper := excess_le_index hU j
    have hprime : (0 : ℝ) ≤ Nat.primeCounting j := by positivity
    linarith

theorem prefixApproximationError_nonneg (J n : ℕ) :
    0 ≤ prefixApproximationError J n := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (abs_nonneg _ ) (by positivity)

/-- For a fixed prefix, the bucket approximation error tends to zero. -/
theorem prefixApproximationError_tendsto_zero
    (hPNT : PrimeNumberTheorem) (J : ℕ) :
    Tendsto (prefixApproximationError J) atTop (nhds 0) := by
  unfold prefixApproximationError
  have hsum : Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range J,
          |(bucketCount n (k + 1) : ℝ) / secondOrderScale n -
              cofactorWeight (k + 1)| *
            (((k + 1 : ℕ) : ℝ) + 1 + Nat.primeCounting (k + 1)))
      atTop (nhds (∑ _k ∈ Finset.range J, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro k hk
    have hbucket := bucketCount_div_secondOrderScale_tendsto
      hPNT (k + 1) (by omega)
    have hdiff : Tendsto
        (fun n : ℕ =>
          (bucketCount n (k + 1) : ℝ) / secondOrderScale n -
            cofactorWeight (k + 1))
        atTop (nhds 0) := by
      have hconst : Tendsto
          (fun _ : ℕ => cofactorWeight (k + 1)) atTop
          (nhds (cofactorWeight (k + 1))) := tendsto_const_nhds
      simpa using! hbucket.sub hconst
    have habs : Tendsto
        (fun n : ℕ =>
          |(bucketCount n (k + 1) : ℝ) / secondOrderScale n -
            cofactorWeight (k + 1)|)
        atTop (nhds 0) := by
      simpa using! hdiff.abs
    simpa using! habs.mul_const
      (((k + 1 : ℕ) : ℝ) + 1 + Nat.primeCounting (k + 1))
  simpa using! hsum

/-- Uniform comparison of a varying compatible prefix with its limiting
cofactor functional. -/
theorem normalizedModelPrefix_le
    {U : ℕ → Finset ℕ} (hU : Compatible U) (J n : ℕ) :
    normalizedModelPrefix J n U ≤
      prefixCofactorSum J U + prefixApproximationError J n := by
  rw [normalizedModelPrefix, prefixCofactorSum, prefixApproximationError,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  simp only [cofactorTerm]
  let a : ℝ := (bucketCount n (k + 1) : ℝ) / secondOrderScale n
  let w : ℝ := cofactorWeight (k + 1)
  let e : ℝ := excess U (k + 1)
  let B : ℝ := (((k + 1 : ℕ) : ℝ) + 1 + Nat.primeCounting (k + 1))
  have he : |e| ≤ B := by
    simpa [e, B] using! abs_excess_le_index_add_prime hU (k + 1)
  calc
    a * e = w * e + (a - w) * e := by ring
    _ ≤ w * e + |(a - w) * e| := by
      have hle := le_abs_self ((a - w) * e)
      linarith
    _ = w * e + |a - w| * |e| := by rw [abs_mul]
    _ ≤ w * e + |a - w| * B := by
      have hmul := mul_le_mul_of_nonneg_left he (abs_nonneg (a - w))
      linarith

/-- Signed contribution of the cofactor interval `[K,√n]`. -/
noncomputable def signedModelTail
    (n K : ℕ) (U : ℕ → Finset ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico K (n.sqrt + 1),
    (bucketCount n j : ℝ) * excess U j

/-- Exact split of the model excess into the first `J` fibres and the
remaining tail. -/
theorem modelExcessSum_eq_head_add_tail
    {n J : ℕ} (U : ℕ → Finset ℕ) (hJsqrt : J ≤ n.sqrt) :
    modelExcessSum n U =
      (∑ j ∈ Finset.Icc 1 J,
        (bucketCount n j : ℝ) * excess U j) +
        signedModelTail n (J + 1) U := by
  classical
  have hUnion :
      Finset.Icc 1 J ∪ Finset.Ico (J + 1) (n.sqrt + 1) =
        Finset.Icc 1 n.sqrt := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hDisjoint :
      Disjoint (Finset.Icc 1 J) (Finset.Ico (J + 1) (n.sqrt + 1)) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjHead hjTail
    simp only [Finset.mem_Icc] at hjHead
    simp only [Finset.mem_Ico] at hjTail
    omega
  rw [modelExcessSum, ← hUnion, Finset.sum_union hDisjoint,
    signedModelTail]

/-- The normalized raw head is exactly `normalizedModelPrefix`. -/
theorem head_div_secondOrderScale_eq_normalizedModelPrefix
    (n J : ℕ) (U : ℕ → Finset ℕ) :
    (∑ j ∈ Finset.Icc 1 J,
      (bucketCount n j : ℝ) * excess U j) / secondOrderScale n =
        normalizedModelPrefix J n U := by
  rw [Finset.sum_div]
  rw [sum_Icc_one_eq_sum_range_succ]
  rw [normalizedModelPrefix]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem signedModelTail_le_positiveModelTail
    (n K : ℕ) (U : ℕ → Finset ℕ) :
    signedModelTail n K U ≤ positiveModelTail n K U := by
  rw [signedModelTail, positiveModelTail]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (excess_le_excessPos U j) (by positivity)

/-- The normalized full model excess is bounded by its finite normalized
prefix plus the uniformly controlled positive tail. -/
theorem normalized_modelExcessSum_le_prefix_add_positiveTail
    {n J : ℕ} {U : ℕ → Finset ℕ} (hJsqrt : J ≤ n.sqrt)
    (hscale : 0 < secondOrderScale n) :
    modelExcessSum n U / secondOrderScale n ≤
      normalizedModelPrefix J n U +
        positiveModelTail n (J + 1) U / secondOrderScale n := by
  rw [modelExcessSum_eq_head_add_tail U hJsqrt, add_div,
    head_div_secondOrderScale_eq_normalizedModelPrefix]
  have htail := (div_le_div_iff_of_pos_right hscale).mpr
    (signedModelTail_le_positiveModelTail n (J + 1) U)
  linarith

/-- The two cutoff errors in the upper bound. -/
noncomputable def modelUpperCutoffError (J : ℕ) : ℝ :=
  primePrefixError J + positiveTailConstant *
    ((J + 1 : ℕ) : ℝ) ^ (-(1 / 6 : ℝ))

theorem modelUpperCutoffError_tendsto_zero
    (hPNT : PrimeNumberTheorem) :
    Tendsto modelUpperCutoffError atTop (nhds 0) := by
  have htail : Tendsto
      (fun J : ℕ => positiveTailConstant *
        ((J + 1 : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) :=
    positiveTailMajorant_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hsum := (primePrefixError_tendsto_zero hPNT).add htail
  have heq : ∀ J : ℕ,
      modelUpperCutoffError J =
        primePrefixError J + positiveTailConstant *
          ((J : ℝ) + 1) ^ (-(1 / 6 : ℝ)) := by
    intro J
    simp [modelUpperCutoffError]
  have hsum' : Tendsto
      (fun J : ℕ => primePrefixError J + positiveTailConstant *
        ((J : ℝ) + 1) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, zero_add] using! hsum
  exact hsum'.congr' (Eventually.of_forall fun J => (heq J).symm)

/-- Uniform upper half of the cofactor-model limit. -/
theorem eventually_normalized_G_lt
    (hPNT : PrimeNumberTheorem) {b : ℝ} (hb : Gamma < b) :
    ∀ᶠ n : ℕ in atTop,
      ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n < b := by
  let δ : ℝ := b - Gamma
  have hδ : 0 < δ := sub_pos.mpr hb
  have hcutEvent : ∀ᶠ J : ℕ in atTop,
      modelUpperCutoffError J < δ / 2 :=
    (modelUpperCutoffError_tendsto_zero hPNT).eventually
      (Iio_mem_nhds (half_pos hδ))
  have hlargeJ : ∀ᶠ J : ℕ in atTop, 8 ≤ J + 1 := by
    filter_upwards [eventually_ge_atTop 7] with J hJ
    omega
  obtain ⟨J, hcut, hJ8⟩ := (hcutEvent.and hlargeJ).exists
  have happEvent : ∀ᶠ n : ℕ in atTop,
      prefixApproximationError J n < δ / 2 :=
    (prefixApproximationError_tendsto_zero hPNT J).eventually
      (Iio_mem_nhds (half_pos hδ))
  filter_upwards [happEvent, eventually_normalized_positiveModelTail_le,
    eventually_ge_atTop (max 9 (J * J))] with n happ htail hn
  obtain ⟨U, hU, hscore⟩ := G_attained n
  have hn9 : 9 ≤ n := (le_max_left 9 (J * J)).trans hn
  have hnJJ : J * J ≤ n := (le_max_right 9 (J * J)).trans hn
  have hJsqrt : J ≤ n.sqrt := Nat.le_sqrt.mpr hnJJ
  have hscale : 0 < secondOrderScale n := by
    rw [secondOrderScale]
    exact div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hGidentity :
      ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n =
        modelExcessSum n U / secondOrderScale n := by
    rw [← hscore]
    exact normalized_modelScore_sub_baseline_eq n U
  have hsplit := normalized_modelExcessSum_le_prefix_add_positiveTail
    (U := U) hJsqrt hscale
  have hprefix := normalizedModelPrefix_le hU J n
  have hGamma : prefixCofactorSum J U ≤ Gamma + primePrefixError J := by
    simpa [primePrefixError] using!
      prefixCofactorSum_le_Gamma_add_primeError
        (compatible_compatiblePrefix hU : CompatiblePrefix J U)
  have htailBound :
      positiveModelTail n (J + 1) U / secondOrderScale n ≤
        positiveTailConstant *
          ((J + 1 : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) :=
    htail U hU (J + 1) hJ8
  rw [hGidentity]
  rw [modelUpperCutoffError] at hcut
  dsimp [δ] at hδ hcut happ ⊢
  nlinarith

/-- Lower half of the cofactor-model limit, supplied by one fixed canonical
near-maximizer of `Gamma`. -/
theorem eventually_lt_normalized_G
    (hPNT : PrimeNumberTheorem) {a : ℝ} (ha : a < Gamma) :
    ∀ᶠ n : ℕ in atTop,
      a < ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n := by
  obtain ⟨J, U, hPrefix, hvalue⟩ :=
    exists_canonicalExtension_value_gt hPNT ha
  have hcanonical := canonical_modelScore_limit hPNT hPrefix
  have hcanonicalEvent : ∀ᶠ n : ℕ in atTop,
      a < ((modelScore n (canonicalExtension J U) : ℝ) -
          (baseline n : ℝ)) / secondOrderScale n :=
    (tendsto_order.1 hcanonical).1 a hvalue
  have hCompat : Compatible (canonicalExtension J U) :=
    compatible_canonicalExtension hPrefix
  filter_upwards [hcanonicalEvent, eventually_ge_atTop 2] with n hcan hn
  have hscale : 0 < secondOrderScale n := by
    rw [secondOrderScale]
    exact div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hscoreNat : modelScore n (canonicalExtension J U) ≤ G n :=
    modelScore_le_G hCompat n
  have hscore :
      (modelScore n (canonicalExtension J U) : ℝ) ≤ (G n : ℝ) := by
    exact_mod_cast hscoreNat
  have hnormalized :
      ((modelScore n (canonicalExtension J U) : ℝ) -
          (baseline n : ℝ)) / secondOrderScale n ≤
        ((G n : ℝ) - (baseline n : ℝ)) / secondOrderScale n := by
    rw [div_le_div_iff_of_pos_right hscale]
    linarith
  exact hcan.trans_le hnormalized

/-- The full finite cofactor-model limit, conditional only on the normalized
prime number theorem already isolated as a proposition. -/
theorem cofactorModelLimit_of_primeNumberTheorem
    (hPNT : PrimeNumberTheorem) : CofactorModelLimit := by
  unfold CofactorModelLimit
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact eventually_lt_normalized_G hPNT ha
  · intro b hb
    exact eventually_normalized_G_lt hPNT hb

end Erdos796
