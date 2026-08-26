import ErdosProblems.Erdos520.CaichAlignedResidualTail
import ErdosProblems.Erdos520.CaichResidualFirstMomentBounds
import ErdosProblems.Erdos520.CaichAlignedScheduledMainPNT

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# The aligned `L2` residual

The upper boundary strip has relative width `1/X`.  This elementary width
already gives the required reciprocal-prime saving: no prime-number theorem
is needed for this residual.  The remaining estimates compare the exact
natural smoothing parameter with the entropy of the aligned test mesh.
-/

theorem card_freshPrimes_le_sub {a b : ℕ} :
    (freshPrimes a b).card ≤ b - a := by
  calc
    (freshPrimes a b).card ≤ (Finset.Ioc a b).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_Ioc.mpr
        ⟨(mem_freshPrimes.mp hp).2.1, (mem_freshPrimes.mp hp).2.2⟩
    _ = b - a := Nat.card_Ioc a b

/-- A relative-width bound alone controls the reciprocal mass. -/
theorem freshReciprocalSum_le_two_div_of_relativeWidth
    {a b X : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hX : 1 ≤ X)
    (hwidth : ((b : ℝ) - (a : ℝ)) ≤ 2 * (a : ℝ) / (X : ℝ)) :
    freshReciprocalSum a b ≤ 2 / (X : ℝ) := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hXr : (0 : ℝ) < (X : ℝ) := by positivity
  calc
    freshReciprocalSum a b ≤ ((freshPrimes a b).card : ℝ) / (a : ℝ) :=
      freshReciprocalSum_le_card_div ha
    _ ≤ ((b - a : ℕ) : ℝ) / (a : ℝ) := by
      gcongr
      exact_mod_cast card_freshPrimes_le_sub (a := a) (b := b)
    _ = ((b : ℝ) - (a : ℝ)) / (a : ℝ) := by rw [Nat.cast_sub hab]
    _ ≤ (2 * (a : ℝ) / (X : ℝ)) / (a : ℝ) := by gcongr
    _ = 2 / (X : ℝ) := by field_simp

/-- The floor-safe short window has reciprocal mass at most `2/X` whenever
its lower floor is at least `2X`. -/
theorem caichTimeWindowReciprocalMass_le_two_div
    {X x a b : ℕ} {t : ℝ} (hX : 2 ≤ X) (hx : 0 < x) (ht : 0 < t)
    (hlarge : 2 * X ≤ caichLambdaLowerCutoff x X ((x : ℝ) / t)) :
    caichTimeWindowReciprocalMass (X : ℝ) a b t ≤ 2 / (X : ℝ) := by
  have hz : 0 < (x : ℝ) / t := by positivity
  rw [caichTimeWindowReciprocalMass_eq_shortWindow
    (X := (X : ℝ)) (x := x) (a := a) (b := b)
    (t := t) (by positivity) hx (ne_of_gt ht)]
  refine (caichShortWindowReciprocalMass_le_cutoffReciprocalSum
    (X := X) (x := x) (a := a) (b := b) (by omega) hz).trans ?_
  apply freshReciprocalSum_le_two_div_of_relativeWidth
  · exact (by omega : 1 ≤ caichLambdaLowerCutoff x X ((x : ℝ) / t))
  · exact caichLambdaLowerCutoff_le_upper x X hz (by omega)
  · omega
  · exact caichLambdaCutoff_width_le x X hz hX hlarge

/-- Throughout the boundary strip above `b`, the lower cutoff is at least
`2X` as soon as `4X ≤ b`. -/
theorem two_mul_le_caichLambdaLowerCutoff_boundary
    {X x b : ℕ} {t : ℝ} (hX : 2 ≤ X) (hx : 0 < x)
    (hb : 4 * X ≤ b)
    (ht : t ∈ Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / (X : ℝ)))) :
    2 * X ≤ caichLambdaLowerCutoff x X ((x : ℝ) / t) := by
  unfold caichLambdaLowerCutoff
  apply Nat.le_floor
  have hxR : (0 : ℝ) < (x : ℝ) := by positivity
  have htpos : 0 < t := (by positivity : (0 : ℝ) ≤ b).trans_lt ht.1
  have hXr : (0 : ℝ) < (X : ℝ) := by positivity
  have hfactor : 0 < 1 + 1 / (X : ℝ) := by positivity
  have hsimp :
      (x : ℝ) /
          (((x : ℝ) / t) * (1 + 1 / (X : ℝ))) =
        t / (1 + 1 / (X : ℝ)) := by
    field_simp
  rw [hsimp]
  apply (le_div_iff₀ hfactor).2
  have hfactor_le : 1 + 1 / (X : ℝ) ≤ 3 / 2 := by
    have hXtwo : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hinv : 1 / (X : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hXtwo
    linarith
  have hbR : (4 : ℝ) * X ≤ b := by exact_mod_cast hb
  calc
    (2 * X : ℕ) * (1 + 1 / (X : ℝ)) ≤
        (2 * (X : ℝ)) * (3 / 2) := by
      norm_cast at hbR ⊢
      gcongr
    _ = 3 * (X : ℝ) := by ring
    _ ≤ (b : ℝ) := by linarith
    _ ≤ t := ht.1.le

/-- One boundary block has normalized first moment at most `2/X`. -/
theorem caichBoundaryAveragedBlockFirstMoment_le_two_mul_div
    {X : ℕ} {x a b : ℕ} (hX : 2 ≤ X) (hx : 0 < x)
    (hb : 4 * X ≤ b) :
    caichBoundaryAveragedBlockFirstMoment (X : ℝ) x a b ≤
      2 * (x : ℝ) / (X : ℝ) := by
  apply caichBoundaryAveragedBlockFirstMoment_le
    (X := (X : ℝ)) (A := 2 * (x : ℝ) / (X : ℝ))
  · positivity
  · positivity
  · have : 1 ≤ X := by omega
    exact this.trans (by omega)
  · intro t ht
    have htpos : 0 < t := (by positivity : (0 : ℝ) ≤ b).trans_lt ht.1
    have hmass := caichTimeWindowReciprocalMass_le_two_div
      (a := a) (b := b) hX hx htpos
      (two_mul_le_caichLambdaLowerCutoff_boundary hX hx hb ht)
    have hcard : ∀ p ∈ freshPrimes a b,
        t / (1 + 1 / (X : ℝ)) < (p : ℝ) ∧ (p : ℝ) ≤ t →
          ((Nat.smoothNumbersUpTo
            (Nat.floor ((x : ℝ) / t)) p).card : ℝ) ≤ (x : ℝ) / t := by
      intro p hp hwindow
      calc
        ((Nat.smoothNumbersUpTo
            (Nat.floor ((x : ℝ) / t)) p).card : ℝ) ≤
            (Nat.floor ((x : ℝ) / t) : ℕ) := by
          exact_mod_cast card_smoothNumbersUpTo_le_self
            (Nat.floor ((x : ℝ) / t)) p
        _ ≤ (x : ℝ) / t := Nat.floor_le (by positivity)
    calc
      caichCoreTimeFirstMomentKernel (X : ℝ) x a b t ≤
          ((x : ℝ) / t) * caichTimeWindowReciprocalMass (X : ℝ) a b t :=
        caichCoreTimeFirstMomentKernel_le_mul_timeWindowMass
          (by positivity) hcard
      _ ≤ ((x : ℝ) / t) * (2 / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (2 * (x : ℝ) / (X : ℝ)) / t := by ring

/-- Summing the boundary estimate over an arbitrary finite schedule. -/
theorem caichScheduledL2FirstMoment_le_two_mul_card_div
    {X : ℕ} {x : ℕ} (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (hX : 2 ≤ X) (hx : 0 < x)
    (hright : ∀ j ∈ blocks, 4 * X ≤ right j) :
    caichScheduledL2FirstMoment (X : ℝ) x blocks left right ≤
      2 * (blocks.card : ℝ) / (X : ℝ) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by positivity
  have hsum : caichBoundaryFirstMoment (X : ℝ) x blocks left right ≤
      (blocks.card : ℝ) * (2 * (x : ℝ) / (X : ℝ)) := by
    unfold caichBoundaryFirstMoment
    calc
      (∑ j ∈ blocks,
          caichBoundaryAveragedBlockFirstMoment (X : ℝ) x
            (left j) (right j)) ≤
          ∑ _j ∈ blocks, 2 * (x : ℝ) / (X : ℝ) := by
        gcongr with j hj
        exact caichBoundaryAveragedBlockFirstMoment_le_two_mul_div
          hX hx (hright j hj)
      _ = (blocks.card : ℝ) * (2 * (x : ℝ) / (X : ℝ)) := by simp
  unfold caichScheduledL2FirstMoment
  calc
    caichBoundaryFirstMoment (X : ℝ) x blocks left right / (x : ℝ) ≤
        ((blocks.card : ℝ) * (2 * (x : ℝ) / (X : ℝ))) / (x : ℝ) :=
      div_le_div_of_nonneg_right hsum hxR.le
    _ = 2 * (blocks.card : ℝ) / (X : ℝ) := by field_simp

/-- Exact selected-schedule first-moment bound.  The hypotheses are the two
eventual geometric facts used elsewhere: the clamp has opened and `4X` lies
below the initial thin endpoint. -/
theorem selectedAlignedHarperL2FirstMoment_le
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {q m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell)
    (hclamp :
      (selectedClampedAlignedHarperBlockCertificate hK hHarper).clamp ≤ ell)
    (hfour : 4 * caichWSmoothingParameterNat q
        (alignedRootExpTestPoint m i) ≤ alignedThinEndpoint K ell 0) :
    selectedAlignedHarperL2FirstMoment hK hHarper q m ell i ≤
      2 * (selectedAlignedHarperBlockCount hK hHarper m ell i : ℝ) /
        caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i) := by
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  let x := alignedRootExpTestPoint m i
  let X := caichWSmoothingParameterNat q x
  have hx : 0 < x := Nat.zero_lt_of_lt
    (one_lt_alignedRootExpTestPoint_of_mem hi)
  have hX : 2 ≤ X := two_le_caichWSmoothingParameterNat_alignedTest
    (r := q) (by omega : 1 ≤ K) hi
  have hscale : clampedAlignedScale w.clamp ell = ell :=
    clampedAlignedScale_eq_of_ge hclamp
  have hbase := caichScheduledL2FirstMoment_le_two_mul_card_div
    (X := X) (x := x)
    (Finset.range (selectedAlignedHarperBlockCount hK hHarper m ell i))
    (selectedAlignedHarperEndpoint hK hHarper ell)
    (fun j ↦ selectedAlignedHarperEndpoint hK hHarper ell (j + 1))
    hX hx (by
      intro j hj
      have hmono : alignedThinEndpoint K ell 0 ≤
          alignedThinEndpoint K ell (j + 1) :=
        alignedThinEndpoint_mono K ell (Nat.zero_le (j + 1))
      simpa only [selectedAlignedHarperEndpoint,
        caichWSmoothingParameterNatCast, w, hscale, X, x] using!
          hfour.trans hmono)
  simpa only [selectedAlignedHarperL2FirstMoment, Finset.card_range,
    caichWSmoothingParameterNatCast, X, x] using! hbase

/-- Eventually, every selected first moment is bounded by the thin-block
count divided by the natural smoothing width. -/
theorem eventually_selectedAlignedHarperL2FirstMoment_le
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      selectedAlignedHarperL2FirstMoment hK hHarper q m ell i ≤
        2 * (alignedThinBlockCount K ell : ℝ) /
          caichWSmoothingParameterNatCast q
            (alignedRootExpTestPoint m i) := by
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  have hfour := eventually_four_mul_caichWSmoothingParameterNat_le_alignedInitial
    q m (by omega : 1 ≤ K)
  filter_upwards [eventually_ge_atTop w.clamp, hfour] with ell hclamp hfourEll
  intro i hi
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hpoint := selectedAlignedHarperL2FirstMoment_le hK hHarper hi
    hclamp (hfourEll i hi)
  have hscale : clampedAlignedScale w.clamp ell = ell :=
    clampedAlignedScale_eq_of_ge hclamp
  have hxUpper : alignedRootExpTestPoint m i ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    rw [if_neg (by omega : ¬ell < 5)] at hi
    exact (Finset.mem_filter.mp hi).2.2
  have hN : selectedAlignedHarperBlockCount hK hHarper m ell i ≤
      alignedThinBlockCount K ell := by
    unfold selectedAlignedHarperBlockCount
    simpa only [w, hscale] using!
      caichAlignedFirstReachingBlock_le_blockCount
        (K := K) (L := ell) (x := alignedRootExpTestPoint m i)
        (by omega : 0 < ell) hxUpper
  exact hpoint.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (by norm_num))
    (caichWSmoothingParameterNatCast_pos q
      (alignedRootExpTestPoint m i)).le)

/-! ## The smoothing width beats the finite-test entropy -/

/-- A power-of-two lower bound for the exact natural smoothing parameter at
every selected test point. -/
theorem two_pow_smoothingExponent_mul_scale_sub_one_le
    {K m ell i q : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    2 ^ (caichWSmoothingExponent q * ((ell - 2) ^ K - 1)) ≤
      caichWSmoothingParameterNat q (alignedRootExpTestPoint m i) := by
  let A : ℕ := (ell - 2) ^ K
  let e : ℕ := caichWSmoothingExponent q
  let x : ℕ := alignedRootExpTestPoint m i
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact one_le_pow₀ (by omega)
  have hxLower : alignedThinEndpoint K ell 0 < x :=
    alignedThinInitial_lt_testPoint_of_mem hi
  have hlogMono : Real.log (alignedThinEndpoint K ell 0 : ℝ) ≤
      Real.log (x : ℝ) := by
    apply Real.log_le_log (by
      exact_mod_cast (show 0 < alignedThinEndpoint K ell 0 by
        have := two_le_alignedThinEndpoint K ell 0
        omega))
    exact_mod_cast hxLower.le
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hpowHalf : ((2 ^ (A - 1) : ℕ) : ℝ) ≤
      (alignedOuterExponent K (ell - 2) : ℝ) * Real.log 2 := by
    have hAeq : A = (A - 1) + 1 := by omega
    have houter : alignedOuterExponent K (ell - 2) = 2 ^ A := by
      simp only [alignedOuterExponent, A]
    have hfactor : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith
    calc
      ((2 ^ (A - 1) : ℕ) : ℝ) =
          ((2 ^ (A - 1) : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((2 ^ (A - 1) : ℕ) : ℝ) * (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = (alignedOuterExponent K (ell - 2) : ℝ) * Real.log 2 := by
        rw [houter, hAeq, pow_succ, Nat.cast_mul]
        norm_num
        ring
  have hlogLower : ((2 ^ (A - 1) : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
    calc
      ((2 ^ (A - 1) : ℕ) : ℝ) ≤
          (alignedOuterExponent K (ell - 2) : ℝ) * Real.log 2 := hpowHalf
      _ = Real.log (alignedThinEndpoint K ell 0 : ℝ) := by
        rw [alignedThinEndpoint_zero, log_alignedOuterEndpoint]
      _ ≤ Real.log (x : ℝ) := hlogMono
  have hsmooth : ((2 ^ (e * (A - 1)) : ℕ) : ℝ) ≤
      caichWSmoothingParameter q x := by
    unfold caichWSmoothingParameter
    change ((2 ^ (e * (A - 1)) : ℕ) : ℝ) ≤ Real.log (x : ℝ) ^ e
    rw [Nat.mul_comm e (A - 1), pow_mul, Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hlogLower e
  have hfloor : 2 ^ (e * (A - 1)) ≤
      Nat.floor (caichWSmoothingParameter q x) := Nat.le_floor hsmooth
  unfold caichWSmoothingParameterNat
  simpa only [e, A, x] using! hfloor.trans (le_max_right 1 _)

theorem pow_le_two_pow_succ_mul_pow_sub_one
    {K ell : ℕ} (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    ell ^ K ≤ 2 ^ (K + 1) * ((ell - 2) ^ K - 1) := by
  let A := (ell - 2) ^ K
  have hbase : ell ≤ 2 * (ell - 2) := by omega
  have hpow : ell ^ K ≤ (2 * (ell - 2)) ^ K :=
    Nat.pow_le_pow_left hbase K
  have hAthree : 3 ≤ A := by
    dsimp only [A]
    exact (show 3 ≤ ell - 2 by omega).trans
      (le_self_pow₀ (by omega) (by omega))
  have hAsub : A ≤ 2 * (A - 1) := by omega
  calc
    ell ^ K ≤ (2 * (ell - 2)) ^ K := hpow
    _ = 2 ^ K * A := by rw [mul_pow]
    _ ≤ 2 ^ K * (2 * (A - 1)) := Nat.mul_le_mul_left _ hAsub
    _ = 2 ^ (K + 1) * (A - 1) := by rw [pow_succ]; ring

theorem two_mul_pow_le_two_pow_mul_pow
    {K ell : ℕ} (hK : 1 ≤ K) (hell : 1 ≤ ell) :
    2 * ell ^ (2 * K + 1) ≤ 2 ^ ((2 * K + 2) * ell ^ K) := by
  have hellPow : ell ≤ ell ^ K :=
    le_self_pow₀ hell (by omega)
  have hellTwo : ell ≤ 2 ^ (ell ^ K) :=
    (Nat.le_of_lt ell.lt_two_pow_self).trans
      (Nat.pow_le_pow_right (by norm_num) hellPow)
  have hpow : ell ^ (2 * K + 1) ≤
      (2 ^ (ell ^ K)) ^ (2 * K + 1) :=
    Nat.pow_le_pow_left hellTwo _
  calc
    2 * ell ^ (2 * K + 1) ≤ 2 * (2 ^ (ell ^ K)) ^ (2 * K + 1) :=
      Nat.mul_le_mul_left 2 hpow
    _ = 2 ^ (1 + (2 * K + 1) * ell ^ K) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ 2 ^ ((2 * K + 2) * ell ^ K) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hL : 1 ≤ ell ^ K := one_le_pow₀ hell
      nlinarith

theorem exp_nat_le_two_pow_two_mul (n : ℕ) :
    Real.exp (n : ℝ) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
  have he : Real.exp 1 ≤ (4 : ℝ) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  calc
    Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simpa only [Nat.cast_ofNat, mul_one] using! Real.exp_nat_mul 1 n
    _ ≤ (4 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) he n
    _ = ((2 ^ (2 * n) : ℕ) : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      norm_cast

theorem selectedAlignedHarperSafeL2Moment_nonneg
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) :
    0 ≤ selectedAlignedHarperSafeL2Moment hK hHarper q m ell i := by
  unfold selectedAlignedHarperSafeL2Moment
  split_ifs with hi
  · unfold selectedAlignedHarperL2FirstMoment
    apply caichScheduledL2FirstMoment_nonneg
    · exact (caichWSmoothingParameterNatCast_pos q
        (alignedRootExpTestPoint m i)).le
    · exact Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)
  · norm_num

/-- The published large-auxiliary threshold costs at most one extra factor
`ell^K` after inversion. -/
theorem one_div_selectedAlignedLargeSafeThreshold_le_pow
    {K ell : ℕ} (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    1 / selectedAlignedLargeSafeThreshold K ell ≤ (ell : ℝ) ^ K := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hpow : caichAuxiliaryPower K ell ≤ (ell : ℝ) ^ K := by
    unfold caichAuxiliaryPower
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hellR
    have hKR : (0 : ℝ) ≤ K := by positivity
    linarith
  have hellTen : (1 : ℝ) ≤ (ell : ℝ) ^ 10 :=
    one_le_pow₀ hellR
  have hQ : 0 < caichAuxiliaryPower K ell := by
    unfold caichAuxiliaryPower
    positivity
  unfold selectedAlignedLargeSafeThreshold
  rw [if_neg (by omega : ¬ell < 5)]
  unfold caichLargeAuxThreshold
  calc
    1 / ((ell : ℝ) ^ 10 / caichAuxiliaryPower K ell) =
        caichAuxiliaryPower K ell / (ell : ℝ) ^ 10 := by field_simp
    _ ≤ caichAuxiliaryPower K ell := by
      exact div_le_self (by positivity) hellTen
    _ ≤ (ell : ℝ) ^ K := hpow

theorem selectedAlignedHarperL2BudgetTerm_le_twoPowRatio
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    {q m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell)
    (hmoment : selectedAlignedHarperL2FirstMoment hK hHarper q m ell i ≤
      2 * (alignedThinBlockCount K ell : ℝ) /
        caichWSmoothingParameterNatCast q
          (alignedRootExpTestPoint m i)) :
    selectedAlignedHarperSafeL2Moment hK hHarper q m ell i /
        selectedAlignedLargeSafeThreshold K ell ≤
      ((2 ^ ((2 * K + 2) * ell ^ K) : ℕ) : ℝ) /
        ((2 ^ (caichWSmoothingExponent q * ((ell - 2) ^ K - 1)) : ℕ) : ℝ) := by
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hXpos : 0 < caichWSmoothingParameterNatCast q
      (alignedRootExpTestPoint m i) :=
    caichWSmoothingParameterNatCast_pos q (alignedRootExpTestPoint m i)
  have hthreshold := one_div_selectedAlignedLargeSafeThreshold_le_pow
    (by omega : 1 ≤ K) hell
  have hthreshold' : (selectedAlignedLargeSafeThreshold K ell)⁻¹ ≤
      (ell : ℝ) ^ K := by simpa only [one_div] using! hthreshold
  have hmomentNonneg : 0 ≤
      selectedAlignedHarperL2FirstMoment hK hHarper q m ell i := by
    unfold selectedAlignedHarperL2FirstMoment
    apply caichScheduledL2FirstMoment_nonneg
    · exact hXpos.le
    · exact Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)
  have hpolyNat := two_mul_pow_le_two_pow_mul_pow
    (by omega : 1 ≤ K) (by omega : 1 ≤ ell)
  have hXlower := two_pow_smoothingExponent_mul_scale_sub_one_le
    (q := q) hi
  have hfirst :
      selectedAlignedHarperSafeL2Moment hK hHarper q m ell i /
          selectedAlignedLargeSafeThreshold K ell ≤
        (2 * (alignedThinBlockCount K ell : ℝ) /
            caichWSmoothingParameterNatCast q
              (alignedRootExpTestPoint m i)) * (ell : ℝ) ^ K := by
    simp only [selectedAlignedHarperSafeL2Moment, if_pos hi]
    rw [div_eq_mul_inv]
    apply mul_le_mul hmoment hthreshold'
    · exact (inv_nonneg.mpr
        (selectedAlignedLargeSafeThreshold_pos K ell).le)
    · exact div_nonneg (by positivity) hXpos.le
  calc
    selectedAlignedHarperSafeL2Moment hK hHarper q m ell i /
        selectedAlignedLargeSafeThreshold K ell ≤
      (2 * (alignedThinBlockCount K ell : ℝ) /
          caichWSmoothingParameterNatCast q
            (alignedRootExpTestPoint m i)) * (ell : ℝ) ^ K := hfirst
    _ = ((2 * ell ^ (2 * K + 1) : ℕ) : ℝ) /
        caichWSmoothingParameterNatCast q
          (alignedRootExpTestPoint m i) := by
      unfold alignedThinBlockCount caichWSmoothingParameterNatCast
      push_cast
      rw [show 2 * K + 1 = (K + 1) + K by omega, pow_add]
      ring
    _ ≤ ((2 ^ ((2 * K + 2) * ell ^ K) : ℕ) : ℝ) /
        ((2 ^ (caichWSmoothingExponent q * ((ell - 2) ^ K - 1)) : ℕ) : ℝ) := by
      apply div_le_div₀
      · positivity
      · exact_mod_cast hpolyNat
      · positivity
      · unfold caichWSmoothingParameterNatCast
        exact_mod_cast hXlower

theorem selectedAlignedHarperL2ScalarSummability_of_smoothingExponent
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hq : (4 * m + 2 * K + 8) * 2 ^ (K + 1) ≤
      caichWSmoothingExponent q) :
    SelectedAlignedHarperL2ScalarSummability hK hHarper q m := by
  have hmomentEvent := eventually_selectedAlignedHarperL2FirstMoment_le
    hK hHarper q m
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat
  filter_upwards [hmomentEvent] with ell hmomentEll
  let L : ℕ := ell ^ K
  let C : ℕ := 2 * m + 2
  let P : ℕ := (2 * K + 2) * L
  let n : ℕ := caichWSmoothingExponent q * ((ell - 2) ^ K - 1)
  have hbudgetNonneg : 0 ≤ caichAuxiliaryFiniteUnionMomentBudget
      (alignedRootExpTests K m)
      (selectedAlignedHarperSafeL2Moment hK hHarper q m)
      (selectedAlignedLargeSafeThreshold K) 1 ell := by
    unfold caichAuxiliaryFiniteUnionMomentBudget
    exact Finset.sum_nonneg fun i hi ↦ div_nonneg
      (selectedAlignedHarperSafeL2Moment_nonneg hK hHarper q m ell i)
      (pow_nonneg (selectedAlignedLargeSafeThreshold_pos K ell).le 1)
  rw [Real.norm_eq_abs, abs_of_nonneg hbudgetNonneg]
  by_cases htests : (alignedRootExpTests K m ell).Nonempty
  · obtain ⟨i0, hi0⟩ := htests
    have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi0
    have hKone : 1 ≤ K := by omega
    have hLone : 1 ≤ L := by
      dsimp only [L]
      exact one_le_pow₀ (by omega)
    have hscale := pow_le_two_pow_succ_mul_pow_sub_one hKone hell
    have hn : (2 * C * L + P) + 2 * L ≤ n := by
      have hscale' :
          (4 * m + 2 * K + 8) * L ≤
            (4 * m + 2 * K + 8) *
              (2 ^ (K + 1) * ((ell - 2) ^ K - 1)) :=
        Nat.mul_le_mul_left _ hscale
      have hq' :
          (4 * m + 2 * K + 8) *
              (2 ^ (K + 1) * ((ell - 2) ^ K - 1)) ≤
            caichWSmoothingExponent q * ((ell - 2) ^ K - 1) := by
        calc
          (4 * m + 2 * K + 8) *
              (2 ^ (K + 1) * ((ell - 2) ^ K - 1)) =
              ((4 * m + 2 * K + 8) * 2 ^ (K + 1)) *
                ((ell - 2) ^ K - 1) := by ring
          _ ≤ caichWSmoothingExponent q * ((ell - 2) ^ K - 1) :=
            Nat.mul_le_mul_right _ hq
      calc
        (2 * C * L + P) + 2 * L =
            (4 * m + 2 * K + 8) * L := by
          dsimp only [C, P]
          ring
        _ ≤ caichWSmoothingExponent q * ((ell - 2) ^ K - 1) :=
          hscale'.trans hq'
        _ = n := rfl
    have hcardExp := card_alignedRootExpTests_le_exp_entropy K m ell
    have hcardTwo' : ((alignedRootExpTests K m ell).card : ℝ) ≤
        ((2 ^ (2 * C * L) : ℕ) : ℝ) := by
      calc
        ((alignedRootExpTests K m ell).card : ℝ) ≤
            Real.exp (((2 * m + 2 : ℕ) : ℝ) *
              (ell : ℝ) ^ (K : ℝ)) := hcardExp
        _ = Real.exp (C * L : ℕ) := by
          congr 1
          dsimp only [C, L]
          rw [Real.rpow_natCast, Nat.cast_mul, Nat.cast_pow]
        _ ≤ ((2 ^ (2 * (C * L)) : ℕ) : ℝ) :=
          exp_nat_le_two_pow_two_mul (C * L)
        _ = ((2 ^ (2 * C * L) : ℕ) : ℝ) := by ring_nf
    have hterm : ∀ i ∈ alignedRootExpTests K m ell,
        selectedAlignedHarperSafeL2Moment hK hHarper q m ell i /
            selectedAlignedLargeSafeThreshold K ell ≤
          ((2 ^ P : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
      intro i hi
      simpa only [P, n] using!
        selectedAlignedHarperL2BudgetTerm_le_twoPowRatio hK hHarper hi
          (hmomentEll i hi)
    unfold caichAuxiliaryFiniteUnionMomentBudget
    calc
      (∑ i ∈ alignedRootExpTests K m ell,
          selectedAlignedHarperSafeL2Moment hK hHarper q m ell i /
            selectedAlignedLargeSafeThreshold K ell ^ 1) ≤
          ∑ _i ∈ alignedRootExpTests K m ell,
            ((2 ^ P : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [pow_one] using! hterm i hi
      _ = ((alignedRootExpTests K m ell).card : ℝ) *
          (((2 ^ P : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) := by simp
      _ ≤ ((2 ^ (2 * C * L) : ℕ) : ℝ) *
          (((2 ^ P : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardTwo' (by positivity)
      _ = ((2 ^ (2 * C * L + P) : ℕ) : ℝ) /
          ((2 ^ n : ℕ) : ℝ) := by
        push_cast
        rw [pow_add]
        ring
      _ ≤ 1 / ((2 ^ (2 * L) : ℕ) : ℝ) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        norm_cast
        simp only [one_mul, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ Real.exp (-(ell : ℝ)) := by
        rw [Real.exp_neg]
        have hden : Real.exp (ell : ℝ) ≤ ((2 ^ (2 * L) : ℕ) : ℝ) := by
          calc
            Real.exp (ell : ℝ) ≤ ((2 ^ (2 * ell) : ℕ) : ℝ) :=
              exp_nat_le_two_pow_two_mul ell
            _ ≤ ((2 ^ (2 * L) : ℕ) : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right (by norm_num)
                (Nat.mul_le_mul_left 2
                  (le_self_pow₀ (by omega : 1 ≤ ell) (by omega : K ≠ 0)))
        simpa only [one_div] using!
          (one_div_le_one_div_of_le (Real.exp_pos (ell : ℝ)) hden)
  · have hempty : alignedRootExpTests K m ell = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp htests
    simp [caichAuxiliaryFiniteUnionMomentBudget, hempty, Real.exp_nonneg]

/-- Markov, the exact finite test union, and the finite initial-scale bridge
from the safe threshold back to Caich's published `L2` threshold. -/
theorem summable_measureReal_selectedAlignedHarperL2_failure
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hscalar : SelectedAlignedHarperL2ScalarSummability
      hK hHarper q m) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell) := by
  let tests := alignedRootExpTests K m
  let value := selectedAlignedHarperL2 hK hHarper q m
  let safeValue : ℕ → ℕ → Omega → ℝ := fun ell i omega ↦
    if i ∈ tests ell then value ell i omega else 0
  let safeMoment : ℕ → ℕ → ℝ := fun ell i ↦
    if i ∈ tests ell then
      selectedAlignedHarperL2FirstMoment hK hHarper q m ell i else 0
  have hsafe := summable_measureReal_caichAuxiliaryComponentFailure_of_natMoment
    tests safeValue safeMoment (selectedAlignedLargeSafeThreshold K) 1
    (by omega)
    (fun ell i omega ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · rw [if_pos hi]
        dsimp only [value]
        unfold selectedAlignedHarperL2
        exact caichScheduledL2_nonneg
          (caichWSmoothingParameterNatCast_pos q
            (alignedRootExpTestPoint m i)).le omega
          (Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)) _ _ _
      · rw [if_neg hi])
    (selectedAlignedLargeSafeThreshold_pos K)
    (fun ell i ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi, pow_one]
        exact integrable_selectedAlignedHarperL2 (q := q) hK hHarper hi
      · simp [hi])
    (fun ell i ↦ by
      unfold safeValue safeMoment
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi, pow_one]
        exact integral_selectedAlignedHarperL2_le_firstMoment
          (q := q) hK hHarper hi
      · simp [hi])
    (by simpa only [tests, safeMoment,
      selectedAlignedHarperSafeL2Moment] using! hscalar)
  apply hsafe.congr
  intro ell
  by_cases hell : ell < 5
  · have hempty : tests ell = ∅ := by
      simp [tests, alignedRootExpTests, hell]
    simp [tests, safeValue, value, hempty, caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale]
  · congr 1
    ext omega
    simp only [safeValue, value,
      selectedAlignedLargeSafeThreshold, if_neg hell,
      caichAuxiliaryComponentFailure, caichAuxiliaryComponentGoodAtScale,
      Set.mem_setOf_eq, not_forall, not_le]
    constructor
    · rintro ⟨i, hi, hbad⟩
      exact ⟨i, by simpa only [tests] using! hi,
        by simpa only [if_pos hi] using! hbad⟩
    · rintro ⟨i, hi, hbad⟩
      have hi' : i ∈ tests ell := by simpa only [tests] using! hi
      exact ⟨i, hi', by simpa only [if_pos hi'] using! hbad⟩

theorem summable_measureReal_selectedAlignedHarperL2_failure_of_smoothingExponent
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ)
    (hq : (4 * m + 2 * K + 8) * 2 ^ (K + 1) ≤
      caichWSmoothingExponent q) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure (alignedRootExpTests K m)
        (selectedAlignedHarperL2 hK hHarper q m)
        (caichLargeAuxThreshold K) ell) :=
  summable_measureReal_selectedAlignedHarperL2_failure hK hHarper q m
    (selectedAlignedHarperL2ScalarSummability_of_smoothingExponent
      hK hHarper q m hq)

end Problem520
end Erdos
