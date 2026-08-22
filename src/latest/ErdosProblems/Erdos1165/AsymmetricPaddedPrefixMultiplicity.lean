/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedRecursiveRenewal
import ErdosProblems.Erdos1165.ProfilePrefixFutureEquiv
import ErdosProblems.Erdos1165.AppendixPairCrossingTail

/-!
# Multiplicity of profile prefixes inside the logarithmic pair padding

The padded renewal is indexed only by the profile at and below its padded
cut.  If it is regrouped from an earlier retained prefix, the omitted
intermediate profile labels contribute a finite multiplicity.  The padding
has logarithmic depth, so this multiplicity is `exp (O(log^2 n))`; the
public profile constant deliberately has much more than this amount in
reserve.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedPrefixMultiplicity

open AppendixFirstMoment AppendixPairCrossingTail AppendixPairMoment
open AsymmetricPaddedRecursiveRenewal AsymmetricPaddedRemoteRenewal
open ProfileConditionalTailUpper ProfileListExponent
open ProfilePrefixFutureEquiv ProfileWeightUpper
open ThickPoint

noncomputable section

/-- A constrained profile coordinate below scale `n` lies in a common
quadratic-sized finite range. -/
lemma profileAtScale_lt_three_sq_succ
    {n p l : ℕ} (_hn : 1 ≤ n) (hp : p ≤ n)
    {m : Profile p} (hm : IsConstrainedProfile profileUpperDelta m)
    (hlower : 2 ≤ l) (hlp : l ≤ p) :
    profileAtScale m l < 3 * n ^ 2 + 1 := by
  have hw := constrained_profileAtScale_window hm hlower hlp
  rw [InProfileWindow, abs_le] at hw
  dsimp only [profileCenter] at hw
  push_cast at hw
  have hlOne : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have hexponent : (1 + profileUpperDelta : ℝ) ≤ 2 := by
    norm_num [profileUpperDelta]
  have hrpow : (l : ℝ) ^ (1 + profileUpperDelta) ≤ (l : ℝ) ^ 2 := by
    calc
      (l : ℝ) ^ (1 + profileUpperDelta) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlOne hexponent
      _ = (l : ℝ) ^ (2 : ℕ) := by norm_num [Real.rpow_two]
  have hln : (l : ℝ) ≤ n := by exact_mod_cast hlp.trans hp
  have hsq : (l : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hval : (profileAtScale m l : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
    nlinarith
  have hvalNat : profileAtScale m l ≤ 3 * n ^ 2 := by exact_mod_cast hval
  omega

/-- The fibre over a fixed earlier prefix injects into a tuple of
quadratically bounded coordinates. -/
lemma fixedPrefix_card_le_pow
    {n start p : ℕ} (hn : 1 ≤ n) (hstart : 2 ≤ start)
    (hstartp : start ≤ p) (hpn : p ≤ n)
    (pref : Profile start) :
    ((constrainedProfiles p profileUpperDelta).filter
        (fun m ↦ profilePrefix hstart hstartp m = pref)).card ≤
      (3 * n ^ 2 + 1) ^ (p - start) := by
  let F := (constrainedProfiles p profileUpperDelta).filter
    (fun m ↦ profilePrefix hstart hstartp m = pref)
  let B := 3 * n ^ 2 + 1
  let e : {m : Profile p // m ∈ F} →
      (Fin (p - start) → Fin B) := fun m i ↦
    ⟨profileFuture hstart hstartp m.1 i, by
      rw [profileFuture_eq_profileAtScale hstart hstartp]
      apply profileAtScale_lt_three_sq_succ hn hpn
        (mem_constrainedProfiles.mp (Finset.mem_filter.mp m.2).1)
      · omega
      · omega⟩
  have he : Function.Injective e := by
    intro m q hmq
    apply Subtype.ext
    apply profileSplit_injective hstart hstartp
    apply Prod.ext
    · exact (Finset.mem_filter.mp m.2).2.trans
        (Finset.mem_filter.mp q.2).2.symm
    · funext i
      exact congrArg Fin.val (congrFun hmq i)
  calc
    F.card = Fintype.card {m : Profile p // m ∈ F} := by
      exact Fintype.card_coe F |>.symm
    _ ≤ Fintype.card (Fin (p - start) → Fin B) :=
      Fintype.card_le_of_injective e he
    _ = B ^ (p - start) := by simp [Fintype.card_pi]
    _ = _ := rfl

/-- The common polynomial tuple bound over logarithmically many padding
coordinates is absorbed by `exp (100 n^(3/5))`. -/
theorem eventually_pow_padding_le_exp :
    ∀ᶠ n : ℕ in atTop,
      ∀ d ≤ decorrelationPadding n,
        ((3 * n ^ 2 + 1 : ℕ) : ℝ) ^ d ≤
          Real.exp (100 * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  filter_upwards
      [eventually_decorrelationPadding_budget_rpow
        (by norm_num : (0 : ℝ) < 3 / 10),
       eventually_ge_atTop 2]
      with n hpadding hn
  intro d hd
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : (0 : ℝ) < n := by positivity
  have hpow0 : 0 ≤ (n : ℝ) ^ (3 / 10 : ℝ) := by positivity
  have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) :=
    Real.one_le_rpow hnReal (by norm_num)
  have hdReal : (d : ℝ) ≤ 3 / 32 * (n : ℝ) ^ (3 / 10 : ℝ) := by
    have hdPad : (d : ℝ) ≤ decorrelationPadding n := by exact_mod_cast hd
    linarith
  let B : ℝ := ((3 * n ^ 2 + 1 : ℕ) : ℝ)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBfour : B ≤ 4 * (n : ℝ) ^ 2 := by
    dsimp only [B]
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hlogMono : Real.log B ≤ Real.log (4 * (n : ℝ) ^ 2) := by
    exact Real.strictMonoOn_log.monotoneOn hBpos
      (mul_pos (by norm_num) (sq_pos_of_pos hnPos)) hBfour
  have hlogn := Real.log_natCast_le_rpow_div n
    (by norm_num : (0 : ℝ) < 3 / 10)
  have hlog4 : Real.log 4 ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      using 1 <;> norm_num
  have hlogB : Real.log B ≤ 10 * (n : ℝ) ^ (3 / 10 : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ 2 ≠ 0), Real.log_pow] at hlogMono
    have hlogn' : Real.log (n : ℝ) ≤
        (10 / 3 : ℝ) * (n : ℝ) ^ (3 / 10 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using hlogn
    calc
      Real.log B ≤ Real.log 4 + (2 : ℝ) * Real.log n := hlogMono
      _ ≤ 3 + 2 * ((10 / 3 : ℝ) *
          (n : ℝ) ^ (3 / 10 : ℝ)) := by gcongr
      _ ≤ 10 * (n : ℝ) ^ (3 / 10 : ℝ) := by nlinarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by
    dsimp only [B]
    exact_mod_cast (by omega : 1 ≤ 3 * n ^ 2 + 1))
  have hexponent : (d : ℝ) * Real.log B ≤
      100 * (n : ℝ) ^ (3 / 5 : ℝ) := by
    have hmul := mul_le_mul hdReal hlogB hlogB0 (by positivity)
    have hrpowMul : (n : ℝ) ^ (3 / 10 : ℝ) *
        (n : ℝ) ^ (3 / 10 : ℝ) =
        (n : ℝ) ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hnPos]
      norm_num
    calc
      (d : ℝ) * Real.log B ≤
          (3 / 32 * (n : ℝ) ^ (3 / 10 : ℝ)) *
            (10 * (n : ℝ) ^ (3 / 10 : ℝ)) := hmul
      _ = (30 / 32 : ℝ) * ((n : ℝ) ^ (3 / 10 : ℝ) *
          (n : ℝ) ^ (3 / 10 : ℝ)) := by ring
      _ = (30 / 32 : ℝ) * (n : ℝ) ^ (3 / 5 : ℝ) := by
        rw [hrpowMul]
      _ ≤ 100 * (n : ℝ) ^ (3 / 5 : ℝ) := by
        gcongr
        norm_num
  calc
    (B : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log B) := by
      rw [Real.exp_nat_mul, Real.exp_log hBpos]
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- The fixed-prefix A.11 estimate needs only the core coefficient; the
larger public coefficient is kept for later padding and buffer losses. -/
theorem constrainedProfileTailWeight_le_coreEnvelope
    {n start : ℕ} (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n) (pref : Profile start) :
    constrainedProfileTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htailStart)
        hstartn pref profileUpperDelta ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        profileUpperCoreConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hraw := constrainedProfileTailWeight_le_exp
    htailStart hstartn pref
  have hnOne : 1 ≤ n :=
    (show 1 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans (htailStart.trans hstartn)
  have hsubset : Finset.Ico start n ⊆
      Finset.Ico profileUpperTailStart n := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    exact ⟨htailStart.trans hj.1, hj.2⟩
  have hsum : (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) ≤
      3 * (n : ℝ) ^ (3 / 5 : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ by positivity)).trans
        (harmonicTail_le_three_rpow hnOne)
  have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hnOne) (by norm_num)
  have ha11 : 0 ≤
      ProfileA11Assembly.a11ErrorCoefficient profileUpperDelta 2 1 11 :=
    ProfileA11Assembly.a11ErrorCoefficient_nonneg
      (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num)
      (by norm_num)
  have hlog : 0 ≤ Real.log
      ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      (constrainedProfiles profileUpperTailStart
        profileUpperDelta).card + 1 ≠ 0)
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hexponent : 3 * profileUpperDelta = (3 / 5 : ℝ) := by
    norm_num [profileUpperDelta]
  rw [hexponent]
  unfold profileUpperCoreConstant
  have hstart0 : (0 : ℝ) ≤ profileUpperTailStart := Nat.cast_nonneg _
  nlinarith

/-- Regrouping a padded continuation row from an earlier fixed prefix costs
only the number of intermediate prefixes.  The logarithmic-padding estimate
absorbs that multiplicity into the reserve between the core and public
profile constants. -/
theorem earlierPrefix_paddedPreludeContinuation_le
    {q l p start : ℕ} (hq : 1 ≤ q)
    (hstart : 2 ≤ start) (hstartp : start ≤ p) (hpq : p ≤ q)
    (htail : profileUpperTailStart ≤ p)
    (pref : Profile start) (center : Point)
    (segments : List
      ((PaddedNearPoint q l center ⊕
          PaddedMiddlePoint q (pairPrefixScale q l) center) ×
        PaddedOuterPoint q l center))
    (hfixed : ∀ midPref : Profile p,
      (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
          (fun m ↦ profilePrefix (hstart.trans hstartp) hpq m = midPref),
        paddedPreludeMultiRecursiveProfileContinuation
          q l center m segments) ≤
        ENNReal.ofReal (Real.exp 1 *
          constrainedProfileTailWeight q p (hstart.trans hstartp) hpq
            midPref profileUpperDelta) *
          (segments.map fun segment :
              ((PaddedNearPoint q l center ⊕
                  PaddedMiddlePoint q (pairPrefixScale q l) center) ×
                PaddedOuterPoint q l center) ↦ match segment.1 with
            | Sum.inl initial =>
                paddedNearUnmarkedKernelENNReal q l center initial segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                  center u segment.2).prod)
    (hcount : (((3 * q ^ 2 + 1 : ℕ) : ℝ) ^ (p - start)) ≤
      Real.exp (100 * (q : ℝ) ^ (3 / 5 : ℝ))) :
    (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
        (fun m ↦ profilePrefix hstart (hstartp.trans hpq) m = pref),
      paddedPreludeMultiRecursiveProfileContinuation
        q l center m segments) ≤
      ENNReal.ofReal (Real.exp 1 *
        Real.exp (-(2 * (q - p : ℕ) : ℝ) +
          (profileUpperCoreConstant + 101) *
            (q : ℝ) ^ (3 / 5 : ℝ))) *
        (segments.map fun segment :
            ((PaddedNearPoint q l center ⊕
                PaddedMiddlePoint q (pairPrefixScale q l) center) ×
              PaddedOuterPoint q l center) ↦ match segment.1 with
          | Sum.inl initial =>
              paddedNearUnmarkedKernelENNReal q l center initial segment.2
          | Sum.inr u =>
              paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                center u segment.2).prod := by
  let F := (constrainedProfiles q profileUpperDelta).filter
    (fun m ↦ profilePrefix hstart (hstartp.trans hpq) m = pref)
  let P := (constrainedProfiles p profileUpperDelta).filter
    (fun m ↦ profilePrefix hstart hstartp m = pref)
  let e : Profile q → Profile p :=
    profilePrefix (hstart.trans hstartp) hpq
  let f : Profile q → ℝ≥0∞ := fun m ↦
    paddedPreludeMultiRecursiveProfileContinuation q l center m segments
  let U : ℝ≥0∞ :=
    (segments.map fun segment :
        ((PaddedNearPoint q l center ⊕
            PaddedMiddlePoint q (pairPrefixScale q l) center) ×
          PaddedOuterPoint q l center) ↦ match segment.1 with
      | Sum.inl initial =>
          paddedNearUnmarkedKernelENNReal q l center initial segment.2
      | Sum.inr u =>
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
            center u segment.2).prod
  have hmap : ∀ m ∈ F, e m ∈ P := by
    intro m hm
    rw [Finset.mem_filter]
    constructor
    · exact profilePrefix_mem (hstart.trans hstartp) hpq
        (Finset.mem_filter.mp hm).1
    · funext i
      exact congrFun (Finset.mem_filter.mp hm).2 i
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap f
  have hinner (midPref : Profile p) (hmidPref : midPref ∈ P) :
      (∑ m ∈ F with e m = midPref, f m) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - p : ℕ) : ℝ) +
            profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) * U := by
    calc
      (∑ m ∈ F with e m = midPref, f m) ≤
          ∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
              (fun m ↦ profilePrefix (hstart.trans hstartp) hpq m = midPref),
            f m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_filter] at hm ⊢
          exact ⟨(Finset.mem_filter.mp hm.1).1, hm.2⟩
        · intro _ _ _
          exact bot_le
      _ ≤ ENNReal.ofReal (Real.exp 1 *
            constrainedProfileTailWeight q p (hstart.trans hstartp) hpq
              midPref profileUpperDelta) * U := by
        simpa only [f, U] using hfixed midPref
      _ ≤ ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - p : ℕ) : ℝ) +
              profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) * U := by
        gcongr
        exact constrainedProfileTailWeight_le_coreEnvelope htail hpq midPref
  have hcardNat := fixedPrefix_card_le_pow hq hstart hstartp hpq pref
  have hcard : (P.card : ℝ) ≤
      Real.exp (100 * (q : ℝ) ^ (3 / 5 : ℝ)) := by
    calc
      (P.card : ℝ) ≤ (((3 * q ^ 2 + 1 : ℕ) ^ (p - start) : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = (((3 * q ^ 2 + 1 : ℕ) : ℝ) ^ (p - start)) := by
        norm_num
      _ ≤ _ := hcount
  have hcore0 : 0 ≤ profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have ha : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
        profileUpperDelta 2 1 11 :=
      ProfileA11Assembly.a11ErrorCoefficient_nonneg
        (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num)
          (by norm_num)
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    positivity
  have hpow0 : 0 ≤ (q : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have hreal : (P.card : ℝ) *
      (Real.exp 1 * Real.exp (-(2 * (q - p : ℕ) : ℝ) +
        profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) ≤
      Real.exp 1 * Real.exp (-(2 * (q - p : ℕ) : ℝ) +
        (profileUpperCoreConstant + 101) *
          (q : ℝ) ^ (3 / 5 : ℝ)) := by
    calc
      _ ≤ Real.exp (100 * (q : ℝ) ^ (3 / 5 : ℝ)) *
          (Real.exp 1 * Real.exp (-(2 * (q - p : ℕ) : ℝ) +
            profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) := by
        gcongr
      _ = Real.exp (1 + 100 * (q : ℝ) ^ (3 / 5 : ℝ) +
          (-(2 * (q - p : ℕ) : ℝ) +
            profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (1 + (-(2 * (q - p : ℕ) : ℝ) +
          (profileUpperCoreConstant + 101) *
            (q : ℝ) ^ (3 / 5 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = _ := by rw [Real.exp_add]
  calc
    (∑ m ∈ F, f m) =
        ∑ midPref ∈ P, ∑ m ∈ F with e m = midPref, f m :=
      hfiber.symm
    _ ≤ ∑ _midPref ∈ P,
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - p : ℕ) : ℝ) +
            profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) * U := by
      exact Finset.sum_le_sum fun midPref hmidPref ↦ hinner midPref hmidPref
    _ = (P.card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - p : ℕ) : ℝ) +
            profileUpperCoreConstant * (q : ℝ) ^ (3 / 5 : ℝ))) * U) := by
      simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - p : ℕ) : ℝ) +
            (profileUpperCoreConstant + 101) *
              (q : ℝ) ^ (3 / 5 : ℝ))) * U := by
      rw [← mul_assoc]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (P.card : ℝ))]
      exact ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rfl

/-- Eventually, a padded continuation row can be conditioned at the earlier
coarse scale `l + 1`, with the same public radial envelope and the unmarked
endpoint product still exposed. -/
theorem eventually_sum_earlierFixedPrefix_paddedPreludeContinuation_le_sharp :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (hstart : 2 ≤ l + 1)
        (hstartp : l + 1 ≤ pairPrefixScale q l)
        (hpq : pairPrefixScale q l ≤ q)
        (_htail : profileUpperTailStart ≤ pairPrefixScale q l),
      ∀ (pref : Profile (l + 1)) (center : Point)
        (segments : List
          ((PaddedNearPoint q l center ⊕
              PaddedMiddlePoint q (pairPrefixScale q l) center) ×
            PaddedOuterPoint q l center)),
        (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
            (fun m ↦ profilePrefix hstart (hstartp.trans hpq) m = pref),
          paddedPreludeMultiRecursiveProfileContinuation
            q l center m segments) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
              (profileUpperCoreConstant + 101) *
                (q : ℝ) ^ (3 / 5 : ℝ))) *
            (segments.map fun segment :
                ((PaddedNearPoint q l center ⊕
                    PaddedMiddlePoint q (pairPrefixScale q l) center) ×
                  PaddedOuterPoint q l center) ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal q l center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                    center u segment.2).prod := by
  filter_upwards
      [eventually_sum_fixedPrefix_paddedPreludeMultiRecursiveProfileContinuation_le,
       eventually_pow_padding_le_exp,
       AppendixPairMoment.eventually_decorrelationPadding_lt,
       eventually_ge_atTop 1]
      with q hfixed hcount hpaddingUpper hq
  intro l hl hstart hstartp hpq htail pref center segments
  have hadd : l + decorrelationPadding q ≤ q :=
    Nat.add_le_of_le_sub hpaddingUpper.le hl
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le hadd
  have hgap : pairPrefixScale q l - (l + 1) ≤
      decorrelationPadding q := by
    rw [hpref]
    omega
  have hrow (midPref : Profile (pairPrefixScale q l)) :=
    hfixed l hl profileUpperDelta (by norm_num [profileUpperDelta])
      (hstart.trans hstartp) hpq midPref center segments
  have hpow := hcount (pairPrefixScale q l - (l + 1)) hgap
  exact earlierPrefix_paddedPreludeContinuation_le hq hstart hstartp hpq
    htail pref center segments hrow hpow

/-- Public-coefficient wrapper retained for the successful-tail row. -/
theorem eventually_sum_earlierFixedPrefix_paddedPreludeContinuation_le :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (hstart : 2 ≤ l + 1)
        (hstartp : l + 1 ≤ pairPrefixScale q l)
        (hpq : pairPrefixScale q l ≤ q)
        (htail : profileUpperTailStart ≤ pairPrefixScale q l),
      ∀ (pref : Profile (l + 1)) (center : Point)
        (segments : List
          ((PaddedNearPoint q l center ⊕
              PaddedMiddlePoint q (pairPrefixScale q l) center) ×
            PaddedOuterPoint q l center)),
        (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
            (fun m ↦ profilePrefix hstart (hstartp.trans hpq) m = pref),
          paddedPreludeMultiRecursiveProfileContinuation
            q l center m segments) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q l : ℕ) : ℝ) +
              profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
            (segments.map fun segment :
                ((PaddedNearPoint q l center ⊕
                    PaddedMiddlePoint q (pairPrefixScale q l) center) ×
                  PaddedOuterPoint q l center) ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal q l center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                    center u segment.2).prod := by
  filter_upwards
      [eventually_sum_earlierFixedPrefix_paddedPreludeContinuation_le_sharp]
      with q hsharp
  intro l hl hstart hstartp hpq htail pref center segments
  refine (hsharp l hl hstart hstartp hpq htail pref center segments).trans ?_
  gcongr
  have hcore0 : 0 ≤ profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have ha : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
        profileUpperDelta 2 1 11 :=
      ProfileA11Assembly.a11ErrorCoefficient_nonneg
        (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num)
          (by norm_num)
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    positivity
  unfold profileUpperConstant
  nlinarith

end

end Erdos1165.AsymmetricPaddedPrefixMultiplicity
