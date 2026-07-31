import Arxiv.Arxiv2407_19026.KernelBounds
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.VLower
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.XLower

/-!
# Kernel-checked bounds for the numerical profiles

Elementary logarithm and exponential estimates used to replace the executable
affine-cover certificates for the Section 4 profiles.
-/

namespace Arxiv2407_19026

noncomputable section

def logLowerAboveTwo (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 * (y + y ^ 3 / 3)

def logLowerBelowTwo (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) * (y + y ^ 3 / 3 + y ^ 5 / (1 - y ^ 2))

def logLowerBelowTwoSharp (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) *
    (y + y ^ 3 / 3 +
      y ^ 5 / (5 * (1 - y ^ 2)))

def logLowerAboveFour (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 *
    (y + y ^ 3 / 3 + y ^ 5 / 5 +
      y ^ 7 / 7)

def logLowerBelowThreeSharp (x : ℝ) : ℝ :=
  let y := (1 - x) / (1 + x)
  (-2) *
    (y + y ^ 3 / 3 + y ^ 5 / 5 +
      y ^ 7 / (7 * (1 - y ^ 2)))

def logLowerNearOne (x : ℝ) : ℝ :=
  let y := (x - 1) / (x + 1)
  2 *
    (y + y ^ 3 / 3 -
      (7 / 50) * y ^ 4 / (1 - y ^ 2))

private lemma log_lower_above_two {x : ℝ} (hx : 1 ≤ x) :
    logLowerAboveTwo x ≤ Real.log x := by
  exact KernelBounds.log_lower_of_one_le hx

private lemma log_lower_below_two {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    logLowerBelowTwo x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.log_div_le_sum_range_add hy0 hy1 2
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [Finset.sum_range_succ, logLowerBelowTwo, y] at h ⊢
  linarith

private lemma log_div_le_sum_range_add_sharp_two {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    1 / 2 * Real.log ((1 + y) / (1 - y)) ≤
      y + y ^ 3 / 3 +
        y ^ 5 / (5 * (1 - y ^ 2)) := by
  have habs : |y| < 1 := by
    rwa [abs_of_nonneg hy0]
  have hplus : 1 + y ≠ 0 := by linarith
  have hminus : 1 - y ≠ 0 := by linarith
  have hs :
      HasSum
          (fun k : ℕ =>
            y ^ (2 * k + 1) / (2 * k + 1))
        (1 / 2 *
          Real.log ((1 + y) / (1 - y))) := by
    have htermEq :
        (fun k : ℕ =>
          y ^ (2 * k + 1) / (2 * k + 1)) =
          (fun k : ℕ => (1 / 2) *
            (2 * (1 / (2 * k + 1)) *
              y ^ (2 * k + 1))) := by
      funext k
      ring
    have hresultEq :
        1 / 2 *
            Real.log ((1 + y) / (1 - y)) =
          (1 / 2) *
            (Real.log (1 + y) -
              Real.log (1 - y)) := by
      rw [Real.log_div hplus hminus]
    rw [htermEq, hresultEq]
    exact
      (Real.hasSum_log_sub_log_of_abs_lt_one
        habs).mul_left (1 / 2)
  let f : ℕ → ℝ :=
    fun k => y ^ (2 * k + 1) / (2 * k + 1)
  let g : ℕ → ℝ :=
    fun k => (y ^ 5 / 5) * (y ^ 2) ^ k
  have hterm (k : ℕ) : f (k + 2) ≤ g k := by
    have hpow :
        y ^ (2 * (k + 2) + 1) =
          y ^ 5 * (y ^ 2) ^ k := by
      rw [show 2 * (k + 2) + 1 =
          5 + 2 * k by omega,
        pow_add, ← pow_mul]
    dsimp [f, g]
    rw [hpow]
    calc
      y ^ 5 * (y ^ 2) ^ k /
            (2 * ((k + 2 : ℕ) : ℝ) + 1) ≤
          y ^ 5 * (y ^ 2) ^ k / 5 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · norm_num
        · norm_num only [Nat.cast_add,
            Nat.cast_ofNat]
          linarith [(Nat.cast_nonneg k :
            (0 : ℝ) ≤ (k : ℝ))]
      _ = (y ^ 5 / 5) * (y ^ 2) ^ k := by
        ring
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_pow,
      abs_of_nonneg hy0]
    nlinarith
  have hg : Summable g :=
    (summable_geometric_of_norm_lt_one
      hy2).mul_left _
  have hf : Summable f := hs.summable
  have hinj :
      Function.Injective (fun k : ℕ => k + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  have htail :
      ∑' k : ℕ, f (k + 2) ≤
        y ^ 5 / (5 * (1 - y ^ 2)) := by
    calc
      ∑' k : ℕ, f (k + 2) ≤
          ∑' k : ℕ, g k :=
        Summable.tsum_le_tsum hterm
          (Summable.comp_injective hf hinj) hg
      _ = y ^ 5 / (5 * (1 - y ^ 2)) := by
        dsimp [g]
        rw [tsum_mul_left,
          tsum_geometric_of_norm_lt_one hy2]
        field_simp
  calc
    1 / 2 * Real.log ((1 + y) / (1 - y)) =
        ∑ k ∈ Finset.range 2, f k +
          ∑' k : ℕ, f (k + 2) := by
      rw [← hs.tsum_eq,
        hf.sum_add_tsum_nat_add 2]
    _ ≤ ∑ k ∈ Finset.range 2, f k +
        y ^ 5 / (5 * (1 - y ^ 2)) :=
      add_le_add_right htail _
    _ = y + y ^ 3 / 3 +
        y ^ 5 / (5 * (1 - y ^ 2)) := by
      norm_num [f, Finset.sum_range_succ]

lemma log_lower_below_two_sharp {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    logLowerBelowTwoSharp x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y :=
    div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h :=
    log_div_le_sum_range_add_sharp_two hy0 hy1
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [logLowerBelowTwoSharp, y] at h ⊢
  linarith

private lemma log_div_le_sum_range_add_sharp_three
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    1 / 2 * Real.log ((1 + y) / (1 - y)) ≤
      y + y ^ 3 / 3 + y ^ 5 / 5 +
        y ^ 7 / (7 * (1 - y ^ 2)) := by
  have habs : |y| < 1 := by
    rwa [abs_of_nonneg hy0]
  have hplus : 1 + y ≠ 0 := by linarith
  have hminus : 1 - y ≠ 0 := by linarith
  have hs :
      HasSum
          (fun k : ℕ =>
            y ^ (2 * k + 1) / (2 * k + 1))
        (1 / 2 *
          Real.log ((1 + y) / (1 - y))) := by
    have htermEq :
        (fun k : ℕ =>
          y ^ (2 * k + 1) / (2 * k + 1)) =
          (fun k : ℕ => (1 / 2) *
            (2 * (1 / (2 * k + 1)) *
              y ^ (2 * k + 1))) := by
      funext k
      ring
    have hresultEq :
        1 / 2 *
            Real.log ((1 + y) / (1 - y)) =
          (1 / 2) *
            (Real.log (1 + y) -
              Real.log (1 - y)) := by
      rw [Real.log_div hplus hminus]
    rw [htermEq, hresultEq]
    exact
      (Real.hasSum_log_sub_log_of_abs_lt_one
        habs).mul_left (1 / 2)
  let f : ℕ → ℝ :=
    fun k => y ^ (2 * k + 1) / (2 * k + 1)
  let g : ℕ → ℝ :=
    fun k => (y ^ 7 / 7) * (y ^ 2) ^ k
  have hterm (k : ℕ) : f (k + 3) ≤ g k := by
    have hpow :
        y ^ (2 * (k + 3) + 1) =
          y ^ 7 * (y ^ 2) ^ k := by
      rw [show 2 * (k + 3) + 1 =
          7 + 2 * k by omega,
        pow_add, ← pow_mul]
    dsimp [f, g]
    rw [hpow]
    calc
      y ^ 7 * (y ^ 2) ^ k /
            (2 * ((k + 3 : ℕ) : ℝ) + 1) ≤
          y ^ 7 * (y ^ 2) ^ k / 7 := by
        apply div_le_div_of_nonneg_left
        · positivity
        · norm_num
        · norm_num only [Nat.cast_add,
            Nat.cast_ofNat]
          linarith [(Nat.cast_nonneg k :
            (0 : ℝ) ≤ (k : ℝ))]
      _ = (y ^ 7 / 7) * (y ^ 2) ^ k := by
        ring
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_pow,
      abs_of_nonneg hy0]
    nlinarith
  have hg : Summable g :=
    (summable_geometric_of_norm_lt_one
      hy2).mul_left _
  have hf : Summable f := hs.summable
  have hinj :
      Function.Injective (fun k : ℕ => k + 3) := by
    intro a b h
    exact Nat.add_right_cancel h
  have htail :
      ∑' k : ℕ, f (k + 3) ≤
        y ^ 7 / (7 * (1 - y ^ 2)) := by
    calc
      ∑' k : ℕ, f (k + 3) ≤
          ∑' k : ℕ, g k :=
        Summable.tsum_le_tsum hterm
          (Summable.comp_injective hf hinj) hg
      _ = y ^ 7 / (7 * (1 - y ^ 2)) := by
        dsimp [g]
        rw [tsum_mul_left,
          tsum_geometric_of_norm_lt_one hy2]
        field_simp
  calc
    1 / 2 * Real.log ((1 + y) / (1 - y)) =
        ∑ k ∈ Finset.range 3, f k +
          ∑' k : ℕ, f (k + 3) := by
      rw [← hs.tsum_eq,
        hf.sum_add_tsum_nat_add 3]
    _ ≤ ∑ k ∈ Finset.range 3, f k +
        y ^ 7 / (7 * (1 - y ^ 2)) :=
      add_le_add_right htail _
    _ = y + y ^ 3 / 3 + y ^ 5 / 5 +
        y ^ 7 / (7 * (1 - y ^ 2)) := by
      norm_num [f, Finset.sum_range_succ]

lemma log_lower_below_three_sharp {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    logLowerBelowThreeSharp x ≤ Real.log x := by
  let y : ℝ := (1 - x) / (1 + x)
  have hxplus : 0 < 1 + x := by linarith
  have hy0 : 0 ≤ y :=
    div_nonneg (sub_nonneg.mpr hx1) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h :=
    log_div_le_sum_range_add_sharp_three
      hy0 hy1
  have hratio : (1 + y) / (1 - y) = x⁻¹ := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio, Real.log_inv] at h
  norm_num [logLowerBelowThreeSharp, y] at h ⊢
  linarith

lemma log_lower_above_four {x : ℝ} (hx : 1 ≤ x) :
    logLowerAboveFour x ≤ Real.log x := by
  let y : ℝ := (x - 1) / (x + 1)
  have hxplus : 0 < x + 1 := by linarith
  have hy0 : 0 ≤ y :=
    div_nonneg (sub_nonneg.mpr hx) hxplus.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxplus]
    linarith
  have h := Real.sum_range_le_log_div hy0 hy1 4
  have hratio : (1 + y) / (1 - y) = x := by
    dsimp [y]
    field_simp [hxplus.ne']
    ring
  rw [hratio] at h
  norm_num [logLowerAboveFour, y,
    Finset.sum_range_succ] at h ⊢
  linarith

lemma log_lower_near_one {x : ℝ}
    (hx : 0 < x)
    (hyabs :
      |(x - 1) / (x + 1)| ≤ (7 / 50 : ℝ)) :
    logLowerNearOne x ≤ Real.log x := by
  let y : ℝ := (x - 1) / (x + 1)
  have hxplus : 0 < x + 1 := by linarith
  have hyabs' : |y| ≤ (7 / 50 : ℝ) := by
    simpa [y] using hyabs
  have hylt : |y| < 1 := by
    linarith
  have hden : 0 < 1 - y ^ 2 := by
    rw [sub_pos, sq_lt_one_iff_abs_lt_one]
    exact hylt
  have h :=
    Real.sum_range_sub_log_div_le hylt 2
  have hratio : (1 + y) / (1 - y) = x := by
    dsimp [y]
    field_simp [hx.ne', hxplus.ne']
    ring
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have habspow :
      |y| ^ 5 ≤ (7 / 50 : ℝ) * y ^ 4 := by
    calc
      |y| ^ 5 = |y| * y ^ 4 := by
        rw [show |y| ^ 5 = |y| * |y| ^ 4 by
          ring, ← abs_pow, abs_of_nonneg
            hy4]
      _ ≤ (7 / 50 : ℝ) * y ^ 4 :=
        mul_le_mul_of_nonneg_right hyabs'
          hy4
  have herr :
      |y| ^ 5 / (1 - y ^ 2) ≤
        (7 / 50 : ℝ) * y ^ 4 /
          (1 - y ^ 2) := by
    exact div_le_div_of_nonneg_right habspow hden.le
  have hlower :=
    neg_le_of_abs_le (h.trans herr)
  dsimp [logLowerNearOne, y]
  linarith

def expNegUpper (z : ℝ) : ℝ :=
  KernelBounds.expNegTaylor9 z + KernelBounds.expNegError10 z

private lemma exp_neg_upper {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-z) ≤ expNegUpper z := by
  have h := KernelBounds.exp_neg_approx hz
  have hu := (abs_le.mp h).2
  dsimp [expNegUpper] at hu ⊢
  linarith

def beta0CorrectionLower (z : ℝ) : ℝ :=
  (-(1 / 4) * z + 2 / 25 * z ^ 2 + 2 / 25 * z ^ 3) *
    expNegUpper z

private lemma beta0_correction_lower {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    beta0CorrectionLower z ≤ ramseyCorrection (2 / 25) z := by
  let P : ℝ := -(1 / 4) * z + 2 / 25 * z ^ 2 + 2 / 25 * z ^ 3
  have hP0 : P ≤ 0 := by
    have hz2 : z ^ 2 ≤ z := by
      nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hz3 : z ^ 3 ≤ z := by
      nlinarith [mul_nonneg (sq_nonneg z) hz.1, hz.2]
    dsimp [P]
    nlinarith [hz.1, hz2, hz3]
  have he := exp_neg_upper hz
  calc
    beta0CorrectionLower z = P * expNegUpper z := by
      dsimp [beta0CorrectionLower, P]
    _ ≤ P * Real.exp (-z) :=
      mul_le_mul_of_nonpos_left he hP0
    _ = ramseyCorrection (2 / 25) z := by
      unfold ramseyCorrection
      dsimp [P]

lemma beta0_vlarge_book1_log_argument {z : ℝ}
    (hz : z ∈ Set.Icc (3 / 1000 : ℝ) (1 / 10)) :
    1 ≤ beta0VLarge z - 1 / 100000 := by
  let u : ℝ := (1000 * z - 3) / 97
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 9
    [81603081633654454748395580608593003670683,
      714663045242229809374408674539621927046900,
      2781285357135284055226312916086002314520000,
      6313007556161359222760183729585046276000000,
      9210194981564639596363294722084277800000000,
      8956424569076442977587036680576060000000000,
      5805383729987469210684520816908000000000000,
      2418578421686362501178863496400000000000000,
      587653486136102652297311070000000000000000,
      63447044290624285053021000000000000000000] hu
  have hid :
      beta0VLarge z - 1 / 100000 - 1 =
        (∑ i ∈ Finset.range 10,
          (([81603081633654454748395580608593003670683,
              714663045242229809374408674539621927046900,
              2781285357135284055226312916086002314520000,
              6313007556161359222760183729585046276000000,
              9210194981564639596363294722084277800000000,
              8956424569076442977587036680576060000000000,
              5805383729987469210684520816908000000000000,
              2418578421686362501178863496400000000000000,
              587653486136102652297311070000000000000000,
              63447044290624285053021000000000000000000].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (9 - i)) /
          63000000000000000000000000000000000000000 := by
    dsimp [u, beta0VLarge]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

lemma beta0_vlarge_book2_log_argument {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 10 : ℝ) (1 / 2)) :
    1 ≤ beta0VLarge z - 1 / 100000 := by
  let u : ℝ := (10 * z - 1) / 4
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have h := KernelBounds.bernstein_sum_nonneg 9
    [1007095941121020397667,
      7975328859028205878455,
      27936976575183245583500,
      56755895776124422087500,
      73589627269442817316250,
      63029190384709196081250,
      35564765091768863937500,
      12700057892834153437500,
      2589733040330398046875,
      227724287191724609375] hu
  have hid :
      beta0VLarge z - 1 / 100000 - 1 =
        (∑ i ∈ Finset.range 10,
          (([1007095941121020397667,
              7975328859028205878455,
              27936976575183245583500,
              56755895776124422087500,
              73589627269442817316250,
              63029190384709196081250,
              35564765091768863937500,
              12700057892834153437500,
              2589733040330398046875,
              227724287191724609375].getD i 0 :
                ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (9 - i)) /
          1000000000000000000000 := by
    dsimp [u, beta0VLarge]
    norm_num [Finset.sum_range_succ]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg h (by norm_num)

lemma beta0_vlarge_book3_near_one {z : ℝ}
    (hz : z ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (43 / 57 : ℝ) ≤
        beta0VLarge z - 1 / 100000 ∧
      beta0VLarge z - 1 / 100000 ≤
        (57 / 43 : ℝ) := by
  let u : ℝ := 2 * z - 1
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor <;> nlinarith [hz.1, hz.2]
  have hlower := KernelBounds.bernstein_sum_nonneg 9
    [13813905597403291,
      104618127036163722,
      347864631437434608,
      663374376947998608,
      793866327932081088,
      611156373051859968,
      296412966897942720,
      83518014226149120,
      10900311973532928,
      191096464915456] hu
  have hupper := KernelBounds.bernstein_sum_nonneg 9
    [2154422093186991,
      34256500656929122,
      190291593827900208,
      555896522653264208,
      985623647349482688,
      1123457472960877568,
      832727060059446720,
      389710971724133120,
      104955905002422528,
      12431278105414656] hu
  have hlowerId :
      beta0VLarge z - 1 / 100000 - 43 / 57 =
        (∑ i ∈ Finset.range 10,
          (([13813905597403291,
              104618127036163722,
              347864631437434608,
              663374376947998608,
              793866327932081088,
              611156373051859968,
              296412966897942720,
              83518014226149120,
              10900311973532928,
              191096464915456].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (9 - i)) /
          29184000000000000 := by
    dsimp [u, beta0VLarge]
    norm_num [Finset.sum_range_succ]
    ring
  have hupperId :
      57 / 43 -
          (beta0VLarge z - 1 / 100000) =
        (∑ i ∈ Finset.range 10,
          (([2154422093186991,
              34256500656929122,
              190291593827900208,
              555896522653264208,
              985623647349482688,
              1123457472960877568,
              832727060059446720,
              389710971724133120,
              104955905002422528,
              12431278105414656].getD i 0 : ℕ) : ℝ) *
            u ^ i * (1 - u) ^ (9 - i)) /
          22016000000000000 := by
    dsimp [u, beta0VLarge]
    norm_num [Finset.sum_range_succ]
    ring
  constructor
  · rw [← sub_nonneg, hlowerId]
    exact div_nonneg hlower (by norm_num)
  · rw [← sub_nonneg, hupperId]
    exact div_nonneg hupper (by norm_num)

def beta0BookLowerOne (z : ℝ) : ℝ :=
  (1 + z) * logLowerAboveTwo (1 + z) +
    beta0CorrectionLower z +
    (logLowerBelowTwo (1 - z * beta0VLarge z) - z ^ 2 +
      z * logLowerAboveTwo (beta0VLarge z - 1 / 100000)) / 2

lemma beta0_book_lower_one_le {z : ℝ}
    (hz : z ∈ Set.Ioc (3 / 1000 : ℝ) (1 / 10)) :
    beta0BookLowerOne z ≤ beta0PolynomialBookMargin z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := Beta0Affine.v_lower z hz'
  have hX := Beta0Affine.x_lower z hz'
  have hcut : ¬z ≤ 3 / 1000 := not_le.mpr hz.1
  have hz0 : 0 < z := lt_trans (by norm_num) hz.1
  have hVnonneg : 0 ≤ beta0VLarge z := by
    have hVlarge : (3 / 4 : ℝ) ≤ beta0VLarge z := by
      simpa [beta0V, if_neg hcut] using hV
    linarith
  have hXpos : 0 < 1 - z * beta0VLarge z := by
    have : (1 / 5 : ℝ) ≤ 1 - z * beta0VLarge z := by
      simpa [beta0PolynomialX, beta0V, if_neg hcut] using hX
    linarith
  have hXone : 1 - z * beta0VLarge z ≤ 1 := by
    nlinarith [mul_nonneg hz0.le hVnonneg]
  have hWone := beta0_vlarge_book1_log_argument
    ⟨le_of_lt hz.1, hz.2⟩
  have hentropy := log_lower_above_two
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have hcorrection := beta0_correction_lower hz'
  have hxlog := log_lower_below_two hXpos hXone
  have hwlog := log_lower_above_two hWone
  have hzw :
      z * logLowerAboveTwo (beta0VLarge z - 1 / 100000) ≤
        z * Real.log (beta0VLarge z - 1 / 100000) :=
    mul_le_mul_of_nonneg_left hwlog hz0.le
  rw [beta0PolynomialBookMargin, beta0PolynomialX, beta0V, if_neg hcut]
  dsimp [beta0BookLowerOne]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
    (show (0 : ℝ) ≤ 1 + z by linarith [hz.1])]

def beta0BookLowerTwo (z : ℝ) : ℝ :=
  (1 + z) * logLowerAboveTwo (1 + z) +
    beta0CorrectionLower z +
    (logLowerBelowTwoSharp
        (1 - z * beta0VLarge z) -
      z ^ 2 +
      z * logLowerAboveTwo
        (beta0VLarge z - 1 / 100000)) / 2

lemma beta0_book_lower_two_le {z : ℝ}
    (hz : z ∈ Set.Ioc (1 / 10 : ℝ) (1 / 2)) :
    beta0BookLowerTwo z ≤
      beta0PolynomialBookMargin z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := Beta0Affine.v_lower z hz'
  have hX := Beta0Affine.x_lower z hz'
  have hcut : ¬z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.1]
  have hz0 : 0 < z := by
    linarith [hz.1]
  have hVnonneg : 0 ≤ beta0VLarge z := by
    have hVlarge :
        (3 / 4 : ℝ) ≤ beta0VLarge z := by
      simpa [beta0V, if_neg hcut] using hV
    linarith
  have hXpos :
      0 < 1 - z * beta0VLarge z := by
    have :
        (1 / 5 : ℝ) ≤
          1 - z * beta0VLarge z := by
      simpa [beta0PolynomialX, beta0V,
        if_neg hcut] using hX
    linarith
  have hXone :
      1 - z * beta0VLarge z ≤ 1 := by
    nlinarith [mul_nonneg hz0.le hVnonneg]
  have hWone :=
    beta0_vlarge_book2_log_argument
      ⟨le_of_lt hz.1, hz.2⟩
  have hentropy := log_lower_above_two
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have hcorrection := beta0_correction_lower hz'
  have hxlog :=
    log_lower_below_two_sharp hXpos hXone
  have hwlog := log_lower_above_two hWone
  have hzw :
      z * logLowerAboveTwo
          (beta0VLarge z - 1 / 100000) ≤
        z * Real.log
          (beta0VLarge z - 1 / 100000) :=
    mul_le_mul_of_nonneg_left hwlog hz0.le
  rw [beta0PolynomialBookMargin,
    beta0PolynomialX, beta0V, if_neg hcut]
  dsimp [beta0BookLowerTwo]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
    (show (0 : ℝ) ≤ 1 + z by linarith [hz.1])]

def beta0BookLowerThree (z : ℝ) : ℝ :=
  (1 + z) * logLowerAboveFour (1 + z) +
    beta0CorrectionLower z +
    (logLowerBelowThreeSharp
        (1 - z * beta0VLarge z) -
      z ^ 2 +
      z * logLowerNearOne
        (beta0VLarge z - 1 / 100000)) / 2

lemma beta0_book_lower_three_le {z : ℝ}
    (hz : z ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    beta0BookLowerThree z ≤
      beta0PolynomialBookMargin z := by
  have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hz.1, hz.2]
  have hV := Beta0Affine.v_lower z hz'
  have hX := Beta0Affine.x_lower z hz'
  have hcut : ¬z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.1]
  have hz0 : 0 < z := by
    linarith [hz.1]
  have hVnonneg : 0 ≤ beta0VLarge z := by
    have hVlarge :
        (3 / 4 : ℝ) ≤ beta0VLarge z := by
      simpa [beta0V, if_neg hcut] using hV
    linarith
  have hXpos :
      0 < 1 - z * beta0VLarge z := by
    have :
        (1 / 5 : ℝ) ≤
          1 - z * beta0VLarge z := by
      simpa [beta0PolynomialX, beta0V,
        if_neg hcut] using hX
    linarith
  have hXone :
      1 - z * beta0VLarge z ≤ 1 := by
    nlinarith [mul_nonneg hz0.le hVnonneg]
  have hWbounds :=
    beta0_vlarge_book3_near_one
      ⟨le_of_lt hz.1, hz.2⟩
  have hWpos :
      0 < beta0VLarge z - 1 / 100000 := by
    linarith [hWbounds.1]
  have hWplus :
      0 < beta0VLarge z - 1 / 100000 + 1 := by
    linarith
  have hWabs :
      |(beta0VLarge z - 1 / 100000 - 1) /
          (beta0VLarge z - 1 / 100000 + 1)| ≤
        (7 / 50 : ℝ) := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hWplus]
      nlinarith [hWbounds.1]
    · rw [div_le_iff₀ hWplus]
      nlinarith [hWbounds.2]
  have hentropy := log_lower_above_four
    (show (1 : ℝ) ≤ 1 + z by linarith [hz.1])
  have hcorrection := beta0_correction_lower hz'
  have hxlog :=
    log_lower_below_three_sharp hXpos hXone
  have hwlog := log_lower_near_one hWpos hWabs
  have hzw :
      z * logLowerNearOne
          (beta0VLarge z - 1 / 100000) ≤
        z * Real.log
          (beta0VLarge z - 1 / 100000) :=
    mul_le_mul_of_nonneg_left hwlog hz0.le
  rw [beta0PolynomialBookMargin,
    beta0PolynomialX, beta0V, if_neg hcut]
  dsimp [beta0BookLowerThree]
  nlinarith [mul_le_mul_of_nonneg_left hentropy
    (show (0 : ℝ) ≤ 1 + z by linarith [hz.1])]


end

end Arxiv2407_19026
