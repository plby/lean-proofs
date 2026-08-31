/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos308.CrootRemoval
import ErdosProblems.Erdos285.Proposition7

/-!
# Erdős 308: analytic bounds and exact correction

The estimates in this file turn the finite descent into a representation
theorem.  The intentionally generous logarithmic exponents are more than is
needed for the qualitative consequence of Croot's theorem used by Problem 308.
-/

namespace Erdos308.CrootAsymptotic

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285 Erdos285.PrimePowers Erdos285.RoughCounts
open Erdos308.CrootRemoval

/-! ## The large-prime-power deletion budget -/

lemma sum_Icc_rpow_neg_two_thirds_le (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by
  let f : ℝ → ℝ := fun t ↦ t ^ (-(2 : ℝ) / 3)
  have hanti : AntitoneOn f (Set.Icc 1 (1 + ((Q - 1 : ℕ) : ℝ))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (by norm_num : (-(2 : ℝ) / 3) ≤ 0)).mono
    intro t ht
    exact ht.1.trans_lt' zero_lt_one
  have hsum := hanti.sum_le_integral
  have htop : (1 : ℝ) + (Q - 1 : ℕ) = Q := by
    exact_mod_cast (show 1 + (Q - 1) = Q by omega)
  have htail : (∑ q ∈ Icc 2 Q, f q) ≤ ∫ t in (1 : ℝ)..Q, f t := by
    rw [← htop]
    calc
      (∑ q ∈ Icc 2 Q, f q) =
          ∑ i ∈ Ico 0 (Q - 1), f (i + 2 : ℕ) := by
        symm
        rw [Finset.sum_Ico_add' (fun q : ℕ ↦ f q) 0 (Q - 1) 2]
        apply Finset.sum_congr
        · ext q
          simp
          omega
        · intro q hi
          rfl
      _ = ∑ i ∈ Ico 0 (Q - 1), f (1 + (i + 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        push_cast
        ring
      _ = ∑ i ∈ range (Q - 1), f (1 + (i + 1 : ℕ)) := by
        rw [Finset.range_eq_Ico]
      _ ≤ ∫ t in (1 : ℝ)..1 + (Q - 1 : ℕ), f t := hsum
  have hint : (∫ t in (1 : ℝ)..Q, f t) =
      3 * ((Q : ℝ) ^ ((1 : ℝ) / 3) - 1) := by
    dsimp [f]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(2 : ℝ) / 3))]
    norm_num [Real.one_rpow]
    ring
  have hdecomp : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext q
    simp
    omega
  rw [hdecomp, Finset.sum_insert (by simp)]
  have honeRaw : ((1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by norm_num
  rw [honeRaw]
  calc
    1 + ∑ q ∈ Icc 2 Q, f q ≤ 1 + ∫ t in (1 : ℝ)..Q, f t := by
      simpa [add_comm] using add_le_add_left htail 1
    _ = 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) - 2 := by rw [hint]; ring
    _ ≤ 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by linarith

lemma div_rpow_two_thirds {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    (x / q) ^ ((2 : ℝ) / 3) =
      x ^ ((2 : ℝ) / 3) * q ^ (-(2 : ℝ) / 3) := by
  rw [Real.div_rpow hx hq.le]
  have he : (-(2 : ℝ) / 3) = -((2 : ℝ) / 3) := by ring
  rw [he, Real.rpow_neg hq.le]
  ring

lemma deletion_rpow_identity {x L : ℝ} (hx : 0 < x) (hL : 0 < L) :
    x ^ ((2 : ℝ) / 3) * (x / L ^ 30) ^ ((1 : ℝ) / 3) * L ^ 3 =
      x / L ^ 7 := by
  rw [Real.div_rpow hx.le (pow_nonneg hL.le 30)]
  have hxpow : x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have hLpow : (L ^ 30) ^ ((1 : ℝ) / 3) = L ^ 10 := by
    rw [← Real.rpow_natCast L 30, ← Real.rpow_mul hL.le]
    norm_num
  rw [hLpow]
  field_simp
  nlinarith

def deletionBudget (x : ℕ) : ℕ :=
  ⌈1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7⌉₊

theorem eventually_totalEliminationBudget_le :
    ∀ᶠ x : ℕ in atTop,
      totalEliminationBudget x (mainCutoffNat x) ≤ deletionBudget x := by
  have hQtop : Tendsto mainCutoffNat atTop atTop :=
    logPowerCutoff_tendsto_atTop 30
  have hlogtop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  filter_upwards [eventually_ge_atTop 3,
    hQtop.eventually (eventually_ge_atTop 1),
    hlogtop.eventually (eventually_ge_atTop 1)] with x hx hQ hlog
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlog0 : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
  have hQcut : (mainCutoffNat x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 30 := by
    rw [← show proposition6MainCutoff x =
      (x : ℝ) / Real.log (x : ℝ) ^ 30 by rfl, mainCutoffNat_eq]
    exact Nat.floor_le (div_nonneg hx0 (pow_nonneg hlog0.le _))
  have hsum : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [totalEliminationBudget, Nat.cast_sum]
    calc
      ∑ q ∈ range (mainCutoffNat x + 1),
          (Erdos308.LargePrime.martinBlockBound x q : ℝ) ≤
          ∑ q ∈ range (mainCutoffNat x + 1),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro q hq
        exact Erdos308.LargePrime.martinBlockBound_cast_le hx1
      _ = ∑ q ∈ Icc 1 (mainCutoffNat x),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        rw [show range (mainCutoffNat x + 1) = insert 0 (Icc 1 (mainCutoffNat x)) by
          ext q
          simp
          omega]
        simp
      _ = 200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
            (∑ q ∈ Icc 1 (mainCutoffNat x),
              (q : ℝ) ^ (-(2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqpos : (0 : ℝ) < q := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1)
        rw [div_rpow_two_thirds hx0 hqpos]
        ring
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
            (3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3)) := by
        gcongr
        exact sum_Icc_rpow_neg_two_thirds_le _ hQ
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
            (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3)) := by
        gcongr
      _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        calc
          200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
                (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3)) =
              600 * ((x : ℝ) ^ ((2 : ℝ) / 3) *
                ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3) *
                Real.log (x : ℝ) ^ 3) := by ring
          _ = 600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
            rw [deletion_rpow_identity (by positivity) hlog0]
          _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have htarget : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      _ ≤ 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := hsum
      _ ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        have hr : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        calc
          600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 =
              600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by ring
          _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) :=
            mul_le_mul_of_nonneg_right (by norm_num) hr
          _ = 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (deletionBudget x : ℝ) := Nat.le_ceil _
  exact_mod_cast htarget.trans hceil

/-- The deletion budget, normalized by the lower end of the interval from
which deletion terms are drawn. -/
def deletionBudgetRatio (alpha : ℝ) (x : ℕ) : ℝ :=
  (deletionBudget x : ℝ) / (alpha * (x : ℝ))

def removalRatio : ℝ :=
  (9 / 10 : ℝ) * Erdos308.Numerics.crootIntervalRatio

lemma removalRatio_pos : 0 < removalRatio := by
  norm_num [removalRatio, Erdos308.Numerics.crootIntervalRatio,
    Erdos308.Numerics.crootCandidateRatio]

lemma removalRatio_le_one : removalRatio ≤ 1 := by
  norm_num [removalRatio, Erdos308.Numerics.crootIntervalRatio,
    Erdos308.Numerics.crootCandidateRatio]

lemma deletionBudgetRatio_tendsto_zero (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (deletionBudgetRatio alpha) atTop (𝓝 0) := by
  have hlogPowTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ) ^ 7) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp tendsto_log_coe_at_top
  have hlogInv : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ) ^ 7)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hlogPowTop
  have hxInv : Tendsto (fun x : ℕ ↦ ((x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun x : ℕ ↦ (1000 / alpha) * (Real.log (x : ℝ) ^ 7)⁻¹ +
        alpha⁻¹ * ((x : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using (hlogInv.const_mul (1000 / alpha)).add (hxInv.const_mul alpha⁻¹)
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg halpha.le (Nat.cast_nonneg x))
  · filter_upwards [eventually_ge_atTop 3] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hceil : (deletionBudget x : ℝ) ≤
        1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    dsimp [deletionBudgetRatio]
    calc
      (deletionBudget x : ℝ) / (alpha * (x : ℝ)) ≤
          (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) /
            (alpha * (x : ℝ)) := by
              exact div_le_div_of_nonneg_right hceil (mul_nonneg halpha.le hxpos.le)
      _ = (1000 / alpha) * (Real.log (x : ℝ) ^ 7)⁻¹ +
          alpha⁻¹ * ((x : ℝ))⁻¹ := by field_simp
  · exact hupper

lemma reciprocalMass_le_card_div {A : Finset ℕ} {alpha : ℝ} {x : ℕ}
    (halpha : 0 < alpha) (hx : 0 < x)
    (hA : ∀ n ∈ A, alpha * (x : ℝ) < n) :
    reciprocalMass A ≤ (A.card : ℝ) / (alpha * (x : ℝ)) := by
  have hden : 0 < alpha * (x : ℝ) := mul_pos halpha (by exact_mod_cast hx)
  rw [reciprocalMass]
  calc
    ∑ n ∈ A, (n : ℝ)⁻¹ ≤ ∑ _n ∈ A, (alpha * (x : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := hden.trans (hA n hn)
      exact (inv_le_inv₀ hnpos hden).2 (hA n hn).le
    _ = (A.card : ℝ) / (alpha * (x : ℝ)) := by
      simp [div_eq_mul_inv]

lemma correctionScale_tendsto_atTop :
    Tendsto Erdos285.approximationCorrectionScale atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ)⁻¹)).comp
  exact tendsto_natCast_atTop_atTop

lemma correctionScale_pow_five_le (x : ℕ) :
    Erdos285.approximationCorrectionScale x ^ 5 ≤ x := by
  have h := pow_le_pow_left₀
    (Nat.cast_nonneg (Erdos285.approximationCorrectionScale x))
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)) 5
  have hp : ((x : ℝ) ^ ((5 : ℝ)⁻¹) : ℝ) ^ 5 = x := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    norm_num
  rw [hp] at h
  exact_mod_cast h

/-- The exact correction denominators lie below the interval used by the
large-prime-power deletion. -/
lemma eventually_correctionCutoff_le_removalFloor :
    ∀ᶠ x : ℕ in atTop,
      2 * Erdos285.approximationCorrectionScale x ^ 4 ≤
        ⌊removalRatio * (x : ℝ)⌋₊ := by
  have hyLarge := correctionScale_tendsto_atTop.eventually
    (eventually_ge_atTop ⌈3 / removalRatio⌉₊)
  filter_upwards [hyLarge, correctionScale_tendsto_atTop.eventually_ge_atTop 2]
      with x hyLarge hyTwo
  let y := Erdos285.approximationCorrectionScale x
  have hyRatio : (3 : ℝ) ≤ removalRatio * y := by
    have hceil : 3 / removalRatio ≤ (⌈3 / removalRatio⌉₊ : ℕ) :=
      Nat.le_ceil _
    have hcast : ((⌈3 / removalRatio⌉₊ : ℕ) : ℝ) ≤ y := by
      exact_mod_cast hyLarge
    have := hceil.trans hcast
    rw [div_le_iff₀ removalRatio_pos] at this
    simpa [mul_comm] using this
  have hy4one : (1 : ℝ) ≤ (y : ℝ) ^ 4 := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ y by omega))
  have hy5 : y ^ 5 ≤ x := correctionScale_pow_five_le x
  have hreal : ((2 * y ^ 4 : ℕ) : ℝ) ≤ removalRatio * (x : ℝ) := by
    push_cast
    calc
      2 * (y : ℝ) ^ 4 ≤ 3 * (y : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ (removalRatio * y) * (y : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hyRatio (by positivity)
      _ = removalRatio * ((y : ℝ) ^ 5) := by ring
      _ ≤ removalRatio * (x : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ removalRatio_pos.le
        exact_mod_cast hy5
  exact Nat.le_floor hreal

lemma logPow30_div_fifthRoot_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) ^ 30 /
        (x : ℝ) ^ ((1 : ℝ) / 5)) atTop (𝓝 0) := by
  have hreal :=
    (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 5) (30 : ℝ)
      (by norm_num)).tendsto_div_nhds_zero
  have hcomp := hreal.comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, Real.rpow_natCast] using hcomp

/-- The exact-correction denominators are also smooth at the main cutoff. -/
lemma eventually_correctionCutoff_le_mainCutoff :
    ∀ᶠ x : ℕ in atTop,
      2 * Erdos285.approximationCorrectionScale x ^ 4 ≤ mainCutoffNat x := by
  have hratio : Tendsto
      (fun x : ℕ ↦
        2 * (Real.log (x : ℝ) ^ 30 /
          (x : ℝ) ^ ((1 : ℝ) / 5)) +
        ((x : ℝ) ^ ((1 : ℝ) / 5))⁻¹) atTop (𝓝 0) := by
    have hrootTop : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ ((1 : ℝ) / 5))
        atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 5)).comp
        tendsto_natCast_atTop_atTop
    simpa using (logPow30_div_fifthRoot_tendsto_zero.const_mul 2).add
      (tendsto_inv_atTop_zero.comp hrootTop)
  have hsmall := hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 3] with x hsmall hx
  let y := Erdos285.approximationCorrectionScale x
  let root := (x : ℝ) ^ ((5 : ℝ)⁻¹)
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hroot : 0 < root := Real.rpow_pos_of_pos hxR _
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hsum : (2 * Real.log (x : ℝ) ^ 30 + 1) / root < 1 := by
    rw [add_div, one_div]
    simpa [root, show (1 : ℝ) / 5 = (5 : ℝ)⁻¹ by norm_num,
      mul_div_assoc] using hsmall
  have hrootLower : 2 * Real.log (x : ℝ) ^ 30 + 1 < root := by
    rwa [div_lt_one hroot] at hsum
  have hrootFloor : root < (y + 1 : ℕ) := by
    dsimp [root, y, Erdos285.approximationCorrectionScale]
    simpa [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
  have hlogY : 2 * Real.log (x : ℝ) ^ 30 < (y : ℝ) := by
    push_cast at hrootFloor
    dsimp [root] at hrootLower hrootFloor
    linarith
  have hy5 : y ^ 5 ≤ x := correctionScale_pow_five_le x
  have hprod : 2 * (y : ℝ) ^ 4 * Real.log (x : ℝ) ^ 30 < (x : ℝ) := by
    have hypos : (0 : ℝ) < y := by
      have : 0 < 2 * Real.log (x : ℝ) ^ 30 := by positivity
      linarith [hlogY]
    calc
      2 * (y : ℝ) ^ 4 * Real.log (x : ℝ) ^ 30 =
          (y : ℝ) ^ 4 * (2 * Real.log (x : ℝ) ^ 30) := by ring
      _ < (y : ℝ) ^ 4 * y := by
        exact mul_lt_mul_of_pos_left hlogY (pow_pos hypos 4)
      _ = ((y : ℝ) ^ 5) := by ring
      _ ≤ (x : ℝ) := by exact_mod_cast hy5
  have hcut : ((2 * y ^ 4 : ℕ) : ℝ) ≤ proposition6MainCutoff x := by
    rw [proposition6MainCutoff]
    push_cast
    apply (le_div_iff₀ (pow_pos hlog 30)).2
    nlinarith
  rw [mainCutoffNat_eq]
  exact Nat.le_floor hcut

/-! ## Reciprocal mass of the nonsmooth denominators -/

def cofactorBound (x : ℕ) : ℕ :=
  x / (mainCutoffNat x + 1)

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun n _ _ ↦
    inv_nonneg.mpr (Nat.cast_nonneg n)

lemma multiplesUpTo_eq_image (x q : ℕ) (hq : 1 ≤ q) :
    multiplesUpTo x q =
      (Finset.Icc 1 (x / q)).image (fun m : ℕ ↦ q * m) := by
  ext n
  simp only [mem_multiplesUpTo, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hn1, hnN, ⟨m, rfl⟩⟩
    refine ⟨m, ⟨?_, (Nat.le_div_iff_mul_le hq).2 ?_⟩, rfl⟩
    · by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      simp [this] at hn1
    · simpa [Nat.mul_comm] using hnN
  · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
    refine ⟨Nat.mul_pos (Nat.zero_lt_of_lt hq) hm1, ?_, dvd_mul_right q m⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hmN

lemma reciprocalMass_multiplesUpTo (x q : ℕ) (hq : 1 ≤ q) :
    reciprocalMass (multiplesUpTo x q) =
      (q : ℝ)⁻¹ * (((harmonic (x / q) : ℚ) : ℝ)) := by
  rw [multiplesUpTo_eq_image x q hq]
  unfold reciprocalMass
  rw [Finset.sum_image]
  · rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp_rw [Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
    rw [Nat.cast_mul]
    field_simp [hq0, hm0]
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hq) hab

lemma cofactor_le (x q : ℕ)
    (hq : q ∈ largePrimePowers x (mainCutoffNat x)) :
    x / q ≤ cofactorBound x := by
  rw [cofactorBound]
  have hq' : mainCutoffNat x + 1 ≤ q := by
    simpa using (mem_largePrimePowers.mp hq).1
  exact Nat.div_le_div_left hq' (by omega)

lemma harmonic_mono_local {a b : ℕ} (hab : a ≤ b) : harmonic a ≤ harmonic b := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right hab) fun n _ _ ↦ by positivity

lemma harmonic_nonneg_local (n : ℕ) : 0 ≤ harmonic n := by
  rw [harmonic_eq_sum_Icc]
  positivity

lemma roughMass_le_harmonic_mul_tail (x : ℕ) :
    reciprocalMass (roughNumbersIn 1 x (mainCutoffNat x)) ≤
      (((harmonic (cofactorBound x) : ℚ) : ℝ)) *
        primePowerReciprocalTail x (mainCutoffNat x) := by
  calc
    reciprocalMass (roughNumbersIn 1 x (mainCutoffNat x)) ≤
        reciprocalMass ((largePrimePowers x (mainCutoffNat x)).biUnion
          (multiplesUpTo x)) :=
      reciprocalMass_mono (roughNumbersIn_subset_biUnion 1 x (mainCutoffNat x))
    _ ≤ ∑ q ∈ largePrimePowers x (mainCutoffNat x),
          reciprocalMass (multiplesUpTo x q) := by
      exact UnitFractions.sum_bUnion_le_sum_of_nonneg fun n hn ↦
        inv_nonneg.mpr (Nat.cast_nonneg n)
    _ ≤ ∑ q ∈ largePrimePowers x (mainCutoffNat x),
          (q : ℝ)⁻¹ * (((harmonic (cofactorBound x) : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 1 ≤ q := (mem_largePrimePowers.mp hq).2.2.one_lt.le
      rw [reciprocalMass_multiplesUpTo x q hq1]
      gcongr
      exact_mod_cast harmonic_mono_local (cofactor_le x q hq)
    _ = (((harmonic (cofactorBound x) : ℚ) : ℝ)) *
        primePowerReciprocalTail x (mainCutoffNat x) := by
      simp only [primePowerReciprocalTail]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

lemma eventually_cofactorBound_le_ceil_log_pow :
    ∀ᶠ x : ℕ in atTop,
      cofactorBound x ≤ ⌈Real.log (x : ℝ) ^ (30 : ℕ)⌉₊ := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with x hlog hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hL : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
  have hfloor : (x : ℝ) / Real.log (x : ℝ) ^ 30 <
      (mainCutoffNat x + 1 : ℕ) := by
    simpa [mainCutoffNat_eq, proposition6MainCutoff] using
      Nat.lt_floor_add_one ((x : ℝ) / Real.log (x : ℝ) ^ 30)
  have hden : (0 : ℝ) < (mainCutoffNat x + 1 : ℕ) := by positivity
  have hreal : (x : ℝ) / (mainCutoffNat x + 1 : ℕ) <
      Real.log (x : ℝ) ^ 30 := by
    rw [div_lt_iff₀ hden]
    have hpow : 0 < Real.log (x : ℝ) ^ (30 : ℕ) := pow_pos hL _
    have := mul_lt_mul_of_pos_right hfloor hpow
    field_simp [hpow.ne'] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hcast : ((cofactorBound x : ℕ) : ℝ) ≤
      (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := by
    exact Nat.cast_div_le
  have hceil : Real.log (x : ℝ) ^ (30 : ℕ) ≤
      ((⌈Real.log (x : ℝ) ^ (30 : ℕ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  exact_mod_cast (hcast.trans hreal.le).trans hceil

lemma cofactorHarmonic_div_sqrt_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ (((harmonic (cofactorBound x) : ℚ) : ℝ)) /
        Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0) := by
  let G : ℕ → ℝ := fun x ↦
    (1 + Real.log 2) * (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
      30 * (Real.log (Real.log (x : ℝ)) /
        Real.sqrt (Real.log (x : ℝ)))
  have hG : Tendsto G atTop (𝓝 0) := by
    dsimp [G]
    simpa using
      (inv_sqrt_log_tendsto_zero.const_mul (1 + Real.log 2)).add
        (loglog_div_sqrt_log_tendsto_zero.const_mul 30)
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    exact div_nonneg (by exact_mod_cast harmonic_nonneg_local (cofactorBound x)) hsqrt.le
  · filter_upwards [eventually_cofactorBound_le_ceil_log_pow,
      tendsto_log_coe_at_top.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 2] with x hcof hlog hx
    have hL : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hL
    have hpow : 1 ≤ Real.log (x : ℝ) ^ (30 : ℕ) := one_le_pow₀ hlog
    have hceilCast :
        ((⌈Real.log (x : ℝ) ^ (30 : ℕ)⌉₊ : ℕ) : ℝ) <
          Real.log (x : ℝ) ^ 30 + 1 :=
      Nat.ceil_lt_add_one (pow_nonneg hL.le _)
    have hceilTwo :
        ((⌈Real.log (x : ℝ) ^ (30 : ℕ)⌉₊ : ℕ) : ℝ) ≤
          2 * Real.log (x : ℝ) ^ 30 := by linarith
    have hharm : (((harmonic (cofactorBound x) : ℚ) : ℝ)) ≤
        1 + Real.log (cofactorBound x : ℝ) := harmonic_le_one_add_log _
    have hlogC : Real.log (cofactorBound x : ℝ) ≤
        Real.log (2 * Real.log (x : ℝ) ^ 30) := by
      by_cases hzero : cofactorBound x = 0
      · rw [hzero]
        norm_num only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by
          have : (1 : ℝ) ≤ 2 * Real.log (x : ℝ) ^ 30 := by nlinarith
          exact this)
      · apply Real.strictMonoOn_log.monotoneOn
        · exact Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hzero)
        · exact Set.mem_Ioi.mpr (mul_pos (by norm_num) (pow_pos hL _))
        · have hcofR : (cofactorBound x : ℝ) ≤
              (⌈Real.log (x : ℝ) ^ (30 : ℕ)⌉₊ : ℕ) := by exact_mod_cast hcof
          exact hcofR.trans hceilTwo
    have hlogExpand : Real.log (2 * Real.log (x : ℝ) ^ 30) =
        Real.log 2 + 30 * Real.log (Real.log (x : ℝ)) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hL.ne'),
        Real.log_pow]
      norm_num
    dsimp [G]
    rw [div_eq_mul_inv]
    have hmain : (((harmonic (cofactorBound x) : ℚ) : ℝ)) ≤
        1 + Real.log 2 + 30 * Real.log (Real.log (x : ℝ)) := by
      rw [hlogExpand] at hlogC
      linarith
    have hinv : 0 ≤ (Real.sqrt (Real.log (x : ℝ)))⁻¹ := inv_nonneg.mpr hsqrt.le
    calc
      (((harmonic (cofactorBound x) : ℚ) : ℝ)) *
          (Real.sqrt (Real.log (x : ℝ)))⁻¹ ≤
          (1 + Real.log 2 + 30 * Real.log (Real.log (x : ℝ))) *
            (Real.sqrt (Real.log (x : ℝ)))⁻¹ :=
        mul_le_mul_of_nonneg_right hmain hinv
      _ = (1 + Real.log 2) * (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
          30 * (Real.log (Real.log (x : ℝ)) /
            Real.sqrt (Real.log (x : ℝ))) := by
        rw [div_eq_mul_inv]
        ring
  · exact hG

theorem globalRoughMass_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (roughNumbersIn 1 x (mainCutoffNat x))) atTop (𝓝 0) := by
  have htail := primePowerReciprocalTail_logPowerCutoff_mul_sqrt_tendsto_zero 30
  have hprod := cofactorHarmonic_div_sqrt_tendsto_zero.mul htail
  apply squeeze_zero' (g := fun x : ℕ ↦
    ((((harmonic (cofactorBound x) : ℚ) : ℝ)) /
      Real.sqrt (Real.log (x : ℝ))) *
      (primePowerReciprocalTail x (mainCutoffNat x) *
        Real.sqrt (Real.log (x : ℝ))))
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [eventually_ge_atTop 2] with x hx
    refine (roughMass_le_harmonic_mul_tail x).trans ?_
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    have heq :
        (((harmonic (cofactorBound x) : ℚ) : ℝ)) *
            primePowerReciprocalTail x (mainCutoffNat x) =
          ((((harmonic (cofactorBound x) : ℚ) : ℝ)) /
              Real.sqrt (Real.log (x : ℝ))) *
            (primePowerReciprocalTail x (mainCutoffNat x) *
              Real.sqrt (Real.log (x : ℝ))) := by
      field_simp [hsqrt.ne']
    exact heq.le
  · simpa [mainCutoffNat] using hprod

/-! ## Smooth-set identities and a finite crossing lemma -/

lemma ratCast_recSum_eq_reciprocalMass (A : Finset ℕ) :
    ((UnitFractions.rec_sum A : ℚ) : ℝ) = reciprocalMass A := by
  simp [UnitFractions.rec_sum, reciprocalMass]

lemma reciprocalMass_Icc_eq_harmonic (x : ℕ) :
    reciprocalMass (Icc 1 x) = ((harmonic x : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp [reciprocalMass]

lemma reciprocalMass_sdiff {A B : Finset ℕ} (hBA : B ⊆ A) :
    reciprocalMass (A \ B) = reciprocalMass A - reciprocalMass B := by
  unfold reciprocalMass
  have h := Finset.sum_sdiff hBA (f := fun n : ℕ ↦ (n : ℝ)⁻¹)
  linarith

lemma isSmooth_iff_largestPrimePowerPart_le_floor {z : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hn : n ≠ 0) :
    UnitFractions.is_smooth z n ↔ largestPrimePowerPart n ≤ ⌊z⌋₊ := by
  constructor
  · exact fun h ↦ largestPrimePowerPart_le_floor_of_isSmooth h
  · intro h
    apply isSmooth_of_largestPrimePowerPart_le hn
    exact (by exact_mod_cast h : (largestPrimePowerPart n : ℝ) ≤ (⌊z⌋₊ : ℕ)).trans
      (Nat.floor_le hz)

lemma fullSmoothBlock_eq_sdiff (x : ℕ) :
    fullSmoothBlock x (proposition6MainCutoff x) =
      Icc 1 x \ roughNumbersIn 1 x (mainCutoffNat x) := by
  have hz : 0 ≤ proposition6MainCutoff x := by
    unfold proposition6MainCutoff
    positivity
  ext n
  simp only [fullSmoothBlock, initialSmoothBlock, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc, mem_roughNumbersIn]
  have hnzero_of_bounds : 0 < n → n ≠ 0 := Nat.ne_of_gt
  constructor
  · rintro ⟨⟨hn0, hnx⟩, hs⟩
    have hmax := (isSmooth_iff_largestPrimePowerPart_le_floor hz
      (hnzero_of_bounds (by simpa using hn0))).1 hs
    exact ⟨⟨by omega, hnx⟩, by
      rw [mainCutoffNat_eq]
      omega⟩
  · rintro ⟨⟨hn1, hnx⟩, hnrough⟩
    have hmax : largestPrimePowerPart n ≤
        ⌊proposition6MainCutoff x⌋₊ := by
      rw [← mainCutoffNat_eq]
      apply Nat.le_of_not_gt
      intro hgt
      exact hnrough ⟨hn1, hnx, hgt⟩
    have hn0 : ⌊(0 : ℝ) * (x : ℝ)⌋₊ < n := by
      simpa using (show 0 < n by omega)
    exact ⟨⟨hn0, hnx⟩,
      (isSmooth_iff_largestPrimePowerPart_le_floor hz
        (by omega : n ≠ 0)).2 hmax⟩

lemma fullSmoothBlock_mass (x : ℕ) :
    reciprocalMass (fullSmoothBlock x (proposition6MainCutoff x)) =
      ((harmonic x : ℚ) : ℝ) -
        reciprocalMass (roughNumbersIn 1 x (mainCutoffNat x)) := by
  have hsub : roughNumbersIn 1 x (mainCutoffNat x) ⊆ Icc 1 x := by
    intro n hn
    have hn' := mem_roughNumbersIn.mp hn
    exact Finset.mem_Icc.mpr ⟨hn'.1, hn'.2.1⟩
  rw [fullSmoothBlock_eq_sdiff, reciprocalMass_sdiff hsub,
    reciprocalMass_Icc_eq_harmonic]

/-- Add nonnegative terms until a real threshold is first crossed. -/
lemma exists_subset_sum_crossing
    {T : Finset ℕ} {w : ℕ → ℝ} {base target step : ℝ}
    (hw0 : ∀ n ∈ T, 0 ≤ w n)
    (hwstep : ∀ n ∈ T, w n ≤ step)
    (hbase : base ≤ target)
    (htotal : target < base + ∑ n ∈ T, w n) :
    ∃ U ⊆ T,
      target < base + ∑ n ∈ U, w n ∧
      base + ∑ n ∈ U, w n ≤ target + step := by
  classical
  induction T using Finset.induction_on generalizing base with
  | empty =>
      simp only [sum_empty, add_zero] at htotal
      exact (not_lt_of_ge hbase htotal).elim
  | @insert a T ha ih =>
      by_cases hfirst : target < base + w a
      · refine ⟨{a}, by simp, ?_, ?_⟩
        · simpa using hfirst
        · simp
          linarith [hwstep a (by simp)]
      · have hbase' : base + w a ≤ target := le_of_not_gt hfirst
        have htotal' : target < (base + w a) + ∑ n ∈ T, w n := by
          simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using htotal
        obtain ⟨U, hUT, hlow, hupp⟩ := ih
          (fun n hn ↦ hw0 n (by simp [hn]))
          (fun n hn ↦ hwstep n (by simp [hn])) hbase' htotal'
        refine ⟨insert a U, ?_, ?_, ?_⟩
        · exact Finset.insert_subset_insert a hUT
        · rw [Finset.sum_insert]
          · linarith
          · intro haU
            exact ha (hUT haU)
        · rw [Finset.sum_insert]
          · linarith
          · intro haU
            exact ha (hUT haU)

/-! ## The protected terminal block has mass below five -/

def protectedBase (x : ℕ) : Finset ℕ :=
  insert 1 (removalBase x (proposition6MainCutoff x))

lemma reciprocalMass_Ioc_eq_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    reciprocalMass (Ioc a b) =
      ((harmonic b : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
  have hsub : Icc 1 a ⊆ Icc 1 b := Finset.Icc_subset_Icc_right hab
  have hdiff : Ioc a b = Icc 1 b \ Icc 1 a := by
    ext n
    simp
    omega
  rw [hdiff, reciprocalMass_sdiff hsub,
    reciprocalMass_Icc_eq_harmonic, reciprocalMass_Icc_eq_harmonic]

lemma terminalInterval_mass_tendsto :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (Ioc ⌊removalRatio * (x : ℝ)⌋₊ x))
      atTop (𝓝 (-Real.log removalRatio)) := by
  let a : ℕ → ℕ := fun x ↦ ⌊removalRatio * (x : ℝ)⌋₊
  have haTop : Tendsto a atTop atTop :=
    tendsto_nat_floor_mul_atTop removalRatio removalRatio_pos
  have herror : Tendsto
      (fun x : ℕ ↦
        (((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ)) -
        (((harmonic (a x) : ℚ) : ℝ) - Real.log (a x : ℝ)))
      atTop (𝓝 0) := by
    simpa [a] using Real.tendsto_harmonic_sub_log.sub
      (Real.tendsto_harmonic_sub_log.comp haTop)
  have hratio : Tendsto
      (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)) atTop (𝓝 removalRatio) := by
    change Tendsto
      ((fun t : ℝ ↦ ((⌊removalRatio * t⌋₊ : ℕ) : ℝ) / t) ∘
        (fun x : ℕ ↦ (x : ℝ))) atTop (𝓝 removalRatio)
    exact (tendsto_nat_floor_mul_div_atTop removalRatio_pos.le).comp
      tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto
      (Real.log ∘ (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)))
      atTop (𝓝 (Real.log removalRatio)) :=
    (Real.continuousAt_log removalRatio_pos.ne').tendsto.comp hratio
  have hlogdiff : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log (a x : ℝ))
      atTop (𝓝 (-Real.log removalRatio)) := by
    apply hlogratio.neg.congr'
    filter_upwards [eventually_ge_atTop 1,
      haTop.eventually (eventually_ge_atTop 1)] with x hx hax
    change -Real.log ((a x : ℝ) / (x : ℝ)) = _
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  have htotal := herror.add hlogdiff
  have htotal' : Tendsto
      (fun x : ℕ ↦ ((harmonic x : ℚ) : ℝ) -
        ((harmonic (a x) : ℚ) : ℝ))
      atTop (𝓝 (-Real.log removalRatio)) := by
    convert htotal using 1
    · funext x
      ring
    · simp
  apply htotal'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hale : a x ≤ x := by
    dsimp [a]
    have hreal : ((⌊removalRatio * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg removalRatio_pos.le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) removalRatio_le_one)
    exact_mod_cast hreal
  symm
  simpa [a] using reciprocalMass_Ioc_eq_harmonic_sub hale

lemma one_sub_log_removalRatio_lt_five :
    1 - Real.log removalRatio < 5 := by
  have hexp4 : (50 : ℝ) < Real.exp 4 := by
    have heq : Real.exp (4 : ℝ) = Real.exp 1 ^ (4 : ℕ) := by
      symm
      simp
    rw [heq]
    have h27 : (27 / 10 : ℝ) < Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hpow := pow_lt_pow_left₀ h27 (by norm_num : (0 : ℝ) ≤ 27 / 10)
      (by norm_num : (4 : ℕ) ≠ 0)
    exact (by norm_num : (50 : ℝ) < (27 / 10 : ℝ) ^ (4 : ℕ)).trans hpow
  have hexpNeg : Real.exp (-4 : ℝ) < 1 / 50 := by
    rw [Real.exp_neg]
    simpa [one_div] using
      (inv_lt_inv₀ (by positivity : 0 < Real.exp (4 : ℝ))
        (by norm_num : (0 : ℝ) < 50)).2 hexp4
  have hratio : (1 / 50 : ℝ) < removalRatio := by
    norm_num [removalRatio, Erdos308.Numerics.crootIntervalRatio,
      Erdos308.Numerics.crootCandidateRatio]
  have hlog : (-4 : ℝ) < Real.log removalRatio := by
    have hmono := Real.strictMonoOn_log (Real.exp_pos (-4)) removalRatio_pos
      (hexpNeg.trans hratio)
    simpa using hmono
  linarith

theorem eventually_protectedBase_mass_lt_five :
    ∀ᶠ x : ℕ in atTop, reciprocalMass (protectedBase x) < 5 := by
  have hupper : Tendsto
      (fun x : ℕ ↦ 1 + reciprocalMass
        (Ioc ⌊removalRatio * (x : ℝ)⌋₊ x))
      atTop (𝓝 (1 - Real.log removalRatio)) := by
    simpa [sub_eq_add_neg] using terminalInterval_mass_tendsto.const_add 1
  have hevent := hupper.eventually (Iio_mem_nhds one_sub_log_removalRatio_lt_five)
  filter_upwards [hevent] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [protectedBase]
  by_cases hmem : 1 ∈ removalBase x (proposition6MainCutoff x)
  · rw [Finset.insert_eq_of_mem hmem]
    calc
      reciprocalMass (removalBase x (proposition6MainCutoff x)) ≤
          reciprocalMass (Ioc ⌊removalRatio * (x : ℝ)⌋₊ x) := by
        apply reciprocalMass_mono
        intro n hn
        simpa [removalBase, removalRatio, initialSmoothBlock] using
          (Finset.mem_filter.mp hn).1
      _ ≤ 1 + reciprocalMass (Ioc ⌊removalRatio * (x : ℝ)⌋₊ x) := by
        linarith [reciprocalMass_nonneg
          (Ioc ⌊removalRatio * (x : ℝ)⌋₊ x)]
  · rw [reciprocalMass, Finset.sum_insert hmem]
    simp only [Nat.cast_one, inv_one]
    gcongr
    apply reciprocalMass_mono
    intro n hn
    simpa [removalBase, removalRatio, initialSmoothBlock] using
      (Finset.mem_filter.mp hn).1

end

end Erdos308.CrootAsymptotic

#print axioms Erdos308.CrootAsymptotic.eventually_totalEliminationBudget_le
