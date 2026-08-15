/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Proposition6
import ErdosProblems.Erdos285.RoughCounts

/-!
# Erdős 285: analytic estimates for Martin's Proposition 6

This file proves the analytic and counting assertions for the explicit initial
block used in `Proposition6.lean`.  The main cutoff is `x / log(x)^30`.  The
integers discarded from a terminal interval are covered by large exact
prime-power divisors, so the prime-power Mertens estimate in `RoughCounts`
shows that both their relative cardinality and their reciprocal mass vanish.

The final section gives a concrete summable deletion budget and compares it
with the elementary five-prime reservoir from `SmoothReservoir.lean`.
-/

namespace Erdos285

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open PrimePowers RoughCounts

/-- The natural-valued version of the main cutoff. -/
def mainCutoffNat (x : ℕ) : ℕ :=
  logPowerCutoff 30 x

lemma mainCutoffNat_eq (x : ℕ) :
    mainCutoffNat x = ⌊proposition6MainCutoff x⌋₊ := by
  rfl

/-- The lower endpoint ratio for the target `r = 1`. -/
def oneLowerRatio : ℝ := Real.exp (-1)

/-- The unfiltered terminal interval for `r = 1`. -/
def fullInitialInterval (x : ℕ) : Finset ℕ :=
  Ioc ⌊oneLowerRatio * (x : ℝ)⌋₊ x

/-- Martin's explicit initial block for `r = 1`. -/
def initialBlockOne (x : ℕ) : Finset ℕ :=
  initialSmoothBlock oneLowerRatio x (proposition6MainCutoff x)

lemma oneLowerRatio_pos : 0 < oneLowerRatio := by
  exact Real.exp_pos _

lemma oneLowerRatio_lt_one : oneLowerRatio < 1 := by
  rw [oneLowerRatio, Real.exp_lt_one_iff]
  norm_num

/-! ## Smoothness and exact prime-power parts -/

/-- Smoothness can be tested on the largest exact prime-power part. -/
lemma isSmooth_iff_largestPrimePowerPart_le_floor {z : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hn : n ≠ 0) :
    UnitFractions.is_smooth z n ↔ largestPrimePowerPart n ≤ ⌊z⌋₊ := by
  constructor
  · intro hs
    by_cases hn2 : 2 ≤ n
    · have hmem := largestPrimePowerPart_mem hn2
      have hspec := (mem_primePowerParts hn).mp hmem
      exact Nat.le_floor (hs _ hspec.1 hspec.2.1)
    · have hempty : primePowerParts n = ∅ :=
        primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn2)
      simp [largestPrimePowerPart, hempty]
  · intro hmax q hqpp hqdiv
    have hqexact : ∃ r : ℕ, r ∈ primePowerParts n ∧ q ∣ r := by
      rcases (isPrimePow_nat_iff q).1 hqpp with ⟨p, k, hp, hk, rfl⟩
      let r := p ^ n.factorization p
      have hk' : k ≤ n.factorization p :=
        (hp.pow_dvd_iff_le_factorization hn).1 hqdiv
      have hfac : n.factorization p ≠ 0 := Nat.ne_zero_of_lt (lt_of_lt_of_le hk hk')
      have hrd : r ∣ n := by
        dsimp [r]
        simpa using Nat.ordProj_dvd n p
      have hcop : Nat.Coprime r (n / r) := by
        dsimp [r]
        exact ((UnitFractions.factorization_eq_iff (n := n) hp hfac).2 rfl).2
      refine ⟨r, (mem_primePowerParts hn).2
        ⟨hp.isPrimePow.pow hfac, hrd, hcop⟩, ?_⟩
      dsimp [r]
      exact pow_dvd_pow p hk'
    obtain ⟨r, hrmem, hqr⟩ := hqexact
    have hrpos : 0 < r := ((mem_primePowerParts hn).1 hrmem).1.pos
    have hqle : q ≤ ⌊z⌋₊ :=
      (Nat.le_of_dvd hrpos hqr).trans
        ((le_largestPrimePowerPart hrmem).trans hmax)
    exact (Nat.cast_le.2 hqle).trans (Nat.floor_le hz)

lemma initialBlockOne_eq_filter_largest (x : ℕ)
    (hcut : 0 ≤ proposition6MainCutoff x) :
    initialBlockOne x =
      (fullInitialInterval x).filter
        (fun n ↦ largestPrimePowerPart n ≤ mainCutoffNat x) := by
  ext n
  simp only [initialBlockOne, initialSmoothBlock, fullInitialInterval,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hnI, hs⟩
    refine ⟨hnI, (isSmooth_iff_largestPrimePowerPart_le_floor hcut ?_).1 hs⟩
    omega
  · rintro ⟨hnI, hs⟩
    refine ⟨hnI, (isSmooth_iff_largestPrimePowerPart_le_floor hcut ?_).2 hs⟩
    omega

/-- The discarded part of the terminal interval. -/
def initialRoughPart (x : ℕ) : Finset ℕ :=
  roughNumbersIn (⌊oneLowerRatio * (x : ℝ)⌋₊ + 1) x (mainCutoffNat x)

lemma initialRoughPart_subset_full (x : ℕ) :
    initialRoughPart x ⊆ fullInitialInterval x := by
  intro n hn
  rw [initialRoughPart, mem_roughNumbersIn] at hn
  simp only [fullInitialInterval, Finset.mem_Ioc]
  omega

lemma initialRoughPart_subset_global (x : ℕ) :
    initialRoughPart x ⊆ roughNumbersIn 1 x (mainCutoffNat x) := by
  intro n hn
  rw [initialRoughPart, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  exact ⟨by omega, hn.2.1, hn.2.2⟩

lemma initialBlockOne_eq_sdiff (x : ℕ)
    (hcut : 0 ≤ proposition6MainCutoff x) :
    initialBlockOne x = fullInitialInterval x \ initialRoughPart x := by
  rw [initialBlockOne_eq_filter_largest x hcut]
  ext n
  simp only [Finset.mem_filter, Finset.mem_sdiff, initialRoughPart,
    mem_roughNumbersIn, fullInitialInterval, Finset.mem_Ioc]
  omega

/-! ## Cardinality of the initial block -/

lemma proposition6MainCutoff_nonneg (x : ℕ) :
    0 ≤ proposition6MainCutoff x := by
  unfold proposition6MainCutoff
  positivity

lemma mainCutoffNat_spec :
    (∀ᶠ x : ℕ in atTop, mainCutoffNat x ≤ x) ∧
      Tendsto mainCutoffNat atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (mainCutoffNat x : ℝ)))
        atTop (𝓝 0) := by
  change
    (∀ᶠ x : ℕ in atTop, logPowerCutoff 30 x ≤ x) ∧
      Tendsto (logPowerCutoff 30) atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (logPowerCutoff 30 x : ℝ)))
        atTop (𝓝 0)
  exact logPowerCutoff_spec 30

lemma fullInitialInterval_card_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ ((fullInitialInterval x).card : ℝ) / x)
      atTop (𝓝 (1 - oneLowerRatio)) := by
  have hfloor : Tendsto
      (fun x : ℕ ↦ ((⌊oneLowerRatio * (x : ℝ)⌋₊ : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 oneLowerRatio) :=
    (tendsto_nat_floor_mul_div_atTop oneLowerRatio_pos.le).comp
      tendsto_natCast_atTop_atTop
  have hlim :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hfloor
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hfloorle : ⌊oneLowerRatio * (x : ℝ)⌋₊ ≤ x := by
    have hreal : ((⌊oneLowerRatio * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg oneLowerRatio_pos.le (Nat.cast_nonneg x))).trans
      (mul_le_of_le_one_left (Nat.cast_nonneg x) oneLowerRatio_lt_one.le)
    exact_mod_cast hreal
  rw [show (fullInitialInterval x).card = x - ⌊oneLowerRatio * (x : ℝ)⌋₊ by
    simp [fullInitialInterval], Nat.cast_sub hfloorle]
  field_simp

lemma initialRoughPart_card_ratio_tendsto_zero :
    Tendsto (fun x : ℕ ↦ ((initialRoughPart x).card : ℝ) / x)
      atTop (𝓝 0) := by
  have hglobal := (roughNumbersIn_logPowerCutoff_card_isLittleO 30).tendsto_div_nhds_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with x
    have hc : ((initialRoughPart x).card : ℝ) ≤
        ((roughNumbersIn 1 x (mainCutoffNat x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (initialRoughPart_subset_global x)
    exact div_le_div_of_nonneg_right
      hc
      (Nat.cast_nonneg x)
  · simpa [mainCutoffNat] using hglobal

/-- The smooth block has the expected density `1-exp(-1)`. -/
theorem initialBlockOne_card_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ ((initialBlockOne x).card : ℝ) / x)
      atTop (𝓝 (1 - Real.exp (-1))) := by
  have hlim := fullInitialInterval_card_ratio_tendsto.sub
    initialRoughPart_card_ratio_tendsto_zero
  have hlim' : Tendsto
      (fun x : ℕ ↦ ((fullInitialInterval x).card : ℝ) / x -
        ((initialRoughPart x).card : ℝ) / x)
      atTop (𝓝 (1 - Real.exp (-1))) := by
    simpa [oneLowerRatio] using hlim
  apply hlim'.congr'
  filter_upwards with x
  have hsub := initialRoughPart_subset_full x
  rw [initialBlockOne_eq_sdiff x (proposition6MainCutoff_nonneg x),
    Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  ring

/-! ## Reciprocal mass of the initial block -/

lemma reciprocalMass_Ioc_eq_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    reciprocalMass (Ioc a b) =
      ((harmonic b : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
  have hsub : Icc 1 a ⊆ Icc 1 b := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hab⟩
  have hsdiff : Icc 1 b \ Icc 1 a = Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  change (∑ n ∈ Ioc a b, (n : ℝ)⁻¹) = _
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← hsdiff, ← Finset.sum_sdiff hsub]
  ring

lemma floorOneEndpoint_tendsto_atTop :
    Tendsto (fun x : ℕ ↦ ⌊oneLowerRatio * (x : ℝ)⌋₊) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop oneLowerRatio oneLowerRatio_pos

lemma fullInitialInterval_reciprocalMass_tendsto_one :
    Tendsto (fun x : ℕ ↦ reciprocalMass (fullInitialInterval x))
      atTop (𝓝 1) := by
  let a : ℕ → ℕ := fun x ↦ ⌊oneLowerRatio * (x : ℝ)⌋₊
  have haTop : Tendsto a atTop atTop := floorOneEndpoint_tendsto_atTop
  have herrorX := Real.tendsto_harmonic_sub_log
  have herrorA := Real.tendsto_harmonic_sub_log.comp haTop
  have herror : Tendsto
      (fun x : ℕ ↦
        (((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ)) -
        (((harmonic (a x) : ℚ) : ℝ) - Real.log (a x : ℝ)))
      atTop (𝓝 0) := by
    simpa [a] using herrorX.sub herrorA
  have hratio : Tendsto
      (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)) atTop (𝓝 oneLowerRatio) := by
    change Tendsto
      ((fun t : ℝ ↦ ((⌊oneLowerRatio * t⌋₊ : ℕ) : ℝ) / t) ∘
        (fun x : ℕ ↦ (x : ℝ))) atTop (𝓝 oneLowerRatio)
    exact (tendsto_nat_floor_mul_div_atTop oneLowerRatio_pos.le).comp
      tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log ((a x : ℝ) / (x : ℝ))) atTop (𝓝 (-1)) := by
    have hc := (Real.continuousAt_log oneLowerRatio_pos.ne').tendsto.comp hratio
    have hc' : Tendsto
        (Real.log ∘ (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)))
        atTop (𝓝 (Real.log oneLowerRatio)) := hc
    change Tendsto
      (Real.log ∘ (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ))) atTop (𝓝 (-1))
    convert hc' using 1
    simp [oneLowerRatio]
  have hlogdiff : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log (a x : ℝ)) atTop (𝓝 1) := by
    have hn := hlogratio.neg
    have hn' : Tendsto
        (fun x : ℕ ↦ -Real.log ((a x : ℝ) / (x : ℝ))) atTop (𝓝 1) := by
      simpa using hn
    apply hn'.congr'
    filter_upwards [eventually_ge_atTop 1,
      haTop.eventually (eventually_ge_atTop 1)] with x hx hax
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  have htotal := herror.add hlogdiff
  have htotal' : Tendsto
      (fun x : ℕ ↦ ((harmonic x : ℚ) : ℝ) -
        ((harmonic (a x) : ℚ) : ℝ)) atTop (𝓝 1) := by
    convert htotal using 1
    · funext x
      ring
    · norm_num
  apply htotal'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hale : a x ≤ x := by
    dsimp [a]
    have hreal : ((⌊oneLowerRatio * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg oneLowerRatio_pos.le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) oneLowerRatio_lt_one.le)
    exact_mod_cast hreal
  symm
  simpa only [a, fullInitialInterval] using
    reciprocalMass_Ioc_eq_harmonic_sub hale

lemma initialRoughPart_subset_proportionalRough (x : ℕ) :
    initialRoughPart x ⊆
      roughNumbersIn (proportionalLeftEndpoint oneLowerRatio x) x
        (logPowerCutoff 30 x) := by
  intro n hn
  rw [initialRoughPart, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  refine ⟨?_, hn.2.1, by simpa [mainCutoffNat] using hn.2.2⟩
  have hceil : proportionalLeftEndpoint oneLowerRatio x ≤
      ⌊oneLowerRatio * (x : ℝ)⌋₊ + 1 := by
    simpa [proportionalLeftEndpoint] using
      Nat.ceil_le_floor_add_one (oneLowerRatio * (x : ℝ))
  exact hceil.trans hn.1

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun n _ _ ↦
    inv_nonneg.mpr (Nat.cast_nonneg n)

lemma initialRoughPart_reciprocalMass_tendsto_zero :
    Tendsto (fun x : ℕ ↦ reciprocalMass (initialRoughPart x))
      atTop (𝓝 0) := by
  have hupper :=
    roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero
      30 oneLowerRatio_pos
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · exact Filter.Eventually.of_forall fun x ↦
      reciprocalMass_mono (initialRoughPart_subset_proportionalRough x)
  · exact hupper

lemma reciprocalMass_sdiff {A B : Finset ℕ} (hBA : B ⊆ A) :
    reciprocalMass (A \ B) = reciprocalMass A - reciprocalMass B := by
  unfold reciprocalMass
  rw [← Finset.sum_sdiff hBA]
  ring

/-- The restricted smooth block still has reciprocal mass tending to one. -/
theorem initialBlockOne_reciprocalMass_tendsto_one :
    Tendsto (fun x : ℕ ↦ reciprocalMass (initialBlockOne x))
      atTop (𝓝 1) := by
  have hlim := fullInitialInterval_reciprocalMass_tendsto_one.sub
    initialRoughPart_reciprocalMass_tendsto_zero
  have hlim' : Tendsto
      (fun x : ℕ ↦ reciprocalMass (fullInitialInterval x) -
        reciprocalMass (initialRoughPart x)) atTop (𝓝 1) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards with x
  rw [initialBlockOne_eq_sdiff x (proposition6MainCutoff_nonneg x),
    reciprocalMass_sdiff (initialRoughPart_subset_full x)]

lemma ratCast_recSum_eq_reciprocalMass (A : Finset ℕ) :
    ((UnitFractions.rec_sum A : ℚ) : ℝ) = reciprocalMass A := by
  simp [UnitFractions.rec_sum, reciprocalMass, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]

theorem initialBlockOne_recSum_tendsto_one :
    Tendsto (fun x : ℕ ↦ ((UnitFractions.rec_sum (initialBlockOne x) : ℚ) : ℝ))
      atTop (𝓝 1) := by
  simpa only [ratCast_recSum_eq_reciprocalMass] using
    initialBlockOne_reciprocalMass_tendsto_one

/-! ## A fixed nearby endpoint `alpha` -/

/-- The terminal interval with arbitrary fixed lower ratio. -/
def fullInitialIntervalAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  Ioc ⌊alpha * (x : ℝ)⌋₊ x

/-- The source-faithful smooth block with arbitrary fixed lower ratio. -/
def initialBlockAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  initialSmoothBlock alpha x (proposition6MainCutoff x)

def initialRoughPartAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  roughNumbersIn (⌊alpha * (x : ℝ)⌋₊ + 1) x (mainCutoffNat x)

lemma initialBlockAt_eq_sdiff (alpha : ℝ) (x : ℕ) :
    initialBlockAt alpha x =
      fullInitialIntervalAt alpha x \ initialRoughPartAt alpha x := by
  ext n
  simp only [initialBlockAt, initialSmoothBlock, fullInitialIntervalAt,
    initialRoughPartAt, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_sdiff, mem_roughNumbersIn]
  have hcut := proposition6MainCutoff_nonneg x
  by_cases hn : n = 0
  · subst n
    simp
  · rw [isSmooth_iff_largestPrimePowerPart_le_floor hcut hn]
    rw [mainCutoffNat_eq]
    omega

lemma initialRoughPartAt_subset_full (alpha : ℝ) (x : ℕ) :
    initialRoughPartAt alpha x ⊆ fullInitialIntervalAt alpha x := by
  intro n hn
  rw [initialRoughPartAt, mem_roughNumbersIn] at hn
  simp only [fullInitialIntervalAt, Finset.mem_Ioc]
  omega

lemma initialRoughPartAt_subset_global (alpha : ℝ) (x : ℕ) :
    initialRoughPartAt alpha x ⊆ roughNumbersIn 1 x (logPowerCutoff 30 x) := by
  intro n hn
  rw [initialRoughPartAt, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  exact ⟨by omega, hn.2.1, by simpa [mainCutoffNat] using hn.2.2⟩

lemma fullInitialIntervalAt_card_ratio_tendsto (alpha : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    Tendsto (fun x : ℕ ↦ ((fullInitialIntervalAt alpha x).card : ℝ) / x)
      atTop (𝓝 (1 - alpha)) := by
  have hfloor : Tendsto
      (fun x : ℕ ↦ ((⌊alpha * (x : ℝ)⌋₊ : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 alpha) :=
    (tendsto_nat_floor_mul_div_atTop halpha0).comp
      tendsto_natCast_atTop_atTop
  have hlim :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hfloor
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hfloorle : ⌊alpha * (x : ℝ)⌋₊ ≤ x := by
    have hreal : ((⌊alpha * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg halpha0 (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha1)
    exact_mod_cast hreal
  rw [show (fullInitialIntervalAt alpha x).card = x - ⌊alpha * (x : ℝ)⌋₊ by
    simp [fullInitialIntervalAt], Nat.cast_sub hfloorle]
  field_simp

lemma initialRoughPartAt_card_ratio_tendsto_zero (alpha : ℝ) :
    Tendsto (fun x : ℕ ↦ ((initialRoughPartAt alpha x).card : ℝ) / x)
      atTop (𝓝 0) := by
  have hglobal := (roughNumbersIn_logPowerCutoff_card_isLittleO 30).tendsto_div_nhds_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with x
    have hc : ((initialRoughPartAt alpha x).card : ℝ) ≤
        ((roughNumbersIn 1 x (logPowerCutoff 30 x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (initialRoughPartAt_subset_global alpha x)
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg x)
  · exact hglobal

/-- Fixed-alpha density form of the first half of Proposition 6. -/
theorem initialBlockAt_card_ratio_tendsto (alpha : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    Tendsto (fun x : ℕ ↦ ((initialBlockAt alpha x).card : ℝ) / x)
      atTop (𝓝 (1 - alpha)) := by
  have hlim := (fullInitialIntervalAt_card_ratio_tendsto alpha halpha0 halpha1).sub
    (initialRoughPartAt_card_ratio_tendsto_zero alpha)
  have hlim' : Tendsto
      (fun x : ℕ ↦ ((fullInitialIntervalAt alpha x).card : ℝ) / x -
        ((initialRoughPartAt alpha x).card : ℝ) / x)
      atTop (𝓝 (1 - alpha)) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards with x
  have hsub := initialRoughPartAt_subset_full alpha x
  rw [initialBlockAt_eq_sdiff alpha x, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub)]
  ring

lemma floorEndpoint_tendsto_atTop {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun x : ℕ ↦ ⌊alpha * (x : ℝ)⌋₊) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop alpha halpha

lemma fullInitialIntervalAt_reciprocalMass_tendsto (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Tendsto (fun x : ℕ ↦ reciprocalMass (fullInitialIntervalAt alpha x))
      atTop (𝓝 (-Real.log alpha)) := by
  let a : ℕ → ℕ := fun x ↦ ⌊alpha * (x : ℝ)⌋₊
  have haTop : Tendsto a atTop atTop := floorEndpoint_tendsto_atTop halpha0
  have herrorX := Real.tendsto_harmonic_sub_log
  have herrorA := Real.tendsto_harmonic_sub_log.comp haTop
  have herror : Tendsto
      (fun x : ℕ ↦
        (((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ)) -
        (((harmonic (a x) : ℚ) : ℝ) - Real.log (a x : ℝ)))
      atTop (𝓝 0) := by
    simpa [a] using herrorX.sub herrorA
  have hratio : Tendsto
      (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)) atTop (𝓝 alpha) := by
    change Tendsto
      ((fun t : ℝ ↦ ((⌊alpha * t⌋₊ : ℕ) : ℝ) / t) ∘
        (fun x : ℕ ↦ (x : ℝ))) atTop (𝓝 alpha)
    exact (tendsto_nat_floor_mul_div_atTop halpha0.le).comp
      tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto
      (Real.log ∘ (fun x : ℕ ↦ (a x : ℝ) / (x : ℝ)))
      atTop (𝓝 (Real.log alpha)) :=
    (Real.continuousAt_log halpha0.ne').tendsto.comp hratio
  have hlogdiff : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log (a x : ℝ))
      atTop (𝓝 (-Real.log alpha)) := by
    have hn := hlogratio.neg
    apply hn.congr'
    filter_upwards [eventually_ge_atTop 1,
      haTop.eventually (eventually_ge_atTop 1)] with x hx hax
    change -Real.log ((a x : ℝ) / (x : ℝ)) = _
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  have htotal := herror.add hlogdiff
  have htotal' : Tendsto
      (fun x : ℕ ↦ ((harmonic x : ℚ) : ℝ) -
        ((harmonic (a x) : ℚ) : ℝ)) atTop (𝓝 (-Real.log alpha)) := by
    convert htotal using 1
    · funext x
      ring
    · simp
  apply htotal'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hale : a x ≤ x := by
    dsimp [a]
    have hreal : ((⌊alpha * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg halpha0.le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha1)
    exact_mod_cast hreal
  symm
  simpa only [a, fullInitialIntervalAt] using
    reciprocalMass_Ioc_eq_harmonic_sub hale

lemma initialRoughPartAt_subset_proportionalRough
    (alpha : ℝ) (x : ℕ) :
    initialRoughPartAt alpha x ⊆
      roughNumbersIn (proportionalLeftEndpoint alpha x) x
        (logPowerCutoff 30 x) := by
  intro n hn
  rw [initialRoughPartAt, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  refine ⟨?_, hn.2.1, by simpa [mainCutoffNat] using hn.2.2⟩
  have hceil : proportionalLeftEndpoint alpha x ≤
      ⌊alpha * (x : ℝ)⌋₊ + 1 := by
    simpa [proportionalLeftEndpoint] using
      Nat.ceil_le_floor_add_one (alpha * (x : ℝ))
  exact hceil.trans hn.1

lemma initialRoughPartAt_reciprocalMass_tendsto_zero
    (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun x : ℕ ↦ reciprocalMass (initialRoughPartAt alpha x))
      atTop (𝓝 0) := by
  have hupper :=
    roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero 30 halpha
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · exact Filter.Eventually.of_forall fun x ↦
      reciprocalMass_mono (initialRoughPartAt_subset_proportionalRough alpha x)
  · exact hupper

/-- Fixed-alpha reciprocal-sum form of the first half of Proposition 6. -/
theorem initialBlockAt_reciprocalMass_tendsto (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Tendsto (fun x : ℕ ↦ reciprocalMass (initialBlockAt alpha x))
      atTop (𝓝 (-Real.log alpha)) := by
  have hlim := (fullInitialIntervalAt_reciprocalMass_tendsto alpha halpha0 halpha1).sub
    (initialRoughPartAt_reciprocalMass_tendsto_zero alpha halpha0)
  have hlim' : Tendsto
      (fun x : ℕ ↦ reciprocalMass (fullInitialIntervalAt alpha x) -
        reciprocalMass (initialRoughPartAt alpha x))
      atTop (𝓝 (-Real.log alpha)) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards with x
  rw [initialBlockAt_eq_sdiff alpha x,
    reciprocalMass_sdiff (initialRoughPartAt_subset_full alpha x)]

theorem initialBlockAt_recSum_tendsto (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Tendsto
      (fun x : ℕ ↦ ((UnitFractions.rec_sum (initialBlockAt alpha x) : ℚ) : ℝ))
      atTop (𝓝 (-Real.log alpha)) := by
  simpa only [ratCast_recSum_eq_reciprocalMass] using
    initialBlockAt_reciprocalMass_tendsto alpha halpha0 halpha1

/-- The real residual after the fixed-alpha initial block. -/
def initialRealResidualAt (alpha : ℝ) (x : ℕ) : ℝ :=
  1 - ((UnitFractions.rec_sum (initialBlockAt alpha x) : ℚ) : ℝ)

theorem initialRealResidualAt_tendsto (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Tendsto (initialRealResidualAt alpha) atTop (𝓝 (1 + Real.log alpha)) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      (initialBlockAt_recSum_tendsto alpha halpha0 halpha1)
  change Tendsto
    (fun x : ℕ ↦ 1 -
      ((UnitFractions.rec_sum (initialBlockAt alpha x) : ℚ) : ℝ))
    atTop (𝓝 (1 + Real.log alpha))
  simpa only [sub_neg_eq_add] using h

/-! ## The accumulated Lemma 12 deletion budget -/

lemma sum_Icc_rpow_neg_two_thirds_le (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by
  let f : ℝ → ℝ := fun t ↦ t ^ (-(2 : ℝ) / 3)
  have hanti : AntitoneOn f (Set.Icc 1 (1 + ((Q - 1 : ℕ) : ℝ))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num :
      (-(2 : ℝ) / 3) ≤ 0)).mono
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
        · intro q hq
          rfl
      _ =
          ∑ i ∈ Ico 0 (Q - 1), f (i + 2 : ℕ) := by
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
  have hone : f 1 = 1 := by simp [f]
  have hdecomp : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext q
    simp
    omega
  rw [hdecomp, Finset.sum_insert (by simp)]
  have honeRaw : ((1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by norm_num
  rw [honeRaw]
  calc
    1 + ∑ q ∈ Icc 2 Q, f q
        ≤ 1 + ∫ t in (1 : ℝ)..Q, f t := by
          simpa [add_comm] using add_le_add_left htail 1
    _ = 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) - 2 := by rw [hint]; ring
    _ ≤ 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by linarith

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

/-- Prime powers that can occur as elimination stages after initialization. -/
def eliminationPrimePowers (x : ℕ) : Finset ℕ :=
  (Icc 1 (mainCutoffNat x)).filter IsPrimePow

/-- The real-valued sum of Martin's Lemma 12 cardinality bounds. -/
def lemma12DeletionCost (x : ℕ) : ℝ :=
  ∑ q ∈ eliminationPrimePowers x,
    200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3

lemma div_rpow_two_thirds {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    (x / q) ^ ((2 : ℝ) / 3) =
      x ^ ((2 : ℝ) / 3) * q ^ (-(2 : ℝ) / 3) := by
  rw [Real.div_rpow hx hq.le]
  have he : (-(2 : ℝ) / 3) = -((2 : ℝ) / 3) := by ring
  rw [he, Real.rpow_neg hq.le]
  ring

lemma lemma12DeletionCost_eq (x : ℕ) :
    lemma12DeletionCost x =
      200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
        (∑ q ∈ eliminationPrimePowers x, (q : ℝ) ^ (-(2 : ℝ) / 3)) := by
  unfold lemma12DeletionCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqpos : (0 : ℝ) < q := by
    have hq1 : 1 ≤ q := by
      simp only [eliminationPrimePowers, Finset.mem_filter, Finset.mem_Icc] at hq
      exact hq.1.1
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  rw [div_rpow_two_thirds (Nat.cast_nonneg x) hqpos]
  ring

lemma elimination_rpow_sum_le (x : ℕ) (hQ : 1 ≤ mainCutoffNat x) :
    (∑ q ∈ eliminationPrimePowers x, (q : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3) := by
  calc
    (∑ q ∈ eliminationPrimePowers x, (q : ℝ) ^ (-(2 : ℝ) / 3)) ≤
        ∑ q ∈ Icc 1 (mainCutoffNat x), (q : ℝ) ^ (-(2 : ℝ) / 3) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro q hq _
      exact Real.rpow_nonneg (Nat.cast_nonneg q) _
    _ ≤ 3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3) :=
      sum_Icc_rpow_neg_two_thirds_le _ hQ

/-- The total Lemma 12 loss is eventually at most `600*x/log(x)^7`. -/
theorem eventually_lemma12DeletionCost_le :
    ∀ᶠ x : ℕ in atTop,
      lemma12DeletionCost x ≤ 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
  have hQtop : Tendsto mainCutoffNat atTop atTop := mainCutoffNat_spec.2.1
  filter_upwards [eventually_ge_atTop 3,
    hQtop.eventually (eventually_ge_atTop 1)] with x hx hQ
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hcutnonneg := proposition6MainCutoff_nonneg x
  have hQcut : (mainCutoffNat x : ℝ) ≤ proposition6MainCutoff x := by
    rw [mainCutoffNat_eq]
    exact Nat.floor_le hcutnonneg
  have hQrpow : (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3) ≤
      proposition6MainCutoff x ^ ((1 : ℝ) / 3) := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hQcut (by norm_num)
  rw [lemma12DeletionCost_eq]
  calc
    200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
          (∑ q ∈ eliminationPrimePowers x, (q : ℝ) ^ (-(2 : ℝ) / 3))
        ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
          (3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3)) := by
            gcongr
            exact elimination_rpow_sum_le x hQ
    _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
          (3 * proposition6MainCutoff x ^ ((1 : ℝ) / 3)) := by
            gcongr
    _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
      rw [show proposition6MainCutoff x =
        (x : ℝ) / Real.log (x : ℝ) ^ 30 by rfl]
      calc
        200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
              (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3)) =
            600 * ((x : ℝ) ^ ((2 : ℝ) / 3) *
              ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3) := by ring
        _ = 600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
          rw [deletion_rpow_identity hxpos hlog]
        _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring

/-- An integer allowance for one Lemma 12 block. -/
def lemma12StageAllowance (x q : ℕ) : ℕ :=
  ⌈200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3⌉₊

/-- Sum of the integer allowances over all possible eliminated prime powers. -/
def totalEliminationAllowance (x : ℕ) : ℕ :=
  ∑ q ∈ eliminationPrimePowers x, lemma12StageAllowance x q

/-- A convenient explicit `x/log(x)^7` budget. -/
def proposition6DeletionBudget (x : ℕ) : ℕ :=
  ⌈1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7⌉₊

lemma eliminationPrimePowers_card_le (x : ℕ) :
    (eliminationPrimePowers x).card ≤ mainCutoffNat x := by
  calc
    (eliminationPrimePowers x).card ≤ (Icc 1 (mainCutoffNat x)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ mainCutoffNat x := by simp

lemma totalEliminationAllowance_cast_le_cost_add_card (x : ℕ) :
    (totalEliminationAllowance x : ℝ) ≤
      lemma12DeletionCost x + (eliminationPrimePowers x).card := by
  rw [totalEliminationAllowance]
  push_cast
  calc
    ∑ q ∈ eliminationPrimePowers x, (lemma12StageAllowance x q : ℝ) ≤
        ∑ q ∈ eliminationPrimePowers x,
          (200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hnonneg : 0 ≤ 200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
          Real.log (x : ℝ) ^ 3 := by positivity
      exact (Nat.ceil_lt_add_one hnonneg).le
    _ = lemma12DeletionCost x + (eliminationPrimePowers x).card := by
      simp only [lemma12DeletionCost, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one]

/-- The sum of all integer block allowances fits the explicit budget. -/
theorem eventually_totalEliminationAllowance_le_budget :
    ∀ᶠ x : ℕ in atTop,
      totalEliminationAllowance x ≤ proposition6DeletionBudget x := by
  have hQtop : Tendsto mainCutoffNat atTop atTop := mainCutoffNat_spec.2.1
  have hlogtop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  filter_upwards [eventually_lemma12DeletionCost_le,
    eventually_ge_atTop 3, hQtop.eventually (eventually_ge_atTop 1),
    hlogtop.eventually (eventually_ge_atTop 1)] with x hcost hx hQ hlog1
  have hxnonneg : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog1
  have hratioNonneg : 0 ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
  have hQcut : (mainCutoffNat x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 30 := by
    rw [← show proposition6MainCutoff x =
      (x : ℝ) / Real.log (x : ℝ) ^ 30 by rfl, mainCutoffNat_eq]
    exact Nat.floor_le (proposition6MainCutoff_nonneg x)
  have hpow : Real.log (x : ℝ) ^ 7 ≤ Real.log (x : ℝ) ^ 30 := by
    exact pow_le_pow_right₀ hlog1 (by omega)
  have hQsmall : (mainCutoffNat x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    exact hQcut.trans
      (div_le_div_of_nonneg_left hxnonneg (pow_pos hlogpos 7) hpow)
  have hallow : (totalEliminationAllowance x : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      (totalEliminationAllowance x : ℝ) ≤
          lemma12DeletionCost x + (eliminationPrimePowers x).card :=
        totalEliminationAllowance_cast_le_cost_add_card x
      _ ≤ 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 +
          (mainCutoffNat x : ℝ) := by
            gcongr
            exact_mod_cast eliminationPrimePowers_card_le x
      _ ≤ 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 +
          (x : ℝ) / Real.log (x : ℝ) ^ 7 := by gcongr
      _ = 601 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by ring
      _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
        have hr : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        nlinarith
      _ = 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (proposition6DeletionBudget x : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hallow.trans hceil

/-! ## Capacity of the five-prime reservoir for the deletion budget -/

lemma proposition6ReservoirScale_tendsto_atTop (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun x : ℕ ↦ proposition6ReservoirScale alpha x) atTop atTop := by
  have hbase : Tendsto (fun x : ℕ ↦ alpha * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop halpha
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ)⁻¹)).comp hbase

lemma reservoirScale_log_le_log (alpha : ℝ) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1) {x : ℕ} (hx : 1 < x) :
    Real.log (proposition6ReservoirScale alpha x) ≤ Real.log (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have haxpos : 0 < alpha * (x : ℝ) := mul_pos halpha0 hxpos
  rw [proposition6ReservoirScale, Real.log_rpow haxpos,
    Real.log_mul halpha0.ne' hxpos.ne']
  have hloga : Real.log alpha ≤ 0 := Real.log_nonpos halpha0.le halpha1
  have hlogx : 0 ≤ Real.log (x : ℝ) := (Real.log_pos (by exact_mod_cast hx)).le
  norm_num
  linarith

/-- The elementary five-prime reservoir is more than large enough for twice
the complete Lemma 12 deletion budget. -/
theorem eventually_two_budget_le_smoothReservoir (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∀ᶠ x : ℕ in atTop,
      2 * proposition6DeletionBudget x ≤
        (smoothReservoir (proposition6ReservoirScale alpha x)).card := by
  let C : ℝ := 120 * 200 ^ 5
  have hC : 0 < C := by dsimp [C]; positivity
  have hyTop := proposition6ReservoirScale_tendsto_atTop alpha halpha0
  have hreservoir := hyTop.eventually eventually_smoothReservoir_card_lower
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  have hscaled : Tendsto
      (fun x : ℕ ↦ alpha * (x : ℝ) / Real.log (x : ℝ) ^ 5)
      atTop atTop := by
    have ht :=
      (UnitFractions.tendsto_mul_add_div_pow_log_at_top alpha 0 5 halpha0).comp
        tendsto_natCast_atTop_atTop
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x ↦ by simp
  filter_upwards [hreservoir, eventually_ge_atTop 3,
    hlogTop.eventually (eventually_ge_atTop (max 1 (4000 * C / alpha))),
    hscaled.eventually (eventually_ge_atTop (4 * C)),
    hyTop.eventually (eventually_gt_atTop 1)]
      with x hreservoir hx hlogLarge hscaledLarge hy1
  let y := proposition6ReservoirScale alpha x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hypos : 0 < y := by
    exact Real.rpow_pos_of_pos (mul_pos halpha0 hxpos) _
  have hlogy : 0 < Real.log y := by
    exact Real.log_pos hy1
  have hlogyx : Real.log y ≤ Real.log (x : ℝ) :=
    reservoirScale_log_le_log alpha halpha0 halpha1 (by omega)
  have hy5 : y ^ 5 = alpha * (x : ℝ) :=
    proposition6ReservoirScale_pow_five halpha0.le
  have hreservoirEq : (y / (200 * Real.log y)) ^ 5 / 120 =
      alpha * (x : ℝ) / (C * Real.log y ^ 5) := by
    dsimp [C]
    rw [div_pow, hy5]
    ring
  have hdenlog : C * Real.log y ^ 5 ≤ C * Real.log (x : ℝ) ^ 5 := by
    gcongr
  have hlower : alpha * (x : ℝ) /
      (C * Real.log (x : ℝ) ^ 5) ≤
      ((smoothReservoir y).card : ℝ) := by
    calc
      alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) ≤
          alpha * (x : ℝ) / (C * Real.log y ^ 5) := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg halpha0.le hxpos.le)
              (mul_pos hC (pow_pos hlogy _)) hdenlog
      _ = (y / (200 * Real.log y)) ^ 5 / 120 := hreservoirEq.symm
      _ ≤ ((smoothReservoir y).card : ℝ) := hreservoir
  have hlogsq : 4000 * C ≤ alpha * Real.log (x : ℝ) ^ 2 := by
    have h1 : 1 ≤ Real.log (x : ℝ) := (le_max_left _ _).trans hlogLarge
    have hthreshold : 4000 * C / alpha ≤ Real.log (x : ℝ) :=
      (le_max_right _ _).trans hlogLarge
    have := mul_le_mul_of_nonneg_left hthreshold halpha0.le
    field_simp at this
    nlinarith
  have hmain : 2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) ≤
      alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) := by
    have hcore : 2000 * (2 * C * Real.log (x : ℝ) ^ 5) ≤
        alpha * Real.log (x : ℝ) ^ 7 := by
      calc
        2000 * (2 * C * Real.log (x : ℝ) ^ 5) =
            (4000 * C) * Real.log (x : ℝ) ^ 5 := by ring
        _ ≤ (alpha * Real.log (x : ℝ) ^ 2) *
            Real.log (x : ℝ) ^ 5 := by gcongr
        _ = alpha * Real.log (x : ℝ) ^ 7 := by ring
    rw [show 2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) =
      2000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 by ring]
    apply (div_le_div_iff₀ (pow_pos hlogx 7)
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC) (pow_pos hlogx 5))).2
    have := mul_le_mul_of_nonneg_left hcore hxpos.le
    ring_nf at this ⊢
    exact this
  have htwo : (2 : ℝ) ≤
      alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) := by
    have hcross : 4 * C * Real.log (x : ℝ) ^ 5 ≤ alpha * (x : ℝ) := by
      exact (le_div_iff₀ (pow_pos hlogx 5)).1 hscaledLarge
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hC) (pow_pos hlogx 5))).2
    nlinarith
  have hbudgetCast : (proposition6DeletionBudget x : ℝ) <
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have htarget : (2 * proposition6DeletionBudget x : ℕ) ≤
      (smoothReservoir y).card := by
    have hcast : ((2 * proposition6DeletionBudget x : ℕ) : ℝ) ≤
        ((smoothReservoir y).card : ℝ) := by
      calc
      ((2 * proposition6DeletionBudget x : ℕ) : ℝ) ≤
          2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) := by
            push_cast
            exact (mul_lt_mul_of_pos_left hbudgetCast (by norm_num)).le
      _ ≤ alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) := by
        calc
          2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) =
              2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) + 2 := by ring
          _ ≤ alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) +
              alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) :=
                add_le_add hmain htwo
          _ = alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) := by ring
      _ ≤ ((smoothReservoir y).card : ℝ) := hlower
    exact_mod_cast hcast
  exact htarget

/-! ## Residual margins -/

def proposition6BudgetRatio (alpha : ℝ) (x : ℕ) : ℝ :=
  (proposition6DeletionBudget x : ℝ) / (alpha * (x : ℝ))

lemma proposition6BudgetRatio_tendsto_zero (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (proposition6BudgetRatio alpha) atTop (𝓝 0) := by
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
    have hceil : (proposition6DeletionBudget x : ℝ) ≤
        1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    dsimp [proposition6BudgetRatio]
    calc
      (proposition6DeletionBudget x : ℝ) / (alpha * (x : ℝ)) ≤
          (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) /
            (alpha * (x : ℝ)) := by
              exact div_le_div_of_nonneg_right hceil (mul_nonneg halpha.le hxpos.le)
      _ = (1000 / alpha) * (Real.log (x : ℝ) ^ 7)⁻¹ +
          alpha⁻¹ * ((x : ℝ))⁻¹ := by field_simp
  · exact hupper

lemma initialResidualLimit_pos {alpha : ℝ}
    (halpha : Real.exp (-1) < alpha) : 0 < 1 + Real.log alpha := by
  have halpha0 : 0 < alpha := (Real.exp_pos _).trans halpha
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) halpha0 halpha
  rw [Real.log_exp] at hlog
  linarith

lemma initialResidualLimit_lt_one {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    1 + Real.log alpha < 1 := by
  linarith [Real.log_neg halpha0 halpha1]

/-- A fixed `alpha` strictly between `exp(-1)` and `1` gives all analytic
residual inequalities required by the Proposition 6 recursion. -/
theorem eventually_initial_residual_margins (alpha : ℝ)
    (halphaLower : Real.exp (-1) < alpha) (halphaUpper : alpha < 1) :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ))⁻¹ + 4 * proposition6BudgetRatio alpha x <
          initialRealResidualAt alpha x ∧
        initialRealResidualAt alpha x + proposition6BudgetRatio alpha x < 1 := by
  have halpha0 : 0 < alpha := (Real.exp_pos _).trans halphaLower
  have hres := initialRealResidualAt_tendsto alpha halpha0 halphaUpper.le
  have hratio := proposition6BudgetRatio_tendsto_zero alpha halpha0
  have hloginv : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hlower := hloginv.add (hratio.const_mul 4)
  have hdiff := hres.sub hlower
  have hupper := hres.add hratio
  have hdiff' : Tendsto
      (fun x : ℕ ↦ initialRealResidualAt alpha x -
        ((Real.log (x : ℝ))⁻¹ + 4 * proposition6BudgetRatio alpha x))
      atTop (𝓝 (1 + Real.log alpha)) := by simpa using hdiff
  have hupper' : Tendsto
      (fun x : ℕ ↦ initialRealResidualAt alpha x +
        proposition6BudgetRatio alpha x)
      atTop (𝓝 (1 + Real.log alpha)) := by simpa using hupper
  have hpos := initialResidualLimit_pos halphaLower
  have hlt := initialResidualLimit_lt_one halpha0 halphaUpper
  have heventLower : ∀ᶠ x : ℕ in atTop,
      0 < initialRealResidualAt alpha x -
        ((Real.log (x : ℝ))⁻¹ + 4 * proposition6BudgetRatio alpha x) := by
    exact hdiff'.eventually (Ioi_mem_nhds hpos)
  have heventUpper : ∀ᶠ x : ℕ in atTop,
      initialRealResidualAt alpha x + proposition6BudgetRatio alpha x < 1 := by
    exact hupper'.eventually (Iio_mem_nhds hlt)
  filter_upwards [heventLower, heventUpper] with x hlo hup
  constructor <;> linarith

/-- Choose a fixed lower endpoint arbitrarily close to `exp(-1)`, but on the
side that leaves a strictly positive residual. -/
lemma exists_alpha_near_exp_neg_one {eps : ℝ} (heps : 0 < eps) :
    ∃ alpha : ℝ,
      Real.exp (-1) < alpha ∧ alpha < 1 ∧
        |(1 - alpha) - (1 - Real.exp (-1))| < eps := by
  let d : ℝ := min (eps / 2) ((1 - Real.exp (-1)) / 2)
  have hexp : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hdpos : 0 < d := by
    exact lt_min (by linarith) (by linarith)
  have hdeps : d < eps := (min_le_left _ _).trans_lt (by linarith)
  have hdgap : d ≤ (1 - Real.exp (-1)) / 2 := min_le_right _ _
  refine ⟨Real.exp (-1) + d, by linarith, by linarith, ?_⟩
  rw [show (1 - (Real.exp (-1) + d)) - (1 - Real.exp (-1)) = -d by ring,
    abs_neg, abs_of_pos hdpos]
  exact hdeps

/-- All analytic/counting facts consumed by the concrete Proposition 6
assembly, bundled at one sufficiently large scale. -/
theorem eventually_proposition6AsymptoticBundle (alpha : ℝ)
    (halphaLower : Real.exp (-1) < alpha) (halphaUpper : alpha < 1) :
    ∀ᶠ x : ℕ in atTop,
      totalEliminationAllowance x ≤ proposition6DeletionBudget x ∧
      2 * proposition6DeletionBudget x ≤
        (smoothReservoir (proposition6ReservoirScale alpha x)).card ∧
      (Real.log (x : ℝ))⁻¹ + 4 * proposition6BudgetRatio alpha x <
        initialRealResidualAt alpha x ∧
      initialRealResidualAt alpha x + proposition6BudgetRatio alpha x < 1 ∧
      mainCutoffNat x ≤ x ∧ 1 ≤ mainCutoffNat x := by
  have halpha0 : 0 < alpha := (Real.exp_pos _).trans halphaLower
  have hQtop := mainCutoffNat_spec.2.1
  filter_upwards [eventually_totalEliminationAllowance_le_budget,
    eventually_two_budget_le_smoothReservoir alpha halpha0 halphaUpper.le,
    eventually_initial_residual_margins alpha halphaLower halphaUpper,
    mainCutoffNat_spec.1, hQtop.eventually (eventually_ge_atTop 1)]
      with x hallow hcapacity hmargins hQle hQone
  exact ⟨hallow, hcapacity, hmargins.1, hmargins.2, hQle, hQone⟩

end

end Erdos285

#print axioms Erdos285.isSmooth_iff_largestPrimePowerPart_le_floor
#print axioms Erdos285.initialBlockAt_card_ratio_tendsto
#print axioms Erdos285.eventually_totalEliminationAllowance_le_budget
#print axioms Erdos285.eventually_two_budget_le_smoothReservoir
#print axioms Erdos285.eventually_proposition6AsymptoticBundle
