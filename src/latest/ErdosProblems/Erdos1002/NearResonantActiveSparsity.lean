import ErdosProblems.Erdos1002.NearResonantLeakageParameters
import ErdosProblems.Erdos1002.ResonantConvergents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointwise sparsity of active near-resonant denominators

The manuscript obtains a bounded number of active denominators in each
dyadic block from continued fractions.  Here we give a shorter equivalent
proof by packing reduced rational cells.  In `(P/2,P]`, every active reduced
fraction lies within `2/P²` of `alpha`, while two distinct reduced fractions
with denominators at most `P` are separated by at least `1/P²`.  Scaling by
`P²` and taking floors injects the active denominators into the four integers
`{-2,-1,0,1}`.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

/-- Denominators in `(P/2,P]` whose actual smooth reduced-cell sum is
nonzero at `alpha`. -/
def nearActiveDenominators
    (a ε : ℝ) (P : ℕ) (alpha : ℝ) : Finset ℕ :=
  (Finset.Ioc (P / 2) P).filter fun p ↦
    smoothNearPrimitivePoleSum a ε p alpha ≠ 0

/-- On the open fundamental interval, an active smooth cell has the literal
nearest primitive numerator. -/
theorem isPrimitiveResonance_of_smoothNearPrimitivePoleSum_ne_zero
    (a ε alpha : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (hne : smoothNearPrimitivePoleSum a ε p alpha ≠ 0) :
    IsPrimitiveResonance p alpha := by
  have heq := nearPrimitivePole_eq_smoothNearPrimitivePoleSum
    a ε p hp ha hε haε hεhalf halpha
  have hnear : nearPrimitivePole a ε p alpha ≠ 0 := by
    simpa only [heq] using! hne
  unfold nearPrimitivePole at hnear
  by_cases hprim : IsPrimitiveResonance p alpha
  · exact hprim
  · simp [hprim] at hnear

/-- Activity forces the scaled nearest-cell coordinate into the outer
cutoff support. -/
theorem abs_mul_resonanceDelta_le_of_smoothNearPrimitivePoleSum_ne_zero
    (a ε alpha : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (hne : smoothNearPrimitivePoleSum a ε p alpha ≠ 0) :
    |(p : ℝ) * resonanceDelta p alpha| ≤ ε := by
  have heq := nearPrimitivePole_eq_smoothNearPrimitivePoleSum
    a ε p hp ha hε haε hεhalf halpha
  have hnear : nearPrimitivePole a ε p alpha ≠ 0 := by
    simpa only [heq] using! hne
  have hprim :=
    isPrimitiveResonance_of_smoothNearPrimitivePoleSum_ne_zero
      a ε alpha p hp ha hε haε hεhalf halpha hne
  unfold nearPrimitivePole at hnear
  rw [if_pos hprim] at hnear
  exact (support_nearW_subset_Icc a ε ha hε haε hnear |> fun h ↦
    (abs_le.mpr ⟨by linarith [h.1], h.2⟩))

/-- Distinct reduced fractions have their elementary Farey separation.
This proof uses the canonical rational denominator only to show that the
cross determinant is nonzero. -/
theorem one_div_mul_le_abs_intDivNat_sub_intDivNat
    (m n : ℤ) (p r : ℕ) (hp : 0 < p) (hr : 0 < r)
    (hm : Nat.Coprime m.natAbs p) (hn : Nat.Coprime n.natAbs r)
    (hpr : p ≠ r) :
    1 / ((p : ℝ) * (r : ℝ)) ≤
      |(m : ℝ) / (p : ℝ) - (n : ℝ) / (r : ℝ)| := by
  have hratne : (m : ℚ) / (p : ℚ) ≠ (n : ℚ) / (r : ℚ) := by
    intro heq
    have hden := congrArg Rat.den heq
    rw [den_intDivNat_of_coprime m p hp hm,
      den_intDivNat_of_coprime n r hr hn] at hden
    exact hpr hden
  have hdet : m * (r : ℤ) - n * (p : ℤ) ≠ 0 := by
    intro hzero
    apply hratne
    field_simp
    have hz := sub_eq_zero.mp hzero
    exact_mod_cast (hz.trans (mul_comm n (p : ℤ)))
  have honeInt : (1 : ℤ) ≤ |m * (r : ℤ) - n * (p : ℤ)| :=
    Int.one_le_abs hdet
  have hone : (1 : ℝ) ≤
      |((m * (r : ℤ) - n * (p : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast honeInt
  have hdenpos : 0 < (p : ℝ) * (r : ℝ) := by positivity
  have heq : |(m : ℝ) / (p : ℝ) - (n : ℝ) / (r : ℝ)| =
      |((m * (r : ℤ) - n * (p : ℤ) : ℤ) : ℝ)| /
        ((p : ℝ) * (r : ℝ)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity),
      abs_div, abs_of_pos hdenpos]
    congr 1
    push_cast
    ring_nf
  rw [heq]
  exact div_le_div_of_nonneg_right hone hdenpos.le

/-- The integer grid coordinate used for the packing injection. -/
def nearActiveGridIndex (P p : ℕ) (alpha : ℝ) : ℤ :=
  ⌊(P : ℝ) ^ 2 *
    ((resonanceNumerator p alpha : ℝ) / (p : ℝ) - alpha)⌋

/-- Every active grid coordinate lies among `-2,-1,0,1`. -/
theorem nearActiveGridIndex_mem_Icc
    (a ε alpha : ℝ) (P p : ℕ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (hpMem : p ∈ nearActiveDenominators a ε P alpha) :
    nearActiveGridIndex P p alpha ∈ Finset.Icc (-2 : ℤ) 1 := by
  have hpFilter := Finset.mem_filter.mp hpMem
  have hpBounds := Finset.mem_Ioc.mp hpFilter.1
  have hpTwo : 2 ≤ p := by
    have hhalf : 2 ≤ P / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
    omega
  have hpR : 0 < (p : ℝ) := by positivity
  have hpLower : P < 2 * p := by
    have hdecomp := Nat.mod_add_div P 2
    have hmod := Nat.mod_lt P (by omega : 0 < 2)
    omega
  have hsupport :=
    abs_mul_resonanceDelta_le_of_smoothNearPrimitivePoleSum_ne_zero
      a ε alpha p hpTwo ha hε haε hεhalf.le halpha hpFilter.2
  rw [abs_mul, abs_of_pos hpR] at hsupport
  have hcenter :
      (resonanceNumerator p alpha : ℝ) / (p : ℝ) - alpha =
        -resonanceDelta p alpha / (p : ℝ) := by
    unfold resonanceDelta
    field_simp
    ring
  let x : ℝ := (P : ℝ) ^ 2 *
    ((resonanceNumerator p alpha : ℝ) / (p : ℝ) - alpha)
  have hxabs : |x| =
      ((P : ℝ) / (p : ℝ)) ^ 2 *
        ((p : ℝ) * |resonanceDelta p alpha|) := by
    dsimp [x]
    rw [hcenter, abs_mul, abs_div, abs_neg, abs_of_pos hpR,
      abs_of_nonneg (sq_nonneg (P : ℝ))]
    field_simp
  have hratio : (P : ℝ) / (p : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hpR]
    exact_mod_cast hpLower.le
  have hratio0 : 0 ≤ (P : ℝ) / (p : ℝ) := by positivity
  have hxlt : |x| < 2 := by
    calc
      |x| = ((P : ℝ) / (p : ℝ)) ^ 2 *
          ((p : ℝ) * |resonanceDelta p alpha|) := hxabs
      _ ≤ (2 : ℝ) ^ 2 * ε := by
        gcongr
      _ < 2 := by nlinarith
  have hxBounds := abs_lt.mp hxlt
  have hlower : (-2 : ℤ) ≤ ⌊x⌋ := by
    rw [Int.le_floor]
    simpa using! hxBounds.1.le
  have hupperStrict : ⌊x⌋ < (2 : ℤ) := by
    rw [Int.floor_lt]
    exact hxBounds.2
  have hupper : ⌊x⌋ ≤ (1 : ℤ) := by omega
  change ⌊x⌋ ∈ Finset.Icc (-2 : ℤ) 1
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

/-- Distinct active reduced fractions in one dyadic denominator block have
distinct unit grid coordinates after scaling by `P²`. -/
theorem nearActiveGridIndex_injOn
    (a ε alpha : ℝ) (P : ℕ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    Set.InjOn (fun p ↦ nearActiveGridIndex P p alpha)
      (nearActiveDenominators a ε P alpha : Set ℕ) := by
  intro p hpMem r hrMem hgrid
  by_contra hpr
  change p ∈ nearActiveDenominators a ε P alpha at hpMem
  change r ∈ nearActiveDenominators a ε P alpha at hrMem
  have hpFilter := Finset.mem_filter.mp hpMem
  have hrFilter := Finset.mem_filter.mp hrMem
  have hpBounds := Finset.mem_Ioc.mp hpFilter.1
  have hrBounds := Finset.mem_Ioc.mp hrFilter.1
  have hpTwo : 2 ≤ p := by
    have hhalf : 2 ≤ P / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
    omega
  have hrTwo : 2 ≤ r := by
    have hhalf : 2 ≤ P / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
    omega
  have hpPrim :=
    isPrimitiveResonance_of_smoothNearPrimitivePoleSum_ne_zero
      a ε alpha p hpTwo ha hε haε hεhalf.le halpha hpFilter.2
  have hrPrim :=
    isPrimitiveResonance_of_smoothNearPrimitivePoleSum_ne_zero
      a ε alpha r hrTwo ha hε haε hεhalf.le halpha hrFilter.2
  have hFarey := one_div_mul_le_abs_intDivNat_sub_intDivNat
    (resonanceNumerator p alpha) (resonanceNumerator r alpha)
    p r (by omega) (by omega) hpPrim hrPrim hpr
  let x : ℝ := (P : ℝ) ^ 2 *
    ((resonanceNumerator p alpha : ℝ) / (p : ℝ) - alpha)
  let y : ℝ := (P : ℝ) ^ 2 *
    ((resonanceNumerator r alpha : ℝ) / (r : ℝ) - alpha)
  have hfloor : ⌊x⌋ = ⌊y⌋ := by
    simpa only [nearActiveGridIndex, x, y] using! hgrid
  have hxylt : |x - y| < 1 := by
    have hxLower : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
    have hxUpper : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
    have hyLower : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
    have hyUpper : y < ((⌊y⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one y
    have hleft : -(1 : ℝ) < x - y := by
      rw [hfloor] at hxLower
      linarith
    have hright : x - y < (1 : ℝ) := by
      rw [hfloor] at hxUpper
      linarith
    exact abs_lt.mpr ⟨hleft, hright⟩
  have hscaledAbs : |x - y| = (P : ℝ) ^ 2 *
      |(resonanceNumerator p alpha : ℝ) / (p : ℝ) -
        (resonanceNumerator r alpha : ℝ) / (r : ℝ)| := by
    dsimp [x, y]
    rw [show
      (P : ℝ) ^ 2 *
          ((resonanceNumerator p alpha : ℝ) / (p : ℝ) - alpha) -
        (P : ℝ) ^ 2 *
          ((resonanceNumerator r alpha : ℝ) / (r : ℝ) - alpha) =
        (P : ℝ) ^ 2 *
          ((resonanceNumerator p alpha : ℝ) / (p : ℝ) -
            (resonanceNumerator r alpha : ℝ) / (r : ℝ)) by ring,
      abs_mul, abs_of_nonneg (sq_nonneg (P : ℝ))]
  have hpUpperR : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hpBounds.2
  have hrUpperR : (r : ℝ) ≤ (P : ℝ) := by exact_mod_cast hrBounds.2
  have hprUpper : (p : ℝ) * (r : ℝ) ≤ (P : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hpUpperR hrUpperR
      (by positivity : (0 : ℝ) ≤ r) (by positivity : (0 : ℝ) ≤ P)]
  have hdenPos : 0 < (p : ℝ) * (r : ℝ) := by positivity
  have hquot : (1 : ℝ) ≤
      (P : ℝ) ^ 2 * (1 / ((p : ℝ) * (r : ℝ))) := by
    rw [one_div, ← div_eq_mul_inv, le_div_iff₀ hdenPos]
    simpa using! hprUpper
  have hscaledLower : (1 : ℝ) ≤ |x - y| := by
    rw [hscaledAbs]
    exact hquot.trans (mul_le_mul_of_nonneg_left hFarey (sq_nonneg (P : ℝ)))
  linarith

/-- At most four denominators can be active in a dyadic block.  This is the
precise pointwise sparsity input used for the low-frequency block norm. -/
theorem card_nearActiveDenominators_le_four
    (a ε alpha : ℝ) (P : ℕ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    (nearActiveDenominators a ε P alpha).card ≤ 4 := by
  let s := nearActiveDenominators a ε P alpha
  let f := fun p ↦ nearActiveGridIndex P p alpha
  have hinj : Set.InjOn f (s : Set ℕ) := by
    simpa only [s, f] using!
      nearActiveGridIndex_injOn a ε alpha P hP ha hε haε hεhalf halpha
  have himageSubset : s.image f ⊆ Finset.Icc (-2 : ℤ) 1 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simpa only [s, f] using!
      nearActiveGridIndex_mem_Icc a ε alpha P p hP ha hε haε hεhalf halpha hp
  calc
    s.card = (s.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc (-2 : ℤ) 1).card := Finset.card_le_card himageSubset
    _ = 4 := by decide

/-- Pointwise square bound for the actual physical carrier block.  The
constant `4` comes only from reduced-rational packing; no continued-fraction
or unproved sparsity hypothesis is hidden here. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTail_le_four_mul_sum
    (N P : ℕ) (ell : ℤ) (a ε alpha : ℝ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ‖smoothNearPrimitivePoleCarrierTail N ell a ε (P / 2) P alpha‖ ^ 2 ≤
      4 * ∑ p ∈ Finset.Ioc (P / 2) P,
        ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
  let s := Finset.Ioc (P / 2) P
  let u := nearActiveDenominators a ε P alpha
  let f : ℕ → ℂ := fun p ↦
    smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha
  have hsum : (∑ p ∈ s, f p) = ∑ p ∈ u, f p := by
    dsimp [u, nearActiveDenominators]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hpMem
    by_cases hpActive : smoothNearPrimitivePoleSum a ε p alpha ≠ 0
    · simp [hpActive]
    · have hpZero : smoothNearPrimitivePoleSum a ε p alpha = 0 :=
        not_ne_iff.mp hpActive
      simp [f, smoothNearPrimitivePoleCarrierTerm,
        unitModulate, hpZero]
  have hcs : ‖∑ p ∈ u, f p‖ ^ 2 ≤
      (u.card : ℝ) * ∑ p ∈ u, ‖f p‖ ^ 2 := by
    have hnorm : ‖∑ p ∈ u, f p‖ ≤ ∑ p ∈ u, ‖f p‖ :=
      norm_sum_le _ _
    calc
      ‖∑ p ∈ u, f p‖ ^ 2 ≤ (∑ p ∈ u, ‖f p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (u.card : ℝ) * ∑ p ∈ u, ‖f p‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
  have hcardNat : u.card ≤ 4 := by
    dsimp [u]
    exact card_nearActiveDenominators_le_four
      a ε alpha P hP ha hε haε hεhalf halpha
  have hcard : (u.card : ℝ) ≤ 4 := by exact_mod_cast hcardNat
  have hus : u ⊆ s := by
    dsimp [u, s, nearActiveDenominators]
    exact Finset.filter_subset _ _
  have hsumNorm : (∑ p ∈ u, ‖f p‖ ^ 2) ≤
      ∑ p ∈ s, ‖f p‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hus (fun _p _hp _hnot ↦ by positivity)
  unfold smoothNearPrimitivePoleCarrierTail
  change ‖∑ p ∈ s, f p‖ ^ 2 ≤ 4 * ∑ p ∈ s, ‖f p‖ ^ 2
  rw [hsum]
  exact hcs.trans (mul_le_mul hcard hsumNorm (by positivity) (by positivity))

private theorem norm_paperExp_activeSparsity (t : ℝ) :
    ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

theorem norm_sq_smoothNearPrimitivePoleCarrierTerm
    (N p : ℕ) (ell : ℤ) (a ε alpha : ℝ) :
    ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 =
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ‖smoothNearPrimitivePoleSum a ε p alpha‖ ^ 2 := by
  unfold smoothNearPrimitivePoleCarrierTerm unitModulate
  rw [norm_mul, norm_mul, norm_paperExp_activeSparsity, one_mul]
  ring

/-- The pointwise packing bound integrated over one period.  The only
exceptional points are the two endpoints, removed explicitly through
`Ioo_ae_eq_Icc`. -/
theorem integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le
    (N P : ℕ) (ell : ℤ) (a ε : ℝ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail
          N ell a ε (P / 2) P alpha‖ ^ 2) ≤
      4 * ∑ p ∈ Finset.Ioc (P / 2) P,
        ∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
  let f : ℝ → ℝ := fun alpha ↦
    ‖smoothNearPrimitivePoleCarrierTail N ell a ε (P / 2) P alpha‖ ^ 2
  let g : ℝ → ℝ := fun alpha ↦
    4 * ∑ p ∈ Finset.Ioc (P / 2) P,
      ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2
  have hfCont : Continuous f := by
    exact (smoothNearPrimitivePoleCarrierTail_continuous
      N (P / 2) P ell a ε ha haε).norm.pow 2
  have hgCont : Continuous g := by
    dsimp [g]
    apply continuous_const.mul
    apply continuous_finset_sum
    intro p _hp
    exact (smoothNearPrimitivePoleCarrierTerm_continuous
      N p ell a ε ha haε).norm.pow 2
  have hpoint : f ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] g := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with alpha halpha
    exact norm_sq_smoothNearPrimitivePoleCarrierTail_le_four_mul_sum
      N P ell a ε alpha hP ha hε haε hεhalf halpha
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (show (0 : ℝ) ≤ 1 by norm_num)
    (hfCont.intervalIntegrable 0 1) (hgCont.intervalIntegrable 0 1) hpoint
  change (∫ alpha in (0 : ℝ)..1, f alpha) ≤ _
  calc
    (∫ alpha in (0 : ℝ)..1, f alpha) ≤
        ∫ alpha in (0 : ℝ)..1, g alpha := hmono
    _ = 4 * ∑ p ∈ Finset.Ioc (P / 2) P,
        ∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum]
      intro p _hp
      exact ((smoothNearPrimitivePoleCarrierTerm_continuous
        N p ell a ε ha haε).norm.pow 2).intervalIntegrable 0 1

/-- The integrated block bound with the actual `j=0` Gevrey mass inserted.
Every factor is explicit and the right side is a finite arithmetic sum. -/
theorem integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le_gevrey
    (N P : ℕ) (ell : ℤ) (a ε : ℝ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail
          N ell a ε (P / 2) P alpha‖ ^ 2) ≤
      4 * ∑ p ∈ Finset.Ioc (P / 2) P,
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
            ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))) := by
  refine (integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le
    N P ell a ε hP ha hε haε hεhalf).trans ?_
  gcongr with p hpMem
  have hpBounds := Finset.mem_Ioc.mp hpMem
  have hpTwo : 2 ≤ p := by
    have hhalf : 2 ≤ P / 2 :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
    omega
  have hmass :=
    integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_le_gevrey
      0 p a ε hpTwo ha hε haε hεhalf
  have hcarrier :
      (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2) =
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleSum a ε p alpha‖ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro alpha _halpha
    exact norm_sq_smoothNearPrimitivePoleCarrierTerm N p ell a ε alpha
  rw [hcarrier]
  have hzeroDeriv : iteratedDeriv 0
      (smoothNearPrimitivePoleSum a ε p) =
      smoothNearPrimitivePoleSum a ε p := by
    simp
  rw [hzeroDeriv] at hmass
  have hmassSimplified :
      (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleSum a ε p alpha‖ ^ 2) ≤
        (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
          ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
    simpa using! hmass
  exact mul_le_mul_of_nonneg_left hmassSimplified (sq_nonneg _)

/-- The totient mass of one dyadic denominator block is bounded by two.
This deliberately elementary estimate is enough for the near-carrier block
bound and avoids importing asymptotics for the summatory totient. -/
theorem sum_totient_mul_inv_sq_Ioc_half_le_two
    (P : ℕ) (hP : 1 ≤ P) :
    (∑ p ∈ Finset.Ioc (P / 2) P,
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) ≤ 2 := by
  have hPR : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hterm : ∀ p ∈ Finset.Ioc (P / 2) P,
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) ≤ 2 / (P : ℝ) := by
    intro p hpMem
    have hpBounds := Finset.mem_Ioc.mp hpMem
    have hpPos : 0 < p := by omega
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hpPos
    have hpLower : P < 2 * p := by
      have hdecomp := Nat.mod_add_div P 2
      have hmod := Nat.mod_lt P (by omega : 0 < 2)
      omega
    have htot : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast Nat.totient_le p
    calc
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) ≤
          (p : ℝ) * (1 / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right htot (by positivity)
      _ = 1 / (p : ℝ) := by field_simp
      _ ≤ 2 / (P : ℝ) := by
        rw [div_le_div_iff₀ hpR hPR]
        have hcast : (P : ℝ) ≤ 2 * (p : ℝ) := by
          exact_mod_cast hpLower.le
        simpa using! hcast
  calc
    (∑ p ∈ Finset.Ioc (P / 2) P,
        (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) ≤
        ∑ _p ∈ Finset.Ioc (P / 2) P, 2 / (P : ℝ) := by
      gcongr with p hpMem
      exact hterm p hpMem
    _ = ((Finset.Ioc (P / 2) P).card : ℝ) * (2 / (P : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (P : ℝ) * (2 / (P : ℝ)) := by
      gcongr
      exact_mod_cast (show (Finset.Ioc (P / 2) P).card ≤ P by
        rw [Nat.card_Ioc]
        omega)
    _ = 2 := by field_simp

/-- Scalar `O(a⁻¹)` norm bound for an entire dyadic physical carrier block.
Combined with the annular leakage estimate, this is the manuscript's
low-denominator square-function input with all constants exposed. -/
theorem integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le_scalar
    (N P : ℕ) (ell : ℤ) (a ε : ℝ) (hP : 4 ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail
          N ell a ε (P / 2) P alpha‖ ^ 2) ≤
      8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
  let G : ℝ := (2 * nearGevreyProfileConstant) ^ 2 * (32 / a)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hmass := integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_le_gevrey
    N P ell a ε hP ha hε haε hεhalf
  have htot := sum_totient_mul_inv_sq_Ioc_half_le_two P (by omega)
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail
          N ell a ε (P / 2) P alpha‖ ^ 2) ≤
        4 * ∑ p ∈ Finset.Ioc (P / 2) P,
          ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
            ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) * G) := by
      simpa only [G] using! hmass
    _ = 4 * (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * G) *
        (∑ p ∈ Finset.Ioc (P / 2) P,
          (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ 4 * (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * G) * 2 := by
      exact mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
      dsimp [G]
      ring

end

end Erdos1002
