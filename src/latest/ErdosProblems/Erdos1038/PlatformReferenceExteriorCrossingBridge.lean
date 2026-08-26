import ErdosProblems.Erdos1038.PlatformReferenceExteriorExplicit
import ErdosProblems.Erdos1038.HighKPlatformCrossing
import ErdosProblems.Erdos1038.PlatformResidualMaterialExteriorIdentity

/-!
# From explicit platform zeroes to canonical exterior crossings

This file supplies the local calculus bridge between the interval checker's
zero/slope certificates and the sign-change predicates used by the canonical
platform-reference limits.  It also identifies the canonical reciprocal
derivative weights with the reciprocal `platformExteriorWx` weights.
-/

set_option warningAsError false

open Filter Set SignType

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

open HighKPlatformFormula

/-- A simple zero with negative derivative has exactly the local sign pattern
required by `IsNegativeSlopeExteriorCrossing`. -/
theorem isNegativeSlopeExteriorCrossing_of_hasDerivAt
    {P : ℝ → ℝ} {d x : ℝ}
    (hx : x < 0) (hP : HasDerivAt P d x) (hzero : P x = 0)
    (hd : d < 0) :
    IsNegativeSlopeExteriorCrossing P x := by
  have hderiv : deriv P x < 0 := by
    rw [hP.deriv]
    exact hd
  have hsign :
      ∀ᶠ y in nhds x, sign (P y) = sign (x - y) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hderiv hzero
  have hsignMem :
      {y : ℝ | sign (P y) = sign (x - y)} ∈ nhds x := hsign
  obtain ⟨lo, hi, hxI, hI⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hsignMem
  refine ⟨hx, ?_, ?_⟩
  · intro l hl
    let y := (max l lo + x) / 2
    have hmax : max l lo < x := max_lt hl hxI.1
    have hly : l < y := by
      dsimp only [y]
      linarith [le_max_left l lo]
    have hloy : lo < y := by
      dsimp only [y]
      linarith [le_max_right l lo]
    have hyx : y < x := by
      dsimp only [y]
      linarith
    have hyhi : y < hi := hyx.trans hxI.2
    have hsy := hI (show y ∈ Ioo lo hi from ⟨hloy, hyhi⟩)
    change sign (P y) = sign (x - y) at hsy
    have hxyPos : 0 < x - y := sub_pos.mpr hyx
    rw [sign_pos hxyPos] at hsy
    exact ⟨y, hly, hyx, sign_eq_one_iff.mp hsy⟩
  · intro u hu
    let m := min (min hi u) 0
    have hxm : x < m := lt_min (lt_min hxI.2 hu) hx
    have hmhi : m ≤ hi :=
      (min_le_left (min hi u) 0).trans (min_le_left hi u)
    have hmu : m ≤ u :=
      (min_le_left (min hi u) 0).trans (min_le_right hi u)
    have hm0 : m ≤ 0 := min_le_right (min hi u) 0
    let y := (x + m) / 2
    have hxy : x < y := by
      dsimp only [y]
      linarith
    have hym : y < m := by
      dsimp only [y]
      linarith
    have hloy : lo < y := hxI.1.trans hxy
    have hyhi : y < hi := hym.trans_le hmhi
    have hyu : y < u := hym.trans_le hmu
    have hy0 : y < 0 := hym.trans_le hm0
    have hsy := hI (show y ∈ Ioo lo hi from ⟨hloy, hyhi⟩)
    change sign (P y) = sign (x - y) at hsy
    rw [sign_neg (sub_neg.mpr hxy)] at hsy
    exact ⟨y, hxy, hyu, hy0, sign_eq_neg_one_iff.mp hsy⟩

/-- A simple zero with positive derivative has exactly the local sign pattern
required by `IsPositiveSlopeExteriorCrossing`. -/
theorem isPositiveSlopeExteriorCrossing_of_hasDerivAt
    {P : ℝ → ℝ} {d a x : ℝ}
    (hx : 0 < x) (hxa : x < a) (hP : HasDerivAt P d x)
    (hzero : P x = 0) (hd : 0 < d) :
    IsPositiveSlopeExteriorCrossing P a x := by
  have hderiv : 0 < deriv P x := by
    rw [hP.deriv]
    exact hd
  have hsign :
      ∀ᶠ y in nhds x, sign (P y) = sign (y - x) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv hzero
  have hsignMem :
      {y : ℝ | sign (P y) = sign (y - x)} ∈ nhds x := hsign
  obtain ⟨lo, hi, hxI, hI⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hsignMem
  refine ⟨hx, hxa, ?_, ?_⟩
  · intro l hl
    let m := max (max l lo) 0
    have hmx : m < x := max_lt (max_lt hl hxI.1) hx
    have hlm : l ≤ m :=
      (le_max_left l lo).trans (le_max_left (max l lo) 0)
    have hlom : lo ≤ m :=
      (le_max_right l lo).trans (le_max_left (max l lo) 0)
    have h0m : 0 ≤ m := le_max_right (max l lo) 0
    let y := (m + x) / 2
    have hmy : m < y := by
      dsimp only [y]
      linarith
    have hyx : y < x := by
      dsimp only [y]
      linarith
    have hly : l < y := hlm.trans_lt hmy
    have hloy : lo < y := hlom.trans_lt hmy
    have hy0 : 0 < y := h0m.trans_lt hmy
    have hyhi : y < hi := hyx.trans hxI.2
    have hsy := hI (show y ∈ Ioo lo hi from ⟨hloy, hyhi⟩)
    change sign (P y) = sign (y - x) at hsy
    rw [sign_neg (sub_neg.mpr hyx)] at hsy
    exact ⟨y, hly, hy0, hyx, sign_eq_neg_one_iff.mp hsy⟩
  · intro u hu
    let m := min (min hi u) a
    have hxm : x < m := lt_min (lt_min hxI.2 hu) hxa
    have hmhi : m ≤ hi :=
      (min_le_left (min hi u) a).trans (min_le_left hi u)
    have hmu : m ≤ u :=
      (min_le_left (min hi u) a).trans (min_le_right hi u)
    have hma : m ≤ a := min_le_right (min hi u) a
    let y := (x + m) / 2
    have hxy : x < y := by
      dsimp only [y]
      linarith
    have hym : y < m := by
      dsimp only [y]
      linarith
    have hloy : lo < y := hxI.1.trans hxy
    have hyhi : y < hi := hym.trans_le hmhi
    have hyu : y < u := hym.trans_le hmu
    have hya : y < a := hym.trans_le hma
    have hsy := hI (show y ∈ Ioo lo hi from ⟨hloy, hyhi⟩)
    change sign (P y) = sign (y - x) at hsy
    rw [sign_pos (sub_pos.mpr hxy)] at hsy
    exact ⟨y, hxy, hyu, hya, sign_eq_one_iff.mp hsy⟩

/-- The correction factor in the explicit derivative formula cannot vanish
at a point strictly left of a genuine platform. -/
theorem platformExteriorCorrection_ne_zero
    {a x : ℝ} (ha : 0 < a) (ha2 : a < 2) (hxa : x < a) :
    1 - ((Real.sqrt 2 - Real.sqrt a) /
          (Real.sqrt 2 + Real.sqrt a)) * platformRho a x ≠ 0 := by
  have hS : 0 < Real.sqrt (2 * a) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hSsq : (Real.sqrt (2 * a)) ^ 2 = 2 * a :=
    Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
  have hSa : a < Real.sqrt (2 * a) := by
    nlinarith [sq_nonneg (Real.sqrt (2 * a) + a)]
  have hK : 0 < platformCrossingScale a x :=
    platformCrossingScale_pos hxa ha2
  have hcenter : a < platformCenter a := by
    simp [platformCenter]
    linarith
  have hnum :
      0 < Real.sqrt (2 * a) + platformCrossingScale a x - x := by
    linarith
  have hden :
      0 < platformCenter a - x + platformCrossingScale a x :=
    add_pos (sub_pos.mpr (hxa.trans hcenter)) hK
  rw [platformExteriorCorrection_eq ha ha2 hxa]
  exact (div_pos hnum hden).ne'

/-- The quantity called the continuum `x`-derivative really is the
derivative of the canonical normalized exterior potential. -/
theorem hasDerivAt_platformReferenceExteriorPotentialLimit_explicit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) (hx0 : x ≠ 0) :
    HasDerivAt
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold)
      (platformReferenceExteriorPotentialXDerivativeLimit C k a
        hk ha ha2 hthreshold x) x := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hk0 : k ≠ 0 := hkpos.ne'
  have hW := hasDerivAt_platformExteriorW_x
    (k := k) hxa ha2 hx0
      (platformExteriorCorrection_ne_zero ha ha2 hxa)
  have hscaled := hW.const_mul (1 / k)
  have hevent :
      (platformReferenceExteriorPotentialLimit C k a
          hk ha ha2 hthreshold) =ᶠ[nhds x]
        (fun y : ℝ ↦ (1 / k) * platformExteriorW k a y) := by
    filter_upwards [Iio_mem_nhds hxa, eventually_ne_nhds hx0]
      with y hya hy0
    have hscale :=
      k_mul_platformReferenceExteriorPotentialLimit_eq_platformExteriorW
        C k a hk ha ha2 hthreshold hya hy0
    calc
      platformReferenceExteriorPotentialLimit C k a
          hk ha ha2 hthreshold y =
          (1 / k) *
            (k * platformReferenceExteriorPotentialLimit C k a
              hk ha ha2 hthreshold y) := by field_simp [hk0]
      _ = (1 / k) * platformExteriorW k a y := by rw [hscale]
  have hcanonical := hscaled.congr_of_eventuallyEq hevent
  apply hcanonical.congr_deriv
  have hscaleDerivative :=
    k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
      C k a hk ha ha2 hthreshold hxa hx0
  rw [← hscaleDerivative]
  field_simp [hk0]

/-- A checker-certified negative root and negative `W_x` are a canonical
negative-slope exterior crossing of the normalized reference potential. -/
theorem platformReference_isNegativeSlopeExteriorCrossing_of_checker
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hx : x < 0)
    (hzero : platformExteriorW k a x = 0)
    (hWx : platformExteriorWx k a x < 0) :
    IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) x := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hxa : x < a := hx.trans ha
  have hx0 : x ≠ 0 := hx.ne
  have hP := hasDerivAt_platformReferenceExteriorPotentialLimit_explicit
    C k a hk ha ha2 hthreshold hxa hx0
  have hscale :=
    k_mul_platformReferenceExteriorPotentialLimit_eq_platformExteriorW
      C k a hk ha ha2 hthreshold hxa hx0
  have hPzero :
      platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold x = 0 :=
    (mul_eq_zero.mp (hscale.trans hzero)).resolve_left hkpos.ne'
  have hscaleDerivative :=
    k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
      C k a hk ha ha2 hthreshold hxa hx0
  have hmulNeg :
      k * platformReferenceExteriorPotentialXDerivativeLimit C k a
          hk ha ha2 hthreshold x < 0 := by
    rw [hscaleDerivative]
    exact hWx
  exact isNegativeSlopeExteriorCrossing_of_hasDerivAt hx hP hPzero
    (neg_of_mul_neg_right hmulNeg hkpos.le)

/-- A checker-certified positive root and positive `W_x` are a canonical
positive-slope exterior crossing of the normalized reference potential. -/
theorem platformReference_isPositiveSlopeExteriorCrossing_of_checker
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hx : 0 < x) (hxa : x < a)
    (hzero : platformExteriorW k a x = 0)
    (hWx : 0 < platformExteriorWx k a x) :
    IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a x := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hx0 : x ≠ 0 := hx.ne'
  have hP := hasDerivAt_platformReferenceExteriorPotentialLimit_explicit
    C k a hk ha ha2 hthreshold hxa hx0
  have hscale :=
    k_mul_platformReferenceExteriorPotentialLimit_eq_platformExteriorW
      C k a hk ha ha2 hthreshold hxa hx0
  have hPzero :
      platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold x = 0 :=
    (mul_eq_zero.mp (hscale.trans hzero)).resolve_left hkpos.ne'
  have hscaleDerivative :=
    k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
      C k a hk ha ha2 hthreshold hxa hx0
  have hmulPos :
      0 < k * platformReferenceExteriorPotentialXDerivativeLimit C k a
          hk ha ha2 hthreshold x := by
    rw [hscaleDerivative]
    exact hWx
  exact isPositiveSlopeExteriorCrossing_of_hasDerivAt hx hxa hP hPzero
    (pos_of_mul_pos_right hmulPos hkpos.le)

/-- The canonical negative-crossing adjoint mass is the checker's negative
reciprocal `W_x` weight. -/
theorem platformReferenceNegativeCrossingAdjointWeight_eq_neg_one_div_platformExteriorWx
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) (hx0 : x ≠ 0) :
    platformReferenceNegativeCrossingAdjointWeight C k a
        hk ha ha2 hthreshold x =
      -1 / platformExteriorWx k a x := by
  unfold platformReferenceNegativeCrossingAdjointWeight
  rw [k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
    C k a hk ha ha2 hthreshold hxa hx0]

/-- The canonical positive-crossing adjoint mass is the checker's positive
reciprocal `W_x` weight. -/
theorem platformReferencePositiveCrossingAdjointWeight_eq_one_div_platformExteriorWx
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) (hx0 : x ≠ 0) :
    platformReferencePositiveCrossingAdjointWeight C k a
        hk ha ha2 hthreshold x =
      1 / platformExteriorWx k a x := by
  unfold platformReferencePositiveCrossingAdjointWeight
  rw [k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
    C k a hk ha ha2 hthreshold hxa hx0]

/-- Checker-facing data for a pair of simple exterior zeroes.  This is
independent of the residual configuration because the canonical platform
potential has the same explicit exterior formula for every configuration. -/
structure PlatformExplicitExteriorCrossingCertificate
    (k a xMinus xPlus : ℝ) : Prop where
  xMinus_neg : xMinus < 0
  xPlus_pos : 0 < xPlus
  xPlus_lt_platform : xPlus < a
  xMinus_zero : platformExteriorW k a xMinus = 0
  xPlus_zero : platformExteriorW k a xPlus = 0
  xMinus_slope_neg : platformExteriorWx k a xMinus < 0
  xPlus_slope_pos : 0 < platformExteriorWx k a xPlus

/-- Configuration-facing consequences of one explicit crossing
certificate. -/
structure PlatformCanonicalExteriorCrossingData
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus : ℝ) : Prop where
  negativeCrossing : IsNegativeSlopeExteriorCrossing
    (platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold) xMinus
  positiveCrossing : IsPositiveSlopeExteriorCrossing
    (platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold) a xPlus
  negativeDerivative_ne :
    platformReferenceExteriorPotentialXDerivativeLimit C k a
      hk ha ha2 hthreshold xMinus ≠ 0
  positiveDerivative_ne :
    platformReferenceExteriorPotentialXDerivativeLimit C k a
      hk ha ha2 hthreshold xPlus ≠ 0
  negativeWeight_pos : 0 <
    platformReferenceNegativeCrossingAdjointWeight C k a
      hk ha ha2 hthreshold xMinus
  positiveWeight_pos : 0 <
    platformReferencePositiveCrossingAdjointWeight C k a
      hk ha ha2 hthreshold xPlus

/-- The exact exterior formula turns checker zero/slope data into every
canonical crossing fact needed by the mesh-limit and adjoint arguments. -/
theorem PlatformExplicitExteriorCrossingCertificate.toCanonical
    {k a xMinus xPlus : ℝ}
    (hcert : PlatformExplicitExteriorCrossingCertificate
      k a xMinus xPlus)
    (C : ResidualConfiguration iota)
    (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    PlatformCanonicalExteriorCrossingData C k a
      hk ha ha2 hthreshold xMinus xPlus := by
  have hxMinusA : xMinus < a := hcert.xMinus_neg.trans ha
  have hxMinus0 : xMinus ≠ 0 := hcert.xMinus_neg.ne
  have hxPlus0 : xPlus ≠ 0 := hcert.xPlus_pos.ne'
  have hminusScale :=
    k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
      C k a hk ha ha2 hthreshold hxMinusA hxMinus0
  have hplusScale :=
    k_mul_platformReferenceExteriorPotentialXDerivativeLimit_eq_platformExteriorWx
      C k a hk ha ha2 hthreshold hcert.xPlus_lt_platform hxPlus0
  refine
    { negativeCrossing :=
        platformReference_isNegativeSlopeExteriorCrossing_of_checker
          C k a hk ha ha2 hthreshold hcert.xMinus_neg
            hcert.xMinus_zero hcert.xMinus_slope_neg
      positiveCrossing :=
        platformReference_isPositiveSlopeExteriorCrossing_of_checker
          C k a hk ha ha2 hthreshold hcert.xPlus_pos
            hcert.xPlus_lt_platform hcert.xPlus_zero hcert.xPlus_slope_pos
      negativeDerivative_ne := ?_
      positiveDerivative_ne := ?_
      negativeWeight_pos := ?_
      positiveWeight_pos := ?_ }
  · intro hzero
    rw [hzero, mul_zero] at hminusScale
    exact hcert.xMinus_slope_neg.ne hminusScale.symm
  · intro hzero
    rw [hzero, mul_zero] at hplusScale
    exact hcert.xPlus_slope_pos.ne' hplusScale.symm
  · rw [platformReferenceNegativeCrossingAdjointWeight_eq_neg_one_div_platformExteriorWx
      C k a hk ha ha2 hthreshold hxMinusA hxMinus0]
    exact div_pos_of_neg_of_neg (by norm_num) hcert.xMinus_slope_neg
  · rw [platformReferencePositiveCrossingAdjointWeight_eq_one_div_platformExteriorWx
      C k a hk ha ha2 hthreshold hcert.xPlus_lt_platform hxPlus0]
    exact one_div_pos.mpr hcert.xPlus_slope_pos

end

end Erdos1038
