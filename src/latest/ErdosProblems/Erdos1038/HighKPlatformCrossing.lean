import ErdosProblems.Erdos1038.HighKPlatformIntervalChecker
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Analytic semantics and stitching for certified platform crossings

This file connects the interval checker's formal symbolic derivative to the
ordinary real derivative, then supplies a compact IVT/uniqueness theorem for
stitching pointwise zeroes into a continuous branch.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

open HighKIntervalExpr

namespace HighKPlatformFormula

/-- Replace one coordinate while leaving all other coordinates fixed. -/
def replaceCoordinate {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    Fin n → ℝ :=
  fun j ↦ if j = i then t else v j

@[simp] theorem replaceCoordinate_same {n : ℕ} (v : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    replaceCoordinate v i t i = t := by
  simp [replaceCoordinate]

@[simp] theorem replaceCoordinate_self {n : ℕ} (v : Fin n → ℝ)
    (i : Fin n) :
    replaceCoordinate v i (v i) = v := by
  funext j
  by_cases h : j = i <;> simp [replaceCoordinate, h]

/-- The exact analytic side conditions needed by `diffExpr`.  Real logarithm
and square root are differentiable at every nonzero input in Mathlib's real
extensions, so no unnecessarily strong positivity assumption is recorded. -/
def DiffDomain {n : ℕ} (v : Fin n → ℝ) :
    HighKIntervalExpr n → Prop
  | .rat _ => True
  | .var _ => True
  | .add p q => DiffDomain v p ∧ DiffDomain v q
  | .neg p => DiffDomain v p
  | .mul p q => DiffDomain v p ∧ DiffDomain v q
  | .inv p => DiffDomain v p ∧ evalReal v p ≠ 0
  | .log _ p => DiffDomain v p ∧ evalReal v p ≠ 0
  | .sqrt _ p => DiffDomain v p ∧ evalReal v p ≠ 0
  | .sin _ p => DiffDomain v p
  | .cos _ p => DiffDomain v p

/-- Formal symbolic differentiation computes the genuine one-variable
derivative obtained by varying coordinate `i`. -/
theorem hasDerivAt_evalReal_diffExpr {n : ℕ} (i : Fin n)
    (v : Fin n → ℝ) :
    ∀ e : HighKIntervalExpr n,
      DiffDomain v e →
        HasDerivAt
          (fun t ↦ evalReal (replaceCoordinate v i t) e)
          (evalReal v (diffExpr i e)) (v i) := by
  intro e
  induction e with
  | rat r =>
      intro _
      simpa [diffExpr] using! hasDerivAt_const (v i) (r : ℝ)
  | var j =>
      intro _
      by_cases hji : j = i
      · subst j
        simpa [diffExpr] using! hasDerivAt_id (v i)
      · simpa [replaceCoordinate, hji, diffExpr] using!
          hasDerivAt_const (v i) (v j)
  | add p q ihp ihq =>
      rintro ⟨hp, hq⟩
      simpa [diffExpr] using! (ihp hp).add (ihq hq)
  | neg p ih =>
      intro hp
      simpa [diffExpr] using! (ih hp).neg
  | mul p q ihp ihq =>
      rintro ⟨hp, hq⟩
      simpa [diffExpr] using! (ihp hp).mul (ihq hq)
  | inv p ih =>
      rintro ⟨hp, hp0⟩
      have hp0' : evalReal (replaceCoordinate v i (v i)) p ≠ 0 := by
        simpa using! hp0
      (convert! (ih hp).inv hp0' using 1;
        simp [diffExpr, HighKIntervalExpr.div, HighKIntervalExpr.sq,
          div_eq_mul_inv, pow_two])
  | log terms p ih =>
      rintro ⟨hp, hp0⟩
      have hp0' : evalReal (replaceCoordinate v i (v i)) p ≠ 0 := by
        simpa using! hp0
      simpa [diffExpr, HighKIntervalExpr.div, div_eq_mul_inv] using!
        (ih hp).log hp0'
  | sqrt steps p ih =>
      rintro ⟨hp, hp0⟩
      have hp0' : evalReal (replaceCoordinate v i (v i)) p ≠ 0 := by
        simpa using! hp0
      simpa [diffExpr, HighKIntervalExpr.div, div_eq_mul_inv] using!
        (ih hp).sqrt hp0'
  | sin doubles p ih =>
      intro hp
      simpa [diffExpr] using! (ih hp).sin
  | cos doubles p ih =>
      intro hp
      simpa [diffExpr] using! (ih hp).cos

@[simp] theorem replaceCoordinate_vec5_zero
    (k xm xp ell pi t : ℝ) :
    replaceCoordinate ![k, xm, xp, ell, pi] 0 t =
      ![t, xm, xp, ell, pi] := by
  funext j
  fin_cases j <;> simp [replaceCoordinate]

def crossingEnvironment (side : PlatformCrossingSide)
    (k x other ell pi : ℝ) : Fin 5 → ℝ :=
  match side with
  | .minus => ![k, x, other, ell, pi]
  | .plus => ![k, other, x, ell, pi]

def CrossingCoordinateHasSide (side : PlatformCrossingSide) (x : ℝ) : Prop :=
  match side with
  | .minus => x < 0
  | .plus => 0 < x

theorem crossingWE_eval
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    (side : PlatformCrossingSide) {k x other ell pi : ℝ}
    (hx : CrossingCoordinateHasSide side x) :
    evalReal (crossingEnvironment side k x other ell pi)
        (crossingWE logTerms sqrtSteps edge side) =
      platformExteriorW k (highKPlatformEdge edge k) x := by
  cases side with
  | minus =>
      exact exteriorWE_eval_minus logTerms sqrtSteps edge hx
  | plus =>
      exact exteriorWE_eval_plus logTerms sqrtSteps edge hx

@[simp] theorem crossingWxE_eval_side
    (sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    (side : PlatformCrossingSide) (k x other ell pi : ℝ) :
    evalReal (crossingEnvironment side k x other ell pi)
        (crossingWxE sqrtSteps edge side) =
      platformExteriorWx k (highKPlatformEdge edge k) x := by
  cases side <;> simp [crossingEnvironment, crossingWxE]

/-- On the negative crossing, the formal `k` derivative is the actual
derivative of the exterior potential along the selected platform edge. -/
theorem hasDerivAt_platformExteriorW_alongEdge_minus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxm : xm < 0)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .minus)) :
    HasDerivAt
      (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xm)
      (evalReal ![k, xm, xp, ell, pi]
        (diffExpr 0 (crossingWE logTerms sqrtSteps edge .minus))) k := by
  have h := hasDerivAt_evalReal_diffExpr 0
    ![k, xm, xp, ell, pi]
    (crossingWE logTerms sqrtSteps edge .minus) hdom
  simp only [replaceCoordinate_vec5_zero] at h
  have heval :
      (fun t ↦ evalReal ![t, xm, xp, ell, pi]
        (crossingWE logTerms sqrtSteps edge .minus)) =
      (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xm) := by
    funext t
    exact exteriorWE_eval_minus logTerms sqrtSteps edge hxm
  rwa [heval] at h

/-- Positive-side counterpart of
`hasDerivAt_platformExteriorW_alongEdge_minus`. -/
theorem hasDerivAt_platformExteriorW_alongEdge_plus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxp : 0 < xp)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .plus)) :
    HasDerivAt
      (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xp)
      (evalReal ![k, xm, xp, ell, pi]
        (diffExpr 0 (crossingWE logTerms sqrtSteps edge .plus))) k := by
  have h := hasDerivAt_evalReal_diffExpr 0
    ![k, xm, xp, ell, pi]
    (crossingWE logTerms sqrtSteps edge .plus) hdom
  simp only [replaceCoordinate_vec5_zero] at h
  have heval :
      (fun t ↦ evalReal ![t, xm, xp, ell, pi]
        (crossingWE logTerms sqrtSteps edge .plus)) =
      (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xp) := by
    funext t
    exact exteriorWE_eval_plus logTerms sqrtSteps edge hxp
  rwa [heval] at h

theorem hasDerivAt_platformExteriorW_alongEdge
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    (side : PlatformCrossingSide) {k x other ell pi : ℝ}
    (hx : CrossingCoordinateHasSide side x)
    (hdom : DiffDomain (crossingEnvironment side k x other ell pi)
      (crossingWE logTerms sqrtSteps edge side)) :
    HasDerivAt
      (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) x)
      (evalReal (crossingEnvironment side k x other ell pi)
        (diffExpr 0 (crossingWE logTerms sqrtSteps edge side))) k := by
  cases side with
  | minus =>
      exact hasDerivAt_platformExteriorW_alongEdge_minus
        logTerms sqrtSteps edge hx hdom
  | plus =>
      exact hasDerivAt_platformExteriorW_alongEdge_plus
        logTerms sqrtSteps edge hx hdom

theorem deriv_platformExteriorW_alongEdge_minus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxm : xm < 0)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .minus)) :
    deriv (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xm) k =
      evalReal ![k, xm, xp, ell, pi]
        (diffExpr 0 (crossingWE logTerms sqrtSteps edge .minus)) :=
  (hasDerivAt_platformExteriorW_alongEdge_minus
    logTerms sqrtSteps edge hxm hdom).deriv

theorem deriv_platformExteriorW_alongEdge_plus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxp : 0 < xp)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .plus)) :
    deriv (fun t ↦ platformExteriorW t (highKPlatformEdge edge t) xp) k =
      evalReal ![k, xm, xp, ell, pi]
        (diffExpr 0 (crossingWE logTerms sqrtSteps edge .plus)) :=
  (hasDerivAt_platformExteriorW_alongEdge_plus
    logTerms sqrtSteps edge hxp hdom).deriv

theorem crossingSlopeE_eval_minus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxm : xm < 0)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .minus)) :
    evalReal ![k, xm, xp, ell, pi]
        (crossingSlopeE logTerms sqrtSteps edge .minus) =
      -(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xm) k /
        platformExteriorWx k (highKPlatformEdge edge k) xm) := by
  rw [crossingSlopeE]
  simp only [HighKIntervalExpr.div, HighKIntervalExpr.evalReal,
    crossingWxE]
  rw [exteriorWxE_eval]
  rw [deriv_platformExteriorW_alongEdge_minus
    logTerms sqrtSteps edge hxm hdom]
  simp [div_eq_mul_inv]

theorem crossingSlopeE_eval_plus
    (logTerms sqrtSteps : ℕ) (edge : HighKPlatformEdge)
    {k xm xp ell pi : ℝ} (hxp : 0 < xp)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .plus)) :
    evalReal ![k, xm, xp, ell, pi]
        (crossingSlopeE logTerms sqrtSteps edge .plus) =
      -(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xp) k /
        platformExteriorWx k (highKPlatformEdge edge k) xp) := by
  rw [crossingSlopeE]
  simp only [HighKIntervalExpr.div, HighKIntervalExpr.evalReal,
    crossingWxE]
  rw [exteriorWxE_eval]
  rw [deriv_platformExteriorW_alongEdge_plus
    logTerms sqrtSteps edge hxp hdom]
  simp [div_eq_mul_inv]

theorem PlatformCrossingBranchCertificate.wx_negative_minus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .minus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i)) :
    platformExteriorWx k (highKPlatformEdge edge k) xm < 0 := by
  have h := evalNegative_sound cert.envelope_ordered hcontains cert.wx_sign
  simpa [crossingWxE] using! h

theorem PlatformCrossingBranchCertificate.wx_positive_plus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .plus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i)) :
    0 < platformExteriorWx k (highKPlatformEdge edge k) xp := by
  have h := evalPositive_sound cert.envelope_ordered hcontains cert.wx_sign
  simpa [crossingWxE] using! h

theorem PlatformCrossingBranchCertificate.slope_contains_minus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .minus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i))
    (hxm : xm < 0)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .minus)) :
    cert.slopeBox.Contains
      (-(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xm) k /
        platformExteriorWx k (highKPlatformEdge edge k) xm)) := by
  have h := evalInterval_sound cert.envelope_ordered hcontains
    (crossingSlopeE logTerms sqrtSteps edge .minus) cert.slopeBox
    cert.slope_eval
  rw [crossingSlopeE_eval_minus
    logTerms sqrtSteps edge hxm hdom] at h
  exact h.2

theorem PlatformCrossingBranchCertificate.slope_contains_plus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .plus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i))
    (hxp : 0 < xp)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .plus)) :
    cert.slopeBox.Contains
      (-(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xp) k /
        platformExteriorWx k (highKPlatformEdge edge k) xp)) := by
  have h := evalInterval_sound cert.envelope_ordered hcontains
    (crossingSlopeE logTerms sqrtSteps edge .plus) cert.slopeBox
    cert.slope_eval
  rw [crossingSlopeE_eval_plus
    logTerms sqrtSteps edge hxp hdom] at h
  exact h.2

def SlopeHasOrientation (orientation : PlatformSlopeOrientation)
    (slope : ℝ) : Prop :=
  match orientation with
  | .decreasing => slope < 0
  | .increasing => 0 < slope

def TransverseHasSide (side : PlatformCrossingSide) (wx : ℝ) : Prop :=
  match side with
  | .minus => wx < 0
  | .plus => 0 < wx

def WeakCrossingBracket (side : PlatformCrossingSide)
    (f : ℝ → ℝ) (left right : ℝ) : Prop :=
  match side with
  | .minus => 0 ≤ f left ∧ f right ≤ 0
  | .plus => f left ≤ 0 ∧ 0 ≤ f right

theorem slopeHasOrientation_of_box
    {orientation : PlatformSlopeOrientation} {I : RatInterval} {slope : ℝ}
    (hcontains : I.Contains slope) (hsign : slopeBoxSign orientation I) :
    SlopeHasOrientation orientation slope := by
  cases orientation with
  | decreasing =>
      exact lt_of_le_of_lt hcontains.2 (by
        simpa [slopeBoxSign] using! hsign)
  | increasing =>
      exact lt_of_lt_of_le (by
        simpa [slopeBoxSign] using! hsign) hcontains.1

theorem PlatformCrossingBranchCertificate.actualSlope_hasOrientation_minus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .minus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i))
    (hxm : xm < 0)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .minus)) :
    SlopeHasOrientation cert.orientation
      (-(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xm) k /
        platformExteriorWx k (highKPlatformEdge edge k) xm)) :=
  slopeHasOrientation_of_box
    (cert.slope_contains_minus hcontains hxm hdom) cert.slope_sign

theorem PlatformCrossingBranchCertificate.actualSlope_hasOrientation_plus
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge .plus)
    {k xm xp ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (![k, xm, xp, ell, pi] i))
    (hxp : 0 < xp)
    (hdom : DiffDomain ![k, xm, xp, ell, pi]
      (crossingWE logTerms sqrtSteps edge .plus)) :
    SlopeHasOrientation cert.orientation
      (-(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) xp) k /
        platformExteriorWx k (highKPlatformEdge edge k) xp)) :=
  slopeHasOrientation_of_box
    (cert.slope_contains_plus hcontains hxp hdom) cert.slope_sign

theorem PlatformCrossingBranchCertificate.transverse_hasSide
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {k x other ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (crossingEnvironment side k x other ell pi i)) :
    TransverseHasSide side
      (platformExteriorWx k (highKPlatformEdge edge k) x) := by
  cases side with
  | minus =>
      exact cert.wx_negative_minus hcontains
  | plus =>
      exact cert.wx_positive_plus hcontains

theorem PlatformCrossingBranchCertificate.actualSlope_hasOrientation
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {k x other ell pi : ℝ}
    (hcontains : ∀ i, (cert.envelope i).Contains
      (crossingEnvironment side k x other ell pi i))
    (hx : CrossingCoordinateHasSide side x)
    (hdom : DiffDomain (crossingEnvironment side k x other ell pi)
      (crossingWE logTerms sqrtSteps edge side)) :
    SlopeHasOrientation cert.orientation
      (-(deriv (fun t ↦
          platformExteriorW t (highKPlatformEdge edge t) x) k /
        platformExteriorWx k (highKPlatformEdge edge k) x)) := by
  cases side with
  | minus =>
      exact cert.actualSlope_hasOrientation_minus hcontains hx hdom
  | plus =>
      exact cert.actualSlope_hasOrientation_plus hcontains hx hdom

theorem PlatformCrossingBranchCertificate.weakBracket_atLo
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {k xLeft xRight other ell pi : ℝ}
    (hleft : ∀ i, (cert.atLoLeft i).Contains
      (crossingEnvironment side k xLeft other ell pi i))
    (hright : ∀ i, (cert.atLoRight i).Contains
      (crossingEnvironment side k xRight other ell pi i))
    (hxLeft : CrossingCoordinateHasSide side xLeft)
    (hxRight : CrossingCoordinateHasSide side xRight) :
    WeakCrossingBracket side
      (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
      xLeft xRight := by
  cases side with
  | minus =>
      have hl := evalPositive_sound cert.atLoLeft_ordered hleft
        cert.atLo_signs.1
      have hr := evalNegative_sound cert.atLoRight_ordered hright
        cert.atLo_signs.2
      rw [crossingWE_eval logTerms sqrtSteps edge .minus hxLeft] at hl
      rw [crossingWE_eval logTerms sqrtSteps edge .minus hxRight] at hr
      exact ⟨hl.le, hr.le⟩
  | plus =>
      have hl := evalNegative_sound cert.atLoLeft_ordered hleft
        cert.atLo_signs.1
      have hr := evalPositive_sound cert.atLoRight_ordered hright
        cert.atLo_signs.2
      rw [crossingWE_eval logTerms sqrtSteps edge .plus hxLeft] at hl
      rw [crossingWE_eval logTerms sqrtSteps edge .plus hxRight] at hr
      exact ⟨hl.le, hr.le⟩

theorem PlatformCrossingBranchCertificate.weakBracket_atHi
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {k xLeft xRight other ell pi : ℝ}
    (hleft : ∀ i, (cert.atHiLeft i).Contains
      (crossingEnvironment side k xLeft other ell pi i))
    (hright : ∀ i, (cert.atHiRight i).Contains
      (crossingEnvironment side k xRight other ell pi i))
    (hxLeft : CrossingCoordinateHasSide side xLeft)
    (hxRight : CrossingCoordinateHasSide side xRight) :
    WeakCrossingBracket side
      (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
      xLeft xRight := by
  cases side with
  | minus =>
      have hl := evalPositive_sound cert.atHiLeft_ordered hleft
        cert.atHi_signs.1
      have hr := evalNegative_sound cert.atHiRight_ordered hright
        cert.atHi_signs.2
      rw [crossingWE_eval logTerms sqrtSteps edge .minus hxLeft] at hl
      rw [crossingWE_eval logTerms sqrtSteps edge .minus hxRight] at hr
      exact ⟨hl.le, hr.le⟩
  | plus =>
      have hl := evalNegative_sound cert.atHiLeft_ordered hleft
        cert.atHi_signs.1
      have hr := evalPositive_sound cert.atHiRight_ordered hright
        cert.atHi_signs.2
      rw [crossingWE_eval logTerms sqrtSteps edge .plus hxLeft] at hl
      rw [crossingWE_eval logTerms sqrtSteps edge .plus hxRight] at hr
      exact ⟨hl.le, hr.le⟩

/-- Algebraic core of implicit differentiation: differentiating the zero
identity forces the branch derivative to be `-F_k/F_x`. -/
theorem implicitRootDerivative_eq
    {F : ℝ → ℝ → ℝ} {root : ℝ → ℝ}
    {k Fk Fx root' : ℝ}
    (hzero : ∀ t, F t (root t) = 0)
    (hcomp : HasDerivAt (fun t ↦ F t (root t))
      (Fk + Fx * root') k)
    (hFx : Fx ≠ 0) :
    root' = -Fk / Fx := by
  have hfun : (fun t ↦ F t (root t)) = (fun _ ↦ (0 : ℝ)) := by
    funext t
    exact hzero t
  have hzeroDeriv : HasDerivAt (fun t ↦ F t (root t)) 0 k := by
    rw [hfun]
    exact hasDerivAt_const k 0
  have heq : Fk + Fx * root' = 0 := hcomp.unique hzeroDeriv
  rw [eq_div_iff hFx]
  nlinarith

theorem strictMonotoneOn_of_oriented_derivative
    {root slope : ℝ → ℝ} {kLo kHi : ℝ}
    (orientation : PlatformSlopeOrientation)
    (hcontinuous : ContinuousOn root (Icc kLo kHi))
    (hderiv : ∀ k ∈ interior (Icc kLo kHi),
      HasDerivAt root (slope k) k)
    (horientation : ∀ k ∈ interior (Icc kLo kHi),
      SlopeHasOrientation orientation (slope k)) :
    match orientation with
    | .decreasing => StrictAntiOn root (Icc kLo kHi)
    | .increasing => StrictMonoOn root (Icc kLo kHi) := by
  cases orientation with
  | decreasing =>
      exact strictAntiOn_of_deriv_neg (convex_Icc kLo kHi) hcontinuous
        (fun k hk ↦ by
          rw [(hderiv k hk).deriv]
          exact horientation k hk)
  | increasing =>
      exact strictMonoOn_of_deriv_pos (convex_Icc kLo kHi) hcontinuous
        (fun k hk ↦ by
          rw [(hderiv k hk).deriv]
          exact horientation k hk)

/-- Endpoint root brackets plus the certified slope orientation identify one
global envelope for the stitched branch. -/
theorem root_mem_envelope_of_orientation
    {root : ℝ → ℝ} {kLo kHi loLeft loRight hiLeft hiRight : ℝ}
    (hk : kLo ≤ kHi)
    (orientation : PlatformSlopeOrientation)
    (horiented : match orientation with
      | .decreasing => AntitoneOn root (Icc kLo kHi)
      | .increasing => MonotoneOn root (Icc kLo kHi))
    (hlo : root kLo ∈ Icc loLeft loRight)
    (hhi : root kHi ∈ Icc hiLeft hiRight) :
    ∀ k ∈ Icc kLo kHi,
      match orientation with
      | .decreasing => root k ∈ Icc hiLeft loRight
      | .increasing => root k ∈ Icc loLeft hiRight := by
  intro k hkmem
  have hkLo : kLo ∈ Icc kLo kHi := left_mem_Icc.mpr hk
  have hkHi : kHi ∈ Icc kLo kHi := right_mem_Icc.mpr hk
  cases orientation with
  | decreasing =>
      exact ⟨hhi.1.trans (horiented hkmem hkHi hkmem.2),
        (horiented hkLo hkmem hkmem.1).trans hlo.2⟩
  | increasing =>
      exact ⟨hlo.1.trans (horiented hkLo hkmem hkmem.1),
        (horiented hkmem hkHi hkmem.2).trans hhi.2⟩

/-! ## The checked `W_x` formula is the genuine transverse derivative -/

theorem hasDerivAt_platformCrossingScale
    {a x : ℝ} (hxa : x < a) (ha2 : a < 2) :
    HasDerivAt (platformCrossingScale a)
      (-(platformCenter a - x) / platformCrossingScale a x) x := by
  have hradBase :=
    ((hasDerivAt_const x a).sub (hasDerivAt_id x)).mul
      ((hasDerivAt_const x 2).sub (hasDerivAt_id x))
  have hrad : HasDerivAt (fun y : ℝ ↦ (a - y) * (2 - y))
      (-(2 - x) - (a - x)) x := by
    convert! hradBase using 1
    simp only [Pi.sub_apply, id_eq]
    ring
  have hK0 : platformCrossingScale a x ≠ 0 :=
    (platformCrossingScale_pos hxa ha2).ne'
  have hrad0 : (a - x) * (2 - x) ≠ 0 :=
    mul_ne_zero (sub_pos.mpr hxa).ne' (sub_pos.mpr (hxa.trans ha2)).ne'
  have hsqrt := hrad.sqrt hrad0
  change HasDerivAt (fun y ↦ Real.sqrt ((a - y) * (2 - y)))
    (-(platformCenter a - x) / platformCrossingScale a x) x
  apply hsqrt.congr_deriv
  unfold platformCenter platformCrossingScale
  field_simp [hK0]
  ring

theorem hasDerivAt_platformRho
    {a x : ℝ} (hxa : x < a) (ha2 : a < 2) :
    HasDerivAt (platformRho a)
      (platformRho a x / platformCrossingScale a x) x := by
  let D : ℝ → ℝ := fun y ↦
    platformCenter a - y + platformCrossingScale a y
  have hK := hasDerivAt_platformCrossingScale hxa ha2
  have hD : HasDerivAt D
      (-1 - (platformCenter a - x) / platformCrossingScale a x) x := by
    have hraw :=
      ((hasDerivAt_const x (platformCenter a)).sub (hasDerivAt_id x)).add hK
    convert! hraw using 1
    ring
  have hK0 : platformCrossingScale a x ≠ 0 :=
    (platformCrossingScale_pos hxa ha2).ne'
  have hDpos : 0 < D x := by
    have hcenter : a < platformCenter a := by
      simp [platformCenter]
      linarith
    exact add_pos (sub_pos.mpr (hxa.trans hcenter))
      (platformCrossingScale_pos hxa ha2)
  have hDform :
      -1 - (platformCenter a - x) / platformCrossingScale a x =
        -(D x) / platformCrossingScale a x := by
    dsimp [D]
    field_simp [hK0]
    ring
  have hinv := hD.inv hDpos.ne'
  have hmul := (hasDerivAt_const x (platformRadius a)).mul hinv
  convert! hmul using 1
  · rw [hDform]
    simp only [zero_mul, zero_add]
    change platformRadius a / D x / platformCrossingScale a x =
      platformRadius a *
        (-(-(D x) / platformCrossingScale a x) / D x ^ 2)
    field_simp [hDpos.ne', hK0]

theorem hasDerivAt_log_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log |y|) (1 / x) x := by
  rcases hx.lt_or_gt with hneg | hpos
  · convert! (Real.hasDerivAt_log (abs_ne_zero.mpr hx)).comp x
      (hasDerivAt_abs_neg hneg) using 1
    rw [abs_of_neg hneg]
    field_simp
  · convert! (Real.hasDerivAt_log (abs_ne_zero.mpr hx)).comp x
      (hasDerivAt_abs_pos hpos) using 1
    rw [abs_of_pos hpos]
    simp [div_eq_mul_inv]

/-- `platformExteriorWx` is exactly the derivative of `platformExteriorW`
with respect to its exterior coordinate. -/
theorem hasDerivAt_platformExteriorW_x
    {k a x : ℝ} (hxa : x < a) (ha2 : a < 2) (hx0 : x ≠ 0)
    (hcorr : 1 -
      ((Real.sqrt 2 - Real.sqrt a) / (Real.sqrt 2 + Real.sqrt a)) *
        platformRho a x ≠ 0) :
    HasDerivAt (fun y ↦ platformExteriorW k a y)
      (platformExteriorWx k a x) x := by
  let K := platformCrossingScale a x
  let D : ℝ → ℝ := fun y ↦
    platformCenter a - y + platformCrossingScale a y
  let rho0 := (Real.sqrt 2 - Real.sqrt a) /
    (Real.sqrt 2 + Real.sqrt a)
  have hK := hasDerivAt_platformCrossingScale hxa ha2
  have hK0 : K ≠ 0 := (platformCrossingScale_pos hxa ha2).ne'
  have hD : HasDerivAt D (-D x / K) x := by
    have hraw :=
      ((hasDerivAt_const x (platformCenter a)).sub (hasDerivAt_id x)).add hK
    have hraw' : HasDerivAt D
        (-1 - (platformCenter a - x) / platformCrossingScale a x) x := by
      convert! hraw using 1
      ring
    apply hraw'.congr_deriv
    change -1 - (platformCenter a - x) / K =
      -(platformCenter a - x + K) / K
    field_simp [hK0]
    ring
  have hDpos : 0 < D x := by
    have hcenter : a < platformCenter a := by
      simp [platformCenter]
      linarith
    exact add_pos (sub_pos.mpr (hxa.trans hcenter))
      (platformCrossingScale_pos hxa ha2)
  have hlogD : HasDerivAt (fun y ↦ Real.log (D y / 2)) (-1 / K) x := by
    have hdiv := hD.div_const 2
    have hlog := hdiv.log (div_ne_zero hDpos.ne' (by norm_num))
    convert! hlog using 1
    field_simp [hDpos.ne', hK0]
  have hrho := hasDerivAt_platformRho hxa ha2
  have hcorrDeriv : HasDerivAt
      (fun y ↦ Real.log (1 - rho0 * platformRho a y))
      (-(rho0 * platformRho a x / K) /
        (1 - rho0 * platformRho a x)) x := by
    have hinside := (hasDerivAt_const x 1).sub
      ((hasDerivAt_const x rho0).mul hrho)
    have hlog := hinside.log (by simpa [rho0] using! hcorr)
    convert! hlog using 1
    dsimp [K]
    ring
  have htotal :=
    ((hasDerivAt_const x k).mul (hasDerivAt_log_abs hx0)).add hlogD |>.sub
      (((hasDerivAt_const x (2 * k)).mul hcorrDeriv))
  convert! htotal using 1
  · rw [platformExteriorWx_eq]
    have hcorr' : 1 - rho0 * platformRho a x ≠ 0 := by
      simpa [rho0] using! hcorr
    change k / x - 1 / K +
        2 * k * rho0 * platformRho a x /
          (K * (1 - rho0 * platformRho a x)) =
      0 * Real.log |x| + k * (1 / x) + -1 / K -
        (0 * Real.log (1 - rho0 * platformRho a x) +
          2 * k * (-(rho0 * platformRho a x / K) /
            (1 - rho0 * platformRho a x)))
    simp only [zero_mul, zero_add]
    field_simp [hx0, hK0, hcorr']
    ring

/-! ## Compact IVT stitching -/

/-- A jointly continuous family with an endpoint sign bracket and a unique
zero in every fibre has a unique continuous zero branch.  Compactness of the
two certified intervals upgrades the pointwise IVT roots to continuity; no
unrecorded choice of numerical roots is involved. -/
theorem existsUnique_continuous_zeroBranch
    {F : ℝ → ℝ → ℝ} {kLo kHi xLo xHi : ℝ}
    (hx : xLo ≤ xHi)
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2)
      (Icc kLo kHi ×ˢ Icc xLo xHi))
    (hbracket : ∀ k ∈ Icc kLo kHi,
      (F k xLo ≤ 0 ∧ 0 ≤ F k xHi) ∨
      (F k xHi ≤ 0 ∧ 0 ≤ F k xLo))
    (hinj : ∀ k ∈ Icc kLo kHi,
      InjOn (F k) (Icc xLo xHi)) :
    ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧
        ∀ k, root k ∈ Icc xLo xHi ∧ F k (root k) = 0 := by
  let Z : Set (ℝ × ℝ) :=
    (Icc kLo kHi ×ˢ Icc xLo xHi) ∩
      {p | F p.1 p.2 = 0}
  have hZcompact : IsCompact Z := by
    apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    · simpa [Z] using!
        (isClosed_Icc.prod isClosed_Icc).isClosed_eq hF continuousOn_const
    · intro p hp
      exact hp.1
  have hex : ∀ k : Icc kLo kHi,
      ∃ x ∈ Icc xLo xHi, F k x = 0 := by
    intro k
    have hc : ContinuousOn (fun x ↦ F k x) (Icc xLo xHi) :=
      hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun _ hxmem ↦ ⟨k.property, hxmem⟩)
    rcases hbracket k k.property with hsign | hsign
    · exact intermediate_value_Icc hx hc hsign
    · exact intermediate_value_Icc' hx hc hsign
  let proj : Z → Icc kLo kHi := fun z ↦
    ⟨z.1.1, by
      have hz := z.property
      exact hz.1.1⟩
  have hproj_cont : Continuous proj := by
    simpa [proj] using!
      (continuous_fst.comp continuous_subtype_val).subtype_mk
        (fun z : Z ↦ by exact z.property.1.1)
  have hproj_inj : Function.Injective proj := by
    intro z w hzw
    have hkzw : z.1.1 = w.1.1 := by
      exact congrArg Subtype.val hzw
    have hzK : z.1.1 ∈ Icc kLo kHi := z.property.1.1
    have hzX : z.1.2 ∈ Icc xLo xHi := z.property.1.2
    have hwX : w.1.2 ∈ Icc xLo xHi := w.property.1.2
    have hFx : F z.1.1 z.1.2 = F z.1.1 w.1.2 := by
      calc
        F z.1.1 z.1.2 = 0 := z.property.2
        _ = F z.1.1 w.1.2 := by
          rw [hkzw]
          exact w.property.2.symm
    have hxzw : z.1.2 = w.1.2 :=
      hinj z.1.1 hzK hzX hwX hFx
    apply Subtype.ext
    exact Prod.ext hkzw hxzw
  have hproj_surj : Function.Surjective proj := by
    intro k
    rcases hex k with ⟨x, hxmem, hzero⟩
    let z : Z := ⟨(k, x), ⟨⟨k.property, hxmem⟩, hzero⟩⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    rfl
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hZcompact
  have hhomeo : IsHomeomorph proj :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨hproj_cont, hproj_inj, hproj_surj⟩
  let H : Z ≃ₜ Icc kLo kHi := hhomeo.homeomorph proj
  let root : Icc kLo kHi → ℝ := fun k ↦ (H.symm k).1.2
  have hroot_cont : Continuous root := by
    exact continuous_snd.comp
      (continuous_subtype_val.comp H.symm.continuous)
  have hroot_spec : ∀ k, root k ∈ Icc xLo xHi ∧
      F k (root k) = 0 := by
    intro k
    have hcoord : (H.symm k).1.1 = k := by
      have happly := H.apply_symm_apply k
      exact congrArg Subtype.val happly
    constructor
    · exact (H.symm k).property.1.2
    · change F k (H.symm k).1.2 = 0
      rw [← hcoord]
      exact (H.symm k).property.2
  refine ⟨root, ⟨hroot_cont, hroot_spec⟩, ?_⟩
  intro other hother
  funext k
  exact (hinj k k.property (hroot_spec k).1 (hother.2 k).1 <|
    (hroot_spec k).2.trans (hother.2 k).2.symm).symm

/-- Endpoint-only implicit stitching.  The sign of `-F_k/F_x`, together with
the transverse sign, fixes the sign of `F_k`.  Hence one endpoint boundary
sign propagates forward in `k` and the other backward, yielding the uniform
IVT bracket used by `existsUnique_continuous_zeroBranch`. -/
theorem existsUnique_continuous_zeroBranch_of_endpointSlope
    {F Fx Fk : ℝ → ℝ → ℝ} {kLo kHi xLo xHi : ℝ}
    (side : PlatformCrossingSide)
    (orientation : PlatformSlopeOrientation)
    (hk : kLo ≤ kHi) (hx : xLo ≤ xHi)
    (hcontinuous : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2)
      (Icc kLo kHi ×ˢ Icc xLo xHi))
    (hFxDeriv : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      HasDerivAt (F k) (Fx k x) x)
    (hFkDeriv : ∀ x ∈ Icc xLo xHi, ∀ k ∈ Icc kLo kHi,
      HasDerivAt (fun t ↦ F t x) (Fk k x) k)
    (htransverse : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      TransverseHasSide side (Fx k x))
    (hslope : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      SlopeHasOrientation orientation (-(Fk k x / Fx k x)))
    (hatLo : WeakCrossingBracket side (F kLo) xLo xHi)
    (hatHi : WeakCrossingBracket side (F kHi) xLo xHi) :
    ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc xLo xHi ∧ F k (root k) = 0 := by
  have hparamMono (hFkPos : ∀ k ∈ Icc kLo kHi,
      ∀ x ∈ Icc xLo xHi, 0 < Fk k x) :
      ∀ x ∈ Icc xLo xHi, MonotoneOn (fun k ↦ F k x)
        (Icc kLo kHi) := by
    intro x hxmem
    have hslice : ContinuousOn (fun k ↦ F k x) (Icc kLo kHi) :=
      hcontinuous.comp (continuousOn_id.prodMk continuousOn_const)
        (fun _ hkmem ↦ ⟨hkmem, hxmem⟩)
    exact (strictMonoOn_of_deriv_pos (convex_Icc kLo kHi) hslice
      (fun k hkint ↦ by
        have hkmem : k ∈ Icc kLo kHi := interior_subset hkint
        rw [(hFkDeriv x hxmem k hkmem).deriv]
        exact hFkPos k hkmem x hxmem)).monotoneOn
  have hparamAnti (hFkNeg : ∀ k ∈ Icc kLo kHi,
      ∀ x ∈ Icc xLo xHi, Fk k x < 0) :
      ∀ x ∈ Icc xLo xHi, AntitoneOn (fun k ↦ F k x)
        (Icc kLo kHi) := by
    intro x hxmem
    have hslice : ContinuousOn (fun k ↦ F k x) (Icc kLo kHi) :=
      hcontinuous.comp (continuousOn_id.prodMk continuousOn_const)
        (fun _ hkmem ↦ ⟨hkmem, hxmem⟩)
    exact (strictAntiOn_of_deriv_neg (convex_Icc kLo kHi) hslice
      (fun k hkint ↦ by
        have hkmem : k ∈ Icc kLo kHi := interior_subset hkint
        rw [(hFkDeriv x hxmem k hkmem).deriv]
        exact hFkNeg k hkmem x hxmem)).antitoneOn
  have hinj : ∀ k ∈ Icc kLo kHi, InjOn (F k) (Icc xLo xHi) := by
    intro k hkmem
    have hslice : ContinuousOn (F k) (Icc xLo xHi) :=
      hcontinuous.comp (continuousOn_const.prodMk continuousOn_id)
        (fun _ hxmem ↦ ⟨hkmem, hxmem⟩)
    cases side with
    | minus =>
        exact (strictAntiOn_of_deriv_neg (convex_Icc xLo xHi) hslice
          (fun x hxint ↦ by
            have hxmem : x ∈ Icc xLo xHi := interior_subset hxint
            rw [(hFxDeriv k hkmem x hxmem).deriv]
            simpa [TransverseHasSide] using!
              htransverse k hkmem x hxmem)).injOn
    | plus =>
        exact (strictMonoOn_of_deriv_pos (convex_Icc xLo xHi) hslice
          (fun x hxint ↦ by
            have hxmem : x ∈ Icc xLo xHi := interior_subset hxint
            rw [(hFxDeriv k hkmem x hxmem).deriv]
            simpa [TransverseHasSide] using!
              htransverse k hkmem x hxmem)).injOn
  apply existsUnique_continuous_zeroBranch hx hcontinuous
  · intro k hkmem
    have hkLo : kLo ∈ Icc kLo kHi := left_mem_Icc.mpr hk
    have hkHi : kHi ∈ Icc kLo kHi := right_mem_Icc.mpr hk
    have hxLo : xLo ∈ Icc xLo xHi := left_mem_Icc.mpr hx
    have hxHi : xHi ∈ Icc xLo xHi := right_mem_Icc.mpr hx
    cases side with
    | minus =>
        change 0 ≤ F kLo xLo ∧ F kLo xHi ≤ 0 at hatLo
        change 0 ≤ F kHi xLo ∧ F kHi xHi ≤ 0 at hatHi
        cases orientation with
        | decreasing =>
            have hFkNeg : ∀ q ∈ Icc kLo kHi,
                ∀ x ∈ Icc xLo xHi, Fk q x < 0 := by
              intro q hq x hxmem
              have hs : -(Fk q x / Fx q x) < 0 := by
                simpa [SlopeHasOrientation] using! hslope q hq x hxmem
              have hs' : (-Fk q x) / Fx q x < 0 := by
                simpa only [neg_div] using! hs
              rcases (div_neg_iff.mp hs') with hcase | hcase
              · exact neg_pos.mp hcase.1
              · have hfx : Fx q x < 0 := by
                  simpa [TransverseHasSide] using!
                    htransverse q hq x hxmem
                exact False.elim ((not_lt_of_ge hfx.le) hcase.2)
            have hanti := hparamAnti hFkNeg
            exact Or.inr ⟨
              (hanti xHi hxHi hkLo hkmem hkmem.1).trans hatLo.2,
              hatHi.1.trans (hanti xLo hxLo hkmem hkHi hkmem.2)⟩
        | increasing =>
            have hFkPos : ∀ q ∈ Icc kLo kHi,
                ∀ x ∈ Icc xLo xHi, 0 < Fk q x := by
              intro q hq x hxmem
              have hs : 0 < -(Fk q x / Fx q x) := by
                simpa [SlopeHasOrientation] using! hslope q hq x hxmem
              have hs' : 0 < (-Fk q x) / Fx q x := by
                simpa only [neg_div] using! hs
              rcases (div_pos_iff.mp hs') with hcase | hcase
              · have hfx : Fx q x < 0 := by
                  simpa [TransverseHasSide] using!
                    htransverse q hq x hxmem
                exact False.elim ((not_lt_of_ge hfx.le) hcase.2)
              · linarith [hcase.1]
            have hmono := hparamMono hFkPos
            exact Or.inr ⟨
              (hmono xHi hxHi hkmem hkHi hkmem.2).trans hatHi.2,
              hatLo.1.trans (hmono xLo hxLo hkLo hkmem hkmem.1)⟩
    | plus =>
        change F kLo xLo ≤ 0 ∧ 0 ≤ F kLo xHi at hatLo
        change F kHi xLo ≤ 0 ∧ 0 ≤ F kHi xHi at hatHi
        cases orientation with
        | decreasing =>
            have hFkPos : ∀ q ∈ Icc kLo kHi,
                ∀ x ∈ Icc xLo xHi, 0 < Fk q x := by
              intro q hq x hxmem
              have hs : -(Fk q x / Fx q x) < 0 := by
                simpa [SlopeHasOrientation] using! hslope q hq x hxmem
              have hs' : (-Fk q x) / Fx q x < 0 := by
                simpa only [neg_div] using! hs
              rcases (div_neg_iff.mp hs') with hcase | hcase
              · have hfx : 0 < Fx q x := by
                  simpa [TransverseHasSide] using!
                    htransverse q hq x hxmem
                exact False.elim ((not_lt_of_ge hfx.le) hcase.2)
              · linarith [hcase.1]
            have hmono := hparamMono hFkPos
            exact Or.inl ⟨
              (hmono xLo hxLo hkmem hkHi hkmem.2).trans hatHi.1,
              hatLo.2.trans (hmono xHi hxHi hkLo hkmem hkmem.1)⟩
        | increasing =>
            have hFkNeg : ∀ q ∈ Icc kLo kHi,
                ∀ x ∈ Icc xLo xHi, Fk q x < 0 := by
              intro q hq x hxmem
              have hs : 0 < -(Fk q x / Fx q x) := by
                simpa [SlopeHasOrientation] using! hslope q hq x hxmem
              have hs' : 0 < (-Fk q x) / Fx q x := by
                simpa only [neg_div] using! hs
              rcases (div_pos_iff.mp hs') with hcase | hcase
              · exact neg_pos.mp hcase.1
              · have hfx : 0 < Fx q x := by
                  simpa [TransverseHasSide] using!
                    htransverse q hq x hxmem
                exact False.elim ((not_lt_of_ge hfx.le) hcase.2)
            have hanti := hparamAnti hFkNeg
            exact Or.inl ⟨
              (hanti xLo hxLo hkLo hkmem hkmem.1).trans hatLo.1,
              hatHi.2.trans (hanti xHi hxHi hkmem hkHi hkmem.2)⟩
  · exact hinj

theorem continuousOn_platformExteriorW_edge
    {edge : HighKPlatformEdge} {kLo kHi xLo xHi : ℝ}
    (ha0 : ∀ k ∈ Icc kLo kHi,
      0 < highKPlatformEdge edge k)
    (hxa : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      x < highKPlatformEdge edge k)
    (ha2 : ∀ k ∈ Icc kLo kHi,
      highKPlatformEdge edge k < 2)
    (hx0 : ∀ x ∈ Icc xLo xHi, x ≠ 0)
    (hcorr : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      1 - ((Real.sqrt 2 -
          Real.sqrt (highKPlatformEdge edge k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge k))) *
          platformRho (highKPlatformEdge edge k) x ≠ 0) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        platformExteriorW p.1 (highKPlatformEdge edge p.1) p.2)
      (Icc kLo kHi ×ˢ Icc xLo xHi) := by
  intro p hp
  let A : ℝ × ℝ → ℝ := fun q ↦ highKPlatformEdge edge q.1
  let X : ℝ × ℝ → ℝ := fun q ↦ q.2
  let K : ℝ × ℝ → ℝ := fun q ↦
    Real.sqrt ((A q - X q) * (2 - X q))
  let D : ℝ × ℝ → ℝ := fun q ↦
    platformCenter (A q) - X q + K q
  let R : ℝ × ℝ → ℝ := fun q ↦ platformRadius (A q)
  let rho : ℝ × ℝ → ℝ := fun q ↦ R q / D q
  let rho0 : ℝ × ℝ → ℝ := fun q ↦
    (Real.sqrt 2 - Real.sqrt (A q)) /
      (Real.sqrt 2 + Real.sqrt (A q))
  have hA : ContinuousAt A p := by
    cases edge <;> simp [A, highKPlatformEdge] <;> fun_prop
  have hX : ContinuousAt X p := by
    exact continuous_snd.continuousAt
  have hK : ContinuousAt K p := by
    exact ((hA.sub hX).mul (continuousAt_const.sub hX)).sqrt
  have hcenter : ContinuousAt (fun q ↦ platformCenter (A q)) p := by
    unfold platformCenter
    fun_prop
  have hD : ContinuousAt D p := by
    exact (hcenter.sub hX).add hK
  have hradius : ContinuousAt R p := by
    unfold R platformRadius
    fun_prop
  have hDpos : 0 < D p := by
    have hcenter_gt : A p < platformCenter (A p) := by
      simp [platformCenter]
      linarith [ha2 p.1 hp.1]
    have hKpos : 0 < K p := by
      exact Real.sqrt_pos.2 <| mul_pos
        (sub_pos.mpr (hxa p.1 hp.1 p.2 hp.2))
        (sub_pos.mpr ((hxa p.1 hp.1 p.2 hp.2).trans (ha2 p.1 hp.1)))
    exact add_pos (sub_pos.mpr
      ((hxa p.1 hp.1 p.2 hp.2).trans hcenter_gt)) hKpos
  have hrho : ContinuousAt rho p :=
    hradius.div hD hDpos.ne'
  have hsqrtA : ContinuousAt (fun q ↦ Real.sqrt (A q)) p := hA.sqrt
  have hsqrtTwo : ContinuousAt (fun _ : ℝ × ℝ ↦ Real.sqrt 2) p :=
    continuousAt_const
  have hsqrtDen : Real.sqrt 2 + Real.sqrt (A p) ≠ 0 := by
    exact (add_pos (Real.sqrt_pos.2 (by norm_num))
      (Real.sqrt_pos.2 (ha0 p.1 hp.1))).ne'
  have hrho0 : ContinuousAt rho0 p := by
    exact (hsqrtTwo.sub hsqrtA).div (hsqrtTwo.add hsqrtA) hsqrtDen
  have hlogAbs : ContinuousAt (fun q ↦ Real.log |X q|) p :=
    hX.abs.log (abs_ne_zero.mpr (hx0 p.2 hp.2))
  have hlogD : ContinuousAt (fun q ↦ Real.log (D q / 2)) p :=
    (hD.div_const 2).log (div_ne_zero hDpos.ne' (by norm_num))
  have hcorr' : 1 - rho0 p * rho p ≠ 0 := by
    simpa [rho0, rho, R, D, K, A, X, platformRho,
      platformCrossingScale] using! hcorr p.1 hp.1 p.2 hp.2
  have hlogCorr : ContinuousAt
      (fun q ↦ Real.log (1 - rho0 q * rho q)) p :=
    (continuousAt_const.sub (hrho0.mul hrho)).log hcorr'
  have htwoK : ContinuousAt (fun q : ℝ × ℝ ↦ 2 * q.1) p :=
    continuousAt_const.mul continuous_fst.continuousAt
  have htotal : ContinuousAt
      (fun q ↦ q.1 * Real.log |X q| + Real.log (D q / 2) -
        (2 * q.1) * Real.log (1 - rho0 q * rho q)) p :=
    (continuous_fst.continuousAt.mul hlogAbs).add hlogD |>.sub
      (htwoK.mul hlogCorr)
  have hfinal : ContinuousAt
      (fun q : ℝ × ℝ ↦
        platformExteriorW q.1 (highKPlatformEdge edge q.1) q.2) p := by
    simpa [platformExteriorW, platformCrossingScale, platformRho,
      A, X, K, D, R, rho, rho0] using! htotal
  exact hfinal.continuousWithinAt

/-- A `PlatformCrossingBranchCertificate` with its rational boxes tied to the
stated slab data yields the global continuous branch directly from its two
endpoint brackets, uniform `W_x` sign, and uniform implicit-slope sign. -/
theorem PlatformCrossingBranchCertificate.existsUnique_continuous_crossing
    {logTerms sqrtSteps : ℕ} {edge : HighKPlatformEdge}
    {side : PlatformCrossingSide}
    (cert : PlatformCrossingBranchCertificate
      logTerms sqrtSteps edge side)
    {kLo kHi xLo xHi other ell pi : ℝ}
    (hk : kLo ≤ kHi) (hx : xLo ≤ xHi)
    (hatLoLeft : ∀ i, (cert.atLoLeft i).Contains
      (crossingEnvironment side kLo xLo other ell pi i))
    (hatLoRight : ∀ i, (cert.atLoRight i).Contains
      (crossingEnvironment side kLo xHi other ell pi i))
    (hatHiLeft : ∀ i, (cert.atHiLeft i).Contains
      (crossingEnvironment side kHi xLo other ell pi i))
    (hatHiRight : ∀ i, (cert.atHiRight i).Contains
      (crossingEnvironment side kHi xHi other ell pi i))
    (henvelope : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi, ∀ i,
      (cert.envelope i).Contains
        (crossingEnvironment side k x other ell pi i))
    (hcoordinate : ∀ x ∈ Icc xLo xHi,
      CrossingCoordinateHasSide side x)
    (ha0 : ∀ k ∈ Icc kLo kHi,
      0 < highKPlatformEdge edge k)
    (hxa : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      x < highKPlatformEdge edge k)
    (ha2 : ∀ k ∈ Icc kLo kHi,
      highKPlatformEdge edge k < 2)
    (hcorr : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      1 - ((Real.sqrt 2 -
          Real.sqrt (highKPlatformEdge edge k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge k))) *
          platformRho (highKPlatformEdge edge k) x ≠ 0)
    (hdom : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      DiffDomain (crossingEnvironment side k x other ell pi)
        (crossingWE logTerms sqrtSteps edge side)) :
    ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc xLo xHi ∧
          platformExteriorW k (highKPlatformEdge edge k) (root k) = 0 := by
  let F : ℝ → ℝ → ℝ := fun k x ↦
    platformExteriorW k (highKPlatformEdge edge k) x
  let Fx : ℝ → ℝ → ℝ := fun k x ↦
    platformExteriorWx k (highKPlatformEdge edge k) x
  let Fk : ℝ → ℝ → ℝ := fun k x ↦
    evalReal (crossingEnvironment side k x other ell pi)
      (diffExpr 0 (crossingWE logTerms sqrtSteps edge side))
  have hx0 : ∀ x ∈ Icc xLo xHi, x ≠ 0 := by
    intro x hxmem hxzero
    subst x
    have hs := hcoordinate 0 hxmem
    cases side <;> simp [CrossingCoordinateHasSide] at hs
  have hstitch : ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc xLo xHi ∧ F k (root k) = 0 := by
    apply existsUnique_continuous_zeroBranch_of_endpointSlope
      (F := F) (Fx := Fx) (Fk := Fk) side cert.orientation hk hx
    · exact continuousOn_platformExteriorW_edge ha0 hxa ha2 hx0 hcorr
    · intro k hkmem x hxmem
      simpa [F, Fx] using! hasDerivAt_platformExteriorW_x
        (hxa k hkmem x hxmem) (ha2 k hkmem) (hx0 x hxmem)
        (hcorr k hkmem x hxmem)
    · intro x hxmem k hkmem
      simpa [F, Fk] using! hasDerivAt_platformExteriorW_alongEdge
        logTerms sqrtSteps edge side (hcoordinate x hxmem)
        (hdom k hkmem x hxmem)
    · intro k hkmem x hxmem
      simpa [Fx] using! cert.transverse_hasSide
        (henvelope k hkmem x hxmem)
    · intro k hkmem x hxmem
      have hs := cert.actualSlope_hasOrientation
        (henvelope k hkmem x hxmem) (hcoordinate x hxmem)
        (hdom k hkmem x hxmem)
      have hd := hasDerivAt_platformExteriorW_alongEdge
        logTerms sqrtSteps edge side (hcoordinate x hxmem)
        (hdom k hkmem x hxmem)
      rw [hd.deriv] at hs
      simpa [Fk, Fx] using! hs
    · simpa [F] using! cert.weakBracket_atLo
        hatLoLeft hatLoRight (hcoordinate xLo (left_mem_Icc.mpr hx))
          (hcoordinate xHi (right_mem_Icc.mpr hx))
    · simpa [F] using! cert.weakBracket_atHi
        hatHiLeft hatHiRight (hcoordinate xLo (left_mem_Icc.mpr hx))
          (hcoordinate xHi (right_mem_Icc.mpr hx))
  simpa [F] using! hstitch

/-- Platform specialization of compact IVT stitching.  A uniform checked
sign for `platformExteriorWx` makes every fibre strictly monotone, so the
pointwise bracketed roots form one and only one continuous crossing branch. -/
theorem existsUnique_continuous_platformCrossing
    {edge : HighKPlatformEdge} {kLo kHi xLo xHi : ℝ}
    (hx : xLo ≤ xHi)
    (hcontinuous : ContinuousOn
      (fun p : ℝ × ℝ ↦
        platformExteriorW p.1 (highKPlatformEdge edge p.1) p.2)
      (Icc kLo kHi ×ˢ Icc xLo xHi))
    (hbracket : ∀ k ∈ Icc kLo kHi,
      (platformExteriorW k (highKPlatformEdge edge k) xLo ≤ 0 ∧
          0 ≤ platformExteriorW k (highKPlatformEdge edge k) xHi) ∨
      (platformExteriorW k (highKPlatformEdge edge k) xHi ≤ 0 ∧
          0 ≤ platformExteriorW k (highKPlatformEdge edge k) xLo))
    (hxa : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      x < highKPlatformEdge edge k)
    (ha2 : ∀ k ∈ Icc kLo kHi,
      highKPlatformEdge edge k < 2)
    (hx0 : ∀ x ∈ Icc xLo xHi, x ≠ 0)
    (hcorr : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      1 - ((Real.sqrt 2 -
          Real.sqrt (highKPlatformEdge edge k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge k))) *
          platformRho (highKPlatformEdge edge k) x ≠ 0)
    (hwx :
      (∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
        0 < platformExteriorWx k (highKPlatformEdge edge k) x) ∨
      (∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
        platformExteriorWx k (highKPlatformEdge edge k) x < 0)) :
    ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧
        ∀ k, root k ∈ Icc xLo xHi ∧
          platformExteriorW k (highKPlatformEdge edge k) (root k) = 0 := by
  apply existsUnique_continuous_zeroBranch hx hcontinuous hbracket
  intro k hk
  have hslice : ContinuousOn
      (fun x ↦ platformExteriorW k (highKPlatformEdge edge k) x)
      (Icc xLo xHi) :=
    hcontinuous.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ hxmem ↦ ⟨hk, hxmem⟩)
  rcases hwx with hpos | hneg
  · exact (strictMonoOn_of_deriv_pos (convex_Icc xLo xHi) hslice
      (fun x hxint ↦ by
        have hxmem : x ∈ Icc xLo xHi := interior_subset hxint
        rw [(hasDerivAt_platformExteriorW_x
          (hxa k hk x hxmem) (ha2 k hk) (hx0 x hxmem)
          (hcorr k hk x hxmem)).deriv]
        exact hpos k hk x hxmem)).injOn
  · exact (strictAntiOn_of_deriv_neg (convex_Icc xLo xHi) hslice
      (fun x hxint ↦ by
        have hxmem : x ∈ Icc xLo xHi := interior_subset hxint
        rw [(hasDerivAt_platformExteriorW_x
          (hxa k hk x hxmem) (ha2 k hk) (hx0 x hxmem)
          (hcorr k hk x hxmem)).deriv]
        exact hneg k hk x hxmem)).injOn

theorem existsUnique_continuous_platformCrossing_of_bounds
    {edge : HighKPlatformEdge} {kLo kHi xLo xHi : ℝ}
    (hx : xLo ≤ xHi)
    (hbracket : ∀ k ∈ Icc kLo kHi,
      (platformExteriorW k (highKPlatformEdge edge k) xLo ≤ 0 ∧
          0 ≤ platformExteriorW k (highKPlatformEdge edge k) xHi) ∨
      (platformExteriorW k (highKPlatformEdge edge k) xHi ≤ 0 ∧
          0 ≤ platformExteriorW k (highKPlatformEdge edge k) xLo))
    (ha0 : ∀ k ∈ Icc kLo kHi,
      0 < highKPlatformEdge edge k)
    (hxa : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      x < highKPlatformEdge edge k)
    (ha2 : ∀ k ∈ Icc kLo kHi,
      highKPlatformEdge edge k < 2)
    (hx0 : ∀ x ∈ Icc xLo xHi, x ≠ 0)
    (hcorr : ∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
      1 - ((Real.sqrt 2 -
          Real.sqrt (highKPlatformEdge edge k)) /
        (Real.sqrt 2 + Real.sqrt (highKPlatformEdge edge k))) *
          platformRho (highKPlatformEdge edge k) x ≠ 0)
    (hwx :
      (∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
        0 < platformExteriorWx k (highKPlatformEdge edge k) x) ∨
      (∀ k ∈ Icc kLo kHi, ∀ x ∈ Icc xLo xHi,
        platformExteriorWx k (highKPlatformEdge edge k) x < 0)) :
    ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧
        ∀ k, root k ∈ Icc xLo xHi ∧
          platformExteriorW k (highKPlatformEdge edge k) (root k) = 0 :=
  existsUnique_continuous_platformCrossing hx
    (continuousOn_platformExteriorW_edge ha0 hxa ha2 hx0 hcorr)
    hbracket hxa ha2 hx0 hcorr hwx

/-- The two stitched exterior zeroes, bundled in the form consumed by the
platform calibration layer. -/
structure ContinuousPlatformCrossingPair
    (edge : HighKPlatformEdge)
    (kLo kHi xmLo xmHi xpLo xpHi : ℝ) where
  xMinus : Icc kLo kHi → ℝ
  xPlus : Icc kLo kHi → ℝ
  continuous_xMinus : Continuous xMinus
  continuous_xPlus : Continuous xPlus
  xMinus_mem : ∀ k, xMinus k ∈ Icc xmLo xmHi
  xPlus_mem : ∀ k, xPlus k ∈ Icc xpLo xpHi
  xMinus_zero : ∀ k : Icc kLo kHi,
    platformExteriorW k (highKPlatformEdge edge k) (xMinus k) = 0
  xPlus_zero : ∀ k : Icc kLo kHi,
    platformExteriorW k (highKPlatformEdge edge k) (xPlus k) = 0

theorem exists_crossingPair_of_uniqueBranches
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi : ℝ}
    (hminus : ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc xmLo xmHi ∧
          platformExteriorW k (highKPlatformEdge edge k) (root k) = 0)
    (hplus : ∃! root : Icc kLo kHi → ℝ,
      Continuous root ∧ ∀ k,
        root k ∈ Icc xpLo xpHi ∧
          platformExteriorW k (highKPlatformEdge edge k) (root k) = 0) :
    Nonempty (ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi) := by
  rcases hminus with ⟨xMinus, hxMinus, _⟩
  rcases hplus with ⟨xPlus, hxPlus, _⟩
  exact ⟨{
    xMinus := xMinus
    xPlus := xPlus
    continuous_xMinus := hxMinus.1
    continuous_xPlus := hxPlus.1
    xMinus_mem := fun k ↦ (hxMinus.2 k).1
    xPlus_mem := fun k ↦ (hxPlus.2 k).1
    xMinus_zero := fun k ↦ (hxMinus.2 k).2
    xPlus_zero := fun k ↦ (hxPlus.2 k).2
  }⟩

/-- Substitute a stitched crossing pair into the exact constant-edge scalar
certificate at every parameter in the slab. -/
theorem platformConstantEdgeCalibration_along_crossingPair_of_interval
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi ell : ℝ}
    {X : Fin 5 → RatInterval}
    {logTerms sqrtSteps trigDoubles N : ℕ} {qCap rCap : Rat}
    (branches : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (hordered : ∀ i, (X i).Ordered)
    (hkContains : ∀ k : Icc kLo kHi, (X 0).Contains k)
    (hxmContains : ∀ x ∈ Icc xmLo xmHi, (X 1).Contains x)
    (hxpContains : ∀ x ∈ Icc xpLo xpHi, (X 2).Contains x)
    (hellContains : (X 3).Contains ell)
    (hpiContains : (X 4).Contains Real.pi)
    (hxmEdge : ∀ k, branches.xMinus k < highKPlatformEdge edge k)
    (hxpEdge : ∀ k, branches.xPlus k < highKPlatformEdge edge k)
    (ha2 : ∀ k : Icc kLo kHi, highKPlatformEdge edge k < 2)
    (hN : 0 < N)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hendpoint : EvalPositive X
      (constantEndpointLowerE logTerms sqrtSteps trigDoubles N
        edge qCap rCap)) :
    ∀ k : Icc kLo kHi,
      PlatformConstantEdgeCalibration k (highKPlatformEdge edge k)
        (branches.xMinus k) (branches.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (branches.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (branches.xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge edge k)
          (branches.xMinus k) (branches.xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge edge k)
            (branches.xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge edge k)
            (branches.xPlus k))) := by
  intro k
  have hcontains : ∀ i,
      (X i).Contains
        (![(k : ℝ), branches.xMinus k, branches.xPlus k, ell, Real.pi] i) := by
    intro i
    fin_cases i
    · exact hkContains k
    · exact hxmContains _ (branches.xMinus_mem k)
    · exact hxpContains _ (branches.xPlus_mem k)
    · exact hellContains
    · exact hpiContains
  exact platformConstantEdgeCalibration_of_interval hordered hcontains
    (hxmEdge k) (hxpEdge k) (ha2 k) hN
    hqCapPos hqCapPi hrCapPos hrCapPi haPi hQmax hRmax
    hQcap hRcap hCeff hendpoint

/-- Affine-edge counterpart of
`platformConstantEdgeCalibration_along_crossingPair_of_interval`. -/
theorem platformAffineCalibration_along_crossingPair_of_interval
    {edge : HighKPlatformEdge}
    {kLo kHi xmLo xmHi xpLo xpHi ell : ℝ}
    {X : Fin 5 → RatInterval}
    {logTerms sqrtSteps trigDoubles N : ℕ} {qCap rCap : Rat}
    (branches : ContinuousPlatformCrossingPair edge
      kLo kHi xmLo xmHi xpLo xpHi)
    (hordered : ∀ i, (X i).Ordered)
    (hkContains : ∀ k : Icc kLo kHi, (X 0).Contains k)
    (hxmContains : ∀ x ∈ Icc xmLo xmHi, (X 1).Contains x)
    (hxpContains : ∀ x ∈ Icc xpLo xpHi, (X 2).Contains x)
    (hellContains : (X 3).Contains ell)
    (hpiContains : (X 4).Contains Real.pi)
    (hxmEdge : ∀ k, branches.xMinus k < highKPlatformEdge edge k)
    (hxpEdge : ∀ k, branches.xPlus k < highKPlatformEdge edge k)
    (ha2 : ∀ k : Icc kLo kHi, highKPlatformEdge edge k < 2)
    (hN : 0 < N)
    (hqCapPos : 0 < (qCap : ℝ)) (hqCapPi : (qCap : ℝ) ≤ Real.pi)
    (hrCapPos : 0 < (rCap : ℝ)) (hrCapPi : (rCap : ℝ) ≤ Real.pi)
    (haPi : EvalPositive X (apiE sqrtSteps edge))
    (hQmax : EvalPositive X (qmaxE sqrtSteps edge))
    (hRmax : EvalPositive X (rmaxE sqrtSteps edge))
    (hRltQ : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (qmaxE sqrtSteps edge)))
    (hQcap : EvalNegative X
      (.sub (qmaxE sqrtSteps edge) (.rat qCap)))
    (hRcap : EvalNegative X
      (.sub (rmaxE sqrtSteps edge) (.rat rCap)))
    (hCeff : EvalNegative X (ceffE logTerms sqrtSteps edge))
    (hleft : EvalPositive X
      (affineLeftLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hcorner : EvalPositive X
      (affineCornerLowerE logTerms sqrtSteps trigDoubles N edge qCap rCap))
    (hderivative : AffineDerivativeBoxCertificate X
      logTerms sqrtSteps trigDoubles edge) :
    ∀ k : Icc kLo kHi,
      PlatformAffineCalibration k (highKPlatformEdge edge k)
        (branches.xMinus k) (branches.xPlus k)
        (-1 / platformExteriorWx k (highKPlatformEdge edge k)
          (branches.xMinus k))
        (1 / platformExteriorWx k (highKPlatformEdge edge k)
          (branches.xPlus k))
        (platformEffectiveConstant ell k (highKPlatformEdge edge k)
          (branches.xMinus k) (branches.xPlus k)
          (-1 / platformExteriorWx k (highKPlatformEdge edge k)
            (branches.xMinus k))
          (1 / platformExteriorWx k (highKPlatformEdge edge k)
            (branches.xPlus k))) := by
  intro k
  have hcontains : ∀ i,
      (X i).Contains
        (![(k : ℝ), branches.xMinus k, branches.xPlus k, ell, Real.pi] i) := by
    intro i
    fin_cases i
    · exact hkContains k
    · exact hxmContains _ (branches.xMinus_mem k)
    · exact hxpContains _ (branches.xPlus_mem k)
    · exact hellContains
    · exact hpiContains
  exact platformAffineCalibration_of_interval hordered hcontains
    (hxmEdge k) (hxpEdge k) (ha2 k) hN
    hqCapPos hqCapPi hrCapPos hrCapPi haPi hQmax hRmax hRltQ
    hQcap hRcap hCeff hleft hcorner hderivative

end HighKPlatformFormula

end

end Erdos1038
