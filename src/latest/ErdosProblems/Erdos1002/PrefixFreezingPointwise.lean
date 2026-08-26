import ErdosProblems.Erdos1002.OscillatoryIntervalSum
import Mathlib.Data.Finset.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pointwise error when a finite rare-event prefix is frozen

The late marked-Poisson argument freezes both its phase and finitely many
real value coordinates at a representative of a deep continued-fraction
cylinder.  This file proves the deterministic pointwise inequality behind
that step.  If every value coordinate moves by at most `eta`, then changing
an interval indicator can happen only in an `eta`-strip about one of the two
endpoints.  The proof keeps the absolute value inside the later tuple sum
and does not appeal to an informal telescoping assertion.
-/

open Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The unit-modulus phase is Lipschitz in its spatial variable, with the
exact derivative constant `2π|K|`. -/
theorem norm_oscillatoryPhase_sub_le
    (K x y : ℝ) :
    ‖oscillatoryPhase K x - oscillatoryPhase K y‖ ≤
      2 * Real.pi * |K| * |x - y| := by
  let u : ℝ := 2 * Real.pi * K * (x - y)
  have hfactor :
      oscillatoryPhase K x - oscillatoryPhase K y =
        oscillatoryPhase K y *
          (Complex.exp (Complex.I * (u : ℂ)) - 1) := by
    unfold oscillatoryPhase
    rw [mul_sub]
    have hexpAdd :
        Complex.exp (((2 * Real.pi * K * x : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((2 * Real.pi * K * y : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (u : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [u]
      push_cast
      ring
    rw [hexpAdd]
    ring
  rw [hfactor, norm_mul]
  have hunit : ‖oscillatoryPhase K y‖ = 1 := by
    unfold oscillatoryPhase
    rw [Complex.norm_exp]
    simp
  rw [hunit, one_mul]
  calc
    ‖Complex.exp (Complex.I * (u : ℂ)) - 1‖ ≤ ‖u‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |K| * |x - y| := by
      dsimp [u]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_pos Real.pi_pos]

/-- The oscillatory phase has unit norm. -/
theorem norm_oscillatoryPhase (K x : ℝ) :
    ‖oscillatoryPhase K x‖ = 1 := by
  unfold oscillatoryPhase
  rw [Complex.norm_exp]
  simp

/-- Closed enlargement `[a-η,b+η]` of `[a,b]`. -/
def closedIntervalEnlargement (a b eta : ℝ) : Set ℝ :=
  Icc (a - eta) (b + eta)

/-- The union of the two closed `eta`-strips around the endpoints of
`[a,b]`. -/
def closedIntervalBoundaryStrip (a b eta : ℝ) : Set ℝ :=
  Icc (a - eta) (a + eta) ∪ Icc (b - eta) (b + eta)

/-- A point within `eta` of a point of `[a,b]` lies in the closed
enlargement. -/
theorem mem_closedIntervalEnlargement_of_abs_sub_le
    {a b x y eta : ℝ}
    (hy : y ∈ Icc a b) (hxy : |x - y| ≤ eta) :
    x ∈ closedIntervalEnlargement a b eta := by
  have hbounds := abs_le.mp hxy
  constructor <;> linarith [hy.1, hy.2]

/-- If two `eta`-close points disagree about membership in `[a,b]`, then
the first point belongs to an endpoint strip. -/
theorem mem_closedIntervalBoundaryStrip_of_membership_ne
    {a b x y eta : ℝ} (heta : 0 ≤ eta)
    (hxy : |x - y| ≤ eta)
    (hne : (x ∈ Icc a b) ≠ (y ∈ Icc a b)) :
    x ∈ closedIntervalBoundaryStrip a b eta := by
  have hbounds := abs_le.mp hxy
  by_cases hx : x ∈ Icc a b
  · have hy : y ∉ Icc a b := fun hy ↦ hne (propext ⟨fun _ ↦ hy, fun _ ↦ hx⟩)
    rw [mem_Icc, not_and_or] at hy
    rcases hy with hy | hy
    · left
      constructor <;> linarith [hx.1, hy]
    · right
      constructor <;> linarith [hx.2, hy]
  · have hy : y ∈ Icc a b := by
      by_contra hyn
      exact hne (propext ⟨fun h ↦ (hx h).elim, fun h ↦ (hyn h).elim⟩)
    rw [mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · left
      constructor <;> linarith [hy.1]
    · right
      constructor <;> linarith [hy.2]

/-- Real `0`--`1` indicator of a closed interval. -/
def closedIntervalIndicator (a b x : ℝ) : ℝ :=
  if x ∈ Icc a b then 1 else 0

/-- Product of a finite family of closed-interval indicators. -/
def closedIntervalIndicatorProduct {r : ℕ}
    (a b x : Fin r → ℝ) : ℝ :=
  ∏ i, closedIntervalIndicator (a i) (b i) (x i)

/-- Indicator of the endpoint strip used in the freezing error. -/
def closedIntervalBoundaryIndicator (a b eta x : ℝ) : ℝ :=
  by
    classical
    exact if x ∈ closedIntervalBoundaryStrip a b eta then 1 else 0

private theorem closedIntervalIndicatorProduct_eq_one
    {r : ℕ} {a b x : Fin r → ℝ}
    (h : ∀ i, x i ∈ Icc (a i) (b i)) :
    closedIntervalIndicatorProduct a b x = 1 := by
  apply Finset.prod_eq_one
  intro i _hi
  simp [closedIntervalIndicator, h i]

private theorem closedIntervalIndicatorProduct_eq_zero
    {r : ℕ} {a b x : Fin r → ℝ}
    {i : Fin r} (h : x i ∉ Icc (a i) (b i)) :
    closedIntervalIndicatorProduct a b x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [closedIntervalIndicator, h]

private theorem closedIntervalIndicator_nonneg (a b x : ℝ) :
    0 ≤ closedIntervalIndicator a b x := by
  simp only [closedIntervalIndicator]
  split <;> positivity

private theorem closedIntervalBoundaryIndicator_nonneg
    (a b eta x : ℝ) :
    0 ≤ closedIntervalBoundaryIndicator a b eta x := by
  simp only [closedIntervalBoundaryIndicator]
  split <;> positivity

private theorem closedIntervalIndicatorProduct_nonneg
    {r : ℕ} (a b x : Fin r → ℝ) :
    0 ≤ closedIntervalIndicatorProduct a b x := by
  exact Finset.prod_nonneg fun i _hi ↦
    closedIntervalIndicator_nonneg (a i) (b i) (x i)

/--
The pointwise prefix-freezing inequality.

The first term is the phase-freezing error on the enlarged value windows.
Every remaining term has one endpoint-boundary strip and enlarged windows
in all other coordinates.  This is the precise deterministic content of
the manuscript's pointwise estimate before probabilities are summed.
-/
theorem norm_phase_mul_intervalProducts_sub_le_freezingError
    {r : ℕ} (a b x y : Fin r → ℝ)
    (phase frozenPhase : ℂ) {delta eta : ℝ}
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hphase : ‖phase‖ ≤ 1) (hfrozenPhase : ‖frozenPhase‖ ≤ 1)
    (hphaseDiff : ‖phase - frozenPhase‖ ≤ delta)
    (hxy : ∀ i, |x i - y i| ≤ eta) :
    ‖phase * (closedIntervalIndicatorProduct a b x : ℂ) -
        frozenPhase * (closedIntervalIndicatorProduct a b y : ℂ)‖ ≤
      delta * closedIntervalIndicatorProduct
        (fun i ↦ a i - eta) (fun i ↦ b i + eta) x +
      ∑ i,
        closedIntervalBoundaryIndicator (a i) (b i) eta (x i) *
          ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
            closedIntervalIndicator (a j - eta) (b j + eta) (x j) := by
  classical
  by_cases hxall : ∀ i, x i ∈ Icc (a i) (b i)
  · by_cases hyall : ∀ i, y i ∈ Icc (a i) (b i)
    · rw [closedIntervalIndicatorProduct_eq_one hxall,
        closedIntervalIndicatorProduct_eq_one hyall]
      norm_num only [Complex.ofReal_one, mul_one]
      have henlarged : ∀ i,
          x i ∈ Icc (a i - eta) (b i + eta) := by
        intro i
        exact mem_closedIntervalEnlargement_of_abs_sub_le (hxall i)
          (by simpa using! (show |x i - x i| ≤ eta by simp [heta]))
      rw [closedIntervalIndicatorProduct_eq_one henlarged, mul_one]
      exact hphaseDiff.trans (le_add_of_nonneg_right <|
        Finset.sum_nonneg fun i _hi ↦
          mul_nonneg (closedIntervalBoundaryIndicator_nonneg _ _ _ _)
            (Finset.prod_nonneg fun j _hj ↦
              closedIntervalIndicator_nonneg _ _ _))
    · push_neg at hyall
      obtain ⟨i, hyi⟩ := hyall
      rw [closedIntervalIndicatorProduct_eq_one hxall,
        closedIntervalIndicatorProduct_eq_zero hyi]
      norm_num only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
        sub_zero]
      have hboundary :
          x i ∈ closedIntervalBoundaryStrip (a i) (b i) eta := by
        apply mem_closedIntervalBoundaryStrip_of_membership_ne heta (hxy i)
        intro heq
        exact hyi (heq.mp (hxall i))
      have herase : ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
          closedIntervalIndicator (a j - eta) (b j + eta) (x j) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        have hxj := hxall j
        have hmem : x j ∈ Icc (a j - eta) (b j + eta) := by
          exact mem_closedIntervalEnlargement_of_abs_sub_le hxj
            (by simpa using! (show |x j - x j| ≤ eta by simp [heta]))
        simp [closedIntervalIndicator, hmem]
      have hterm :
          closedIntervalBoundaryIndicator (a i) (b i) eta (x i) *
              ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
                closedIntervalIndicator (a j - eta) (b j + eta) (x j) = 1 := by
        simp [closedIntervalBoundaryIndicator, hboundary, herase]
      let boundaryTerm : Fin r → ℝ := fun j ↦
        closedIntervalBoundaryIndicator (a j) (b j) eta (x j) *
          ∏ k ∈ (Finset.univ : Finset (Fin r)).erase j,
            closedIntervalIndicator (a k - eta) (b k + eta) (x k)
      have hterm' : boundaryTerm i = 1 := by
        exact hterm
      have htermNonneg : ∀ j ∈ (Finset.univ : Finset (Fin r)),
          0 ≤ boundaryTerm j := by
        intro j _hj
        exact mul_nonneg
          (closedIntervalBoundaryIndicator_nonneg _ _ _ _)
          (Finset.prod_nonneg fun k _hk ↦
            closedIntervalIndicator_nonneg _ _ _)
      have hsumOne : 1 ≤
          ∑ j,
            closedIntervalBoundaryIndicator (a j) (b j) eta (x j) *
              ∏ k ∈ (Finset.univ : Finset (Fin r)).erase j,
                closedIntervalIndicator (a k - eta) (b k + eta) (x k) := by
        change 1 ≤ ∑ j, boundaryTerm j
        rw [← hterm']
        exact Finset.single_le_sum htermNonneg (Finset.mem_univ i)
      exact hphase.trans <| hsumOne.trans <|
        le_add_of_nonneg_left (mul_nonneg hdelta
          (closedIntervalIndicatorProduct_nonneg _ _ _))
  · by_cases hyall : ∀ i, y i ∈ Icc (a i) (b i)
    · push_neg at hxall
      obtain ⟨i, hxi⟩ := hxall
      rw [closedIntervalIndicatorProduct_eq_zero hxi,
        closedIntervalIndicatorProduct_eq_one hyall]
      norm_num only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
        zero_sub, norm_neg]
      have hboundary :
          x i ∈ closedIntervalBoundaryStrip (a i) (b i) eta := by
        apply mem_closedIntervalBoundaryStrip_of_membership_ne heta (hxy i)
        intro heq
        exact hxi (heq.mpr (hyall i))
      have herase : ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
          closedIntervalIndicator (a j - eta) (b j + eta) (x j) = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        have hmem : x j ∈ Icc (a j - eta) (b j + eta) :=
          mem_closedIntervalEnlargement_of_abs_sub_le (hyall j) (hxy j)
        simp [closedIntervalIndicator, hmem]
      have hterm :
          closedIntervalBoundaryIndicator (a i) (b i) eta (x i) *
              ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
                closedIntervalIndicator (a j - eta) (b j + eta) (x j) = 1 := by
        simp [closedIntervalBoundaryIndicator, hboundary, herase]
      let boundaryTerm : Fin r → ℝ := fun j ↦
        closedIntervalBoundaryIndicator (a j) (b j) eta (x j) *
          ∏ k ∈ (Finset.univ : Finset (Fin r)).erase j,
            closedIntervalIndicator (a k - eta) (b k + eta) (x k)
      have hterm' : boundaryTerm i = 1 := by
        exact hterm
      have htermNonneg : ∀ j ∈ (Finset.univ : Finset (Fin r)),
          0 ≤ boundaryTerm j := by
        intro j _hj
        exact mul_nonneg
          (closedIntervalBoundaryIndicator_nonneg _ _ _ _)
          (Finset.prod_nonneg fun k _hk ↦
            closedIntervalIndicator_nonneg _ _ _)
      have hsumOne : 1 ≤
          ∑ j,
            closedIntervalBoundaryIndicator (a j) (b j) eta (x j) *
              ∏ k ∈ (Finset.univ : Finset (Fin r)).erase j,
                closedIntervalIndicator (a k - eta) (b k + eta) (x k) := by
        change 1 ≤ ∑ j, boundaryTerm j
        rw [← hterm']
        exact Finset.single_le_sum htermNonneg (Finset.mem_univ i)
      exact hfrozenPhase.trans <| hsumOne.trans <|
        le_add_of_nonneg_left (mul_nonneg hdelta
          (closedIntervalIndicatorProduct_nonneg _ _ _))
    · push_neg at hxall hyall
      obtain ⟨i, hxi⟩ := hxall
      obtain ⟨j, hyj⟩ := hyall
      rw [closedIntervalIndicatorProduct_eq_zero hxi,
        closedIntervalIndicatorProduct_eq_zero hyj]
      norm_num only [Complex.ofReal_zero, mul_zero, sub_self, norm_zero]
      exact add_nonneg
        (mul_nonneg hdelta (closedIntervalIndicatorProduct_nonneg _ _ _))
        (Finset.sum_nonneg fun k _hk ↦ mul_nonneg
          (closedIntervalBoundaryIndicator_nonneg _ _ _ _)
          (Finset.prod_nonneg fun l _hl ↦
            closedIntervalIndicator_nonneg _ _ _))

/-- Direct oscillatory-phase specialization of the pointwise freezing
inequality.  The phase error is no longer a hypothesis: it follows from the
proved Lipschitz bound and the distance from the cylinder representative. -/
theorem norm_oscillatoryPhase_mul_intervalProducts_sub_le_freezingError
    {r : ℕ} (a b x y : Fin r → ℝ)
    (K alpha representative : ℝ) {phaseRadius eta : ℝ}
    (hphaseRadius : 0 ≤ phaseRadius) (heta : 0 ≤ eta)
    (halpha : |alpha - representative| ≤ phaseRadius)
    (hxy : ∀ i, |x i - y i| ≤ eta) :
    ‖oscillatoryPhase K alpha *
          (closedIntervalIndicatorProduct a b x : ℂ) -
        oscillatoryPhase K representative *
          (closedIntervalIndicatorProduct a b y : ℂ)‖ ≤
      (2 * Real.pi * |K| * phaseRadius) *
          closedIntervalIndicatorProduct
            (fun i ↦ a i - eta) (fun i ↦ b i + eta) x +
        ∑ i,
          closedIntervalBoundaryIndicator (a i) (b i) eta (x i) *
            ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
              closedIntervalIndicator (a j - eta) (b j + eta) (x j) := by
  apply norm_phase_mul_intervalProducts_sub_le_freezingError
      a b x y (oscillatoryPhase K alpha)
      (oscillatoryPhase K representative)
  · positivity
  · exact heta
  · rw [norm_oscillatoryPhase]
  · rw [norm_oscillatoryPhase]
  · exact (norm_oscillatoryPhase_sub_le K alpha representative).trans <|
      mul_le_mul_of_nonneg_left halpha (by positivity)
  · exact hxy

end

end Erdos1002
