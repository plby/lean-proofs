import ErdosProblems.Erdos1038.PlatformReferenceBlockObservableRecombination
import ErdosProblems.Erdos1038.PlatformReferenceUniformComparison
import ErdosProblems.Erdos1038.ResidualWidthInverseBranch

/-!
# Root limits for the canonical platform inverse series

When the platform edge is at least one, every canonical reference mesh is
itself a residual configuration: its probability weights are `k` times the
Lagrange weights.  This lets the finite inverse-branch theorems identify the
odd series with the difference of the positive and negative zero-potential
roots.  Pointwise convergence of the logarithmic potential then squeezes
those two roots to their continuum crossings.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

omit [LinearOrder iota] in
/-- The canonical refined Lagrange weights retain total mass `1 / k`. -/
theorem sum_platformResidualRefinementAlpha_eq_one_div
    (C : ResidualConfiguration iota) (k : ℝ) (n : ℕ) :
    (∑ p, platformResidualRefinementAlpha C k n p) = 1 / k := by
  have hsum :=
    sum_platformResidualRefinementAlpha_mul C k n (fun _p ↦ (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [one_div, inv_mul_cancel₀ hden] at hsum
  simp only [mul_one] at hsum
  rw [sum_residualLagrangeAlpha] at hsum
  exact hsum

/-- Regard one canonical platform reference mesh as a residual probability
configuration.  The additional hypothesis `1 ≤ a` is exactly what puts its
locations in the normalized interval `[1,2]`. -/
def platformReferenceResidualConfiguration
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    ResidualConfiguration (iota × Fin (n + 1)) where
  weight p := k * platformResidualRefinementAlpha C k n p
  weight_pos p := by
    exact mul_pos (zero_lt_one.trans_le hk)
      (refinedLagrangeWeight_pos (Nat.succ_pos n)
        (residualLagrangeAlpha_pos C (zero_lt_one.trans_le hk)) p)
  sum_weight := by
    rw [← Finset.mul_sum,
      sum_platformResidualRefinementAlpha_eq_one_div C k n]
    field_simp [(zero_lt_one.trans_le hk).ne']
  location := platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n
  location_mem p := by
    have hp := platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p
    exact ⟨ha1.trans hp.1, hp.2⟩

@[simp]
theorem platformReferenceResidualConfiguration_location
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
      hthreshold n).location =
      platformResidualRefinementReference C k a hk ha ha2 hthreshold n :=
  rfl

@[simp]
theorem residualLagrangeAlpha_platformReferenceResidualConfiguration
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    residualLagrangeAlpha
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n) k =
      platformResidualRefinementAlpha C k n := by
  funext p
  unfold residualLagrangeAlpha platformReferenceResidualConfiguration
  field_simp [(zero_lt_one.trans_le hk).ne']

/-- The normalized continuum logarithmic potential at any non-support point
to the left of the platform. -/
def platformReferenceExteriorPotentialLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (x : ℝ) : ℝ :=
  Real.log |x| +
    platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
      (fun _i d ↦ Real.log (d - x))

/-- The corresponding normalized potential on the `n`th canonical mesh. -/
def platformResidualRefinementExteriorPotential
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) (x : ℝ) : ℝ :=
  Real.log |x| +
    ∑ p, platformResidualRefinementAlpha C k n p *
      Real.log
        (platformResidualRefinementReference C k a hk ha ha2
          hthreshold n p - x)

/-- At every fixed point to the left of the platform, the canonical discrete
potential converges to its full-quantile continuum value. -/
theorem tendsto_platformResidualRefinement_exteriorPotential
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    Tendsto
      (fun n ↦ platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n x)
      atTop
      (nhds (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold x)) := by
  have hobservable := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun _i d ↦ Real.log (d - x)) (by
      intro i
      exact (continuousOn_id.sub continuousOn_const).log fun d hd ↦
        (sub_pos.mpr (hxa.trans_le hd.1)).ne')
  simpa only [platformResidualRefinementExteriorPotential,
    platformReferenceExteriorPotentialLimit] using!
      tendsto_const_nhds.add hobservable

/-- On the positive side this two-sided notation agrees with the earlier
positive exterior-potential limit. -/
theorem platformReferenceExteriorPotentialLimit_eq_logPotentialLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) :
    platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold s =
      platformReferenceExteriorLogPotentialLimit C k a
        hk ha ha2 hthreshold s := by
  simp only [platformReferenceExteriorPotentialLimit,
    platformReferenceExteriorLogPotentialLimit, abs_of_pos hs]

/-- The residual potential of the packaged mesh is `k` times the normalized
canonical potential. -/
theorem residualPotential_platformReferenceResidualConfiguration
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {x : ℝ} (hxa : x < a) :
    residualPotential
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n) k x =
      k * platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n x := by
  let reference := platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n
  have habs (p : iota × Fin (n + 1)) :
      |x - reference p| = reference p - x := by
    rw [abs_of_neg]
    · ring
    · exact sub_neg.mpr (hxa.trans_le
        (platformResidualRefinementReference_mem_Icc
          C k a hk ha ha2 hthreshold n p).1)
  unfold residualPotential platformResidualRefinementExteriorPotential
    platformReferenceResidualConfiguration
  simp only [reference] at habs ⊢
  simp_rw [habs]
  have hfactor :
      (∑ p, k * platformResidualRefinementAlpha C k n p *
          Real.log
            (platformResidualRefinementReference C k a hk ha ha2
              hthreshold n p - x)) =
        k * ∑ p, platformResidualRefinementAlpha C k n p *
          Real.log
            (platformResidualRefinementReference C k a hk ha ha2
              hthreshold n p - x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  rw [hfactor]
  ring

/-- The packaged residual scale is the actual canonical inverse monomial. -/
theorem residualScale_platformReferenceResidualConfiguration
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    residualScale
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n) k =
      inverseMonomial (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a hk ha ha2
          hthreshold n) := by
  symm
  simpa only [
    residualLagrangeAlpha_platformReferenceResidualConfiguration,
    platformReferenceResidualConfiguration_location] using!
      inverseMonomial_residualLagrangeAlpha
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n) k

/-- Positive evaluation of the canonical inverse power series. -/
def platformResidualRefinementPositiveInverseValue
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) : ℝ :=
  lagrangeInverseValue (platformResidualRefinementAlpha C k n)
    (platformResidualRefinementReference C k a hk ha ha2 hthreshold n)
    (inverseMonomial (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a hk ha ha2 hthreshold n))

/-- Negative evaluation of the same canonical inverse power series. -/
def platformResidualRefinementNegativeInverseValue
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) : ℝ :=
  lagrangeInverseValue (platformResidualRefinementAlpha C k n)
    (platformResidualRefinementReference C k a hk ha ha2 hthreshold n)
    (-inverseMonomial (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a hk ha ha2 hthreshold n))

theorem platformResidualRefinementPositiveInverseValue_eq_residual
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    platformResidualRefinementPositiveInverseValue C k a
        hk ha ha2 hthreshold n =
      lagrangeInverseValue
        (residualLagrangeAlpha
          (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
            hthreshold n) k)
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n).location
        (residualScale
          (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
            hthreshold n) k) := by
  rw [platformResidualRefinementPositiveInverseValue,
    residualLagrangeAlpha_platformReferenceResidualConfiguration,
    platformReferenceResidualConfiguration_location,
    residualScale_platformReferenceResidualConfiguration]

theorem platformResidualRefinementNegativeInverseValue_eq_residual
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    platformResidualRefinementNegativeInverseValue C k a
        hk ha ha2 hthreshold n =
      lagrangeInverseValue
        (residualLagrangeAlpha
          (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
            hthreshold n) k)
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n).location
        (-residualScale
          (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
            hthreshold n) k) := by
  rw [platformResidualRefinementNegativeInverseValue,
    residualLagrangeAlpha_platformReferenceResidualConfiguration,
    platformReferenceResidualConfiguration_location,
    residualScale_platformReferenceResidualConfiguration]

/-- A point left of the platform edge is left of every location, hence of
the minimum location of the packaged residual configuration. -/
theorem lt_residualMinLocation_platformReferenceResidualConfiguration
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {x : ℝ} (hxa : x < a) :
    x < residualMinLocation
      (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
        hthreshold n) := by
  let Q := platformReferenceResidualConfiguration C k a hk ha ha1 ha2
    hthreshold n
  rw [← location_residualMinIndex Q]
  change x < platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n (residualMinIndex Q)
  exact hxa.trans_le
    (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n (residualMinIndex Q)).1

/-- A positive continuum barrier makes the packaged canonical meshes
separated after discarding finitely many coarse meshes. -/
theorem eventually_platformReferenceResidualConfiguration_separated
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop,
      IsResidualSeparationPoint
        (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
          hthreshold n) k s := by
  have hpotential :=
    (tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold hsa).eventually (Ioi_mem_nhds hlimit)
  filter_upwards [hpotential] with n hn
  refine ⟨hs, ?_, ?_⟩
  · intro p
    exact hsa.trans_le
      (platformResidualRefinementReference_mem_Icc
        C k a hk ha ha2 hthreshold n p).1
  · rw [residualPotential_platformReferenceResidualConfiguration
      C k a hk ha ha1 ha2 hthreshold n hsa]
    exact mul_nonneg (zero_lt_one.trans_le hk).le hn.le

/-- On the negative half-line, positive potential means that the inverse
map lies below the negative scale. -/
theorem residualPotential_pos_iff_psi_lt_neg_scale_of_neg
    {jota : Type*} [Fintype jota]
    (C : ResidualConfiguration jota) {k y : ℝ}
    (hk : 0 < k) (hy : y < 0) :
    0 < residualPotential C k y ↔
      residualPsi C k y < -residualScale C k := by
  have hyMin : y < residualMinLocation C :=
    hy.trans (residualMinLocation_pos C)
  have hpsi : residualPsi C k y < 0 := by
    unfold residualPsi
    exact mul_neg_of_neg_of_pos hy (Real.exp_pos _)
  have hscale := residualScale_pos C k
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale
      C hk.ne' hy.ne hyMin,
    mul_pos_iff]
  simp only [hk, true_and, not_lt_of_ge hk.le, false_and, or_false]
  rw [Real.log_pos_iff
      (div_pos (abs_pos.mpr hpsi.ne) hscale).le,
    one_lt_div hscale, abs_of_neg hpsi]
  constructor <;> intro h <;> linarith

/-- On the negative half-line, negative potential means that the inverse
map lies above the negative scale. -/
theorem residualPotential_neg_iff_neg_scale_lt_psi_of_neg
    {jota : Type*} [Fintype jota]
    (C : ResidualConfiguration jota) {k y : ℝ}
    (hk : 0 < k) (hy : y < 0) :
    residualPotential C k y < 0 ↔
      -residualScale C k < residualPsi C k y := by
  have hyMin : y < residualMinLocation C :=
    hy.trans (residualMinLocation_pos C)
  have hpsi : residualPsi C k y < 0 := by
    unfold residualPsi
    exact mul_neg_of_neg_of_pos hy (Real.exp_pos _)
  have hscale := residualScale_pos C k
  rw [residualPotential_eq_k_mul_log_abs_psi_div_scale
      C hk.ne' hy.ne hyMin,
    mul_neg_iff]
  simp only [hk, true_and, not_lt_of_ge hk.le, false_and, or_false]
  rw [Real.log_neg_iff (div_pos (abs_pos.mpr hpsi.ne) hscale),
    div_lt_one hscale, abs_of_neg hpsi]
  constructor <;> intro h <;> linarith

/-- A negative potential point below a positive separation barrier lies
strictly below the positive inverse-series root. -/
theorem lt_platformResidualRefinementPositiveInverseValue_of_separated
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {y s : ℝ} (hy : 0 < y) (hys : y < s) (hsa : s < a)
    (hsep : IsResidualSeparationPoint
      (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
        hthreshold n) k s)
    (hpotential :
      platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n y < 0) :
    y < platformResidualRefinementPositiveInverseValue C k a
      hk ha ha2 hthreshold n := by
  rw [platformResidualRefinementPositiveInverseValue_eq_residual
    C k a hk ha ha1 ha2 hthreshold n]
  let Q := platformReferenceResidualConfiguration C k a hk ha ha1 ha2
    hthreshold n
  let W := lagrangeInverseValue (residualLagrangeAlpha Q k) Q.location
    (residualScale Q k)
  let yc := residualCriticalPoint Q k (zero_lt_one.trans_le hk)
  change y < W
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hyMin : y < residualMinLocation Q := by
    simpa only [Q] using!
      lt_residualMinLocation_platformReferenceResidualConfiguration
        C k a hk ha ha1 ha2 hthreshold n (hys.trans hsa)
  have hsMin : s < residualMinLocation Q := by
    rw [← location_residualMinIndex Q]
    exact hsep.2.1 (residualMinIndex Q)
  have hyPotentialQ : residualPotential Q k y < 0 := by
    have heq := residualPotential_platformReferenceResidualConfiguration
      C k a hk ha ha1 ha2 hthreshold n (hys.trans hsa)
    change residualPotential Q k y < 0
    rw [heq]
    exact mul_neg_of_pos_of_neg hk0 hpotential
  have hyPsiLt : residualPsi Q k y < residualScale Q k :=
    (residualPotential_neg_iff_psi_lt_scale_of_pos
      Q hk0 hy hyMin).mp hyPotentialQ
  have hsScaleLe : residualScale Q k ≤ residualPsi Q k s :=
    (residualPotential_nonneg_iff_scale_le_psi_of_pos
      Q hk0 hsep.1 hsMin).mp hsep.2.2
  have hycMem := residualCriticalPoint_mem_Ioo Q k hk0
  have hyLtYc : y < yc := by
    by_contra hnot
    have hycLeY : yc ≤ y := le_of_not_gt hnot
    have hycLeS : yc ≤ s := hycLeY.trans hys.le
    have hanti := residualPsi_strictAntiOn_right Q k hk0
      ⟨hycLeY, hyMin⟩ ⟨hycLeS, hsMin⟩ hys
    linarith
  have hW0 : 0 ≤ W := by
    unfold W lagrangeInverseValue
    exact tsum_nonneg fun degree ↦ mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg
        (residualLagrangeAlpha Q k) Q.location
        (residualLagrangeAlpha_pos Q hk0)
        (residual_locations_mem_positiveCoordinates Q) degree)
      (pow_nonneg (residualScale_pos Q k).le degree)
  have hWle : W ≤ yc :=
    residual_lagrangeInverseValue_le_critical_of_separation Q hk0 hsep
  have hpsiW : residualPsi Q k W = residualScale Q k :=
    residualPsi_lagrangeInverseValue_eq_scale_of_separation Q hk0 hsep
  by_contra hnot
  have hWleY : W ≤ y := le_of_not_gt hnot
  have hpsiLe := (residualPsi_strictMonoOn_left Q k hk0).monotoneOn
    ⟨hW0, hWle⟩ ⟨hy.le, hyLtYc.le⟩ hWleY
  rw [hpsiW] at hpsiLe
  linarith

/-- A positive discrete potential point bounds the positive inverse-series
root from above. -/
theorem platformResidualRefinementPositiveInverseValue_lt_of_potential_pos
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {y : ℝ} (hy : 0 < y) (hya : y < a)
    (hpotential : 0 <
      platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n y) :
    platformResidualRefinementPositiveInverseValue C k a
        hk ha ha2 hthreshold n < y := by
  let alpha := platformResidualRefinementAlpha C k n
  let reference := platformResidualRefinementReference C k a
    hk ha ha2 hthreshold n
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have halpha (p : iota × Fin (n + 1)) : 0 < alpha p := by
    exact refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C hk0) p
  have href : reference ∈ positiveCoordinates (iota × Fin (n + 1)) :=
    platformResidualRefinementReference_mem_positiveCoordinates
      C k a hk ha ha2 hthreshold n
  have hyr (p : iota × Fin (n + 1)) : y < reference p :=
    hya.trans_le (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p).1
  have hpotential' :
      0 < Real.log y + ∑ p, alpha p * Real.log (reference p - y) := by
    simpa only [platformResidualRefinementExteriorPotential,
      abs_of_pos hy, alpha, reference] using! hpotential
  have hstrict := inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    alpha reference href hy hyr hpotential'
  simpa only [platformResidualRefinementPositiveInverseValue,
    alpha, reference] using!
      lagrangeInverseValue_lt_comparison alpha reference halpha href
        hy hyr (inverseMonomial_pos alpha reference).le hstrict

/-- A positive-potential point on the negative half-line lies below the
negative inverse-series root. -/
theorem lt_platformResidualRefinementNegativeInverseValue_of_potential_pos
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {y s : ℝ} (hy : y < 0)
    (hsep : IsResidualSeparationPoint
      (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
        hthreshold n) k s)
    (hpotential : 0 <
      platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n y) :
    y < platformResidualRefinementNegativeInverseValue C k a
      hk ha ha2 hthreshold n := by
  rw [platformResidualRefinementNegativeInverseValue_eq_residual
    C k a hk ha ha1 ha2 hthreshold n]
  let Q := platformReferenceResidualConfiguration C k a hk ha ha1 ha2
    hthreshold n
  let W := lagrangeInverseValue (residualLagrangeAlpha Q k) Q.location
    (-residualScale Q k)
  change y < W
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hyPotentialQ : 0 < residualPotential Q k y := by
    have heq := residualPotential_platformReferenceResidualConfiguration
      C k a hk ha ha1 ha2 hthreshold n (hy.trans ha)
    change 0 < residualPotential Q k y
    rw [heq]
    exact mul_pos hk0 hpotential
  have hyPsiLt : residualPsi Q k y < -residualScale Q k :=
    (residualPotential_pos_iff_psi_lt_neg_scale_of_neg Q hk0 hy).mp
      hyPotentialQ
  have hWneg : W < 0 :=
    residual_lagrangeInverseValue_neg_lt_zero_of_separation Q hk0 hsep
  have hpsiW : residualPsi Q k W = -residualScale Q k :=
    residualPsi_lagrangeInverseValue_neg_eq_neg_scale_of_separation
      Q hk0 hsep
  by_contra hnot
  have hWleY : W ≤ y := le_of_not_gt hnot
  have hpsiLe := (residualPsi_strictMonoOn_nonpos Q hk0).monotoneOn
    hWneg.le hy.le hWleY
  rw [hpsiW] at hpsiLe
  linarith

/-- A negative-potential point on the negative half-line lies above the
negative inverse-series root. -/
theorem platformResidualRefinementNegativeInverseValue_lt_of_potential_neg
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    {y s : ℝ} (hy : y < 0)
    (hsep : IsResidualSeparationPoint
      (platformReferenceResidualConfiguration C k a hk ha ha1 ha2
        hthreshold n) k s)
    (hpotential :
      platformResidualRefinementExteriorPotential C k a
        hk ha ha2 hthreshold n y < 0) :
    platformResidualRefinementNegativeInverseValue C k a
        hk ha ha2 hthreshold n < y := by
  rw [platformResidualRefinementNegativeInverseValue_eq_residual
    C k a hk ha ha1 ha2 hthreshold n]
  let Q := platformReferenceResidualConfiguration C k a hk ha ha1 ha2
    hthreshold n
  let W := lagrangeInverseValue (residualLagrangeAlpha Q k) Q.location
    (-residualScale Q k)
  change W < y
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hyPotentialQ : residualPotential Q k y < 0 := by
    have heq := residualPotential_platformReferenceResidualConfiguration
      C k a hk ha ha1 ha2 hthreshold n (hy.trans ha)
    change residualPotential Q k y < 0
    rw [heq]
    exact mul_neg_of_pos_of_neg hk0 hpotential
  have hyPsiGt : -residualScale Q k < residualPsi Q k y :=
    (residualPotential_neg_iff_neg_scale_lt_psi_of_neg Q hk0 hy).mp
      hyPotentialQ
  have hWneg : W < 0 :=
    residual_lagrangeInverseValue_neg_lt_zero_of_separation Q hk0 hsep
  have hpsiW : residualPsi Q k W = -residualScale Q k :=
    residualPsi_lagrangeInverseValue_neg_eq_neg_scale_of_separation
      Q hk0 hsep
  by_contra hnot
  have hyLeW : y ≤ W := le_of_not_gt hnot
  have hpsiLe := (residualPsi_strictMonoOn_nonpos Q hk0).monotoneOn
    hy.le hWneg.le hyLeW
  rw [hpsiW] at hpsiLe
  linarith

/-- Local strict sign change of negative slope at a continuum crossing. -/
def IsNegativeSlopeExteriorCrossing (P : ℝ → ℝ) (x : ℝ) : Prop :=
  x < 0 ∧
    (∀ l < x, ∃ y, l < y ∧ y < x ∧ 0 < P y) ∧
    (∀ u > x, ∃ y, x < y ∧ y < u ∧ y < 0 ∧ P y < 0)

/-- Local strict sign change of positive slope at a continuum crossing,
with all comparison points kept strictly left of the platform edge. -/
def IsPositiveSlopeExteriorCrossing
    (P : ℝ → ℝ) (a x : ℝ) : Prop :=
  0 < x ∧ x < a ∧
    (∀ l < x, ∃ y, l < y ∧ 0 < y ∧ y < x ∧ P y < 0) ∧
    (∀ u > x, ∃ y, x < y ∧ y < u ∧ y < a ∧ 0 < P y)

/-- The positive canonical inverse values converge to any positive-slope
continuum crossing lying below a positive separation barrier. -/
theorem tendsto_platformResidualRefinementPositiveInverseValue
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hcrossing : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus) :
    Tendsto
      (fun n ↦ platformResidualRefinementPositiveInverseValue C k a
        hk ha ha2 hthreshold n)
      atTop (nhds xPlus) := by
  have hsep := eventually_platformReferenceResidualConfiguration_separated
    C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier
  rw [tendsto_order]
  constructor
  · intro l hl
    obtain ⟨y, hly, hy, hyx, hyPotential⟩ := hcrossing.2.2.1 l hl
    have hyS : y < s := hyx.trans hxPlusS
    have hyLimit := tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold (hyS.trans hsa)
    have hyDiscrete := hyLimit.eventually (Iio_mem_nhds hyPotential)
    filter_upwards [hsep, hyDiscrete] with n hnsep hnPotential
    exact hly.trans
      (lt_platformResidualRefinementPositiveInverseValue_of_separated
        C k a hk ha ha1 ha2 hthreshold n hy hyS hsa
          hnsep hnPotential)
  · intro u hu
    obtain ⟨y, hxy, hyu, hya, hyPotential⟩ := hcrossing.2.2.2 u hu
    have hyLimit := tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold hya
    have hyDiscrete := hyLimit.eventually (Ioi_mem_nhds hyPotential)
    filter_upwards [hyDiscrete] with n hnPotential
    exact
      (platformResidualRefinementPositiveInverseValue_lt_of_potential_pos
        C k a hk ha ha2 hthreshold n
          (hcrossing.1.trans hxy) hya hnPotential).trans hyu

/-- The negative canonical inverse values converge to a negative-slope
continuum crossing. -/
theorem tendsto_platformResidualRefinementNegativeInverseValue
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hcrossing : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus) :
    Tendsto
      (fun n ↦ platformResidualRefinementNegativeInverseValue C k a
        hk ha ha2 hthreshold n)
      atTop (nhds xMinus) := by
  have hsep := eventually_platformReferenceResidualConfiguration_separated
    C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier
  rw [tendsto_order]
  constructor
  · intro l hl
    obtain ⟨y, hly, hyx, hyPotential⟩ := hcrossing.2.1 l hl
    have hy : y < 0 := hyx.trans hcrossing.1
    have hyLimit := tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold (hy.trans ha)
    have hyDiscrete := hyLimit.eventually (Ioi_mem_nhds hyPotential)
    filter_upwards [hsep, hyDiscrete] with n hnsep hnPotential
    exact hly.trans
      (lt_platformResidualRefinementNegativeInverseValue_of_potential_pos
        C k a hk ha ha1 ha2 hthreshold n hy hnsep hnPotential)
  · intro u hu
    obtain ⟨y, hxy, hyu, hy, hyPotential⟩ := hcrossing.2.2 u hu
    have hyLimit := tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold (hy.trans ha)
    have hyDiscrete := hyLimit.eventually (Iio_mem_nhds hyPotential)
    filter_upwards [hsep, hyDiscrete] with n hnsep hnPotential
    exact
      (platformResidualRefinementNegativeInverseValue_lt_of_potential_neg
        C k a hk ha ha1 ha2 hthreshold n hy hnsep hnPotential).trans hyu

/-- On every sufficiently fine separated mesh, the odd inverse-width series
is exactly the difference of the two canonical inverse values. -/
theorem eventually_inverseWidthSeries_platformResidualRefinement_eq_roots
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop,
      inverseWidthSeries (platformResidualRefinementAlpha C k n)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n) =
        platformResidualRefinementPositiveInverseValue C k a
            hk ha ha2 hthreshold n -
          platformResidualRefinementNegativeInverseValue C k a
            hk ha ha2 hthreshold n := by
  have hsep := eventually_platformReferenceResidualConfiguration_separated
    C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier
  filter_upwards [hsep] with n hnsep
  let Q := platformReferenceResidualConfiguration C k a hk ha ha1 ha2
    hthreshold n
  have hwidth := inverseWidthSeries_residual_eq_inverseValue_sub_neg
    Q (zero_lt_one.trans_le hk) hnsep
  simpa only [Q,
    residualLagrangeAlpha_platformReferenceResidualConfiguration,
    platformReferenceResidualConfiguration_location,
    residualScale_platformReferenceResidualConfiguration,
    platformResidualRefinementPositiveInverseValue,
    platformResidualRefinementNegativeInverseValue] using! hwidth

/-- The actual canonical inverse-width series converges to the distance
between the two continuum exterior crossings. -/
theorem tendsto_inverseWidthSeries_platformResidualRefinement_crossings
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus) :
    Tendsto
      (fun n ↦ inverseWidthSeries
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop (nhds (xPlus - xMinus)) := by
  have hpositive := tendsto_platformResidualRefinementPositiveInverseValue
    C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier hplus
  have hnegative := tendsto_platformResidualRefinementNegativeInverseValue
    C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier hminus
  apply (hpositive.sub hnegative).congr'
  filter_upwards
      [eventually_inverseWidthSeries_platformResidualRefinement_eq_roots
        C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier] with n hn
  exact hn.symm

/-- Final base-series value identification: the continuum odd coefficient
sum is the distance between the negative and positive platform crossings. -/
theorem two_mul_tsum_platformReferenceScaledLagrangeCoefficientLimit_eq_crossingWidth
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus) :
    2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientLimit C k a
          hk ha ha2 hthreshold (2 * j + 1) =
      xPlus - xMinus := by
  have hlogBarrier : 0 < platformReferenceExteriorLogPotentialLimit
      C k a hk ha ha2 hthreshold s := by
    rw [← platformReferenceExteriorPotentialLimit_eq_logPotentialLimit
      C k a hk ha ha2 hthreshold hs]
    exact hbarrier
  have hcoefficient :=
    tendsto_inverseWidthSeries_platformResidualRefinement
      C k a hk ha ha2 hthreshold hs hsa hlogBarrier
  have hcrossings :=
    tendsto_inverseWidthSeries_platformResidualRefinement_crossings
      C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
        hminus hplus
  exact tendsto_nhds_unique hcoefficient hcrossings

end

end Erdos1038
