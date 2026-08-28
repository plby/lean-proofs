import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegralKernels

/-!
# Jointly analytic Cauchy kernels in three complex variables

The three denominators are elements of the actual Banach algebra of
continuous functions on the boundary of a polydisc.  Inversion in that
algebra gives joint analyticity in all three poles.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

open CuspNormalization.Germs.NormalIntegral

/-- The product coordinates used only to prove the native threefold result. -/
abbrev ProductModel := ℂ × (ℂ × ℂ)

/-- The actual product of the three integration circles. -/
abbrev BoundaryCube (r : ℝ) :=
  sphere (0 : ℂ) r × (sphere (0 : ℂ) r × sphere (0 : ℂ) r)

/-- The open, equal-radius polydisc. -/
def openCube (r : ℝ) : Set ProductModel :=
  ball 0 r ×ˢ (ball 0 r ×ˢ ball 0 r)

/-- The closed, equal-radius polydisc. -/
def closedCube (r : ℝ) : Set ProductModel :=
  closedBall 0 r ×ˢ (closedBall 0 r ×ˢ closedBall 0 r)

theorem isOpen_openCube (r : ℝ) : IsOpen (openCube r) :=
  isOpen_ball.prod (isOpen_ball.prod isOpen_ball)

/-- First boundary coordinate in the continuous-function algebra. -/
def boundaryFirst (r : ℝ) : C(BoundaryCube r, ℂ) :=
  ⟨fun w => w.1.1, continuous_subtype_val.comp continuous_fst⟩

/-- Second boundary coordinate in the continuous-function algebra. -/
def boundarySecond (r : ℝ) : C(BoundaryCube r, ℂ) :=
  ⟨fun w => w.2.1.1,
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)⟩

/-- Third boundary coordinate in the continuous-function algebra. -/
def boundaryThird (r : ℝ) : C(BoundaryCube r, ℂ) :=
  ⟨fun w => w.2.2.1,
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)⟩

def firstDenominator (r : ℝ) (z : ProductModel) : C(BoundaryCube r, ℂ) :=
  boundaryFirst r - ContinuousMap.const _ z.1

def secondDenominator (r : ℝ) (z : ProductModel) : C(BoundaryCube r, ℂ) :=
  boundarySecond r - ContinuousMap.const _ z.2.1

def thirdDenominator (r : ℝ) (z : ProductModel) : C(BoundaryCube r, ℂ) :=
  boundaryThird r - ContinuousMap.const _ z.2.2

private theorem boundary_sub_ne_zero {r : ℝ} {z : ℂ}
    (hz : z ∈ ball 0 r) (w : sphere (0 : ℂ) r) : (w : ℂ) - z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hw : ‖(w : ℂ)‖ = r := by
    simpa only [mem_sphere, dist_zero_right] using w.2
  have hzn : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
  exact (ne_of_lt hzn) (he ▸ hw)

theorem firstDenominator_ne_zero {r : ℝ} {z : ProductModel}
    (hz : z.1 ∈ ball 0 r) (w : BoundaryCube r) : firstDenominator r z w ≠ 0 :=
  boundary_sub_ne_zero hz w.1

theorem secondDenominator_ne_zero {r : ℝ} {z : ProductModel}
    (hz : z.2.1 ∈ ball 0 r) (w : BoundaryCube r) : secondDenominator r z w ≠ 0 :=
  boundary_sub_ne_zero hz w.2.1

theorem thirdDenominator_ne_zero {r : ℝ} {z : ProductModel}
    (hz : z.2.2 ∈ ball 0 r) (w : BoundaryCube r) : thirdDenominator r z w ≠ 0 :=
  boundary_sub_ne_zero hz w.2.2

private theorem denominator_analyticAt (r : ℝ) (u : C(BoundaryCube r, ℂ))
    {p : ProductModel → ℂ} {z : ProductModel} (hp : AnalyticAt ℂ p z) :
    AnalyticAt ℂ (fun x => u - ContinuousMap.const (BoundaryCube r) (p x)) z := by
  have hc := ((ContinuousLinearMap.const (R := ℂ) (M := ℂ)
    (BoundaryCube r)).analyticAt (p z)).comp hp
  exact analyticAt_const.sub hc

theorem firstDenominator_analyticAt (r : ℝ) (z : ProductModel) :
    AnalyticAt ℂ (firstDenominator r) z :=
  denominator_analyticAt r _ analyticAt_fst

theorem secondDenominator_analyticAt (r : ℝ) (z : ProductModel) :
    AnalyticAt ℂ (secondDenominator r) z :=
  denominator_analyticAt r _ (analyticAt_fst.comp analyticAt_snd)

theorem thirdDenominator_analyticAt (r : ℝ) (z : ProductModel) :
    AnalyticAt ℂ (thirdDenominator r) z :=
  denominator_analyticAt r _ (analyticAt_snd.comp analyticAt_snd)

/-- The genuine three Cauchy kernels multiplied by the boundary data. -/
def boundaryKernel (r : ℝ) (u : C(BoundaryCube r, ℂ)) (z : ProductModel) :
    C(BoundaryCube r, ℂ) :=
  Ring.inverse (firstDenominator r z) * Ring.inverse (secondDenominator r z) *
    Ring.inverse (thirdDenominator r z) * u

theorem boundaryKernel_apply {r : ℝ} (u : C(BoundaryCube r, ℂ))
    {z : ProductModel} (hz : z ∈ openCube r) (w : BoundaryCube r) :
    boundaryKernel r u z w =
      ((w.1.1 : ℂ) - z.1)⁻¹ * ((w.2.1.1 : ℂ) - z.2.1)⁻¹ *
        ((w.2.2.1 : ℂ) - z.2.2)⁻¹ * u w := by
  simp only [boundaryKernel, ContinuousMap.mul_apply]
  rw [inverse_continuousMap_apply _ (firstDenominator_ne_zero hz.1),
    inverse_continuousMap_apply _ (secondDenominator_ne_zero hz.2.1),
    inverse_continuousMap_apply _ (thirdDenominator_ne_zero hz.2.2)]
  rfl

theorem boundaryKernel_analyticOnNhd (r : ℝ) (u : C(BoundaryCube r, ℂ)) :
    AnalyticOnNhd ℂ (boundaryKernel r u) (openCube r) := by
  intro z hz
  have h₁ := (analyticAt_inverse_continuousMap (firstDenominator r z)
    (firstDenominator_ne_zero hz.1)).comp (firstDenominator_analyticAt r z)
  have h₂ := (analyticAt_inverse_continuousMap (secondDenominator r z)
    (secondDenominator_ne_zero hz.2.1)).comp (secondDenominator_analyticAt r z)
  have h₃ := (analyticAt_inverse_continuousMap (thirdDenominator r z)
    (thirdDenominator_ne_zero hz.2.2)).comp (thirdDenominator_analyticAt r z)
  exact ((h₁.mul h₂).mul h₃).mul analyticAt_const

/-- Every actual bounded integral of these kernels is jointly analytic. -/
theorem analyticOnNhd_boundaryKernel_functional (r : ℝ)
    (u : C(BoundaryCube r, ℂ)) (L : C(BoundaryCube r, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun z => L (boundaryKernel r u z)) (openCube r) := by
  intro z hz
  exact (L.analyticAt _).comp (boundaryKernel_analyticOnNhd r u z hz)

/-- Restriction of the original continuous function to the actual boundary. -/
def boundaryValues {f : ProductModel → ℂ} {r : ℝ}
    (hf : ContinuousOn f (closedCube r)) : C(BoundaryCube r, ℂ) := by
  let e : BoundaryCube r → ProductModel := fun w => (w.1.1, (w.2.1.1, w.2.2.1))
  have he : Continuous e :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  refine ⟨fun w => f (e w), hf.comp_continuous he ?_⟩
  intro w
  exact ⟨sphere_subset_closedBall w.1.2,
    sphere_subset_closedBall w.2.1.2, sphere_subset_closedBall w.2.2.2⟩

@[simp] theorem boundaryValues_apply {f : ProductModel → ℂ} {r : ℝ}
    (hf : ContinuousOn f (closedCube r)) (w : BoundaryCube r) :
    boundaryValues hf w = f (w.1.1, (w.2.1.1, w.2.2.1)) := rfl

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
