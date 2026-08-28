import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsEllipticGrowth
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableGrowth

/-!
# Actual entire extensions of the descended differential coefficients

The proved elliptic growth removes the two finite punctures of a descended
one-form coefficient. For a cubic differential, multiplying by
`t²(t - 1)²` gives the same removable growth. The resulting functions use
their actual punctured limits at the two marked points and retain the
original coefficients everywhere else, including their germs at infinity.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle
open TriangleHolomorphicDifferentialsRemovable

theorem differentialDescent_growth_zero {p : ℕ} {A : ℍ → ℂ}
    (hp : 0 < p) (hInv : IsInvariantDifferential p A)
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) :
    Tendsto (fun t : ℂ => t ^ p * differentialDescent p A t)
      (𝓝[≠] 0) (𝓝 0) := by
  simpa only [ellipticCenter, specialSourceCoordinate_centerOne, sub_zero] using
    differentialDescent_elliptic_growth hp hInv hA Elliptic.Kind.three

theorem differentialDescent_growth_one {p : ℕ} {A : ℍ → ℂ}
    (hp : 0 < p) (hInv : IsInvariantDifferential p A)
    (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) :
    Tendsto (fun t : ℂ => (t - 1) ^ p * differentialDescent p A t)
      (𝓝[≠] 1) (𝓝 0) := by
  simpa only [ellipticCenter, specialSourceCoordinate_centerTwo] using
    differentialDescent_elliptic_growth hp hInv hA Elliptic.Kind.four

/-- The actual descended one-form coefficient with its two removable
values supplied by the punctured limits. -/
def oneFormExtension (A : ℍ → ℂ) : ℂ → ℂ :=
  patchTwo (differentialDescent 1 A) 0 1
    (limUnder (𝓝[≠] (0 : ℂ)) (differentialDescent 1 A))
    (limUnder (𝓝[≠] (1 : ℂ)) (differentialDescent 1 A))

@[simp] theorem oneFormExtension_zero (A : ℍ → ℂ) :
    oneFormExtension A 0 = limUnder (𝓝[≠] (0 : ℂ)) (differentialDescent 1 A) := by
  exact patchTwo_left _ _ _ (by norm_num)

@[simp] theorem oneFormExtension_one (A : ℍ → ℂ) :
    oneFormExtension A 1 = limUnder (𝓝[≠] (1 : ℂ)) (differentialDescent 1 A) :=
  patchTwo_right _ _ _ _ _

theorem oneFormExtension_eq_of_ne (A : ℍ → ℂ) {t : ℂ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    oneFormExtension A t = differentialDescent 1 A t :=
  patchTwo_eq_of_ne _ _ _ ht0 ht1

theorem oneFormExtension_eventuallyEq_nhdsNE (A : ℍ → ℂ) (c : ℂ) :
    oneFormExtension A =ᶠ[𝓝[≠] c] differentialDescent 1 A :=
  patchTwo_eventuallyEq_nhdsNE _ _ _ _ _ _

theorem oneFormExtension_eventuallyEq_cocompact (A : ℍ → ℂ) :
    oneFormExtension A =ᶠ[cocompact ℂ] differentialDescent 1 A :=
  patchTwo_eventuallyEq_cocompact _ _ _ _ _

/-- Entirety follows from the actual branching growth, not an extension
or boundedness assumption on the descended coefficient. -/
theorem oneFormExtension_entire {A : ℍ → ℂ}
    (hInv : IsInvariantDifferential 1 A) (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) :
    ∀ t, AnalyticAt ℂ (oneFormExtension A) t := by
  apply patchTwo_entire_of_sub_mul_tendsto_zero (by norm_num : (0 : ℂ) ≠ 1)
    (fun _ ht0 ht1 => differentialDescent_analytic hInv hA ht0 ht1)
  · simpa only [sub_zero, pow_one] using
      differentialDescent_growth_zero (by decide) hInv hA
  · simpa only [pow_one] using differentialDescent_growth_one (by decide) hInv hA

/-- The entire extension pulls back to the original one-form coefficient
divided by the derivative of the actual finite source coordinate. -/
theorem oneFormExtension_projection {A : ℍ → ℂ}
    (hInv : IsInvariantDifferential 1 A) {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    oneFormExtension A (specialSourceCoordinate z) =
      A z / scalarDeriv specialSourceCoordinate z := by
  have hmark := (specialSourceCoordinate_regular_iff z).mp hz
  rw [oneFormExtension_eq_of_ne A hmark.1 hmark.2,
    differentialDescent_projection hInv hz, pow_one]

/-- Clear the possible double poles of the actual descended cubic
coefficient at the two finite marked values. -/
def clearedCubicDescent (C : ℍ → ℂ) (t : ℂ) : ℂ :=
  t ^ 2 * (t - 1) ^ 2 * differentialDescent 3 C t

theorem clearedCubicDescent_analytic {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C)
    {t : ℂ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    AnalyticAt ℂ (clearedCubicDescent C) t :=
  ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 2)).mul
    (differentialDescent_analytic hInv hC ht0 ht1)

theorem clearedCubicDescent_growth_zero {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) :
    Tendsto (fun t : ℂ => (t - 0) * clearedCubicDescent C t)
      (𝓝[≠] 0) (𝓝 0) := by
  have hid : Tendsto (fun t : ℂ => t) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (differentialDescent_growth_zero (by decide) hInv hC).mul
    ((hid.sub_const 1).pow 2)
  simp only [zero_mul] at hlim
  convert hlim using 1
  ext t
  simp only [clearedCubicDescent, sub_zero]
  ring

theorem clearedCubicDescent_growth_one {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) :
    Tendsto (fun t : ℂ => (t - 1) * clearedCubicDescent C t)
      (𝓝[≠] 1) (𝓝 0) := by
  have hid : Tendsto (fun t : ℂ => t) (𝓝[≠] 1) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (differentialDescent_growth_one (by decide) hInv hC).mul (hid.pow 2)
  simp only [zero_mul] at hlim
  convert hlim using 1
  ext t
  simp only [clearedCubicDescent]
  ring

/-- The actual cleared cubic coefficient, patched only at its two
removable punctures and with their actual limit values. -/
def clearedCubicExtension (C : ℍ → ℂ) : ℂ → ℂ :=
  patchTwo (clearedCubicDescent C) 0 1
    (limUnder (𝓝[≠] (0 : ℂ)) (clearedCubicDescent C))
    (limUnder (𝓝[≠] (1 : ℂ)) (clearedCubicDescent C))

@[simp] theorem clearedCubicExtension_zero (C : ℍ → ℂ) :
    clearedCubicExtension C 0 = limUnder (𝓝[≠] (0 : ℂ)) (clearedCubicDescent C) := by
  exact patchTwo_left _ _ _ (by norm_num)

@[simp] theorem clearedCubicExtension_one (C : ℍ → ℂ) :
    clearedCubicExtension C 1 = limUnder (𝓝[≠] (1 : ℂ)) (clearedCubicDescent C) :=
  patchTwo_right _ _ _ _ _

theorem clearedCubicExtension_eq_of_ne (C : ℍ → ℂ) {t : ℂ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    clearedCubicExtension C t = clearedCubicDescent C t :=
  patchTwo_eq_of_ne _ _ _ ht0 ht1

theorem clearedCubicExtension_eventuallyEq_nhdsNE (C : ℍ → ℂ) (c : ℂ) :
    clearedCubicExtension C =ᶠ[𝓝[≠] c] clearedCubicDescent C :=
  patchTwo_eventuallyEq_nhdsNE _ _ _ _ _ _

theorem clearedCubicExtension_eventuallyEq_cocompact (C : ℍ → ℂ) :
    clearedCubicExtension C =ᶠ[cocompact ℂ] clearedCubicDescent C :=
  patchTwo_eventuallyEq_cocompact _ _ _ _ _

/-- Clearing the two finite double poles gives an entire function using
only invariance, holomorphy upstairs, and the proved elliptic branching. -/
theorem clearedCubicExtension_entire {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) :
    ∀ t, AnalyticAt ℂ (clearedCubicExtension C) t :=
  patchTwo_entire_of_sub_mul_tendsto_zero (by norm_num : (0 : ℂ) ≠ 1)
    (fun _ ht0 ht1 => clearedCubicDescent_analytic hInv hC ht0 ht1)
    (clearedCubicDescent_growth_zero hInv hC) (clearedCubicDescent_growth_one hInv hC)

theorem clearedCubicDescent_projection {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    clearedCubicDescent C (specialSourceCoordinate z) =
      specialSourceCoordinate z ^ 2 * (specialSourceCoordinate z - 1) ^ 2 * C z /
        scalarDeriv specialSourceCoordinate z ^ 3 := by
  rw [clearedCubicDescent, differentialDescent_projection hInv hz, mul_div_assoc]

/-- The entire cleared coefficient retains the exact cubic pullback
formula on the actual regular locus. -/
theorem clearedCubicExtension_projection {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    clearedCubicExtension C (specialSourceCoordinate z) =
      specialSourceCoordinate z ^ 2 * (specialSourceCoordinate z - 1) ^ 2 * C z /
        scalarDeriv specialSourceCoordinate z ^ 3 := by
  have hmark := (specialSourceCoordinate_regular_iff z).mp hz
  rw [clearedCubicExtension_eq_of_ne C hmark.1 hmark.2,
    clearedCubicDescent_projection hInv hz]

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
