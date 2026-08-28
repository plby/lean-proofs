import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsExtensions
import Mathlib.Analysis.Meromorphic.Order

/-!
# Global one-form and meromorphic cubic descent

The entire one-form coefficient pulls back to the original coefficient
on the whole upper half-plane, including the elliptic fibres. This follows
from the proved density of the regular locus and continuity.

The cubic coefficient is an actual meromorphic function on the finite
plane. Its only possible poles are the two marked points, with order at
most two. Its literal quotient formula is asserted only on the regular
locus; total division at a pole does not express a differential pullback.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods SpecialPeriods.Triangle

/-- The actual entire one-form extension pulls back correctly even at
the elliptic fibres, by continuity from the dense regular locus. -/
theorem oneFormExtension_pullback {A : ℍ → ℂ}
    (hInv : IsInvariantDifferential 1 A) (hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω A) (z : ℍ) :
    oneFormExtension A (specialSourceCoordinate z) *
      scalarDeriv specialSourceCoordinate z = A z := by
  have hF : Continuous (oneFormExtension A) :=
    continuous_iff_continuousAt.mpr fun t => (oneFormExtension_entire hInv hA t).continuousAt
  have hleft : Continuous (fun w : ℍ => oneFormExtension A (specialSourceCoordinate w) *
      scalarDeriv specialSourceCoordinate w) :=
    (hF.comp specialSourceCoordinate_holomorphic.continuous).mul
      (scalarDeriv_holomorphic specialSourceCoordinate_holomorphic).continuous
  have he : triangleRegularLocus ⊆ {w : ℍ |
      oneFormExtension A (specialSourceCoordinate w) *
        scalarDeriv specialSourceCoordinate w = A w} := by
    intro w hw
    change oneFormExtension A (specialSourceCoordinate w) *
      scalarDeriv specialSourceCoordinate w = A w
    rw [oneFormExtension_projection hInv hw]
    exact div_mul_cancel₀ _ (specialSourceCoordinate_scalarDeriv_ne_zero_of_regular hw)
  have hc : closure triangleRegularLocus ⊆ {w : ℍ |
      oneFormExtension A (specialSourceCoordinate w) *
        scalarDeriv specialSourceCoordinate w = A w} :=
    closure_minimal he (isClosed_eq hleft hA.continuous)
  rw [triangleRegularLocus_dense.closure_eq] at hc
  exact hc (mem_univ z)

/-- The actual meromorphic cubic coefficient in the finite source
coordinate, formed from its proved entire cleared coefficient. -/
def cubicMeromorphicDescent (C : ℍ → ℂ) (t : ℂ) : ℂ :=
  clearedCubicExtension C t / (t ^ 2 * (t - 1) ^ 2)

theorem cubicMeromorphicDescent_meromorphicAt {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) (t : ℂ) :
    MeromorphicAt (cubicMeromorphicDescent C) t :=
  (clearedCubicExtension_entire hInv hC t).meromorphicAt.div
    (((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 2)).meromorphicAt)

theorem cubicMeromorphicDescent_analytic {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C)
    {t : ℂ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    AnalyticAt ℂ (cubicMeromorphicDescent C) t :=
  (clearedCubicExtension_entire hInv hC t).div
    ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 2))
    (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 (sub_ne_zero.mpr ht1)))

/-- The meromorphic cubic coefficient has at worst a double pole at the
actual first marked value. -/
theorem cubicMeromorphicDescent_order_zero_ge {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) :
    (-2 : WithTop ℤ) ≤ meromorphicOrderAt (cubicMeromorphicDescent C) 0 := by
  have hden : meromorphicOrderAt (fun t : ℂ => t ^ 2 * (t - 1) ^ 2) 0 = 2 := by
    apply (meromorphicOrderAt_eq_int_iff (by fun_prop)).2
    refine ⟨fun t : ℂ => (t - 1) ^ 2, by fun_prop, by norm_num, ?_⟩
    exact Filter.Eventually.of_forall (by intro t; simp [smul_eq_mul])
  have hnum := clearedCubicExtension_entire hInv hC 0
  change (-2 : WithTop ℤ) ≤ meromorphicOrderAt
    (clearedCubicExtension C / fun t : ℂ => t ^ 2 * (t - 1) ^ 2) 0
  rw [meromorphicOrderAt_div hnum.meromorphicAt (by fun_prop), hden]
  simpa [sub_eq_add_neg, add_comm] using
    add_le_add_right hnum.meromorphicOrderAt_nonneg (-2 : WithTop ℤ)

/-- The same actual order bound holds at the second marked value. -/
theorem cubicMeromorphicDescent_order_one_ge {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) (hC : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω C) :
    (-2 : WithTop ℤ) ≤ meromorphicOrderAt (cubicMeromorphicDescent C) 1 := by
  have hden : meromorphicOrderAt (fun t : ℂ => t ^ 2 * (t - 1) ^ 2) 1 = 2 := by
    apply (meromorphicOrderAt_eq_int_iff (by fun_prop)).2
    refine ⟨fun t : ℂ => t ^ 2, by fun_prop, by norm_num, ?_⟩
    exact Filter.Eventually.of_forall (by intro t; simp [smul_eq_mul, mul_comm])
  have hnum := clearedCubicExtension_entire hInv hC 1
  change (-2 : WithTop ℤ) ≤ meromorphicOrderAt
    (clearedCubicExtension C / fun t : ℂ => t ^ 2 * (t - 1) ^ 2) 1
  rw [meromorphicOrderAt_div hnum.meromorphicAt (by fun_prop), hden]
  simpa [sub_eq_add_neg, add_comm] using
    add_le_add_right hnum.meromorphicOrderAt_nonneg (-2 : WithTop ℤ)

/-- The meromorphic function agrees with the genuine scalar descent
off the two marked values. -/
theorem cubicMeromorphicDescent_eq_of_ne (C : ℍ → ℂ) {t : ℂ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    cubicMeromorphicDescent C t = differentialDescent 3 C t := by
  rw [cubicMeromorphicDescent, clearedCubicExtension_eq_of_ne C ht0 ht1,
    clearedCubicDescent]
  apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 ht0)
    (pow_ne_zero 2 (sub_ne_zero.mpr ht1)))).mpr
  exact mul_comm _ _

/-- The actual regular pullback coefficient. No literal value at a
meromorphic pole is used in this identity. -/
theorem cubicMeromorphicDescent_projection {C : ℍ → ℂ}
    (hInv : IsInvariantDifferential 3 C) {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    cubicMeromorphicDescent C (specialSourceCoordinate z) =
      C z / scalarDeriv specialSourceCoordinate z ^ 3 := by
  have hmark := (specialSourceCoordinate_regular_iff z).mp hz
  rw [cubicMeromorphicDescent_eq_of_ne C hmark.1 hmark.2,
    differentialDescent_projection hInv hz]

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
