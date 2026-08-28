import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationModel
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar quadratic coordinates at the two cubic critical points

The cubic difference factors as a square times a positive affine factor
near either endpoint. Taking its positive square root gives an actual
smooth local coordinate with nonzero derivative at the endpoint.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

def endpointCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) * Real.sqrt (a + e * (s - e * a) / 3)

def endpointDomain (a e : ℝ) : Set ℝ := {s | 0 < a + e * (s - e * a) / 3}

theorem endpointDomain_open (a e : ℝ) : IsOpen (endpointDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

theorem endpoint_mem_domain {a : ℝ} (ha : 0 < a) (e : ℝ) :
    e * a ∈ endpointDomain a e := by
  simpa [endpointDomain] using ha

theorem endpointCoordinate_center (a e : ℝ) : endpointCoordinate a e (e * a) = 0 := by
  simp [endpointCoordinate]

theorem contDiffOn_endpointCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointCoordinate a e) (endpointDomain a e) := by
  intro s hs
  have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => t - e * a) s :=
    contDiffAt_id.sub contDiffAt_const
  exact (hlin.mul ((contDiffAt_const.add
    ((contDiffAt_const.mul hlin).div_const 3)).sqrt (ne_of_gt hs))).contDiffWithinAt

theorem hasDerivAt_endpointCoordinate {a : ℝ} (ha : 0 < a) (e : ℝ) :
    HasDerivAt (endpointCoordinate a e) (Real.sqrt a) (e * a) := by
  have hd := ((hasDerivAt_id (e * a)).sub_const (e * a)).mul
    ((((hasDerivAt_id (e * a)).sub_const (e * a)).const_mul e).div_const 3 |>.const_add a
      |>.sqrt (by simpa using ha.ne'))
  convert! hd using 1 <;> simp [endpointCoordinate]

theorem cubic_endpoint_square {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (he : e ^ 2 = 1)
    {p : Model m} (hp : p.1 ∈ endpointDomain a e) :
    cubic σ (-(a ^ 2)) p = cubic σ (-(a ^ 2)) (e * a, 0) +
      e * endpointCoordinate a e p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 := by
  simp only [cubic, endpointCoordinate, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero, add_zero, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

theorem exists_endpoint_scalar_chart {a : ℝ} (ha : 0 < a) (e : ℝ) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ Φ.source ∧ Φ.source ⊆ endpointDomain a e ∧
      (Φ : ℝ → ℝ) = endpointCoordinate a e ∧ Φ (e * a) = 0 := by
  have hd := (hasDerivAt_endpointCoordinate ha e).hasFDerivAt
  have hi : Function.Injective (fderiv ℝ (endpointCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * Real.sqrt a = y * Real.sqrt a at hxy
    exact mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne' hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointCoordinate a e) (e * a)).toLinearMap hi).toContinuousLinearEquiv
  obtain ⟨Φ, hp, hsub, hΦ⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    (endpointDomain_open a e) (endpoint_mem_domain ha e) (contDiffOn_endpointCoordinate a e)
    ⟨A, rfl⟩
  exact ⟨Φ, hp, hsub, hΦ, by rw [hΦ, endpointCoordinate_center]⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
