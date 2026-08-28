import Wikipedia.NoExoticSixSphere.OrthogonalExponentialStationarity
import Wikipedia.NoExoticSixSphere.SmoothCurveExtension

/-!
# Boundary first variation for exponential segments

The velocity at either endpoint pairs with the actual variation of that
endpoint. The endpoints may vary: no fixed-endpoint hypothesis is imposed.
Equalities of endpoint curves are needed only near the parameter in question.
-/

open scoped ContDiff Topology
open Filter

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  HilbertSchmidt OrthogonalPathEnergy OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ}

noncomputable def endpointBody (γ : ℝ → OrthogonalOperators n) (s : ℝ) :
    Vector n →L[ℝ] Vector n :=
  (inverse (γ s)).1.1.comp (deriv (fun r ↦ (γ r).1.1) s)

theorem variation_eq_endpointBody {a : ℝ × ℝ → OrthogonalOperators n}
    (ha : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a))
    (s t : ℝ) (γ : ℝ → OrthogonalOperators n)
    (heq : (fun r ↦ a (r, t)) =ᶠ[𝓝 s] γ) :
    variation a (s, t) = endpointBody γ s := by
  have hco : (fun r ↦ (γ r).1.1) =ᶠ[𝓝 s]
      (fun r ↦ OrthogonalMaurerCartan.operator a (r, t)) := by
    filter_upwards [heq] with r hr
    exact congrArg (fun b : OrthogonalOperators n ↦ b.1.1) hr.symm
  have hd := (hasDerivAt_first ((ha.differentiable (by simp)) (s, t))).congr_of_eventuallyEq hco
  simp only [variation, endpointBody, heq.eq_of_nhds, hd.deriv]

theorem hasDerivAt_energy_boundary_of_exponential
    {a : ℝ × ℝ → OrthogonalOperators n}
    (ha : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a))
    (s l u : ℝ) (b : OrthogonalOperators n) (K : SkewOperators n)
    (hpath : ∀ t, a (s, t) = b * exp (t • K)) :
    HasDerivAt (fun r ↦ energy (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) l u)
      (2 * (innerForm K (variation a (s, u)) - innerForm K (variation a (s, l)))) s := by
  have hv := velocity_of_exponential_slice ha s b K hpath
  have hz (A : Vector n →L[ℝ] Vector n) : innerForm 0 A = 0 := by simp [innerForm]
  simpa only [second_velocity_eq_zero_of_constant ha s K hv, hv, hz,
    intervalIntegral.integral_zero, sub_zero] using hasDerivAt_energy_boundary ha s l u

theorem contDiff_exponentialSegment_family
    {α : ℝ → OrthogonalOperators n} {K : ℝ → SkewOperators n}
    (hα : ContDiff ℝ ∞ (fun r ↦ (α r).1.1)) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (α p.1 * exp (p.2 • K p.1)).1.1) := by
  have harg : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.2 • K p.1) :=
    contDiff_snd.smul (hK.comp contDiff_fst)
  have hexp : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (exp (p.2 • K p.1)).1.1) :=
    ContDiff.comp (f := fun p : ℝ × ℝ ↦ p.2 • K p.1)
      (g := fun X : SkewOperators n ↦ (exp X).1.1) contDiff_exp_operator harg
  exact (hα.comp contDiff_fst).clm_comp hexp

/-- The squared logarithm derivative is the difference of endpoint pairings. -/
theorem hasDerivAt_squareNorm_of_endpoints
    {α β : ℝ → OrthogonalOperators n} {K : ℝ → SkewOperators n}
    (hα : ContDiff ℝ ∞ (fun r ↦ (α r).1.1)) (hK : ContDiff ℝ ∞ K)
    (s : ℝ) (hend : (fun r ↦ α r * exp (K r)) =ᶠ[𝓝 s] β) :
    HasDerivAt (fun r ↦ squareNorm (K r : Vector n →L[ℝ] Vector n))
      (2 * (innerForm (K s) (endpointBody β s) -
        innerForm (K s) (endpointBody α s))) s := by
  let a : ℝ × ℝ → OrthogonalOperators n := fun p ↦ α p.1 * exp (p.2 • K p.1)
  have ha : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a) :=
    contDiff_exponentialSegment_family hα hK
  have hzero : (fun r ↦ a (r, 0)) =ᶠ[𝓝 s] α := by
    filter_upwards [] with r
    simp only [a, zero_smul, exp_zero, mul_one]
  have hone : (fun r ↦ a (r, 1)) =ᶠ[𝓝 s] β := by
    simpa only [a, one_smul] using hend
  have hd := hasDerivAt_energy_boundary_of_exponential ha s 0 1 (α s) (K s) (fun _ ↦ rfl)
  rw [variation_eq_endpointBody ha s 1 β hone, variation_eq_endpointBody ha s 0 α hzero] at hd
  have he : (fun r ↦ energy (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) 0 1) =
      (fun r ↦ squareNorm (K r : Vector n →L[ℝ] Vector n)) := by
    funext r
    simpa only [sub_zero, one_mul] using energy_left_exp (α r) (K r) 0 1
  rwa [he] at hd

/-- Only local smoothness of the logarithm is needed for the boundary formula. -/
theorem hasDerivAt_squareNorm_of_local_endpoints
    {α β : ℝ → OrthogonalOperators n} {K : ℝ → SkewOperators n}
    {U : Set ℝ} {s : ℝ}
    (hα : ContDiff ℝ ∞ (fun r ↦ (α r).1.1))
    (hU : IsOpen U) (hs : s ∈ U) (hK : ContDiffOn ℝ ∞ K U)
    (hend : (fun r ↦ α r * exp (K r)) =ᶠ[𝓝 s] β) :
    HasDerivAt (fun r ↦ squareNorm (K r : Vector n →L[ℝ] Vector n))
      (2 * (innerForm (K s) (endpointBody β s) -
        innerForm (K s) (endpointBody α s))) s := by
  obtain ⟨G, hG, heq⟩ := SmoothCurveExtension.exists_global hU hs hK
  have hGend : (fun r ↦ α r * exp (G r)) =ᶠ[𝓝 s] β := by
    filter_upwards [heq, hend] with r hr he
    rwa [hr]
  have hd := hasDerivAt_squareNorm_of_endpoints hα hG s hGend
  rw [heq.eq_of_nhds] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [heq] with r hr
  rw [hr]

end NoExoticSixSphere.OrthogonalFirstVariation
