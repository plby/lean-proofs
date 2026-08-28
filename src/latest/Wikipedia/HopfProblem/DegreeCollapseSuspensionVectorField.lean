import Wikipedia.HopfProblem.DegreeCollapseIsotopySuspension
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The actual smooth vector field of an isotopy suspension

Differentiate the genuine product diffeomorphism in the vertical direction.
Its conjugated translation flow solves this autonomous field for all real
times. The retained time coordinate has speed one. Common spatial support
and stationary time collars give compact support for its difference from
the original vertical field.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def suspensionField
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) (p : E × ℝ) : E × ℝ :=
  fderiv ℝ Ψ (Ψ.symm p) (0, 1)

theorem contDiff_suspensionField
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) :
    ContDiff ℝ ∞ (suspensionField Ψ) := by
  have hΨ : ContDiff ℝ ∞ (Ψ : (E × ℝ) → E × ℝ) := Ψ.contMDiff.contDiff
  have hΨinv : ContDiff ℝ ∞ (Ψ.symm : (E × ℝ) → E × ℝ) := Ψ.symm.contMDiff.contDiff
  exact ((hΨ.fderiv_right (by simp)).comp hΨinv).clm_apply contDiff_const

/-- The actual complete suspended flow solves the constructed autonomous field. -/
theorem hasDerivAt_suspensionFlow
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (p : E × ℝ) (t : ℝ) :
    HasDerivAt (fun s => suspensionFlow Ψ s p)
      (suspensionField Ψ (suspensionFlow Ψ t p)) t := by
  have hb : HasDerivAt (fun s : ℝ => ((Ψ.symm p).1, (Ψ.symm p).2 + s)) (0, 1) t :=
    (hasDerivAt_const t (Ψ.symm p).1).prodMk ((hasDerivAt_id t).const_add (Ψ.symm p).2)
  have hd := (Ψ.contMDiff.contDiff.differentiable (by simp)
    ((Ψ.symm p).1, (Ψ.symm p).2 + t)).hasFDerivAt.comp_hasDerivAt t hb
  change HasDerivAt (fun s => Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + s))
    (fderiv ℝ Ψ (Ψ.symm (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t))) (0, 1)) t
  rw [Ψ.symm_apply_apply]
  exact hd

theorem hasDerivAt_suspensionFlow_zero
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (p : E × ℝ) : HasDerivAt (fun s => suspensionFlow Ψ s p) (suspensionField Ψ p) 0 := by
  simpa only [(suspensionFlow Ψ).map_zero_apply] using hasDerivAt_suspensionFlow Ψ p 0

/-- The constructed field has exact positive speed in the retained coordinate. -/
theorem suspensionField_height
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : E × ℝ) : (suspensionField Ψ p).2 = 1 := by
  have hd : HasDerivAt (fun t => (suspensionFlow Ψ t p).2) (suspensionField Ψ p).2 0 :=
    (hasDerivAt_suspensionFlow_zero Ψ p).snd
  have heq : (fun t => (suspensionFlow Ψ t p).2) = fun t => p.2 + t :=
    funext (fun t => suspensionFlow_height Ψ hheight t p)
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_id (0 : ℝ)).const_add p.2)

/-- A stationary time germ gives precisely the original vertical field,
even when the slice diffeomorphism is not the identity. -/
theorem suspensionField_eq_vertical_of_stationary {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (p : E × ℝ)
    (hstationary : ∀ᶠ s in 𝓝 p.2, ∀ x, A (s, x) = A (p.2, x)) :
    suspensionField Ψ p = (0, 1) := by
  let q := Ψ.symm p
  have hq : Ψ q = p := Ψ.apply_symm_apply p
  have hqheight : q.2 = p.2 := by
    have hh := congrArg Prod.snd hq
    rw [hΨ] at hh
    exact hh
  have hqfirst : A (p.2, q.1) = p.1 := by
    have hh := congrArg Prod.fst hq
    rw [hΨ] at hh
    change A (q.2, q.1) = p.1 at hh
    rwa [hqheight] at hh
  have ht : Tendsto (fun t : ℝ => p.2 + t) (𝓝 0) (𝓝 p.2) := by
    have hc : Continuous (fun t : ℝ => p.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq : (fun t => suspensionFlow Ψ t p) =ᶠ[𝓝 0] (fun t => (p.1, p.2 + t)) := by
    filter_upwards [ht.eventually hstationary] with t hts
    change Ψ (q.1, q.2 + t) = (p.1, p.2 + t)
    rw [hΨ, hqheight, hts q.1, hqfirst]
  have hv : HasDerivAt (fun t : ℝ => (p.1, p.2 + t)) (0, 1) 0 :=
    (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2)
  exact ((hasDerivAt_suspensionFlow_zero Ψ p).congr_of_eventuallyEq heq.symm).unique hv

/-- Outside common spatial support, the entire flow trajectory is vertical. -/
theorem suspensionFlow_vertical_off_support {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E}
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : E × ℝ} (hp : p.1 ∉ K) (t : ℝ) :
    suspensionFlow Ψ t p = (p.1, p.2 + t) := by
  have hΨp : Ψ p = p := by rw [hΨ, hfix _ _ hp]
  have hinv : Ψ.symm p = p := by
    have hh := Ψ.symm_apply_apply p
    rwa [hΨp] at hh
  change Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t) = _
  rw [hinv, hΨ, hfix _ _ hp]

/-- Outside common spatial support, the field is exactly vertical. -/
theorem suspensionField_eq_vertical_off_support {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E}
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : E × ℝ} (hp : p.1 ∉ K) :
    suspensionField Ψ p = (0, 1) := by
  have heq : (fun t => suspensionFlow Ψ t p) = fun t => (p.1, p.2 + t) :=
    funext (fun t => suspensionFlow_vertical_off_support Ψ hΨ hfix hp t)
  have hd := hasDerivAt_suspensionFlow_zero Ψ p
  rw [heq] at hd
  exact hd.unique ((hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add p.2))

/-- A common compact spatial support and stationary exterior time germs
make the actual field perturbation compactly supported. -/
theorem hasCompactSupport_suspensionField_sub_vertical {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) {K : Set E} (hK : IsCompact K)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {a b : ℝ}
    (hstationary : ∀ s ∉ Icc a b, ∀ᶠ r in 𝓝 s, ∀ x, A (r, x) = A (s, x)) :
    HasCompactSupport (fun p => suspensionField Ψ p - (0, 1)) := by
  apply HasCompactSupport.intro (hK.prod (isCompact_Icc : IsCompact (Icc a b)))
  intro p hp
  have hv : suspensionField Ψ p = (0, 1) := by
    by_cases hx : p.1 ∈ K
    · have ht : p.2 ∉ Icc a b := fun h => hp ⟨hx, h⟩
      exact suspensionField_eq_vertical_of_stationary Ψ hΨ p (hstationary _ ht)
    · exact suspensionField_eq_vertical_off_support Ψ hΨ hfix hx
  rw [hv, sub_self]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
