import Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct
import Mathlib.Dynamics.Flow

/-!
# Actual suspension of a smooth coordinate isotopy

Retaining time turns the given smooth family of diffeomorphisms into one
genuine product diffeomorphism, with a proved smooth inverse. Conjugating
vertical translation constructs a complete smooth flow with exact time
translation and the prescribed transition from the zero to the one slice.
The associated native field and localization are subsequent steps.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete time-retaining coordinate change, with its native smooth inverse. -/
theorem exists_isotopy_suspension_diffeomorph [FiniteDimensional ℝ E]
    {A : ℝ × E → E} (hA : ContDiff ℝ ∞ A)
    (hslice : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = A (t, x)) :
    ∃ Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞,
      ∀ p, Ψ p = (A (p.2, p.1), p.2) := by
  have hF : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => A (p.2, p.1)) :=
    hA.contMDiff.comp (contMDiff_snd.prodMk_space contMDiff_fst)
  let D := FiberwiseDiffeomorph.diffeomorph hF hslice
  let V := PartialChart.vectorProduct E ℝ
  exact ⟨(V.trans D).trans V.symm, fun p => rfl⟩

def suspensionFlow
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) : Flow ℝ (E × ℝ) where
  toFun t p := Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)
  cont' := by
    apply Ψ.continuous.comp
    exact (Ψ.symm.continuous.comp continuous_snd).fst.prodMk
      ((Ψ.symm.continuous.comp continuous_snd).snd.add continuous_fst)
  map_zero' p := by simp only [add_zero, Prod.mk.eta, Ψ.apply_symm_apply]
  map_add' s t p := by
    simp only [Ψ.symm_apply_apply]
    congr 1
    apply Prod.ext
    · rfl
    · ring

theorem suspensionFlow_chart
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (t : ℝ) (p : E × ℝ) : suspensionFlow Ψ t (Ψ p) = Ψ (p.1, p.2 + t) := by
  change Ψ ((Ψ.symm (Ψ p)).1, (Ψ.symm (Ψ p)).2 + t) = _
  rw [Ψ.symm_apply_apply]

theorem contDiff_suspensionFlow
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞) :
    ContDiff ℝ ∞ (fun q : ℝ × (E × ℝ) => suspensionFlow Ψ q.1 q.2) := by
  have hΨ : ContDiff ℝ ∞ (Ψ : (E × ℝ) → E × ℝ) := Ψ.contMDiff.contDiff
  have hΨinv : ContDiff ℝ ∞ (Ψ.symm : (E × ℝ) → E × ℝ) := Ψ.symm.contMDiff.contDiff
  exact hΨ.comp (((hΨinv.comp contDiff_snd).fst).prodMk
    (((hΨinv.comp contDiff_snd).snd).add contDiff_fst))

/-- The suspended flow advances the actual retained coordinate by exactly elapsed time. -/
theorem suspensionFlow_height
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (t : ℝ) (p : E × ℝ) :
    (suspensionFlow Ψ t p).2 = p.2 + t := by
  have hinv : (Ψ.symm p).2 = p.2 := by
    have hh := hheight (Ψ.symm p)
    rw [Ψ.apply_symm_apply] at hh
    exact hh.symm
  change (Ψ ((Ψ.symm p).1, (Ψ.symm p).2 + t)).2 = _
  rw [hheight, hinv]

/-- The prescribed isotopy endpoint is the exact slice-to-slice transition of a complete flow. -/
theorem suspensionFlow_endpoint {A : ℝ × E → E}
    (Ψ : Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞)
    (hΨ : ∀ p, Ψ p = (A (p.2, p.1), p.2)) (hA0 : ∀ x, A (0, x) = x) (x : E) :
    suspensionFlow Ψ 1 (x, 0) = (A (1, x), 1) := by
  have hstart : Ψ (x, (0 : ℝ)) = (x, 0) := by rw [hΨ, hA0]
  rw [← hstart, suspensionFlow_chart, zero_add, hΨ]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
