import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Analytic pullback of actual alternating covectors

Pullback of a continuous alternating covector is analytic in the linear
map. We prove this for the actual normed spaces of alternating maps, by
factoring the polynomial multilinear pullback through a continuous linear
retraction. No formal tensor symbols replace the actual covectors.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicAlternatingMaps

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (p : ℕ)

local instance multilinear_finite :
    FiniteDimensional ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin p => E) F) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear :
      ContinuousMultilinearMap ℂ (fun _ : Fin p => E) F →ₗ[ℂ] _)
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- The genuine continuous inclusion of alternating maps into multilinear maps. -/
abbrev inclusion :
    (E [⋀^Fin p]→L[ℂ] F) →L[ℂ] ContinuousMultilinearMap ℂ (fun _ : Fin p => E) F :=
  ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℂ

/-- A continuous linear retraction of the actual multilinear-map space
onto its alternating subspace. Only its left-inverse property is used. -/
def retraction :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => E) F →L[ℂ] (E [⋀^Fin p]→L[ℂ] F) :=
  (inclusion E F p).toLinearMap.leftInverse.toContinuousLinearMap

@[simp] theorem retraction_inclusion (a : E [⋀^Fin p]→L[ℂ] F) :
    retraction E F p (inclusion E F p a) = a := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr ContinuousAlternatingMap.toContinuousMultilinearMap_injective) a

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G]
  [FiniteDimensional ℂ G]

/-- Polynomial pullback on actual continuous multilinear maps. -/
def multilinearPullback (A : E →L[ℂ] G) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p => G) F →L[ℂ]
      ContinuousMultilinearMap ℂ (fun _ : Fin p => E) F :=
  ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
    (fun _ : Fin p => E) (fun _ : Fin p => G) F (fun _ => A)

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G] in
theorem multilinearPullback_contDiff :
    ContDiff ℂ ω (multilinearPullback E F p G) :=
  (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
    (fun _ : Fin p => E) (fun _ : Fin p => G) F).contDiff.comp
      (contDiff_pi.mpr fun _ => contDiff_id)

omit [FiniteDimensional ℂ G] in
theorem pullback_eq_retraction (A : E →L[ℂ] G) :
    (ContinuousAlternatingMap.compContinuousLinearMapCLM A :
      (G [⋀^Fin p]→L[ℂ] F) →L[ℂ] (E [⋀^Fin p]→L[ℂ] F)) =
      (retraction E F p).comp
        ((multilinearPullback E F p G A).comp (inclusion G F p)) := by
  apply ContinuousLinearMap.ext
  intro a
  exact (retraction_inclusion E F p (a.compContinuousLinearMap A)).symm

omit [FiniteDimensional ℂ G] in
/-- The actual alternating-covector pullback operator is complex analytic. -/
theorem pullback_contDiff :
    ContDiff ℂ ω
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E →L[ℂ] G) → (G [⋀^Fin p]→L[ℂ] F) →L[ℂ] (E [⋀^Fin p]→L[ℂ] F)) := by
  have h : ContDiff ℂ ω (fun A : E →L[ℂ] G =>
      (retraction E F p).comp
        ((multilinearPullback E F p G A).comp (inclusion G F p))) :=
    contDiff_const.clm_comp
      ((multilinearPullback_contDiff E F p G).clm_comp contDiff_const)
  simpa only [← pullback_eq_retraction] using h

omit [FiniteDimensional ℂ G] in
/-- Joint analyticity in the covector and the genuine linear map. -/
theorem pullback_apply_contDiff :
    ContDiff ℂ ω (fun q : (G [⋀^Fin p]→L[ℂ] F) × (E →L[ℂ] G) =>
      q.1.compContinuousLinearMap q.2) :=
  ((pullback_contDiff E F p G).comp contDiff_snd).clm_apply contDiff_fst

end Wikipedia.HopfProblem.HolomorphicAlternatingMaps
