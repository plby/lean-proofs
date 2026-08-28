import Wikipedia.SmoothSixDPoincare.MorsePerturbation
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Stability of nondegenerate critical points on a compact set

A smooth parameter family has jointly continuous first and second spatial
derivatives. The absence of degenerate critical points over a fixed compact
set is consequently an open condition on its parameters.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

section CompactQuantifier

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

/-- Universal quantification over a compact set preserves an open condition on parameters. -/
theorem isOpen_forall_mem_compact {K : Set X} (hK : IsCompact K)
    {U : Set (P × X)} (hU : IsOpen U) :
    IsOpen {p : P | ∀ x ∈ K, (p, x) ∈ U} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let B : Set (P × K) := {q | (q.1, (q.2 : X)) ∉ U}
  have hB : IsClosed B := hU.isClosed_compl.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hproj : IsClosed ((Prod.fst : P × K → P) '' B) :=
    isClosedMap_fst_of_compactSpace B hB
  have heq : {p : P | ∀ x ∈ K, (p, x) ∈ U} = ((Prod.fst : P × K → P) '' B)ᶜ := by
    ext p
    constructor
    · intro hp ⟨⟨q, x⟩, hbad, hq⟩
      change q = p at hq
      subst q
      exact hbad (hp x x.property)
    · intro hp x hx
      by_contra hbad
      exact hp ⟨(p, ⟨x, hx⟩), hbad, rfl⟩
  rw [heq]
  exact hproj.isOpen_compl

end CompactQuantifier

section DerivativeFamily

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spatial differentiation preserves smooth dependence on both the parameter and point. -/
theorem contDiff_spatialDerivative {f : P → E → F}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × E => fderiv ℝ (f q.1) q.2) := by
  let g : (P × E) → E → F := fun q x => f q.1 x
  have hg : ContDiff ℝ ∞ (Function.uncurry g) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hg.fderiv contDiff_snd (by simp)

end DerivativeFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Express invertibility of a genuine Hessian by a determinant in the chosen dual coordinates. -/
theorem bijective_hessian_iff (A : E →L[ℝ] (E →L[ℝ] ℝ)) :
    Function.Bijective A ↔ (dualEquiv.symm.toContinuousLinearMap.comp A).det ≠ 0 := by
  rw [← RegularValues.bijective_iff_det_ne_zero]
  constructor
  · intro hA
    exact dualEquiv.symm.bijective.comp hA
  · intro hA
    have heq : (fun x : E => dualEquiv ((dualEquiv.symm.toContinuousLinearMap.comp A) x)) =
        A := by
      funext x
      exact dualEquiv.apply_symm_apply _
    rw [← heq]
    exact dualEquiv.bijective.comp hA

/-- Nondegeneracy of all critical points in a prescribed set, using the actual derivatives. -/
def IsMorseOn (f : E → ℝ) (K : Set E) : Prop :=
  ∀ x ∈ K, fderiv ℝ f x = 0 → Function.Bijective (fderiv ℝ (fderiv ℝ f) x)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- For a smooth family, being Morse on a fixed compact set is open in the parameter. -/
theorem isOpen_isMorseOn {f : P → E → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {K : Set E} (hK : IsCompact K) :
    IsOpen {p : P | IsMorseOn (f p) K} := by
  have h₁ := contDiff_spatialDerivative hf
  have h₂ := contDiff_spatialDerivative (f := fun p x => fderiv ℝ (f p) x) h₁
  let U : Set (P × E) := {q | fderiv ℝ (f q.1) q.2 ≠ 0 ∨
    (dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det ≠ 0}
  have hdet : Continuous (fun q : P × E =>
      (dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ (f q.1)) q.2)).det) :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp h₂.continuous)
  have hU : IsOpen U :=
    (isClosed_eq h₁.continuous continuous_const).isOpen_compl.union
      (isClosed_eq hdet continuous_const).isOpen_compl
  have heq : {p : P | IsMorseOn (f p) K} = {p : P | ∀ x ∈ K, (p, x) ∈ U} := by
    ext p
    simp only [IsMorseOn, mem_ofPred_eq, U, bijective_hessian_iff]
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    exact imp_iff_not_or
  rw [heq]
  exact isOpen_forall_mem_compact hK hU

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
