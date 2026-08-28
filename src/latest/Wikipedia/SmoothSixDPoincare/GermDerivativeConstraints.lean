import Wikipedia.SmoothSixDPoincare.RelativeGermIsotopy

/-!
# The actual derivative inherits local coordinate and fixed-subspace constraints

Local equality of the projected map gives the derivative's projection law.
Restricting to the original fixed subspace gives its identity action there.
These identities are derived from the nonlinear coordinate germ, rather than
added as assumptions about a replacement frame.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a locally projection-preserving map preserves the same projection. -/
theorem fderiv_preserves_projection {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0)
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x) :
    Q.comp (fderiv ℝ f 0) = Q := by
  have heq : Q ∘ f =ᶠ[𝓝 (0 : E)] Q := by
    filter_upwards [hU.mem_nhds hzero] with x hx
    exact hQ x hx
  have hc : fderiv ℝ (Q ∘ f) 0 = Q.comp (fderiv ℝ f 0) :=
    (Q.hasFDerivAt.comp 0 hf.hasFDerivAt).fderiv
  exact hc.symm.trans (heq.fderiv_eq.trans Q.fderiv)

/-- The original derivative fixes every vector in a locally pointwise-fixed linear subspace. -/
theorem fderiv_fixes_subspace {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableAt ℝ f 0)
    (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∀ x ∈ S, fderiv ℝ f 0 x = x := by
  have heq : f ∘ (S.subtypeL : S → E) =ᶠ[𝓝 (0 : S)] (S.subtypeL : S → E) := by
    have hn : ∀ᶠ x : S in 𝓝 (0 : S), (x : E) ∈ U :=
      S.subtypeL.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hzero)
    filter_upwards [hn] with x hx
    exact hS x ⟨hx, x.property⟩
  have hc : fderiv ℝ (f ∘ (S.subtypeL : S → E)) (0 : S) =
      (fderiv ℝ f 0).comp S.subtypeL :=
    (hf.hasFDerivAt.comp (0 : S) S.subtypeL.hasFDerivAt).fderiv
  have hlinear : (fderiv ℝ f 0).comp S.subtypeL = S.subtypeL :=
    hc.symm.trans (heq.fderiv_eq.trans S.subtypeL.fderiv)
  intro x hx
  exact congrArg (fun A : S →L[ℝ] E => A ⟨x, hx⟩) hlinear

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
