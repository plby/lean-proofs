import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalk
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRingEvaluation

/-!
# The analytic-germ comparison preserves genuine stalk evaluation

The categorical evaluation map and evaluation on ordinary analytic germs
agree through the proved stalk ring isomorphism.  The proof tests these
actual ring maps on the genuine local-section representatives of the
stalk colimit.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The ring isomorphism from the categorical stalk to actual analytic
germs commutes with the two independently constructed evaluations. -/
theorem eval_comp_modelStalkEquiv (a : E) :
    (Germs.eval a).comp (modelStalkEquiv a).toRingHom = stalkEval 𝓘(ℂ, E) E a := by
  apply RingHom.ext
  intro φ
  obtain ⟨U, ha, f, rfl⟩ := (presheaf 𝓘(ℂ, E) E).exists_germ_eq φ
  exact (eval_modelStalkEquiv_germ a U ha f).trans
    (stalkEval_germ 𝓘(ℂ, E) E U a ha f).symm

@[simp] theorem eval_modelStalkEquiv (a : E)
    (φ : (presheaf 𝓘(ℂ, E) E).stalk a) :
    Germs.eval a (modelStalkEquiv a φ) = stalkEval 𝓘(ℂ, E) E a φ :=
  congrArg (fun f => f φ) (eval_comp_modelStalkEquiv a)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
