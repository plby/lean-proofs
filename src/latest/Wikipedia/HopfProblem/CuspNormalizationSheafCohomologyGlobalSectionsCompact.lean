import Wikipedia.HopfProblem.HolomorphicFunctionSheafGlobal
import Mathlib.Geometry.Manifold.Complex

/-!
# Actual holomorphic global sections on a compact connected manifold

The compact maximum principle proves constancy of the actual section
functions. Evaluation, with literal constant functions as inverse, is
therefore a complex-algebra equivalence.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open HolomorphicFunctionSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Actual constant functions supply every value at the chosen point. -/
theorem compact_global_eval_surjective (x : M) :
    Function.Surjective (globalSectionsEval I M x) := by
  intro c
  exact ⟨algebraMap ℂ (GlobalSections I M) c, rfl⟩

variable [I.Boundaryless] [IsManifold I 1 M] [CompactSpace M] [PreconnectedSpace M]

/-- The values of an actual global holomorphic section are equal. -/
theorem compact_global_apply_eq (s : GlobalSections I M) (x y : M) :
    s (toTopOpen M x) = s (toTopOpen M y) :=
  ((globalSectionsAlgEquiv I M s).contMDiff.mdifferentiable (by simp)).apply_eq_of_compactSpace x y

/-- Evaluation of actual global sections is injective by the compact
maximum principle on the actual manifold. -/
theorem compact_global_eval_injective (x : M) :
    Function.Injective (globalSectionsEval I M x) := by
  intro f g h
  apply ContMDiffMap.ext
  intro y
  exact (compact_global_apply_eq I M f y x).trans
    (h.trans (compact_global_apply_eq I M g x y))

/-- Evaluation is an algebra equivalence on actual global sections. -/
def compactGlobalEvalEquiv (x : M) : GlobalSections I M ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofBijective (globalSectionsEval I M x)
    ⟨compact_global_eval_injective I M x, compact_global_eval_surjective I M x⟩

@[simp] theorem compactGlobalEvalEquiv_apply (x : M) (s : GlobalSections I M) :
    compactGlobalEvalEquiv I M x s = s (toTopOpen M x) := rfl

/-- The inverse is the literal constant sheaf section. -/
@[simp] theorem compactGlobalEvalEquiv_symm_apply (x : M) (c : ℂ) :
    (compactGlobalEvalEquiv I M x).symm c = algebraMap ℂ (GlobalSections I M) c := by
  apply (compactGlobalEvalEquiv I M x).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
