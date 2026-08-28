import Wikipedia.HopfProblem.ComplexRealManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Real regularity of the unchanged complex local maps

Only the scalar field of differentiation is restricted. The underlying
atlases, maps, partial inverses, and source and target sets are unchanged.
These lemmas apply in particular to the original toric and cusp coverings.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N] {n : ℕ∞ω}

/-- Complex regularity implies real regularity in the literal same charts. -/
theorem contMDiffWithinAt_real_of_complex {f : M → N} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f s x) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f s x := by
  rcases contMDiffWithinAt_iff.mp hf with ⟨hc, hd⟩
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

theorem contMDiffOn_real_of_complex {f : M → N} {s : Set M}
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) n f s) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) n f s :=
  fun x hx => contMDiffWithinAt_real_of_complex (hf x hx)

theorem contMDiff_real_of_complex {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) n f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f :=
  contMDiffOn_univ.mp (contMDiffOn_real_of_complex hf.contMDiffOn)

/-- A genuine complex partial diffeomorphism remains one over the real field. -/
def partialDiffeomorphReal (e : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) M N n) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_real_of_complex e.contMDiffOn_toFun
  contMDiffOn_invFun := contMDiffOn_real_of_complex e.contMDiffOn_invFun

@[simp] theorem partialDiffeomorphReal_apply
    (e : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) M N n) (x : M) :
    partialDiffeomorphReal e x = e x := rfl

@[simp] theorem partialDiffeomorphReal_symm_apply
    (e : PartialDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) M N n) (y : N) :
    (partialDiffeomorphReal e).symm y = e.symm y := rfl

theorem isLocalDiffeomorphAt_real_of_complex {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f x := by
  obtain ⟨e, hx, he⟩ := hf
  exact ⟨partialDiffeomorphReal e, hx, he⟩

theorem isLocalDiffeomorph_real_of_complex {f : M → N}
    (hf : IsLocalDiffeomorph 𝓘(ℂ, E) 𝓘(ℂ, F) n f) :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) n f :=
  fun x => isLocalDiffeomorphAt_real_of_complex (hf x)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
