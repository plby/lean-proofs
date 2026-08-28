import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Critical points of a map preserving the first coordinate

For a linear map preserving the first coordinate, surjectivity is equivalent
to surjectivity on the vertical slice. The derivative version applies this
to an actual differentiable map with first coordinate locally equal to the
source's first coordinate. This is the algebraic step used in Sard's
nonzero-rank reduction.
-/

open scoped Topology

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem surjective_triangular_iff_vertical (L : ℝ × E →L[ℝ] ℝ × F)
    (hfirst : ∀ v, (L v).1 = v.1) :
    Function.Surjective L ↔ Function.Surjective (fun v : E ↦ (L (0, v)).2) := by
  constructor
  · intro h w
    obtain ⟨⟨t, v⟩, hv⟩ := h (0, w)
    have ht : t = 0 := (hfirst (t, v)).symm.trans (congrArg Prod.fst hv)
    refine ⟨v, ?_⟩
    simpa only [ht] using congrArg Prod.snd hv
  · rintro h ⟨t, w⟩
    obtain ⟨v, hv⟩ := h (w - t • (L (1, 0)).2)
    change (L (0, v)).2 = w - t • (L (1, 0)).2 at hv
    refine ⟨(t, v), Prod.ext (hfirst (t, v)) ?_⟩
    have he : (t, v) = t • ((1 : ℝ), (0 : E)) + (0, v) := by ext <;> simp
    rw [he, map_add, map_smul]
    change t • (L (1, 0)).2 + (L (0, v)).2 = w
    rw [hv, ← add_sub_assoc, add_sub_cancel_left]

theorem surjective_fderiv_iff_vertical {g : ℝ × E → ℝ × F} {p : ℝ × E}
    (hg : DifferentiableAt ℝ g p)
    (hfirst : (fun q ↦ (g q).1) =ᶠ[𝓝 p] (Prod.fst : ℝ × E → ℝ)) :
    Function.Surjective (fderiv ℝ g p) ↔
      Function.Surjective (fderiv ℝ (fun v : E ↦ (g (p.1, v)).2) p.2) := by
  let D := fderiv ℝ g p
  have he : (ContinuousLinearMap.fst ℝ ℝ F).comp D = ContinuousLinearMap.fst ℝ ℝ E := by
    calc
      _ = fderiv ℝ (fun q ↦ (g q).1) p := hg.hasFDerivAt.fst.fderiv.symm
      _ = fderiv ℝ (Prod.fst : ℝ × E → ℝ) p := hfirst.fderiv_eq
      _ = _ := fderiv_fst
  have hDfirst : ∀ v, (D v).1 = v.1 :=
    fun v ↦ congrArg (fun L : ℝ × E →L[ℝ] ℝ ↦ L v) he
  have hslice : (fderiv ℝ (fun v : E ↦ (g (p.1, v)).2) p.2 : E → F) =
      fun v ↦ (D (0, v)).2 := by
    have hi : HasFDerivAt (fun v : E ↦ (p.1, v))
        (ContinuousLinearMap.inr ℝ ℝ E) p.2 := hasFDerivAt_prodMk_right p.1 p.2
    have hg' : HasFDerivAt (fun q : ℝ × E ↦ (g q).2)
        ((ContinuousLinearMap.snd ℝ ℝ F).comp D) (p.1, p.2) := hg.hasFDerivAt.snd
    have hs := hg'.comp p.2 hi
    funext v
    exact congrArg (fun L : E →L[ℝ] F ↦ L v) hs.fderiv
  rw [hslice]
  exact surjective_triangular_iff_vertical D hDfirst

end NoExoticSixSphere.Sard
