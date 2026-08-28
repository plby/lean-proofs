import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Biholomorphisms determined by ambient fibre immersions

A homeomorphism between two complex manifolds is biholomorphic whenever it
identifies their genuine analytic immersions into a common ambient manifold.
The source and ambient complex model spaces may have arbitrary dimensions.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.EmbeddedFibre

variable {E V X Y M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace X] [ChartedSpace E X]
    [TopologicalSpace Y] [ChartedSpace E Y]
    [TopologicalSpace M] [ChartedSpace V M]
    (e : X ≃ₜ Y) {f : X → M} {g : Y → M}
    (hf : Manifold.IsImmersion (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω f)
    (hg : Manifold.IsImmersion (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω g)
    (hcomm : ∀ x, g (e x) = f x)

def biholomorphOfHomeomorph :
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) X Y ω where
  toEquiv := e.toEquiv
  contMDiff_toFun := (ContMDiff.iff_comp_isImmersion hg).mpr
    ⟨e.continuous, hf.contMDiff.congr hcomm⟩
  contMDiff_invFun := (ContMDiff.iff_comp_isImmersion hf).mpr
    ⟨e.symm.continuous, hg.contMDiff.congr (fun y => by
      change f (e.symm y) = g y
      rw [← hcomm, e.apply_symm_apply])⟩

@[simp] theorem biholomorphOfHomeomorph_apply (x : X) :
    biholomorphOfHomeomorph e hf hg hcomm x = e x := rfl

@[simp] theorem biholomorphOfHomeomorph_symm_apply (y : Y) :
    (biholomorphOfHomeomorph e hf hg hcomm).symm y = e.symm y := rfl

@[simp] theorem biholomorphOfHomeomorph_coe :
    (biholomorphOfHomeomorph e hf hg hcomm : X → Y) = e := rfl

include hf hg hcomm in
theorem homeomorph_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω e :=
  (biholomorphOfHomeomorph e hf hg hcomm).contMDiff

include hf hg hcomm in
theorem homeomorph_symm_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω e.symm :=
  (biholomorphOfHomeomorph e hf hg hcomm).symm.contMDiff

end Wikipedia.HopfProblem.EmbeddedFibre
