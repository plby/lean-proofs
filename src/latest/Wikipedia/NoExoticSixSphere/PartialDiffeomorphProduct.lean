import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Product partial diffeomorphisms with their actual product domains
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {E H M F H' N E' G M' F' G' N' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ E' G} [TopologicalSpace M'] [ChartedSpace G M']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [TopologicalSpace G']
  {J' : ModelWithCorners ℝ F' G'} [TopologicalSpace N'] [ChartedSpace G' N']

def partialDiffeomorphProd (Φ : PartialDiffeomorph I J M N ∞)
    (Ψ : PartialDiffeomorph I' J' M' N' ∞) :
    PartialDiffeomorph (I.prod I') (J.prod J') (M × M') (N × N') ∞ where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph).toPartialEquiv
  open_source := Φ.open_source.prod Ψ.open_source
  open_target := Φ.open_target.prod Ψ.open_target
  contMDiffOn_toFun :=
    (Φ.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ hp ↦ hp.1)).prodMk
      (Ψ.contMDiffOn_toFun.comp contMDiffOn_snd (fun _ hp ↦ hp.2))
  contMDiffOn_invFun :=
    (Φ.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ hp ↦ hp.1)).prodMk
      (Ψ.contMDiffOn_invFun.comp contMDiffOn_snd (fun _ hp ↦ hp.2))

end NoExoticSixSphere
