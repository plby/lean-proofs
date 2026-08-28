import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Products of diffeomorphisms with independent normed model spaces
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M C H' N B' K M' C' K' N' : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [TopologicalSpace K]
  {I' : ModelWithCorners ℝ B' K} [TopologicalSpace M'] [ChartedSpace K M']
  [NormedAddCommGroup C'] [NormedSpace ℝ C'] [TopologicalSpace K']
  {J' : ModelWithCorners ℝ C' K'} [TopologicalSpace N'] [ChartedSpace K' N']

def diffeomorphProd (f : Diffeomorph I J M N ∞) (g : Diffeomorph I' J' M' N' ∞) :
    Diffeomorph (I.prod I') (J.prod J') (M × M') (N × N') ∞ where
  toEquiv := f.toEquiv.prodCongr g.toEquiv
  contMDiff_toFun :=
    (f.contMDiff.comp contMDiff_fst).prodMk (g.contMDiff.comp contMDiff_snd)
  contMDiff_invFun :=
    (f.symm.contMDiff.comp contMDiff_fst).prodMk (g.symm.contMDiff.comp contMDiff_snd)

theorem diffeomorphProd_apply (f : Diffeomorph I J M N ∞) (g : Diffeomorph I' J' M' N' ∞)
    (p : M × M') : diffeomorphProd f g p = (f p.1, g p.2) := rfl

end NoExoticSixSphere
