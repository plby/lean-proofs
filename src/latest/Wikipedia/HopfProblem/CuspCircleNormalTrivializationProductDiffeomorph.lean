import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Products of diffeomorphisms with independently varying models

Both factors may change their normed model vector space. The forward and
inverse maps are the ordinary products of the given native diffeomorphisms.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F F' H H' K K' M M' N N' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace K] [TopologicalSpace K']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace N'] [ChartedSpace K' N']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F K} {J' : ModelWithCorners 𝕜 F' K'} {n : ℕ∞ω}

/-- The product map for fully independent native model spaces on both factors. -/
def productDiffeomorph (e : Diffeomorph I I' M M' n) (f : Diffeomorph J J' N N' n) :
    Diffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  toEquiv := e.toEquiv.prodCongr f.toEquiv
  contMDiff_toFun := e.contMDiff.prodMap f.contMDiff
  contMDiff_invFun := e.symm.contMDiff.prodMap f.symm.contMDiff

@[simp] theorem productDiffeomorph_apply
    (e : Diffeomorph I I' M M' n) (f : Diffeomorph J J' N N' n) (p : M × N) :
    productDiffeomorph e f p = (e p.1, f p.2) := rfl

@[simp] theorem productDiffeomorph_symm_apply
    (e : Diffeomorph I I' M M' n) (f : Diffeomorph J J' N N' n) (p : M' × N') :
    (productDiffeomorph e f).symm p = (e.symm p.1, f.symm p.2) := rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
