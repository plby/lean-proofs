import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# An injective local diffeomorphism on an open set has a smooth partial inverse

The inverse comes from the actual injective map. Its smoothness follows by
comparison with the given local inverses, on genuine open neighborhoods.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [Nonempty M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {U : Set M} (hU : IsOpen U) (hinj : InjOn f U)
  (hloc : IsLocalDiffeomorphOn I J ∞ f U)

include hU hloc in
omit [Nonempty M] in
theorem isOpen_image_of_localDiffeomorph : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hx]
  exact image_mem_map (hU.mem_nhds hx)

include hU hloc in
theorem contMDiffAt_injectiveLocalInverse {y : N}
    (hy : y ∈ (hinj.toPartialEquiv f U).target) :
    ContMDiffAt J I ∞ (hinj.toPartialEquiv f U).symm y := by
  let p := hinj.toPartialEquiv f U
  have hx : p.symm y ∈ U := p.map_target hy
  obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
  have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
  have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
  have hφyx : φ.symm y = p.symm y := by
    calc
      φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
      _ = p.symm y := φ.left_inv' hφx
  have hg : ContMDiffAt J I ∞ φ.symm y :=
    φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
  have hNU : U ∈ 𝓝 (φ.symm y) := by
    rw [hφyx]
    exact hU.mem_nhds hx
  have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
    filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
    have hfz : f (φ.symm z) = z :=
      (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
    exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
  exact hfg.contMDiffAt_iff.mpr hg

def injectiveLocalPartialDiffeomorph : PartialDiffeomorph I J M N ∞ where
  toPartialEquiv := hinj.toPartialEquiv f U
  open_source := hU
  open_target := isOpen_image_of_localDiffeomorph hU hloc
  contMDiffOn_toFun := hloc.contMDiffOn
  contMDiffOn_invFun _ hy :=
    (contMDiffAt_injectiveLocalInverse hU hinj hloc hy).contMDiffWithinAt

end NoExoticSixSphere
