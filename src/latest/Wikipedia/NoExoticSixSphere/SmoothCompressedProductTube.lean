import Wikipedia.NoExoticSixSphere.CompressedProductTube
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth compression of a product tube

The radial map onto a ball and its inverse are smooth on their respective
domains. Composing this compression with a product tubular neighborhood
therefore retains a smooth local inverse on the full open tube.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.CompressedProductTube

variable {E H M K F H' Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace Y] [ChartedSpace H' Y]

noncomputable def compression (r : ℝ) (hr : 0 < r) :
    PartialDiffeomorph (I.prod 𝓘(ℝ, K)) (I.prod 𝓘(ℝ, K)) (M × K) (M × K) ∞ where
  toPartialEquiv := ((OpenPartialHomeomorph.refl M).prod
    (OpenPartialHomeomorph.univBall (0 : K) r)).toPartialEquiv
  open_source := ((OpenPartialHomeomorph.refl M).prod
    (OpenPartialHomeomorph.univBall (0 : K) r)).open_source
  open_target := ((OpenPartialHomeomorph.refl M).prod
    (OpenPartialHomeomorph.univBall (0 : K) r)).open_target
  contMDiffOn_toFun :=
    (contMDiff_fst.prodMk
      (OpenPartialHomeomorph.contDiff_univBall.contMDiff.comp contMDiff_snd)).contMDiffOn
  contMDiffOn_invFun := by
    change ContMDiffOn (I.prod 𝓘(ℝ, K)) (I.prod 𝓘(ℝ, K)) ∞
      (fun p : M × K ↦ (p.1, (OpenPartialHomeomorph.univBall (0 : K) r).symm p.2))
      (univ ×ˢ (OpenPartialHomeomorph.univBall (0 : K) r).target)
    rw [OpenPartialHomeomorph.univBall_target _ hr]
    exact contMDiffOn_fst.prodMk
      (OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn.comp
        contMDiffOn_snd (fun _ hp ↦ hp.2))

theorem compression_source (r : ℝ) (hr : 0 < r) :
    (compression I (M := M) (K := K) r hr).source = univ := by
  change univ ×ˢ (OpenPartialHomeomorph.univBall (0 : K) r).source = _
  simp only [OpenPartialHomeomorph.univBall_source, univ_prod_univ]

variable {I} (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, K)) J (M × K) Y ∞)
  (r : ℝ) (hr : 0 < r)

noncomputable def smoothTube : PartialDiffeomorph (I.prod 𝓘(ℝ, K)) J (M × K) Y ∞ :=
  (compression I r hr).trans Φ

theorem smoothTube_apply (p : M × K) :
    smoothTube Φ r hr p = map Φ.toOpenPartialHomeomorph r p := rfl

theorem smoothTube_source
    (hsource : ∀ x v, ‖v‖ ≤ r → (x, v) ∈ Φ.source) :
    (smoothTube Φ r hr).source = univ := by
  apply eq_univ_of_forall
  intro p
  change p ∈ (compression I r hr).source ∧ compression I r hr p ∈ Φ.source
  refine ⟨by rw [compression_source]; trivial, ?_⟩
  have hmem := (OpenPartialHomeomorph.univBall (0 : K) r).map_source
    (show p.2 ∈ (OpenPartialHomeomorph.univBall (0 : K) r).source by simp)
  rw [OpenPartialHomeomorph.univBall_target _ hr, Metric.mem_ball, dist_zero_right] at hmem
  exact hsource p.1 _ hmem.le

theorem smoothTube_zero (x : M) : smoothTube Φ r hr (x, 0) = Φ (x, 0) :=
  map_zero Φ.toOpenPartialHomeomorph r x

end NoExoticSixSphere.CompressedProductTube
