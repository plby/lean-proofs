import Wikipedia.NoExoticSixSphere.ProductTubeCollapse
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Adding a normal factor while retaining a smooth inverse

The product tube uses the original partial diffeomorphism and keeps the
new normal coordinate unchanged. Its full source and inverse smoothness
are proved in the ordinary normed-product models used by the collapse.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenFiberCollapse

variable {B H M K Y T : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, K)) 𝓘(ℝ, Y) (M × K) Y ∞)
  (hsource : Φ.source = univ)

def productTubePartial :
    PartialDiffeomorph (I.prod 𝓘(ℝ, K × T)) 𝓘(ℝ, Y × T) (M × (K × T)) (Y × T) ∞ := by
  let e := (Homeomorph.prodAssoc M K T).symm.toOpenPartialHomeomorph.trans
    (Φ.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl T))
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · have hΦ : ContMDiff (I.prod 𝓘(ℝ, K)) 𝓘(ℝ, Y) ∞ Φ := by
      have h := Φ.contMDiffOn
      rw [hsource] at h
      exact contMDiffOn_univ.mp h
    have hk : ContMDiff (I.prod 𝓘(ℝ, K × T)) 𝓘(ℝ, K) ∞
        (fun p : M × (K × T) ↦ p.2.1) :=
      contDiff_fst.contMDiff.comp contMDiff_snd
    have ht : ContMDiff (I.prod 𝓘(ℝ, K × T)) 𝓘(ℝ, T) ∞
        (fun p : M × (K × T) ↦ p.2.2) :=
      contDiff_snd.contMDiff.comp contMDiff_snd
    exact ((hΦ.comp (contMDiff_fst.prodMk hk)).prodMk_space ht).contMDiffOn
  · have hΦ : ContMDiffOn 𝓘(ℝ, Y × T) (I.prod 𝓘(ℝ, K)) ∞
        (fun p : Y × T ↦ Φ.symm p.1) (Φ.target ×ˢ univ) :=
      Φ.contMDiffOn_invFun.comp contDiff_fst.contMDiff.contMDiffOn (fun _ hp ↦ hp.1)
    have h := (contMDiff_fst.comp_contMDiffOn hΦ).prodMk
      ((contMDiff_snd.comp_contMDiffOn hΦ).prodMk_space
        contDiff_snd.contMDiff.contMDiffOn)
    exact h.mono (fun _ hp ↦ hp.1)

theorem productTubePartial_apply (p : M × (K × T)) :
    productTubePartial Φ hsource p = productTube Φ p := rfl

theorem productTubePartial_symm_apply (p : Y × T) :
    (productTubePartial Φ hsource).symm p =
      ((Φ.symm p.1).1, ((Φ.symm p.1).2, p.2)) := rfl

theorem productTubePartial_source : (productTubePartial (T := T) Φ hsource).source = univ := by
  apply eq_univ_of_forall
  intro p
  change p ∈ univ ∧ ((p.1, p.2.1) ∈ Φ.source ∧ p.2.2 ∈ univ)
  simp only [hsource, mem_univ, and_self]

end NoExoticSixSphere.OpenFiberCollapse

namespace NoExoticSixSphere

variable {B H M C J N E K P : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace J]
  {I' : ModelWithCorners ℝ C J} [TopologicalSpace N] [ChartedSpace J N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace K]
  {I'' : ModelWithCorners ℝ E K} [TopologicalSpace P] [ChartedSpace K P]

theorem partialDiffeomorph_trans_apply
    (Φ : PartialDiffeomorph I I' M N ∞) (Ψ : PartialDiffeomorph I' I'' N P ∞) (x : M) :
    (Φ.trans Ψ) x = Ψ (Φ x) := rfl

theorem diffeomorph_partial_apply (d : Diffeomorph I I' M N ∞) (x : M) :
    d.toPartialDiffeomorph x = d x := rfl

theorem partialDiffeomorph_trans_source_univ
    (Φ : PartialDiffeomorph I I' M N ∞) (Ψ : PartialDiffeomorph I' I'' N P ∞)
    (hΦ : Φ.source = univ) (hΨ : Ψ.source = univ) : (Φ.trans Ψ).source = univ := by
  change Φ.source ∩ Φ ⁻¹' Ψ.source = univ
  rw [hΦ, hΨ]
  simp only [preimage_univ, inter_self]

end NoExoticSixSphere
