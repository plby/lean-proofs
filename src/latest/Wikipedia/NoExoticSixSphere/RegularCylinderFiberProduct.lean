import Wikipedia.NoExoticSixSphere.CylinderFiberProduct
import Wikipedia.NoExoticSixSphere.RegularFiberManifold

/-!
# Smooth product neighborhoods at constant ends of regular homotopies

The topological product identification is a diffeomorphism for the regular
fiber atlases already constructed from the original maps. Both directions
are smooth by the ambient smooth-map criterion; no new transported atlas is
substituted for either regular fiber's atlas.
-/

open scoped Manifold ContDiff
open Module TopologicalSpace

namespace NoExoticSixSphere.CylinderFiberProduct

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (F : C(ℝ × M, N)) (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F)
  (f : C(M, N)) (hf : ContMDiff I J ∞ f) (b : N)
  (hregF : ∀ p, F p = b → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J F p))
  (hregf : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
  (l k : ℕ) (hdF : finrank ℝ (ℝ × B) = finrank ℝ C + l)
  (hdf : finrank ℝ B = finrank ℝ C + k)
  (U : Opens ℝ) (hconstant : ∀ t ∈ U, ∀ x, F (t, x) = f x)

theorem contMDiff_homeomorph :
    letI := regularFiberAtlas F hF b hregF l hdF;
    letI := regularFiberAtlas f hf b hregf k hdf;
    ContMDiff (𝓡 l) ((𝓘(ℝ, ℝ)).prod (𝓡 k)) ∞ (homeomorph F f b U hconstant) := by
  let := regularFiberAtlas F hF b hregF l hdF
  let := regularFiberAtlas f hf b hregf k hdf
  have hinc : ContMDiff (𝓡 l) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : timeDomain F b U ↦ p.val.val) :=
    (regularFiber_contMDiff_subtype_val F hF b hregF l hdF).comp contMDiff_subtype_val
  have ht : ContMDiff (𝓡 l) 𝓘(ℝ, ℝ) ∞
      (fun p ↦ (homeomorph F f b U hconstant p).1) :=
    (ContMDiff.subtypeVal_comp_iff U _).mp (contMDiff_fst.comp hinc)
  have hx : ContMDiff (𝓡 l) (𝓡 k) ∞
      (fun p ↦ (homeomorph F f b U hconstant p).2) :=
    (regularFiber_contMDiff_iff_ambient f hf b hregf k hdf _).mpr (contMDiff_snd.comp hinc)
  exact ht.prodMk hx

theorem contMDiff_homeomorph_symm :
    letI := regularFiberAtlas F hF b hregF l hdF;
    letI := regularFiberAtlas f hf b hregf k hdf;
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 k)) (𝓡 l) ∞ (homeomorph F f b U hconstant).symm := by
  let := regularFiberAtlas F hF b hregF l hdF
  let := regularFiberAtlas f hf b hregf k hdf
  have ht : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 k)) 𝓘(ℝ, ℝ) ∞
      (fun p : U × {x : M // f x = b} ↦ p.1.val) :=
    contMDiff_subtype_val.comp contMDiff_fst
  have hx : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 k)) I ∞
      (fun p : U × {x : M // f x = b} ↦ p.2.val) :=
    (regularFiber_contMDiff_subtype_val f hf b hregf k hdf).comp contMDiff_snd
  have hinc : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 k)) (𝓡 l) ∞
      (fun p ↦ ((homeomorph F f b U hconstant).symm p).val) :=
    (regularFiber_contMDiff_iff_ambient F hF b hregF l hdF _).mpr (ht.prodMk hx)
  exact (ContMDiff.subtypeVal_comp_iff (timeDomain F b U) _).mp hinc

noncomputable def diffeomorph :
    letI := regularFiberAtlas F hF b hregF l hdF;
    letI := regularFiberAtlas f hf b hregf k hdf;
    timeDomain F b U ≃ₘ⟮𝓡 l, (𝓘(ℝ, ℝ)).prod (𝓡 k)⟯ U × {x : M // f x = b} := by
  let := regularFiberAtlas F hF b hregF l hdF
  let := regularFiberAtlas f hf b hregf k hdf
  exact
    { toEquiv := (homeomorph F f b U hconstant).toEquiv
      contMDiff_toFun := contMDiff_homeomorph F hF f hf b hregF hregf l k hdF hdf U hconstant
      contMDiff_invFun :=
        contMDiff_homeomorph_symm F hF f hf b hregF hregf l k hdF hdf U hconstant }

end NoExoticSixSphere.CylinderFiberProduct
