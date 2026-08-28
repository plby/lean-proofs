import Wikipedia.NoExoticSixSphere.SlabInteriorAtlas
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-! # The ambient inclusion of the strict-time slab piece is an immersion -/

open scoped Manifold ContDiff
open Module Function

namespace NoExoticSixSphere.CylinderFiberSlab

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  (F : C(ℝ × M, N)) (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F) (b : N)
  (hreg : ∀ p, F p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J F p))
  (l : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + l) (s t : ℝ)
  {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace G]
  {R : ModelWithCorners ℝ D G}
  (Φ : PartialDiffeomorph (𝓡 l) R (EuclideanSpace ℝ (Fin l)) G ∞)
  (hsource : Φ.source = Set.univ)

theorem interiorAtlas_injective_mfderiv_ambient (p : interiorDomain F b s t) :
    letI := interiorAtlas F hF b hreg l hd s t Φ hsource;
    Injective (mfderiv R ((𝓘(ℝ, ℝ)).prod I)
      (fun q : interiorDomain F b s t ↦ q.val.val.val) p) := by
  let := regularFiberAtlas F hF b hreg l hd
  let := regularFiber_isManifold F hF b hreg l hd
  let g := fun q : fiberInterior F b s t ↦ q.val.val
  have hg : ContMDiff (𝓡 l) ((𝓘(ℝ, ℝ)).prod I) ∞ g :=
    (regularFiber_contMDiff_subtype_val F hF b hreg l hd).comp contMDiff_subtype_val
  have hinj (q : fiberInterior F b s t) :
      Injective (mfderiv (𝓡 l) ((𝓘(ℝ, ℝ)).prod I) g q) := by
    change Injective (mfderiv (𝓡 l) ((𝓘(ℝ, ℝ)).prod I)
      ((Subtype.val : {p : ℝ × M // F p = b} → ℝ × M) ∘
        (Subtype.val : fiberInterior F b s t → {p : ℝ × M // F p = b})) q)
    rw [mfderiv_comp q
      ((regularFiber_contMDiff_subtype_val F hF b hreg l hd).mdifferentiable (by simp) q.val)
      ((contMDiff_subtype_val (I := 𝓡 l) (U := fiberInterior F b s t) (n := ∞)).mdifferentiable
        (by simp) q)]
    exact (regularFiber_injective_mfderiv_subtype_val F hF b hreg l hd q.val).comp
      (mfderiv_openSubset_val_bijective (I := 𝓡 l) (fiberInterior F b s t) q).injective
  let := ChangedModelAtlas.chartedSpace (M := fiberInterior F b s t) Φ hsource
  let := interiorAtlas F hF b hreg l hd s t Φ hsource
  let e := (ModelAtlasTransport.diffeomorph (interiorHomeomorph F b s t) R).trans
    (ChangedModelAtlas.diffeomorph (M := fiberInterior F b s t) Φ hsource)
  change Injective (mfderiv R ((𝓘(ℝ, ℝ)).prod I) (g ∘ e) p)
  rw [mfderiv_comp p (hg.mdifferentiable (by simp) (e p))
    (e.contMDiff.mdifferentiable (by simp) p)]
  exact (hinj (e p)).comp (e.mfderivToContinuousLinearEquiv (by simp) p).injective

end NoExoticSixSphere.CylinderFiberSlab
