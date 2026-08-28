import Wikipedia.NoExoticSixSphere.ManifoldLevelNormalForm

/-!
# Equal-dimensional manifold inverse functions

The regular-level normal form has a zero-dimensional complementary factor
when the model dimensions agree. Removing that factor gives a genuine local
diffeomorphism between the original manifolds and their existing atlases.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem isLocalDiffeomorphAt_of_surjective_mfderiv {f : M → N}
    (hf : ContMDiff I J ∞ f) (hd : finrank ℝ B = finrank ℝ C) (x : M)
    (hreg : Function.Surjective (mfderiv I J f x)) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hcx : f x ∈ c.source := mem_extChartAt_source (f x)
  have hg : ContMDiffOn I 𝓘(ℝ, C) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hy ↦ hy)
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, C) ∞ c (f x) :=
    ⟨c, hcx, fun _ _ ↦ rfl⟩
  have hs : Function.Surjective (mfderiv I 𝓘(ℝ, C) (c ∘ f) x) := by
    rw [mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hf.mdifferentiable (by simp) x)]
    exact (hc.mfderivToContinuousLinearEquiv (by simp)).surjective.comp hreg
  obtain ⟨Φ, hxΦ, hΦU, hfirst, _⟩ :=
    exists_manifoldLevelNormalForm hU hcx hg hs 0 (by simpa using hd)
  let p := (ContinuousLinearEquiv.prodUnique ℝ C (EuclideanSpace ℝ (Fin 0))).toDiffeomorph
  refine ⟨(Φ.trans p.toPartialDiffeomorph).trans c.symm, ?_, ?_⟩
  · refine ⟨⟨hxΦ, Set.mem_univ _⟩, ?_⟩
    change (Φ x).1 ∈ c.target
    rw [hfirst x hxΦ]
    exact c.map_source' hcx
  · intro y hy
    change f y = c.symm ((Φ y).1)
    rw [hfirst y hy.1.1]
    exact (c.left_inv' (hΦU hy.1.1)).symm

noncomputable def diffeomorphOfBijectiveImmersion (f : M → N)
    (hf : ContMDiff I J ∞ f) (hbij : Function.Bijective f)
    (hd : finrank ℝ B = finrank ℝ C)
    (himm : ∀ x, Function.Injective (mfderiv I J f x)) : M ≃ₘ⟮I, J⟯ N := by
  apply IsLocalDiffeomorph.diffeomorphOfBijective (f := f) _ hbij
  intro x
  apply isLocalDiffeomorphAt_of_surjective_mfderiv hf hd x
  let D : B →L[ℝ] C := mfderiv I J f x
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (himm x)

end NoExoticSixSphere
