import Wikipedia.NoExoticSixSphere.ManifoldLevelNormalForm

/-!
# Regularity persists on a neighborhood

A regular-level normal form makes the differential surjective throughout its
source, not just at the base point. Apply this in an actual target-chart
domain to show that the regular-point locus of a smooth map between
finite-dimensional boundaryless manifolds is open.
-/

open scoped Manifold ContDiff Topology
open Set Module

namespace NoExoticSixSphere

section NormalForm

variable {B H M F K : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem surjective_mfderiv_of_levelNormalForm
    (Φ : PartialDiffeomorph I 𝓘(ℝ, F × K) M (F × K) ∞)
    {f : M → F} (hfirst : ∀ y ∈ Φ.source, (Φ y).1 = f y) {x : M} (hx : x ∈ Φ.source) :
    Function.Surjective (mfderiv I 𝓘(ℝ, F) f x) := by
  have heq : (Prod.fst ∘ Φ) =ᶠ[𝓝 x] f :=
    Filter.eventually_of_mem (Φ.open_source.mem_nhds hx) hfirst
  have hΦ : IsLocalDiffeomorphAt I 𝓘(ℝ, F × K) ∞ Φ x :=
    ⟨Φ, hx, fun _ _ ↦ rfl⟩
  have hp : ContMDiff 𝓘(ℝ, F × K) 𝓘(ℝ, F) ∞ (Prod.fst : F × K → F) :=
    contDiff_fst.contMDiff
  have hps : Function.Surjective
      (mfderiv 𝓘(ℝ, F × K) 𝓘(ℝ, F) (Prod.fst : F × K → F) (Φ x)) := by
    rw [mfderiv_eq_fderiv, fderiv_fst]
    exact fun y ↦ ⟨(y, 0), rfl⟩
  rw [← heq.mfderiv_eq, mfderiv_comp x (hp.mdifferentiable (by simp) (Φ x))
    (hΦ.mdifferentiableAt (by simp))]
  exact hps.comp (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective

end NormalForm

section VectorTarget

variable {B H M F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_regularPointNeighborhood_vector {f : M → F} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hreg : Function.Surjective (mfderiv I 𝓘(ℝ, F) f x)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, Function.Surjective (mfderiv I 𝓘(ℝ, F) f y) := by
  let D : B →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  have hdim : finrank ℝ F ≤ finrank ℝ B :=
    LinearMap.finrank_le_finrank_of_surjective (f := D.toLinearMap) hreg
  obtain ⟨Φ, hxΦ, hΦU, hfirst, _⟩ := exists_manifoldLevelNormalForm hU hx hf hreg
    (finrank ℝ B - finrank ℝ F) (by omega)
  exact ⟨Φ.source, Φ.open_source, hxΦ, hΦU,
    fun _ hy ↦ surjective_mfderiv_of_levelNormalForm Φ hfirst hy⟩

end VectorTarget

section ManifoldTarget

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem exists_regularPointNeighborhood {f : M → N} (hf : ContMDiff I J ∞ f) {x : M}
    (hreg : Function.Surjective (mfderiv I J f x)) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, Function.Surjective (mfderiv I J f y) := by
  let c := modelChartPartialDiffeomorph (I := J) (f x)
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hxU : x ∈ U := mem_extChartAt_source (f x)
  have hg : ContMDiffOn I 𝓘(ℝ, C) ∞ (c ∘ f) U :=
    c.contMDiffOn_toFun.comp hf.contMDiffOn (fun _ hy ↦ hy)
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, C) ∞ c (f x) :=
    ⟨c, hxU, fun _ _ ↦ rfl⟩
  have hs : Function.Surjective (mfderiv I 𝓘(ℝ, C) (c ∘ f) x) := by
    rw [mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hf.mdifferentiable (by simp) x)]
    exact (hc.mfderivToContinuousLinearEquiv (by simp)).surjective.comp hreg
  obtain ⟨V, hV, hxV, hVU, hVreg⟩ := exists_regularPointNeighborhood_vector hU hxU hg hs
  refine ⟨V, hV, hxV, fun y hy ↦ ?_⟩
  have hcy : IsLocalDiffeomorphAt J 𝓘(ℝ, C) ∞ c (f y) :=
    ⟨c, hVU hy, fun _ _ ↦ rfl⟩
  have hi : Function.Injective (mfderiv J 𝓘(ℝ, C) c (f y)) :=
    (hcy.mfderivToContinuousLinearEquiv (by simp)).injective
  have hsy := hVreg y hy
  rw [mfderiv_comp y (hcy.mdifferentiableAt (by simp)) (hf.mdifferentiable (by simp) y)] at hsy
  intro v
  obtain ⟨w, hw⟩ := hsy ((mfderiv J 𝓘(ℝ, C) c (f y)) v)
  exact ⟨w, hi hw⟩

theorem isOpen_regularPoints {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsOpen {x | Function.Surjective (mfderiv I J f x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hV, hxV, hreg⟩ := exists_regularPointNeighborhood hf hx
  exact ⟨V, hreg, hV, hxV⟩

end ManifoldTarget

end NoExoticSixSphere
