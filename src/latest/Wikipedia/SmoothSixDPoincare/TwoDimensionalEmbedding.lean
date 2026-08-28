import Wikipedia.SmoothSixDPoincare.RelativeCompactPlaneEmbedding

/-!
# Relative compact embeddings for any two-dimensional real normed source

A continuous linear equivalence identifies the source with the product
plane used by the affine construction. Smoothness, actual native derivative
injectivity, the relative homotopy, and compact embedding are all transported
back to the original source. The source topology is not changed.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E E' G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

/-- Precomposition by a continuous linear equivalence preserves injective native derivatives. -/
theorem injective_mfderiv_comp_linearEquiv_iff (e : E' ≃L[ℝ] E) {f : E → N} {x : E'}
    (hf : MDifferentiableAt 𝓘(ℝ, E) J f (e x)) :
    Function.Injective (mfderiv 𝓘(ℝ, E') J (f ∘ e) x) ↔
      Function.Injective (mfderiv 𝓘(ℝ, E) J f (e x)) := by
  have he : mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E) e x = e.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact e.toContinuousLinearMap.fderiv
  have hesmooth : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ e := e.contDiff.contMDiff
  rw [mfderiv_comp x hf (hesmooth.mdifferentiableAt (by simp)), he]
  constructor
  · intro h v w hvw
    apply e.symm.injective
    apply h
    change (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm v)) =
      (mfderiv 𝓘(ℝ, E) J f (e x)) (e (e.symm w))
    exact (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (v : E))).trans
      (hvw.trans (congrArg (mfderiv 𝓘(ℝ, E) J f (e x)) (e.apply_symm_apply (w : E))).symm)
  · exact fun h => h.comp e.injective

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]

/-- The relative compact embedding construction works on the original two-dimensional normed
source, including the actual Euclidean space containing the standard disk. -/
theorem exists_relative_compact_embedding_twoDimensional (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hsourceDim : Module.finrank ℝ E = 2)
    (hdim : 5 ≤ Module.finrank ℝ G) {K C : Set E} (hK : IsCompact K) (hC : IsClosed C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ f.HomotopicRel g C ∧
      Topology.IsClosedEmbedding (fun x : K => g x) ∧
      ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x) := by
  let e : PlaneImmersion.Plane ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by
    simp only [PlaneImmersion.Plane, Module.finrank_prod, Module.finrank_self]
    omega)
  let fp : C(PlaneImmersion.Plane, N) := ⟨f ∘ e, f.continuous.comp e.continuous⟩
  have hfp : ContMDiff 𝓘(ℝ, PlaneImmersion.Plane) J ∞ fp := hf.comp e.contDiff.contMDiff
  have hKp : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hCp : IsClosed (e ⁻¹' C) := hC.preimage e.continuous
  have hfixedp : InjOn fp ((e ⁻¹' K) ∩ (e ⁻¹' C)) := by
    intro x hx y hy hxy
    exact e.injective (hfixed ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxy)
  have hderivp : ∀ x ∈ (e ⁻¹' K) ∩ (e ⁻¹' C),
      Function.Injective (mfderiv 𝓘(ℝ, PlaneImmersion.Plane) J fp x) := by
    intro x hx
    exact (injective_mfderiv_comp_linearEquiv_iff e (hf.mdifferentiableAt (by simp))).mpr
      (hderiv (e x) ⟨hx.1, hx.2⟩)
  obtain ⟨gp, hgp, ⟨Hrel⟩, hembp, hgpderiv⟩ :=
    exists_relative_compact_embedding fp hfp hdim hKp hCp hfixedp hderivp
  let g : C(E, N) := ⟨gp ∘ e.symm, gp.continuous.comp e.symm.continuous⟩
  have hg : ContMDiff 𝓘(ℝ, E) J ∞ g := hgp.comp e.symm.contDiff.contMDiff
  have hpreK (x : E) (hx : x ∈ K) : e.symm x ∈ e ⁻¹' K := by
    change e (e.symm x) ∈ K
    simpa only [e.apply_symm_apply] using hx
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · refine ⟨{
      toFun := fun q => Hrel (q.1, e.symm q.2)
      continuous_toFun := Hrel.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro x
      rw [Hrel.apply_zero]
      exact congrArg f (e.apply_symm_apply x)
    · intro x
      exact Hrel.apply_one (e.symm x)
    · intro t x hx
      change Hrel (t, e.symm x) = f x
      have hpreC : e.symm x ∈ e ⁻¹' C := by
        change e (e.symm x) ∈ C
        simpa only [e.apply_symm_apply] using hx
      rw [Hrel.eq_fst t hpreC]
      exact congrArg f (e.apply_symm_apply x)
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    have hpeq : gp (e.symm x) = gp (e.symm y) := hxy
    exact congrArg Subtype.val (hembp.injective
      (a₁ := ⟨e.symm x, hpreK x x.property⟩) (a₂ := ⟨e.symm y, hpreK y y.property⟩) hpeq)
  · intro x hx
    exact (injective_mfderiv_comp_linearEquiv_iff e.symm (hgp.mdifferentiableAt (by simp))).mpr
      (hgpderiv (e.symm x) (hpreK x hx))

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
