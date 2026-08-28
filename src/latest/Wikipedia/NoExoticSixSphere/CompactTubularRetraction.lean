import Wikipedia.NoExoticSixSphere.TubularNeighborhood
import Wikipedia.NoExoticSixSphere.CompactLocalDiffeomorph

/-!
# Smooth tubular retraction near a compact subset of the original manifold

The ambient manifold need not be compact. Compactness is used only for the
specified subset of its actual zero section. Normal displacement gives a
single injective smooth neighborhood there, hence a retraction which fixes
an open neighborhood of the compact subset in the original manifold.
-/

noncomputable section

open Set Bundle Function Filter
open scoped Manifold ContDiff Topology Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) [Nonempty M]

omit [Nonempty M] in
/-- A local section through the actual normal vector splits the projection derivative. -/
theorem surjective_mfderiv_normalBundle_proj (v : e.NormalBundle) :
    Surjective (mfderiv ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 n)
      (π e.NormalModel e.NormalSpace) v) := by
  let t := trivializationAt e.NormalModel e.NormalSpace v.proj
  have hv : v ∈ t.source := FiberBundle.mem_trivializationAt_proj_source
  let s : M → e.NormalBundle := fun x ↦ t.toOpenPartialHomeomorph.symm (x, (t v).2)
  have hsv : s v.proj = v := by
    change t.toOpenPartialHomeomorph.symm (v.proj, (t v).2) = v
    rw [t.mk_proj_snd hv]
    exact t.toOpenPartialHomeomorph.left_inv hv
  have htarget : (v.proj, (t v).2) ∈ t.target := by
    rw [t.mk_proj_snd hv]
    exact t.toOpenPartialHomeomorph.map_source hv
  have hs : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞ s v.proj :=
    (t.contMDiffOn_symm.contMDiffAt (t.open_target.mem_nhds htarget)).comp v.proj
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have he : (fun x ↦ (s x).proj) =ᶠ[𝓝 v.proj] id := by
    filter_upwards [t.open_baseSet.mem_nhds (t.mem_source.mp hv)] with x hx
    exact t.proj_symm_apply' hx
  have hp : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 n)
      (π e.NormalModel e.NormalSpace) (s v.proj) :=
    (Bundle.contMDiff_proj (n := ∞) e.NormalSpace).mdifferentiableAt (by simp)
  have hc := mfderiv_comp v.proj hp (hs.mdifferentiableAt (by simp))
  have hid : mfderiv (𝓡 n) (𝓡 n)
      ((π e.NormalModel e.NormalSpace) ∘ s) v.proj =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    calc
      _ = mfderiv (𝓡 n) (𝓡 n) id v.proj := he.mfderiv_eq
      _ = _ := mfderiv_id
  rw [hid, hsv] at hc
  intro w
  refine ⟨mfderiv (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) s v.proj w, ?_⟩
  exact (congrArg (fun L ↦ L w) hc).symm

theorem exists_tubularNeighborhood_near_compact {K : Set M} (hK : IsCompact K) :
    ∃ Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
      (zeroSection e.NormalModel e.NormalSpace) '' K ⊆ Φ.source ∧
      (Φ : e.NormalBundle → EuclideanSpace ℝ (Fin e.ambientDimension)) = e.normalDisplacement := by
  have hc : IsCompact ((zeroSection e.NormalModel e.NormalSpace) '' K) :=
    hK.image (Bundle.Trivialization.continuous_zeroSection ℝ)
  have hi : InjOn e.normalDisplacement ((zeroSection e.NormalModel e.NormalSpace) '' K) :=
    e.normalDisplacement_injOn_zeroSection.mono (image_subset_range _ _)
  obtain ⟨U, hU, hKU, -, hUi, hUl⟩ := exists_injective_localDiffeomorph_neighborhood
    hc hi (by rintro _ ⟨x, hx, rfl⟩; exact e.isLocalDiffeomorphAt_normalDisplacement_zero x)
    isOpen_univ (subset_univ _)
  exact ⟨e.normalNeighborhoodPartialDiffeomorph hU hUi (fun v ↦ hUl v.val v.property),
    hKU, rfl⟩

structure RetractionNear (K : Set M) where
  base : TopologicalSpace.Opens M
  covers : K ⊆ base
  domain : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin e.ambientDimension))
  toFun : EuclideanSpace ℝ (Fin e.ambientDimension) → M
  smooth : ContMDiffOn (𝓡 e.ambientDimension) (𝓡 n) ∞ toFun domain
  fixes : ∀ x ∈ base, toFun (e.toFun x) = x
  contains : e.toFun '' (base : Set M) ⊆ domain
  submersive : ∀ y ∈ domain,
    Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 n) toFun y)

theorem nonempty_retractionNear {K : Set M} (hK : IsCompact K) :
    Nonempty (e.RetractionNear K) := by
  obtain ⟨Φ, hKΦ, hΦ⟩ := e.exists_tubularNeighborhood_near_compact hK
  let U : TopologicalSpace.Opens M :=
    ⟨(zeroSection e.NormalModel e.NormalSpace) ⁻¹' Φ.source,
      Φ.open_source.preimage (Bundle.Trivialization.continuous_zeroSection ℝ)⟩
  have he (x : M) : Φ (zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
    rw [hΦ, e.normalDisplacement_zero]
  refine ⟨{
    base := U
    covers := fun x hx ↦ hKΦ ⟨x, hx, rfl⟩
    domain := ⟨Φ.target, Φ.open_target⟩
    toFun := fun y ↦ (Φ.symm y).proj
    smooth := (Bundle.contMDiff_proj e.NormalSpace).comp_contMDiffOn Φ.contMDiffOn_invFun
    fixes := ?_
    contains := ?_
    submersive := ?_
  }⟩
  · intro x hx
    have h := Φ.left_inv' hx
    rw [he] at h
    exact congrArg (fun v : e.NormalBundle ↦ v.proj) h
  · rintro _ ⟨x, hx, rfl⟩
    exact he x ▸ Φ.map_source' hx
  · intro y hy
    have hlocal : IsLocalDiffeomorphAt (𝓡 e.ambientDimension)
        ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞ Φ.symm y :=
      ⟨Φ.symm, hy, fun _ _ ↦ rfl⟩
    have hsurj := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
    change Surjective (mfderiv (𝓡 e.ambientDimension)
      ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) Φ.symm y) at hsurj
    have hinv : ContMDiffAt (𝓡 e.ambientDimension)
        ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞ Φ.symm y :=
      Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)
    change Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 n)
      ((π e.NormalModel e.NormalSpace) ∘ Φ.symm) y)
    rw [mfderiv_comp y
      ((Bundle.contMDiff_proj (n := ∞) e.NormalSpace).mdifferentiableAt (by simp))
      (hinv.mdifferentiableAt (by simp))]
    exact (e.surjective_mfderiv_normalBundle_proj (Φ.symm y)).comp hsurj

end NoExoticSixSphere.EuclideanEmbedding
