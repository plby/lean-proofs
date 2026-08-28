import Wikipedia.NoExoticSixSphere.FamilyDiskEmbedding
import Wikipedia.NoExoticSixSphere.SphereExtensionFamily
import Wikipedia.NoExoticSixSphere.StabilizedSpanningDisk
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# Spanning disks constructed jointly for a smooth family of embedded spheres

The original sphere family supplies every disk, its immersion, exact boundary,
avoidance of the old ambient space, and one common open radial collar. The
entire disk family is smooth in parameter and disk coordinates together.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization

theorem exists_family_spanningDisk {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {K : Set P} (hK : IsCompact K) {n N : ℕ} (b : Sphere n)
    (f : P → Sphere n → Vector N)
    (hf : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 N) ∞ (uncurry f))
    (hi : ∀ t ∈ K, Injective (f t))
    (hd : ∀ t ∈ K, ∀ s, Injective (mfderiv (𝓡 n) (𝓡 N) (f t) s)) :
    ∃ G : P → Vector (n + 1) → Vector (N + (1 + (1 + (n + 1)))),
      ContDiff ℝ ∞ (uncurry G) ∧
      (∀ t ∈ K, IsClosedEmbedding
        (fun x : closedBall (0 : Vector (n + 1)) 1 ↦ G t x.val)) ∧
      (∀ t ∈ K, ∀ x ∈ closedBall (0 : Vector (n + 1)) 1,
        Injective (fderiv ℝ (G t) x)) ∧
      (∀ t ∈ K, ∀ s : Sphere n,
        G t s.val = appendZeroMap N (1 + (1 + (n + 1))) (f t s)) ∧
      (∀ t ∈ K, ∀ x ∈ ball (0 : Vector (n + 1)) 1,
        G t x ∉ range (appendZeroMap N (1 + (1 + (n + 1))))) ∧
      ∃ V : Set (Vector (n + 1)), IsOpen V ∧ sphere 0 1 ⊆ V ∧
        ∀ t ∈ K, EqOn (G t) (collar b (f t)) V := by
  have hs (t : P) : ContMDiff (𝓡 n) (𝓡 N) ∞ (f t) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  let f₀ : P → Vector (n + 1) → Vector N × ℝ :=
    fun t ↦ SphereExtensionWithHeight.map b (f t)
  have hf₀ : ContDiff ℝ ∞ (uncurry f₀) :=
    SphereExtensionWithHeight.contDiff_map_family b f hf
  have hi₀ : ∀ t ∈ K, InjOn (f₀ t) (sphere (0 : Vector (n + 1)) 1) :=
    fun t ht ↦ SphereExtensionWithHeight.injOn_map_sphere b (f t) (hi t ht)
  have hd₀ : ∀ t ∈ K, ∀ x ∈ sphere (0 : Vector (n + 1)) 1,
      Injective (fderiv ℝ (f₀ t) x) := fun t ht x hx ↦
    SphereExtensionWithHeight.injective_fderiv_map_sphere b (f t) (hs t) (hd t ht) ⟨x, hx⟩
  obtain ⟨g, hg, hge, hgd, hga, V, hV, hSV, hVg⟩ :=
    DiskGraph.exists_family_embedding_rel_sphere_avoiding hK f₀ hf₀ hi₀ hd₀
      isOpen_univ (subset_univ _)
      (fun _ ↦ (univ : Set (Vector N)) ×ˢ ({0} : Set ℝ))
      (fun t _ x hx _ ↦ SphereExtensionWithHeight.avoids_oldAmbient b (f t) hx)
  let L := coordinates N (n + 1)
  have hcollar (t : P) (ht : t ∈ K) : EqOn (L ∘ g t) (collar b (f t)) V := by
    intro x hx
    change L (g t x) = L (f₀ t x, 0)
    rw [hVg t ht x hx]
  refine ⟨fun t ↦ L ∘ g t, L.contDiff.comp hg, ?_, ?_, ?_, ?_,
    V, hV, hSV, hcollar⟩
  · intro t ht
    exact L.toHomeomorph.isClosedEmbedding.comp (hge t ht)
  · intro t ht x hx
    have hgt : ContDiff ℝ ∞ (g t) := hg.comp (contDiff_const.prodMk contDiff_id)
    rw [(L.hasFDerivAt.comp x ((hgt.differentiable (by simp) x).hasFDerivAt)).fderiv]
    exact L.injective.comp (hgd t ht x hx)
  · intro t ht s
    exact (hcollar t ht (hSV s.property)).trans (collar_coe b (f t) s)
  · intro t ht x hx h
    obtain ⟨y, hy⟩ := h
    have he : g t x = ((y, 0), 0) := L.injective (by
      rw [coordinates_old]
      exact hy.symm)
    exact hga t ht x hx (by rw [he]; exact ⟨⟨mem_univ _, rfl⟩, rfl⟩)

end NoExoticSixSphere.StabilizedSpanningDisk
