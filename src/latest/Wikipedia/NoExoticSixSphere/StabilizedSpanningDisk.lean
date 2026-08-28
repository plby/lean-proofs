import Wikipedia.NoExoticSixSphere.EuclideanDiskEmbedding
import Wikipedia.NoExoticSixSphere.SphereExtensionWithHeight

/-!
# An embedded spanning disk after explicit stabilization

Every smooth embedded immersive sphere in Euclidean space bounds an actual
smooth embedded disk after adding a normal height and supported graph
coordinates. The disk's interior misses the entire original ambient space.
Near the boundary its map is exactly the prescribed radial extension with
normal height, followed by zero coordinates. For a three-sphere this uses
six added ambient coordinates.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

def coordinates (N d : ℕ) :
    ((EuclideanSpace ℝ (Fin N) × ℝ) × (ℝ × EuclideanSpace ℝ (Fin d))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + (1 + (1 + d)))) :=
  (ContinuousLinearEquiv.prodAssoc ℝ (EuclideanSpace ℝ (Fin N)) ℝ
    (ℝ × EuclideanSpace ℝ (Fin d))).trans
      (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
        ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (DiskGraph.extraCoordinates d))).trans
          (DiskGraph.coordinateEquiv N (1 + d)))

theorem coordinates_old (N d : ℕ) (y : EuclideanSpace ℝ (Fin N)) :
    coordinates N d ((y, 0), 0) = appendZeroMap N (1 + (1 + d)) y := by
  change DiskGraph.coordinateEquiv N (1 + d)
    (y, (0, DiskGraph.extraCoordinates d 0)) = _
  rw [map_zero]
  exact DiskGraph.coordinateEquiv_old N (1 + d) y

def collar {n N : ℕ} (b : Sphere n) (f : Sphere n → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (N + (1 + (1 + (n + 1))))) :=
  coordinates N (n + 1) (SphereExtensionWithHeight.map b f x, 0)

theorem collar_coe {n N : ℕ} (b : Sphere n) (f : Sphere n → EuclideanSpace ℝ (Fin N))
    (s : Sphere n) :
    collar b f s.val = appendZeroMap N (1 + (1 + (n + 1))) (f s) := by
  rw [collar, SphereExtensionWithHeight.map_coe, coordinates_old]

/-- No disk or collar is supplied: the original smooth sphere and its immersion suffice. -/
theorem exists_spanningDisk {n N : ℕ} (b : Sphere n)
    (f : Sphere n → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff (𝓡 n) (𝓡 N) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 n) (𝓡 N) f s)) :
    ∃ G : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (N + (1 + (1 + (n + 1))))),
      ContDiff ℝ ∞ G ∧
      IsClosedEmbedding
        (fun x : closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦ G x.val) ∧
      (∀ x ∈ closedBall 0 1, Injective (fderiv ℝ G x)) ∧
      (∀ s : Sphere n, G s.val = appendZeroMap N (1 + (1 + (n + 1))) (f s)) ∧
      (∀ x ∈ ball 0 1, G x ∉ range (appendZeroMap N (1 + (1 + (n + 1))))) ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))),
        IsOpen V ∧ sphere 0 1 ⊆ V ∧ EqOn G (collar b f) V := by
  let f₀ := SphereExtensionWithHeight.map b f
  have hf₀ := SphereExtensionWithHeight.contDiff_map b f hf
  have hd₀ : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      Injective (fderiv ℝ f₀ x) := fun x hx ↦
    SphereExtensionWithHeight.injective_fderiv_map_sphere b f hf hd ⟨x, hx⟩
  obtain ⟨g, hg, hge, hgd, hga, V, hV, hSV, _, hVg⟩ :=
    DiskGraph.exists_embedding_rel_sphere_avoiding hf₀
      (SphereExtensionWithHeight.injOn_map_sphere b f hi) hd₀ isOpen_univ
      (subset_univ _) ((univ : Set (EuclideanSpace ℝ (Fin N))) ×ˢ ({0} : Set ℝ))
      (fun x hx ↦ SphereExtensionWithHeight.avoids_oldAmbient b f hx.2)
  let L := coordinates N (n + 1)
  have hcollar : EqOn (L ∘ g) (collar b f) V := by
    intro x hx
    change L (g x) = L (f₀ x, 0)
    rw [hVg x hx]
  refine ⟨L ∘ g, L.contDiff.comp hg, L.toHomeomorph.isClosedEmbedding.comp hge,
    ?_, ?_, ?_, V, hV, hSV, hcollar⟩
  · intro x hx
    rw [(L.hasFDerivAt.comp x ((hg.differentiable (by simp) x).hasFDerivAt)).fderiv]
    exact L.injective.comp (hgd x hx)
  · intro s
    exact (hcollar (hSV s.property)).trans (collar_coe b f s)
  · intro x hx h
    obtain ⟨y, hy⟩ := h
    have he : g x = ((y, 0), 0) := L.injective (by
      rw [coordinates_old]
      exact hy.symm)
    exact hga x hx (by rw [he]; exact ⟨⟨mem_univ _, rfl⟩, rfl⟩)

end NoExoticSixSphere.StabilizedSpanningDisk
