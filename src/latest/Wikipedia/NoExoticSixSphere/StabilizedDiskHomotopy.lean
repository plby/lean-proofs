import Wikipedia.NoExoticSixSphere.SupportedGraphHomotopy
import Wikipedia.NoExoticSixSphere.FramedSpanningDisk

/-!
# Comparing embedded disks through exact relative stabilized homotopies

Two smooth embedded immersed disks with a common open boundary collar are
joined after five-coordinate stabilization. The homotopy is jointly smooth,
every disk remains embedded and immersive, and the entire common smaller
collar is fixed. Both endpoints are exactly zero-coordinate stabilization.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization

theorem exists_homotopy_rel_collar {N : ℕ} (f g : Vector 4 → Vector N)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfe : IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ f x.val))
    (hge : IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ g x.val))
    (hfi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ f x))
    (hgi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ g x))
    {U : Set (Vector 4)} (hU : IsOpen U) (hSU : sphere 0 1 ⊆ U) (heq : EqOn f g U) :
    ∃ H : ℝ → Vector 4 → Vector (N + 5), ContDiff ℝ ∞ (Function.uncurry H) ∧
      (∀ t, IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ H t x.val)) ∧
      (∀ t x, x ∈ closedBall (0 : Vector 4) 1 → Injective (fderiv ℝ (H t) x)) ∧
      (∀ x, H 0 x = appendZeroMap N 5 (f x)) ∧
      (∀ x, H 1 x = appendZeroMap N 5 (g x)) ∧
      ∃ V : Set (Vector 4), IsOpen V ∧ sphere 0 1 ⊆ V ∧ V ⊆ U ∧
        ∀ t x, x ∈ V → H t x = appendZeroMap N 5 (f x) := by
  obtain ⟨r, hr, hr1, hsub⟩ := exists_annulus_subset_sphere_neighborhood hU hSU
  let β := DiskGraph.cutoff (Vector 4) r hr
  have hβ : ContDiff ℝ ∞ β := β.contDiff
  have hzero (x : Vector 4) (hx : x ∈ closedBall 0 1) (hz : β x = 0) : x ∈ U :=
    hsub ⟨hx, (DiskGraph.cutoff_eq_zero_iff r hr x).mp hz⟩
  have hfj : InjOn f (closedBall (0 : Vector 4) 1) := fun x hx y hy h ↦
    congrArg Subtype.val (hfe.injective (show f (⟨x, hx⟩ : closedBall (0 : Vector 4) 1).val =
      f (⟨y, hy⟩ : closedBall (0 : Vector 4) 1).val from h))
  have hgj : InjOn g (closedBall (0 : Vector 4) 1) := fun x hx y hy h ↦
    congrArg Subtype.val (hge.injective (show g (⟨x, hx⟩ : closedBall (0 : Vector 4) 1).val =
      g (⟨y, hy⟩ : closedBall (0 : Vector 4) 1).val from h))
  let L := DiskGraph.coordinateEquiv N 4
  let G := SupportedGraphHomotopy.map f g β
  have hGs : ContDiff ℝ ∞ (Function.uncurry G) :=
    SupportedGraphHomotopy.contDiff_map f g β hf hg hβ
  have hGt (t : ℝ) : ContDiff ℝ ∞ (G t) :=
    hGs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨fun t x ↦ L (G t x), L.contDiff.comp hGs, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    apply ((L.contDiff.comp (hGt t)).continuous.comp continuous_subtype_val).isClosedEmbedding
    intro x y h
    exact Subtype.ext (SupportedGraphHomotopy.injOn_map f g β heq hzero hfj hgj t
      x.property y.property (L.injective h))
  · intro t x hx
    change Injective (fderiv ℝ (L ∘ G t) x)
    rw [(L.hasFDerivAt.comp x (((hGt t).differentiable (by simp) x).hasFDerivAt)).fderiv]
    exact L.injective.comp
      (SupportedGraphHomotopy.injective_fderiv_map f g β hf hg hβ hU heq hzero hfi hgi t hx)
  · intro x
    change L (SupportedGraphHomotopy.map f g β 0 x) = _
    rw [SupportedGraphHomotopy.map_zero]
    exact DiskGraph.coordinateEquiv_old N 4 (f x)
  · intro x
    change L (SupportedGraphHomotopy.map f g β 1 x) = _
    rw [SupportedGraphHomotopy.map_one]
    exact DiskGraph.coordinateEquiv_old N 4 (g x)
  · refine ⟨U ∩ {x | r < ‖x‖}, hU.inter (isOpen_lt continuous_const continuous_norm),
      ?_, inter_subset_left, ?_⟩
    · intro x hx
      refine ⟨hSU hx, ?_⟩
      have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
      exact hr1.trans_eq hn.symm
    · intro t x hx
      change L (SupportedGraphHomotopy.map f g β t x) = _
      rw [SupportedGraphHomotopy.map_eq f g β t (heq hx.1)
        ((DiskGraph.cutoff_eq_zero_iff r hr x).mpr hx.2.le)]
      exact DiskGraph.coordinateEquiv_old N 4 (f x)

namespace DiskData

theorem exists_homotopy_stabilized {N : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N}
    (D₀ D₁ : DiskData b f) :
    ∃ H : ℝ → Vector 4 → Vector (N + 11), ContDiff ℝ ∞ (Function.uncurry H) ∧
      (∀ t, IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ H t x.val)) ∧
      (∀ t x, x ∈ closedBall (0 : Vector 4) 1 → Injective (fderiv ℝ (H t) x)) ∧
      (∀ x, H 0 x = appendZeroMap (N + 6) 5 (D₀.toFun x)) ∧
      (∀ x, H 1 x = appendZeroMap (N + 6) 5 (D₁.toFun x)) ∧
      ∃ V : Set (Vector 4), IsOpen V ∧ sphere 0 1 ⊆ V ∧
        ∀ t x, x ∈ V → H t x = appendZeroMap (N + 6) 5 (collar b f x) := by
  obtain ⟨U₀, hU₀, hS₀, h₀⟩ := D₀.collar_eq
  obtain ⟨U₁, hU₁, hS₁, h₁⟩ := D₁.collar_eq
  have heq : EqOn D₀.toFun D₁.toFun (U₀ ∩ U₁) :=
    fun _ hx ↦ (h₀ hx.1).trans (h₁ hx.2).symm
  obtain ⟨H, hH, hHe, hHi, hH₀, hH₁, V, hV, hSV, hVU, hfixed⟩ :=
    exists_homotopy_rel_collar D₀.toFun D₁.toFun D₀.smooth D₁.smooth
      D₀.embedded D₁.embedded D₀.immersive D₁.immersive (hU₀.inter hU₁)
      (fun _ hx ↦ ⟨hS₀ hx, hS₁ hx⟩) heq
  refine ⟨H, hH, hHe, hHi, hH₀, hH₁, V, hV, hSV, ?_⟩
  intro t x hx
  exact (hfixed t x hx).trans (congrArg (appendZeroMap (N + 6) 5) (h₀ (hVU hx).1))

end DiskData

end NoExoticSixSphere.StabilizedSpanningDisk
