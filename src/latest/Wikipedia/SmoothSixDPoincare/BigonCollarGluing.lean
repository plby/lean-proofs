import Wikipedia.SmoothSixDPoincare.InnerBigonCollarAvoidance
import Wikipedia.SmoothSixDPoincare.SmoothOpenGluing
import Wikipedia.SmoothSixDPoincare.StarConvexSmoothExtension

/-!
# Glue a collar-disjoint inner disk to the original cornered bigon boundary

The maps agree on an entire neighborhood of the shared inner frontier. The
actual collar-disjointness condition excludes mixed interior intersections.
The resulting whole bigon is embedded and immersive, misses both sheets in
its interior, and retains every original boundary germ. A smooth star-convex
extension then makes the map global without changing it near the bigon.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

/-- An actual collar-disjoint inner filling gives the complete clean embedded immersive bigon,
with a global smooth map and the entire original boundary germ retained. -/
theorem exists_filled_clean_bigon_of_collar_disjoint_inner
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hcollar : innerBigonCollar h r ⊆ d.domain)
    (F : C(ℝ × ℝ, M)) (hF : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F)
    (hinjF : InjOn F (bigon h))
    (hiF : ∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p))
    (havoidF : ∀ p ∈ bigon h, F p ∉ S ∪ T)
    (hcollarF : ∀ p ∈ interior (bigon h), F p ∉ d.map '' innerBigonCollar h r)
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hfrontW : frontier (bigon h) ⊆ W)
    (hEq : EqOn F (d.map ∘ innerBigonMap h r) W) :
    ∃ f : C(ℝ × ℝ, M), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
      IsClosedEmbedding (fun p : bigon h => f p) ∧
      (∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
      (∀ p ∈ interior (bigon h), f p ∉ S ∪ T) ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ frontier (bigon h) ⊆ V ∧ EqOn f d.map V := by
  let c := innerBigonDiffeomorph h r hr.1.ne'
  let core : Set (ℝ × ℝ) := c '' bigon h
  let P : Set (ℝ × ℝ) := c '' (interior (bigon h) ∪ W)
  let Q : Set (ℝ × ℝ) := d.domain \ c '' (bigon h \ W)
  let G : (ℝ × ℝ) → M := F ∘ c.symm
  have hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G := hF.comp c.symm.contMDiff
  have hP : IsOpen P := c.toHomeomorph.isOpenMap _ (isOpen_interior.union hW)
  have hQ : IsOpen Q := d.open_domain.inter
    (((isCompact_bigon d.height_pos).inter_right hW.isClosed_compl).image
      c.continuous).isClosed.isOpen_compl
  have hfront (p : ℝ × ℝ) (hp : p ∈ bigon h) (hi : p ∉ interior (bigon h)) :
      p ∈ frontier (bigon h) := by
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp, hi⟩
  have hcoreP : core ⊆ P := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    by_cases hi : p ∈ interior (bigon h)
    · exact Or.inl hi
    · exact Or.inr (hfrontW (hfront p hp hi))
  have hcollarQ : innerBigonCollar h r ⊆ Q := by
    intro p hp
    refine ⟨hcollar hp, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact hz.2 (hfrontW ((innerBigonMap_mem_collar_iff d.height_pos hr hz.1).mp hp))
  have hnotCore (p : ℝ × ℝ) (hp : p ∈ bigon h) (hn : p ∉ core) :
      p ∈ innerBigonCollar h r :=
    ⟨hp, fun hi => hn (image_mono interior_subset hi)⟩
  have hcover : bigon h ⊆ P ∪ Q := by
    intro p hp
    by_cases hc : p ∈ core
    · exact Or.inl (hcoreP hc)
    · exact Or.inr (hcollarQ (hnotCore p hp hc))
  have hfrontQ : frontier (bigon h) ⊆ Q := by
    intro p hp
    apply hcollarQ
    refine ⟨((mem_frontier_bigon_iff h p).mp hp).1, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hi : p ∈ interior (bigon h) :=
      heq ▸ innerBigonMap_mem_interior d.height_pos hr (interior_subset hz)
    rw [frontier] at hp
    exact hp.2 hi
  have hmatch : EqOn G d.map (P ∩ Q) := by
    rintro p ⟨hp, hq⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hzW : z ∈ W := by
      rcases hz with hz | hz
      · by_contra hn
        exact hq.2 ⟨z, ⟨interior_subset hz, hn⟩, rfl⟩
      · exact hz
    change F (c.symm (c z)) = d.map (c z)
    rw [c.symm_apply_apply]
    exact hEq hzW
  obtain ⟨j, hj, hjG, hjd⟩ := exists_smooth_open_gluing hP hQ hG.contMDiffOn
    (d.smooth.mono inter_subset_left) hmatch
  have hjInner (p : ℝ × ℝ) (hp : p ∈ bigon h) : j (c p) = F p :=
    (hjG (hcoreP ⟨p, hp, rfl⟩)).trans (congrArg F (c.symm_apply_apply p))
  have hjCollar (p : ℝ × ℝ) (hp : p ∈ innerBigonCollar h r) : j p = d.map p :=
    hjd (hcollarQ hp)
  have hcross (p : ℝ × ℝ) (hp : p ∈ bigon h) (z : ℝ × ℝ)
      (hz : z ∈ innerBigonCollar h r) (heq : F p = d.map z) : c p = z := by
    by_cases hi : p ∈ interior (bigon h)
    · exact False.elim (hcollarF p hi ⟨z, hz, heq.symm⟩)
    · have hpf := hfront p hp hi
      apply d.injective
        (hcollar ((innerBigonMap_mem_collar_iff d.height_pos hr hp).mpr hpf)) (hcollar hz)
      exact (hEq (hfrontW hpf)).symm.trans heq
  have hinj : InjOn j (bigon h) := by
    intro p hp z hz heq
    by_cases hpCore : p ∈ core
    · obtain ⟨p', hp', rfl⟩ := hpCore
      rw [hjInner p' hp'] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact congrArg c (hinjF hp' hz' heq)
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact hcross p' hp' z hzC heq
    · have hpC := hnotCore p hp hpCore
      rw [hjCollar p hpC] at heq
      by_cases hzCore : z ∈ core
      · obtain ⟨z', hz', rfl⟩ := hzCore
        rw [hjInner z' hz'] at heq
        exact (hcross z' hz' p hpC heq.symm).symm
      · have hzC := hnotCore z hz hzCore
        rw [hjCollar z hzC] at heq
        exact d.injective (hcollar hpC) (hcollar hzC) heq
  have hi : ∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) j p) := by
    intro p hp
    by_cases hpCore : p ∈ core
    · have heq : j =ᶠ[𝓝 p] G :=
        mem_of_superset (hP.mem_nhds (hcoreP hpCore)) (fun _ hx => hjG hx)
      rw [heq.mfderiv_eq]
      change Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (F ∘ c.symm) p)
      rw [mfderiv_comp p (hF.mdifferentiableAt (by simp))
        (c.symm.contMDiff.mdifferentiableAt (by simp))]
      have hpin : c.symm p ∈ bigon h := by
        obtain ⟨z, hz, rfl⟩ := hpCore
        rwa [c.symm_apply_apply]
      exact (hiF _ hpin).comp
        (PartialChart.bijective_mfderiv c.symm.toPartialDiffeomorph (mem_univ p)).injective
    · have hpC := hnotCore p hp hpCore
      have heq : j =ᶠ[𝓝 p] d.map :=
        mem_of_superset (hQ.mem_nhds (hcollarQ hpC)) (fun _ hx => hjd hx)
      rw [heq.mfderiv_eq]
      exact d.derivative_injective p (hcollar hpC)
  have havoid : ∀ p ∈ interior (bigon h), j p ∉ S ∪ T := by
    intro p hp
    by_cases hpCore : p ∈ core
    · obtain ⟨z, hz, rfl⟩ := hpCore
      rw [hjInner z hz]
      exact havoidF z hz
    · have hpC := hnotCore p (interior_subset hp) hpCore
      rw [hjCollar p hpC]
      exact d.interior_avoids p ⟨hcollar hpC, hp⟩
  obtain ⟨f, hf, V, hV, hKV, -, hfj⟩ := exists_smooth_extension_near_starConvex
    (isCompact_bigon d.height_pos) (zero_mem_bigon d.height_pos.le)
    (starConvex_bigon d.height_pos.le) (hP.union hQ) hcover hj
  have hinjf : InjOn f (bigon h) := by
    intro p hp z hz heq
    apply hinj hp hz
    exact (hfj (hKV hp)).symm.trans (heq.trans (hfj (hKV hz)))
  have hembf : IsClosedEmbedding (fun p : bigon h => f p) := by
    let : CompactSpace (bigon h) := isCompact_iff_compactSpace.mp (isCompact_bigon d.height_pos)
    apply (hf.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p z heq
    exact Subtype.ext (hinjf p.property z.property heq)
  refine ⟨⟨f, hf.continuous⟩, hf, hembf, ?_, ?_, V ∩ Q, hV.inter hQ, ?_, ?_⟩
  · intro p hp
    have heq : f =ᶠ[𝓝 p] j :=
      mem_of_superset (hV.mem_nhds (hKV hp)) (fun _ hx => hfj hx)
    change Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)
    rw [heq.mfderiv_eq]
    exact hi p hp
  · intro p hp
    change f p ∉ S ∪ T
    rw [hfj (hKV (interior_subset hp))]
    exact havoid p hp
  · intro p hp
    exact ⟨hKV ((mem_frontier_bigon_iff h p).mp hp).1, hfrontQ hp⟩
  · intro p hp
    exact (hfj hp.1).trans (hjd hp.2)

end Wikipedia.SmoothSixDPoincare
