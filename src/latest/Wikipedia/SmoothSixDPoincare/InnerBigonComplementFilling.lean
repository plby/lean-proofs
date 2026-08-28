import Wikipedia.SmoothSixDPoincare.InnerCleanBigonBoundary
import Wikipedia.SmoothSixDPoincare.SmoothBigonNeighborhoodExtension
import Wikipedia.SmoothSixDPoincare.OpenComplementAvoidance

/-!
# Inner bigon fillings with the contraction performed in the actual complement

The circle contractions in `U` are explicit hypotheses of these intermediate
lemmas. They are not inferred from ambient simple connectedness. The resulting
smooth filling remains in `U` globally and preserves the whole actual inner
boundary germ. The complement contractions still need to come from the handle
geometry in the proof of the unconditional target.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Contractions inside `U` give an actual smooth inner filling, preserving the full clean
boundary germ, native immersion, and local embeddedness. -/
theorem CleanBigonBoundary.exists_smooth_inner_extension_in_open
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h)
    (U : Opens M) (hU : (S ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧ innerBigonCollar h r ⊆ d.domain ∧
      ∃ F : C(ℝ × ℝ, U),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
      ∃ W : Set (ℝ × ℝ), IsOpen W ∧ frontier (bigon h) ⊆ W ∧
        EqOn (Subtype.val ∘ F) (d.map ∘ innerBigonMap h r) W ∧ InjOn F W ∧
        (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
        ∀ p ∈ W, (F p : M) ∉ S ∪ T := by
  classical
  obtain ⟨r, hr, hcollar, V, hV, hfrontV, hsmooth, hinj, hderiv, -, havoid⟩ :=
    d.exists_inner_clean_neighborhood
  have hzero : (0 : ℝ × ℝ) ∈ frontier (bigon h) := by
    rw [mem_frontier_bigon_iff]
    refine ⟨?_, Or.inl rfl⟩
    change 0 ≤ (0 : ℝ) ∧ h * 0 ^ 2 + 0 ≤ h
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
      And.intro le_rfl d.height_pos.le
  let c : U := ⟨d.map (innerBigonMap h r 0), hU (havoid 0 (hfrontV hzero))⟩
  let f : (ℝ × ℝ) → U := fun p =>
    if hp : p ∈ V then ⟨d.map (innerBigonMap h r p), hU (havoid p hp)⟩ else c
  have hval (p : ℝ × ℝ) (hp : p ∈ V) : (f p : M) = d.map (innerBigonMap h r p) := by
    dsimp [f]
    rw [dif_pos hp]
  have hfval : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ f) V :=
    hsmooth.congr (fun p hp => hval p hp)
  have hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f V := by
    intro p hp
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U f V p).mp (hfval p hp)
  obtain ⟨F, hF, W, hW, hfrontW, hWV, hEq⟩ :=
    exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies hnull
      d.height_pos hV hf hfrontV
  have hEqval : EqOn (Subtype.val ∘ F) (d.map ∘ innerBigonMap h r) W := by
    intro p hp
    exact (congrArg Subtype.val (hEq hp)).trans (hval p (hWV hp))
  have hinjF : InjOn F W := by
    intro p hp q hq hpq
    apply hinj (hWV hp) (hWV hq)
    exact (hEqval hp).symm.trans ((congrArg Subtype.val hpq).trans (hEqval hq))
  refine ⟨r, hr, hcollar, F, hF, W, hW, hfrontW, hEqval, hinjF, ?_, ?_⟩
  · intro p hp
    have heq : (Subtype.val ∘ F) =ᶠ[𝓝 p] (d.map ∘ innerBigonMap h r) :=
      mem_of_superset (hW.mem_nhds hp) (fun _ hq => hEqval hq)
    have hi : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p) := by
      rw [heq.mfderiv_eq]
      exact hderiv p (hWV hp)
    have hc : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) :=
      contMDiff_subtype_val
    rw [mfderiv_comp p (hc.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))] at hi
    intro v w hvw
    apply hi
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) (F p)) hvw
  · intro p hp
    change (Subtype.val ∘ F) p ∉ S ∪ T
    rw [hEqval hp]
    exact havoid p (hWV hp)

variable [FiniteDimensional ℝ E] [T2Space M]
  {D Y : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace Y] [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y]

/-- The actual inner boundary has an embedded immersive filling in `U` disjoint from the
full compact obstacle, with the entire original inner boundary germ retained. -/
theorem CleanBigonBoundary.exists_embedded_inner_extension_in_open
    (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (range g) T a b k l h)
    (U : Opens M) (hU : (range g ∪ T)ᶜ ⊆ U)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, U),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E)
    (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧ innerBigonCollar h r ⊆ d.domain ∧
      ∃ F : C(ℝ × ℝ, U),
      ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
      IsClosedEmbedding (fun p : bigon h => F p) ∧
      (∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p)) ∧
      (∀ p ∈ bigon h, (F p : M) ∉ range g) ∧
      ∃ W : Set (ℝ × ℝ), IsOpen W ∧ frontier (bigon h) ⊆ W ∧
        EqOn (Subtype.val ∘ F) (d.map ∘ innerBigonMap h r) W := by
  obtain ⟨r, hr, hcollar, F, hF, V, hV, hfrontV, hEq, hinj, hderiv, havoid⟩ :=
    d.exists_smooth_inner_extension_in_open U hU hnull
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, -, hC, hfrontC, hCV⟩ := exists_compact_closed_between hcompact hV hfrontV
  have hinjC : InjOn F (bigon h ∩ C) := hinj.mono (inter_subset_right.trans hCV)
  have hiC : ∀ p ∈ bigon h ∩ C,
      Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p) :=
    fun p hp => hderiv p (hCV hp.2)
  have hclean : ∀ p ∈ bigon h ∩ C, p ∉ (∅ : Set (ℝ × ℝ)) → (F p : M) ∉ range g := by
    intro p hp _ hmem
    exact havoid p (hCV hp.2) (Or.inl hmem)
  obtain ⟨G, hG, hhom, hemb, hiG, havoidG⟩ :=
    ManifoldImmersion.exists_relative_embedded_avoidance_in_open U F g hF hg
      (by simp [Module.finrank_prod]) hdim (by simpa [Module.finrank_prod] using hobstacle)
      (isCompact_bigon d.height_pos) hC (empty_subset _) hinjC hiC hclean
  refine ⟨r, hr, hcollar, G, hG, hemb, hiG, ?_, interior C, isOpen_interior, hfrontC, ?_⟩
  · intro p hp
    exact havoidG p ⟨hp, notMem_empty p⟩
  · intro p hp
    have hpC : p ∈ C := interior_subset hp
    exact (congrArg Subtype.val (hhom.fst_eq_snd hpC)).symm.trans (hEq (hCV hpC))

end Wikipedia.SmoothSixDPoincare
