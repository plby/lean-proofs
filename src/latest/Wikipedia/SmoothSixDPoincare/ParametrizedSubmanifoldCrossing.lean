import Wikipedia.SmoothSixDPoincare.CleanTransverseSheetChart
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Crossing charts retaining actual chosen native sheet parametrizations

The sheet coordinates may come from tubular charts adapted to already
constructed arcs. Native transversality and the two genuine parametrizations
give an actual crossing chart, with exact sheet restrictions and recognition
of the full original sheet images.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace Z P]

/-- Actual sheet charts can be prescribed, including charts adapted to existing arc germs. -/
theorem exists_clean_crossingChart_of_parametrizations {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source)
    (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, E) (A × B) M ∞,
      closedBall (0 : A) a ×ˢ closedBall (0 : B) a ⊆ Φ.source ∧
      Φ.source ⊆ c.source ×ˢ d.source ∧ Φ.target ⊆ O ∧ Φ (0, 0) = F (c 0) ∧
      (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (c u)) ∧
      (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (d v)) ∧
      (∀ q ∈ Φ.source, (Φ q ∈ range F ↔ q.2 = 0) ∧ (Φ q ∈ range G ↔ q.1 = 0)) := by
  let f := F ∘ c
  let g := G ∘ d
  have hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f c.source :=
    hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hg : ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ g d.source :=
    hG.comp_contMDiffOn d.contMDiffOn_toFun
  have hembf : IsEmbedding (fun u : c.source => f u) :=
    hembF.comp c.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hembg : IsEmbedding (fun v : d.source => g v) :=
    hembG.comp d.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hdf : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0 =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0) :=
    mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hc0)
  have hdg : mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0 =
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)).comp (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0) :=
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (d.mdifferentiableAt (by simp) hd0)
  have ht' : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0).coprod
      (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0)) := by
    rw [hdf, hdg]
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := ht w
    obtain ⟨a, ha⟩ := (PartialChart.bijective_mfderiv c hc0).2 u
    obtain ⟨b, hb⟩ := (PartialChart.bijective_mfderiv d hd0).2 v
    refine ⟨(a, b), ?_⟩
    let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)
    let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)
    let C : A →L[ℝ] D := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0
    let Q : B →L[ℝ] Z := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0
    change DF (C a) + DG (Q b) = w
    change C a = u at ha
    change Q b = v at hb
    rw [ha, hb]
    exact huv
  obtain ⟨U, hU, hpreU⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  obtain ⟨V, hV, hpreV⟩ := hembG.isInducing.isOpen_iff.mp d.open_target
  have hxU : F (c 0) ∈ U := by
    change c 0 ∈ F ⁻¹' U
    rw [hpreU]
    exact c.map_source' hc0
  have hyV : G (d 0) ∈ V := by
    change d 0 ∈ G ⁻¹' V
    rw [hpreV]
    exact d.map_source' hd0
  have hxV : F (c 0) ∈ V := hxy ▸ hyV
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart c.open_source d.open_source hc0 hd0 hf hg
      hxy hembf hembg hdim ht' (hO.inter (hU.inter hV)) ⟨hxO, hxU, hxV⟩
  refine ⟨a, ha, Φ, hprod, hsource, fun _ hq => (htarget hq).1,
    hleft 0 (hprod ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩),
    hleft, hright, ?_⟩
  intro q hq
  have hqUV := (htarget (Φ.map_source' hq)).2
  have hrangeF : Φ q ∈ range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨n, hn⟩
      have hnU : F n ∈ U := hn ▸ hqUV.1
      have hnT : n ∈ c.target := by
        change n ∈ F ⁻¹' U at hnU
        rwa [hpreU] at hnU
      refine ⟨c.invFun n, c.map_target' hnT, ?_⟩
      exact (congrArg F (c.right_inv' hnT)).trans hn
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  have hrangeG : Φ q ∈ range G ↔ Φ q ∈ g '' d.source := by
    constructor
    · rintro ⟨p, hp⟩
      have hpV : G p ∈ V := hp ▸ hqUV.2
      have hpT : p ∈ d.target := by
        change p ∈ G ⁻¹' V at hpV
        rwa [hpreV] at hpV
      refine ⟨d.invFun p, d.map_target' hpT, ?_⟩
      exact (congrArg G (d.right_inv' hpT)).trans hp
    · rintro ⟨v, _, hv⟩
      exact ⟨d v, hv⟩
  exact ⟨hrangeF.trans (himages q hq).1, hrangeG.trans (himages q hq).2⟩

end Wikipedia.SmoothSixDPoincare
