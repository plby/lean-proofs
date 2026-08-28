import Wikipedia.SmoothSixDPoincare.ChartedFaceAvoidance
import Wikipedia.SmoothSixDPoincare.LowerExteriorChart
import Wikipedia.SmoothSixDPoincare.SmoothShrunkSurgeryExistence
import Wikipedia.SmoothSixDPoincare.DisjointLowerFaceRealization

/-!
# Moving an already transported smooth face below a native surgery

The input is the actual closed face and a smooth open chart extending it.
The output has that same form in the preceding lower level. Avoidance,
shrinking, exact whole-sublevel transport, and the full lower chart are all
constructed; no global identification with an original attaching level is
assumed. This is the reusable local step for successive downward moves.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  {G H X N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H) [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]

open Classical in
theorem exists_smooth_shrunk_disjoint_chartedFace
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hd : d.HasSmoothExterior hf)
    (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ G + n < Module.finrank ℝ E - 1)
    (x₀ : X) (g : C(X × MorseHandle.UnitDisk N, d.UpperLevel)) (hg : Injective g) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ Θ : PartialDiffeomorph (I.prod 𝓘(ℝ, N)) 𝓘(ℝ, RegularLevel.Model E)
        (X × N) d.UpperLevel ∞,
      ((univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Θ.source) →
      (∀ x (w : MorseHandle.UnitDisk N), Θ (x, w.val) = g (x, w)) →
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          d.UpperLevel d.UpperLevel ∞,
        SupportedDiffeomorph.IsotopicToIdentity e ∧
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ R : d.ShrunkSurgeryRealization s,
          Nonempty R.AmbientExtension ∧ R.HasSmoothExterior hf ∧
          ∃ L : C(X × MorseHandle.UnitDisk N, d.LowerLevel),
            IsClosedEmbedding L ∧ Disjoint (range L) (range d.surgery.oldPiece) ∧
            (∀ z, (R.attachmentHomeomorph ⟨(L z).val, Or.inl (L z).property.le⟩).val =
              (e (g z)).val) ∧
            ∃ Ψ : PartialDiffeomorph (I.prod 𝓘(ℝ, N)) 𝓘(ℝ, RegularLevel.Model E)
                (X × N) d.LowerLevel ∞,
              ((univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Ψ.source) ∧
              (∀ x (w : MorseHandle.UnitDisk N), Ψ (x, w.val) = L (x, w)) ∧
              Ψ.target ⊆ (range d.surgery.oldPiece)ᶜ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  intro Θ hsource hface
  have hdim' : Module.finrank ℝ G + Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) <
      Module.finrank ℝ (RegularLevel.Model E) := by
    simpa [RegularLevel.Model] using hdim
  obtain ⟨e, he, havoid⟩ := SupportedDiffeomorph.exists_ambient_avoiding_charted_face
    Θ g hsource hface (d.belt_smooth hf n) hdim'
  let g' : C(X × MorseHandle.UnitDisk N, d.UpperLevel) :=
    ⟨fun z => e (g z), e.toHomeomorph.continuous.comp g.continuous⟩
  let Θ' := Θ.trans e.toPartialDiffeomorph
  have hsource' : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Θ'.source :=
    fun z hz => ⟨hsource hz, mem_univ _⟩
  have hface' (x) (w : MorseHandle.UnitDisk N) : Θ' (x, w.val) = g' (x, w) :=
    congrArg e (hface x w)
  obtain ⟨s, hs, hs₁, htube⟩ :=
    d.exists_closedBeltTube_avoiding_compact (isCompact_range g'.continuous) havoid
  let v₀ := SphereCoordinates.standardParametrization d.chart.PositiveCoordinates n
    (Hemisphere.point true ⟨0, by simp⟩)
  obtain ⟨R, hambient, hR⟩ := d.exists_smooth_shrunkSurgeryRealization hf hd n v₀ hs hs₁
  obtain ⟨L, hL, hdisjoint, -, hmap⟩ := R.exists_disjoint_lowerExteriorFace g'
    (g'.continuous.isClosedEmbedding (e.injective.comp hg)) htube
  let j := fun z : X × MorseHandle.UnitDisk N => (z.1, z.2.val)
  have hj (z) : j z ∈ Θ'.source := hsource' ⟨mem_univ _, z.2.property⟩
  have ht (z) : Θ' (j z) ∉ d.closedBeltTube s := by
    rw [hface' z.1 z.2]
    exact disjoint_left.mp htube ⟨z, rfl⟩
  have hm (z) : (R.attachmentHomeomorph ⟨(L z).val, Or.inl (L z).property.le⟩).val =
      (Θ' (j z)).val := by
    rw [hface' z.1 z.2]
    exact hmap z
  obtain ⟨Ψ, hΨsource, hΨpoint, hΨtarget⟩ :=
    R.exists_lowerExteriorChart hf hR (I.prod 𝓘(ℝ, N))
      j (x₀, ⟨0, by simp⟩) L Θ' hj ht hm
  refine ⟨e, he, s, hs, hs₁, R, hambient, hR, L, hL, hdisjoint, hmap, Ψ, ?_,
    fun x w => hΨpoint (x, w), hΨtarget⟩
  rintro ⟨x, w⟩ ⟨_, hw⟩
  exact hΨsource (x, ⟨w, hw⟩)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
