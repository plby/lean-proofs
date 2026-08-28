import Wikipedia.SmoothSixDPoincare.TubularBigonPlanarFrame
import Wikipedia.SmoothSixDPoincare.ComplementFrameTransport

/-!
# A complete normal frame adapted to both actual boundary sheets

The first two columns are kept unchanged. Transport the actual upper-sheet
frame from the point with the same arc time using the existing full splitting.
This gives exactly the upper-sheet columns on its arc and remains a complement
throughout the bigon. Openness supplies an invertible frame on a neighborhood.

This is a statement about the actual normal derivatives, not yet an exact
nonlinear coordinate chart for the sheets.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  (tube : TubularBigon (E := E) S T a b k.map l.map h)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
    (E := E) S k.map)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
    (E := E) T l.map)

/-- Construct both pairs of normal columns with their actual lower/upper sheet restrictions. -/
theorem exists_adapted_planar_frame_of_opposite_corner_signs
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
      ContDiff ℝ ∞ W ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
      ∃ O : Set (ℝ × ℝ), IsOpen O ∧ bigon h ⊆ O ∧
        ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
          ContDiffOn ℝ ∞ C O ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            C (upperBoundaryArc h t) = e.normalFrame tube.chart t) ∧
          ∀ p ∈ O, Bijective ((W p).coprod (C p)) := by
  obtain ⟨W, hW, hlo, hhi, V, hV, hKV, B, hB, -, hb⟩ :=
    tube.exists_planar_frame_of_opposite_corner_signs d e hsign
  obtain ⟨⟨D, hD, hID, hG⟩, -⟩ := tube.upper_sheetFrame e
  let r : (ℝ × ℝ) → (ℝ × ℝ) := upperBoundaryArc h ∘ arcTime
  have hq : ContDiff ℝ ∞ (upperBoundaryArc h) := by unfold upperBoundaryArc; fun_prop
  have hr : ContDiff ℝ ∞ r := hq.comp contDiff_arcTime
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have htq (t : ℝ) : arcTime (upperBoundaryArc h t) = t := htime t _
  have hrq (t : ℝ) : r (upperBoundaryArc h t) = upperBoundaryArc h t := by
    dsimp only [r, Function.comp_apply]
    rw [htq]
  have htimeK : MapsTo arcTime (bigon h) (Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have hrK : MapsTo r (bigon h) (bigon h) :=
    fun _ hp => tube.upperBoundaryArc_mem_bigon (htimeK hp)
  let O₀ := V ∩ (r ⁻¹' V ∩ arcTime ⁻¹' D)
  have hO₀ : IsOpen O₀ :=
    hV.inter ((hV.preimage hr.continuous).inter (hD.preimage contDiff_arcTime.continuous))
  have hKO₀ : bigon h ⊆ O₀ := fun p hp => ⟨hKV hp, hKV (hrK hp), hID (htimeK hp)⟩
  let C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)) :=
    fun p => transportComplement (W p) (B p) (W (r p)) (B (r p))
      (e.normalFrame tube.chart (arcTime p))
  have hC : ContDiffOn ℝ ∞ C O₀ := by
    apply contDiffOn_transportComplement hO₀ hW.contDiffOn (hB.mono inter_subset_left)
      (hW.comp hr).contDiffOn (hB.comp hr.contDiffOn (fun _ hp => hp.2.1))
      (hG.comp contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
    intro p hp
    exact isInvertible_coprod_of_bijective (W (r p)) (B (r p)) (hb _ hp.2.1)
  have hcompK : ∀ p ∈ bigon h, Bijective ((W p).coprod (C p)) := by
    intro p hp
    have ht := htimeK hp
    have hupper : Bijective ((W (r p)).coprod (e.normalFrame tube.chart (arcTime p))) :=
      bijective_coprod_comm _ _ (hhi (arcTime p) ht)
    exact bijective_transportComplement (W p) (B p) (W (r p)) (B (r p)) _
      (isInvertible_coprod_of_bijective _ _ (hb p (hKV hp)))
      (isInvertible_coprod_of_bijective _ _ (hb _ (hKV (hrK hp)))) hupper
  have hTC : ContDiffOn ℝ ∞ (fun p => (W p).coprod (C p)) O₀ :=
    contDiffOn_coprod hW.contDiffOn hC
  let O := O₀ ∩ {p | Injective ((W p).coprod (C p))}
  have hO : IsOpen O :=
    hTC.continuousOn.isOpen_inter_preimage hO₀ ContinuousLinearMap.isOpen_injective
  have hKO : bigon h ⊆ O := fun p hp => ⟨hKO₀ hp, (hcompK p hp).1⟩
  refine ⟨W, hW, hlo, O, hO, hKO, C, hC.mono inter_subset_left, ?_, ?_⟩
  · intro t ht
    dsimp only [C]
    rw [hrq, htq]
    exact transportComplement_self _ _ _ (isInvertible_coprod_of_bijective _ _
      (hb _ (hKV (tube.upperBoundaryArc_mem_bigon ht))))
  · intro p hp
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact ⟨hp.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hp.2⟩

end Wikipedia.SmoothSixDPoincare.TubularBigon
