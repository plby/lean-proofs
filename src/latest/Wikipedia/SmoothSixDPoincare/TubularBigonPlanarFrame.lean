import Wikipedia.SmoothSixDPoincare.TubularBigonIntersectionSigns
import Wikipedia.SmoothSixDPoincare.BigonBoundaryField
import Wikipedia.SmoothSixDPoincare.TwoFrameFieldExtension

/-!
# A constructed planar normal two-frame for an opposite-sign tubular bigon

The lower sheet field and the constructed upper complement have matching
whole corner germs. They glue near the actual bigon frontier and extend
as an injective two-frame over the disk. Complementary columns are then
constructed on an open disk neighborhood. The original lower-frame germs
are retained, and the extended frame complements the actual upper sheet.

The newly constructed complementary columns have no prescribed sheet germs.
This result does not construct a sheet-compatible tubular map or cancel handles.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

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

/-- Construct a genuine local field on a neighborhood of the entire frontier. -/
theorem exists_planar_boundary_frame_of_opposite_corner_signs
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ frontier (bigon h) ⊆ O ∧
      ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
        ContDiffOn ℝ ∞ W O ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          Bijective ((e.normalFrame tube.chart t).coprod
            (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
        ∀ p ∈ frontier (bigon h), Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_boundary_complement_of_opposite_corner_signs d e hsign
  obtain ⟨U, V, hU, hV, hfront, hlow, hupp, W, hW, hWL, hWH⟩ :=
    exists_smooth_bigon_boundary_field tube.height_pos hD hID hL hH h0 h1
  have htime (t y : ℝ) : arcTime (2 * t - 1, y) = t := by dsimp [arcTime]; ring
  have hHi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (H t) := by
    intro t ht u v huv
    have heq : ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  refine ⟨U ∪ V, hU.union hV, hfront, W, hW, ?_, ?_, ?_⟩
  · intro t ht
    filter_upwards [hU.mem_nhds (hlow ht)] with p hp
    exact hWL hp
  · intro t ht
    rw [hWH (hupp ht)]
    dsimp only [Function.comp_apply]
    rw [htime]
    exact hcomp t (hID ht)
  · intro p hp
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hp
    · rw [hWL (hlow ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact (tube.lower_sheetFrame d).2 t ht
    · rw [hWH (hupp ht)]
      dsimp only [Function.comp_apply]
      rw [htime]
      exact hHi t ht

/-- Extend the actual sheet-compatible two-frame across the disk and complete it nearby. -/
theorem exists_planar_frame_of_opposite_corner_signs
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
      ContDiff ℝ ∞ W ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Bijective ((e.normalFrame tube.chart t).coprod
          (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ bigon h ⊆ V ∧
        ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
          ContDiffOn ℝ ∞ B V ∧
          (∀ p ∈ bigon h, (B p).range = (W p).rangeᗮ) ∧
          ∀ p ∈ V, Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_planar_boundary_frame_of_opposite_corner_signs d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    FrameField.exists_completed_frame_of_local_field_finrank_two
      (D := EuclideanSpace ℝ (Fin 2)) finrank_euclideanSpace_fin hO hW₀
      isClosed_frontier hfront (isCompact_bigon tube.height_pos)
      (starConvex_bigon tube.height_pos.le) (zero_mem_bigon tube.height_pos.le)
      (fun p hp => hinj p hp.2) finrank_euclideanSpace_fin
  refine ⟨W, hW, ?_, ?_, V, hV, hKV, B, hB, hr, hb⟩
  · intro t ht
    have hp : (2 * t - 1, 0) ∈ frontier (bigon h) :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
    exact (heq.filter_mono (nhds_le_nhdsSet hp)).trans (hlo t ht)
  · intro t ht
    have hp : (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (bigon h) :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
    rw [heq.self_of_nhdsSet hp]
    exact hhi t ht

end Wikipedia.SmoothSixDPoincare.TubularBigon
