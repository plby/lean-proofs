import Wikipedia.SmoothSixDPoincare.TubularBigonCornerFrames
import Wikipedia.SmoothSixDPoincare.ComplementFrameGermJoin
import Wikipedia.SmoothSixDPoincare.BigonBoundaryField

/-!
# A constructed one-plus-two normal frame over the five-dimensional tubular bigon

The two-dimensional first sheet supplies one normal column. Same-sign actual
endpoint normal determinants construct a complementary line along the other
edge with matching corner germs. These columns glue near the whole frontier,
extend without zeros across the disk, and admit a constructed complementary
two-frame. Relating the sign to native intersection signs and constructing
the sheet-compatible ambient chart remain separate obligations.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

/-- One fixed coordinate model for the upper normal two-plane followed by the lower normal line. -/
def rankThreePairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

/-- The actual determinant of the unequal normal frames in the same fixed model at both ends. -/
def rankThreePairDet
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (B : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (rankThreePairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

end Wikipedia.SmoothSixDPoincare.FrameField

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3))
    (E := E) S k.map)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))
    (E := E) T l.map)

/-- The genuine endpoint normal determinants construct the upper-edge complementary line. -/
theorem exists_rankThree_boundary_complement_of_normal_sign
    (hsign : 0 < rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
      ∃ H : ℝ → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
        ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
        (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
        (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, -⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, -, hRC⟩ :=
    tube.upper_sheetFrame_complement_of_finrank e 1 (by simp only [finrank_euclideanSpace_fin])
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from inter_subset_right)
  have hsplit : ∀ t ∈ U, Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    exists_smooth_complement_with_germs_of_frame_sign_of_finrank_one_or_two
      (Or.inl finrank_euclideanSpace_fin) rankThreePairCoordinates hU hIU hRU hCU hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

/-- The lower normal line and the constructed upper complement give an injective local
one-column field around the entire original cornered frontier. -/
theorem exists_rankThree_planar_boundary_frame_of_normal_sign
    (hsign : 0 < rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ frontier (bigon h) ⊆ O ∧
      ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
        ContDiffOn ℝ ∞ W O ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          Bijective ((e.normalFrame tube.chart t).coprod
            (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
        ∀ p ∈ frontier (bigon h), Injective (W p) := by
  obtain ⟨D, hD, hID, hL, H, hH, hcomp, h0, h1⟩ :=
    tube.exists_rankThree_boundary_complement_of_normal_sign d e hsign
  have hHi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (H t) := by
    intro t ht u v huv
    have heq : ((e.normalFrame tube.chart t).coprod (H t)) (0, u) =
        ((e.normalFrame tube.chart t).coprod (H t)) (0, v) := by
      simpa only [ContinuousLinearMap.coprod_apply, map_zero, zero_add] using huv
    exact congrArg Prod.snd ((hcomp t (hID ht)).1 heq)
  obtain ⟨O, hO, hfront, W, hW, hlo, hhi, hinj⟩ :=
    exists_injective_bigon_boundary_field tube.height_pos hD hID hL hH h0 h1
      (tube.lower_sheetFrame d).2 hHi
  refine ⟨O, hO, hfront, W, hW, hlo, ?_, hinj⟩
  intro t ht
  rw [(hhi t ht).eq_of_nhds]
  have htime : arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = t := by
    dsimp [arcTime]
    ring
  change Bijective ((e.normalFrame tube.chart t).coprod
    (H (arcTime (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))))
  rw [htime]
  exact hcomp t (hID ht)

/-- Extend the actual lower normal column across the whole disk and construct its
complementary two-frame, retaining the lower germs and upper complement condition. -/
theorem exists_rankThree_planar_frame_of_normal_sign
    (hsign : 0 < rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Bijective ((e.normalFrame tube.chart t).coprod
          (W (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))))) ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ bigon h ⊆ V ∧
        ∃ B : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
          ContDiffOn ℝ ∞ B V ∧
          (∀ p ∈ bigon h, (B p).range = (W p).rangeᗮ) ∧
          ∀ p ∈ V, Bijective ((W p).coprod (B p)) := by
  obtain ⟨O, hO, hfront, W₀, hW₀, hlo, hhi, hinj⟩ :=
    tube.exists_rankThree_planar_boundary_frame_of_normal_sign d e hsign
  obtain ⟨W, hW, heq, V, hV, hKV, B, hB, hr, hb⟩ :=
    exists_completed_one_column_frame finrank_euclideanSpace_fin hO hW₀
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
