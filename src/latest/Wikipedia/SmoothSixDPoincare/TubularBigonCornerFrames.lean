import Wikipedia.SmoothSixDPoincare.NativeCornerFrameComplement
import Wikipedia.SmoothSixDPoincare.TubularBigonSheetFrames

/-!
# The two constructed normal frames are complementary at both actual corners

At time zero or one, both retained strip germs lie in the same tubular disk
germ. Original native transversality therefore makes the two two-frames span
the four-dimensional normal model. Their combined map is an actual linear
isomorphism at either corner. No intersection-sign condition is asserted here.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

variable {E M D D' N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup D'] [NormedSpace ℝ D']
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace D' P]

/-- The actual sheet frames are complementary at each corner of the constructed tubular bigon. -/
theorem corner_sheetFrames_bijective_of_finrank
    {A B C H : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {F : N → M} {G : P → M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) (range F) (range G) a k₀ k₁}
    {l : CleanStripPatch (E := E) (range G) (range F) b l₀ l₁}
    (tube : TubularBigon (E := E) (range F) (range G) a b k.map l.map h n)
    (d : StripNormalData A B
      (E := E) (range F) k.map)
    (e : StripNormalData C H
      (E := E) (range G) l.map)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D') 𝓘(ℝ, E) ∞ G)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x : N} {y : P}
    (hx : F x = a t) (hy : G y = b t)
    (htrans : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, D') 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ C = n) :
    Bijective ((d.normalFrame tube.chart t).coprod (e.normalFrame tube.chart t)) := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by
    rcases ht with rfl | rfl <;> ring
  have hpoint : (2 * t - 1, 0) ∈ bigon h := by
    have hf : (2 * t - 1, 0) ∈ frontier (bigon h) :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, htI, Or.inl rfl⟩
    exact ((mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ((2 * t - 1, 0), 0) ∈ tube.chart.source :=
    tube.source_contains ⟨hpoint, Metric.mem_closedBall_self tube.radius_pos.le⟩
  have hkt : (t, (0 : ℝ)) ∈ k.domain :=
    k.contains_strip ⟨htI, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
  have hlt : (t, (0 : ℝ)) ∈ l.domain :=
    l.contains_strip ⟨htI, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
  have hupper : upperStripCoordinates h (2 * t - 1, 0) = (t, 0) := by
    have h := upperStripCoordinates_upper h t
    rwa [hheight] at h
  have hsurj₁ : Surjective (fderiv ℝ (lowerStripCoordinates h) (2 * t - 1, 0)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (injective_fderiv_lowerStripCoordinates tube.height_pos.ne' (2 * t - 1))
  have hsurj₂ : Surjective (fderiv ℝ (upperStripCoordinates h) (2 * t - 1, 0)) := by
    have hi := injective_fderiv_upperStripCoordinates tube.height_pos.ne' (2 * t - 1)
    rw [hheight] at hi
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  have hgerm₂ := tube.upper_germ t htI
  rw [hheight] at hgerm₂
  have hsurj := surjective_corner_normalFrames d e tube.chart hF hG htI htI
    (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt))
    (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section hsource
    (contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
    (contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
    (lowerStripCoordinates_lower h t) hupper hsurj₁ hsurj₂ (tube.lower_germ t htI) hgerm₂
    (hx.trans (k.center t htI).symm) (hy.trans (l.center t htI).symm) htrans
  have hdim' : Module.finrank ℝ (A × C) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using hdim
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mpr hsurj, hsurj⟩

/-- The original two-plus-two normal-frame specialization at a native corner. -/
theorem corner_sheetFrames_bijective
    {F : N → M} {G : P → M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) (range F) (range G) a k₀ k₁}
    {l : CleanStripPatch (E := E) (range G) (range F) b l₀ l₁}
    (tube : TubularBigon (E := E) (range F) (range G) a b k.map l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) (range F) k.map)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) (range G) l.map)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D') 𝓘(ℝ, E) ∞ G)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x : N} {y : P}
    (hx : F x = a t) (hy : G y = b t)
    (htrans : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, D') 𝓘(ℝ, E) G y))) :
    Bijective ((d.normalFrame tube.chart t).coprod (e.normalFrame tube.chart t)) :=
  corner_sheetFrames_bijective_of_finrank tube d e hF hG ht hx hy htrans
    (by simp only [finrank_euclideanSpace_fin])

end Wikipedia.SmoothSixDPoincare.TubularBigon
