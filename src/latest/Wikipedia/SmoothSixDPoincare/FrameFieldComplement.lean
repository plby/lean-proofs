import Wikipedia.SmoothSixDPoincare.StarConvexProjectionFrame
import Wikipedia.NoExoticSixSphere.SmoothProjection

/-!
# Complete a smooth partial frame over a star-convex region

The Gram projection and radial range transport construct a complementary
frame without changing the original columns. Their sum is a linear
isomorphism throughout a genuine open neighborhood of the compact region.
No boundary values for the complementary columns are asserted.
-/

noncomputable section

open Set Function Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {E D Z F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A frame and a frame of its actual orthogonal complement give an isomorphism. -/
theorem bijective_coprod_of_orthogonal_range (L : D →L[ℝ] F) (B : Z →L[ℝ] F)
    (hL : Injective L) (hB : Injective B) (hr : B.range = L.rangeᗮ) :
    Bijective (L.coprod B) := by
  have hd : Disjoint L.range B.range := by
    rw [hr]
    exact L.range.orthogonal_disjoint
  constructor
  · change Injective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  · change Surjective (L.toLinearMap.coprod B.toLinearMap)
    rw [← LinearMap.range_eq_top, LinearMap.range_coprod, hr]
    exact L.range.isCompl_orthogonal.sup_eq_top

/-- Complete the original columns smoothly near a compact star-convex region.
The complementary frame is orthogonal on the region, and the combined frame
is invertible throughout an open neighborhood. -/
theorem exists_smooth_complement_near_starConvex_on
    {L : E → (D →L[ℝ] F)} {O : Set E} (hO : IsOpen O) (hL : ContDiffOn ℝ ∞ L O)
    {K : Set E} (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K)
    (h0 : (0 : E) ∈ K) (hKO : K ⊆ O) (hi : ∀ x ∈ K, Injective (L x))
    (n : ℕ) (hdim : finrank ℝ D + n = finrank ℝ F) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
        ContDiffOn ℝ ∞ B V ∧
        (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
        ∀ x ∈ V, Bijective ((L x).coprod (B x)) := by
  let φ : EuclideanSpace ℝ (Fin (finrank ℝ D)) ≃L[ℝ] D :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin
  let A (x : E) := (L x).comp φ.toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A O := hL.clm_comp contDiffOn_const
  have hAr (x : E) : (A x).range = (L x).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
  let U : Set E := O ∩ {x | Injective (L x)}
  have hU : IsOpen U :=
    hL.continuousOn.isOpen_inter_preimage hO ContinuousLinearMap.isOpen_injective
  have hKU : K ⊆ U := fun x hx => ⟨hKO hx, hi x hx⟩
  let P (x : E) : F →L[ℝ] F := 1 - NoExoticSixSphere.gramProjection (A x)
  have hP (x : E) (hx : x ∈ U) : P x = ((L x).rangeᗮ).starProjection := by
    dsimp only [P]
    rw [NoExoticSixSphere.gramProjection_eq_starProjection _ (hx.2.comp φ.injective)]
    simp only [hAr]
    exact (Submodule.starProjection_orthogonal' (L x).range).symm
  have hsP : ContDiffOn ℝ ∞ P U := by
    intro x hx
    have hg : ContDiffAt ℝ ∞ (fun y => NoExoticSixSphere.gramProjection (A y)) x :=
      (NoExoticSixSphere.contMDiffAt_gramProjection
        (hA.contDiffAt (hO.mem_nhds hx.1)).contMDiffAt
        (hx.2.comp φ.injective)).contDiffAt
    exact (contDiffAt_const.sub hg).contDiffWithinAt
  have hidem : ∀ x ∈ K, IsIdempotentElem (P x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact ((L x).rangeᗮ).isIdempotentElem_starProjection
  obtain ⟨W, hW, hKW, B₀, hB₀, hB₀i⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU P hidem hsP
  have hr (x : E) (hx : x ∈ K) : (P x).range = (L x).rangeᗮ := by
    rw [hP x (hKU hx), Submodule.range_starProjection]
  have hcenter : finrank ℝ (P 0).range = n := by
    have hrank : finrank ℝ (L 0).range = finrank ℝ D :=
      LinearMap.finrank_range_of_inj (hi 0 h0)
    have hs := (L 0).range.finrank_add_finrank_orthogonal
    rw [hrank] at hs
    rw [hr 0 h0]
    omega
  let ψ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (P 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  let B (x : E) := (B₀ x).comp ψ.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ B (W ∩ O) :=
    (hB₀.clm_comp contDiffOn_const).mono inter_subset_left
  have hBr : ∀ x ∈ K, (B x).range = (L x).rangeᗮ := by
    intro x hx
    calc
      (B x).range = (B₀ x).range :=
        LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ψ.surjective)
      _ = (P x).range := (hB₀i x hx).2
      _ = (L x).rangeᗮ := hr x hx
  have hBi : ∀ x ∈ K, Injective (B x) :=
    fun x hx => (hB₀i x hx).1.comp ψ.injective
  let T (x : E) := (L x).coprod (B x)
  have hT : ContDiffOn ℝ ∞ T (W ∩ O) := by
    have hs := ((hL.mono inter_subset_right).clm_comp
      (contDiffOn_const (c := ContinuousLinearMap.fst ℝ D (EuclideanSpace ℝ (Fin n))))).add
        (hB.clm_comp
          (contDiffOn_const (c := ContinuousLinearMap.snd ℝ D (EuclideanSpace ℝ (Fin n)))))
    exact hs
  have hTi : ∀ x ∈ K, Bijective (T x) :=
    fun x hx => bijective_coprod_of_orthogonal_range (L x) (B x)
      (hi x hx) (hBi x hx) (hBr x hx)
  let V : Set E := (W ∩ O) ∩ {x | Injective (T x)}
  have hV : IsOpen V :=
    hT.continuousOn.isOpen_inter_preimage (hW.inter hO) ContinuousLinearMap.isOpen_injective
  refine ⟨V, hV, fun x hx => ⟨⟨hKW hx, hKO hx⟩, (hTi x hx).1⟩, B,
    hB.mono inter_subset_left, hBr, ?_⟩
  intro x hx
  have hdim' : finrank ℝ (D × EuclideanSpace ℝ (Fin n)) = finrank ℝ F := by
    rw [finrank_prod, finrank_euclideanSpace_fin]
    exact hdim
  exact ⟨hx.2, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hx.2⟩

/-- The global-field specialization of smooth complementary-frame construction. -/
theorem exists_smooth_complement_near_starConvex
    {L : E → (D →L[ℝ] F)} (hL : ContDiff ℝ ∞ L)
    {K : Set E} (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K)
    (h0 : (0 : E) ∈ K) (hi : ∀ x ∈ K, Injective (L x))
    (n : ℕ) (hdim : finrank ℝ D + n = finrank ℝ F) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧
      ∃ B : E → (EuclideanSpace ℝ (Fin n) →L[ℝ] F),
        ContDiffOn ℝ ∞ B V ∧
        (∀ x ∈ K, (B x).range = (L x).rangeᗮ) ∧
        ∀ x ∈ V, Bijective ((L x).coprod (B x)) :=
  exists_smooth_complement_near_starConvex_on isOpen_univ hL.contDiffOn hK hstar h0
    (subset_univ K) hi n hdim

end Wikipedia.SmoothSixDPoincare.FrameField
