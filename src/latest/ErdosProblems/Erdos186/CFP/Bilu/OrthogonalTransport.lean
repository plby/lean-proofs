/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.VolumeSections
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Transport of Bilu's coordinate section inequality

This file identifies an arbitrary orthogonal decomposition `L ⊕ Lᗮ` with
the coordinate Hilbert product used in `VolumeSections`.
-/

namespace Erdos186.CFP.Bilu.VolumeSections

open Filter MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal MeasureTheory Pointwise Topology

/-- Coordinate realization of the orthogonal decomposition `L ⊕ Lᗮ`. -/
noncomputable def orthogonalCoordinateEquiv {l m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ) :
    OrthogonalProduct l m ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2 eL eM).trans
    L.orthogonalDecomposition.symm

@[simp]
theorem orthogonalCoordinateEquiv_apply {l m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m)) :
    orthogonalCoordinateEquiv L eL eM (orthogonalPair x y) =
      (eL x : E) + (eM y : E) := by
  simp [orthogonalCoordinateEquiv, orthogonalPair]

@[simp]
theorem orthogonalProjection_orthogonalCoordinateEquiv {l m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (x : EuclideanSpace ℝ (Fin l)) (y : EuclideanSpace ℝ (Fin m)) :
    (Lᗮ).orthogonalProjectionOnto
      (orthogonalCoordinateEquiv L eL eM (orthogonalPair x y)) = eM y := by
  simp

/-- The coordinate second projection is exactly the orthogonal projection,
after embedding the coordinate copy of `Lᗮ` into the ambient space. -/
theorem image_secondProjection_preimage_orthogonalCoordinateEquiv
    {l m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (B : Set E) :
    eM '' secondProjection ((orthogonalCoordinateEquiv L eL eM) ⁻¹' B) =
      (Lᗮ).orthogonalProjectionOnto '' B := by
  let e := orthogonalCoordinateEquiv L eL eM
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx⟩, rfl⟩
    refine ⟨e (orthogonalPair x y), hx, ?_⟩
    exact orthogonalProjection_orthogonalCoordinateEquiv L eL eM x y
  · rintro ⟨b, hb, rfl⟩
    let p : OrthogonalProduct l m := e.symm b
    have hp_pair : orthogonalPair p.fst p.snd = p := by
      apply (MeasurableEquiv.toLp 2
        (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m))).symm.injective
      rfl
    refine ⟨p.snd, ⟨p.fst, ?_⟩, ?_⟩
    · change e (orthogonalPair p.fst p.snd) ∈ B
      rw [hp_pair]
      simpa [p] using hb
    · have hp : e p = b := by simp [p]
      rw [← hp]
      rw [← hp_pair]
      exact (orthogonalProjection_orthogonalCoordinateEquiv
        L eL eM p.fst p.snd).symm

/-- The coordinate central fibre is exactly the section by `L`, after
embedding the coordinate copy of `L` into the ambient space. -/
theorem image_centralFiber_preimage_orthogonalCoordinateEquiv
    {l m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (B : Set E) :
    (fun x : EuclideanSpace ℝ (Fin l) ↦ (eL x : E)) ''
        centralFiber ((orthogonalCoordinateEquiv L eL eM) ⁻¹' B) =
      B ∩ (L : Set E) := by
  let e := orthogonalCoordinateEquiv L eL eM
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change e (orthogonalPair x 0) ∈ B at hx
      simpa [e] using hx
    · exact (eL x).property
  · rintro ⟨hzB, hzL⟩
    let zL : L := ⟨z, hzL⟩
    refine ⟨eL.symm zL, ?_, ?_⟩
    · change e (orthogonalPair (eL.symm zL) 0) ∈ B
      simpa [e, zL] using hzB
    · simp [zL]

/-- Isometric transport of the sharp coordinate inequality (6.7) to an
arbitrary orthogonal decomposition.  The regularity hypotheses are stated
on the coordinate projection here; the compact-body wrapper below derives
them from geometric hypotheses on `B`. -/
theorem orthogonal_projection_central_section_bound_of_equivs
    {l m : ℕ} (hl : 0 < l) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (B : Set E) (hconv : Convex ℝ B) (hB : MeasurableSet B)
    (hPnhds : secondProjection
        ((orthogonalCoordinateEquiv L eL eM) ⁻¹' B) ∈ 𝓝 0)
    (hPclosed : IsClosed (secondProjection
        ((orthogonalCoordinateEquiv L eL eM) ⁻¹' B)))
    (hPbounded : Bornology.IsVonNBounded ℝ (secondProjection
        ((orthogonalCoordinateEquiv L eL eM) ⁻¹' B))) :
    intrinsicVolume m ((Lᗮ).orthogonalProjectionOnto '' B) *
        intrinsicVolume l (B ∩ (L : Set E)) ≤
      ((m + l).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B := by
  let e := orthogonalCoordinateEquiv L eL eM
  let Bc : Set (OrthogonalProduct l m) := e ⁻¹' B
  have hconv_c : Convex ℝ Bc := hconv.linear_preimage e.toLinearMap
  have hB_c : MeasurableSet Bc := hB.preimage e.continuous.measurable
  have hb := coordinate_projection_central_section_bound hl hconv_c hB_c
    hPnhds hPclosed hPbounded
  have hproj :
      intrinsicVolume m (secondProjection Bc) =
        intrinsicVolume m ((Lᗮ).orthogonalProjectionOnto '' B) := by
    have hmeasure := eM.isometry.euclideanHausdorffMeasure_image
      (d := m) (secondProjection Bc)
    rw [image_secondProjection_preimage_orthogonalCoordinateEquiv
      L eL eM B] at hmeasure
    exact hmeasure.symm
  have hsection :
      intrinsicVolume l (centralFiber Bc) =
        intrinsicVolume l (B ∩ (L : Set E)) := by
    have hg : Isometry (fun x : EuclideanSpace ℝ (Fin l) ↦ (eL x : E)) :=
      isometry_subtype_coe.comp eL.isometry
    have hmeasure := hg.euclideanHausdorffMeasure_image
      (d := l) (centralFiber Bc)
    rw [image_centralFiber_preimage_orthogonalCoordinateEquiv
      L eL eM B] at hmeasure
    exact hmeasure.symm
  have hfull : intrinsicVolume (l + m) Bc = intrinsicVolume (l + m) B := by
    have hmeasure := e.isometry.euclideanHausdorffMeasure_preimage
      (d := l + m) B
    rw [e.surjective.range_eq, inter_univ] at hmeasure
    exact hmeasure
  rw [hproj, hsection, hfull] at hb
  exact hb

/-- Source-facing compact-body form of (6.7), still parameterized by
orthonormal coordinate equivalences for `L` and `Lᗮ`.  Compactness gives
closedness and boundedness of the projection, while the centered inball
gives the gauge neighbourhood hypothesis. -/
theorem orthogonal_projection_central_section_bound_compact_of_equivs
    {l m : ℕ} (hl : 0 < l) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin l) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] Lᗮ)
    (B : Set E) (hconv : Convex ℝ B) (hcompact : IsCompact B)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall (0 : E) ρ ⊆ B) :
    intrinsicVolume m ((Lᗮ).orthogonalProjectionOnto '' B) *
        intrinsicVolume l (B ∩ (L : Set E)) ≤
      ((m + l).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B := by
  let e := orthogonalCoordinateEquiv L eL eM
  let Bc : Set (OrthogonalProduct l m) := e ⁻¹' B
  let D : Set (EuclideanSpace ℝ (Fin m)) := secondProjection Bc
  have hBccompact : IsCompact Bc := e.toHomeomorph.isCompact_preimage.mpr hcompact
  have hDeq : D = (fun p : OrthogonalProduct l m ↦ p.snd) '' Bc := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨orthogonalPair x y, hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.fst, ?_⟩
      have hp_pair : orthogonalPair p.fst p.snd = p := by
        apply (MeasurableEquiv.toLp 2
          (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m))).symm.injective
        rfl
      rwa [hp_pair]
  have hDcompact : IsCompact D := by
    rw [hDeq]
    exact hBccompact.image (by fun_prop)
  have hball_c : Metric.closedBall (0 : OrthogonalProduct l m) ρ ⊆ Bc := by
    intro p hp
    apply hball
    simpa [Metric.mem_closedBall, e.norm_map] using hp
  have hball_D : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ρ ⊆ D := by
    intro y hy
    refine ⟨0, hball_c ?_⟩
    simpa [Metric.mem_closedBall, orthogonalPair] using hy
  have hDnhds : D ∈ 𝓝 0 :=
    mem_of_superset (Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin m)) hρ) hball_D
  exact orthogonal_projection_central_section_bound_of_equivs hl L eL eM B hconv
    hcompact.isClosed.measurableSet hDnhds hDcompact.isClosed
      (hDcompact.isVonNBounded ℝ)

/-- An arbitrary finite-dimensional subspace of the stated finrank is
isometric to the corresponding coordinate Euclidean space. -/
noncomputable def euclideanEquivSubmoduleOfFinrankEq
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℝ E) (hL : finrank ℝ L = d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L :=
  ((stdOrthonormalBasis ℝ L).reindex (finCongr hL)).repr.symm

/-- Fully coordinate-free sharp section/projection inequality for a compact
convex body containing a centered positive-radius ball.  This is Bilu's
Lemma 6.7, under the nondegenerate `l > 0` hypothesis used in Lemma 6.6. -/
theorem orthogonal_projection_central_section_bound_compact
    {l m : ℕ} (hl : 0 < l) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E) (hL : finrank ℝ L = l) (hM : finrank ℝ Lᗮ = m)
    (B : Set E) (hconv : Convex ℝ B) (hcompact : IsCompact B)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall (0 : E) ρ ⊆ B) :
    intrinsicVolume m ((Lᗮ).orthogonalProjectionOnto '' B) *
        intrinsicVolume l (B ∩ (L : Set E)) ≤
      ((l + m).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B := by
  simpa [Nat.add_comm] using
    (orthogonal_projection_central_section_bound_compact_of_equivs hl L
      (euclideanEquivSubmoduleOfFinrankEq L hL)
      (euclideanEquivSubmoduleOfFinrankEq Lᗮ hM)
      B hconv hcompact hρ hball)

/-- The central section of a seminorm unit ball by a nonzero line has at
least the expected length `2 ‖w‖ / p(w)`, written without division. -/
theorem central_line_section_bound_of_unitBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : Set E) (p : Seminorm ℝ E) (w : E) (hw : w ≠ 0)
    (hpw : 0 < p w) (hunit : B = {x | p x ≤ 1}) :
    (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ ≤
      ENNReal.ofReal (p w) * intrinsicVolume 1
        (B ∩ ((ℝ ∙ w) : Set E)) := by
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : E := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hwnorm.ne']
  let f : ℝ →ₗᵢ[ℝ] E := LinearIsometry.toSpanSingleton ℝ E hu
  let r : ℝ := ‖w‖ / p w
  have hr : 0 < r := div_pos hwnorm hpw
  have himage : f '' Icc (-r) r ⊆ B ∩ ((ℝ ∙ w) : Set E) := by
    rintro _ ⟨t, ht, rfl⟩
    have habs : |t| ≤ r := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    constructor
    · rw [hunit]
      change p (f t) ≤ 1
      rw [LinearIsometry.toSpanSingleton_apply]
      change p (t • u) ≤ 1
      rw [map_smul_eq_mul]
      change ‖t‖ * p (‖w‖⁻¹ • w) ≤ 1
      rw [map_smul_eq_mul]
      have hfactor : 0 ≤ ‖‖w‖⁻¹‖ * p w :=
        mul_nonneg (norm_nonneg _) (apply_nonneg p _)
      calc
        ‖t‖ * (‖‖w‖⁻¹‖ * p w) ≤
            r * (‖‖w‖⁻¹‖ * p w) := by
          apply mul_le_mul_of_nonneg_right _ hfactor
          simpa [Real.norm_eq_abs] using habs
        _ = 1 := by
          simp only [r, Real.norm_of_nonneg (inv_nonneg.mpr hwnorm.le)]
          field_simp [hpw.ne', hwnorm.ne']
    · rw [LinearIsometry.toSpanSingleton_apply]
      change t • u ∈ ℝ ∙ w
      exact Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w))
  have hinterval :
      intrinsicVolume 1 (f '' Icc (-r) r) = ENNReal.ofReal (2 * r) := by
    calc
      intrinsicVolume 1 (f '' Icc (-r) r) =
          intrinsicVolume 1 (Icc (-r) r) :=
        f.isometry.euclideanHausdorffMeasure_image _
      _ = volume (Icc (-r) r) := by
        unfold intrinsicVolume
        have hm : (μHE[1] : Measure ℝ) = volume := by
          simpa using
            (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
        rw [hm]
      _ = ENNReal.ofReal (2 * r) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  have hlength : ENNReal.ofReal (2 * r) ≤
      intrinsicVolume 1 (B ∩ ((ℝ ∙ w) : Set E)) := by
    rw [← hinterval]
    exact measure_mono himage
  calc
    (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ =
        ENNReal.ofReal (p w) * ENNReal.ofReal (2 * r) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hpw.le]
      congr 1
      dsimp only [r]
      field_simp
    _ ≤ ENNReal.ofReal (p w) *
        intrinsicVolume 1 (B ∩ ((ℝ ∙ w) : Set E)) :=
      mul_le_mul_right hlength _

/-- A seminorm whose unit ball is compact is positive on every nonzero
vector.  Thus the Minkowski functional of a convex body is a norm. -/
theorem seminorm_pos_of_isCompact_unitBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set E) (p : Seminorm ℝ E) (hcompact : IsCompact B)
    (hunit : B = {x | p x ≤ 1}) {w : E} (hw : w ≠ 0) :
    0 < p w := by
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hpw_ne : p w ≠ 0 := by
    intro hpw
    obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
    have h0B : (0 : E) ∈ B := by
      rw [hunit]
      simp
    have hR0 : 0 ≤ R := by
      simpa using hR 0 h0B
    let t : ℝ := (R + 1) / ‖w‖
    have ht : 0 < t := div_pos (by linarith) hwnorm
    have htwB : t • w ∈ B := by
      rw [hunit]
      change p (t • w) ≤ 1
      rw [map_smul_eq_mul, hpw, mul_zero]
      norm_num
    have hnorm : ‖t • w‖ = R + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      dsimp only [t]
      field_simp [hwnorm.ne']
    linarith [hR (t • w) htwB]
  exact (apply_nonneg p w).lt_of_ne hpw_ne.symm

/-- Exact l=1 specialization: Bilu's Lemma 6.6 for a compact convex
seminorm unit ball.  All geometric and one-dimensional section estimates
are discharged internally. -/
theorem lemma66_compact_seminorm_unitBall {n : ℕ} (hn : 0 < n)
    (B : Set (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0)
    (hconv : Convex ℝ B) (hcompact : IsCompact B)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ B)
    (hunit : B = {x | p x ≤ 1}) :
    Lemma66Conclusion B p w := by
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := ℝ ∙ w
  have hpw : 0 < p w := seminorm_pos_of_isCompact_unitBall B p hcompact hunit hw
  have hL : finrank ℝ L = 1 := by
    simpa [L] using finrank_span_singleton hw
  have hM : finrank ℝ Lᗮ = n - 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal L
    simp only [hL, finrank_euclideanSpace_fin] at hsum
    omega
  have hprojection :=
    orthogonal_projection_central_section_bound_compact
      (l := 1) (m := n - 1) (by omega) L hL hM B hconv hcompact hρ hball
  have hnadd : 1 + (n - 1) = n := by omega
  have hprojection' :
      intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B) *
          intrinsicVolume 1 (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n)))) ≤
        (n : ℝ≥0∞) * intrinsicVolume n B := by
    simpa only [L, hnadd, Nat.choose_one_right] using hprojection
  exact lemma66_of_central_section_bound B p w
    (central_line_section_bound_of_unitBall B p w hw hpw hunit) hprojection'

#print axioms orthogonal_projection_central_section_bound_compact
#print axioms central_line_section_bound_of_unitBall
#print axioms lemma66_compact_seminorm_unitBall

end Erdos186.CFP.Bilu.VolumeSections
