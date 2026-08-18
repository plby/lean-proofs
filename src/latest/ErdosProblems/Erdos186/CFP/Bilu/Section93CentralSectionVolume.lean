/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.CoordinateFlag
import ErdosProblems.Erdos186.CFP.Bilu.OrthogonalTransport

/-!
# Central sections of a convex body

This file transports the factorial section estimate from the canonical
coordinate flag to an arbitrary linear subspace of a Euclidean space.
-/

namespace Erdos186.CFP.Bilu.VolumeSections

open MeasureTheory Set Module
open scoped ENNReal

/-- The successor coordinate isometry is inverse to the canonical
orthogonal splitting, after putting the factors in source order. -/
theorem euclideanFinAddEquivProdL2_coordinateSuccessorEmbedding
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanFinAddEquivProdL2 n 1 (coordinateSuccessorEmbedding n x) =
      orthogonalPair x 0 := by
  let e := euclideanFinAddEquivProdL2 n 1
  let g := LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  change e (e.symm (g
    ((LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ
      (EuclideanSpace ℝ (Fin n))) (conePair 0 x)))) = orthogonalPair x 0
  rw [e.apply_symm_apply]
  simp only [LinearIsometryEquiv.withLpProdComm_apply]
  change g (WithLp.toLp 2 (x, 0)) = WithLp.toLp 2 (x, 0)
  dsimp only [g]
  rw [LinearIsometryEquiv.withLpProdCongr_apply]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · rfl
  · exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero

/-- The first component of the canonical orthogonal splitting is the
initial coordinate block. -/
@[simp] theorem euclideanFinAddEquivProdL2_apply_fst
    (d k : ℕ) (y : EuclideanSpace ℝ (Fin (d + k))) (i : Fin d) :
    (euclideanFinAddEquivProdL2 d k y).fst i = y (Fin.castAdd k i) := by
  rfl

/-- The second component of the canonical orthogonal splitting is the
terminal coordinate block. -/
@[simp] theorem euclideanFinAddEquivProdL2_apply_snd
    (d k : ℕ) (y : EuclideanSpace ℝ (Fin (d + k))) (i : Fin k) :
    (euclideanFinAddEquivProdL2 d k y).snd i = y (Fin.natAdd d i) := by
  rfl

/-- Appending one coordinate preserves every old coordinate. -/
@[simp] theorem coordinateSuccessorEmbedding_apply_castAdd
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    coordinateSuccessorEmbedding n x (Fin.castAdd 1 i) = x i := by
  have h := congrArg (fun p : OrthogonalProduct n 1 ↦ p.fst i)
    (euclideanFinAddEquivProdL2_coordinateSuccessorEmbedding n x)
  simpa [orthogonalPair] using h

/-- The coordinate appended by `coordinateSuccessorEmbedding` is zero. -/
@[simp] theorem coordinateSuccessorEmbedding_apply_last
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateSuccessorEmbedding n x (Fin.last n) = 0 := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [hlast]
  have h := congrArg (fun p : OrthogonalProduct n 1 ↦ p.snd (0 : Fin 1))
    (euclideanFinAddEquivProdL2_coordinateSuccessorEmbedding n x)
  simpa [orthogonalPair] using h

/-- The initial member of the canonical flag preserves the first block. -/
theorem canonicalCoordinateFlagF_initial_apply_castAdd
    (d k : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    canonicalCoordinateFlagF d k 0 (Nat.zero_le k) x (Fin.castAdd k i) =
      x i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [canonicalCoordinateFlagF, coordinateFlagEmbedding_succ]
      change coordinateSuccessorEmbedding (d + k)
        (coordinateFlagEmbedding d (Nat.zero_le k) x)
          (Fin.castAdd (k + 1) i) = x i
      rw [show Fin.castAdd (k + 1) i =
          Fin.castAdd 1 (Fin.castAdd k i) by rfl]
      rw [coordinateSuccessorEmbedding_apply_castAdd]
      exact ih

/-- The remaining block of the initial member of the canonical flag is zero. -/
theorem canonicalCoordinateFlagF_initial_apply_natAdd
    (d k : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    canonicalCoordinateFlagF d k 0 (Nat.zero_le k) x (Fin.natAdd d i) = 0 := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [canonicalCoordinateFlagF, coordinateFlagEmbedding_succ]
        change coordinateSuccessorEmbedding (d + k)
          (coordinateFlagEmbedding d (Nat.zero_le k) x) (Fin.last (d + k)) = 0
        exact coordinateSuccessorEmbedding_apply_last _ _
      · rw [canonicalCoordinateFlagF, coordinateFlagEmbedding_succ]
        change coordinateSuccessorEmbedding (d + k)
          (coordinateFlagEmbedding d (Nat.zero_le k) x)
            (Fin.natAdd d (Fin.castSucc j)) = 0
        rw [show Fin.natAdd d (Fin.castSucc j) =
            Fin.castAdd 1 (Fin.natAdd d j) by rfl]
        rw [coordinateSuccessorEmbedding_apply_castAdd]
        exact ih j

/-- Under the canonical splitting `R^(d+k) = R^d ⊕ R^k`, the initial
member of the coordinate flag is the inclusion into the first factor. -/
theorem euclideanFinAddEquivProdL2_coordinateFlagF_initial
    (d k : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    euclideanFinAddEquivProdL2 d k
        (canonicalCoordinateFlagF d k 0 (Nat.zero_le k) x) =
      orthogonalPair x 0 := by
  apply (MeasurableEquiv.toLp 2
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k))).symm.injective
  apply Prod.ext
  · ext i
    simp [euclideanFinAddEquivProdL2, orthogonalPair,
      canonicalCoordinateFlagF_initial_apply_castAdd]
  · ext i
    simp [euclideanFinAddEquivProdL2, orthogonalPair,
      canonicalCoordinateFlagF_initial_apply_natAdd]

/-- Coordinate isometry which identifies the first block with `L` and
the second block with its orthogonal complement. -/
noncomputable def subspaceCoordinateEquiv {d k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] Lᗮ) :
    EuclideanSpace ℝ (Fin (d + k)) ≃ₗᵢ[ℝ] E :=
  (euclideanFinAddEquivProdL2 d k).trans
    (orthogonalCoordinateEquiv L eL eM)

/-- The initial transported coordinate plane is exactly the chosen
coordinate copy of `L`. -/
theorem subspaceCoordinateEquiv_coordinateFlagF_initial
    {d k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] Lᗮ)
    (x : EuclideanSpace ℝ (Fin d)) :
    subspaceCoordinateEquiv L eL eM
        (canonicalCoordinateFlagF d k 0 (Nat.zero_le k) x) =
      (eL x : E) := by
  rw [subspaceCoordinateEquiv, LinearIsometryEquiv.trans_apply,
    euclideanFinAddEquivProdL2_coordinateFlagF_initial,
    orthogonalCoordinateEquiv_apply]
  simp

/-- Solved factorial estimate for the pullback of a central section to
orthonormal coordinates on an arbitrary subspace. -/
theorem intrinsicVolume_subspaceCoordinate_section_le_of_equivs
    {d k : ℕ} {rho : ℝ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E)
    (eL : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] L)
    (eM : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] Lᗮ)
    {B : Set E} (hrho : 0 < rho) (hB : MeasurableSet B)
    (hconv : Convex ℝ B) (hball : Metric.closedBall (0 : E) rho ⊆ B) :
    intrinsicVolume d
        ((fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) ⁻¹' B) ≤
      (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
        ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) B := by
  let u := subspaceCoordinateEquiv L eL eM
  let a : ℝ≥0∞ := (d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    positivity
  have hatop : a ≠ ∞ := by
    dsimp [a]
    finiteness
  have hset :
      ((transportedCoordinateFlagF d k u.toLinearIsometry 0
          (Nat.zero_le k)) ⁻¹' B) =
        ((fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) ⁻¹' B) := by
    ext x
    simp only [mem_preimage]
    change ((subspaceCoordinateEquiv L eL eM)
      (canonicalCoordinateFlagF d k 0 (Nat.zero_le k) x) ∈ B) ↔
        (eL x : E) ∈ B
    rw [subspaceCoordinateEquiv_coordinateFlagF_initial]
  have hcross := origin_centered_equiv_coordinate_section_bound
    u hrho hB hconv hball
  rw [hset] at hcross
  calc
    intrinsicVolume d
        ((fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) ⁻¹' B) =
        a⁻¹ * (a * intrinsicVolume d
          ((fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) ⁻¹' B)) := by
      symm
      exact ENNReal.inv_mul_cancel_left ha0 hatop
    _ ≤ a⁻¹ * (((d + k).factorial : ℝ≥0∞) *
          intrinsicVolume (d + k) B) :=
      mul_le_mul_right hcross a⁻¹
    _ = (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
          ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) B := by
      dsimp [a]
      ac_rfl

/-- Coordinate-free factorial bound for the central section `B ∩ L`. -/
theorem intrinsicVolume_centralSubspace_section_le
    {d k : ℕ} {rho : ℝ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℝ E) (hL : finrank ℝ L = d)
    (hM : finrank ℝ Lᗮ = k)
    {B : Set E} (hrho : 0 < rho) (hB : MeasurableSet B)
    (hconv : Convex ℝ B) (hball : Metric.closedBall (0 : E) rho ⊆ B) :
    intrinsicVolume d (B ∩ (L : Set E)) ≤
      (((d.factorial : ℝ≥0∞) * ENNReal.ofReal (rho ^ k))⁻¹ *
        ((d + k).factorial : ℝ≥0∞)) * intrinsicVolume (d + k) B := by
  let eL := euclideanEquivSubmoduleOfFinrankEq L hL
  let eM := euclideanEquivSubmoduleOfFinrankEq Lᗮ hM
  let S : Set (EuclideanSpace ℝ (Fin d)) :=
    (fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) ⁻¹' B
  have himage :
      (fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) '' S =
        B ∩ (L : Set E) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, (eL x).property⟩
    · rintro ⟨hzB, hzL⟩
      let zL : L := ⟨z, hzL⟩
      refine ⟨eL.symm zL, ?_, ?_⟩
      · change (eL (eL.symm zL) : E) ∈ B
        simpa [zL] using hzB
      · simp [zL]
  have hg : Isometry (fun x : EuclideanSpace ℝ (Fin d) ↦ (eL x : E)) :=
    isometry_subtype_coe.comp eL.isometry
  have hmeasure := hg.euclideanHausdorffMeasure_image (d := d) S
  rw [himage] at hmeasure
  change intrinsicVolume d (B ∩ (L : Set E)) = intrinsicVolume d S at hmeasure
  rw [hmeasure]
  exact intrinsicVolume_subspaceCoordinate_section_le_of_equivs
    L eL eM hrho hB hconv hball

#print axioms intrinsicVolume_centralSubspace_section_le

end Erdos186.CFP.Bilu.VolumeSections
