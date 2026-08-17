/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions
import ErdosProblems.Erdos651.FiniteRamsey
import ErdosProblems.Erdos651.Kirchberger

/-!
# The above--below relation

This file isolates the geometric Ramsey step in the Pohoata--Zakharov proof.
The vertical projection forgets the last coordinate. When the projections of
two segments cross in their relative interiors, their lifts are strictly
ordered by height as soon as the four endpoints are affinely independent.
-/

namespace Erdos651

open AffineMap Set

noncomputable section

/-- Projection of `R^3` to the first two coordinates. -/
def verticalProjection (p : Point 3) : Point 2 :=
  WithLp.toLp 2 fun i : Fin 2 => p i.castSucc

/-- The last coordinate of a point of `R^3`. -/
def verticalHeight (p : Point 3) : ℝ := p 2

/-- A parametrized point of the segment from `p` to `q`. -/
def segmentPoint (p q : Point 3) (t : ℝ) : Point 3 :=
  lineMap p q t

/-- Signed area of the projected ordered triangle. -/
def projectedOrientation (a b c : Point 3) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- The projections of `ac` and `bd` cross at the displayed interior parameters. -/
def ProjectedSegmentsCrossAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  t ∈ Ioo (0 : ℝ) 1 ∧ u ∈ Ioo (0 : ℝ) 1 ∧
    verticalProjection (segmentPoint a c t) =
      verticalProjection (segmentPoint b d u)

/-- At a projected crossing, the segment `ac` is strictly above `bd`. -/
def SegmentAboveAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  ProjectedSegmentsCrossAt a c b d t u ∧
    verticalHeight (segmentPoint b d u) < verticalHeight (segmentPoint a c t)

/-- At a projected crossing, the segment `ac` is strictly below `bd`. -/
def SegmentBelowAt (a c b d : Point 3) (t u : ℝ) : Prop :=
  ProjectedSegmentsCrossAt a c b d t u ∧
    verticalHeight (segmentPoint a c t) < verticalHeight (segmentPoint b d u)

/-- The two projected open segments cross and `ac` is above `bd`. -/
def SegmentAbove (a c b d : Point 3) : Prop :=
  ∃ t u : ℝ, SegmentAboveAt a c b d t u

/-- The two projected open segments cross and `ac` is below `bd`. -/
def SegmentBelow (a c b d : Point 3) : Prop :=
  ∃ t u : ℝ, SegmentBelowAt a c b d t u

private lemma projectedOrientation_identities_of_crossing
    {a b c d : Point 3} {t u : ℝ}
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    u * projectedOrientation a b d = t * projectedOrientation a b c ∧
      u * projectedOrientation a c d = (1 - u) * projectedOrientation a b c ∧
      u * projectedOrientation b c d = (1 - t) * projectedOrientation a b c := by
  have h₀ := congrArg (fun p : Point 2 => p 0) hcross.2.2
  have h₁ := congrArg (fun p : Point 2 => p 1) hcross.2.2
  simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub] at h₀ h₁
  have r₀ : u * (d 0 - a 0) - t * (c 0 - a 0) +
      (1 - u) * (b 0 - a 0) = 0 := by linarith [h₀]
  have r₁ : u * (d 1 - a 1) - t * (c 1 - a 1) +
      (1 - u) * (b 1 - a 1) = 0 := by linarith [h₁]
  constructor
  · simp only [projectedOrientation]
    linear_combination (b 0 - a 0) * r₁ - (b 1 - a 1) * r₀
  constructor
  · simp only [projectedOrientation]
    linear_combination (c 0 - a 0) * r₁ - (c 1 - a 1) * r₀
  · simp only [projectedOrientation]
    linear_combination (c 0 - b 0) * r₁ - (c 1 - b 1) * r₀

lemma point3_eq_of_projection_eq_of_height_eq {p q : Point 3}
    (hproj : verticalProjection p = verticalProjection q)
    (hheight : verticalHeight p = verticalHeight q) : p = q := by
  ext i
  fin_cases i
  · simpa [verticalProjection] using congrArg (fun r : Point 2 => r 0) hproj
  · simpa [verticalProjection] using congrArg (fun r : Point 2 => r 1) hproj
  · simpa [verticalHeight] using hheight

lemma crossing_height_ne_of_affineIndependent
    {a c b d : Point 3} {t u : ℝ}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    verticalHeight (segmentPoint a c t) ≠
      verticalHeight (segmentPoint b d u) := by
  intro hheight
  have heq : segmentPoint a c t = segmentPoint b d u :=
    point3_eq_of_projection_eq_of_height_eq hcross.2.2 hheight
  let w₁ : Fin 4 → ℝ := Finset.affineCombinationLineMapWeights 0 2 t
  let w₂ : Fin 4 → ℝ := Finset.affineCombinationLineMapWeights 1 3 u
  have hw₁ : ∑ i, w₁ i = 1 := by
    simpa [w₁] using
      (Finset.sum_affineCombinationLineMapWeights (s := (Finset.univ : Finset (Fin 4)))
        (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by simp) (by simp) t)
  have hw₂ : ∑ i, w₂ i = 1 := by
    simpa [w₂] using
      (Finset.sum_affineCombinationLineMapWeights (s := (Finset.univ : Finset (Fin 4)))
        (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by simp) (by simp) u)
  have hac : (Finset.univ : Finset (Fin 4)).affineCombination ℝ ![a, b, c, d] w₁ =
      segmentPoint a c t := by
    simpa [w₁, segmentPoint] using
      (Finset.affineCombination_affineCombinationLineMapWeights
        (s := (Finset.univ : Finset (Fin 4))) ![a, b, c, d]
        (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by simp) (by simp) t)
  have hbd : (Finset.univ : Finset (Fin 4)).affineCombination ℝ ![a, b, c, d] w₂ =
      segmentPoint b d u := by
    simpa [w₂, segmentPoint] using
      (Finset.affineCombination_affineCombinationLineMapWeights
        (s := (Finset.univ : Finset (Fin 4))) ![a, b, c, d]
        (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by simp) (by simp) u)
  have hweights : ∀ i ∈ (Finset.univ : Finset (Fin 4)), w₁ i = w₂ i :=
    (hind.affineCombination_eq_iff_eq hw₁ hw₂).mp (hac.trans (heq.trans hbd.symm))
  have hzero : 1 - t = 0 := by
    simpa [w₁, w₂] using hweights 0 (by simp)
  linarith [hcross.1.2]

theorem segmentAboveAt_or_segmentBelowAt
    {a c b d : Point 3} {t u : ℝ}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    SegmentAboveAt a c b d t u ∨ SegmentBelowAt a c b d t u := by
  rcases lt_or_gt_of_ne (crossing_height_ne_of_affineIndependent hind hcross) with h | h
  · exact Or.inr ⟨hcross, h⟩
  · exact Or.inl ⟨hcross, h⟩

theorem segmentAbove_or_segmentBelow
    {a c b d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (hcross : ∃ t u : ℝ, ProjectedSegmentsCrossAt a c b d t u) :
    SegmentAbove a c b d ∨ SegmentBelow a c b d := by
  obtain ⟨t, u, htu⟩ := hcross
  rcases segmentAboveAt_or_segmentBelowAt hind htu with h | h
  · exact Or.inl ⟨t, u, h⟩
  · exact Or.inr ⟨t, u, h⟩

lemma segmentAbove_swap_left {a c b d : Point 3}
    (h : SegmentAbove a c b d) : SegmentAbove c a b d := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have ht0 : 0 < t := hcross.1.1
  have ht1 : t < 1 := hcross.1.2
  refine ⟨1 - t, u, ⟨⟨by linarith, by linarith⟩,
    hcross.2.1, ?_⟩, ?_⟩
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hcross.2.2
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hheight

lemma segmentAbove_swap_right {a c b d : Point 3}
    (h : SegmentAbove a c b d) : SegmentAbove a c d b := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hu0 : 0 < u := hcross.2.1.1
  have hu1 : u < 1 := hcross.2.1.2
  refine ⟨t, 1 - u, ⟨hcross.1,
    ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hcross.2.2
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hheight

lemma segmentBelow_swap_right {a c b d : Point 3}
    (h : SegmentBelow a c b d) : SegmentBelow a c d b := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hu0 : 0 < u := hcross.2.1.1
  have hu1 : u < 1 := hcross.2.1.2
  refine ⟨t, 1 - u, ⟨hcross.1, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hcross.2.2
  · simpa [segmentPoint, AffineMap.lineMap_apply_one_sub] using hheight

lemma segmentAbove_iff_reverse {a c b d : Point 3} :
    SegmentAbove a c b d ↔ SegmentBelow b d a c := by
  constructor
  · rintro ⟨t, u, hcross, hheight⟩
    exact ⟨u, t, ⟨⟨hcross.2.1, hcross.1, hcross.2.2.symm⟩, hheight⟩⟩
  · rintro ⟨u, t, hcross, hheight⟩
    exact ⟨t, u, ⟨⟨hcross.2.1, hcross.1, hcross.2.2.symm⟩, hheight⟩⟩

/-! ## The oriented-volume form of above/below -/

/-- Matrix of the three displacement vectors from `a`. -/
def vsubMatrix (a b c d : Point 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![b - a, c - a, d - a] j i

/-- Signed volume of the ordered tetrahedron `(a,b,c,d)`. -/
def orientedVolume (a b c d : Point 3) : ℝ :=
  (vsubMatrix a b c d).det

private lemma orientedVolume_eq (a b c d : Point 3) :
    orientedVolume a b c d =
      (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
      (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
      (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0)) := by
  simp [orientedVolume, vsubMatrix, Matrix.det_fin_three]
  ring

/-- The signed volume is an affine functional of its fourth vertex. -/
def orientedVolumeLinear (a b c : Point 3) : Point 3 →ₗ[ℝ] ℝ where
  toFun p := orientedVolume a b c p - orientedVolume a b c 0
  map_add' p q := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hadd (i : Fin 3) : (p + q) i = p i + q i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hadd, hzero]
    ring
  map_smul' r p := by
    rw [orientedVolume_eq, orientedVolume_eq, orientedVolume_eq]
    change _ = _
    have hsmul (i : Fin 3) : (r • p) i = r * p i := rfl
    have hzero (i : Fin 3) : (0 : Point 3) i = 0 := rfl
    simp only [hsmul, hzero, RingHom.id_apply]
    ring

def orientedVolumeAffine (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (orientedVolumeLinear a b c).toAffineMap +
    AffineMap.const ℝ (Point 3) (orientedVolume a b c 0)

@[simp] lemma orientedVolumeAffine_apply (a b c p : Point 3) :
    orientedVolumeAffine a b c p = orientedVolume a b c p := by
  simp [orientedVolumeAffine, orientedVolumeLinear]

private lemma mem_convexHull_zero_face
    (T : Finset (Point 3)) (φ : Point 3 →ᵃ[ℝ] ℝ) {z : Point 3}
    (hφ : ∀ p ∈ T, 0 ≤ φ p) (hz : z ∈ convexHull ℝ (T : Set (Point 3)))
    (hz0 : φ z = 0) :
    z ∈ convexHull ℝ ((T.filter fun p => φ p = 0 : Finset (Point 3)) : Set (Point 3)) := by
  obtain ⟨w, hw, hwsum, hwz⟩ := Finset.mem_convexHull'.mp hz
  let U := T.filter fun p => φ p = 0
  have hzcomb : T.affineCombination ℝ id w = z := by
    rw [T.affineCombination_eq_linear_combination _ _ hwsum]
    simpa using hwz
  have hsumprod : ∑ p ∈ T, w p * φ p = φ z := by
    calc
      ∑ p ∈ T, w p * φ p = T.affineCombination ℝ (φ ∘ id) w := by
        rw [T.affineCombination_eq_linear_combination _ _ hwsum]
        simp only [Function.comp_apply, id_eq, smul_eq_mul]
      _ = φ (T.affineCombination ℝ id w) :=
        (T.map_affineCombination id w hwsum φ).symm
      _ = φ z := by rw [hzcomb]
  have hsumzero : ∑ p ∈ T, w p * φ p = 0 := hsumprod.trans hz0
  have hterm : ∀ p ∈ T, w p * φ p = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hsumzero
    · exact hsumzero
    · intro p hp
      exact mul_nonneg (hw p hp) (hφ p hp)
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hwzero : ∀ p ∈ T, p ∉ U → w p = 0 := by
    intro p hpT hpU
    have hφne : φ p ≠ 0 := by
      intro hφ
      exact hpU (Finset.mem_filter.2 ⟨hpT, hφ⟩)
    exact (mul_eq_zero.mp (hterm p hpT)).resolve_right hφne
  have hsumU : ∑ p ∈ U, w p = 1 := by
    rw [Finset.sum_subset hUT hwzero]
    exact hwsum
  have hpointU : ∑ p ∈ U, w p • p = z := by
    rw [Finset.sum_subset hUT]
    · exact hwz
    · intro p hpT hpU
      simp [hwzero p hpT hpU]
  apply Finset.mem_convexHull'.2
  exact ⟨w, (fun p hp => hw p (hUT hp)), hsumU, hpointU⟩

lemma orientedVolume_ne_zero_of_affineIndependent {a b c d : Point 3}
    (h : AffineIndependent ℝ ![a, b, c, d]) : orientedVolume a b c d ≠ 0 := by
  have hv : LinearIndependent ℝ ![b - a, c - a, d - a] := by
    apply (linearIndependent_equiv' (finSuccAboveEquiv (0 : Fin 4)) ?_).mpr
      ((affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c, d] 0).mp h)
    funext i
    fin_cases i <;> rfl
  have hcols : LinearIndependent ℝ (vsubMatrix a b c d).col := by
    have hmapped := hv.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun :
        (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) =
          (vsubMatrix a b c d).col := by
      funext j i
      rfl
    change LinearIndependent ℝ
      (fun j => (EuclideanSpace.equiv (Fin 3) ℝ) (![b - a, c - a, d - a] j)) at hmapped
    rw [hfun] at hmapped
    exact hmapped
  exact ((Matrix.isUnit_iff_isUnit_det (vsubMatrix a b c d)).mp
    ((Matrix.linearIndependent_cols_iff_isUnit).mp hcols)).ne_zero

private lemma crossing_orientedVolume_identity
    {a b c d : Point 3} {t u : ℝ}
    (hcross : ProjectedSegmentsCrossAt a c b d t u) :
    u * orientedVolume a b c d =
      -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
        ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) := by
  have h₀ := congrArg (fun p : Point 2 => p 0) hcross.2.2
  have h₁ := congrArg (fun p : Point 2 => p 1) hcross.2.2
  simp [verticalProjection, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h₀ h₁
  have r₀ : u * (d 0 - a 0) - t * (c 0 - a 0) + (1 - u) * (b 0 - a 0) = 0 := by
    linarith [h₀]
  have r₁ : u * (d 1 - a 1) - t * (c 1 - a 1) + (1 - u) * (b 1 - a 1) = 0 := by
    linarith [h₁]
  rw [orientedVolume_eq]
  simp [verticalHeight, segmentPoint, AffineMap.lineMap_apply, vsub_eq_sub,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  linear_combination
    ((b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1)) * r₀ +
    ((b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2)) * r₁

private lemma orientedVolume_rotate (a b c d : Point 3) :
    orientedVolume a b c d = -orientedVolume d a b c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

private lemma orientedVolume_middle_rotate (a b c d : Point 3) :
    orientedVolume a b c d = orientedVolume a d b c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

private lemma orientedVolume_swap_last (a b c d : Point 3) :
    orientedVolume a b c d = -orientedVolume a b d c := by
  rw [orientedVolume_eq, orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_first (a b c : Point 3) :
    orientedVolume a b c a = 0 := by
  rw [orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_second (a b c : Point 3) :
    orientedVolume a b c b = 0 := by
  rw [orientedVolume_eq]
  ring

@[simp] private lemma orientedVolume_self_third (a b c : Point 3) :
    orientedVolume a b c c = 0 := by
  rw [orientedVolume_eq]
  ring

private lemma ordered_above_volume_orientation_neg
    {a b c d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (h : SegmentAbove a c b d) :
    orientedVolume a b c d * projectedOrientation a b c < 0 := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hid := crossing_orientedVolume_identity hcross
  have hu : 0 < u := hcross.2.1.1
  have hH : 0 < verticalHeight (segmentPoint a c t) -
      verticalHeight (segmentPoint b d u) := sub_pos.mpr hheight
  have hP : projectedOrientation a b c ≠ 0 := by
    intro hP0
    have hV : orientedVolume a b c d = 0 := by
      have : u * orientedVolume a b c d = 0 := by
        rw [hid]
        change -(verticalHeight (segmentPoint a c t) -
          verticalHeight (segmentPoint b d u)) * projectedOrientation a b c = 0
        rw [hP0, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hu.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hind hV
  have hsq : 0 < projectedOrientation a b c ^ 2 := sq_pos_of_ne_zero hP
  have hidP := congrArg (fun z : ℝ => z * projectedOrientation a b c) hid
  have hmul : u * (orientedVolume a b c d * projectedOrientation a b c) < 0 := by
    calc
      u * (orientedVolume a b c d * projectedOrientation a b c) =
          (u * orientedVolume a b c d) * projectedOrientation a b c := by ring
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) *
            projectedOrientation a b c := hidP
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          projectedOrientation a b c ^ 2 := by
        rw [pow_two, projectedOrientation]
        ring
      _ < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hH) hsq
  by_contra hnonneg
  exact (not_lt_of_ge (mul_nonneg hu.le (le_of_not_gt hnonneg))) hmul

private lemma ordered_below_volume_orientation_pos
    {a b c d : Point 3}
    (hind : AffineIndependent ℝ ![a, b, c, d])
    (h : SegmentBelow a c b d) :
    0 < orientedVolume a b c d * projectedOrientation a b c := by
  obtain ⟨t, u, hcross, hheight⟩ := h
  have hid := crossing_orientedVolume_identity hcross
  have hu : 0 < u := hcross.2.1.1
  have hH : verticalHeight (segmentPoint a c t) -
      verticalHeight (segmentPoint b d u) < 0 := sub_neg.mpr hheight
  have hP : projectedOrientation a b c ≠ 0 := by
    intro hP0
    have hV : orientedVolume a b c d = 0 := by
      have : u * orientedVolume a b c d = 0 := by
        rw [hid]
        change -(verticalHeight (segmentPoint a c t) -
          verticalHeight (segmentPoint b d u)) * projectedOrientation a b c = 0
        rw [hP0, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hu.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hind hV
  have hsq : 0 < projectedOrientation a b c ^ 2 := sq_pos_of_ne_zero hP
  have hidP := congrArg (fun z : ℝ => z * projectedOrientation a b c) hid
  have hmul : 0 < u * (orientedVolume a b c d * projectedOrientation a b c) := by
    calc
      0 < -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          projectedOrientation a b c ^ 2 := mul_pos (neg_pos.mpr hH) hsq
      _ = -(verticalHeight (segmentPoint a c t) - verticalHeight (segmentPoint b d u)) *
          ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) *
            projectedOrientation a b c := by
        rw [pow_two, projectedOrientation]
        ring
      _ = (u * orientedVolume a b c d) * projectedOrientation a b c := hidP.symm
      _ = u * (orientedVolume a b c d * projectedOrientation a b c) := by ring
  by_contra hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt hnonpos))) hmul

private lemma product_pos_of_positive_ratio {P Q u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hQ : Q ≠ 0) (h : u * P = v * Q) :
    0 < Q * P := by
  have hsq : 0 < Q ^ 2 := sq_pos_of_ne_zero hQ
  have hmul := congrArg (fun z : ℝ => z * Q) h
  have : 0 < u * (Q * P) := by
    nlinarith
  by_contra hnonpos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hu.le (le_of_not_gt hnonpos))) this

private lemma same_sign_trans {A B C : ℝ}
    (hAB : 0 < A * B) (hBC : 0 < B * C) : 0 < A * C := by
  rcases (mul_pos_iff.mp hBC) with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · exact mul_pos (pos_of_mul_pos_left hAB hB.le) hC
  · exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left hAB hB.le) hC

private lemma opposite_sign_trans {A B C : ℝ}
    (hAB : A * B < 0) (hBC : 0 < B * C) : A * C < 0 := by
  rcases (mul_pos_iff.mp hBC) with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · exact mul_neg_of_neg_of_pos (neg_of_mul_neg_left hAB hB.le) hC
  · exact mul_neg_of_pos_of_neg (pos_of_mul_neg_left hAB hB.le) hC

/-- If two chords from the same first three endpoints are both above (or
both below), the corresponding ordered tetrahedra have the same orientation. -/
lemma orientedVolumes_same_sign_of_same_above
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (he : AffineIndependent ℝ ![a, b, c, e])
    (habd : SegmentAbove a c b d) (habe : SegmentAbove a c b e) :
    (0 < orientedVolume a b c d ∧ 0 < orientedVolume a b c e) ∨
      (orientedVolume a b c d < 0 ∧ orientedVolume a b c e < 0) := by
  obtain ⟨td, ud, hcrossd, hheightd⟩ := habd
  obtain ⟨te, ue, hcrosse, highte⟩ := habe
  have hid := crossing_orientedVolume_identity hcrossd
  have hie := crossing_orientedVolume_identity hcrosse
  have hud : 0 < ud := hcrossd.2.1.1
  have hue : 0 < ue := hcrosse.2.1.1
  have hHd : 0 < verticalHeight (segmentPoint a c td) -
      verticalHeight (segmentPoint b d ud) := sub_pos.mpr hheightd
  have hHe : 0 < verticalHeight (segmentPoint a c te) -
      verticalHeight (segmentPoint b e ue) := sub_pos.mpr highte
  let P : ℝ := (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)
  have hP : P ≠ 0 := by
    intro hP0
    have : orientedVolume a b c d = 0 := by
      dsimp [P] at hP0
      have hid0 : ud * orientedVolume a b c d = 0 := by
        rw [hid, hP0, mul_zero]
      exact (mul_eq_zero.mp hid0).resolve_left hud.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hd this
  rcases hP.lt_or_gt with hPneg | hPpos
  · left
    constructor
    · exact pos_of_mul_pos_right (by nlinarith [hid]) hud.le
    · exact pos_of_mul_pos_right (by nlinarith [hie]) hue.le
  · right
    constructor
    · exact neg_of_mul_neg_right (by nlinarith [hid]) hud.le
    · exact neg_of_mul_neg_right (by nlinarith [hie]) hue.le

lemma orientedVolumes_same_sign_of_same_below
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (_he : AffineIndependent ℝ ![a, b, c, e])
    (habd : SegmentBelow a c b d) (habe : SegmentBelow a c b e) :
    (0 < orientedVolume a b c d ∧ 0 < orientedVolume a b c e) ∨
      (orientedVolume a b c d < 0 ∧ orientedVolume a b c e < 0) := by
  obtain ⟨td, ud, hcrossd, hheightd⟩ := habd
  obtain ⟨te, ue, hcrosse, highte⟩ := habe
  have hid := crossing_orientedVolume_identity hcrossd
  have hie := crossing_orientedVolume_identity hcrosse
  have hud : 0 < ud := hcrossd.2.1.1
  have hue : 0 < ue := hcrosse.2.1.1
  have hHd : verticalHeight (segmentPoint a c td) -
      verticalHeight (segmentPoint b d ud) < 0 := sub_neg.mpr hheightd
  have hHe : verticalHeight (segmentPoint a c te) -
      verticalHeight (segmentPoint b e ue) < 0 := sub_neg.mpr highte
  let P : ℝ := (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)
  have hP : P ≠ 0 := by
    intro hP0
    have : orientedVolume a b c d = 0 := by
      dsimp [P] at hP0
      have hid0 : ud * orientedVolume a b c d = 0 := by
        rw [hid, hP0, mul_zero]
      exact (mul_eq_zero.mp hid0).resolve_left hud.ne'
    exact orientedVolume_ne_zero_of_affineIndependent hd this
  rcases hP.lt_or_gt with hPneg | hPpos
  · right
    constructor
    · exact neg_of_mul_neg_right (by nlinarith [hid]) hud.le
    · exact neg_of_mul_neg_right (by nlinarith [hie]) hue.le
  · left
    constructor
    · exact pos_of_mul_pos_right (by nlinarith [hid]) hud.le
    · exact pos_of_mul_pos_right (by nlinarith [hie]) hue.le

private lemma convex_relation_orientedVolume_identity
    {a b c d e : Point 3} {A B C D E : ℝ}
    (hs₁ : A + C = 1) (hs₂ : B + D + E = 1)
    (hp : A • a + C • c = B • b + D • d + E • e) :
    E * orientedVolume a b c e = -D * orientedVolume a b c d := by
  have hp₀ := congrArg (fun p : Point 3 => p 0) hp
  have hp₁ := congrArg (fun p : Point 3 => p 1) hp
  have hp₂ := congrArg (fun p : Point 3 => p 2) hp
  change A * a 0 + C * c 0 = B * b 0 + D * d 0 + E * e 0 at hp₀
  change A * a 1 + C * c 1 = B * b 1 + D * d 1 + E * e 1 at hp₁
  change A * a 2 + C * c 2 = B * b 2 + D * d 2 + E * e 2 at hp₂
  have r₀ : E * (e 0 - a 0) + D * (d 0 - a 0) + B * (b 0 - a 0) -
      C * (c 0 - a 0) = 0 := by
    linear_combination -hp₀ + a 0 * hs₁ - a 0 * hs₂
  have r₁ : E * (e 1 - a 1) + D * (d 1 - a 1) + B * (b 1 - a 1) -
      C * (c 1 - a 1) = 0 := by
    linear_combination -hp₁ + a 1 * hs₁ - a 1 * hs₂
  have r₂ : E * (e 2 - a 2) + D * (d 2 - a 2) + B * (b 2 - a 2) -
      C * (c 2 - a 2) = 0 := by
    linear_combination -hp₂ + a 2 * hs₁ - a 2 * hs₂
  rw [orientedVolume_eq, orientedVolume_eq]
  linear_combination
    ((b 1 - a 1) * (c 2 - a 2) - (b 2 - a 2) * (c 1 - a 1)) * r₀ +
    ((b 2 - a 2) * (c 0 - a 0) - (b 0 - a 0) * (c 2 - a 2)) * r₁ +
    ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) * r₂

/-- The convex-combination core of Proposition 2.3: a common strict
orientation for the two tetrahedra prevents the segment from meeting the
opposite triangle. -/
private theorem segment_triangle_disjoint_of_same_orientation
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (he : AffineIndependent ℝ ![a, b, c, e]) (hde : d ≠ e)
    (hsign : (0 < orientedVolume a b c d ∧ 0 < orientedVolume a b c e) ∨
      (orientedVolume a b c d < 0 ∧ orientedVolume a b c e < 0)) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, d, e} : Set (Point 3))) := by
  have hac : a ≠ c := by
    intro h
    have hi : (0 : Fin 4) = 2 := hd.injective (by simpa using h)
    omega
  have hbd : b ≠ d := by
    intro h
    have hi : (1 : Fin 4) = 3 := hd.injective (by simpa using h)
    omega
  have hbe : b ≠ e := by
    intro h
    have hi : (1 : Fin 4) = 3 := he.injective (by simpa using h)
    omega
  rw [Set.disjoint_left]
  intro z hzac hzbde
  have hzac' : z ∈ convexHull ℝ (({a, c} : Finset (Point 3)) : Set (Point 3)) := by
    simpa using hzac
  have hzbde' : z ∈ convexHull ℝ (({b, d, e} : Finset (Point 3)) : Set (Point 3)) := by
    simpa using hzbde
  obtain ⟨w, hw, hwsum, hwz⟩ := Finset.mem_convexHull'.mp hzac'
  obtain ⟨v, hv, hvsum, hvz⟩ := Finset.mem_convexHull'.mp hzbde'
  have hwsum' : w a + w c = 1 := by simpa [hac] using hwsum
  have hvsum' : v b + v d + v e = 1 := by
    simpa [hbd, hbe, hde, add_assoc] using hvsum
  have hwz' : w a • a + w c • c = z := by simpa [hac] using hwz
  have hvz' : v b • b + v d • d + v e • e = z := by
    simpa [hbd, hbe, hde, add_assoc] using hvz
  have hpoint : w a • a + w c • c = v b • b + v d • d + v e • e :=
    hwz'.trans hvz'.symm
  have hidentity := convex_relation_orientedVolume_identity hwsum' hvsum' hpoint
  have hvd : orientedVolume a b c d ≠ 0 :=
    orientedVolume_ne_zero_of_affineIndependent hd
  have hve : orientedVolume a b c e ≠ 0 :=
    orientedVolume_ne_zero_of_affineIndependent he
  have hnotboth : ¬ (v d = 0 ∧ v e = 0) := by
    rintro ⟨hD, hE⟩
    have hB : v b = 1 := by linarith [hvsum']
    let w₁ : Fin 4 → ℝ := ![w a, 0, w c, 0]
    let w₂ : Fin 4 → ℝ := ![0, v b, 0, 0]
    have hsums : ∑ i, w₁ i = ∑ i, w₂ i := by
      simp [Fin.sum_univ_four, w₁, w₂, hwsum', hB]
    have hpoints : ∑ i, w₁ i • ![a, b, c, d] i =
        ∑ i, w₂ i • ![a, b, c, d] i := by
      simp only [Fin.sum_univ_four]
      simp [w₁, w₂]
      simpa [hD, hE] using hpoint
    have hcoeff := hd.eq_of_sum_eq_sum (s := Finset.univ) hsums hpoints
    have := hcoeff 1 (by simp)
    simp [w₁, w₂, hB] at this
  have hD : v d ≠ 0 := by
    intro hD
    have hE : v e = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hve
      rw [hidentity, hD, neg_zero, zero_mul]
    exact hnotboth ⟨hD, hE⟩
  have hE : v e ≠ 0 := by
    intro hE
    have hD : v d = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hvd
      have : -v d * orientedVolume a b c d = 0 := by
        rw [← hidentity, hE, zero_mul]
      simpa using this
    exact hnotboth ⟨hD, hE⟩
  have hDpos : 0 < v d := lt_of_le_of_ne (hv d (by simp)) (Ne.symm hD)
  have hEpos : 0 < v e := lt_of_le_of_ne (hv e (by simp)) (Ne.symm hE)
  rcases hsign with hpos | hneg
  · have hleft : 0 < v e * orientedVolume a b c e := mul_pos hEpos hpos.2
    have hright : -v d * orientedVolume a b c d < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hDpos) hpos.1
    linarith [hidentity]
  · have hleft : v e * orientedVolume a b c e < 0 := mul_neg_of_pos_of_neg hEpos hneg.2
    have hright : 0 < -v d * orientedVolume a b c d :=
      mul_pos_of_neg_of_neg (neg_neg_of_pos hDpos) hneg.1
    linarith [hidentity]

/-- The geometric core of Proposition 2.3: if `ac` lies above both `bd`
and `be`, then the segment `ac` misses the triangle `bde`. -/
theorem segment_triangle_disjoint_of_same_above
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (he : AffineIndependent ℝ ![a, b, c, e]) (hde : d ≠ e)
    (habd : SegmentAbove a c b d) (habe : SegmentAbove a c b e) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, d, e} : Set (Point 3))) :=
  segment_triangle_disjoint_of_same_orientation hd he hde
    (orientedVolumes_same_sign_of_same_above hd he habd habe)

/-- The same conclusion when the first segment is uniformly below the two
other segments. -/
theorem segment_triangle_disjoint_of_same_below
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (he : AffineIndependent ℝ ![a, b, c, e]) (hde : d ≠ e)
    (habd : SegmentBelow a c b d) (habe : SegmentBelow a c b e) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, d, e} : Set (Point 3))) :=
  segment_triangle_disjoint_of_same_orientation hd he hde
    (orientedVolumes_same_sign_of_same_below hd he habd habe)

/-- The companion form in which the two lower segments share their second
endpoint rather than their first endpoint. -/
theorem segment_triangle_disjoint_of_same_above_shared_right
    {a b b' c d : Point 3}
    (hb : AffineIndependent ℝ ![a, b, c, d])
    (hb' : AffineIndependent ℝ ![a, b', c, d]) (hbb' : b ≠ b')
    (hab : SegmentAbove a c b d) (hab' : SegmentAbove a c b' d) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, b', d} : Set (Point 3))) := by
  have hbperm : AffineIndependent ℝ ![a, d, c, b] := by
    have h := hb.comp_embedding (Equiv.swap (1 : Fin 4) 3).toEmbedding
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hb'perm : AffineIndependent ℝ ![a, d, c, b'] := by
    have h := hb'.comp_embedding (Equiv.swap (1 : Fin 4) 3).toEmbedding
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hdisj := segment_triangle_disjoint_of_same_above hbperm hb'perm hbb'
    (segmentAbove_swap_right hab) (segmentAbove_swap_right hab')
  have hset : ({d, b, b'} : Set (Point 3)) = {b, b', d} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  simpa [hset] using hdisj

theorem segment_triangle_disjoint_of_same_below_shared_right
    {a b b' c d : Point 3}
    (hb : AffineIndependent ℝ ![a, b, c, d])
    (hb' : AffineIndependent ℝ ![a, b', c, d]) (hbb' : b ≠ b')
    (hab : SegmentBelow a c b d) (hab' : SegmentBelow a c b' d) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, b', d} : Set (Point 3))) := by
  have hbperm : AffineIndependent ℝ ![a, d, c, b] := by
    have h := hb.comp_embedding (Equiv.swap (1 : Fin 4) 3).toEmbedding
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hb'perm : AffineIndependent ℝ ![a, d, c, b'] := by
    have h := hb'.comp_embedding (Equiv.swap (1 : Fin 4) 3).toEmbedding
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hdisj := segment_triangle_disjoint_of_same_below hbperm hb'perm hbb'
    (segmentBelow_swap_right hab) (segmentBelow_swap_right hab')
  have hset : ({d, b, b'} : Set (Point 3)) = {b, b', d} := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  simpa [hset] using hdisj

/-- The five-point `X₁,X₂,X₃,X₄,X₄` circuit excluded in the proof of
Pohoata--Zakharov Proposition 2.3. -/
theorem five_point_four_block_separation_right
    {a b c d e : Point 3}
    (hd : AffineIndependent ℝ ![a, b, c, d])
    (he : AffineIndependent ℝ ![a, b, c, e]) (hde : d ≠ e)
    (habd : SegmentAbove a c b d) (habe : SegmentAbove a c b e) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, d, e} : Set (Point 3))) :=
  segment_triangle_disjoint_of_same_above hd he hde habd habe

/-- The five-point `X₁,X₂,X₂,X₃,X₄` circuit excluded in the proof of
Pohoata--Zakharov Proposition 2.3. -/
theorem five_point_four_block_separation_left
    {a b b' c d : Point 3}
    (hb : AffineIndependent ℝ ![a, b, c, d])
    (hb' : AffineIndependent ℝ ![a, b', c, d]) (hbb' : b ≠ b')
    (hab : SegmentAbove a c b d) (hab' : SegmentAbove a c b' d) :
    Disjoint (convexHull ℝ ({a, c} : Set (Point 3)))
      (convexHull ℝ ({b, b', d} : Set (Point 3))) :=
  segment_triangle_disjoint_of_same_above_shared_right hb hb' hbb' hab hab'

/-! ## The four-uniform Ramsey selection -/

/-- Every interlaced quadruple of indices has the projected crossing and
general-position properties needed by the above--below dichotomy.  Consecutive
vertices of a strictly convex projected polygon satisfy this predicate. -/
def IsProjectedConvexChain {I : Type*} [LinearOrder I]
    (x : I → Point 3) (S : Finset I) : Prop :=
  ∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
    i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
      AffineIndependent ℝ ![x i₀, x i₁, x i₂, x i₃] ∧
        ∃ t u : ℝ, ProjectedSegmentsCrossAt (x i₀) (x i₂) (x i₁) (x i₃) t u

/-- All interlaced chords on `S` have the same strict vertical order. -/
def UniformAboveBelowOn {I : Type*} [LinearOrder I]
    (x : I → Point 3) (S : Finset I) : Prop :=
  (∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
        SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃)) ∨
  (∀ i₀ ∈ S, ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ i₃ ∈ S,
      i₀ < i₁ → i₁ < i₂ → i₂ < i₃ →
        SegmentBelow (x i₀) (x i₂) (x i₁) (x i₃))

private lemma cutSign_above_before
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i a b c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (hi : i ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hia : i < a) (hab : a < b) (hbc : b < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain i hi a ha b hb c hc hia hab hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove i hi a ha b hb c hc hia hab hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x i) (x a) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x i) (x a) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.1.2) hQ hids.2.2
  have h := opposite_sign_trans hneg hsame
  rw [orientedVolume_rotate]
  nlinarith

private lemma cutSign_above_between₁
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a i b c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hi : i ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hai : a < i) (hib : i < b) (hbc : b < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain a ha i hi b hb c hc hai hib hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove a ha i hi b hb c hc hai hib hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x i) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x a) (x i) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.2.1.2) hQ hids.2.1
  rw [orientedVolume_middle_rotate]
  exact opposite_sign_trans hneg hsame

private lemma cutSign_above_between₂
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b i c : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hi : i ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbi : b < i) (hic : i < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain a ha b hb i hi c hc hab hbi hic
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hneg := ordered_above_volume_orientation_neg hdata.1
    (habove a ha b hb i hi c hc hab hbi hic)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x b) (x i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hneg
    exact (lt_irrefl 0) hneg
  have hsame : 0 < projectedOrientation (x a) (x b) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 hcross.1.1 hQ hids.1
  have h := opposite_sign_trans hneg hsame
  rw [orientedVolume_swap_last]
  nlinarith

private lemma cutSign_above_after
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i : I} (hchain : IsProjectedConvexChain x S)
    (habove : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hi : i ∈ S)
    (hab : a < b) (hbc : b < c) (hci : c < i) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 :=
  ordered_above_volume_orientation_neg
    (hchain a ha b hb c hc i hi hab hbc hci).1
    (habove a ha b hb c hc i hi hab hbc hci)

private lemma cutSign_below_before
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i a b c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (hi : i ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hia : i < a) (hab : a < b) (hbc : b < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain i hi a ha b hb c hc hia hab hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow i hi a ha b hb c hc hia hab hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x i) (x a) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x i) (x a) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.1.2) hQ hids.2.2
  have h := same_sign_trans hpos hsame
  rw [orientedVolume_rotate]
  nlinarith

private lemma cutSign_below_between₁
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a i b c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hi : i ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hai : a < i) (hib : i < b) (hbc : b < c) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) := by
  have hdata := hchain a ha i hi b hb c hc hai hib hbc
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow a ha i hi b hb c hc hai hib hbc)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x i) (x b) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x a) (x i) (x b) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 (sub_pos.mpr hcross.2.1.2) hQ hids.2.1
  rw [orientedVolume_middle_rotate]
  exact same_sign_trans hpos hsame

private lemma cutSign_below_between₂
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b i c : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hi : i ∈ S) (hc : c ∈ S)
    (hab : a < b) (hbi : b < i) (hic : i < c) :
    orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) < 0 := by
  have hdata := hchain a ha b hb i hi c hc hab hbi hic
  obtain ⟨t, u, hcross⟩ := hdata.2
  have hpos := ordered_below_volume_orientation_pos hdata.1
    (hbelow a ha b hb i hi c hc hab hbi hic)
  have hids := projectedOrientation_identities_of_crossing hcross
  have hQ : projectedOrientation (x a) (x b) (x i) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hsame : 0 < projectedOrientation (x a) (x b) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
    product_pos_of_positive_ratio hcross.2.1.1 hcross.1.1 hQ hids.1
  have h := same_sign_trans hpos hsame
  rw [orientedVolume_swap_last]
  nlinarith

private lemma cutSign_below_after
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i : I} (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ → SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hi : i ∈ S)
    (hab : a < b) (hbc : b < c) (hci : c < i) :
    0 < orientedVolume (x a) (x b) (x c) (x i) *
      projectedOrientation (x a) (x b) (x c) :=
  ordered_below_volume_orientation_pos
    (hchain a ha b hb c hc i hi hab hbc hci).1
    (hbelow a ha b hb c hc i hi hab hbc hci)

/-- The affine cut through three vertices, normalized so that the sign
lemmas above do not depend on the orientation of their projection. -/
private def alternatingCutAffine (a b c : Point 3) : Point 3 →ᵃ[ℝ] ℝ :=
  projectedOrientation a b c • orientedVolumeAffine a b c

@[simp] private lemma alternatingCutAffine_apply (a b c p : Point 3) :
    alternatingCutAffine a b c p =
      orientedVolume a b c p * projectedOrientation a b c := by
  simp [alternatingCutAffine, mul_comm]

private theorem convexHulls_disjoint_of_weak_affine_separator
    (A B : Finset (Point 3)) (f : Point 3 →ᵃ[ℝ] ℝ)
    (hAB : Disjoint A B) (hA : ∀ p ∈ A, 0 ≤ f p) (hB : ∀ p ∈ B, f p ≤ 0)
    (hzero : AffineIndependent ℝ
      (fun p : ↥((A.filter fun p => f p = 0) ∪ (B.filter fun p => f p = 0)) ↦
        (p : Point 3))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  classical
  rw [Set.disjoint_left]
  intro z hzA hzB
  have hznonneg : 0 ≤ f z := by
    have hz : z ∈ f ⁻¹' Set.Ici 0 :=
      convexHull_min (fun p hp => hA p hp)
        ((convex_Ici (0 : ℝ)).affine_preimage f) hzA
    exact hz
  have hznonpos : f z ≤ 0 := by
    have hz : z ∈ f ⁻¹' Set.Iic 0 :=
      convexHull_min (fun p hp => hB p hp)
        ((convex_Iic (0 : ℝ)).affine_preimage f) hzB
    exact hz
  have hzf : f z = 0 := le_antisymm hznonpos hznonneg
  have hzAf := mem_convexHull_zero_face A f hA hzA hzf
  have hzBf' := mem_convexHull_zero_face B (-f)
    (by intro p hp; simpa using neg_nonneg.mpr (hB p hp)) hzB (by simp [hzf])
  have hfilter : B.filter (fun p => (-f) p = 0) = B.filter fun p => f p = 0 := by
    ext p
    simp
  rw [hfilter] at hzBf'
  have hinter := hzero.convexHull_inter'
  have hzinter : z ∈
      convexHull ℝ ((A.filter fun p => f p = 0) : Set (Point 3)) ∩
        convexHull ℝ ((B.filter fun p => f p = 0) : Set (Point 3)) :=
    ⟨hzAf, hzBf'⟩
  rw [← hinter] at hzinter
  have hdiszero : Disjoint
      (((A.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3))
      (((B.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    change p ∈ A.filter (fun p => f p = 0) at hpA
    change p ∈ B.filter (fun p => f p = 0) at hpB
    exact Finset.disjoint_left.1 hAB (Finset.mem_filter.1 hpA).1
      (Finset.mem_filter.1 hpB).1
  have hempty :
      (((A.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) ∩
        (((B.filter fun p => f p = 0) : Finset (Point 3)) : Set (Point 3)) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdiszero
  rw [hempty] at hzinter
  simpa using hzinter

private lemma affineIndependent_finset_of_subset_quad
    {p₀ p₁ p₂ p₃ : Point 3} {T : Finset (Point 3)}
    (h : AffineIndependent ℝ ![p₀, p₁, p₂, p₃])
    (hT : T ⊆ {p₀, p₁, p₂, p₃}) :
    AffineIndependent ℝ (fun p : ↥T ↦ (p : Point 3)) := by
  have hrange : Set.range (![p₀, p₁, p₂, p₃] : Fin 4 → Point 3) =
      ({p₀, p₁, p₂, p₃} : Set (Point 3)) := by
    ext p
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  have hrangeAI := h.range
  rw [hrange] at hrangeAI
  exact hrangeAI.mono (by
    intro p hp
    simpa using hT hp)

private theorem five_point_partition_disjoint_of_adjacent_pair
    (A B : Finset (Point 3)) (f : Point 3 →ᵃ[ℝ] ℝ)
    {p q r s t : Point 3}
    (hAB : Disjoint A B)
    (hAcov : A ⊆ {p, q, r, s, t}) (hBcov : B ⊆ {p, q, r, s, t})
    (hpq : (p ∈ A ∧ q ∈ A) ∨ (p ∈ B ∧ q ∈ B))
    (hroot : f r = 0 ∧ f s = 0 ∧ f t = 0)
    (hsign : (0 < f p ∧ 0 < f q) ∨ (f p < 0 ∧ f q < 0))
    (hrootAI : AffineIndependent ℝ
      (fun z : ↥({r, s, t} : Finset (Point 3)) ↦ (z : Point 3))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  classical
  have hfp : f p ≠ 0 := by rcases hsign with h | h <;> nlinarith [h.1]
  have hfq : f q ≠ 0 := by rcases hsign with h | h <;> nlinarith [h.2]
  have hzero_f : AffineIndependent ℝ
      (fun z : ↥((A.filter fun z => f z = 0) ∪ (B.filter fun z => f z = 0)) ↦
        (z : Point 3)) := by
    apply hrootAI.mono
    intro z hz
    simp only [Finset.coe_union, Finset.coe_filter, Set.mem_union, Set.mem_setOf_eq] at hz
    have hzcover : z ∈ ({p, q, r, s, t} : Finset (Point 3)) := by
      rcases hz with hz | hz
      · exact hAcov hz.1
      · exact hBcov hz.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzcover ⊢
    rcases hzcover with rfl | rfl | rfl | rfl | rfl
    · rcases hz with hz | hz <;> exact (hfp hz.2).elim
    · rcases hz with hz | hz <;> exact (hfq hz.2).elim
    · simp
    · simp
    · simp
  have hzero_neg : AffineIndependent ℝ
      (fun z : ↥((A.filter fun z => (-f) z = 0) ∪ (B.filter fun z => (-f) z = 0)) ↦
        (z : Point 3)) := by
    have heq :
        (A.filter fun z => (-f) z = 0) ∪ (B.filter fun z => (-f) z = 0) =
          (A.filter fun z => f z = 0) ∪ (B.filter fun z => f z = 0) := by
      ext z
      simp
    rw [heq]
    exact hzero_f
  rcases hpq with hpqA | hpqB
  · rcases hsign with hpos | hneg
    · apply convexHulls_disjoint_of_weak_affine_separator A B f hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact hpos.1.le
        · exact hpos.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hpqA.1 hzB).elim
        · exact (Finset.disjoint_left.1 hAB hpqA.2 hzB).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_f
    · apply convexHulls_disjoint_of_weak_affine_separator A B (-f) hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · simpa using neg_nonneg.mpr hneg.1.le
        · simpa using neg_nonneg.mpr hneg.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hpqA.1 hzB).elim
        · exact (Finset.disjoint_left.1 hAB hpqA.2 hzB).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_neg
  · rcases hsign with hpos | hneg
    · apply convexHulls_disjoint_of_weak_affine_separator A B (-f) hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.1).elim
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.2).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · simpa using neg_nonpos.mpr hpos.1.le
        · simpa using neg_nonpos.mpr hpos.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_neg
    · apply convexHulls_disjoint_of_weak_affine_separator A B f hAB
      · intro z hzA
        have hz := hAcov hzA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.1).elim
        · exact (Finset.disjoint_left.1 hAB hzA hpqB.2).elim
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · intro z hzB
        have hz := hBcov hzB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl
        · exact hneg.1.le
        · exact hneg.2.le
        · simp [hroot.1]
        · simp [hroot.2.1]
        · simp [hroot.2.2]
      · exact hzero_f

/-- Proposition 2.3 in the `X₁,X₂,X₃,X₄,X₄` five-point normal form,
obtained directly from the uniform-above alternative.  In particular, the
local Kirchberger witness is discharged rather than retained as a premise. -/
theorem uniformAbove_fivePointSeparation_right
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₃ i₄ i₄' : I}
    (hchain : IsProjectedConvexChain x S)
    (habe : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ →
        SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₃ : i₃ ∈ S)
    (hi₄ : i₄ ∈ S) (hi₄' : i₄' ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄) (h₄₄' : i₄ < i₄') :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₄, x i₄'} : Set (Point 3))) := by
  have hd := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
  have he := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄' hi₄' h₁₂ h₂₃
    (h₃₄.trans h₄₄')).1
  have hlast := (hchain i₂ hi₂ i₃ hi₃ i₄ hi₄ i₄' hi₄' h₂₃ h₃₄ h₄₄').1
  have hne : x i₄ ≠ x i₄' := by
    intro h
    have hi : (2 : Fin 4) = 3 := hlast.injective (by simpa using h)
    omega
  exact five_point_four_block_separation_right hd he hne
    (habe i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄)
    (habe i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄' hi₄' h₁₂ h₂₃ (h₃₄.trans h₄₄'))

/-- Proposition 2.3 in the `X₁,X₂,X₂,X₃,X₄` five-point normal form,
again with the Kirchberger witness discharged by uniform above/below data. -/
theorem uniformAbove_fivePointSeparation_left
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₂' i₃ i₄ : I}
    (hchain : IsProjectedConvexChain x S)
    (habe : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ →
        SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃))
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₂' : i₂' ∈ S)
    (hi₃ : i₃ ∈ S) (hi₄ : i₄ ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₂' : i₂ < i₂') (h₂'₃ : i₂' < i₃) (h₃₄ : i₃ < i₄) :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₂', x i₄} : Set (Point 3))) := by
  have h₂₃ : i₂ < i₃ := h₂₂'.trans h₂'₃
  have hb := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
  have hb' := (hchain i₁ hi₁ i₂' hi₂' i₃ hi₃ i₄ hi₄
    (h₁₂.trans h₂₂') h₂'₃ h₃₄).1
  have hmid := (hchain i₁ hi₁ i₂ hi₂ i₂' hi₂' i₃ hi₃ h₁₂ h₂₂' h₂'₃).1
  have hne : x i₂ ≠ x i₂' := by
    intro h
    have hi : (1 : Fin 4) = 2 := hmid.injective (by simpa using h)
    omega
  exact five_point_four_block_separation_left hb hb' hne
    (habe i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄)
    (habe i₁ hi₁ i₂' hi₂' i₃ hi₃ i₄ hi₄ (h₁₂.trans h₂₂') h₂'₃ h₃₄)

theorem uniformBelow_fivePointSeparation_right
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₃ i₄ i₄' : I}
    (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ →
        SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₃ : i₃ ∈ S)
    (hi₄ : i₄ ∈ S) (hi₄' : i₄' ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄) (h₄₄' : i₄ < i₄') :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₄, x i₄'} : Set (Point 3))) := by
  have hd := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
  have he := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄' hi₄' h₁₂ h₂₃
    (h₃₄.trans h₄₄')).1
  have hlast := (hchain i₂ hi₂ i₃ hi₃ i₄ hi₄ i₄' hi₄' h₂₃ h₃₄ h₄₄').1
  have hne : x i₄ ≠ x i₄' := by
    intro h
    have hi : (2 : Fin 4) = 3 := hlast.injective (by simpa using h)
    omega
  exact segment_triangle_disjoint_of_same_below hd he hne
    (hbelow i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄)
    (hbelow i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄' hi₄' h₁₂ h₂₃ (h₃₄.trans h₄₄'))

theorem uniformBelow_fivePointSeparation_left
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₂' i₃ i₄ : I}
    (hchain : IsProjectedConvexChain x S)
    (hbelow : ∀ j₀ ∈ S, ∀ j₁ ∈ S, ∀ j₂ ∈ S, ∀ j₃ ∈ S,
      j₀ < j₁ → j₁ < j₂ → j₂ < j₃ →
        SegmentBelow (x j₀) (x j₂) (x j₁) (x j₃))
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₂' : i₂' ∈ S)
    (hi₃ : i₃ ∈ S) (hi₄ : i₄ ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₂' : i₂ < i₂') (h₂'₃ : i₂' < i₃) (h₃₄ : i₃ < i₄) :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₂', x i₄} : Set (Point 3))) := by
  have h₂₃ : i₂ < i₃ := h₂₂'.trans h₂'₃
  have hb := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
  have hb' := (hchain i₁ hi₁ i₂' hi₂' i₃ hi₃ i₄ hi₄
    (h₁₂.trans h₂₂') h₂'₃ h₃₄).1
  have hmid := (hchain i₁ hi₁ i₂ hi₂ i₂' hi₂' i₃ hi₃ h₁₂ h₂₂' h₂'₃).1
  have hne : x i₂ ≠ x i₂' := by
    intro h
    have hi : (1 : Fin 4) = 2 := hmid.injective (by simpa using h)
    omega
  exact segment_triangle_disjoint_of_same_below_shared_right hb hb' hne
    (hbelow i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄)
    (hbelow i₁ hi₁ i₂' hi₂' i₃ hi₃ i₄ hi₄ (h₁₂.trans h₂₂') h₂'₃ h₃₄)

/-- The unconditional five-point normal form of Proposition 2.3, covering
both Ramsey colors. -/
theorem uniformAboveBelow_fivePointSeparation_right
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₃ i₄ i₄' : I}
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S)
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₃ : i₃ ∈ S)
    (hi₄ : i₄ ∈ S) (hi₄' : i₄' ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄) (h₄₄' : i₄ < i₄') :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₄, x i₄'} : Set (Point 3))) := by
  rcases huniform with habove | hbelow
  · exact uniformAbove_fivePointSeparation_right hchain habove hi₁ hi₂ hi₃ hi₄ hi₄'
      h₁₂ h₂₃ h₃₄ h₄₄'
  · exact uniformBelow_fivePointSeparation_right hchain hbelow hi₁ hi₂ hi₃ hi₄ hi₄'
      h₁₂ h₂₃ h₃₄ h₄₄'

theorem uniformAboveBelow_fivePointSeparation_left
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {i₁ i₂ i₂' i₃ i₄ : I}
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S)
    (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S) (hi₂' : i₂' ∈ S)
    (hi₃ : i₃ ∈ S) (hi₄ : i₄ ∈ S)
    (h₁₂ : i₁ < i₂) (h₂₂' : i₂ < i₂') (h₂'₃ : i₂' < i₃) (h₃₄ : i₃ < i₄) :
    Disjoint (convexHull ℝ ({x i₁, x i₃} : Set (Point 3)))
      (convexHull ℝ ({x i₂, x i₂', x i₄} : Set (Point 3))) := by
  rcases huniform with habove | hbelow
  · exact uniformAbove_fivePointSeparation_left hchain habove hi₁ hi₂ hi₂' hi₃ hi₄
      h₁₂ h₂₂' h₂'₃ h₃₄
  · exact uniformBelow_fivePointSeparation_left hchain hbelow hi₁ hi₂ hi₂' hi₃ hi₄
      h₁₂ h₂₂' h₂'₃ h₃₄

private noncomputable def quadAboveColor {I : Type*} [LinearOrder I]
    (x : I → Point 3) (A : Finset I) : Bool := by
  classical
  exact decide (∃ i₀ i₁ i₂ i₃ : I,
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧
    A = {i₀, i₁, i₂, i₃} ∧ SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃))

private lemma interlaced_insert_card {I : Type*} [LinearOrder I]
    {i₀ i₁ i₂ i₃ : I} (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) :
    ({i₀, i₁, i₂, i₃} : Finset I).card = 4 := by
  have h₀₂ : i₀ ≠ i₂ := (h₀₁.trans h₁₂).ne
  have h₀₃ : i₀ ≠ i₃ := (h₀₁.trans (h₁₂.trans h₂₃)).ne
  have h₁₃ : i₁ ≠ i₃ := (h₁₂.trans h₂₃).ne
  simp [h₀₁.ne, h₁₂.ne, h₂₃.ne, h₀₂, h₀₃, h₁₃]

/-- Four-uniform Ramsey selection for a lifted convex chain: a sufficiently
long chain has an `m`-element subchain on which every pair of crossing chords
has one fixed vertical order. -/
theorem exists_uniformAboveBelow_subchain (m : ℕ) :
    ∃ N : ℕ, ∀ {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I),
      N ≤ S.card → IsProjectedConvexChain x S →
        ∃ H : Finset I, H ⊆ S ∧ H.card = m ∧ UniformAboveBelowOn x H := by
  obtain ⟨N, hN⟩ := finite_quadruple_ramsey m
  refine ⟨N, ?_⟩
  intro I _ x S hcard hchain
  classical
  obtain ⟨H, hHS, hHm, b, hb⟩ := hN S hcard (quadAboveColor x)
  refine ⟨H, hHS, hHm, ?_⟩
  cases b with
  | false =>
      right
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hcfalse : quadAboveColor x A = false := hb A hAH hAcard
      have hnabove : ¬ SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃) := by
        intro habove
        have : quadAboveColor x A = true := by
          change decide (∃ j₀ j₁ j₂ j₃ : I,
            j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
            A = {j₀, j₁, j₂, j₃} ∧
              SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃)) = true
          exact decide_eq_true ⟨i₀, i₁, i₂, i₃, h₀₁, h₁₂, h₂₃, rfl, habove⟩
        simp_all
      have hdata := hchain i₀ (hHS hi₀) i₁ (hHS hi₁)
        i₂ (hHS hi₂) i₃ (hHS hi₃) h₀₁ h₁₂ h₂₃
      exact (segmentAbove_or_segmentBelow hdata.1 hdata.2).resolve_left hnabove
  | true =>
      left
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hctrue : quadAboveColor x A = true := hb A hAH hAcard
      have hex : ∃ j₀ j₁ j₂ j₃ : I,
          j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
          A = {j₀, j₁, j₂, j₃} ∧
            SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃) := by
        apply of_decide_eq_true
        exact hctrue
      obtain ⟨j₀, j₁, j₂, j₃, hj₀₁, hj₁₂, hj₂₃, hAeq, habove⟩ := hex
      have hj₀mem : j₀ ∈ A := by rw [hAeq]; simp
      have hj₁mem : j₁ ∈ A := by rw [hAeq]; simp
      have hj₂mem : j₂ ∈ A := by rw [hAeq]; simp
      have hj₃mem : j₃ ∈ A := by rw [hAeq]; simp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hj₀mem hj₁mem hj₂mem hj₃mem
      have hj₀ : j₀ = i₀ := by grind
      have hj₁ : j₁ = i₁ := by grind
      have hj₂ : j₂ = i₂ := by grind
      have hj₃ : j₃ = i₃ := by grind
      simpa [hj₀, hj₁, hj₂, hj₃] using habove

/-- The same four-uniform Ramsey selection with the concrete threshold used
by the nested-scale Pohoata--Zakharov assembly. -/
theorem exists_uniformAboveBelow_subchain_of_ramseySequence
    {m : ℕ} {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I)
    (hcard : uniformRamseySequence 4 m ≤ S.card)
    (hchain : IsProjectedConvexChain x S) :
    ∃ H : Finset I, H ⊆ S ∧ H.card = m ∧ UniformAboveBelowOn x H := by
  classical
  obtain ⟨H, hHS, hHm, b, hb⟩ :=
    uniformRamseySequence_spec 4 m S hcard (quadAboveColor x)
  refine ⟨H, hHS, hHm, ?_⟩
  cases b with
  | false =>
      right
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hcfalse : quadAboveColor x A = false := hb A hAH hAcard
      have hnabove : ¬ SegmentAbove (x i₀) (x i₂) (x i₁) (x i₃) := by
        intro habove
        have : quadAboveColor x A = true := by
          change decide (∃ j₀ j₁ j₂ j₃ : I,
            j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
            A = {j₀, j₁, j₂, j₃} ∧
              SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃)) = true
          exact decide_eq_true ⟨i₀, i₁, i₂, i₃, h₀₁, h₁₂, h₂₃, rfl, habove⟩
        simp_all
      have hdata := hchain i₀ (hHS hi₀) i₁ (hHS hi₁)
        i₂ (hHS hi₂) i₃ (hHS hi₃) h₀₁ h₁₂ h₂₃
      exact (segmentAbove_or_segmentBelow hdata.1 hdata.2).resolve_left hnabove
  | true =>
      left
      intro i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃
      let A : Finset I := {i₀, i₁, i₂, i₃}
      have hAH : A ⊆ H := by
        intro i hi
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        all_goals assumption
      have hAcard : A.card = 4 := by
        simpa [A] using interlaced_insert_card h₀₁ h₁₂ h₂₃
      have hctrue : quadAboveColor x A = true := hb A hAH hAcard
      have hex : ∃ j₀ j₁ j₂ j₃ : I,
          j₀ < j₁ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
          A = {j₀, j₁, j₂, j₃} ∧
            SegmentAbove (x j₀) (x j₂) (x j₁) (x j₃) := by
        apply of_decide_eq_true
        exact hctrue
      obtain ⟨j₀, j₁, j₂, j₃, hj₀₁, hj₁₂, hj₂₃, hAeq, habove⟩ := hex
      have hmem0 : j₀ ∈ A := by rw [hAeq]; simp
      have hmem1 : j₁ ∈ A := by rw [hAeq]; simp
      have hmem2 : j₂ ∈ A := by rw [hAeq]; simp
      have hmem3 : j₃ ∈ A := by rw [hAeq]; simp
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hmem0 hmem1 hmem2 hmem3
      have hj₀ : j₀ = i₀ := by grind
      have hj₁ : j₁ = i₁ := by grind
      have hj₂ : j₂ = i₂ := by grind
      have hj₃ : j₃ = i₃ := by grind
      simpa [hj₀, hj₁, hj₂, hj₃] using habove

/-! ## Alternating blocks and the five-point separation reduction -/

/-- The first side of the four consecutive blocks cut at `a,b,c`: the
initial and the third block. -/
def firstAlternatingBlock {I : Type*} [LinearOrder I]
    (S : Finset I) (a b c : I) : Finset I :=
  S.filter fun i => i < a ∨ (b ≤ i ∧ i < c)

/-- The second side of the four consecutive blocks cut at `a,b,c`: the
second and final block. -/
def secondAlternatingBlock {I : Type*} [LinearOrder I]
    (S : Finset I) (a b c : I) : Finset I :=
  S.filter fun i => (a ≤ i ∧ i < b) ∨ c ≤ i

private lemma IsProjectedConvexChain.injOn
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    (hchain : IsProjectedConvexChain x S) (hcard : 4 ≤ S.card) :
    Set.InjOn x (S : Set I) := by
  classical
  intro i hi j hj hij
  by_contra hne
  have hpcard : ({i, j} : Finset I).card = 2 := by simp [hne]
  have hpS : ({i, j} : Finset I) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  obtain ⟨T, hpT, hTS, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hpS (by omega : ({i, j} : Finset I).card ≤ 4) hcard
  let e : Fin 4 ↪o I := T.orderEmbOfFin hTcard
  have heS (r : Fin 4) : e r ∈ S :=
    hTS (T.orderEmbOfFin_mem hTcard r)
  have he₀₁ : e 0 < e 1 := e.strictMono (by omega)
  have he₁₂ : e 1 < e 2 := e.strictMono (by omega)
  have he₂₃ : e 2 < e 3 := e.strictMono (by omega)
  have heAI := (hchain (e 0) (heS 0) (e 1) (heS 1) (e 2) (heS 2) (e 3) (heS 3)
    he₀₁ he₁₂ he₂₃).1
  have hefun : (![x (e 0), x (e 1), x (e 2), x (e 3)] : Fin 4 → Point 3) =
      fun r => x (e r) := by
    funext r
    fin_cases r <;> rfl
  rw [hefun] at heAI
  have hiT : i ∈ T := hpT (by simp)
  have hjT : j ∈ T := hpT (by simp)
  have hiimage : i ∈ Finset.image e Finset.univ := by
    rw [T.image_orderEmbOfFin_univ hTcard]
    exact hiT
  have hjimage : j ∈ Finset.image e Finset.univ := by
    rw [T.image_orderEmbOfFin_univ hTcard]
    exact hjT
  obtain ⟨ri, -, hri⟩ := Finset.mem_image.1 hiimage
  obtain ⟨rj, -, hrj⟩ := Finset.mem_image.1 hjimage
  have hrirj : ri = rj := heAI.injective (by simpa [hri, hrj] using hij)
  apply hne
  exact hri.symm.trans ((congrArg e hrirj).trans hrj)

/-- The local five-index classification.  Five ordered indices placed in
four consecutive alternating blocks have an adjacent pair in one block.
The plane through the other three indices has one strict sign on that pair;
its zero face is an affinely independent face of an ordered quadruple. -/
private theorem five_ordered_alternatingBlock_hulls_disjoint
    {I : Type*} [LinearOrder I] {x : I → Point 3} {S : Finset I}
    {a b c i₀ i₁ i₂ i₃ i₄ : I}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S)
    (hinj : Set.InjOn x (S : Set I))
    (hi₀ : i₀ ∈ S) (hi₁ : i₁ ∈ S) (hi₂ : i₂ ∈ S)
    (hi₃ : i₃ ∈ S) (hi₄ : i₄ ∈ S)
    (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (h₂₃ : i₂ < i₃) (h₃₄ : i₃ < i₄) :
    let U : Finset I := {i₀, i₁, i₂, i₃, i₄}
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock U a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock U a b c).image x : Set (Point 3))) := by
  classical
  dsimp only
  let U : Finset I := {i₀, i₁, i₂, i₃, i₄}
  let P := firstAlternatingBlock U a b c
  let Q := secondAlternatingBlock U a b c
  let A := P.image x
  let B := Q.image x
  have hiU : ∀ r ∈ U, r ∈ S := by
    intro r hr
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro r hrP hrQ
    simp only [P, Q, firstAlternatingBlock, secondAlternatingBlock,
      Finset.mem_filter] at hrP hrQ
    grind
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    obtain ⟨r, hrP, rfl⟩ := Finset.mem_image.1 hyA
    obtain ⟨s, hsQ, hrs⟩ := Finset.mem_image.1 hyB
    have hrU : r ∈ U := by
      exact (Finset.mem_filter.1 hrP).1
    have hsU : s ∈ U := by
      exact (Finset.mem_filter.1 hsQ).1
    have hrs' : r = s := hinj (hiU r hrU) (hiU s hsU) hrs.symm
    subst s
    exact Finset.disjoint_left.1 hPQ hrP hsQ
  have hAcov : A ⊆ {x i₀, x i₁, x i₂, x i₃, x i₄} := by
    intro y hy
    obtain ⟨r, hrP, rfl⟩ := Finset.mem_image.1 hy
    have hrU : r ∈ U := (Finset.mem_filter.1 hrP).1
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hrU ⊢
    rcases hrU with rfl | rfl | rfl | rfl | rfl <;> simp
  have hBcov : B ⊆ {x i₀, x i₁, x i₂, x i₃, x i₄} := by
    intro y hy
    obtain ⟨r, hrQ, rfl⟩ := Finset.mem_image.1 hy
    have hrU : r ∈ U := (Finset.mem_filter.1 hrQ).1
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hrU ⊢
    rcases hrU with rfl | rfl | rfl | rfl | rfl <;> simp
  have hpair :
      ((i₀ ∈ P ∧ i₁ ∈ P) ∨ (i₀ ∈ Q ∧ i₁ ∈ Q)) ∨
      ((i₁ ∈ P ∧ i₂ ∈ P) ∨ (i₁ ∈ Q ∧ i₂ ∈ Q)) ∨
      ((i₂ ∈ P ∧ i₃ ∈ P) ∨ (i₂ ∈ Q ∧ i₃ ∈ Q)) ∨
      ((i₃ ∈ P ∧ i₄ ∈ P) ∨ (i₃ ∈ Q ∧ i₄ ∈ Q)) := by
    simp only [P, Q, firstAlternatingBlock, secondAlternatingBlock,
      Finset.mem_filter]
    simp only [U, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
      true_and]
    grind
  have hcover_perm (p q r s t : Point 3)
      (heq : ({p, q, r, s, t} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄}) :
      A ⊆ {p, q, r, s, t} ∧ B ⊆ {p, q, r, s, t} := by
    rw [heq]
    exact ⟨hAcov, hBcov⟩
  rcases hpair with hpair | hpair | hpair | hpair
  · let f := alternatingCutAffine (x i₂) (x i₃) (x i₄)
    have hpq : (x i₀ ∈ A ∧ x i₁ ∈ A) ∨ (x i₀ ∈ B ∧ x i₁ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₂) = 0 ∧ f (x i₃) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₀) ∧ 0 < f (x i₁)) ∨
        (f (x i₀) < 0 ∧ f (x i₁) < 0) := by
      rcases huniform with habove | hbelow
      · left
        simpa [f] using ⟨
          cutSign_above_before hchain habove hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄,
          cutSign_above_before hchain habove hi₁ hi₂ hi₃ hi₄
            h₁₂ h₂₃ h₃₄⟩
      · right
        simpa [f] using ⟨
          cutSign_below_before hchain hbelow hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄,
          cutSign_below_before hchain hbelow hi₁ hi₂ hi₃ hi₄
            h₁₂ h₂₃ h₃₄⟩
    have hquad := (hchain i₁ hi₁ i₂ hi₂ i₃ hi₃ i₄ hi₄ h₁₂ h₂₃ h₃₄).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₂, x i₃, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have hcov := hcover_perm (x i₀) (x i₁) (x i₂) (x i₃) (x i₄) rfl
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₃) (x i₄)
    have hpq : (x i₁ ∈ A ∧ x i₂ ∈ A) ∨ (x i₁ ∈ B ∧ x i₂ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₃) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₁) ∧ 0 < f (x i₂)) ∨
        (f (x i₁) < 0 ∧ f (x i₂) < 0) := by
      rcases huniform with habove | hbelow
      · right
        simpa [f] using ⟨
          cutSign_above_between₁ hchain habove hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄,
          cutSign_above_between₁ hchain habove hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄⟩
      · left
        simpa [f] using ⟨
          cutSign_below_between₁ hchain hbelow hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄,
          cutSign_below_between₁ hchain hbelow hi₀ hi₂ hi₃ hi₄
            (h₀₁.trans h₁₂) h₂₃ h₃₄⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₃ hi₃ i₄ hi₄ h₀₁
      (h₁₂.trans h₂₃) h₃₄).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₃, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₁, x i₂, x i₀, x i₃, x i₄} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₁) (x i₂) (x i₀) (x i₃) (x i₄) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₁) (x i₄)
    have hpq : (x i₂ ∈ A ∧ x i₃ ∈ A) ∨ (x i₂ ∈ B ∧ x i₃ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₁) = 0 ∧ f (x i₄) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₂) ∧ 0 < f (x i₃)) ∨
        (f (x i₂) < 0 ∧ f (x i₃) < 0) := by
      rcases huniform with habove | hbelow
      · left
        simpa [f] using ⟨
          cutSign_above_between₂ hchain habove hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄),
          cutSign_above_between₂ hchain habove hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄⟩
      · right
        simpa [f] using ⟨
          cutSign_below_between₂ hchain hbelow hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄),
          cutSign_below_between₂ hchain hbelow hi₀ hi₁ hi₃ hi₄ h₀₁
            (h₁₂.trans h₂₃) h₃₄⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₂ hi₂ i₄ hi₄ h₀₁ h₁₂
      (h₂₃.trans h₃₄)).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₁, x i₄} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₂, x i₃, x i₀, x i₁, x i₄} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₂) (x i₃) (x i₀) (x i₁) (x i₄) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI
  · let f := alternatingCutAffine (x i₀) (x i₁) (x i₂)
    have hpq : (x i₃ ∈ A ∧ x i₄ ∈ A) ∨ (x i₃ ∈ B ∧ x i₄ ∈ B) := by
      rcases hpair with h | h
      · exact Or.inl ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
      · exact Or.inr ⟨Finset.mem_image_of_mem x h.1, Finset.mem_image_of_mem x h.2⟩
    have hroot : f (x i₀) = 0 ∧ f (x i₁) = 0 ∧ f (x i₂) = 0 := by
      simp [f]
    have hsign : (0 < f (x i₃) ∧ 0 < f (x i₄)) ∨
        (f (x i₃) < 0 ∧ f (x i₄) < 0) := by
      rcases huniform with habove | hbelow
      · right
        simpa [f] using ⟨
          cutSign_above_after hchain habove hi₀ hi₁ hi₂ hi₃ h₀₁ h₁₂ h₂₃,
          cutSign_above_after hchain habove hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄)⟩
      · left
        simpa [f] using ⟨
          cutSign_below_after hchain hbelow hi₀ hi₁ hi₂ hi₃ h₀₁ h₁₂ h₂₃,
          cutSign_below_after hchain hbelow hi₀ hi₁ hi₂ hi₄ h₀₁ h₁₂
            (h₂₃.trans h₃₄)⟩
    have hquad := (hchain i₀ hi₀ i₁ hi₁ i₂ hi₂ i₃ hi₃ h₀₁ h₁₂ h₂₃).1
    have hrootAI : AffineIndependent ℝ
        (fun z : ↥({x i₀, x i₁, x i₂} : Finset (Point 3)) ↦ (z : Point 3)) :=
      affineIndependent_finset_of_subset_quad hquad (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl | rfl <;> simp)
    have heq : ({x i₃, x i₄, x i₀, x i₁, x i₂} : Finset (Point 3)) =
        {x i₀, x i₁, x i₂, x i₃, x i₄} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor <;> rintro (rfl | rfl | rfl | rfl | rfl) <;> simp
    have hcov := hcover_perm (x i₃) (x i₄) (x i₀) (x i₁) (x i₂) heq
    exact five_point_partition_disjoint_of_adjacent_pair A B f hAB hcov.1 hcov.2
      hpq hroot hsign hrootAI

/-- In dimension three, it is enough to rule out intersecting convex hulls
on subconfigurations using at most five points in total.  This is the exact
finite form of the Kirchberger reduction used in the alternating-block step. -/
theorem finite_hulls_disjoint_of_five_point_witnesses
    (A B : Finset (Point 3))
    (hsmall : ∀ A' B' : Finset (Point 3), A' ⊆ A → B' ⊆ B →
      A'.card + B'.card ≤ 5 →
        Disjoint (convexHull ℝ (A' : Set (Point 3)))
          (convexHull ℝ (B' : Set (Point 3)))) :
    Disjoint (convexHull ℝ (A : Set (Point 3)))
      (convexHull ℝ (B : Set (Point 3))) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  obtain ⟨A', B', hA'A, hB'B, hcard, hinter⟩ :=
    finite_kirchberger_point3 A B ⟨z, hzA, hzB⟩
  obtain ⟨z', hz'A, hz'B⟩ := hinter
  exact Set.disjoint_left.1 (hsmall A' B' hA'A hB'B hcard) hz'A hz'B

/-- Alternating-block hull separation, reduced to the only local witnesses
which can occur in `R^3`.  The above--below sign condition is used downstream
to discharge `hsmall` by its four- and five-point circuit analysis. -/
theorem alternatingBlock_hulls_disjoint_of_five_point_witnesses
    {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I) (a b c : I)
    (hsmall : ∀ A' B' : Finset (Point 3),
      A' ⊆ (firstAlternatingBlock S a b c).image x →
      B' ⊆ (secondAlternatingBlock S a b c).image x →
      A'.card + B'.card ≤ 5 →
        Disjoint (convexHull ℝ (A' : Set (Point 3)))
          (convexHull ℝ (B' : Set (Point 3)))) :
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock S a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock S a b c).image x : Set (Point 3))) :=
  finite_hulls_disjoint_of_five_point_witnesses _ _ hsmall

/-- **Pohoata--Zakharov, Corollary 2.4 (alternating-block form).**
For a five-point-or-longer projected convex chain with one uniform
above/below color, the hulls of the first-and-third and second-and-fourth
blocks are disjoint for every weakly ordered triple of cuts.

The proof applies Kirchberger in `R³`, pulls a witness of size at most five
back to chain indices, and extends it to exactly five indices.  Of the four
consecutive block colors, some color is repeated on adjacent witness
indices.  The four cases are precisely the green circuit types; the cut
plane through the other three indices excludes each of them. -/
theorem alternatingBlock_hulls_disjoint
    {I : Type*} [LinearOrder I] (x : I → Point 3) (S : Finset I) (a b c : I)
    (hcard : 5 ≤ S.card) (hab : a ≤ b) (hbc : b ≤ c)
    (hchain : IsProjectedConvexChain x S) (huniform : UniformAboveBelowOn x S) :
    Disjoint
      (convexHull ℝ ((firstAlternatingBlock S a b c).image x : Set (Point 3)))
      (convexHull ℝ ((secondAlternatingBlock S a b c).image x : Set (Point 3))) := by
  classical
  have hinj : Set.InjOn x (S : Set I) := hchain.injOn (by omega)
  apply alternatingBlock_hulls_disjoint_of_five_point_witnesses x S a b c
  intro A' B' hA' hB' hwcard
  let IA := (firstAlternatingBlock S a b c).filter fun i => x i ∈ A'
  let IB := (secondAlternatingBlock S a b c).filter fun i => x i ∈ B'
  have hIAimage : IA.image x = A' := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hi).2
    · intro hp
      have hpbig := hA' hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hpbig
      exact Finset.mem_image_of_mem x (Finset.mem_filter.2 ⟨hi, hp⟩)
  have hIBimage : IB.image x = B' := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hi).2
    · intro hp
      have hpbig := hB' hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hpbig
      exact Finset.mem_image_of_mem x (Finset.mem_filter.2 ⟨hi, hp⟩)
  have hIAS : IA ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
  have hIBS : IB ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1
  have hIAcard : IA.card = A'.card := by
    rw [← hIAimage]
    exact (Finset.card_image_of_injOn (hinj.mono hIAS)).symm
  have hIBcard : IB.card = B'.card := by
    rw [← hIBimage]
    exact (Finset.card_image_of_injOn (hinj.mono hIBS)).symm
  have hIAIB : Disjoint IA IB := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hiA' := Finset.mem_filter.1 (Finset.mem_filter.1 hiA).1
    have hiB' := Finset.mem_filter.1 (Finset.mem_filter.1 hiB).1
    grind
  have hunionS : IA ∪ IB ⊆ S := Finset.union_subset hIAS hIBS
  have hunioncard : (IA ∪ IB).card ≤ 5 := by
    rw [Finset.card_union_of_disjoint hIAIB, hIAcard, hIBcard]
    exact hwcard
  obtain ⟨U, hsubU, hUS, hUcard⟩ :=
    Finset.exists_subsuperset_card_eq hunionS hunioncard hcard
  let e : Fin 5 ↪o I := U.orderEmbOfFin hUcard
  have heU (r : Fin 5) : e r ∈ U := U.orderEmbOfFin_mem hUcard r
  have heS (r : Fin 5) : e r ∈ S := hUS (heU r)
  have he₀₁ : e 0 < e 1 := e.strictMono (by omega)
  have he₁₂ : e 1 < e 2 := e.strictMono (by omega)
  have he₂₃ : e 2 < e 3 := e.strictMono (by omega)
  have he₃₄ : e 3 < e 4 := e.strictMono (by omega)
  have hfive := five_ordered_alternatingBlock_hulls_disjoint hab hbc hchain huniform hinj
    (heS 0) (heS 1) (heS 2) (heS 3) (heS 4) he₀₁ he₁₂ he₂₃ he₃₄
  have hUeq : ({e 0, e 1, e 2, e 3, e 4} : Finset I) = U := by
    ext i
    constructor
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl | rfl | rfl | rfl) <;> exact heU _
    · intro hi
      have hirange : i ∈ Set.range e := by
        have hrange : Set.range e = (U : Set I) := by
          simpa only [e] using U.range_orderEmbOfFin hUcard
        rw [hrange]
        exact hi
      obtain ⟨r, rfl⟩ := hirange
      fin_cases r <;> simp
  rw [hUeq] at hfive
  have hIAU : IA ⊆ firstAlternatingBlock U a b c := by
    intro i hi
    have hiData := Finset.mem_filter.1 hi
    have hiBlock := Finset.mem_filter.1 hiData.1
    exact Finset.mem_filter.2 ⟨hsubU (Finset.mem_union_left IB hi), hiBlock.2⟩
  have hIBU : IB ⊆ secondAlternatingBlock U a b c := by
    intro i hi
    have hiData := Finset.mem_filter.1 hi
    have hiBlock := Finset.mem_filter.1 hiData.1
    exact Finset.mem_filter.2 ⟨hsubU (Finset.mem_union_right IA hi), hiBlock.2⟩
  have hA'sub : A' ⊆ (firstAlternatingBlock U a b c).image x := by
    rw [← hIAimage]
    exact Finset.image_mono x hIAU
  have hB'sub : B' ⊆ (secondAlternatingBlock U a b c).image x := by
    rw [← hIBimage]
    exact Finset.image_mono x hIBU
  exact hfive.mono (convexHull_mono (by exact hA'sub))
    (convexHull_mono (by exact hB'sub))

end

end Erdos651
