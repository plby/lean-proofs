import Wikipedia.HopfProblem.OrbitPairPushoutProductHomotopyExtension

/-!
# Neighborhood deformation data for the two endpoints of the unit interval

The height is the clipped fourfold distance to the nearer endpoint.
The final map is the clipped affine function `2t - 1/2`. Their linear
interpolation fixes both endpoints and sends the height sublevel at one
to the endpoint set. These are the actual interval and its actual
two-endpoint inclusion.
-/

noncomputable section

open CategoryTheory unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.IntervalBoundary

def endpoints : Set I := {t | t = 0 ∨ t = 1}

def inclusion : TopCat.of ↥endpoints ⟶ TopCat.of I :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def height : C(I, I) :=
  ⟨fun t ↦ Set.projIcc 0 1 zero_le_one (4 * min (t : ℝ) (1 - (t : ℝ))),
    continuous_projIcc.comp (continuous_const.mul
      (continuous_subtype_val.min (continuous_const.sub continuous_subtype_val)))⟩

def endpoint : C(I, I) :=
  ⟨fun t ↦ Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1 / 2),
    continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)⟩

theorem endpoint_zero : endpoint 0 = 0 := by
  apply _root_.projIcc_eq_zero.mpr
  norm_num

theorem endpoint_one : endpoint 1 = 1 := by
  apply _root_.projIcc_eq_one.mpr
  norm_num

theorem height_zero_iff (t : I) : height t = 0 ↔ t ∈ endpoints := by
  change Set.projIcc 0 1 zero_le_one (4 * min (t : ℝ) (1 - (t : ℝ))) = 0 ↔ t = 0 ∨ t = 1
  rw [_root_.projIcc_eq_zero]
  constructor
  · intro h
    by_cases ht : (t : ℝ) ≤ 1 - (t : ℝ)
    · rw [min_eq_left ht] at h
      left
      apply Subtype.ext
      change (t : ℝ) = (0 : ℝ)
      have h0 := t.property.1
      linarith
    · rw [min_eq_right (not_le.mp ht).le] at h
      right
      apply Subtype.ext
      change (t : ℝ) = (1 : ℝ)
      have h1 := t.property.2
      linarith
  · rintro (rfl | rfl) <;> norm_num

theorem endpoint_mem_of_height_lt_one (t : I) (ht : height t < 1) : endpoint t ∈ endpoints := by
  have hn : height t ≠ 1 := ne_of_lt ht
  have hd : 4 * min (t : ℝ) (1 - (t : ℝ)) < 1 := by
    apply lt_of_not_ge
    intro h
    exact hn (_root_.projIcc_eq_one.mpr h)
  by_cases h : (t : ℝ) ≤ 1 - (t : ℝ)
  · rw [min_eq_left h] at hd
    left
    apply _root_.projIcc_eq_zero.mpr
    linarith
  · rw [min_eq_right (not_le.mp h).le] at hd
    right
    apply _root_.projIcc_eq_one.mpr
    linarith

def deformation : C(I × I, I) :=
  ⟨fun p ↦ Set.Icc.convexComb p.2 (endpoint p.2) p.1,
    Set.Icc.continuous_convexComb_prod.comp
      (continuous_snd.prodMk ((endpoint.continuous.comp continuous_snd).prodMk continuous_fst))⟩

def data : NeighborhoodDeformation.Data inclusion where
  height := height
  deformation := deformation
  zero_iff t := (height_zero_iff t).trans
    ⟨fun h ↦ ⟨⟨t, h⟩, rfl⟩, fun ⟨q, hq⟩ ↦ hq ▸ q.property⟩
  bottom t := Set.Icc.convexComb_zero t (endpoint t)
  fixed s q := by
    change Set.Icc.convexComb q.val (endpoint q.val) s = q.val
    rcases q.property with h | h
    · rw [h, endpoint_zero, Set.Icc.convexComb_eq]
    · rw [h, endpoint_one, Set.Icc.convexComb_eq]
  terminal t ht := ⟨⟨endpoint t, endpoint_mem_of_height_lt_one t ht⟩,
    (Set.Icc.convexComb_one t (endpoint t)).symm⟩

theorem inclusion_hasHomotopyExtension : HomotopyExtension.HasHomotopyExtension inclusion :=
  NeighborhoodDeformation.hasHomotopyExtension data IsEmbedding.subtypeVal

theorem inclusion_isClosedEmbedding : IsClosedEmbedding inclusion :=
  ⟨IsEmbedding.subtypeVal, NeighborhoodDeformation.range_isClosed data⟩

end Wikipedia.HopfProblem.OrbitPair.IntervalBoundary
