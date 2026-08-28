import Wikipedia.NoExoticSixSphere.SphereCylinderPoles
import Wikipedia.NoExoticSixSphere.GLOrthonormalization

/-!
# Flattening an equatorial belt of the original three-sphere

A normalized head-coordinate deformation is homotopic to the identity.
Its endpoint sends a whole open belt to the equator, so a closed-hemisphere
cut-and-paste can be compared on an actual open cover. Both poles are kept.
-/

noncomputable section

open Set Function Metric Topology

namespace NoExoticSixSphere.SphereEquatorialFlattening

open GLOrthonormalization SphereCylinder

def scalar (h : ℝ) : ℝ := max (h - 1 / 2) 0 + min (h + 1 / 2) 0

theorem continuous_scalar : Continuous scalar :=
  ((continuous_id.sub continuous_const).max continuous_const).add
    ((continuous_id.add continuous_const).min continuous_const)

theorem scalar_one : scalar 1 = 1 / 2 := by norm_num [scalar]

theorem scalar_neg_one : scalar (-1) = -(1 / 2) := by norm_num [scalar]

def blend (t : unitInterval) (h : ℝ) : ℝ := (1 - (t : ℝ)) * h + (t : ℝ) * scalar h

def vector (t : unitInterval) (x : Sphere 3) : Vector 4 :=
  join 2 (blend t (x.val 0), tail 2 x.val)

theorem vector_ne_zero (t : unitInterval) (x : Sphere 3) : vector t x ≠ 0 := by
  intro hz
  have ht : tail 2 x.val = 0 := by
    have h := congrArg (tail 2) hz
    simpa only [vector, tail_join, map_zero] using h
  have hp : x ∉ band 2 := fun h ↦ h ht
  have hh : blend t (x.val 0) = 0 := congrArg (fun v : Vector 4 ↦ v 0) hz
  rcases (not_mem_band_iff 2 x).mp hp with rfl | rfl
  · simp only [endPole_head, Bool.false_eq_true, ↓reduceIte, blend, scalar_neg_one] at hh
    nlinarith [t.property.1, t.property.2]
  · simp only [endPole_head, ↓reduceIte, blend, scalar_one] at hh
    nlinarith [t.property.1, t.property.2]

def point (t : unitInterval) (x : Sphere 3) : Sphere 3 :=
  ⟨NormedSpace.normalize (vector t x), by
    simpa only [mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (vector_ne_zero t x)⟩

theorem continuous_vector : Continuous (fun p : unitInterval × Sphere 3 ↦ vector p.1 p.2) := by
  have ht : Continuous (fun p : unitInterval × Sphere 3 ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hh : Continuous (fun p : unitInterval × Sphere 3 ↦ p.2.val 0) :=
    (((join 2).symm.continuous.comp continuous_subtype_val).fst).comp continuous_snd
  have hs := continuous_scalar.comp hh
  exact (join 2).continuous.comp
    ((((continuous_const.sub ht).mul hh).add (ht.mul hs)).prodMk
      ((tail 2).continuous.comp (continuous_subtype_val.comp continuous_snd)))

theorem continuous_point : Continuous (fun p : unitInterval × Sphere 3 ↦ point p.1 p.2) := by
  have hn : Continuous (fun p : unitInterval × Sphere 3 ↦ ‖vector p.1 p.2‖⁻¹) :=
    continuous_vector.norm.inv₀ (fun p ↦ norm_ne_zero_iff.mpr (vector_ne_zero p.1 p.2))
  exact (hn.smul continuous_vector).subtype_mk _

theorem point_zero (x : Sphere 3) : point 0 x = x := by
  apply Subtype.ext
  have hv : vector 0 x = x.val := by
    change join 2 ((1 - (0 : ℝ)) * x.val 0 + 0 * scalar (x.val 0), tail 2 x.val) = x.val
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact (join 2).apply_symm_apply x.val
  change NormedSpace.normalize (vector 0 x) = x.val
  rw [hv]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm x)

def map : C(Sphere 3, Sphere 3) :=
  (⟨fun p : unitInterval × Sphere 3 ↦ point p.1 p.2, continuous_point⟩ :
    C(unitInterval × Sphere 3, Sphere 3)).comp
      ⟨fun x ↦ ((1 : unitInterval), x), continuous_const.prodMk continuous_id⟩

def homotopy : (ContinuousMap.id (Sphere 3)).Homotopy map where
  toFun p := point p.1 p.2
  continuous_toFun := continuous_point
  map_zero_left := point_zero
  map_one_left _ := rfl

theorem map_head (x : Sphere 3) : (map x).val 0 = ‖vector 1 x‖⁻¹ * scalar (x.val 0) := by
  change ‖vector 1 x‖⁻¹ * blend 1 (x.val 0) = _
  simp [blend]

def northOpen : Set (Sphere 3) := {x | -(1 / 2 : ℝ) < x.val 0}

def southOpen : Set (Sphere 3) := {x | x.val 0 < (1 / 2 : ℝ)}

theorem isOpen_north : IsOpen northOpen :=
  isOpen_lt continuous_const (((join 2).symm.continuous.comp continuous_subtype_val).fst)

theorem isOpen_south : IsOpen southOpen :=
  isOpen_lt (((join 2).symm.continuous.comp continuous_subtype_val).fst) continuous_const

theorem open_cover : northOpen ∪ southOpen = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true]
  change -(1 / 2 : ℝ) < x.val 0 ∨ x.val 0 < (1 / 2 : ℝ)
  by_cases h : -(1 / 2 : ℝ) < x.val 0
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem map_head_nonneg {x : Sphere 3} (hx : x ∈ northOpen) : 0 ≤ (map x).val 0 := by
  rw [map_head]
  apply mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
  have hp : 0 ≤ x.val 0 + (1 / 2 : ℝ) := by change -(1 / 2 : ℝ) < x.val 0 at hx; linarith
  simp only [scalar, min_eq_right hp, add_zero]
  exact le_max_right _ _

theorem map_head_nonpos {x : Sphere 3} (hx : x ∈ southOpen) : (map x).val 0 ≤ 0 := by
  rw [map_head]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
  have hn : x.val 0 - (1 / 2 : ℝ) ≤ 0 := by change x.val 0 < (1 / 2 : ℝ) at hx; linarith
  simp only [scalar, max_eq_right hn, zero_add]
  exact min_le_right _ _

end NoExoticSixSphere.SphereEquatorialFlattening
