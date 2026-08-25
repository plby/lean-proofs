import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.Direction
import Mathlib.Topology.Homotopy.Basic

/-!
# Transfer of angular contractions to the punctured plane

Polar reconstruction is continuous for positive radii.  Combining an angular
contraction with linear interpolation of the positive radial coordinate gives
a contraction in the punctured plane.  For a loop, both parameter endpoints
remain fixed throughout this construction.
-/

noncomputable section

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.RadialTransfer

open PlaneIsometries

/-- A path avoiding `x`, regarded as a path in the punctured plane. -/
def puncturedPath (x : Plane) (γ : C(I, Plane)) (hx : ∀ t, γ t ≠ x) :
    C(I, ({x}ᶜ : Set Plane)) where
  toFun t := ⟨γ t, by simpa only [mem_compl_iff, mem_singleton_iff] using hx t⟩
  continuous_toFun := γ.continuous.subtype_mk _

@[simp] theorem puncturedPath_coe (x : Plane) (γ : C(I, Plane))
    (hx : ∀ t, γ t ≠ x) (t : I) : (puncturedPath x γ hx t : Plane) = γ t := rfl

/-- Continuous reconstruction from a positive radius and angular coordinate. -/
def reconstruct (x : Plane) :
    C(Ioi (0 : ℝ) × AddCircle (1 : ℝ), ({x}ᶜ : Set Plane)) where
  toFun p := ⟨x + complexEquiv.symm
    ((p.1.val : ℂ) * ((AddCircle.homeomorphCircle one_ne_zero) p.2 : ℂ)), by
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    have hz := congrArg complexEquiv he
    rw [map_add, complexEquiv.apply_symm_apply, add_eq_left] at hz
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.property))
      (Circle.coe_ne_zero _)) hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.add
    apply complexEquiv.symm.continuous.comp
    exact (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          ((AddCircle.homeomorphCircle one_ne_zero).continuous.comp continuous_snd))

/-- The radial coordinate around `x` is positive on its punctured plane. -/
def radius (x : Plane) (p : ({x}ᶜ : Set Plane)) : Ioi (0 : ℝ) :=
  ⟨‖complexEquiv ((p : Plane) - x)‖, norm_pos_iff.mpr (by
    exact (map_ne_zero_iff complexEquiv complexEquiv.injective).mpr
      (sub_ne_zero.mpr (by
        simpa only [mem_compl_iff, mem_singleton_iff] using p.property)))⟩

/-- Polar reconstruction recovers the original point. -/
theorem reconstruct_direction (x : Plane) (p : ({x}ᶜ : Set Plane)) :
    reconstruct x (radius x p, directionFrom x p) = p := by
  apply Subtype.ext
  change x + complexEquiv.symm
    ((‖complexEquiv ((p : Plane) - x)‖ : ℂ) *
      ((AddCircle.homeomorphCircle one_ne_zero) (directionFrom x p) : ℂ)) = p
  have hangle :
      ((AddCircle.homeomorphCircle one_ne_zero) (directionFrom x p) : ℂ) =
        complexEquiv ((p : Plane) - x) / (‖complexEquiv ((p : Plane) - x)‖ : ℂ) := by
    simp only [directionFrom, directionDifference, ContinuousMap.coe_mk,
      circleAngle, Homeomorph.apply_symm_apply]
    rfl
  rw [hangle]
  have hr : (‖complexEquiv ((p : Plane) - x)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (radius x p).property)
  rw [mul_div_cancel₀ _ hr, complexEquiv.symm_apply_apply]
  abel

private theorem interpolation_pos (s : I) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - (s : ℝ)) * a + (s : ℝ) * b := by
  by_cases hs : (s : ℝ) < 1
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hs) ha) (mul_nonneg s.property.1 hb.le)
  · have he : (s : ℝ) = 1 := le_antisymm s.property.2 (le_of_not_gt hs)
    simpa only [he, sub_self, zero_mul, one_mul, zero_add] using hb

/-- Linear interpolation contracts the radial coordinate to its initial value. -/
def radialHomotopy (x : Plane) (γ : C(I, Plane)) (hx : ∀ t, γ t ≠ x) :
    C(I × I, Ioi (0 : ℝ)) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (radius x (puncturedPath x γ hx p.2)).val +
    (p.1 : ℝ) * (radius x (puncturedPath x γ hx 0)).val,
    interpolation_pos p.1 (radius x (puncturedPath x γ hx p.2)).property
      (radius x (puncturedPath x γ hx 0)).property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (complexEquiv.continuous.comp
        ((γ.continuous.comp continuous_snd).sub continuous_const)).norm).add
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

@[simp] theorem radialHomotopy_zero (x : Plane) (γ : C(I, Plane))
    (hx : ∀ t, γ t ≠ x) (t : I) :
    radialHomotopy x γ hx (0, t) = radius x (puncturedPath x γ hx t) := by
  apply Subtype.ext
  simp [radialHomotopy]

@[simp] theorem radialHomotopy_one (x : Plane) (γ : C(I, Plane))
    (hx : ∀ t, γ t ≠ x) (t : I) :
    radialHomotopy x γ hx (1, t) = radius x (puncturedPath x γ hx 0) := by
  apply Subtype.ext
  simp [radialHomotopy]

theorem radialHomotopy_endpoint (x : Plane) (γ : C(I, Plane))
    (hx : ∀ t, γ t ≠ x) (hclosed : γ 1 = γ 0) (s t : I) (ht : t ∈ ({0, 1} : Set I)) :
    radialHomotopy x γ hx (s, t) = radius x (puncturedPath x γ hx t) := by
  have hbase : (puncturedPath x γ hx t : Plane) = γ 0 := by
    rcases (show t = 0 ∨ t = 1 from by simpa only [mem_insert_iff, mem_singleton_iff] using ht)
      with rfl | rfl
    · rfl
    · exact hclosed
  apply Subtype.ext
  change (1 - (s : ℝ)) * ‖complexEquiv (γ t - x)‖ +
    (s : ℝ) * ‖complexEquiv (γ 0 - x)‖ = ‖complexEquiv (γ t - x)‖
  change γ t = γ 0 at hbase
  rw [hbase]
  ring

/-- Lift an angular nullhomotopy by interpolating positive radial coordinates. -/
def puncturedContraction (x : Plane) (γ : C(I, Plane)) (hx : ∀ t, γ t ≠ x)
    (hclosed : γ 1 = γ 0)
    (H : (directionPath γ x hx).HomotopyRel
      (ContinuousMap.const I (directionPath γ x hx 0)) {0, 1}) :
    (puncturedPath x γ hx).HomotopyRel
      (ContinuousMap.const I (puncturedPath x γ hx 0)) {0, 1} where
  toFun p := reconstruct x (radialHomotopy x γ hx p, H p)
  continuous_toFun := (reconstruct x).continuous.comp
    ((radialHomotopy x γ hx).continuous.prodMk H.continuous)
  map_zero_left := by
    intro t
    rw [radialHomotopy_zero, H.apply_zero]
    exact reconstruct_direction x (puncturedPath x γ hx t)
  map_one_left := by
    intro t
    rw [radialHomotopy_one, H.apply_one]
    exact reconstruct_direction x (puncturedPath x γ hx 0)
  prop' := by
    intro s t ht
    change reconstruct x (radialHomotopy x γ hx (s, t), H (s, t)) =
      puncturedPath x γ hx t
    rw [radialHomotopy_endpoint x γ hx hclosed s t ht, H.eq_fst s ht]
    exact reconstruct_direction x (puncturedPath x γ hx t)

/-- Nullhomotopic angular direction implies a loop contracts in the punctured
plane, with its basepoint fixed. -/
theorem direction_null_implies_punctured_null (x : Plane) (γ : C(I, Plane))
    (hx : ∀ t, γ t ≠ x) (hclosed : γ 1 = γ 0)
    (h : (directionPath γ x hx).HomotopicRel
      (ContinuousMap.const I (directionPath γ x hx 0)) {0, 1}) :
    (puncturedPath x γ hx).HomotopicRel
      (ContinuousMap.const I (puncturedPath x γ hx 0)) {0, 1} := by
  rcases h with ⟨H⟩
  exact ⟨puncturedContraction x γ hx hclosed H⟩

end Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.RadialTransfer

end
