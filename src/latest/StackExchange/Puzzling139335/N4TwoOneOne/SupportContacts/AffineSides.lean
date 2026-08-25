import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.Admissible
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Pulling actual square-side contacts back through an affine isometry
-/

open Set

namespace Puzzling139335.N4TwoOneOne.SupportContacts

noncomputable section

def sideSign (upper : Bool) : ℝ := if upper then 1 else -1

def sideLevel (upper : Bool) : ℝ := if upper then 1 else 0

/-- Two distinct actual points on the selected square-side line. -/
def HasTwoSidePoints (D : Set Plane) (i : Fin 2) (upper : Bool) : Prop :=
  ∃ p ∈ D, ∃ q ∈ D, p ≠ q ∧ p i = sideLevel upper ∧ q i = sideLevel upper

def sideNormalX (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2) (upper : Bool) : ℝ :=
  sideSign upper * PlaneIsometries.linearMatrix e i 0

def sideNormalY (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2) (upper : Bool) : ℝ :=
  sideSign upper * PlaneIsometries.linearMatrix e i 1

theorem sideSign_ne_zero (upper : Bool) : sideSign upper ≠ 0 := by
  cases upper <;> norm_num [sideSign]

theorem unitSquare_coordinate {p : Plane} (hp : p ∈ unitSquare) (i : Fin 2) :
    0 ≤ p i ∧ p i ≤ 1 := by
  fin_cases i
  · exact hp.1
  · exact hp.2

theorem affine_coordinate (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) (i : Fin 2) :
    e p i = PlaneIsometries.linearMatrix e i 0 * p 0 +
      PlaneIsometries.linearMatrix e i 1 * p 1 + e 0 i := by
  have h := congrArg (fun q : Plane => q i)
    (PlaneIsometries.affine_apply_eq_matrix_coordinates e p)
  fin_cases i <;> simpa using h

theorem sideNormal_value (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane)
    (i : Fin 2) (upper : Bool) :
    sideNormalX e i upper * p 0 + sideNormalY e i upper * p 1 =
      sideSign upper * (e p i - e 0 i) := by
  rw [affine_coordinate]
  simp only [sideNormalX, sideNormalY]
  ring

theorem sideNormal_unit (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2) (upper : Bool) :
    sideNormalX e i upper ^ 2 + sideNormalY e i upper ^ 2 = 1 := by
  have hrow := PlaneIsometries.linearMatrix_row_dot e i i
  simp at hrow
  cases upper <;> simp only [sideNormalX, sideNormalY, sideSign, Bool.false_eq_true,
    if_false, if_true, one_mul, neg_one_mul, neg_sq] <;> nlinarith only [hrow]

theorem sideNormal_nonzero (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2) (upper : Bool) :
    sideNormalX e i upper ≠ 0 ∨ sideNormalY e i upper ≠ 0 := by
  by_contra hn
  push Not at hn
  have hunit := sideNormal_unit e i upper
  rw [hn.1, hn.2] at hunit
  norm_num at hunit

theorem sideNormals_orthogonal (e : Plane ≃ᵃⁱ[ℝ] Plane) {i j : Fin 2}
    (hij : i ≠ j) (upper other : Bool) :
    sideNormalX e i upper * sideNormalX e j other +
      sideNormalY e i upper * sideNormalY e j other = 0 := by
  have hrow := PlaneIsometries.linearMatrix_row_dot e i j
  rw [if_neg hij] at hrow
  calc
    _ = sideSign upper * sideSign other *
        (PlaneIsometries.linearMatrix e i 0 * PlaneIsometries.linearMatrix e j 0 +
          PlaneIsometries.linearMatrix e i 1 * PlaneIsometries.linearMatrix e j 1) := by
      simp only [sideNormalX, sideNormalY]
      ring
    _ = 0 := by rw [hrow, mul_zero]

/-- The actual preimage of a side point is a supporting point in the pulled
back outward normal direction. -/
theorem supportsAt_of_image_side_point {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hfit : e '' P ⊆ unitSquare) {p : Plane} (hp : p ∈ P)
    {i : Fin 2} {upper : Bool} (hside : e p i = sideLevel upper) :
    SupportsAt P (sideNormalX e i upper) (sideNormalY e i upper) p := by
  refine ⟨hp, ?_⟩
  intro q hq
  rw [sideNormal_value, sideNormal_value]
  have hcoord := unitSquare_coordinate (hfit ⟨q, hq, rfl⟩) i
  cases upper <;> simp only [sideSign, sideLevel, Bool.false_eq_true, if_false,
    if_true, one_mul, neg_one_mul] at hside ⊢ <;>
    linarith only [hcoord.1, hcoord.2, hside]

theorem hasTwoSupportPoints_of_hasTwoSidePoints {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare)
    {i : Fin 2} {upper : Bool} (hside : HasTwoSidePoints (e '' P) i upper) :
    HasTwoSupportPoints P (sideNormalX e i upper) (sideNormalY e i upper) := by
  obtain ⟨x, ⟨p, hp, rfl⟩, y, ⟨q, hq, rfl⟩, hpq, hpi, hqi⟩ := hside
  refine ⟨p, q, ?_, supportsAt_of_image_side_point e hfit hp hpi,
    supportsAt_of_image_side_point e hfit hq hqi⟩
  exact fun heq => hpq (congrArg e heq)

/-- Every source maximizer in a contacted side's pulled-back normal maps to
that side. -/
theorem image_on_side_of_support {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hfit : e '' P ⊆ unitSquare) {i : Fin 2} {upper : Bool}
    (hside : HasTwoSidePoints (e '' P) i upper) {p : Plane}
    (hp : SupportsAt P (sideNormalX e i upper) (sideNormalY e i upper) p) :
    e p i = sideLevel upper := by
  obtain ⟨x, ⟨q, hq, rfl⟩, y, hy, hxy, hqi, hyi⟩ := hside
  have hqSupport := supportsAt_of_image_side_point e hfit hq hqi
  have hval : sideNormalX e i upper * q 0 + sideNormalY e i upper * q 1 =
      sideNormalX e i upper * p 0 + sideNormalY e i upper * p 1 :=
    le_antisymm (hp.2 q hq) (hqSupport.2 p hp.1)
  rw [sideNormal_value, sideNormal_value] at hval
  have hsub := mul_left_cancel₀ (sideSign_ne_zero upper) hval
  linarith only [hsub, hqi]

theorem exists_corner_of_extremal_coordinates {p : Plane}
    (hzero : p 0 = 0 ∨ p 0 = 1) (hone : p 1 = 0 ∨ p 1 = 1) :
    ∃ j : Fin 4, p = corner j := by
  rcases hzero with hzero | hzero <;> rcases hone with hone | hone
  · refine ⟨0, ?_⟩
    apply PlaneIsometries.plane_ext <;> simp [corner, hzero, hone]
  · refine ⟨3, ?_⟩
    apply PlaneIsometries.plane_ext <;> simp [corner, hzero, hone]
  · refine ⟨1, ?_⟩
    apply PlaneIsometries.plane_ext <;> simp [corner, hzero, hone]
  · refine ⟨2, ?_⟩
    apply PlaneIsometries.plane_ext <;> simp [corner, hzero, hone]

theorem exists_corner_of_two_side_coordinates {p : Plane} {i j : Fin 2}
    (hij : i ≠ j) {upper other : Bool}
    (hi : p i = sideLevel upper) (hj : p j = sideLevel other) :
    ∃ k : Fin 4, p = corner k := by
  have hie : p i = 0 ∨ p i = 1 := by cases upper <;> simp_all [sideLevel]
  have hje : p j = 0 ∨ p j = 1 := by cases other <;> simp_all [sideLevel]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact exists_corner_of_extremal_coordinates hie hje
  · exact exists_corner_of_extremal_coordinates hje hie
  · exact (hij rfl).elim

end

end Puzzling139335.N4TwoOneOne.SupportContacts
