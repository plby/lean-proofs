import StackExchange.Puzzling139335.N7Geometry.TripleCornerBounds
import StackExchange.Puzzling139335.N6.TripleSectors.Maps
import StackExchange.Puzzling139335.CornerSupport
import StackExchange.Puzzling139335.CornerSupport.Equality.Coordinates
import StackExchange.Puzzling139335.ThreeCorners.FullBisector

/-!
# Support arms in the opposite-parity triple-corner configuration

Two supporting wedges at the acute source origin and the canonical wedge at
the bottom-right vertex bound the direction of every other supporting right
corner.  The long-arm contradiction is then a pair of support inequalities;
no differentiability or monotonicity statement about the convex hull is used.
-/

open Set

namespace Puzzling139335.N6.TripleOppositeParity.SupportArms

open TripleCornerBounds
open TripleSectors (sqrt_three_pos sqrt_three_sq one_lt_sqrt_three sqrt_three_lt_two)

noncomputable section

theorem triangle_subset_square : triangle ⊆ unitSquare := by
  intro p hp
  rcases hp with ⟨hy, hxy, hx⟩
  have hx0 : 0 ≤ p 0 := (mul_nonneg sqrt_three_pos.le hy).trans hxy
  have hy1 : p 1 ≤ 1 := by
    have hmul := mul_nonneg (sub_nonneg.mpr one_lt_sqrt_three.le) hy
    nlinarith only [hmul, hxy, hx]
  exact ⟨⟨hx0, hx⟩, ⟨hy, hy1⟩⟩

def axisOriginCorner {P : Set Plane} (hP : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) :
    SupportCorner P 0 where
  mem := h0
  firstNormal := !₂[-1, 0]
  secondNormal := !₂[0, -1]
  norm_firstNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by norm_num [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    have hx0 := (triangle_subset_square (hP hx)).1.1
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr hx0
  second_support := by
    intro x hx
    have hy := (hP hx).1
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr hy

def tiltedOriginCorner {P : Set Plane} (hP : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) :
    SupportCorner P 0 where
  mem := h0
  firstNormal := !₂[-Real.sqrt 3 / 2, -1 / 2]
  secondNormal := !₂[-1 / 2, Real.sqrt 3 / 2]
  norm_firstNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    change (-Real.sqrt 3 / 2) ^ 2 + (-1 / 2 : ℝ) ^ 2 = 1 ^ 2
    nlinarith only [sqrt_three_sq]
  norm_secondNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    change (-1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 = 1 ^ 2
    nlinarith only [sqrt_three_sq]
  orthogonal := by simp [Schoenflies.Plane.inner_eq]; ring
  first_support := by
    intro x hx
    have hx0 := (triangle_subset_square (hP hx)).1.1
    have hy := (hP hx).1
    have hprod := mul_nonneg sqrt_three_pos.le hx0
    simp only [Schoenflies.Plane.inner_eq, sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith only [hprod, hy]
  second_support := by
    intro x hx
    have hxy := (hP hx).2.1
    simp only [Schoenflies.Plane.inner_eq, sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith only [hxy]

/-- The acute source origin cannot carry a full right-corner germ. -/
theorem not_full_origin {P : Set Plane} (hP : P ⊆ triangle) :
    ¬ UnitPairs.IsFullSquareCorner P (0 : Plane) := by
  intro hfull
  have hbis := hfull.bisector_eq (axisOriginCorner hP hfull.mem)
    (tiltedOriginCorner hP hfull.mem)
  have hx := congrArg (fun v : Plane => v 0) hbis
  simp only [axisOriginCorner, tiltedOriginCorner, SupportCorner.bisector,
    PiLp.add_apply, Matrix.cons_val_zero] at hx
  nlinarith only [hx, sqrt_three_sq]

def bottomRightCorner {P : Set Plane} (hP : P ⊆ triangle)
    (hB : corner 1 ∈ P) : SupportCorner P (corner 1) :=
  (squareSupportCorner 1).mono (hP.trans triangle_subset_square) hB

def cosine {P : Set Plane} {C : Plane} (h : SupportCorner P C) : ℝ :=
  (h.bisector 0 + h.bisector 1) / 2

def sine {P : Set Plane} {C : Plane} (h : SupportCorner P C) : ℝ :=
  (h.bisector 1 - h.bisector 0) / 2

theorem cosine_sq_add_sine_sq {P : Set Plane} {C : Plane} (h : SupportCorner P C) :
    cosine h ^ 2 + sine h ^ 2 = 1 := by
  have hs : h.bisector 0 ^ 2 + h.bisector 1 ^ 2 = 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using h.bisector_norm_sq
  dsimp [cosine, sine]
  nlinarith only [hs]

/-- Separation from the two source-origin wedges and the bottom-right wedge
places the other corner's directions between zero and thirty degrees. -/
theorem direction_bounds {P : Set Plane} {C : Plane} (hP : P ⊆ triangle)
    (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P) (h : SupportCorner P C)
    (hC0 : C ≠ 0) (hCB : C ≠ corner 1) :
    0 ≤ sine h ∧ Real.sqrt 3 / 2 ≤ cosine h ∧ Real.sqrt 3 * sine h ≤ cosine h := by
  have haxis := (axisOriginCorner hP h0).bisectors_inner_nonpos h (Ne.symm hC0)
  have htilt := (tiltedOriginCorner hP h0).bisectors_inner_nonpos h (Ne.symm hC0)
  have hbase := (bottomRightCorner hP hB).bisectors_inner_nonpos h (Ne.symm hCB)
  simp only [axisOriginCorner, SupportCorner.bisector, Schoenflies.Plane.inner_eq,
    PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, zero_add,
    neg_mul, one_mul] at haxis
  simp only [tiltedOriginCorner, SupportCorner.bisector, Schoenflies.Plane.inner_eq,
    PiLp.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at htilt
  norm_num [bottomRightCorner, SupportCorner.mono, squareSupportCorner,
    SupportCorner.bisector, Schoenflies.Plane.inner_eq, Fin.ext_iff] at hbase
  have hc : 0 ≤ cosine h := by
    simp only [cosine, SupportCorner.bisector, PiLp.add_apply]
    linarith only [haxis]
  have hs : 0 ≤ sine h := by
    simp only [sine, SupportCorner.bisector, PiLp.add_apply]
    linarith only [hbase]
  have hsc : Real.sqrt 3 * sine h ≤ cosine h := by
    simp only [sine, cosine, SupportCorner.bisector, PiLp.add_apply]
    nlinarith only [htilt]
  have hsquares : 3 * sine h ^ 2 ≤ cosine h ^ 2 := by
    calc
      3 * sine h ^ 2 = (Real.sqrt 3 * sine h) ^ 2 := by
        rw [mul_pow, sqrt_three_sq]
      _ ≤ cosine h ^ 2 := (sq_le_sq₀ (mul_nonneg sqrt_three_pos.le hs) hc).mpr hsc
  have hunit := cosine_sq_add_sine_sq h
  have hbound : Real.sqrt 3 / 2 ≤ cosine h := by
    apply (sq_le_sq₀ (by positivity) hc).mp
    nlinarith only [hsquares, hunit, sqrt_three_sq]
  exact ⟨hs, hbound, hsc⟩

private def coordinateSingletonCorner (C : Plane) (c s : ℝ)
    (hunit : c ^ 2 + s ^ 2 = 1) : SupportCorner ({C} : Set Plane) C where
  mem := mem_singleton C
  firstNormal := !₂[-s, c]
  secondNormal := !₂[c, s]
  norm_firstNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [Fin.sum_univ_two, add_comm] using hunit
  norm_secondNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [Fin.sum_univ_two] using hunit
  orthogonal := by simp [Schoenflies.Plane.inner_eq]; ring
  first_support := by intro x hx; rcases hx with rfl; simp
  second_support := by intro x hx; rcases hx with rfl; simp

/-- The bisector determines an explicitly ordered support frame. -/
def coordinateCorner {P : Set Plane} {C : Plane} (h : SupportCorner P C) :
    SupportCorner P C where
  mem := h.mem
  firstNormal := !₂[-sine h, cosine h]
  secondNormal := !₂[cosine h, sine h]
  norm_firstNormal :=
    (coordinateSingletonCorner C (cosine h) (sine h) (cosine_sq_add_sine_sq h)).norm_firstNormal
  norm_secondNormal :=
    (coordinateSingletonCorner C (cosine h) (sine h) (cosine_sq_add_sine_sq h)).norm_secondNormal
  orthogonal :=
    (coordinateSingletonCorner C (cosine h) (sine h) (cosine_sq_add_sine_sq h)).orthogonal
  first_support := by
    intro x hx
    let k := coordinateSingletonCorner C (cosine h) (sine h) (cosine_sq_add_sine_sq h)
    have hsum : h.bisector = k.normalBasis 0 + k.normalBasis 1 := by
      ext i
      fin_cases i <;> simp [k, coordinateSingletonCorner, cosine, sine] <;> ring
    simpa [k, coordinateSingletonCorner] using
      (CornerSupport.Equality.coords_nonpos_of_bisector_eq_sum h k.normalBasis hsum hx).1
  second_support := by
    intro x hx
    let k := coordinateSingletonCorner C (cosine h) (sine h) (cosine_sq_add_sine_sq h)
    have hsum : h.bisector = k.normalBasis 0 + k.normalBasis 1 := by
      ext i
      fin_cases i <;> simp [k, coordinateSingletonCorner, cosine, sine] <;> ring
    simpa [k, coordinateSingletonCorner] using
      (CornerSupport.Equality.coords_nonpos_of_bisector_eq_sum h k.normalBasis hsum hx).2

/-- The support inequality at the end of the vertical face and the actual
endpoint of the incoming arm imply the needed height bound directly. -/
theorem long_arm_height {P : Set Plane} {C : Plane} (hP : P ⊆ triangle)
    (h : SupportCorner P C) {r : ℝ} (hE : (!₂[1, r] : Plane) ∈ P)
    (hs : 0 < sine h) (hc : 0 ≤ cosine h)
    (harm : C - (1 - r) • (coordinateCorner h).firstNormal ∈ P) :
    r + (1 - r) * cosine h ≤ C 1 := by
  have hsupport := (coordinateCorner h).second_support !₂[1, r] hE
  simp only [coordinateCorner, Schoenflies.Plane.inner_eq, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hsupport
  have harmx := (hP harm).2.2
  change C 0 - (1 - r) * -sine h ≤ 1 at harmx
  have hprod := mul_nonneg hc (show 0 ≤ 1 - C 0 - (1 - r) * sine h by
    nlinarith only [harmx])
  have hmul : (r + (1 - r) * cosine h) * sine h ≤ C 1 * sine h := by
    nlinarith only [hsupport, hprod]
  exact (mul_le_mul_iff_left₀ hs).mp (by simpa only [mul_comm] using hmul)

/-- With the actual long arm, every positive turn is impossible. -/
theorem sine_eq_zero_of_long_arm {P : Set Plane} {C : Plane}
    (hP : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P)
    (h : SupportCorner P C) (hC0 : C ≠ 0) (hCB : C ≠ corner 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hE : (!₂[1, r] : Plane) ∈ P)
    (harm : C - (1 - r) • (coordinateCorner h).firstNormal ∈ P) : sine h = 0 := by
  obtain ⟨hs, hc, _⟩ := direction_bounds hP h0 hB h hC0 hCB
  apply le_antisymm _ hs
  by_contra hpos
  have hspos : 0 < sine h := lt_of_not_ge hpos
  have hc0 : 0 ≤ cosine h := (by positivity : 0 ≤ Real.sqrt 3 / 2).trans hc
  have hheight := long_arm_height hP h hE hspos hc0 harm
  have htriangle := hP h.mem
  have hupper : C 1 ≤ 1 / Real.sqrt 3 := by
    apply (le_div_iff₀ sqrt_three_pos).mpr
    nlinarith only [htriangle.2.1, htriangle.2.2]
  exact TripleCornerBounds.support_arm_impossible hr.1 hr.2 hc hheight hupper

/-- The surviving zero-turn case has its corner on the right supporting line. -/
theorem corner_on_right_of_zero_turn {P : Set Plane} {C : Plane}
    (hP : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) (hB : corner 1 ∈ P)
    (h : SupportCorner P C) (hC0 : C ≠ 0) (hCB : C ≠ corner 1)
    {r : ℝ} (hE : (!₂[1, r] : Plane) ∈ P) (hs : sine h = 0) :
    cosine h = 1 ∧ C 0 = 1 ∧ 0 < C 1 ∧ C 1 < 1 := by
  have hc := (direction_bounds hP h0 hB h hC0 hCB).2.1
  have hunit := cosine_sq_add_sine_sq h
  rw [hs] at hunit
  have hc1 : cosine h = 1 := by
    nlinarith only [hunit, hc, sqrt_three_pos]
  have hsupport := (coordinateCorner h).second_support !₂[1, r] hE
  simp only [coordinateCorner, Schoenflies.Plane.inner_eq, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, hs, hc1, one_mul, zero_mul,
    add_zero] at hsupport
  have htri := hP h.mem
  have hCx : C 0 = 1 := by linarith only [hsupport, htri.2.2]
  have hCy : 0 < C 1 := by
    apply lt_of_le_of_ne htri.1
    intro hzero
    apply hCB
    ext i
    fin_cases i
    · simpa [corner] using hCx
    · simpa [corner] using hzero.symm
  have hCy1 : C 1 < 1 := by
    have hprod := mul_pos (sub_pos.mpr one_lt_sqrt_three) hCy
    nlinarith only [hprod, htri.2.1, hCx]
  exact ⟨hc1, hCx, hCy, hCy1⟩

end

end Puzzling139335.N6.TripleOppositeParity.SupportArms
