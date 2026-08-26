import ErdosProblems.Erdos633.Trapezoid
import ErdosProblems.Erdos633.Congruence
import ErdosProblems.Erdos633.Isosceles

/-!
# The Euclidean template for a triangle with a 120-degree angle

Hexagonal coordinates have squared norm `x²+xy+y²`. A reference triangle
with sides `a,b,c`, where `c²=a²+ab+b²`, supplies three similar triangles
of scales `b,c,a` covering a trapezoid of height `ab` and base `c²`.
-/

namespace Erdos633

noncomputable def hexUnit : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

noncomputable def hexTriangle : Triangle where
  a := 0
  b := 1
  c := hexUnit
  nondegenerate := by
    simp [hexUnit]

theorem hexTriangle_side_squares :
    Complex.normSq (hexTriangle.b - hexTriangle.a) = 1 ∧
    Complex.normSq (hexTriangle.c - hexTriangle.a) = 1 ∧
    Complex.normSq (hexTriangle.c - hexTriangle.b) = 1 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [hexTriangle, hexUnit, sub_zero, Complex.normSq_apply,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  constructor
  · norm_num
  constructor <;> nlinarith

theorem hexUnit_normSq : Complex.normSq hexUnit = 1 := by
  simpa only [hexTriangle, sub_zero] using hexTriangle_side_squares.2.1

noncomputable def hexCoordinates : ℂ ≃ᵃ[ℝ] ℂ := hexTriangle.coordinateEquiv

theorem hexCoordinates_apply (z : ℂ) :
    hexCoordinates z = (z.re : ℂ) + (z.im : ℂ) * hexUnit := by
  simp [hexCoordinates, Triangle.coordinateEquiv_apply, hexTriangle, Complex.real_smul]

theorem hexCoordinates_normSq_sub (z w : ℂ) :
    Complex.normSq (hexCoordinates z - hexCoordinates w) =
      (z.re - w.re) ^ 2 + (z.re - w.re) * (z.im - w.im) + (z.im - w.im) ^ 2 := by
  rw [hexCoordinates, Triangle.coordinateEquiv_normSq_sub,
    hexTriangle_side_squares.1, hexTriangle_side_squares.2.1,
    hexTriangle_side_squares.2.2]
  ring

structure OneTwentyShape where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c
  conic : c ^ 2 = a ^ 2 + a * b + b ^ 2

def OneTwentyShape.swap (S : OneTwentyShape) : OneTwentyShape where
  a := S.b
  b := S.a
  c := S.c
  a_pos := S.b_pos
  b_pos := S.a_pos
  c_pos := S.c_pos
  conic := by rw [S.conic]; ring

def OneTwentyShape.normalizedReference (S : OneTwentyShape) : Triangle where
  a := 0
  b := (S.a : ℂ)
  c := ⟨-S.b, S.b⟩
  nondegenerate := by
    simpa using mul_ne_zero (ne_of_gt S.a_pos) (ne_of_gt S.b_pos)

noncomputable def OneTwentyShape.reference (S : OneTwentyShape) : Triangle :=
  S.normalizedReference.mapAffineEquiv hexCoordinates

@[simp] theorem OneTwentyShape.reference_a (S : OneTwentyShape) : S.reference.a = 0 := by
  change hexCoordinates 0 = 0
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.reference_b (S : OneTwentyShape) :
    S.reference.b = (S.a : ℂ) := by
  change hexCoordinates (S.a : ℂ) = _
  simp [hexCoordinates_apply]

@[simp] theorem OneTwentyShape.reference_c (S : OneTwentyShape) :
    S.reference.c = (S.b : ℂ) * (hexUnit - 1) := by
  change hexCoordinates ⟨-S.b, S.b⟩ = _
  simp only [hexCoordinates_apply, Complex.ofReal_neg]
  ring

def OneTwentyShape.fan (S : OneTwentyShape) : TrapezoidFan where
  H := S.a * S.b
  L := S.c ^ 2
  p := S.b ^ 2
  H_pos := mul_pos S.a_pos S.b_pos
  p_pos := sq_pos_of_pos S.b_pos
  top_right_pos := by
    rw [S.conic]
    nlinarith [sq_pos_of_pos S.a_pos]

noncomputable def OneTwentyShape.left (S : OneTwentyShape) : Triangle :=
  S.fan.left.mapAffineEquiv hexCoordinates

noncomputable def OneTwentyShape.center (S : OneTwentyShape) : Triangle :=
  S.fan.center.mapAffineEquiv hexCoordinates

noncomputable def OneTwentyShape.right (S : OneTwentyShape) : Triangle :=
  S.fan.right.mapAffineEquiv hexCoordinates

theorem OneTwentyShape.reference_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.reference.b - S.reference.a) = S.a ^ 2 ∧
    Complex.normSq (S.reference.c - S.reference.a) = S.b ^ 2 ∧
    Complex.normSq (S.reference.c - S.reference.b) = S.c ^ 2 := by
  change Complex.normSq (hexCoordinates (S.a : ℂ) - hexCoordinates 0) = S.a ^ 2 ∧
    Complex.normSq (hexCoordinates ⟨-S.b, S.b⟩ - hexCoordinates 0) = S.b ^ 2 ∧
    Complex.normSq (hexCoordinates ⟨-S.b, S.b⟩ - hexCoordinates (S.a : ℂ)) = S.c ^ 2
  simp only [hexCoordinates_normSq_sub, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, sub_zero, S.conic]
  constructor
  · ring
  constructor <;> ring

theorem OneTwentyShape.left_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.left.swapAB.b - S.left.swapAB.a) = S.b ^ 2 * S.a ^ 2 ∧
    Complex.normSq (S.left.swapAB.c - S.left.swapAB.a) = S.b ^ 2 * S.b ^ 2 ∧
    Complex.normSq (S.left.swapAB.c - S.left.swapAB.b) = S.b ^ 2 * S.c ^ 2 := by
  change Complex.normSq (hexCoordinates 0 - hexCoordinates ⟨0, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩ -
      hexCoordinates ⟨0, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩ - hexCoordinates 0) = _
  simp only [hexCoordinates_normSq_sub, Complex.zero_re, Complex.zero_im, S.conic]
  constructor
  · ring
  constructor <;> ring

theorem OneTwentyShape.center_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.center.swapAC.b - S.center.swapAC.a) = S.c ^ 2 * S.a ^ 2 ∧
    Complex.normSq (S.center.swapAC.c - S.center.swapAC.a) = S.c ^ 2 * S.b ^ 2 ∧
    Complex.normSq (S.center.swapAC.c - S.center.swapAC.b) = S.c ^ 2 * S.c ^ 2 := by
  change Complex.normSq (hexCoordinates ((S.c ^ 2 : ℝ) : ℂ) -
      hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates 0 - hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates 0 - hexCoordinates ((S.c ^ 2 : ℝ) : ℂ)) = _
  simp only [hexCoordinates_normSq_sub, Complex.zero_re, Complex.zero_im,
    Complex.ofReal_re, Complex.ofReal_im, S.conic]
  constructor
  · ring
  constructor <;> ring

theorem OneTwentyShape.right_side_squares (S : OneTwentyShape) :
    Complex.normSq (S.right.rotate.b - S.right.rotate.a) = S.a ^ 2 * S.a ^ 2 ∧
    Complex.normSq (S.right.rotate.c - S.right.rotate.a) = S.a ^ 2 * S.b ^ 2 ∧
    Complex.normSq (S.right.rotate.c - S.right.rotate.b) = S.a ^ 2 * S.c ^ 2 := by
  change Complex.normSq (hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩ -
      hexCoordinates ⟨S.c ^ 2 - S.a * S.b, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates ((S.c ^ 2 : ℝ) : ℂ) -
      hexCoordinates ⟨S.c ^ 2 - S.a * S.b, S.a * S.b⟩) = _ ∧
    Complex.normSq (hexCoordinates ((S.c ^ 2 : ℝ) : ℂ) -
      hexCoordinates ⟨S.b ^ 2, S.a * S.b⟩) = _
  simp only [hexCoordinates_normSq_sub, Complex.ofReal_re, Complex.ofReal_im, S.conic]
  constructor
  · ring
  constructor <;> ring

theorem OneTwentyShape.congruent_of_scaled_sides (S : OneTwentyShape)
    (P : Triangle) (q : ℝ) (hq : 0 < q)
    (hab : Complex.normSq (P.b - P.a) = q ^ 2 * S.a ^ 2)
    (hac : Complex.normSq (P.c - P.a) = q ^ 2 * S.b ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = q ^ 2 * S.c ^ 2) :
    ∃ e : ℂ ≃ᵢ ℂ,
      e '' (S.reference.mapSimilarity 0 (q : ℂ)
        (by exact_mod_cast ne_of_gt hq)).carrier = P.carrier := by
  apply Triangle.congruent_of_normSq
  · change Complex.normSq ((0 + (q : ℂ) * S.reference.b) -
      (0 + (q : ℂ) * S.reference.a)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.1, Complex.normSq_ofReal, hab]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.reference.c) -
      (0 + (q : ℂ) * S.reference.a)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.2.1, Complex.normSq_ofReal, hac]
    ring
  · change Complex.normSq ((0 + (q : ℂ) * S.reference.c) -
      (0 + (q : ℂ) * S.reference.b)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.2.2, Complex.normSq_ofReal, hbc]
    ring

theorem OneTwentyShape.left_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.reference.mapSimilarity 0 (S.b : ℂ)
      (by exact_mod_cast ne_of_gt S.b_pos)).carrier = S.left.carrier := by
  simpa only [Triangle.swapAB_carrier] using
    S.congruent_of_scaled_sides S.left.swapAB S.b S.b_pos
      S.left_side_squares.1 S.left_side_squares.2.1 S.left_side_squares.2.2

theorem OneTwentyShape.center_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.reference.mapSimilarity 0 (S.c : ℂ)
      (by exact_mod_cast ne_of_gt S.c_pos)).carrier = S.center.carrier := by
  simpa only [Triangle.swapAC_carrier] using
    S.congruent_of_scaled_sides S.center.swapAC S.c S.c_pos
      S.center_side_squares.1 S.center_side_squares.2.1 S.center_side_squares.2.2

theorem OneTwentyShape.right_congruent (S : OneTwentyShape) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (S.reference.mapSimilarity 0 (S.a : ℂ)
      (by exact_mod_cast ne_of_gt S.a_pos)).carrier = S.right.carrier := by
  simpa only [Triangle.rotate_carrier] using
    S.congruent_of_scaled_sides S.right.rotate S.a S.a_pos
      S.right_side_squares.1 S.right_side_squares.2.1 S.right_side_squares.2.2

end Erdos633
