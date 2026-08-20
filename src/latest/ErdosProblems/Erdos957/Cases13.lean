import ErdosProblems.Erdos957.Basic

/-!
# Coordinate lemmas for Cases 1 and 3 in Dumitrescu's charging scheme

This module deliberately stays at the low-level Euclidean-coordinate layer.  A point is a
pair of real coordinates and `sqDist` is the square of its Euclidean distance.  The lemmas below
record the coordinate conclusions used in Cases 1 and 3 without assuming any global charging
inequality.
-/

namespace Erdos957Cases13

open scoped RealInnerProductSpace

/-- A concrete point in the real Euclidean plane. -/
abbrev Point := ℝ × ℝ

/-- The square of Euclidean distance in the coordinate plane. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The coordinate plane identified with Mathlib's concrete Euclidean plane `ℂ`. -/
def toComplex (p : Point) : ℂ := ⟨p.1, p.2⟩

/-- The same coordinate point in the `EuclideanSpace` model used by the target theorem. -/
abbrev EuclideanPoint := EuclideanSpace ℝ (Fin 2)

noncomputable def toEuclidean (p : Point) : EuclideanPoint := !₂[p.1, p.2]

private lemma euclidean_inner_eq_coordinates (u v : EuclideanPoint) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma euclidean_norm_sq_eq_coordinates (u : EuclideanPoint) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, euclidean_inner_eq_coordinates]
  ring

/-- Direct bridge to the Euclidean-plane representation used elsewhere in this repository. -/
lemma sqDist_eq_euclidean_dist_sq (p q : Point) :
    sqDist p q = dist (toEuclidean p) (toEuclidean q) ^ 2 := by
  rw [dist_eq_norm, euclidean_norm_sq_eq_coordinates]
  simp [sqDist, toEuclidean]

/-- `sqDist` really is the square of the Euclidean metric, not a surrogate metric. -/
lemma sqDist_eq_complex_dist_sq (p q : Point) :
    sqDist p q = dist (toComplex p) (toComplex q) ^ 2 := by
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq]
  simp only [sqDist, toComplex, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

lemma sqDist_eq_one_iff_dist_eq_one (p q : Point) :
    sqDist p q = 1 ↔ dist (toComplex p) (toComplex q) = 1 := by
  rw [sqDist_eq_complex_dist_sq]
  constructor
  · intro h
    nlinarith [(dist_nonneg : 0 ≤ dist (toComplex p) (toComplex q))]
  · intro h
    rw [h]
    norm_num

lemma one_le_sqDist_iff_one_le_dist (p q : Point) :
    1 ≤ sqDist p q ↔ 1 ≤ dist (toComplex p) (toComplex q) := by
  rw [sqDist_eq_complex_dist_sq]
  constructor
  · intro h
    nlinarith [(dist_nonneg : 0 ≤ dist (toComplex p) (toComplex q))]
  · intro h
    nlinarith

def origin : Point := (0, 0)

/-- The normalized position of the Case 3 middle neighbor. -/
def verticalDown : Point := (0, -1)

/-- The positive square root of three. -/
noncomputable def sqrtThree : ℝ := √3

lemma sqrtThree_pos : 0 < sqrtThree := by
  exact Real.sqrt_pos.2 (by norm_num)

lemma sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

@[simp] lemma sqDist_self (p : Point) : sqDist p p = 0 := by
  simp [sqDist]

@[simp] lemma sqDist_origin (p : Point) : sqDist origin p = p.1 ^ 2 + p.2 ^ 2 := by
  simp [sqDist, origin]

@[simp] lemma sqDist_verticalDown (p : Point) :
    sqDist verticalDown p = p.1 ^ 2 + (p.2 + 1) ^ 2 := by
  simp [sqDist, verticalDown]
  ring

lemma sqDist_comm (p q : Point) : sqDist p q = sqDist q p := by
  simp only [sqDist]
  ring

/-- Coordinate form of the normalized minimum-distance hypothesis. -/
def IsOneSeparated (S : Set Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ sqDist p q

lemma eq_or_one_le_sqDist_of_oneSeparated {S : Set Point} (hS : IsOneSeparated S)
    {p q : Point} (hp : p ∈ S) (hq : q ∈ S) :
    p = q ∨ 1 ≤ sqDist p q := by
  by_cases h : p = q
  · exact Or.inl h
  · exact Or.inr (hS p hp q hq h)

/-! ## Case 1: explicit regular-hexagon coordinates -/

/-- The left common unit neighbor of `origin` and a unit point `v`. -/
noncomputable def case1Left (v : Point) : Point :=
  ((v.1 + sqrtThree * v.2) / 2, (v.2 - sqrtThree * v.1) / 2)

/-- The right common unit neighbor of `origin` and a unit point `v`. -/
noncomputable def case1Right (v : Point) : Point :=
  ((v.1 - sqrtThree * v.2) / 2, (v.2 + sqrtThree * v.1) / 2)

/-- The regular-hexagon continuation forced above the left common neighbor. -/
noncomputable def case1ForcedAboveLeft (v : Point) : Point :=
  ((case1Left v).1 - v.1, (case1Left v).2 - v.2)

/-- The regular-hexagon continuation forced above the right common neighbor. -/
noncomputable def case1ForcedAboveRight (v : Point) : Point :=
  ((case1Right v).1 - v.1, (case1Right v).2 - v.2)

/-- The open 60-degree cone about the negative vertical ray.  This is precisely the scalar
coordinate information about a middle edge needed by the Case 1 calculation. -/
def InOpenMiddleCone (v : Point) : Prop :=
  sqrtThree * v.1 < -v.2 ∧ -sqrtThree * v.1 < -v.2

/-- A normalized point in the source rectangle used by the paper. -/
def InSourceRectangle (p : Point) : Prop :=
  -7 / 4 ≤ p.1 ∧ p.1 ≤ 7 / 4 ∧ -2 ≤ p.2 ∧ p.2 ≤ 0

lemma case1Left_common_unit {v : Point} (hv : sqDist origin v = 1) :
    sqDist origin (case1Left v) = 1 ∧ sqDist v (case1Left v) = 1 := by
  have hs := sqrtThree_sq
  constructor
  · simp only [sqDist, origin, case1Left, zero_sub] at hv ⊢
    ring_nf at hv ⊢
    nlinarith
  · simp only [sqDist, origin, case1Left, zero_sub] at hv ⊢
    ring_nf at hv ⊢
    nlinarith

lemma case1Right_common_unit {v : Point} (hv : sqDist origin v = 1) :
    sqDist origin (case1Right v) = 1 ∧ sqDist v (case1Right v) = 1 := by
  have hs := sqrtThree_sq
  constructor
  · simp only [sqDist, origin, case1Right, zero_sub] at hv ⊢
    ring_nf at hv ⊢
    nlinarith
  · simp only [sqDist, origin, case1Right, zero_sub] at hv ⊢
    ring_nf at hv ⊢
    nlinarith

lemma case1_forcedAboveLeft_height {v : Point} (hv : InOpenMiddleCone v) :
    0 < (case1ForcedAboveLeft v).2 := by
  rcases hv with ⟨_, hright⟩
  simp only [case1ForcedAboveLeft, case1Left]
  nlinarith

lemma case1_forcedAboveRight_height {v : Point} (hv : InOpenMiddleCone v) :
    0 < (case1ForcedAboveRight v).2 := by
  rcases hv with ⟨hleft, _⟩
  simp only [case1ForcedAboveRight, case1Right]
  nlinarith

/-- The left continuation is itself a unit point and a unit neighbor of the left recipient. -/
lemma case1_forcedAboveLeft_unit_edges {v : Point} (hv : sqDist origin v = 1) :
    sqDist origin (case1ForcedAboveLeft v) = 1 ∧
      sqDist (case1Left v) (case1ForcedAboveLeft v) = 1 := by
  have hcommon := case1Left_common_unit hv
  simp only [sqDist, origin] at hv
  simp only [sqDist, origin, case1ForcedAboveLeft] at hcommon ⊢
  constructor <;> nlinarith

/-- The right continuation is itself a unit point and a unit neighbor of the right recipient. -/
lemma case1_forcedAboveRight_unit_edges {v : Point} (hv : sqDist origin v = 1) :
    sqDist origin (case1ForcedAboveRight v) = 1 ∧
      sqDist (case1Right v) (case1ForcedAboveRight v) = 1 := by
  have hcommon := case1Right_common_unit hv
  simp only [sqDist, origin] at hv
  simp only [sqDist, origin, case1ForcedAboveRight] at hcommon ⊢
  constructor <;> nlinarith

lemma case1Left_below_support {v : Point} (hv : InOpenMiddleCone v) :
    (case1Left v).2 < 0 := by
  rcases hv with ⟨_, hright⟩
  simp only [case1Left]
  nlinarith

lemma case1Right_below_support {v : Point} (hv : InOpenMiddleCone v) :
    (case1Right v).2 < 0 := by
  rcases hv with ⟨hleft, _⟩
  simp only [case1Right]
  nlinarith

lemma unit_point_in_sourceRectangle {p : Point} (hp : sqDist origin p = 1)
    (hbelow : p.2 ≤ 0) : InSourceRectangle p := by
  simp only [sqDist, origin] at hp
  constructor
  · nlinarith [sq_nonneg (p.1 + 1)]
  constructor
  · nlinarith [sq_nonneg (p.1 - 1)]
  constructor
  · nlinarith [sq_nonneg (p.2 + 1)]
  · exact hbelow

lemma case1_recipients_in_sourceRectangle {v : Point} (hvunit : sqDist origin v = 1)
    (hvcone : InOpenMiddleCone v) :
    InSourceRectangle (case1Left v) ∧ InSourceRectangle (case1Right v) := by
  constructor
  · exact unit_point_in_sourceRectangle (case1Left_common_unit hvunit).1
      (case1Left_below_support hvcone).le
  · exact unit_point_in_sourceRectangle (case1Right_common_unit hvunit).1
      (case1Right_below_support hvcone).le

/-- The supporting-half-plane obstruction in Case 1.  Hexagonal rigidity supplies the displayed
forced point if the corresponding common neighbor has six unit neighbors; this lemma proves that
the supplied point cannot belong to the configuration. -/
lemma case1_forcedAboveLeft_not_mem {S : Set Point} {v : Point}
    (hS : ∀ p ∈ S, p.2 ≤ 0) (hvcone : InOpenMiddleCone v) :
    case1ForcedAboveLeft v ∉ S := by
  intro hmem
  exact (not_lt_of_ge (hS _ hmem)) (case1_forcedAboveLeft_height hvcone)

/-- The right-hand version of the supporting-half-plane obstruction in Case 1. -/
lemma case1_forcedAboveRight_not_mem {S : Set Point} {v : Point}
    (hS : ∀ p ∈ S, p.2 ≤ 0) (hvcone : InOpenMiddleCone v) :
    case1ForcedAboveRight v ∉ S := by
  intro hmem
  exact (not_lt_of_ge (hS _ hmem)) (case1_forcedAboveRight_height hvcone)

/-! ## Case 3: the high adjacent neighbor is forced to be equilateral -/

/-- Scalar core of Case 3.  The two points lie on the indicated right-hand arcs of the two unit
circles centered at `(0,0)` and `(0,-1)`.  They are strictly closer than one. -/
lemma case3_right_arc_closeness
    {qx qy tx ty : ℝ}
    (hqUnit : qx ^ 2 + qy ^ 2 = 1)
    (hqLower : -(1 / 2 : ℝ) ≤ qy)
    (hqBelow : qy < 0)
    (hqx : 0 ≤ qx)
    (htUnit : tx ^ 2 + (ty + 1) ^ 2 = 1)
    (htLower : -1 ≤ ty)
    (htUpper : ty ≤ -(1 / 2 : ℝ))
    (htx : 0 ≤ tx) :
    (tx - qx) ^ 2 + (ty - qy) ^ 2 < 1 := by
  have hdpos : 0 < -ty := by linarith
  have hOneSubB : 0 < 1 + qy := by linarith
  have hLast : 0 < 1 - qy + ty := by linarith
  have hfactor : 0 < 2 * (-ty) * (1 + qy) * (1 - qy + ty) := by positivity
  have hleftpos : 0 < (-ty) * (1 + qy) := mul_pos hdpos hOneSubB
  have hrightnonneg : 0 ≤ qx * tx := mul_nonneg hqx htx
  have hsquares : ((-ty) * (1 + qy)) ^ 2 < (qx * tx) ^ 2 := by
    nlinarith
  have hproduct : (-ty) * (1 + qy) < qx * tx := by
    nlinarith
  nlinarith

/-- In the normalized right-hand Case 3 picture, the selected high neighbor `t` must coincide
with the already existing unit neighbor `q` of the source.  The last hypothesis is exactly the
one-separated-set dichotomy for `q` and `t`, not an assumption of the desired conclusion. -/
lemma case3_right_candidate_eq_existing
    {q t : Point}
    (hqUnit : sqDist origin q = 1)
    (hqAwayFromV : 1 ≤ sqDist verticalDown q)
    (hqBelow : q.2 < 0)
    (hqx : 0 ≤ q.1)
    (htUnit : sqDist verticalDown t = 1)
    (htAwayFromU : 1 ≤ sqDist origin t)
    (htHigh : verticalDown.2 ≤ t.2)
    (htx : 0 ≤ t.1)
    (hsep : q = t ∨ 1 ≤ sqDist q t) :
    q = t := by
  rcases hsep with h | h
  · exact h
  exfalso
  have hqLower : -(1 / 2 : ℝ) ≤ q.2 := by
    simp only [sqDist, verticalDown] at hqAwayFromV
    simp only [sqDist, origin] at hqUnit
    nlinarith
  have htLower : -1 ≤ t.2 := by simpa [verticalDown] using htHigh
  have htUpper : t.2 ≤ -(1 / 2 : ℝ) := by
    simp only [sqDist, verticalDown] at htUnit
    simp only [sqDist, origin] at htAwayFromU
    nlinarith
  have hqUnit' : q.1 ^ 2 + q.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hqUnit
  have htUnit' : t.1 ^ 2 + (t.2 + 1) ^ 2 = 1 := by
    simp only [sqDist, verticalDown] at htUnit
    nlinarith [sq_nonneg (t.2 + 1)]
  have hclose := case3_right_arc_closeness
    hqUnit' hqLower hqBelow hqx htUnit' htLower htUpper htx
  simp only [sqDist] at h hclose
  linarith

/-- The same Case 3 conclusion with the separation dichotomy discharged from an ambient
one-separated configuration. -/
lemma case3_right_candidate_eq_existing_of_oneSeparated
    {S : Set Point} (hS : IsOneSeparated S) {q t : Point} (hqS : q ∈ S) (htS : t ∈ S)
    (hqUnit : sqDist origin q = 1)
    (hqAwayFromV : 1 ≤ sqDist verticalDown q)
    (hqBelow : q.2 < 0)
    (hqx : 0 ≤ q.1)
    (htUnit : sqDist verticalDown t = 1)
    (htAwayFromU : 1 ≤ sqDist origin t)
    (htHigh : verticalDown.2 ≤ t.2)
    (htx : 0 ≤ t.1) :
    q = t :=
  case3_right_candidate_eq_existing hqUnit hqAwayFromV hqBelow hqx htUnit
    htAwayFromU htHigh htx (eq_or_one_le_sqDist_of_oneSeparated hS hqS htS)

/-- Reflection of the preceding result across the vertical axis. -/
lemma case3_left_candidate_eq_existing
    {q t : Point}
    (hqUnit : sqDist origin q = 1)
    (hqAwayFromV : 1 ≤ sqDist verticalDown q)
    (hqBelow : q.2 < 0)
    (hqx : q.1 ≤ 0)
    (htUnit : sqDist verticalDown t = 1)
    (htAwayFromU : 1 ≤ sqDist origin t)
    (htHigh : verticalDown.2 ≤ t.2)
    (htx : t.1 ≤ 0)
    (hsep : q = t ∨ 1 ≤ sqDist q t) :
    q = t := by
  let reflect : Point → Point := fun p ↦ (-p.1, p.2)
  have hqUnit' : sqDist origin (reflect q) = 1 := by
    simpa [reflect, sqDist, origin] using hqUnit
  have hqAwayFromV' : 1 ≤ sqDist verticalDown (reflect q) := by
    simpa [reflect, sqDist, verticalDown] using hqAwayFromV
  have htUnit' : sqDist verticalDown (reflect t) = 1 := by
    simpa [reflect, sqDist, verticalDown] using htUnit
  have htAwayFromU' : 1 ≤ sqDist origin (reflect t) := by
    simpa [reflect, sqDist, origin] using htAwayFromU
  have hsep' : reflect q = reflect t ∨ 1 ≤ sqDist (reflect q) (reflect t) := by
    rcases hsep with h | h
    · exact Or.inl (congrArg reflect h)
    · apply Or.inr
      dsimp only [reflect, sqDist] at h ⊢
      nlinarith
  have heq := case3_right_candidate_eq_existing hqUnit' hqAwayFromV' hqBelow
    (by simpa [reflect] using hqx) htUnit' htAwayFromU'
    (by simpa [reflect, verticalDown] using htHigh) (by simpa [reflect] using htx) hsep'
  exact Prod.ext (by simpa [reflect] using congrArg Prod.fst heq)
    (by simpa [reflect] using congrArg Prod.snd heq)

/-- Once the Case 3 candidate has been identified with the existing source neighbor, it is a
common unit neighbor and hence the recipient lies in the source rectangle. -/
lemma case3_recipient_common_unit_and_in_rectangle
    {q t : Point} (hqt : q = t) (hqUnit : sqDist origin q = 1)
    (htUnit : sqDist verticalDown t = 1) (htBelow : t.2 ≤ 0) :
    sqDist origin t = 1 ∧ sqDist verticalDown t = 1 ∧ InSourceRectangle t := by
  subst q
  exact ⟨hqUnit, htUnit, unit_point_in_sourceRectangle hqUnit htBelow⟩

/-- For a common unit neighbor of `(0,0)` and `(0,-1)`, translating it one unit upward gives
the regular-hexagon continuation strictly above the support line. -/
def case3ForcedAbove (t : Point) : Point := (t.1, t.2 + 1)

lemma case3_forcedAbove_height {t : Point}
    (htU : sqDist origin t = 1) (htV : sqDist verticalDown t = 1) :
    (case3ForcedAbove t).2 = 1 / 2 := by
  simp only [sqDist, origin] at htU
  simp only [sqDist, verticalDown] at htV
  simp only [case3ForcedAbove]
  nlinarith

/-- The forced continuation in Case 3 completes two more unit edges of the regular hexagon. -/
lemma case3_forcedAbove_unit_edges {t : Point}
    (_htU : sqDist origin t = 1) (htV : sqDist verticalDown t = 1) :
    sqDist origin (case3ForcedAbove t) = 1 ∧
      sqDist t (case3ForcedAbove t) = 1 := by
  simp only [sqDist, verticalDown] at htV
  simp only [sqDist, origin, case3ForcedAbove]
  constructor <;> nlinarith

/-- The support-line contradiction used to show that the secondary Case 3 recipient cannot have
a complete regular hexagon of unit neighbors.  Hexagonal rigidity is the separate bridge that
produces `case3ForcedAbove t` from degree six. -/
lemma case3_forcedAbove_not_mem {S : Set Point} {t : Point}
    (hS : ∀ p ∈ S, p.2 ≤ 0)
    (htU : sqDist origin t = 1) (htV : sqDist verticalDown t = 1) :
    case3ForcedAbove t ∉ S := by
  intro hmem
  have hhalf := case3_forcedAbove_height htU htV
  have := hS _ hmem
  nlinarith

end Erdos957Cases13
