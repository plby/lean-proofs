import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coordinate estimates behind the locality step in Erdős problem 957

This file isolates the elementary part of the locality argument in Dumitrescu's charging
scheme. Points are represented by pairs of real coordinates in the moving frame at a flat
diameter endpoint. The key estimate below uses vertical diameter component at least `100`,
rather than the `10` printed in the paper: the latter does not imply the claimed rectangle
exclusion with the paper's constants.
-/

namespace Erdos957Locality

abbrev Point := ℝ × ℝ

/-- A quantitative cosine bound for the exposing-frame variant of the locality argument.
The first hull edge can deviate by one degree from horizontal and the next three turns each
contribute another degree, so all four directions lie within `π / 45` (four degrees). -/
lemma three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five :
    (399 / 400 : ℝ) < Real.cos (Real.pi / 45) := by
  have hpi : Real.pi / 45 < (7 / 100 : ℝ) := by
    nlinarith [Real.pi_lt_d2]
  have hsq : (Real.pi / 45) ^ 2 < (7 / 100 : ℝ) ^ 2 := by
    rw [sq_lt_sq₀ (by positivity) (by norm_num)]
    exact hpi
  have hcos := Real.one_sub_sq_div_two_lt_cos (x := Real.pi / 45) (by positivity)
  nlinarith

/-- The earlier angle-bisector bound at `π / 50` follows from the exposing-frame estimate. -/
lemma three_nine_nine_div_four_hundred_lt_cos_pi_div_fifty :
    (399 / 400 : ℝ) < Real.cos (Real.pi / 50) := by
  have hnonneg : 0 ≤ Real.pi / 50 := by positivity
  have hlepi : Real.pi / 45 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hangle : Real.pi / 50 ≤ Real.pi / 45 := by nlinarith [Real.pi_pos]
  exact three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le
    (Real.cos_le_cos_of_nonneg_of_le_pi hnonneg hlepi hangle)

/-- A unit-or-longer edge making angle at most `π/45` with the positive horizontal axis has
horizontal component greater than `399/400`. -/
lemma horizontal_increment_gt_three_nine_nine_div_four_hundred
    {r θ dx : ℝ} (hr : 1 ≤ r) (htheta : |θ| ≤ Real.pi / 45)
    (hdx : dx = r * Real.cos θ) :
    (399 / 400 : ℝ) < dx := by
  have habs_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have hpi : Real.pi / 45 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos_mono : Real.cos (Real.pi / 45) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi habs_nonneg hpi htheta
  rw [Real.cos_abs] at hcos_mono
  have hcos_pos : 0 < Real.cos θ := by
    have hrat : (0 : ℝ) < 399 / 400 := by norm_num
    exact hrat.trans
      (three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le hcos_mono)
  have hscale : Real.cos θ ≤ r * Real.cos θ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hcos_pos.le]
  rw [hdx]
  exact three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le
    (hcos_mono.trans hscale)

/-- Four such almost-horizontal edges put the next hull vertex beyond `x = 399/100`. -/
lemma four_flat_steps_exit_right
    {p₀ p₁ p₂ p₃ p₄ : Point}
    (hp₀ : p₀.1 = 0)
    (h₀ : (399 / 400 : ℝ) < p₁.1 - p₀.1)
    (h₁ : (399 / 400 : ℝ) < p₂.1 - p₁.1)
    (h₂ : (399 / 400 : ℝ) < p₃.1 - p₂.1)
    (h₃ : (399 / 400 : ℝ) < p₄.1 - p₃.1) :
    (399 / 100 : ℝ) < p₄.1 := by
  linarith

/-- Polar-coordinate description of one directed hull edge. -/
def IsPolarEdge (p q : Point) (r θ : ℝ) : Prop :=
  q.1 - p.1 = r * Real.cos θ ∧ q.2 - p.2 = r * Real.sin θ

/-- Starting within one degree of horizontal in an arbitrary exposing frame and making three
turns of at most one degree keeps each of the first four right-going edge directions within
`π/45` (four degrees) of horizontal. -/
lemma four_edge_angles_near_horizontal
    {θ₀ θ₁ θ₂ θ₃ : ℝ}
    (hθ₀ : |θ₀| ≤ Real.pi / 180)
    (hθ₁ : |θ₁ - θ₀| ≤ Real.pi / 180)
    (hθ₂ : |θ₂ - θ₁| ≤ Real.pi / 180)
    (hθ₃ : |θ₃ - θ₂| ≤ Real.pi / 180) :
    |θ₀| ≤ Real.pi / 45 ∧ |θ₁| ≤ Real.pi / 45 ∧
      |θ₂| ≤ Real.pi / 45 ∧ |θ₃| ≤ Real.pi / 45 := by
  have hp : 0 < Real.pi := Real.pi_pos
  have ha₁ : |θ₁| ≤ |θ₁ - θ₀| + |θ₀| := by
    calc
      |θ₁| = |(θ₁ - θ₀) + θ₀| := by congr 1; ring
      _ ≤ |θ₁ - θ₀| + |θ₀| := abs_add_le _ _
  have ha₂ : |θ₂| ≤ |θ₂ - θ₁| + |θ₁| := by
    calc
      |θ₂| = |(θ₂ - θ₁) + θ₁| := by congr 1; ring
      _ ≤ |θ₂ - θ₁| + |θ₁| := abs_add_le _ _
  have ha₃ : |θ₃| ≤ |θ₃ - θ₂| + |θ₂| := by
    calc
      |θ₃| = |(θ₃ - θ₂) + θ₂| := by congr 1; ring
      _ ≤ |θ₃ - θ₂| + |θ₂| := abs_add_le _ _
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Four one-separated polar edges controlled by the flat turns exit the right side at
`x > 399/100`. This is the analytic content of the flat-neighborhood hypothesis used by the
locality rectangle argument. -/
lemma four_polar_flat_edges_exit_right
    {p₀ p₁ p₂ p₃ p₄ : Point}
    {r₀ r₁ r₂ r₃ θ₀ θ₁ θ₂ θ₃ : ℝ}
    (hp₀ : p₀.1 = 0)
    (he₀ : IsPolarEdge p₀ p₁ r₀ θ₀)
    (he₁ : IsPolarEdge p₁ p₂ r₁ θ₁)
    (he₂ : IsPolarEdge p₂ p₃ r₂ θ₂)
    (he₃ : IsPolarEdge p₃ p₄ r₃ θ₃)
    (hr₀ : 1 ≤ r₀) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hr₃ : 1 ≤ r₃)
    (hθ₀ : |θ₀| ≤ Real.pi / 180)
    (hθ₁ : |θ₁ - θ₀| ≤ Real.pi / 180)
    (hθ₂ : |θ₂ - θ₁| ≤ Real.pi / 180)
    (hθ₃ : |θ₃ - θ₂| ≤ Real.pi / 180) :
    (399 / 100 : ℝ) < p₄.1 := by
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ :=
    four_edge_angles_near_horizontal hθ₀ hθ₁ hθ₂ hθ₃
  exact four_flat_steps_exit_right hp₀
    (horizontal_increment_gt_three_nine_nine_div_four_hundred hr₀ ha₀ he₀.1)
    (horizontal_increment_gt_three_nine_nine_div_four_hundred hr₁ ha₁ he₁.1)
    (horizontal_increment_gt_three_nine_nine_div_four_hundred hr₂ ha₂ he₂.1)
    (horizontal_increment_gt_three_nine_nine_div_four_hundred hr₃ ha₃ he₃.1)

/-- A direction in the four-degree flat-edge cone has downward slope at most `1/10`. -/
lemma neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
    {θ : ℝ} (hθ : |θ| ≤ Real.pi / 45) :
    -Real.sin θ ≤ Real.cos θ / 10 := by
  have habsθ : |θ| < (7 / 100 : ℝ) := by
    nlinarith [Real.pi_lt_d2]
  have habssin : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
  have hsin : -Real.sin θ < (7 / 100 : ℝ) := by
    have hle : -Real.sin θ ≤ |Real.sin θ| := neg_le_abs (Real.sin θ)
    linarith
  have hpi : Real.pi / 45 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcosMono : Real.cos (Real.pi / 45) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hpi hθ
  rw [Real.cos_abs] at hcosMono
  have hcos : (399 / 400 : ℝ) < Real.cos θ :=
    three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le hcosMono
  nlinarith

/-- Four positive-radius polar edges in the flat cone stay above the line `y = -x/10`.
This is the cone datum needed to remove vertical monotonicity from the chord argument. -/
lemma four_polar_edges_flat_cone
    {p₀ p₁ p₂ p₃ p₄ : Point}
    {r₀ r₁ r₂ r₃ θ₀ θ₁ θ₂ θ₃ : ℝ}
    (hp₀ : p₀ = (0, 0))
    (he₀ : IsPolarEdge p₀ p₁ r₀ θ₀)
    (he₁ : IsPolarEdge p₁ p₂ r₁ θ₁)
    (he₂ : IsPolarEdge p₂ p₃ r₂ θ₂)
    (he₃ : IsPolarEdge p₃ p₄ r₃ θ₃)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (hθ₀ : |θ₀| ≤ Real.pi / 45)
    (hθ₁ : |θ₁| ≤ Real.pi / 45)
    (hθ₂ : |θ₂| ≤ Real.pi / 45)
    (hθ₃ : |θ₃| ≤ Real.pi / 45) :
    -p₄.2 ≤ p₄.1 / 10 := by
  subst p₀
  have hs₀ := neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθ₀
  have hs₁ := neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθ₁
  have hs₂ := neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθ₂
  have hs₃ := neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθ₃
  have hm₀ : r₀ * (-Real.sin θ₀) ≤ r₀ * (Real.cos θ₀ / 10) :=
    mul_le_mul_of_nonneg_left hs₀ hr₀
  have hm₁ : r₁ * (-Real.sin θ₁) ≤ r₁ * (Real.cos θ₁ / 10) :=
    mul_le_mul_of_nonneg_left hs₁ hr₁
  have hm₂ : r₂ * (-Real.sin θ₂) ≤ r₂ * (Real.cos θ₂ / 10) :=
    mul_le_mul_of_nonneg_left hs₂ hr₂
  have hm₃ : r₃ * (-Real.sin θ₃) ≤ r₃ * (Real.cos θ₃ / 10) :=
    mul_le_mul_of_nonneg_left hs₃ hr₃
  rcases he₀ with ⟨he₀x, he₀y⟩
  rcases he₁ with ⟨he₁x, he₁y⟩
  rcases he₂ with ⟨he₂x, he₂y⟩
  rcases he₃ with ⟨he₃x, he₃y⟩
  nlinarith

/-- A length-`≥ 101` ray within one degree of the downward vertical satisfies the coarse
coordinate bounds used by `right_chain_avoids_competing_rectangle`. The ray is parametrized as
`(r * sin θ, -r * cos θ)`. -/
lemma inward_diameter_coordinate_bounds
    {r θ : ℝ} (hr : 101 ≤ r) (htheta : |θ| ≤ Real.pi / 180) :
    -(r * Real.cos θ) ≤ -(100 : ℝ) ∧
      (-(r * Real.cos θ)) / 50 ≤ r * Real.sin θ ∧
      r * Real.sin θ ≤ -((-(r * Real.cos θ)) / 50) := by
  have hangle : |θ| ≤ Real.pi / 45 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have hpi45 : Real.pi / 45 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos_mono : Real.cos (Real.pi / 45) ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hpi45 hangle
  rw [Real.cos_abs] at hcos_mono
  have hcos : (399 / 400 : ℝ) < Real.cos θ :=
    three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le hcos_mono
  have habstheta : |θ| < (7 / 400 : ℝ) := by
    have hpi := Real.pi_lt_d2
    nlinarith
  have habssin : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
  have hsin : -(7 / 400 : ℝ) < Real.sin θ := by
    have hneg : -|Real.sin θ| ≤ Real.sin θ := neg_abs_le (Real.sin θ)
    linarith
  have hsinUpper : Real.sin θ < (7 / 400 : ℝ) := by
    have hle : Real.sin θ ≤ |Real.sin θ| := le_abs_self (Real.sin θ)
    linarith
  have hrpos : 0 < r := by linarith
  constructor
  · have hscaled : (101 : ℝ) * (399 / 400) < r * Real.cos θ := by
      have h₁ : (101 : ℝ) * (399 / 400) ≤ r * (399 / 400) := by
        gcongr
      have h₂ : r * (399 / 400) < r * Real.cos θ := by
        nlinarith [mul_pos hrpos (sub_pos.mpr hcos)]
      exact h₁.trans_lt h₂
    norm_num at hscaled ⊢
    linarith
  · constructor
    · have hsum : 0 < Real.sin θ + Real.cos θ / 50 := by
        nlinarith
      have hscaled : 0 ≤ r * (Real.sin θ + Real.cos θ / 50) :=
        mul_nonneg hrpos.le hsum.le
      nlinarith
    · have hdiff : 0 < Real.cos θ / 50 - Real.sin θ := by
        nlinarith
      have hscaled : 0 ≤ r * (Real.cos θ / 50 - Real.sin θ) :=
        mul_nonneg hrpos.le hdiff.le
      nlinarith

/-- The signed two-dimensional cross product. -/
def cross (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

/-- `z` is on the exterior (right-chain) side of the directed chord from `p` to `q`. -/
def ExteriorOfRightChord (p q z : Point) : Prop :=
  0 ≤ cross (q.1 - p.1, q.2 - p.2) (z.1 - p.1, z.2 - p.2)

/-- Horizontal coordinate after rotating a coordinate frame counterclockwise by `θ`. -/
noncomputable def rotatedX (θ : ℝ) (p : Point) : ℝ :=
  p.1 * Real.cos θ - p.2 * Real.sin θ

/-- The honest edge charts in Cases 2 and 4 put every recipient in `|x| ≤ 3/2` and
`|y| ≤ 2`. Transporting such a point to a supporting/bisector chart whose axes differ by at
most one degree still leaves it strictly inside the paper's horizontal interval `(-7/4, 7/4)`.
This is the quantitative bridge that lets the original recipient rectangle remain unchanged. -/
lemma abs_rotatedX_lt_seven_div_four {θ : ℝ} {p : Point}
    (hx : |p.1| ≤ 3 / 2) (hy : |p.2| ≤ 2)
    (hθ : |θ| ≤ Real.pi / 180) :
    |rotatedX θ p| < (7 / 4 : ℝ) := by
  have htri : |rotatedX θ p| ≤
      |p.1| * |Real.cos θ| + |p.2| * |Real.sin θ| := by
    simpa [rotatedX, sub_eq_add_neg, abs_mul, mul_comm] using
      (abs_add_le (p.1 * Real.cos θ) (-(p.2 * Real.sin θ)))
  have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  have hsin : |Real.sin θ| ≤ Real.pi / 180 :=
    (Real.abs_sin_le_abs.trans hθ)
  have hxcos : |p.1| * |Real.cos θ| ≤ (3 / 2 : ℝ) := by
    calc
      |p.1| * |Real.cos θ| ≤ (3 / 2 : ℝ) * 1 :=
        mul_le_mul hx hcos (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := by norm_num
  have hysin : |p.2| * |Real.sin θ| ≤ 2 * (Real.pi / 180) :=
    mul_le_mul hy hsin (abs_nonneg _) (by norm_num)
  have hsmall : 2 * (Real.pi / 180) < (1 / 4 : ℝ) := by
    nlinarith [Real.pi_lt_four]
  linarith

/-- The rectangle containing every recipient of a charge sent from the origin. -/
def InRecipientRectangle (v : Point) : Prop :=
  -(7 / 4 : ℝ) ≤ v.1 ∧ v.1 ≤ 7 / 4 ∧ -(2 : ℝ) ≤ v.2 ∧ v.2 ≤ 0

/-- The enlarged rectangle in which a competing hull source would have to lie. -/
def InCompetingSourceRectangle (v : Point) : Prop :=
  -(15 / 4 : ℝ) ≤ v.1 ∧ v.1 ≤ 15 / 4 ∧ -(4 : ℝ) ≤ v.2 ∧ v.2 ≤ 0

/-- A point at coordinatewise distance at most two from a recipient lies in the enlarged
rectangle, provided it lies below the supporting line. In the geometric application the
coordinatewise bounds follow from Euclidean distance at most two. -/
lemma competing_source_mem_rectangle {v w : Point}
    (hv : InRecipientRectangle v)
    (hx : |w.1 - v.1| ≤ 2) (hy : |w.2 - v.2| ≤ 2) (hwy : w.2 ≤ 0) :
    InCompetingSourceRectangle w := by
  rcases hv with ⟨hvxl, hvxu, hvyl, hvyu⟩
  rw [abs_le] at hx hy
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · exact hwy

/-- The standard product distance on coordinate pairs at most two implies coordinatewise
distance at most two. The analogous Euclidean-plane fact follows by bounding a coordinate by
the Euclidean norm. -/
lemma abs_coord_sub_le_of_dist_le_two {v w : Point} (h : dist v w ≤ 2) :
    |w.1 - v.1| ≤ 2 ∧ |w.2 - v.2| ≤ 2 := by
  rw [Prod.dist_eq, max_le_iff] at h
  constructor
  · simpa [Real.dist_eq, abs_sub_comm] using h.1
  · simpa [Real.dist_eq, abs_sub_comm] using h.2

/-- Metric form of `competing_source_mem_rectangle`. -/
lemma competing_source_mem_rectangle_of_dist {v w : Point}
    (hv : InRecipientRectangle v) (hvw : dist v w ≤ 2) (hwy : w.2 ≤ 0) :
    InCompetingSourceRectangle w := by
  obtain ⟨hx, hy⟩ := abs_coord_sub_le_of_dist_le_two hvw
  exact competing_source_mem_rectangle hv hx hy hwy

/-- The printed threshold `Δ ≥ 10` cannot by itself yield the chord/rectangle exclusion.
These explicit coordinates have a vertical opposite point at distance `58`, a plausible fourth
flat-chain vertex, and an exterior-chain point still inside the enlarged rectangle. This is an
algebraic counterexample to that intermediate numerical implication, not to the final theorem. -/
lemma ten_is_not_enough_for_chord_exclusion :
    let p : Point := (4, -(1 / 7 : ℝ))
    let q : Point := (0, -58)
    let z : Point := (187 / 50, -4)
    ExteriorOfRightChord p q z ∧ InCompetingSourceRectangle z ∧
      (10 : ℝ) < dist (0, 0) q := by
  norm_num [ExteriorOfRightChord, cross, InCompetingSourceRectangle, Prod.dist_eq,
    Real.dist_eq]

/-- The numerical inequality responsible for the constants `15/4` and `4`.

Here `p` is the fourth vertex on the right of the flat diameter endpoint, `q` is its opposite
diameter endpoint, and `z` is a later point of the right convex chain. The hypotheses
`399/100 ≤ p.x`, `q.y ≤ -100`, and `q.y/50 ≤ q.x` are coarse consequences respectively of
four almost-horizontal one-separated hull edges, large diameter, and a diameter direction
within one degree of the inward normal. -/
lemma right_chain_avoids_competing_rectangle
    {p q z : Point}
    (hpx : (399 / 100 : ℝ) ≤ p.1)
    (hpyLower : -(4 : ℝ) ≤ p.2) (hpyUpper : p.2 ≤ 0)
    (hqy : q.2 ≤ -(100 : ℝ))
    (hqx : q.2 / 50 ≤ q.1)
    (hzyLower : -(4 : ℝ) ≤ z.2) (hzyUpper : z.2 ≤ p.2)
    (hexterior : ExteriorOfRightChord p q z) :
    (15 / 4 : ℝ) < z.1 := by
  simp only [ExteriorOfRightChord, cross] at hexterior
  have hA : 0 ≤ p.2 - z.2 := by linarith
  have hA4 : p.2 - z.2 ≤ p.2 + 4 := by linarith
  have hpy4 : 0 ≤ p.2 + 4 := by linarith
  have hD : 0 < p.2 - q.2 := by linarith
  have hmargin :
      0 < (p.1 - 15 / 4) * (p.2 - q.2) - (p.1 - q.1) * (p.2 + 4) := by
    have hqcoeff : q.2 / 50 * (p.2 + 4) ≤ q.1 * (p.2 + 4) :=
      mul_le_mul_of_nonneg_right hqx hpy4
    have hpxcoeff :
        (399 / 100 : ℝ) * (-(q.2 + 4)) ≤ p.1 * (-(q.2 + 4)) := by
      apply mul_le_mul_of_nonneg_right hpx
      linarith
    have hqy0 : q.2 ≤ 0 := by linarith
    have hqpy : 0 ≤ q.2 * p.2 := mul_nonneg_of_nonpos_of_nonpos hqy0 hpyUpper
    nlinarith
  by_contra hz
  have hzx : z.1 ≤ 15 / 4 := le_of_not_gt hz
  have hprod :
      (p.2 - q.2) * (p.1 - z.1) ≥
        (p.2 - q.2) * (p.1 - 15 / 4) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact hD.le
  by_cases hpq : q.1 ≤ p.1
  · have hAprod : (p.1 - q.1) * (p.2 - z.2) ≤
        (p.1 - q.1) * (p.2 + 4) :=
      mul_le_mul_of_nonneg_left hA4 (sub_nonneg.mpr hpq)
    nlinarith
  · have hpq' : p.1 < q.1 := lt_of_not_ge hpq
    have hneg : (p.1 - q.1) * (p.2 - z.2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hA
    nlinarith

/-- Right-chain exclusion without a vertical-monotonicity assumption on the later hull vertex.

Instead of assuming `z.y ≤ p.y`, this version uses the actual four-flat-edge cone
`-p.y ≤ p.x / 10`, both one-degree diameter-direction bounds, and the fact that the candidate
already lies in the horizontal span of the expanded source rectangle. -/
lemma right_chain_without_vertical_monotonicity
    {p q z : Point}
    (hpx : (399 / 100 : ℝ) ≤ p.1)
    (hpyUpper : p.2 ≤ 0)
    (hpCone : -p.2 ≤ p.1 / 10)
    (hqy : q.2 ≤ -(100 : ℝ))
    (hqxLower : q.2 / 50 ≤ q.1)
    (hqxUpper : q.1 ≤ -(q.2 / 50))
    (hzxLower : -(15 / 4 : ℝ) ≤ z.1)
    (hzyLower : -(4 : ℝ) ≤ z.2) (hzyUpper : z.2 ≤ 0)
    (hexterior : ExteriorOfRightChord p q z) :
    (15 / 4 : ℝ) < z.1 := by
  by_contra hz
  have hzx : z.1 ≤ 15 / 4 := le_of_not_gt hz
  have hpxz : 0 < p.1 - z.1 := by linarith
  by_cases hpq : q.1 ≤ p.1
  · by_cases hzp : z.2 ≤ p.2
    · exact (not_lt_of_ge hzx)
        (right_chain_avoids_competing_rectangle hpx
          (by linarith [hzyLower]) hpyUpper hqy hqxLower
          hzyLower hzp hexterior)
    · have hpz : p.2 < z.2 := lt_of_not_ge hzp
      have hqpx : q.1 - p.1 ≤ 0 := sub_nonpos.mpr hpq
      have hzpy : 0 < z.2 - p.2 := sub_pos.mpr hpz
      have hzxneg : z.1 - p.1 < 0 := by linarith
      by_cases hqpy : q.2 ≤ p.2
      · have hfirst : (q.1 - p.1) * (z.2 - p.2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hqpx hzpy.le
        have hsecond : 0 ≤ (q.2 - p.2) * (z.1 - p.1) :=
          mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hqpy) hzxneg.le
        simp only [ExteriorOfRightChord, cross] at hexterior
        nlinarith
      · have hpqy : p.2 < q.2 := lt_of_not_ge hqpy
        have hcoef : -q.2 / 50 - p.1 < 0 := by
          nlinarith [hpCone]
        have hAupper : q.1 - p.1 ≤ -q.2 / 50 - p.1 := by
          nlinarith [hqxUpper]
        have hfirstStep :
            (q.1 - p.1) * (z.2 - p.2) ≤
              (-q.2 / 50 - p.1) * (z.2 - p.2) :=
          mul_le_mul_of_nonneg_right hAupper hzpy.le
        have hgapLower : -4 - p.2 ≤ z.2 - p.2 := by linarith
        have hfirst :
            (q.1 - p.1) * (z.2 - p.2) ≤
              (-q.2 / 50 - p.1) * (-4 - p.2) := by
          exact hfirstStep.trans
            (mul_le_mul_of_nonpos_left hgapLower hcoef.le)
        have hqgap : 0 ≤ q.2 - p.2 := by linarith
        have hxgapUpper : p.1 - z.1 ≤ p.1 + 15 / 4 := by linarith
        have hsecond :
            (q.2 - p.2) * (p.1 - z.1) ≤
              (q.2 - p.2) * (p.1 + 15 / 4) :=
          mul_le_mul_of_nonneg_left hxgapUpper hqgap
        have hcoefPos : 0 ≤ -q.2 / 50 + 15 / 4 := by linarith
        have hconeGap : 0 ≤ p.1 / 10 + p.2 := by linarith [hpCone]
        have hproduct :
            0 ≤ (-q.2 / 50 + 15 / 4) * (p.1 / 10 + p.2) :=
          mul_nonneg hcoefPos hconeGap
        have hmargin :
            (-q.2 / 50 - p.1) * (-4 - p.2) +
              (q.2 - p.2) * (p.1 + 15 / 4) < 0 := by
          nlinarith
        simp only [ExteriorOfRightChord, cross] at hexterior
        nlinarith
  · have hpq' : p.1 < q.1 := lt_of_not_ge hpq
    have hpxpos : 0 < p.1 := by linarith
    have hcoef : q.2 + p.1 / 10 < 0 := by
      have hqbound : q.2 ≤ -50 * q.1 := by nlinarith [hqxUpper]
      nlinarith
    have hA0 : 0 ≤ q.1 - p.1 := by linarith
    have hAupper : q.1 - p.1 ≤ -q.2 / 50 - p.1 := by
      nlinarith [hqxUpper]
    have hyupper : z.2 - p.2 ≤ p.1 / 10 := by
      nlinarith [hzyUpper, hpCone]
    have hfirstStep :
        (q.1 - p.1) * (z.2 - p.2) ≤
          (q.1 - p.1) * (p.1 / 10) :=
      mul_le_mul_of_nonneg_left hyupper hA0
    have hpdiv : 0 ≤ p.1 / 10 := by positivity
    have hfirst :
        (q.1 - p.1) * (z.2 - p.2) ≤
          (-q.2 / 50 - p.1) * (p.1 / 10) :=
      hfirstStep.trans (mul_le_mul_of_nonneg_right hAupper hpdiv)
    have hcoefUpper : q.2 - p.2 ≤ q.2 + p.1 / 10 := by
      nlinarith [hpCone]
    have hB0 : 0 ≤ p.1 - z.1 := hpxz.le
    have hsecondStep :
        (q.2 - p.2) * (p.1 - z.1) ≤
          (q.2 + p.1 / 10) * (p.1 - z.1) :=
      mul_le_mul_of_nonneg_right hcoefUpper hB0
    have hB : p.1 - 15 / 4 ≤ p.1 - z.1 := by linarith
    have hsecond :
        (q.2 - p.2) * (p.1 - z.1) ≤
          (q.2 + p.1 / 10) * (p.1 - 15 / 4) := by
      exact hsecondStep.trans
        (mul_le_mul_of_nonpos_left hB hcoef.le)
    have hmargin :
        (-q.2 / 50 - p.1) * (p.1 / 10) +
          (q.2 + p.1 / 10) * (p.1 - 15 / 4) < 0 := by
      have hqpos : 0 < -q.2 := by linarith
      have hxmargin : 0 < 499 / 500 * p.1 - 15 / 4 := by
        nlinarith
      nlinarith [mul_pos hqpos hxmargin]
    simp only [ExteriorOfRightChord, cross] at hexterior
    nlinarith

/-- Descriptive alias for `right_chain_without_vertical_monotonicity`. -/
lemma right_chain_avoids_competing_rectangle_of_flat_cone
    {p q z : Point}
    (hpx : (399 / 100 : ℝ) ≤ p.1)
    (hpyUpper : p.2 ≤ 0)
    (hpCone : -p.2 ≤ p.1 / 10)
    (hqy : q.2 ≤ -(100 : ℝ))
    (hqxLower : q.2 / 50 ≤ q.1)
    (hqxUpper : q.1 ≤ -(q.2 / 50))
    (hzxLower : -(15 / 4 : ℝ) ≤ z.1)
    (hzyLower : -(4 : ℝ) ≤ z.2) (hzyUpper : z.2 ≤ 0)
    (hexterior : ExteriorOfRightChord p q z) :
    (15 / 4 : ℝ) < z.1 :=
  right_chain_without_vertical_monotonicity hpx hpyUpper hpCone hqy
    hqxLower hqxUpper hzxLower hzyLower hzyUpper hexterior

/-- Reflection of the right-chain estimate across the vertical axis. -/
lemma left_chain_avoids_competing_rectangle
    {p q z : Point}
    (hpx : p.1 ≤ -(399 / 100 : ℝ))
    (hpyLower : -(4 : ℝ) ≤ p.2) (hpyUpper : p.2 ≤ 0)
    (hqy : q.2 ≤ -(100 : ℝ))
    (hqx : q.1 ≤ -(q.2 / 50))
    (hzyLower : -(4 : ℝ) ≤ z.2) (hzyUpper : z.2 ≤ p.2)
    (hexterior : ExteriorOfRightChord (-p.1, p.2) (-q.1, q.2) (-z.1, z.2)) :
    z.1 < -(15 / 4 : ℝ) := by
  have h := right_chain_avoids_competing_rectangle
    (p := (-p.1, p.2)) (q := (-q.1, q.2)) (z := (-z.1, z.2))
    (by dsimp; linarith) hpyLower hpyUpper hqy (by dsimp; linarith)
    hzyLower hzyUpper hexterior
  dsimp at h
  linarith

/-- The checked coordinate core of the right-hand locality argument, with the flat-edge and
diameter-ray inputs exposed separately. In a polygon formalization, the four increment
hypotheses come from the seven `> 179°` hull angles, while `hexterior` and `hzyUpper` come from
cyclic convexity of the arc from `p₄` to the opposite diameter endpoint. -/
lemma right_locality_coordinate_core
    {p₀ p₁ p₂ p₃ p₄ z : Point} {r θ : ℝ}
    (hp₀ : p₀.1 = 0)
    (h₀ : (399 / 400 : ℝ) < p₁.1 - p₀.1)
    (h₁ : (399 / 400 : ℝ) < p₂.1 - p₁.1)
    (h₂ : (399 / 400 : ℝ) < p₃.1 - p₂.1)
    (h₃ : (399 / 400 : ℝ) < p₄.1 - p₃.1)
    (hp₄y : p₄.2 ≤ 0)
    (hr : 101 ≤ r) (htheta : |θ| ≤ Real.pi / 180)
    (hzyLower : -(4 : ℝ) ≤ z.2) (hzyUpper : z.2 ≤ p₄.2)
    (hexterior : ExteriorOfRightChord p₄
      (r * Real.sin θ, -(r * Real.cos θ)) z) :
    (15 / 4 : ℝ) < z.1 := by
  have hp₄x : (399 / 100 : ℝ) ≤ p₄.1 :=
    (four_flat_steps_exit_right hp₀ h₀ h₁ h₂ h₃).le
  have hp₄yLower : -(4 : ℝ) ≤ p₄.2 := hzyLower.trans hzyUpper
  obtain ⟨hqy, hqxLower, _hqxUpper⟩ := inward_diameter_coordinate_bounds hr htheta
  exact right_chain_avoids_competing_rectangle hp₄x hp₄yLower hp₄y hqy hqxLower
    hzyLower hzyUpper hexterior

end Erdos957Locality
