import ErdosProblems.Erdos957.ExceptionalCollisionGeometry
import ErdosProblems.Erdos957.Case4NoThree
import ErdosProblems.Erdos957.ExceptionalWindowDispatch
import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.DirectSameSide

/-!
# Case-2 secondary collision leaves

These are downstream consequences of the formula-retaining Case-2
descriptor.  They assume no capacity or collision bound.  The final cyclic
role dispatch only has to supply the displayed orbit inequalities and unit
incidences.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case2SecondaryNoThree

open Erdos957GeometryCore
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957ExceptionalCollisionGeometry
open Erdos957CollisionInstantiation
open Erdos957GeometryLocalRows
open Erdos957RoleCollisions
open Erdos957CoherentRealizedRows
open Erdos957DirectSameSide

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P}
variable {F : P.FlatAlignedFrameData}

/-- Coordinate core for the direct-arrival side at the second away source.
The common Case-2 target is `e`.  Of its two equilateral completions with a
shallow-cone hull source, the completion having nonnegative oriented area
lies on or above the retained support line.  Hence an actual non-hull proxy,
which is strictly below that line, has negative oriented area. -/
private lemma case2_e_equilateral_proxy_cross_neg
    {t r : Point}
    (htx : (2 : ℝ) * (399 / 400 : ℝ) < t 0)
    (hty : t 1 < 0)
    (hcone : -t 1 ≤ t 0 / 10)
    (hte : dist t Erdos957Cases24.Case2.e = 1)
    (htr : dist t r = 1)
    (her : dist Erdos957Cases24.Case2.e r = 1)
    (hry : r 1 < 0) :
    Erdos957GeometryCore.cross (r - t)
      (Erdos957Cases24.Case2.e - t) < 0 := by
  have hsqrtPos := Erdos957Cases24.sqrtThree_pos
  have hsqrtSq := Erdos957Cases24.sqrtThree_sq
  have hteSq := Erdos957Cases24.dist_sq_eq_coordinates
    t Erdos957Cases24.Case2.e
  have htrSq := Erdos957Cases24.dist_sq_eq_coordinates t r
  have herSq := Erdos957Cases24.dist_sq_eq_coordinates
    Erdos957Cases24.Case2.e r
  rw [hte] at hteSq
  rw [htr] at htrSq
  rw [her] at herSq
  simp only [Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hteSq htrSq herSq
  ring_nf at hteSq htrSq herSq
  let a : ℝ := t 0 - 3 / 2
  let b : ℝ := t 1 + Erdos957Cases24.sqrtThree / 2
  have haPos : 0 < a := by dsimp [a]; linarith
  have htXUpper : t 0 ≤ 5 / 2 := by
    nlinarith [sq_nonneg (t 1 + Erdos957Cases24.sqrtThree / 2)]
  have hbPos : 0 < b := by
    dsimp [b]
    have hsqrtLower : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
      nlinarith
    linarith
  have hbUpper : b < Erdos957Cases24.sqrtThree / 2 := by
    dsimp [b]
    linarith
  have habNorm : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    nlinarith
  have haHalf : (1 / 2 : ℝ) < a := by
    have hbSqLt : b ^ 2 < (Erdos957Cases24.sqrtThree / 2) ^ 2 := by
      nlinarith only [hbUpper, hbPos, hsqrtPos,
        sq_nonneg (b + Erdos957Cases24.sqrtThree / 2)]
    have haSq : (1 / 4 : ℝ) < a ^ 2 := by
      nlinarith only [habNorm, hbSqLt, hsqrtSq]
    nlinarith only [haSq, haPos, sq_nonneg (a + 1 / 2)]
  have haLtOne : a < 1 := by
    nlinarith [sq_nonneg b]
  have hprod : 0 < (2 * a - 1) * (1 - a) :=
    mul_pos (by linarith) (by linarith)
  have hsqCompare :
      (Erdos957Cases24.sqrtThree * (1 - a)) ^ 2 < b ^ 2 := by
    nlinarith [mul_pow Erdos957Cases24.sqrtThree (1 - a) 2]
  have hlinear :
      Erdos957Cases24.sqrtThree * (1 - a) < b := by
    have hleft : 0 ≤ Erdos957Cases24.sqrtThree * (1 - a) :=
      mul_nonneg hsqrtPos.le (by linarith)
    nlinarith only [hsqCompare, hleft, hbPos, sq_nonneg
      (b + Erdos957Cases24.sqrtThree * (1 - a))]
  let c : ℝ := Erdos957GeometryCore.cross (r - t)
    (Erdos957Cases24.Case2.e - t)
  have hdot :
      (r 0 - t 0) * (3 / 2 - t 0) +
          (r 1 - t 1) *
            (-(Erdos957Cases24.sqrtThree / 2) - t 1) = 1 / 2 := by
    nlinarith only [hteSq, htrSq, herSq, hsqrtSq]
  have hcFormula : c =
      (r 0 - t 0) * (-(Erdos957Cases24.sqrtThree / 2) - t 1) -
        (r 1 - t 1) * (3 / 2 - t 0) := by
    simp only [c, Erdos957GeometryCore.cross,
      Erdos957Cases24.Case2.e, PiLp.sub_apply,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one]
  have htrNorm :
      (r 0 - t 0) ^ 2 + (r 1 - t 1) ^ 2 = 1 := by
    nlinarith only [htrSq]
  have hteNorm :
      (3 / 2 - t 0) ^ 2 +
        (-(Erdos957Cases24.sqrtThree / 2) - t 1) ^ 2 = 1 := by
    nlinarith only [hteSq]
  have hlagrange :
      ((r 0 - t 0) * (-(Erdos957Cases24.sqrtThree / 2) - t 1) -
          (r 1 - t 1) * (3 / 2 - t 0)) ^ 2 +
        ((r 0 - t 0) * (3 / 2 - t 0) +
          (r 1 - t 1) *
            (-(Erdos957Cases24.sqrtThree / 2) - t 1)) ^ 2 =
      ((r 0 - t 0) ^ 2 + (r 1 - t 1) ^ 2) *
        ((3 / 2 - t 0) ^ 2 +
          (-(Erdos957Cases24.sqrtThree / 2) - t 1) ^ 2) := by
    ring
  have hcSq : c ^ 2 = 3 / 4 := by
    rw [hcFormula]
    rw [htrNorm, hteNorm, hdot] at hlagrange
    norm_num at hlagrange ⊢
    nlinarith only [hlagrange]
  by_contra hnot
  have hcNonneg : 0 ≤ c := le_of_not_gt hnot
  have hcEq : c = Erdos957Cases24.sqrtThree / 2 := by
    nlinarith only [hcSq, hcNonneg, hsqrtPos, hsqrtSq]
  have hby : r 1 - t 1 =
      (-(Erdos957Cases24.sqrtThree / 2) - t 1) * (1 / 2) -
        (3 / 2 - t 0) * c := by
    calc
      r 1 - t 1 = (r 1 - t 1) *
          ((3 / 2 - t 0) ^ 2 +
            (-(Erdos957Cases24.sqrtThree / 2) - t 1) ^ 2) := by
              rw [hteNorm]
              ring
      _ = (-(Erdos957Cases24.sqrtThree / 2) - t 1) *
            ((r 0 - t 0) * (3 / 2 - t 0) +
              (r 1 - t 1) *
                (-(Erdos957Cases24.sqrtThree / 2) - t 1)) -
          (3 / 2 - t 0) *
            ((r 0 - t 0) *
                (-(Erdos957Cases24.sqrtThree / 2) - t 1) -
              (r 1 - t 1) * (3 / 2 - t 0)) := by ring
      _ = _ := by rw [hdot, ← hcFormula]
  have hryFormula :
      r 1 = (t 1 - Erdos957Cases24.sqrtThree / 2) / 2 +
        (t 0 - 3 / 2) * c := by
    nlinarith only [hby]
  rw [hcEq] at hryFormula
  have : 0 < r 1 := by
    dsimp [a, b] at hlinear
    nlinarith only [hlinear, hryFormula]
  linarith

/-- Pure two-chart sign core.  The vector `(a,b)` points along the same
incoming hull edge as `(c,-d)` in the second chart.  Both edge directions
have slope at most `1/10`.  A unit target vector whose first coordinate in
the first chart is at most `-99/200` therefore still has negative first
coordinate in the second chart.  The two displayed equations are exactly
dot- and signed-area preservation. -/
private lemma fst_neg_of_shallow_edge_chart_change
    {a b c d x y X Y : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hb : |b| ≤ a / 10) (hd : |d| ≤ c / 10)
    (hx : x ≤ -(99 / 200 : ℝ)) (hy : |y| ≤ 1)
    (hdot : a * x + b * y = c * X - d * Y)
    (hcross : a * y - b * x = c * Y + d * X) :
    X < 0 := by
  have hab : 0 < a * c := mul_pos ha hc
  have hb' : |b| ≤ |a| / 10 := by simpa [abs_of_pos ha] using hb
  have hd' : |d| ≤ |c| / 10 := by simpa [abs_of_pos hc] using hd
  have hbd : |b * d| ≤ (a * c) / 100 := by
    rw [abs_mul]
    calc
      |b| * |d| ≤ (|a| / 10) * (|c| / 10) := by gcongr
      _ = (a * c) / 100 := by rw [abs_of_pos ha, abs_of_pos hc]; ring
  have had : |a * d| ≤ (a * c) / 10 := by
    rw [abs_mul, abs_of_pos ha]
    calc
      a * |d| ≤ a * (|c| / 10) := by gcongr
      _ = (a * c) / 10 := by rw [abs_of_pos hc]; ring
  have hbc : |b * c| ≤ (a * c) / 10 := by
    rw [abs_mul, abs_of_pos hc]
    calc
      |b| * c ≤ (|a| / 10) * c := by gcongr
      _ = (a * c) / 10 := by rw [abs_of_pos ha]; ring
  have hcoef : (99 / 100 : ℝ) * (a * c) ≤ a * c - b * d := by
    have hbdLower : -(a * c / 100) ≤ b * d := by
      exact le_trans (by linarith) (neg_abs_le (b * d))
    have hbdUpper : b * d ≤ a * c / 100 :=
      (le_abs_self (b * d)).trans hbd
    linarith
  have hcoefNonneg : 0 ≤ a * c - b * d := by
    have : 0 ≤ (99 / 100 : ℝ) * (a * c) := by positivity
    linarith
  have hmix : |a * d + b * c| ≤ (a * c) / 5 := by
    calc
      |a * d + b * c| ≤ |a * d| + |b * c| := abs_add_le _ _
      _ ≤ (a * c) / 10 + (a * c) / 10 := add_le_add had hbc
      _ = (a * c) / 5 := by ring
  have hxmul : (a * c - b * d) * x ≤
      (a * c - b * d) * (-(99 / 200 : ℝ)) :=
    mul_le_mul_of_nonneg_left hx hcoefNonneg
  have hcoefMul :
      (a * c - b * d) * (-(99 / 200 : ℝ)) ≤
        ((99 / 100 : ℝ) * (a * c)) * (-(99 / 200 : ℝ)) :=
    mul_le_mul_of_nonpos_right hcoef (by norm_num)
  have hmixedMul : (a * d + b * c) * y ≤ (a * c) / 5 := by
    calc
      (a * d + b * c) * y ≤
          |a * d + b * c| * |y| := by
            rw [← abs_mul]
            exact le_abs_self _
      _ ≤ ((a * c) / 5) * 1 := by gcongr
      _ = (a * c) / 5 := by ring
  have hformula : (c ^ 2 + d ^ 2) * X =
      (a * c - b * d) * x + (a * d + b * c) * y := by
    calc
      (c ^ 2 + d ^ 2) * X =
          c * (c * X - d * Y) + d * (c * Y + d * X) := by ring
      _ = c * (a * x + b * y) + d * (a * y - b * x) := by
        rw [← hdot, ← hcross]
      _ = (a * c - b * d) * x + (a * d + b * c) * y := by ring
  have hnegative :
      (a * c - b * d) * x + (a * d + b * c) * y < 0 := by
    calc
      _ ≤ ((99 / 100 : ℝ) * (a * c)) * (-(99 / 200 : ℝ)) +
          (a * c) / 5 := add_le_add (hxmul.trans hcoefMul) hmixedMul
      _ < 0 := by nlinarith
  have hnormPos : 0 < c ^ 2 + d ^ 2 := by nlinarith [sq_nonneg d]
  nlinarith

/-- Polarization of the two distance-preserving coordinate packages.  It
lets the exceptional sign argument compare dot products without introducing
an additional chart-transition structure. -/
private lemma rigid_aligned_dot_displacements
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (p q r : Vertex A) :
    let ep := E.toCanonical p
    let eq := E.toCanonical q
    let er := E.toCanonical r
    let cp := C.coord i p
    let cq := C.coord i q
    let cr := C.coord i r
    (eq 0 - ep 0) * (er 0 - ep 0) +
        (eq 1 - ep 1) * (er 1 - ep 1) =
      (cq.1 - cp.1) * (cr.1 - cp.1) +
        (cq.2 - cp.2) * (cr.2 - cp.2) := by
  dsimp only
  have hEpq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical p) (E.toCanonical q)
  have hEpr := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical p) (E.toCanonical r)
  have hEqr := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical q) (E.toCanonical r)
  rw [E.dist_eq] at hEpq hEpr hEqr
  have hCpq := C.sqDist_coord i p q
  have hCpr := C.sqDist_coord i p r
  have hCqr := C.sqDist_coord i q r
  simp only [Erdos957Cases13.sqDist] at hCpq hCpr hCqr
  simp only [PiLp.sub_apply] at hEpq hEpr hEqr
  nlinarith

/-- One positive-radius polar edge within four degrees has positive
horizontal increment and absolute slope at most `1/10`. -/
private lemma polar_edge_positive_abs_slope
    {p q : ℝ × ℝ} {r θ : ℝ}
    (hr : 1 ≤ r) (hθ : |θ| ≤ Real.pi / 45)
    (hp : Erdos957Locality.IsPolarEdge p q r θ) :
    0 < q.1 - p.1 ∧ |q.2 - p.2| ≤ (q.1 - p.1) / 10 := by
  have hx :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      hr hθ hp.1
  have hn :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθ
  have hθneg : |-θ| ≤ Real.pi / 45 := by simpa using hθ
  have hp' :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hθneg
  have hs : |Real.sin θ| ≤ Real.cos θ / 10 := by
    apply abs_le.mpr
    constructor
    · linarith [hn]
    · simpa only [Real.sin_neg, Real.cos_neg, neg_neg] using hp'
  have hr0 : 0 ≤ r := by linarith
  have hrs := mul_le_mul_of_nonneg_left hs hr0
  rcases hp with ⟨hpx, hpy⟩
  constructor
  · linarith
  · rw [hpy, hpx, abs_mul, abs_of_nonneg hr0]
    simpa only [mul_div_assoc] using hrs

private lemma no_target_with_case2_distance_drop_after_two_flat_steps
    {p₁ p₂ q : Erdos957Cases24.Point}
    (h₁x : (399 / 400 : ℝ) < p₁ 0)
    (h₁s : |p₁ 1| ≤ p₁ 0 / 10)
    (h₂x : (399 / 400 : ℝ) < p₂ 0 - p₁ 0)
    (h₂s : |p₂ 1 - p₁ 1| ≤ (p₂ 0 - p₁ 0) / 10)
    (hedge : dist p₁ p₂ = 1)
    (hqx : q 0 ≤ 3 / 2) (hqyLower : (-2 : ℝ) ≤ q 1)
    (hqyUpper : q 1 ≤ -3 / 4)
    (hd₁ : dist q p₁ ^ 2 ≤ 7)
    (hdrop : 1 ≤ dist q p₁ ^ 2 - dist q p₂ ^ 2) : False := by
  have h₁ := Erdos957Cases24.dist_sq_eq_coordinates q p₁
  have h₂ := Erdos957Cases24.dist_sq_eq_coordinates q p₂
  have hedgeSq := Erdos957Cases24.dist_sq_eq_coordinates p₁ p₂
  rw [hedge] at hedgeSq
  norm_num at hedgeSq
  rcases abs_le.mp h₁s with ⟨h₁lo, h₁hi⟩
  rcases abs_le.mp h₂s with ⟨h₂lo, h₂hi⟩
  have h₁Coord :
      (q 0 - p₁ 0) ^ 2 + (q 1 - p₁ 1) ^ 2 ≤ 7 := by
    rw [← h₁]
    exact hd₁
  have hp₁xUpper : p₁ 0 < 9 / 2 := by
    by_contra h
    have hgap : 3 ≤ p₁ 0 - q 0 := by linarith
    have hgapSq : 9 ≤ (p₁ 0 - q 0) ^ 2 := by
      nlinarith [sq_nonneg (p₁ 0 - q 0 - 3)]
    nlinarith [h₁Coord, sq_nonneg (q 1 - p₁ 1)]
  have hp₁yLower : -(9 / 20 : ℝ) < p₁ 1 := by linarith
  have hp₁yUpper : p₁ 1 < 9 / 20 := by linarith
  have hdxPos : 0 < p₂ 0 - p₁ 0 := by linarith
  have hdxLe : p₂ 0 - p₁ 0 ≤ 1 := by
    nlinarith only [hedgeSq, sq_nonneg (p₂ 1 - p₁ 1), hdxPos]
  have hbNeg : q 1 - p₁ 1 < 0 := by linarith
  have hbracket :
      (q 0 - p₁ 0) - (q 1 - p₁ 1) / 10 < 1 := by
    linarith
  have hmul :
      (q 1 - p₁ 1) * (p₂ 1 - p₁ 1) ≤
        -(q 1 - p₁ 1) * (p₂ 0 - p₁ 0) / 10 := by
    have hnonneg : 0 ≤ -(q 1 - p₁ 1) *
        ((p₂ 1 - p₁ 1) + (p₂ 0 - p₁ 0) / 10) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hnonneg]
  have hdotLower : 1 ≤
      (q 0 - p₁ 0) * (p₂ 0 - p₁ 0) +
        (q 1 - p₁ 1) * (p₂ 1 - p₁ 1) := by
    nlinarith only [h₁, h₂, hedgeSq, hdrop]
  have hdotUpper :
      (q 0 - p₁ 0) * (p₂ 0 - p₁ 0) +
          (q 1 - p₁ 1) * (p₂ 1 - p₁ 1) < 1 := by
    have hraw :
        (q 0 - p₁ 0) * (p₂ 0 - p₁ 0) +
            (q 1 - p₁ 1) * (p₂ 1 - p₁ 1) ≤
          (p₂ 0 - p₁ 0) *
            ((q 0 - p₁ 0) - (q 1 - p₁ 1) / 10) := by
      nlinarith only [hmul]
    by_cases hsign : 0 ≤
        (q 0 - p₁ 0) - (q 1 - p₁ 1) / 10
    · have hscale := mul_le_mul_of_nonneg_right hdxLe hsign
      nlinarith only [hraw, hscale, hbracket]
    · have hprod : (p₂ 0 - p₁ 0) *
          ((q 0 - p₁ 0) - (q 1 - p₁ 1) / 10) < 0 :=
        mul_neg_of_pos_of_neg hdxPos (lt_of_not_ge hsign)
      linarith
  linarith

/-- Pure coordinate core for the remaining two-step Case-2/Case-2
collision.  The two hull increments point right inside the flat cone.  A
canonical Case-2 secondary cannot simultaneously have one of the three
Case-2 distance fingerprints from the intermediate and terminal vertices.
This statement deliberately contains no hull, role, or capacity data. -/
private lemma no_case2Secondary_fingerprint_after_two_flat_steps
    {p₁ p₂ q : Erdos957Cases24.Point}
    (h₁x : (399 / 400 : ℝ) < p₁ 0)
    (h₁s : |p₁ 1| ≤ p₁ 0 / 10)
    (h₂x : (399 / 400 : ℝ) < p₂ 0 - p₁ 0)
    (h₂s : |p₂ 1 - p₁ 1| ≤ (p₂ 0 - p₁ 0) / 10)
    (hedge : dist p₁ p₂ = 1)
    (hq : q = Erdos957Cases24.Case2.w ∨
      q = Erdos957Cases24.Case2.wNext ∨
      q = Erdos957Cases24.Case2.e)
    (hfp :
      (dist q p₁ ^ 2 = 4 ∧ dist q p₂ ^ 2 = 3) ∨
      (dist q p₁ ^ 2 = 7 ∧ dist q p₂ ^ 2 = 4) ∨
      (dist q p₁ ^ 2 = 7 ∧ dist q p₂ ^ 2 = 3)) : False := by
  have hqx : q 0 ≤ 3 / 2 := by
    rcases hq with h | h | h <;> rw [h] <;>
      norm_num [Erdos957Cases24.Case2.w,
        Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e]
  have hqyLower : (-2 : ℝ) ≤ q 1 := by
    rcases hq with h | h | h <;> rw [h] <;>
      simp only [Erdos957Cases24.Case2.w,
        Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e,
        Erdos957Cases24.point_apply_one] <;>
      nlinarith [Erdos957Cases24.sqrtThree_pos,
        Erdos957Cases24.sqrtThree_sq]
  have hqyUpper : q 1 ≤ -3 / 4 := by
    rcases hq with h | h | h <;> rw [h] <;>
      simp only [Erdos957Cases24.Case2.w,
        Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e,
        Erdos957Cases24.point_apply_one] <;>
      nlinarith [Erdos957Cases24.sqrtThree_pos,
        Erdos957Cases24.sqrtThree_sq]
  have hd₁ : dist q p₁ ^ 2 ≤ 7 := by
    rcases hfp with h | h | h <;> rw [h.1] <;> norm_num
  have hdrop : 1 ≤ dist q p₁ ^ 2 - dist q p₂ ^ 2 := by
    rcases hfp with h | h | h <;> rw [h.1, h.2] <;> norm_num
  exact no_target_with_case2_distance_drop_after_two_flat_steps
    h₁x h₁s h₂x h₂s hedge hqx hqyLower hqyUpper hd₁ hdrop

/-- The second outgoing edge still advances almost one full horizontal
unit in the terminal chart of a unit predecessor edge.  This is the
single-edge refinement of the cumulative prefix estimate. -/
private lemma previous_terminal_away_second_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1) :
    let p₁ := Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
      ((source.1 : Point) - (P.next⁻¹ source).1)
      ((P.next source).1 : Point)
    let p₂ := Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
      ((source.1 : Point) - (P.next⁻¹ source).1)
      (((P.next ^ 2) source).1 : Point)
    (399 / 400 : ℝ) < p₂.1 - p₁.1 ∧
      |p₂.2 - p₁.2| ≤ (p₂.1 - p₁.1) / 10 := by
  let pred := P.next⁻¹ source
  let e : ℝ × ℝ :=
    (-((F.chart.coord source pred.1).1),
      -((F.chart.coord source pred.1).2))
  obtain ⟨hl0, -, -, -⟩ := F.leftFlatAngles source hi
  obtain ⟨hr0, hr1, -, -⟩ := F.rightFlatAngles source hi
  have hleftNorm :
      (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
          (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source pred.1 source.1
    rw [show dist (pred.1 : Point) (source.1 : Point) = 1 by
      simpa [pred] using hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, neg_sq, one_pow] at hs
    simpa [pred, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord]
      using hs
  have hleftRadius : F.leftRadius source 0 = 1 := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.leftAngle source 0)
    have hrad := F.leftRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.leftRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.leftRadius source 0 ^ 2 *
            (Real.sin (F.leftAngle source 0) ^ 2 +
              Real.cos (F.leftAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
            (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hleftNorm
    nlinarith
  have he : e =
      (Real.cos (-F.leftAngle source 0),
        Real.sin (-F.leftAngle source 0)) := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hleftRadius] at hx hy
    norm_num at hx hy
    simp only [e, pred,
      CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hangle :
      |F.rightAngle source 1 + F.leftAngle source 0| ≤ Real.pi / 45 := by
    have hr1abs : |F.rightAngle source 1| ≤
        |F.rightAngle source 1 - F.rightAngle source 0| +
          |F.rightAngle source 0| := by
      calc
        _ = |(F.rightAngle source 1 - F.rightAngle source 0) +
            F.rightAngle source 0| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    have hsum := abs_add_le (F.rightAngle source 1)
      (F.leftAngle source 0)
    nlinarith [Real.pi_pos]
  have hp := Erdos957Case4NoThree.pairEdgeTransform_polar he
    (F.rightPolar source (1 : Fin 4))
  have hp' : Erdos957Locality.IsPolarEdge
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.rightOrbitCoord P source 1))
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.rightOrbitCoord P source 2))
      (F.rightRadius source 1)
      (F.rightAngle source 1 + F.leftAngle source 0) := by
    simpa [sub_eq_add_neg] using hp
  have hx :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one source 1) hangle hp'.1
  change (399 / 400 : ℝ) <
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.coord source ((P.next ^ 2) source).1)).1 -
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.coord source (P.next source).1)).1 at hx
  let θ := F.rightAngle source 1 + F.leftAngle source 0
  have hsinNeg :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
      hangle
  have hangleNeg : |-θ| ≤ Real.pi / 45 := by
    simpa only [abs_neg] using hangle
  have hsinPos :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
      hangleNeg
  have habsSin : |Real.sin θ| ≤ Real.cos θ / 10 := by
    apply abs_le.mpr
    constructor
    · dsimp only [θ] at *
      linarith
    · simpa only [Real.sin_neg, Real.cos_neg, neg_neg] using hsinPos
  have hrNonneg : 0 ≤ F.rightRadius source 1 := by
    linarith [F.rightRadius_ge_one source 1]
  have hm := mul_le_mul_of_nonneg_left habsSin hrNonneg
  have hy :
      |(Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.coord source ((P.next ^ 2) source).1)).2 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.coord source (P.next source).1)).2| ≤
        ((Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.coord source ((P.next ^ 2) source).1)).1 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.coord source (P.next source).1)).1) / 10 := by
    have hxPolar := hp'.1
    have hyPolar := hp'.2
    change
      |(Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.rightOrbitCoord P source 2)).2 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.rightOrbitCoord P source 1)).2| ≤
        ((Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.rightOrbitCoord P source 2)).1 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.rightOrbitCoord P source 1)).1) / 10
    rw [hyPolar, hxPolar, abs_mul, abs_of_nonneg hrNonneg]
    dsimp only [θ] at hm
    nlinarith
  dsimp only
  rw [Erdos957Case4NoThree.terminalEdgePairCoord_eq_aligned
      F.chart source pred.1 ((P.next ^ 2) source).1 hunit,
    Erdos957Case4NoThree.terminalEdgePairCoord_eq_aligned
      F.chart source pred.1 (P.next source).1 hunit]
  exact ⟨hx, hy⟩

/-- Reflected successor-side analogue of
`previous_terminal_away_second_increment_gt`. -/
private lemma next_reflected_away_second_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1) :
    let p₁ := (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical (P.next⁻¹ source).1
    let p₂ := (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical (((P.next⁻¹) ^ 2) source).1
    (399 / 400 : ℝ) < p₂ 0 - p₁ 0 ∧
      |p₂ 1 - p₁ 1| ≤ (p₂ 0 - p₁ 0) / 10 := by
  let succ := P.next source
  let e : ℝ × ℝ :=
    ((F.chart.coord source succ.1).1,
      -((F.chart.coord source succ.1).2))
  obtain ⟨hr0, -, -, -⟩ := F.rightFlatAngles source hi
  obtain ⟨hl0, hl1, -, -⟩ := F.leftFlatAngles source hi
  have hrightNorm :
      (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
          (F.chart.rightOrbitCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source succ.1 source.1
    rw [show dist (succ.1 : Point) (source.1 : Point) = 1 by
      simpa [succ, dist_comm] using hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, one_pow] at hs
    simpa [succ, CyclicHullData.AlignedChartData.rightOrbitCoord] using hs
  have hrightRadius : F.rightRadius source 0 = 1 := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.rightAngle source 0)
    have hrad := F.rightRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.rightRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.rightRadius source 0 ^ 2 *
            (Real.sin (F.rightAngle source 0) ^ 2 +
              Real.cos (F.rightAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
            (F.chart.rightOrbitCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hrightNorm
    nlinarith
  have he : e =
      (Real.cos (-F.rightAngle source 0),
        Real.sin (-F.rightAngle source 0)) := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hrightRadius] at hx hy
    norm_num at hx hy
    simp only [e, succ, CyclicHullData.AlignedChartData.rightOrbitCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hangle :
      |F.leftAngle source 1 + F.rightAngle source 0| ≤ Real.pi / 45 := by
    have hl1abs : |F.leftAngle source 1| ≤
        |F.leftAngle source 1 - F.leftAngle source 0| +
          |F.leftAngle source 0| := by
      calc
        _ = |(F.leftAngle source 1 - F.leftAngle source 0) +
            F.leftAngle source 0| := by congr 1 <;> ring
        _ ≤ _ := abs_add_le _ _
    have hsum := abs_add_le (F.leftAngle source 1)
      (F.rightAngle source 0)
    nlinarith [Real.pi_pos]
  have hp := Erdos957Case4NoThree.pairEdgeTransform_polar he
    (F.leftPolar source (1 : Fin 4))
  have hp' : Erdos957Locality.IsPolarEdge
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.leftOrbitReflectedCoord P source 1))
      (Erdos957Case4NoThree.pairEdgeTransform e
        (F.chart.leftOrbitReflectedCoord P source 2))
      (F.leftRadius source 1)
      (F.leftAngle source 1 + F.rightAngle source 0) := by
    simpa [sub_eq_add_neg] using hp
  have hx :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one source 1) hangle hp'.1
  let θ := F.leftAngle source 1 + F.rightAngle source 0
  have hsinNeg :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
      hangle
  have hangleNeg : |-θ| ≤ Real.pi / 45 := by
    simpa only [abs_neg] using hangle
  have hsinPos :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
      hangleNeg
  have habsSin : |Real.sin θ| ≤ Real.cos θ / 10 := by
    apply abs_le.mpr
    constructor
    · dsimp only [θ] at *
      linarith
    · simpa only [Real.sin_neg, Real.cos_neg, neg_neg] using hsinPos
  have hrNonneg : 0 ≤ F.leftRadius source 1 := by
    linarith [F.leftRadius_ge_one source 1]
  have hm := mul_le_mul_of_nonneg_left habsSin hrNonneg
  have hy :
      |(Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.leftOrbitReflectedCoord P source 2)).2 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.leftOrbitReflectedCoord P source 1)).2| ≤
        ((Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.leftOrbitReflectedCoord P source 2)).1 -
          (Erdos957Case4NoThree.pairEdgeTransform e
            (F.chart.leftOrbitReflectedCoord P source 1)).1) / 10 := by
    have hxPolar := hp'.1
    have hyPolar := hp'.2
    rw [hyPolar, hxPolar, abs_mul, abs_of_nonneg hrNonneg]
    dsimp only [θ] at hm
    nlinarith
  dsimp only
  rw [Erdos957Case4NoThree.reflectedSuccessorCoord_eq_aligned
      F.chart source hunit (((P.next⁻¹) ^ 2) source).1,
    Erdos957Case4NoThree.reflectedSuccessorCoord_eq_aligned
      F.chart source hunit (P.next⁻¹ source).1]
  simpa only [e, succ,
    CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
    pow_one,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] using And.intro hx hy

/-- The second away hull edge advances almost one unit in every retained
Case-2 normalized frame.  This is the reflection-safe formula wrapper around
the two orientation-specific increment lemmas above. -/
lemma Case2SecondaryFormula.away_second_increment_gt
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source) :
    (399 / 400 : ℝ) <
      (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side 1).1) 0 -
      (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side 0).1) 0 := by
  cases D.edgeFrame_spec with
  | previous hside hunit hframe =>
      rw [hside]
      rw [hframe]
      norm_num [Erdos957Case4NoThree.awayHullVertex]
      exact (previous_terminal_away_second_increment_gt F source hi hunit).1
  | next hside hunit hframe =>
      rw [hside]
      rw [hframe]
      norm_num [Erdos957Case4NoThree.awayHullVertex]
      exact (next_reflected_away_second_increment_gt F source hi hunit).1

/-- The actual second away edge is not only longitudinally positive in the
retained rigid frame; its transverse increment has absolute slope at most
`1/10`.  This is the formula-level form used by chart-sign transport. -/
lemma Case2SecondaryFormula.away_second_edge_bounds
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source) :
    let p₁ := D.edgeFrame.toCanonical
      (Erdos957Case4NoThree.awayHullVertex P source D.side 0).1
    let p₂ := D.edgeFrame.toCanonical
      (Erdos957Case4NoThree.awayHullVertex P source D.side 1).1
    (399 / 400 : ℝ) < p₂ 0 - p₁ 0 ∧
      |p₂ 1 - p₁ 1| ≤ (p₂ 0 - p₁ 0) / 10 := by
  cases D.edgeFrame_spec with
  | previous hside hunit hframe =>
      rw [hside, hframe]
      norm_num [Erdos957Case4NoThree.awayHullVertex]
      exact previous_terminal_away_second_increment_gt F source hi hunit
  | next hside hunit hframe =>
      rw [hside, hframe]
      norm_num [Erdos957Case4NoThree.awayHullVertex]
      exact next_reflected_away_second_increment_gt F source hi hunit

/-- The three possible squared-distance fingerprints of a canonical Case-2
secondary, measured from the incident endpoint and from its own source. -/
private lemma case2_secondary_incident_source_sq_distance_cases
    {q : Erdos957Cases24.Point}
    (hq : q = Erdos957Cases24.Case2.w ∨
      q = Erdos957Cases24.Case2.wNext ∨
      q = Erdos957Cases24.Case2.e) :
    (dist q Erdos957Cases24.Case2.uPrev ^ 2 = 4 ∧
        dist q Erdos957Cases24.Case2.u ^ 2 = 3) ∨
      (dist q Erdos957Cases24.Case2.uPrev ^ 2 = 7 ∧
        dist q Erdos957Cases24.Case2.u ^ 2 = 4) ∨
      (dist q Erdos957Cases24.Case2.uPrev ^ 2 = 7 ∧
        dist q Erdos957Cases24.Case2.u ^ 2 = 3) := by
  rcases hq with rfl | rfl | rfl
  · left
    constructor <;>
      rw [Erdos957Cases24.dist_sq_eq_coordinates] <;>
      simp only [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.w,
        Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one] <;>
      nlinarith [Erdos957Cases24.sqrtThree_sq]
  · right; left
    constructor <;>
      rw [Erdos957Cases24.dist_sq_eq_coordinates] <;>
      simp only [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.wNext,
        Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one] <;>
      nlinarith [Erdos957Cases24.sqrtThree_sq]
  · right; right
    constructor <;>
      rw [Erdos957Cases24.dist_sq_eq_coordinates] <;>
      simp only [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.e,
        Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one] <;>
      nlinarith [Erdos957Cases24.sqrtThree_sq]

/-- The elementary two-circle classification behind the adjacent
Case-2/Case-2 branch.  A unit hull source which is at distance `sqrt 3`
from the canonical `wNext` point is either the forbidden straight
continuation or the canonical middle point. -/
lemma eq_case2_v_or_uNext_of_dist_u_one_dist_wNext_sqrtThree
    {z : Erdos957Cases24.Point}
    (hu : dist Erdos957Cases24.Case2.u z = 1)
    (hw : dist Erdos957Cases24.Case2.wNext z =
      Erdos957Cases24.sqrtThree) :
    z = Erdos957Cases24.Case2.v ∨
      z = Erdos957Cases24.Case2.uNext := by
  have huSq := congrArg (fun r : ℝ ↦ r ^ 2) hu
  have hwSq := congrArg (fun r : ℝ ↦ r ^ 2) hw
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at huSq hwSq
  simp only [Erdos957Cases24.Case2.u,
    Erdos957Cases24.Case2.wNext,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one,
    one_pow, Erdos957Cases24.sqrtThree_sq] at huSq hwSq
  have hline : z 0 - Erdos957Cases24.sqrtThree * z 1 = 1 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hfactor : z 1 *
      (Erdos957Cases24.sqrtThree + 2 * z 1) = 0 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  rcases mul_eq_zero.mp hfactor with hy | hy
  · right
    apply Erdos957Cases24.point_ext
    · simpa [hy] using hline
    · simpa [Erdos957Cases24.Case2.uNext] using hy
  · left
    have hy' : z 1 = -(Erdos957Cases24.sqrtThree / 2) := by
      linarith
    have hx' : z 0 = -(1 / 2 : ℝ) := by
      rw [hy'] at hline
      nlinarith [Erdos957Cases24.sqrtThree_sq]
    exact Erdos957Cases24.point_ext
      (by simpa [Erdos957Cases24.Case2.v] using hx')
      (by simpa [Erdos957Cases24.Case2.v] using hy')

/-- A shallow-cone direct competitor is automatically on or before the
rightmost point of the unit circle about the forced target `e`. -/
lemma Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hadj : (unitDistanceGraph A).Adj t v) :
    (D.edgeFrame.toCanonical t) 0 ≤ 5 / 2 := by
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hunit : dist (D.edgeFrame.toCanonical t)
      (D.edgeFrame.toCanonical v) = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have hsq := Erdos957Cases24.dist_sq_eq_coordinates
    (D.edgeFrame.toCanonical t) (D.edgeFrame.toCanonical v)
  rw [hunit, he] at hsq
  simp only [Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] at hsq
  nlinarith [sq_nonneg
    ((D.edgeFrame.toCanonical t) 1 + Erdos957Cases24.sqrtThree / 2)]

/-- Once the shallow-cone screen forces a direct competitor's common
Case-2 target to `e`, the competitor lies strictly above that target as
soon as its normalized horizontal coordinate has not passed `5/2`.
This is the vertical premise used by the formula-derived Figure-13 core. -/
lemma Case2SecondaryFormula.competitor_above_target_of_shallow_cone
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hx : (D.edgeFrame.toCanonical t) 0 ≤ 5 / 2)
    (hadj : (unitDistanceGraph A).Adj t v) :
    (D.edgeFrame.toCanonical v) 1 <
      (D.edgeFrame.toCanonical t) 1 := by
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hsqrt : 1 < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  rw [he]
  simp only [Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_one]
  linarith

/-- The preceding upper bound is intrinsic to the direct incidence, so the
above-target conclusion has a convenient premise-minimal form. -/
lemma Case2SecondaryFormula.competitor_above_target_of_shallow_cone'
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hadj : (unitDistanceGraph A).Adj t v) :
    (D.edgeFrame.toCanonical v) 1 <
      (D.edgeFrame.toCanonical t) 1 :=
  Case2SecondaryFormula.competitor_above_target_of_shallow_cone D hcone
    (Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
      D hcone hadj) hadj

/-- A direct competitor on the incoming half of the outgoing unit circle is
impossible.  One-separation from the retained outer point `b` gives `x ≥ 1`;
the forced `e` unit-circle equation, `x ≤ 3/2`, strict support, and the
shallow cone then have no simultaneous solution. -/
lemma Case2SecondaryFormula.no_direct_competitor_of_shallow_cone_of_fst_le
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (htHull : t ∈ P.H)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hx : (D.edgeFrame.toCanonical t) 0 ≤ 3 / 2)
    (hy : (D.edgeFrame.toCanonical t) 1 < 0)
    (hadj : (unitDistanceGraph A).Adj t v) : False := by
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hneOuter : t ≠ D.outer := by
    intro h
    apply D.outer_not_hull
    simpa [h] using htHull
  have hsep : 1 ≤ dist (t : Point) (D.outer : Point) :=
    hA t t.property D.outer D.outer.property
      (fun h ↦ hneOuter (Subtype.ext h))
  have hsepCoord : 1 ≤ dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.b := by
    rw [← D.outer_edge_coordinate, D.edgeFrame.dist_eq]
    exact hsep
  have hunitCoord : dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.e = 1 := by
    rw [← he, D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have hunitSq := Erdos957Cases24.dist_sq_eq_coordinates
    (D.edgeFrame.toCanonical t) Erdos957Cases24.Case2.e
  rw [hunitCoord] at hunitSq
  have hsepSq : 1 ≤ dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.b ^ 2 := by
    nlinarith [dist_nonneg (x := D.edgeFrame.toCanonical t)
      (y := Erdos957Cases24.Case2.b)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsepSq
  simp only [Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at hunitSq hsepSq
  have hxLower : (1 : ℝ) ≤ (D.edgeFrame.toCanonical t) 0 := by
    nlinarith [hunitSq, hsepSq]
  have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  let x := (D.edgeFrame.toCanonical t) 0
  let y := (D.edgeFrame.toCanonical t) 1
  let a := y + Erdos957Cases24.sqrtThree / 2
  have hxProd : 0 ≤ (x - 1) * (3 / 2 - x) := by
    exact mul_nonneg (by dsimp [x]; linarith) (by dsimp [x]; linarith)
  have haPos : 0 < a := by
    dsimp [a, x, y] at ⊢
    linarith
  have haLt : a < Erdos957Cases24.sqrtThree / 2 := by
    dsimp [a, y]
    linarith
  have haSumPos : 0 < Erdos957Cases24.sqrtThree / 2 + a := by
    linarith [Erdos957Cases24.sqrtThree_pos]
  have haProd : 0 <
      (Erdos957Cases24.sqrtThree / 2 - a) *
        (Erdos957Cases24.sqrtThree / 2 + a) :=
    mul_pos (sub_pos.mpr haLt) haSumPos
  dsimp [x, y, a] at hxProd haProd
  nlinarith [hunitSq, hxProd, haProd,
    Erdos957Cases24.sqrtThree_sq]

/-- Every hull direct competitor in the outgoing shallow cone lies strictly
past horizontal coordinate `2` in the Case-2 rigid chart.  This is the
one-competitor form of the outer-`b` separation argument and is useful in
the remaining mixed exceptional triple branches. -/
lemma Case2SecondaryFormula.direct_competitor_fst_gt_two_of_shallow_cone
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (htHull : t ∈ P.H)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hy : (D.edgeFrame.toCanonical t) 1 < 0)
    (hadj : (unitDistanceGraph A).Adj t v) :
    (2 : ℝ) < (D.edgeFrame.toCanonical t) 0 := by
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hneOuter : t ≠ D.outer := by
    intro h
    apply D.outer_not_hull
    simpa [h] using htHull
  have hsep : 1 ≤ dist (t : Point) (D.outer : Point) :=
    hA t t.property D.outer D.outer.property
      (fun h ↦ hneOuter (Subtype.ext h))
  have hsepCoord : 1 ≤ dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.b := by
    rw [← D.outer_edge_coordinate, D.edgeFrame.dist_eq]
    exact hsep
  have hunitCoord : dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.e = 1 := by
    rw [← he, D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have hunitSq := Erdos957Cases24.dist_sq_eq_coordinates
    (D.edgeFrame.toCanonical t) Erdos957Cases24.Case2.e
  rw [hunitCoord] at hunitSq
  have hsepSq : 1 ≤ dist (D.edgeFrame.toCanonical t)
      Erdos957Cases24.Case2.b ^ 2 := by
    nlinarith [dist_nonneg (x := D.edgeFrame.toCanonical t)
      (y := Erdos957Cases24.Case2.b)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsepSq
  simp only [Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at hunitSq hsepSq
  have hxLower : (1 : ℝ) ≤ (D.edgeFrame.toCanonical t) 0 := by
    nlinarith [hunitSq, hsepSq]
  have hxUpper : (D.edgeFrame.toCanonical t) 0 ≤ 5 / 2 :=
    Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
      D hcone hadj
  have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hyLower : -(1 / 2 : ℝ) ≤ (D.edgeFrame.toCanonical t) 1 := by
    linarith
  have haPos : 0 < (D.edgeFrame.toCanonical t) 1 +
      Erdos957Cases24.sqrtThree / 2 := by
    linarith
  have haLt : (D.edgeFrame.toCanonical t) 1 +
      Erdos957Cases24.sqrtThree / 2 <
        Erdos957Cases24.sqrtThree / 2 := by
    linarith
  have haSumPos : 0 < Erdos957Cases24.sqrtThree / 2 +
      ((D.edgeFrame.toCanonical t) 1 +
        Erdos957Cases24.sqrtThree / 2) := by
    linarith [Erdos957Cases24.sqrtThree_pos]
  have haProd : 0 <
      (Erdos957Cases24.sqrtThree / 2 -
          ((D.edgeFrame.toCanonical t) 1 +
            Erdos957Cases24.sqrtThree / 2)) *
        (Erdos957Cases24.sqrtThree / 2 +
          ((D.edgeFrame.toCanonical t) 1 +
            Erdos957Cases24.sqrtThree / 2)) :=
    mul_pos (sub_pos.mpr haLt) haSumPos
  by_contra h
  have hxLeTwo : (D.edgeFrame.toCanonical t) 0 ≤ 2 := le_of_not_gt h
  have hxProd : 0 ≤ ((D.edgeFrame.toCanonical t) 0 - 1) *
      (2 - (D.edgeFrame.toCanonical t) 0) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hunitSq, haProd, hxProd,
    Erdos957Cases24.sqrtThree_sq]

/-- The incident cyclic partner is not itself a direct competitor to the
Case-2 secondary.  The proof uses the exact reflection-safe endpoint
coordinate rather than any global chart alignment. -/
lemma Case2SecondaryFormula.not_adj_incident_partner
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    ¬ (unitDistanceGraph A).Adj
      (cyclicSideVertex P source D.side) v := by
  intro hadj
  have hunit : dist Erdos957Cases24.Case2.uPrev
      (D.edgeFrame.toCanonical v) = 1 := by
    rw [← D.side_edge_coordinate]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  exact case2_uPrev_not_unit_secondary
    (D.edgeFrame.toCanonical v)
    (by
      rcases D.target_edge_coordinate_cases with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) hunit

/-- Every canonical Case-2 secondary lies within Euclidean distance two
of its emitting source.  This is the metric form of the retained two-edge
path and is useful even when the competing role is itself exceptional. -/
lemma Case2SecondaryFormula.source_target_dist_le_two
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    dist (source.1 : Point) (v : Point) ≤ 2 := by
  have hsource : D.edgeFrame.toCanonical source.1 =
      Erdos957Cases24.Case2.u := by
    rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
  rw [← D.edgeFrame.dist_eq, hsource]
  rcases D.target_edge_coordinate_cases with h | h | h <;> rw [h]
  all_goals
    have hsq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u
      (D.edgeFrame.toCanonical v)
    rw [h] at hsq
    simp only [Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hsq ⊢
    nlinarith [Erdos957Cases24.sqrtThree_sq,
      dist_nonneg (x := Erdos957Cases24.Case2.u)
        (y := D.edgeFrame.toCanonical v)]

/-- Every actual configuration point other than the normalized source and
its incident cyclic partner is strictly below the Case-2 supporting edge.
This packages the endpoint bookkeeping needed after a cyclic-orbit split. -/
lemma Case2SecondaryFormula.coordinate_snd_neg_of_ne_endpoints
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hneSource : t ≠ source.1)
    (hneSide : t ≠ cyclicSideVertex P source D.side) :
    (D.edgeFrame.toCanonical t) 1 < 0 := by
  apply D.strict_support (D.edgeFrame.toCanonical t)
  · exact Finset.mem_image.mpr ⟨t, t.property, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro ht
      apply hneSide
      apply Subtype.ext
      apply D.edgeFrame.toCanonical.injective
      rw [D.side_edge_coordinate]
      exact ht
    · intro ht
      apply hneSource
      apply Subtype.ext
      apply D.edgeFrame.toCanonical.injective
      have hsource : D.edgeFrame.toCanonical source.1 =
          Erdos957Cases24.Case2.u := by
        rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
      rw [hsource]
      exact ht

/-- Reflection-safe prefix control in the exact rigid frame retained by a
Case-2 secondary descriptor.  This is the `SideNormalizedFrameSpec` form of
the production Case-4 prefix theorem, avoiding reconstruction of the
dependent two-extreme witness which the formula record intentionally
erases. -/
lemma Case2SecondaryFormula.away_prefix_bounds
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := D.edgeFrame.toCanonical
      (Erdos957Case4NoThree.awayHullVertex P source D.side k).1
    z 1 < 0 ∧
      ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
  have hmetric :
      ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
          (D.edgeFrame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 0 ∧
        -(D.edgeFrame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 1 ≤
          (D.edgeFrame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 0 / 10 := by
    cases D.edgeFrame_spec with
    | previous hside hunit hframe =>
        rw [hside]
        simp only [Erdos957Case4NoThree.awayHullVertex]
        rw [hframe]
        exact Erdos957Case4NoThree.previous_terminal_away_prefix_bounds
          F source hi hunit k
    | next hside hunit hframe =>
        rw [hside]
        simp only [Erdos957Case4NoThree.awayHullVertex]
        rw [hframe]
        exact Erdos957Case4NoThree.next_reflected_away_prefix_bounds
          F source hi hunit k
  let z := D.edgeFrame.toCanonical
    (Erdos957Case4NoThree.awayHullVertex P source D.side k).1
  have hzMem : z ∈ D.edgeFrame.image A := by
    exact Finset.mem_image.mpr
      ⟨(Erdos957Case4NoThree.awayHullVertex P source D.side k).1,
        (Erdos957Case4NoThree.awayHullVertex P source D.side k).1.property,
        rfl⟩
  have hzNotEndpoints :
      z ∉ ({Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u} : Finset Point) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hz
      have hx := hmetric.1
      have hpos : (0 : ℝ) <
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by positivity
      change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 at hx
      rw [show z = Erdos957Cases24.Case2.uPrev by exact hz] at hx
      norm_num [Erdos957Cases24.Case2.uPrev] at hx
      linarith
    · intro hz
      have hx := hmetric.1
      have hpos : (0 : ℝ) <
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by positivity
      change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 at hx
      rw [show z = Erdos957Cases24.Case2.u by exact hz] at hx
      norm_num [Erdos957Cases24.Case2.u] at hx
      linarith
  exact ⟨D.strict_support z hzMem hzNotEndpoints, hmetric⟩

lemma Case2SecondaryFormula.away_third_fst_gt_five_halves
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) :
    (5 / 2 : ℝ) <
      (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side 2).1) 0 := by
  have h := (Case2SecondaryFormula.away_prefix_bounds D F hi 2).2.1
  norm_num at h ⊢
  linarith

/-- The metric prefix cone with denominator `10` implies the weaker
denominator-`5` cone used by the exceptional collision classifier. -/
lemma Case2SecondaryFormula.away_cone_div_five
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) (k : Fin 3) :
    -(D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 1 ≤
      (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 0 / 5 := by
  have h := Case2SecondaryFormula.away_prefix_bounds D F hi k
  have hpos : (0 : ℝ) <
      (D.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source D.side k).1) 0 := by
    have hfac : (0 : ℝ) <
        ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by positivity
    linarith [h.2.1]
  linarith [h.2.2]

/-- The non-hull-proxy direct form at the second away source has the cyclic
association of the retained Case-2 side.  This is the reflection-safe form
of the elementary equilateral picture: in the terminal chart the canonical
and aligned oriented areas have the same sign, while in the reflected
successor chart they have opposite signs. -/
lemma Case2SecondaryFormula.outer_association_of_shallow_position
    {source t : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (htx : (2 : ℝ) * (399 / 400 : ℝ) <
      (D.edgeFrame.toCanonical t.1) 0)
    (hty : (D.edgeFrame.toCanonical t.1) 1 < 0)
    (hcone : -(D.edgeFrame.toCanonical t.1) 1 ≤
      (D.edgeFrame.toCanonical t.1) 0 / 10)
    {association : ArrivalAssociation}
    (hadj : (unitDistanceGraph A).Adj t.1 v)
    (O : OuterDirectFormula F.chart t v association) :
    association = cyclicSideAssociation D.side := by
  let z := D.edgeFrame.toCanonical t.1
  let r := D.edgeFrame.toCanonical O.proxy
  change (2 : ℝ) * (399 / 400 : ℝ) < z 0 at htx
  change z 1 < 0 at hty
  change -z 1 ≤ z 0 / 10 at hcone
  have hconeFive : -z 1 ≤ z 0 / 5 := by
    have hzPos : 0 < z 0 := by linarith
    linarith
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hconeFive hadj
  have hproxyNeSource : O.proxy ≠ source.1 := by
    intro h
    apply O.proxy_not_hull
    simpa [h] using source.property
  have hproxyNeSide : O.proxy ≠ cyclicSideVertex P source D.side := by
    intro h
    apply O.proxy_not_hull
    rw [h]
    cases hside : D.side with
    | previous =>
        simpa [cyclicSideVertex, hside] using (P.next⁻¹ source).property
    | next =>
        simpa [cyclicSideVertex, hside] using (P.next source).property
  have hry : r 1 < 0 := by
    dsimp [r]
    exact
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.coordinate_snd_neg_of_ne_endpoints
        D hproxyNeSource hproxyNeSide
  have hte : dist z Erdos957Cases24.Case2.e = 1 := by
    rw [← he]
    dsimp [z]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have htr : dist z r = 1 := by
    dsimp [z, r]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using O.source_proxy
  have her : dist Erdos957Cases24.Case2.e r = 1 := by
    rw [← he]
    dsimp [r]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using O.target_proxy
  have hcanonical : Erdos957GeometryCore.cross (r - z)
      (Erdos957Cases24.Case2.e - z) < 0 :=
    case2_e_equilateral_proxy_cross_neg htx hty hcone hte htr her hry
  have hcanonicalFrame : Erdos957GeometryCore.cross
      (D.edgeFrame.toCanonical O.proxy - D.edgeFrame.toCanonical t.1)
      (D.edgeFrame.toCanonical v - D.edgeFrame.toCanonical t.1) < 0 := by
    rw [he]
    exact hcanonical
  have haligned := Erdos957Case3SameSide.crossFrom_coord_eq_neg_cross
    F.chart t t.1 O.proxy v
  cases D.edgeFrame_spec with
  | previous hside hunit hframe =>
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_terminalUnitEdgeRigidChart
          (P.next⁻¹ source).1.1 source.1.1 t.1 O.proxy v hunit
      rw [← hframe] at hrigid
      have hglobal : Erdos957GeometryCore.cross
          (O.proxy - t.1) (v - t.1) > 0 := by
        have hrigid' : Erdos957GeometryCore.cross
              (D.edgeFrame.toCanonical O.proxy -
                D.edgeFrame.toCanonical t.1)
              (D.edgeFrame.toCanonical v -
                D.edgeFrame.toCanonical t.1) =
            -Erdos957GeometryCore.cross (O.proxy - t.1) (v - t.1) := by
          change Erdos957GeometryCore.cross
              (D.edgeFrame.toCanonical O.proxy -
                D.edgeFrame.toCanonical t.1)
              (D.edgeFrame.toCanonical v -
                D.edgeFrame.toCanonical t.1) =
            -Erdos957GeometryCore.cross (O.proxy - t.1) (v - t.1) at hrigid
          exact hrigid
        linarith
      have halignedNeg : Erdos957Case3General.crossFrom
          (F.chart.coord t t.1) (F.chart.coord t O.proxy)
          (F.chart.coord t v) < 0 := by
        rw [haligned]
        linarith
      rcases O.association_side with h | h
      · rw [h.2, hside]
        rfl
      · linarith [h.1, halignedNeg]
  | next hside hunit hframe =>
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_reflectedSuccessorUnitEdgeRigidChart
          P source hunit t.1 O.proxy v
      rw [← hframe] at hrigid
      have hglobal : Erdos957GeometryCore.cross
          (O.proxy - t.1) (v - t.1) < 0 := by
        have hrigid' : Erdos957GeometryCore.cross
              (D.edgeFrame.toCanonical O.proxy -
                D.edgeFrame.toCanonical t.1)
              (D.edgeFrame.toCanonical v -
                D.edgeFrame.toCanonical t.1) =
            Erdos957GeometryCore.cross (O.proxy - t.1) (v - t.1) := by
          change Erdos957GeometryCore.cross
              (D.edgeFrame.toCanonical O.proxy -
                D.edgeFrame.toCanonical t.1)
              (D.edgeFrame.toCanonical v -
                D.edgeFrame.toCanonical t.1) =
            Erdos957GeometryCore.cross (O.proxy - t.1) (v - t.1) at hrigid
          exact hrigid
        linarith
      have halignedPos : 0 < Erdos957Case3General.crossFrom
          (F.chart.coord t t.1) (F.chart.coord t O.proxy)
          (F.chart.coord t v) := by
        rw [haligned]
        linarith
      rcases O.association_side with h | h
      · linarith [h.1, halignedPos]
      · rw [h.2, hside]
        rfl

/-- Specialization of `outer_association_of_shallow_position` to the
second vertex continuing away from the retained incident edge. -/
lemma Case2SecondaryFormula.outer_association_at_away_second
    {source t : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source)
    (ht : t = Erdos957Case4NoThree.awayHullVertex P source D.side 1)
    {association : ArrivalAssociation}
    (hadj : (unitDistanceGraph A).Adj t.1 v)
    (O : OuterDirectFormula F.chart t v association) :
    association = cyclicSideAssociation D.side := by
  have hzBounds :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_prefix_bounds
      D F hi 1
  apply Case2SecondaryFormula.outer_association_of_shallow_position
    (t := t) D F
  · rw [ht]
    simpa using hzBounds.2.1
  · rw [ht]
    exact hzBounds.1
  · rw [ht]
    exact hzBounds.2.2
  · exact hadj
  · exact O

/-- The two-extreme direct form at the second away source has the same
cyclic association.  Choosing its other hull neighbor on the outward side
would put that neighbor at the third away vertex, which the checked
three-step shallow-cone estimate proves is not unit-adjacent to the Case-2
secondary target. -/
lemma Case2SecondaryFormula.paired_association_at_away_second
    {source t : {p // p ∈ P.H}} {v middle : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source)
    (ht : t = Erdos957Case4NoThree.awayHullVertex P source D.side 1)
    {association : ArrivalAssociation}
    (T : TwoExtremeCyclicWitness P t middle)
    (htarget : v = middle)
    (hassociation : association = cyclicSideAssociation T.side) :
    association = cyclicSideAssociation D.side := by
  subst t
  have hsideAdjMiddle : (unitDistanceGraph A).Adj
      (cyclicSideVertex P
        (Erdos957Case4NoThree.awayHullVertex P source D.side 1)
        T.side) middle :=
    (unitDistanceGraph A).adj_symm T.side_adjacent
  have hsideAdj : (unitDistanceGraph A).Adj
      (cyclicSideVertex P
        (Erdos957Case4NoThree.awayHullVertex P source D.side 1)
        T.side) v :=
    @Eq.ndrec (Vertex A) middle
      (fun x => (unitDistanceGraph A).Adj
        (cyclicSideVertex P
          (Erdos957Case4NoThree.awayHullVertex P source D.side 1)
          T.side) x)
      hsideAdjMiddle v htarget.symm
  cases hs : D.side <;> cases htSide : T.side
  · simpa [hassociation, htSide]
  · exfalso
    have hvertex : cyclicSideVertex P
        (Erdos957Case4NoThree.awayHullVertex P source D.side 1) T.side =
        Erdos957Case4NoThree.awayHullVertex P source D.side 2 := by
      simp [hs, htSide, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, pow_succ]
    rw [hvertex] at hsideAdj
    exact
      (Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_shallow_cone_and_fst_gt_five_halves
        D
        (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_cone_div_five
          D F hi 2)
        (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_third_fst_gt_five_halves
          D F hi)
        hsideAdj).elim
  · exfalso
    have hvertex : cyclicSideVertex P
        (Erdos957Case4NoThree.awayHullVertex P source D.side 1) T.side =
        Erdos957Case4NoThree.awayHullVertex P source D.side 2 := by
      simp [hs, htSide, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, pow_succ]
    rw [hvertex] at hsideAdj
    exact
      (Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_shallow_cone_and_fst_gt_five_halves
        D
        (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_cone_div_five
          D F hi 2)
        (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_third_fst_gt_five_halves
          D F hi)
        hsideAdj).elim
  · simpa [hassociation, htSide]

/-- The singleton direct form at the second away source also has the cyclic
association.  This proof compares the two retained charts through their
common incoming hull edge.  It therefore needs only the abstract aligned
frame data, not an additional global chart-transition axiom. -/
lemma Case2SecondaryFormula.singleton_association_at_away_second
    {source t : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source)
    (hit : P.IsFlat t)
    (ht : t = Erdos957Case4NoThree.awayHullVertex P source D.side 1)
    {association : ArrivalAssociation} {middleCoord : ℝ × ℝ}
    (hadj : (unitDistanceGraph A).Adj t.1 v)
    (htarget : F.chart.coord t v = middleCoord)
    (hassociation : association = horizontalAssociation middleCoord.1) :
    association = cyclicSideAssociation D.side := by
  subst t
  let t₀ := Erdos957Case4NoThree.awayHullVertex P source D.side 0
  let t₁ := Erdos957Case4NoThree.awayHullVertex P source D.side 1
  let p₀ := D.edgeFrame.toCanonical t₀.1
  let p₁ := D.edgeFrame.toCanonical t₁.1
  let a : ℝ := p₁ 0 - p₀ 0
  let b : ℝ := p₁ 1 - p₀ 1
  let x : ℝ := (D.edgeFrame.toCanonical v) 0 - p₁ 0
  let y : ℝ := (D.edgeFrame.toCanonical v) 1 - p₁ 1
  have hab := Case2SecondaryFormula.away_second_edge_bounds D F hi
  change (399 / 400 : ℝ) < a ∧ |b| ≤ a / 10 at hab
  have ha : 0 < a := by linarith [hab.1]
  have hcone := Case2SecondaryFormula.away_cone_div_five D F hi 1
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hp₁x := (Case2SecondaryFormula.away_prefix_bounds D F hi 1).2.1
  have hx : x ≤ -(99 / 200 : ℝ) := by
    dsimp [x, p₁, t₁]
    rw [he]
    simp only [Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero]
    norm_num at hp₁x ⊢
    linarith
  have hunit : dist p₁ (D.edgeFrame.toCanonical v) = 1 := by
    dsimp [p₁, t₁]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have hunitSq := Erdos957Cases24.dist_sq_eq_coordinates
    p₁ (D.edgeFrame.toCanonical v)
  rw [hunit] at hunitSq
  have hy : |y| ≤ 1 := by
    dsimp [y]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  cases D.edgeFrame_spec with
  | previous hside hsideUnit hframe =>
      have hprev : P.next⁻¹ t₁ = t₀ := by
        simp [t₀, t₁, hside, Erdos957Case4NoThree.awayHullVertex,
          pow_succ]
      let c : ℝ := -(F.chart.coord t₁ t₀.1).1
      let d : ℝ := (F.chart.coord t₁ t₀.1).2
      let X : ℝ := (F.chart.coord t₁ v).1
      let Y : ℝ := (F.chart.coord t₁ v).2
      obtain ⟨hl0, -, -, -⟩ := F.leftFlatAngles t₁ hit
      have hl0' : |F.leftAngle t₁ 0| ≤ Real.pi / 45 := by
        nlinarith [Real.pi_pos]
      have hcdRaw := polar_edge_positive_abs_slope
        (F.leftRadius_ge_one t₁ 0) hl0' (F.leftPolar t₁ 0)
      have hcd : 0 < c ∧ |d| ≤ c / 10 := by
        have hzero : F.chart.leftOrbitReflectedCoord P t₁ 0 = (0, 0) :=
          F.chart.leftOrbitReflectedCoord_zero P t₁
        have hone : F.chart.leftOrbitReflectedCoord P t₁ 1 =
            (-(F.chart.coord t₁ t₀.1).1,
              (F.chart.coord t₁ t₀.1).2) := by
          simp [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
            hprev]
        norm_num [hzero, hone] at hcdRaw
        simpa [c, d] using hcdRaw
      have hdotRaw := rigid_aligned_dot_displacements
        D.edgeFrame F.chart t₁ t₁.1 t₀.1 v
      have hdot : a * x + b * y = c * X - d * Y := by
        dsimp only at hdotRaw
        rw [F.chart.coord_source] at hdotRaw
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hdotRaw ⊢
        linarith
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_terminalUnitEdgeRigidChart
          (P.next⁻¹ source).1.1 source.1.1 t₁.1 t₀.1 v hsideUnit
      rw [← hframe] at hrigid
      have hrigid' : Erdos957GeometryCore.cross
          (D.edgeFrame.toCanonical t₀.1 -
            D.edgeFrame.toCanonical t₁.1)
          (D.edgeFrame.toCanonical v -
            D.edgeFrame.toCanonical t₁.1) =
          -Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1) := by
        change Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
          -Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1)
          at hrigid
        exact hrigid
      have haligned := F.chart.cross_displacements t₁ t₁.1 t₀.1 v
      have hcross : a * y - b * x = c * Y + d * X := by
        have hEq := hrigid'.trans haligned.symm
        simp only [Erdos957GeometryCore.cross, PiLp.sub_apply,
          CyclicHullData.pairCross, CyclicHullData.pairSub] at hEq
        rw [F.chart.coord_source] at hEq
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hEq ⊢
        linarith
      have hX : X < 0 := fst_neg_of_shallow_edge_chart_change
        ha hcd.1 hab.2 hcd.2 hx hy hdot hcross
      rw [hassociation]
      have hm : middleCoord.1 < 0 := by
        rw [← htarget]
        exact hX
      simp [horizontalAssociation, cyclicSideAssociation, hside, le_of_lt hm]
  | next hside hsideUnit hframe =>
      have hnext : P.next t₁ = t₀ := by
        simp [t₀, t₁, hside, Erdos957Case4NoThree.awayHullVertex,
          pow_succ]
      let c : ℝ := (F.chart.coord t₁ t₀.1).1
      let d : ℝ := (F.chart.coord t₁ t₀.1).2
      let X : ℝ := -(F.chart.coord t₁ v).1
      let Y : ℝ := (F.chart.coord t₁ v).2
      obtain ⟨hr0, -, -, -⟩ := F.rightFlatAngles t₁ hit
      have hr0' : |F.rightAngle t₁ 0| ≤ Real.pi / 45 := by
        nlinarith [Real.pi_pos]
      have hcdRaw := polar_edge_positive_abs_slope
        (F.rightRadius_ge_one t₁ 0) hr0' (F.rightPolar t₁ 0)
      have hcd : 0 < c ∧ |d| ≤ c / 10 := by
        have hzero : F.chart.rightOrbitCoord P t₁ 0 = (0, 0) :=
          F.chart.rightOrbitCoord_zero P t₁
        have hone : F.chart.rightOrbitCoord P t₁ 1 =
            F.chart.coord t₁ t₀.1 := by
          simp [CyclicHullData.AlignedChartData.rightOrbitCoord, hnext]
        norm_num [hzero, hone] at hcdRaw
        simpa [c, d] using hcdRaw
      have hdotRaw := rigid_aligned_dot_displacements
        D.edgeFrame F.chart t₁ t₁.1 t₀.1 v
      have hdot : a * x + b * y = c * X - d * Y := by
        dsimp only at hdotRaw
        rw [F.chart.coord_source] at hdotRaw
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hdotRaw ⊢
        linarith
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_reflectedSuccessorUnitEdgeRigidChart
          P source hsideUnit t₁.1 t₀.1 v
      rw [← hframe] at hrigid
      have hrigid' : Erdos957GeometryCore.cross
          (D.edgeFrame.toCanonical t₀.1 -
            D.edgeFrame.toCanonical t₁.1)
          (D.edgeFrame.toCanonical v -
            D.edgeFrame.toCanonical t₁.1) =
          Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1) := by
        change Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
          Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1)
          at hrigid
        exact hrigid
      have haligned := F.chart.cross_displacements t₁ t₁.1 t₀.1 v
      have hcross : a * y - b * x = c * Y + d * X := by
        have hEq : Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
            -CyclicHullData.pairCross
              (CyclicHullData.pairSub (F.chart.coord t₁ t₀.1)
                (F.chart.coord t₁ t₁.1))
              (CyclicHullData.pairSub (F.chart.coord t₁ v)
                (F.chart.coord t₁ t₁.1)) := by
          rw [hrigid', haligned]
          ring
        simp only [Erdos957GeometryCore.cross, PiLp.sub_apply,
          CyclicHullData.pairCross, CyclicHullData.pairSub] at hEq
        rw [F.chart.coord_source] at hEq
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hEq ⊢
        linarith
      have hX : X < 0 := fst_neg_of_shallow_edge_chart_change
        ha hcd.1 hab.2 hcd.2 hx hy hdot hcross
      rw [hassociation]
      have hm : 0 < middleCoord.1 := by
        rw [← htarget]
        dsimp [X] at hX
        linarith
      simp [horizontalAssociation, cyclicSideAssociation, hside,
        not_le.mpr hm]

/-- The singleton direct form at the first away source has the cyclic
association whenever the source lies past horizontal coordinate `2`.
The proof is the same two-chart comparison as for the second away source,
now using the first edge from the anchored source. -/
lemma Case2SecondaryFormula.singleton_association_at_away_first_of_fst_gt_two
    {source t : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source)
    (hit : P.IsFlat t)
    (ht : t = Erdos957Case4NoThree.awayHullVertex P source D.side 0)
    (htx : (2 : ℝ) < (D.edgeFrame.toCanonical t.1) 0)
    {association : ArrivalAssociation} {middleCoord : ℝ × ℝ}
    (hadj : (unitDistanceGraph A).Adj t.1 v)
    (htarget : F.chart.coord t v = middleCoord)
    (hassociation : association = horizontalAssociation middleCoord.1) :
    association = cyclicSideAssociation D.side := by
  subst t
  let t₀ := source
  let t₁ := Erdos957Case4NoThree.awayHullVertex P source D.side 0
  let p₀ := D.edgeFrame.toCanonical t₀.1
  let p₁ := D.edgeFrame.toCanonical t₁.1
  let a : ℝ := p₁ 0 - p₀ 0
  let b : ℝ := p₁ 1 - p₀ 1
  let x : ℝ := (D.edgeFrame.toCanonical v) 0 - p₁ 0
  let y : ℝ := (D.edgeFrame.toCanonical v) 1 - p₁ 1
  have hp₀ : p₀ = Erdos957Cases24.Case2.u := by
    dsimp [p₀, t₀]
    rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
  have hp₁Bounds := Case2SecondaryFormula.away_prefix_bounds D F hi 0
  have hab : (399 / 400 : ℝ) < a ∧ |b| ≤ a / 10 := by
    have hp₁y : p₁ 1 < 0 := by
      exact hp₁Bounds.1
    have hp₁x : (399 / 400 : ℝ) < p₁ 0 := by
      norm_num at hp₁Bounds
      exact hp₁Bounds.2.1
    have hp₁s : -p₁ 1 ≤ p₁ 0 / 10 := hp₁Bounds.2.2
    change (399 / 400 : ℝ) < p₁ 0 - p₀ 0 ∧
      |p₁ 1 - p₀ 1| ≤ (p₁ 0 - p₀ 0) / 10
    rw [hp₀]
    simpa [Erdos957Cases24.Case2.u, abs_of_neg hp₁y] using
      And.intro hp₁x hp₁s
  have ha : 0 < a := by linarith [hab.1]
  have hcone := Case2SecondaryFormula.away_cone_div_five D F hi 0
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone hadj
  have hx : x ≤ -(99 / 200 : ℝ) := by
    dsimp [x, p₁, t₁]
    rw [he]
    simp only [Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero]
    norm_num at htx ⊢
    linarith
  have hunit : dist p₁ (D.edgeFrame.toCanonical v) = 1 := by
    dsimp [p₁, t₁]
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  have hunitSq := Erdos957Cases24.dist_sq_eq_coordinates
    p₁ (D.edgeFrame.toCanonical v)
  rw [hunit] at hunitSq
  have hy : |y| ≤ 1 := by
    dsimp [y]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  cases D.edgeFrame_spec with
  | previous hside hsideUnit hframe =>
      have hprev : P.next⁻¹ t₁ = t₀ := by
        simp [t₀, t₁, hside, Erdos957Case4NoThree.awayHullVertex]
      let c : ℝ := -(F.chart.coord t₁ t₀.1).1
      let d : ℝ := (F.chart.coord t₁ t₀.1).2
      let X : ℝ := (F.chart.coord t₁ v).1
      let Y : ℝ := (F.chart.coord t₁ v).2
      obtain ⟨hl0, -, -, -⟩ := F.leftFlatAngles t₁ hit
      have hl0' : |F.leftAngle t₁ 0| ≤ Real.pi / 45 := by
        nlinarith [Real.pi_pos]
      have hcdRaw := polar_edge_positive_abs_slope
        (F.leftRadius_ge_one t₁ 0) hl0' (F.leftPolar t₁ 0)
      have hcd : 0 < c ∧ |d| ≤ c / 10 := by
        have hzero : F.chart.leftOrbitReflectedCoord P t₁ 0 = (0, 0) :=
          F.chart.leftOrbitReflectedCoord_zero P t₁
        have hone : F.chart.leftOrbitReflectedCoord P t₁ 1 =
            (-(F.chart.coord t₁ t₀.1).1,
              (F.chart.coord t₁ t₀.1).2) := by
          simp [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
            hprev]
        norm_num [hzero, hone] at hcdRaw
        simpa [c, d] using hcdRaw
      have hdotRaw := rigid_aligned_dot_displacements
        D.edgeFrame F.chart t₁ t₁.1 t₀.1 v
      have hdot : a * x + b * y = c * X - d * Y := by
        dsimp only at hdotRaw
        rw [F.chart.coord_source] at hdotRaw
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hdotRaw ⊢
        linarith
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_terminalUnitEdgeRigidChart
          (P.next⁻¹ source).1.1 source.1.1 t₁.1 t₀.1 v hsideUnit
      rw [← hframe] at hrigid
      have hrigid' : Erdos957GeometryCore.cross
          (D.edgeFrame.toCanonical t₀.1 -
            D.edgeFrame.toCanonical t₁.1)
          (D.edgeFrame.toCanonical v -
            D.edgeFrame.toCanonical t₁.1) =
          -Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1) := by
        change Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
          -Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1)
          at hrigid
        exact hrigid
      have haligned := F.chart.cross_displacements t₁ t₁.1 t₀.1 v
      have hcross : a * y - b * x = c * Y + d * X := by
        have hEq := hrigid'.trans haligned.symm
        simp only [Erdos957GeometryCore.cross, PiLp.sub_apply,
          CyclicHullData.pairCross, CyclicHullData.pairSub] at hEq
        rw [F.chart.coord_source] at hEq
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hEq ⊢
        linarith
      have hX : X < 0 := fst_neg_of_shallow_edge_chart_change
        ha hcd.1 hab.2 hcd.2 hx hy hdot hcross
      rw [hassociation]
      have hm : middleCoord.1 < 0 := by
        rw [← htarget]
        exact hX
      simp [horizontalAssociation, cyclicSideAssociation, hside, le_of_lt hm]
  | next hside hsideUnit hframe =>
      have hnext : P.next t₁ = t₀ := by
        simp [t₀, t₁, hside, Erdos957Case4NoThree.awayHullVertex]
      let c : ℝ := (F.chart.coord t₁ t₀.1).1
      let d : ℝ := (F.chart.coord t₁ t₀.1).2
      let X : ℝ := -(F.chart.coord t₁ v).1
      let Y : ℝ := (F.chart.coord t₁ v).2
      obtain ⟨hr0, -, -, -⟩ := F.rightFlatAngles t₁ hit
      have hr0' : |F.rightAngle t₁ 0| ≤ Real.pi / 45 := by
        nlinarith [Real.pi_pos]
      have hcdRaw := polar_edge_positive_abs_slope
        (F.rightRadius_ge_one t₁ 0) hr0' (F.rightPolar t₁ 0)
      have hcd : 0 < c ∧ |d| ≤ c / 10 := by
        have hzero : F.chart.rightOrbitCoord P t₁ 0 = (0, 0) :=
          F.chart.rightOrbitCoord_zero P t₁
        have hone : F.chart.rightOrbitCoord P t₁ 1 =
            F.chart.coord t₁ t₀.1 := by
          simp [CyclicHullData.AlignedChartData.rightOrbitCoord, hnext]
        norm_num [hzero, hone] at hcdRaw
        simpa [c, d] using hcdRaw
      have hdotRaw := rigid_aligned_dot_displacements
        D.edgeFrame F.chart t₁ t₁.1 t₀.1 v
      have hdot : a * x + b * y = c * X - d * Y := by
        dsimp only at hdotRaw
        rw [F.chart.coord_source] at hdotRaw
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hdotRaw ⊢
        linarith
      have hrigid :=
        Erdos957DirectSameSide.crossFrom_reflectedSuccessorUnitEdgeRigidChart
          P source hsideUnit t₁.1 t₀.1 v
      rw [← hframe] at hrigid
      have hrigid' : Erdos957GeometryCore.cross
          (D.edgeFrame.toCanonical t₀.1 -
            D.edgeFrame.toCanonical t₁.1)
          (D.edgeFrame.toCanonical v -
            D.edgeFrame.toCanonical t₁.1) =
          Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1) := by
        change Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
          Erdos957GeometryCore.cross (t₀.1 - t₁.1) (v - t₁.1)
          at hrigid
        exact hrigid
      have haligned := F.chart.cross_displacements t₁ t₁.1 t₀.1 v
      have hcross : a * y - b * x = c * Y + d * X := by
        have hEq : Erdos957GeometryCore.cross
            (D.edgeFrame.toCanonical t₀.1 -
              D.edgeFrame.toCanonical t₁.1)
            (D.edgeFrame.toCanonical v -
              D.edgeFrame.toCanonical t₁.1) =
            -CyclicHullData.pairCross
              (CyclicHullData.pairSub (F.chart.coord t₁ t₀.1)
                (F.chart.coord t₁ t₁.1))
              (CyclicHullData.pairSub (F.chart.coord t₁ v)
                (F.chart.coord t₁ t₁.1)) := by
          rw [hrigid', haligned]
          ring
        simp only [Erdos957GeometryCore.cross, PiLp.sub_apply,
          CyclicHullData.pairCross, CyclicHullData.pairSub] at hEq
        rw [F.chart.coord_source] at hEq
        dsimp [a, b, c, d, x, y, X, Y, p₀, p₁] at hEq ⊢
        linarith
      have hX : X < 0 := fst_neg_of_shallow_edge_chart_change
        ha hcd.1 hab.2 hcd.2 hx hy hdot hcross
      rw [hassociation]
      have hm : 0 < middleCoord.1 := by
        rw [← htarget]
        dsimp [X] at hX
        linarith
      simp [horizontalAssociation, cyclicSideAssociation, hside,
        not_le.mpr hm]

/-- The first three vertices on the incident side, starting with the stored
cyclic partner. -/
def incidentHullVertex (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (side : CyclicSide)
    (k : Fin 3) : {p // p ∈ P.H} :=
  match side with
  | .previous => ((P.next⁻¹) ^ (k.1 + 1)) source
  | .next => (P.next ^ (k.1 + 1)) source

/-- Formula-level transport of the negative-side prefix bound through the
same reflection-safe frame specification. -/
lemma Case2SecondaryFormula.incident_prefix_fst_lt
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) (k : Fin 3) :
    (D.edgeFrame.toCanonical
      (incidentHullVertex P source D.side k).1) 0 <
      -(((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ)) := by
  cases D.edgeFrame_spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      have h := Erdos957Case4NoThree.previous_terminal_incident_prefix_bounds
        F source hi hunit k
      linarith
  | next hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      have h := Erdos957Case4NoThree.next_reflected_incident_prefix_bounds
        F source hi hunit k
      linarith

lemma Case2SecondaryFormula.incident_second_fst_lt_neg_one
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) :
    (D.edgeFrame.toCanonical
      (incidentHullVertex P source D.side 1).1) 0 < -1 := by
  have h := Case2SecondaryFormula.incident_prefix_fst_lt D F hi 1
  norm_num at h ⊢
  linarith

lemma Case2SecondaryFormula.incident_third_fst_lt_neg_one
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData)
    (hi : P.IsFlat source) :
    (D.edgeFrame.toCanonical
      (incidentHullVertex P source D.side 2).1) 0 < -1 := by
  have h := Case2SecondaryFormula.incident_prefix_fst_lt D F hi 2
  norm_num at h ⊢
  linarith

lemma Case2SecondaryFormula.not_adj_away_third
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source) :
    ¬ (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P source D.side 2).1 v := by
  apply
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_shallow_cone_and_fst_gt_five_halves
      D
  · exact Case2SecondaryFormula.away_cone_div_five D F hi 2
  · exact Case2SecondaryFormula.away_third_fst_gt_five_halves D F hi

lemma Case2SecondaryFormula.not_adj_incident_second
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source) :
    ¬ (unitDistanceGraph A).Adj
      (incidentHullVertex P source D.side 1).1 v :=
  Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_fst_lt_neg_one
    D (Case2SecondaryFormula.incident_second_fst_lt_neg_one D F hi)

lemma Case2SecondaryFormula.not_adj_incident_third
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (F : P.FlatAlignedFrameData) (hi : P.IsFlat source) :
    ¬ (unitDistanceGraph A).Adj
      (incidentHullVertex P source D.side 2).1 v :=
  Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_fst_lt_neg_one
    D (Case2SecondaryFormula.incident_third_fst_lt_neg_one D F hi)

/-- Complete analytic direct/direct leaf.  Two shallow-cone direct
competitors to one Case-2 secondary are impossible once cyclic dispatch
shows that they are mutually unit adjacent, have not passed `x=5/2`, and
lie below the old supporting line. -/
lemma Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone
    {source : {p // p ∈ P.H}} {v r s : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hrCone : -(D.edgeFrame.toCanonical r) 1 ≤
      (D.edgeFrame.toCanonical r) 0 / 5)
    (hsCone : -(D.edgeFrame.toCanonical s) 1 ≤
      (D.edgeFrame.toCanonical s) 0 / 5)
    (hrx : (D.edgeFrame.toCanonical r) 0 ≤ 5 / 2)
    (hsx : (D.edgeFrame.toCanonical s) 0 ≤ 5 / 2)
    (hrv : (unitDistanceGraph A).Adj r v)
    (hsv : (unitDistanceGraph A).Adj s v)
    (hrs : (unitDistanceGraph A).Adj r s)
    (hr0 : (D.edgeFrame.toCanonical r) 1 < 0)
    (hs0 : (D.edgeFrame.toCanonical s) 1 < 0) : False := by
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hrCone hrv
  exact D.no_unit_triangle_strictly_above_e he hrv hsv hrs
    (Case2SecondaryFormula.competitor_above_target_of_shallow_cone
      D hrCone hrx hrv)
    (Case2SecondaryFormula.competitor_above_target_of_shallow_cone
      D hsCone hsx hsv)
    hr0 hs0

/-- Premise-minimal form of the direct/direct kernel: the unit-circle
equations supply both horizontal upper bounds. -/
lemma Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone'
    {source : {p // p ∈ P.H}} {v r s : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hrCone : -(D.edgeFrame.toCanonical r) 1 ≤
      (D.edgeFrame.toCanonical r) 0 / 5)
    (hsCone : -(D.edgeFrame.toCanonical s) 1 ≤
      (D.edgeFrame.toCanonical s) 0 / 5)
    (hrv : (unitDistanceGraph A).Adj r v)
    (hsv : (unitDistanceGraph A).Adj s v)
    (hrs : (unitDistanceGraph A).Adj r s)
    (hr0 : (D.edgeFrame.toCanonical r) 1 < 0)
    (hs0 : (D.edgeFrame.toCanonical s) 1 < 0) : False :=
  Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone D
    hrCone hsCone
    (Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
      D hrCone hrv)
    (Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
      D hsCone hsv)
    hrv hsv hrs hr0 hs0

/-- The current Case-4 whole branch of Figure 13, derived from the actual
formula records.  The two competitors are the Case-4 source and its stored
incident cyclic partner; all three unit incidences come from the checked
whole-row formula.  Cyclic orbit dispatch only has to provide the two
shallow-cone bounds in the Case-2 frame. -/
lemma Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4WholeSameAssociationPlacement D2 D4 E2 E4)
    (hne : source2 ≠ source4)
    (hsourceCone :
      -(X.case2.formula.edgeFrame.toCanonical source4.1) 1 ≤
        (X.case2.formula.edgeFrame.toCanonical source4.1) 0 / 5)
    (hsideCone :
      -(X.case2.formula.edgeFrame.toCanonical X.case4.formula.side) 1 ≤
        (X.case2.formula.edgeFrame.toCanonical X.case4.formula.side) 0 / 5) :
    False := by
  have hsourceNeSource : source4.1 ≠ source2.1 := by
    intro h
    apply hne
    exact Subtype.ext h.symm
  have hsourceNeSide :
      source4.1 ≠ cyclicSideVertex P source2
        X.case2.formula.side := by
    intro h
    apply Case2SecondaryFormula.not_adj_incident_partner X.case2.formula
    simpa [h] using X.case4.formula.source_target_adj
  have hsideNeSource : X.case4.formula.side ≠ source2.1 := by
    intro h
    apply X.case2.formula.not_source_adj_target
    simpa [h] using X.case4.formula.side_target_adj
  have hsideNeSide : X.case4.formula.side ≠
      cyclicSideVertex P source2 X.case2.formula.side := by
    intro h
    apply Case2SecondaryFormula.not_adj_incident_partner X.case2.formula
    simpa [h] using X.case4.formula.side_target_adj
  have hsourceBelow :=
    Case2SecondaryFormula.coordinate_snd_neg_of_ne_endpoints
      X.case2.formula
      hsourceNeSource hsourceNeSide
  have hsideBelow :=
    Case2SecondaryFormula.coordinate_snd_neg_of_ne_endpoints
      X.case2.formula
      hsideNeSource hsideNeSide
  exact Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone'
    X.case2.formula
    hsourceCone hsideCone
    X.case4.formula.source_target_adj
    X.case4.formula.side_target_adj
    ((unitDistanceGraph A).adj_symm X.case4.formula.side_source_adj)
    hsourceBelow hsideBelow

/-- Complete six-slot cyclic dispatch for a Case-2 secondary and a
same-association Case-4 whole arrival.  The proof is reflection invariant:
the stored side decides which three slots are `away` and which three are
`incident`. -/
lemma Case2Case4WholeSameAssociationPlacement.no_collision_of_flat_window
    {source2 source4 : {p // p ∈ P.H}}
    {R2 : RealizedSourceRow P F.chart source2}
    {R4 : RealizedSourceRow P F.chart source4} {v : Vertex A}
    {D2 : RealizedPositiveTarget R2 v}
    {D4 : RealizedPositiveTarget R4 v}
    {E2 : RealizedArrivalDescriptor R2 D2.role D2.target}
    {E4 : RealizedArrivalDescriptor R4 D4.role D4.target}
    (X : Case2Case4WholeSameAssociationPlacement D2 D4 E2 E4)
    (hi : P.IsFlat source2) (hne : source2 ≠ source4) : False := by
  rcases X.source_orbit_cases_of_ne hne with
    hprev3 | hprev2 | hprev1 | hnext1 | hnext2 | hnext3
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hs := congrArg Subtype.val hprev3
      have hs' : source4.1 =
          (incidentHullVertex P source2 X.case2.formula.side 2).1 := by
        simpa [incidentHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_third
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj

    · have hs := congrArg Subtype.val hprev3
      have hs' : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 2).1 := by
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_away_third
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hs := congrArg Subtype.val hprev2
      have hs' : source4.1 =
          (incidentHullVertex P source2 X.case2.formula.side 1).1 := by
        simpa [incidentHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_second
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj
    · have hsource : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 1).1 := by
        have hs := congrArg Subtype.val hprev2
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      have hside : X.case4.formula.side =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 2).1 := by
        rw [X.case4.formula.side_eq, h4]
        simp [cyclicSideVertex, hprev2,
          Erdos957Case4NoThree.awayHullVertex, h2, pow_succ']
      apply Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
        X hne
      · rw [hsource]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 1
      · rw [hside]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 2
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hs := congrArg Subtype.val hprev1
      have hs' : source4.1 =
          cyclicSideVertex P source2 X.case2.formula.side := by
        simpa [cyclicSideVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_partner X.case2.formula
      rw [← hs']
      exact X.case4.formula.source_target_adj
    · have hsource : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 0).1 := by
        have hs := congrArg Subtype.val hprev1
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      have hside : X.case4.formula.side =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 1).1 := by
        rw [X.case4.formula.side_eq, h4]
        simp [cyclicSideVertex, hprev1,
          Erdos957Case4NoThree.awayHullVertex, h2, pow_succ']
      apply Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
        X hne
      · rw [hsource]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 0
      · rw [hside]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 1
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hsource : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 0).1 := by
        have hs := congrArg Subtype.val hnext1
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      have hside : X.case4.formula.side =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 1).1 := by
        rw [X.case4.formula.side_eq, h4]
        simp [cyclicSideVertex, hnext1,
          Erdos957Case4NoThree.awayHullVertex, h2, pow_succ']
      apply Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
        X hne
      · rw [hsource]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 0
      · rw [hside]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 1
    · have hs := congrArg Subtype.val hnext1
      have hs' : source4.1 =
          cyclicSideVertex P source2 X.case2.formula.side := by
        simpa [cyclicSideVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_partner X.case2.formula
      rw [← hs']
      exact X.case4.formula.source_target_adj
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hsource : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 1).1 := by
        have hs := congrArg Subtype.val hnext2
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      have hside : X.case4.formula.side =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 2).1 := by
        rw [X.case4.formula.side_eq, h4]
        simp [cyclicSideVertex, hnext2,
          Erdos957Case4NoThree.awayHullVertex, h2, pow_succ']
      apply Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
        X hne
      · rw [hsource]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 1
      · rw [hside]
        exact Case2SecondaryFormula.away_cone_div_five
          X.case2.formula F hi 2
    · have hs := congrArg Subtype.val hnext2
      have hs' : source4.1 =
          (incidentHullVertex P source2 X.case2.formula.side 1).1 := by
        simpa [incidentHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_second
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj
  · rcases X.opposite_sides with ⟨h2, h4⟩ | ⟨h2, h4⟩
    · have hs := congrArg Subtype.val hnext3
      have hs' : source4.1 =
          (Erdos957Case4NoThree.awayHullVertex P source2
            X.case2.formula.side 2).1 := by
        simpa [Erdos957Case4NoThree.awayHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_away_third
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj
    · have hs := congrArg Subtype.val hnext3
      have hs' : source4.1 =
          (incidentHullVertex P source2 X.case2.formula.side 2).1 := by
        simpa [incidentHullVertex, h2] using hs
      apply Case2SecondaryFormula.not_adj_incident_third
        X.case2.formula F hi
      rw [← hs']
      exact X.case4.formula.source_target_adj

/-! ## Source-indexed exceptional dispatch

These results expose the exact frontier of the anchored no-three proof.
They contain no capacity hypothesis. -/

/-- A direct source in the genuine seven-window can hit a Case-2 secondary
only from the first or second vertex continuing away from the incident edge. -/
lemma Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (hadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hne : s ≠ t) :
    sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 := by
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  rcases Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hne with hprev3 | hprev2 | hprev1 | hnext1 | hnext2 | hnext3
  · rw [hprev3] at hadj
    cases hside : D.side with
    | previous =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_third D F hi
        simpa [incidentHullVertex, hside] using hadj
    | next =>
        exfalso
        apply Case2SecondaryFormula.not_adj_away_third D F hi
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hadj
  · rw [hprev2] at hadj
    cases hside : D.side with
    | previous =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_second D F hi
        simpa [incidentHullVertex, hside] using hadj
    | next =>
        right
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hprev2
  · rw [hprev1] at hadj
    cases hside : D.side with
    | previous =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_partner D
        simpa [cyclicSideVertex, hside] using hadj
    | next =>
        left
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hprev1
  · rw [hnext1] at hadj
    cases hside : D.side with
    | previous =>
        left
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hnext1
    | next =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_partner D
        simpa [cyclicSideVertex, hside] using hadj
  · rw [hnext2] at hadj
    cases hside : D.side with
    | previous =>
        right
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hnext2
    | next =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_second D F hi
        simpa [incidentHullVertex, hside] using hadj
  · rw [hnext3] at hadj
    cases hside : D.side with
    | previous =>
        exfalso
        apply Case2SecondaryFormula.not_adj_away_third D F hi
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using hadj
    | next =>
        exfalso
        apply Case2SecondaryFormula.not_adj_incident_third D F hi
        simpa [incidentHullVertex, hside] using hadj

/-- Two distinct direct competitors occupy the two outgoing slots, in one
of the two possible orders.  No unproved mutual adjacency is inserted. -/
lemma Case2SecondaryFormula.two_direct_competitors_occupy_away_pair
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (htadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 v)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let a := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let b := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    (sourceIndex P W t.1 t.property = a ∧
        sourceIndex P W u.1 u.property = b) ∨
      (sourceIndex P W t.1 t.property = b ∧
        sourceIndex P W u.1 u.property = a) := by
  have ht :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
      D F htadj htWindow hst
  have hu :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
      D F huadj huWindow hsu
  rcases ht with ht | ht <;> rcases hu with hu | hu
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inl ⟨ht, hu⟩
  · exact Or.inr ⟨ht, hu⟩
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)

/-- Two direct realized competitors cannot accompany one Case-2 secondary
arrival.  The two direct sources are forced into the first two outgoing
hull slots.  One-separation from the retained Case-2 outer point `b` forces
the first source past horizontal coordinate `2`, while the unit circle about
the forced target `e` keeps the second source at or before `5/2`; the checked
flat-edge increment between the slots is already greater than `399/400`.

This closes the direct/direct branch of the anchored no-three argument
without assuming that the two competing hull sources are unit-adjacent. -/
theorem Case2SecondaryFormula.no_two_direct_competitors_in_window
    (hA : IsOneSeparated A)
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (htadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 v)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  let source := sourceIndex P W s.1 s.property
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have no_order : ∀ {first second : Source P W},
      (unitDistanceGraph A).Adj
          (sourceIndex P W first.1 first.property).1 v →
      (unitDistanceGraph A).Adj
          (sourceIndex P W second.1 second.property).1 v →
      sourceIndex P W first.1 first.property =
          Erdos957Case4NoThree.awayHullVertex P source D.side 0 →
      sourceIndex P W second.1 second.property =
          Erdos957Case4NoThree.awayHullVertex P source D.side 1 →
      False := by
    intro first second hfirstAdj hsecondAdj hfirst hsecond
    let p := D.edgeFrame.toCanonical
      (sourceIndex P W first.1 first.property).1
    let q := D.edgeFrame.toCanonical
      (sourceIndex P W second.1 second.property).1
    have hpCone : -p 1 ≤ p 0 / 5 := by
      dsimp [p]
      rw [hfirst]
      exact Case2SecondaryFormula.away_cone_div_five D F hi 0
    have hpNeg : p 1 < 0 := by
      dsimp [p]
      rw [hfirst]
      exact (Case2SecondaryFormula.away_prefix_bounds D F hi 0).1
    have hpUpper : p 0 ≤ 5 / 2 := by
      exact Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
        D hpCone hfirstAdj
    have hqCone : -q 1 ≤ q 0 / 5 := by
      dsimp [q]
      rw [hsecond]
      exact Case2SecondaryFormula.away_cone_div_five D F hi 1
    have hqUpper : q 0 ≤ 5 / 2 := by
      exact Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
        D hqCone hsecondAdj
    have hincrement : (399 / 400 : ℝ) < q 0 - p 0 := by
      dsimp [p, q]
      rw [hfirst, hsecond]
      exact Case2SecondaryFormula.away_second_increment_gt D F hi
    have he :=
      Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
        D hpCone hfirstAdj
    have hpUnit : dist p Erdos957Cases24.Case2.e = 1 := by
      rw [← he, D.edgeFrame.dist_eq]
      simpa [p, unitDistanceGraph] using hfirstAdj
    have hpNeOuter :
        (sourceIndex P W first.1 first.property).1 ≠ D.outer := by
      intro h
      apply D.outer_not_hull
      simpa [h] using
        (sourceIndex P W first.1 first.property).property
    have hpSep : 1 ≤ dist
        ((sourceIndex P W first.1 first.property).1 : Point)
        (D.outer : Point) :=
      hA _ (sourceIndex P W first.1 first.property).1.property
        D.outer D.outer.property (fun h ↦ hpNeOuter (Subtype.ext h))
    have hpSepCoord : 1 ≤ dist p Erdos957Cases24.Case2.b := by
      rw [← D.outer_edge_coordinate, D.edgeFrame.dist_eq]
      exact hpSep
    have hpUnitSq := Erdos957Cases24.dist_sq_eq_coordinates
      p Erdos957Cases24.Case2.e
    rw [hpUnit] at hpUnitSq
    have hpSepSq : 1 ≤ dist p Erdos957Cases24.Case2.b ^ 2 := by
      nlinarith [dist_nonneg (x := p) (y := Erdos957Cases24.Case2.b)]
    rw [Erdos957Cases24.dist_sq_eq_coordinates] at hpSepSq
    simp only [Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
      one_pow] at hpUnitSq hpSepSq
    have hpLower : (1 : ℝ) ≤ p 0 := by
      nlinarith [hpUnitSq, hpSepSq]
    have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
      nlinarith [Erdos957Cases24.sqrtThree_pos,
        Erdos957Cases24.sqrtThree_sq]
    have haPos : 0 < p 1 + Erdos957Cases24.sqrtThree / 2 := by
      have hpYLower : -(1 / 2 : ℝ) ≤ p 1 := by
        linarith
      linarith
    have haLt : p 1 + Erdos957Cases24.sqrtThree / 2 <
        Erdos957Cases24.sqrtThree / 2 := by
      linarith
    have haSumPos : 0 < Erdos957Cases24.sqrtThree / 2 +
        (p 1 + Erdos957Cases24.sqrtThree / 2) := by
      linarith [Erdos957Cases24.sqrtThree_pos]
    have haProd : 0 <
        (Erdos957Cases24.sqrtThree / 2 -
            (p 1 + Erdos957Cases24.sqrtThree / 2)) *
          (Erdos957Cases24.sqrtThree / 2 +
            (p 1 + Erdos957Cases24.sqrtThree / 2)) :=
      mul_pos (sub_pos.mpr haLt) haSumPos
    have hpGtTwo : (2 : ℝ) < p 0 := by
      by_contra h
      have hpLeTwo : p 0 ≤ 2 := le_of_not_gt h
      have hprod : 0 ≤ (p 0 - 1) * (2 - p 0) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hpUnitSq, haProd, hprod,
        Erdos957Cases24.sqrtThree_sq]
    nlinarith
  have hslots := Case2SecondaryFormula.two_direct_competitors_occupy_away_pair
    D F htadj huadj htWindow huWindow hst hsu htu
  rcases hslots with ⟨ht, hu⟩ | ⟨ht, hu⟩
  · exact no_order htadj huadj ht hu
  · exact no_order huadj htadj hu ht

/-- The squared distance from the incident endpoint of a Case-2 row to its
secondary target is four or seven.  In particular, it is never a direct
unit arrival from that endpoint. -/
lemma Case2SecondaryFormula.side_target_sq_distance_cases
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    dist ((cyclicSideVertex P source D.side).1 : Point) (v : Point) ^ 2 = 4 ∨
      dist ((cyclicSideVertex P source D.side).1 : Point) (v : Point) ^ 2 = 7 := by
  have hdist : dist ((cyclicSideVertex P source D.side).1 : Point)
        (v : Point) =
      dist Erdos957Cases24.Case2.uPrev (D.edgeFrame.toCanonical v) := by
    calc
      _ = dist (D.edgeFrame.toCanonical
            (cyclicSideVertex P source D.side).1)
          (D.edgeFrame.toCanonical v) := (D.edgeFrame.dist_eq _ _).symm
      _ = _ := by rw [D.side_edge_coordinate]
  rcases D.target_edge_coordinate_cases with h | h | h
  · left
    rw [hdist, h, Erdos957Cases24.dist_sq_eq_coordinates]
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.w, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  · right
    rw [hdist, h, Erdos957Cases24.dist_sq_eq_coordinates]
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.wNext, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  · right
    rw [hdist, h, Erdos957Cases24.dist_sq_eq_coordinates]
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.e, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_sq]

lemma Case2SecondaryFormula.not_side_adj_target
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    ¬ (unitDistanceGraph A).Adj
      (cyclicSideVertex P source D.side) v := by
  intro hadj
  have hunit : dist ((cyclicSideVertex P source D.side).1 : Point)
      (v : Point) = 1 := by simpa [unitDistanceGraph] using hadj
  rcases
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.side_target_sq_distance_cases
        D with h | h <;>
    rw [hunit] at h <;> norm_num at h

/-- At the canonical terminal recipient `e`, the anchor source is at
squared distance three. -/
lemma Case2SecondaryFormula.source_target_sq_eq_three_of_target_eq_e
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e) :
    dist (source.1 : Point) (v : Point) ^ 2 = 3 := by
  have hsource : D.edgeFrame.toCanonical source.1 =
      Erdos957Cases24.Case2.u := by
    rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
  rw [← D.edgeFrame.dist_eq, hsource, he,
    Erdos957Cases24.dist_sq_eq_coordinates]
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
  nlinarith [Erdos957Cases24.sqrtThree_sq]

/-- Once another arrival forces the anchored Case-2 target to `e`, any
source in the seven-window which reaches that target within two unit edges
must lie in one of the three outgoing slots.  This is the common metric
core used for both another Case-2 secondary and a generalized Case-4
split-right recipient. -/
theorem Case2SecondaryFormula.competitor_within_two_eq_away_first_second_or_third
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (hdist : dist
      ((sourceIndex P W t.1 t.property).1 : Point) (v : Point) ≤ 2)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 2 := by
  let z := D.edgeFrame.toCanonical
    (sourceIndex P W t.1 t.property).1
  let q := D.edgeFrame.toCanonical v
  have hdist' : dist z q ≤ 2 := by
    rwa [D.edgeFrame.dist_eq]
  have hdistSq : dist z q ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := q)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hdistSq
  have heq : q = Erdos957Cases24.Case2.e := by
    exact he
  have no_incident (hx : z 0 ≤ -1) : False := by
    rw [heq] at hdistSq
    simp only [q, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hdistSq
    nlinarith [sq_nonneg (z 0 - 3 / 2),
      sq_nonneg (z 1 + Erdos957Cases24.sqrtThree / 2)]
  have horbit :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  cases hside : D.side with
  | previous =>
      rcases horbit with h | h | h | h | h | h
      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            incidentHullVertex P (sourceIndex P W s.1 s.property)
              D.side 2 by
          simpa [incidentHullVertex, hside] using h]
        have hx := Case2SecondaryFormula.incident_prefix_fst_lt
          D F hi 2
        norm_num at hx
        linarith

      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            incidentHullVertex P (sourceIndex P W s.1 s.property)
              D.side 1 by
          simpa [incidentHullVertex, hside] using h]
        have hx := Case2SecondaryFormula.incident_prefix_fst_lt
          D F hi 1
        norm_num at hx
        linarith
      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            cyclicSideVertex P (sourceIndex P W s.1 s.property) D.side by
          simpa [cyclicSideVertex, hside] using h]
        rw [D.side_edge_coordinate]
        norm_num [Erdos957Cases24.Case2.uPrev]
      · exact Or.inl (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact Or.inr (Or.inl (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inr (Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h))
  | next =>
      rcases horbit with h | h | h | h | h | h
      · exact Or.inr (Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inr (Or.inl (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inl (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            cyclicSideVertex P (sourceIndex P W s.1 s.property) D.side by
          simpa [cyclicSideVertex, hside] using h]
        rw [D.side_edge_coordinate]
        norm_num [Erdos957Cases24.Case2.uPrev]
      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            incidentHullVertex P (sourceIndex P W s.1 s.property)
              D.side 1 by
          simpa [incidentHullVertex, hside] using h]
        have hx := Case2SecondaryFormula.incident_prefix_fst_lt
          D F hi 1
        norm_num at hx
        linarith
      · exfalso
        apply no_incident
        dsimp [z]
        rw [show sourceIndex P W t.1 t.property =
            incidentHullVertex P (sourceIndex P W s.1 s.property)
              D.side 2 by
          simpa [incidentHullVertex, hside] using h]
        have hx := Case2SecondaryFormula.incident_prefix_fst_lt
          D F hi 2
        norm_num at hx
        linarith

/-- Case-2 specialization of
`competitor_within_two_eq_away_first_second_or_third`. -/
theorem Case2SecondaryFormula.case2_competitor_eq_away_first_second_or_third
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 2 := by
  exact
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.competitor_within_two_eq_away_first_second_or_third
      D F he (Case2SecondaryFormula.source_target_dist_le_two E)
      htWindow hst

/-- Generalized Case-4 split-right specialization.  Its retained middle
gives an honest two-edge path from the emitting hull source to the selected
recipient; no branch rigidity or capacity premise is used. -/
theorem Case2SecondaryFormula.case4SplitRight_competitor_eq_away_first_second_or_third
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 2 := by
  exact
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.competitor_within_two_eq_away_first_second_or_third
      D F he E.source_target_dist_le_two htWindow hst

/-- Exact four-place reduction for the mixed direct/split residual.  The
direct source can use only outgoing slot zero or one; the split source can
also use slot two, and source distinctness removes the two diagonal pairs.
No association or Case-4 branch assumption is used. -/
theorem Case2SecondaryFormula.direct_case4SplitRight_competitors_away_placements
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W u.1 u.property) v)
    (F : P.FlatAlignedFrameData)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (htadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    let a₂ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 2
    (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = a₁) ∨
      (sourceIndex P W t.1 t.property = a₀ ∧
        sourceIndex P W u.1 u.property = a₂) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = a₀) ∨
      (sourceIndex P W t.1 t.property = a₁ ∧
        sourceIndex P W u.1 u.property = a₂) := by
  have ht := Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
    D F htadj htWindow hst
  have hu :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case4SplitRight_competitor_eq_away_first_second_or_third
      D E F he huWindow hsu
  rcases ht with ht | ht <;> rcases hu with hu | hu | hu
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inl ⟨ht, hu⟩
  · exact Or.inr (Or.inl ⟨ht, hu⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ht, hu⟩))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inr (Or.inr (Or.inr ⟨ht, hu⟩))

/-- The analogous four-place reduction for one further Case-2 secondary
and one direct competitor.  Here the direct hit itself supplies the
canonical-target equation needed by the two-edge reduction. -/
theorem Case2SecondaryFormula.case2_direct_competitors_away_placements
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    let a₂ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 2
    (sourceIndex P W u.1 u.property = a₀ ∧
        sourceIndex P W t.1 t.property = a₁) ∨
      (sourceIndex P W u.1 u.property = a₀ ∧
        sourceIndex P W t.1 t.property = a₂) ∨
      (sourceIndex P W u.1 u.property = a₁ ∧
        sourceIndex P W t.1 t.property = a₀) ∨
      (sourceIndex P W u.1 u.property = a₁ ∧
        sourceIndex P W t.1 t.property = a₂) := by
  have hu := Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
    D F huadj huWindow hsu
  have hcone :
      -(D.edgeFrame.toCanonical
        (sourceIndex P W u.1 u.property).1) 1 ≤
        (D.edgeFrame.toCanonical
          (sourceIndex P W u.1 u.property).1) 0 / 5 := by
    rcases hu with hu | hu
    · rw [hu]
      exact Case2SecondaryFormula.away_cone_div_five D F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0
    · rw [hu]
      exact Case2SecondaryFormula.away_cone_div_five D F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 1
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone huadj
  have ht :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_competitor_eq_away_first_second_or_third
      D E F he htWindow hst
  rcases hu with hu | hu <;> rcases ht with ht | ht | ht
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inl ⟨hu, ht⟩
  · exact Or.inr (Or.inl ⟨hu, ht⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hu, ht⟩))
  · exfalso
    apply htu
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) (ht.trans hu.symm)
  · exact Or.inr (Or.inr (Or.inr ⟨hu, ht⟩))

/-- One of the four formal Case2/direct placements is impossible before
any association dispatch: a direct emitter at outgoing slot one cannot
coexist with a Case-2 emitter at outgoing slot zero.  The Case-2 incident
endpoint is either the anchor source, whose squared distance to `e` is
three, or the direct emitter, whose distance is one; its own fingerprint
allows only four or seven. -/
lemma Case2SecondaryFormula.no_case2_at_away_first_direct_at_away_second
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (he : D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 0)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 1) : False := by
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  let su := sourceIndex P W u.1 u.property
  have hpartner : cyclicSideVertex P st E.side = ss ∨
      cyclicSideVertex P st E.side = su := by
    cases hd : D.side <;> cases heSide : E.side
    · left
      simpa [ss, st, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hd, heSide, htIndex]
    · right
      simpa [ss, st, su, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hd, heSide, htIndex, huIndex,
        pow_two]
    · right
      simpa [ss, st, su, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hd, heSide, htIndex, huIndex,
        pow_two]
    · left
      simpa [ss, st, cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hd, heSide, htIndex]
  rcases hpartner with hpartner | hpartner
  · have hfp :=
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.side_target_sq_distance_cases
        E
    have hsquare :=
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.source_target_sq_eq_three_of_target_eq_e
        D he
    change cyclicSideVertex P st E.side = ss at hpartner
    rw [hpartner] at hfp
    change dist (ss.1 : Point) (v : Point) ^ 2 = 3 at hsquare
    rcases hfp with hfp | hfp <;> rw [hsquare] at hfp <;> norm_num at hfp
  · apply
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target E
    change cyclicSideVertex P st E.side = su at hpartner
    rw [hpartner]
    exact huadj

/-- Three-place normal form for the remaining Case2/Case2/direct triple.
The reflected near-diagonal placement eliminated above is omitted. -/
theorem Case2SecondaryFormula.case2_direct_competitors_away_placements_three
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    let a₀ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 0
    let a₁ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 1
    let a₂ := Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) D.side 2
    (sourceIndex P W u.1 u.property = a₀ ∧
        sourceIndex P W t.1 t.property = a₁) ∨
      (sourceIndex P W u.1 u.property = a₀ ∧
        sourceIndex P W t.1 t.property = a₂) ∨
      (sourceIndex P W u.1 u.property = a₁ ∧
        sourceIndex P W t.1 t.property = a₂) := by
  have hplaces :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_direct_competitors_away_placements
      D E F huadj htWindow huWindow hst hsu htu
  rcases hplaces with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact
      (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_case2_at_away_first_direct_at_away_second
      D E
      (Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
        D (by
          rw [h.1]
          exact Case2SecondaryFormula.away_cone_div_five D F
            (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 1)
        huadj)
      huadj h.2 h.1).elim
  · exact Or.inr (Or.inr h)

/-- If a direct emitter is immediately behind a Case-2 emitter in the
anchor's outgoing orbit (slots zero and one), the latter's normalized
incident side must point forward, away from the direct emitter. -/
lemma Case2SecondaryFormula.case2_side_opposite_of_direct_away_zero_case2_away_one
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 0)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 1) :
    E.side = match D.side with | .previous => .next | .next => .previous := by
  cases hd : D.side <;> cases heSide : E.side
  · exfalso
    apply
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target E
    have hpartner : cyclicSideVertex P
        (sourceIndex P W t.1 t.property) E.side =
        (sourceIndex P W u.1 u.property).1 := by
      simpa [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex,
        hd, heSide, htIndex, huIndex, pow_two]
    rw [hpartner]
    exact huadj
  · rfl
  · rfl
  · exfalso
    apply
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target E
    have hpartner : cyclicSideVertex P
        (sourceIndex P W t.1 t.property) E.side =
        (sourceIndex P W u.1 u.property).1 := by
      simpa [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex,
        hd, heSide, htIndex, huIndex, pow_two]
    rw [hpartner]
    exact huadj

/-- The same orientation conclusion for direct slot one followed by
Case-2 slot two. -/
lemma Case2SecondaryFormula.case2_side_opposite_of_direct_away_one_case2_away_two
    {s t u : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (huadj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 1)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) D.side 2) :
    E.side = match D.side with | .previous => .next | .next => .previous := by
  cases hd : D.side <;> cases heSide : E.side
  · exfalso
    apply
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target E
    have hpartner : cyclicSideVertex P
        (sourceIndex P W t.1 t.property) E.side =
        (sourceIndex P W u.1 u.property).1 := by
      simpa [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex,
        hd, heSide, htIndex, huIndex, pow_succ]
    rw [hpartner]
    exact huadj
  · rfl
  · rfl
  · exfalso
    apply
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target E
    have hpartner : cyclicSideVertex P
        (sourceIndex P W t.1 t.property) E.side =
        (sourceIndex P W u.1 u.property).1 := by
      simpa [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex,
        hd, heSide, htIndex, huIndex, pow_succ]
    rw [hpartner]
    exact huadj

/-- Exact source-indexed wrapper for the completely checked Case-2
secondary/Case-4-whole same-association branch. -/
lemma no_case2Secondary_case4Primary_same_association_in_window
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (rows t.1 t.property) v)
    (Es : RealizedArrivalDescriptor
      (rows s.1 s.property) Ds.role Ds.target)
    (Et : RealizedArrivalDescriptor
      (rows t.1 t.property) Dt.role Dt.target)
    (hsRole : Ds.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : Dt.role = PairCases.TargetRoleName.case4Primary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : Es.association = Et.association)
    (hne : s ≠ t) : False := by
  obtain ⟨X⟩ := nonempty_case2Case4WholeSameAssociationPlacement
    Ds Dt Es Et hsRole htRole htWindow hassoc
  have hneIndex : sourceIndex P W s.1 s.property ≠
      sourceIndex P W t.1 t.property := by
    intro h
    apply hne
    apply Subtype.ext
    exact congrArg (fun z : {p // p ∈ P.H} ↦ z.1) h
  exact
    Erdos957Case2SecondaryNoThree.Case2Case4WholeSameAssociationPlacement.no_collision_of_flat_window
      X (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) hneIndex

/-- Two same-associated Case-2 secondary rows cannot collide when the
second source is the first hull vertex continuing away from the first
row's incident unit edge.  The proof is entirely metric: the two canonical
secondary distance lists force `wNext` for the first row and `w` for the
second.  The second source is then either the first row's non-hull middle or
the forbidden straight continuation. -/
lemma no_case2Secondary_same_association_at_away_first
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side 0) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  have hsides : Bs.formula.side = Bt.formula.side := by
    have hsideAssoc : oppositeCyclicSideAssociation Bs.formula.side =
        oppositeCyclicSideAssociation Bt.formula.side := by
      rw [← Bs.association_eq, ← Bt.association_eq]
      exact hassoc
    cases hs : Bs.formula.side <;> cases ht : Bt.formula.side <;>
      simp [hs, ht, oppositeCyclicSideAssociation] at hsideAssoc ⊢
  have htAway' : st = Erdos957Case4NoThree.awayHullVertex P ss
      Bs.formula.side 0 := by
    exact htAway
  have hpartner : cyclicSideVertex P st Bt.formula.side = ss := by
    rw [← hsides]
    cases hside : Bs.formula.side with
    | previous =>
        simp [st, ss, htAway', Erdos957Case4NoThree.awayHullVertex,
          cyclicSideVertex, hside]
    | next =>
        simp [st, ss, htAway', Erdos957Case4NoThree.awayHullVertex,
          cyclicSideVertex, hside]
  have hssCoord : Bs.formula.edgeFrame.toCanonical ss.1 =
      Erdos957Cases24.Case2.u := by
    rw [← Bs.formula.source_actual,
      Bs.formula.edgeFrame.toCanonical_actual]
  have hstCoord : Bt.formula.edgeFrame.toCanonical st.1 =
      Erdos957Cases24.Case2.u := by
    rw [← Bt.formula.source_actual,
      Bt.formula.edgeFrame.toCanonical_actual]
  have hpartnerCoord : Bt.formula.edgeFrame.toCanonical ss.1 =
      Erdos957Cases24.Case2.uPrev := by
    rw [← hpartner, ← Bt.formula.side_actual,
      Bt.formula.edgeFrame.toCanonical_actual]
  have hdistSource :
      dist Erdos957Cases24.Case2.u
          (Bs.formula.edgeFrame.toCanonical v) =
        dist Erdos957Cases24.Case2.uPrev
          (Bt.formula.edgeFrame.toCanonical v) := by
    calc
      _ = dist (ss.1 : Point) (v : Point) := by
        rw [← hssCoord]
        exact Bs.formula.edgeFrame.dist_eq ss.1 v
      _ = dist (Bt.formula.edgeFrame.toCanonical ss.1)
          (Bt.formula.edgeFrame.toCanonical v) := by
        rw [Bt.formula.edgeFrame.dist_eq]
      _ = _ := by rw [hpartnerCoord]
  have hsCoord := Bs.formula.target_edge_coordinate_cases
  have htCoord := Bt.formula.target_edge_coordinate_cases
  have hforced : Bs.formula.edgeFrame.toCanonical v =
        Erdos957Cases24.Case2.wNext ∧
      Bt.formula.edgeFrame.toCanonical v =
        Erdos957Cases24.Case2.w := by
    rcases hsCoord with hs | hs | hs <;>
      rcases htCoord with ht | ht | ht
    all_goals try { exact ⟨hs, ht⟩ }
    all_goals exfalso
    all_goals have hsq := congrArg (fun r : ℝ ↦ r ^ 2) hdistSource
    all_goals rw [hs, ht, Erdos957Cases24.dist_sq_eq_coordinates,
      Erdos957Cases24.dist_sq_eq_coordinates] at hsq
    all_goals simp only [Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hsq
    all_goals nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hstUnit : dist (ss.1 : Point) (st.1 : Point) = 1 := by
    rw [← hpartner]
    simpa [dist_comm] using Bt.formula.side_unit
  let z := Bs.formula.edgeFrame.toCanonical st.1
  have huz : dist Erdos957Cases24.Case2.u z = 1 := by
    calc
      _ = dist (Bs.formula.edgeFrame.toCanonical ss.1)
          (Bs.formula.edgeFrame.toCanonical st.1) := by rw [hssCoord]
      _ = dist (ss.1 : Point) (st.1 : Point) :=
        Bs.formula.edgeFrame.dist_eq ss.1 st.1
      _ = 1 := hstUnit
  have hcanonical : dist Erdos957Cases24.Case2.w
      Erdos957Cases24.Case2.u = Erdos957Cases24.sqrtThree := by
    have hsq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.w Erdos957Cases24.Case2.u
    have hsqrt := Erdos957Cases24.sqrtThree_pos
    simp only [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.u,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hsq
    have hsq' : dist Erdos957Cases24.Case2.w
        Erdos957Cases24.Case2.u ^ 2 = 3 := by
      calc
        _ = (0 - 0 : ℝ) ^ 2 +
            (-Erdos957Cases24.sqrtThree - 0) ^ 2 := hsq
        _ = 3 := by nlinarith [Erdos957Cases24.sqrtThree_sq]
    apply (sq_eq_sq₀
      (dist_nonneg (x := Erdos957Cases24.Case2.w)
        (y := Erdos957Cases24.Case2.u))
      (le_of_lt hsqrt)).mp
    nlinarith [hsq', Erdos957Cases24.sqrtThree_sq]
  have hwz : dist Erdos957Cases24.Case2.wNext z =
      Erdos957Cases24.sqrtThree := by
    calc
      _ = dist (Bs.formula.edgeFrame.toCanonical v)
          (Bs.formula.edgeFrame.toCanonical st.1) := by rw [hforced.1]
      _ = dist (v : Point) (st.1 : Point) :=
        Bs.formula.edgeFrame.dist_eq v st.1
      _ = dist (Bt.formula.edgeFrame.toCanonical v)
          (Bt.formula.edgeFrame.toCanonical st.1) := by
        rw [Bt.formula.edgeFrame.dist_eq]
      _ = dist Erdos957Cases24.Case2.w Erdos957Cases24.Case2.u := by
        rw [hforced.2, hstCoord]
      _ = Erdos957Cases24.sqrtThree := hcanonical
  rcases eq_case2_v_or_uNext_of_dist_u_one_dist_wNext_sqrtThree
      huz hwz with hz | hz
  · apply Bs.formula.middle_not_hull
    have hstMiddlePoint : (st.1 : Point) =
        (Bs.formula.middle : Point) := by
      apply Bs.formula.edgeFrame.toCanonical.injective
      change z = Bs.formula.edgeFrame.toCanonical Bs.formula.middle
      rw [hz, ← Bs.formula.middle_actual,
        Bs.formula.edgeFrame.toCanonical_actual]
    have hstMiddle : st.1 = Bs.formula.middle :=
      Subtype.ext hstMiddlePoint
    exact hstMiddle ▸ st.property
  · apply Erdos957Case24Bridge.case2_uNext_not_mem_of_strict_support
      Bs.formula.strict_support
    exact Finset.mem_image.mpr ⟨st.1, st.1.property, hz⟩

/-- The incident-partner placement is the preceding theorem with the two
rows exchanged: equal Case-2 associations give the same normalized side,
so the original source is the first away vertex of its incident partner. -/
lemma no_case2Secondary_same_association_at_incident_first
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (htIncident : sourceIndex P W t.1 t.property =
      cyclicSideVertex P (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  have hsides : Bs.formula.side = Bt.formula.side := by
    have hsideAssoc : oppositeCyclicSideAssociation Bs.formula.side =
        oppositeCyclicSideAssociation Bt.formula.side := by
      rw [← Bs.association_eq, ← Bt.association_eq]
      exact hassoc
    cases hs : Bs.formula.side <;> cases ht : Bt.formula.side <;>
      simp [hs, ht, oppositeCyclicSideAssociation] at hsideAssoc ⊢
  apply no_case2Secondary_same_association_at_away_first
    T S htRole hsRole hassoc.symm
  change sourceIndex P W s.1 s.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W t.1 t.property) Bt.formula.side 0
  have htIncident' : sourceIndex P W t.1 t.property =
      cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Bs.formula.side := by
    exact htIncident
  rw [← hsides]
  cases hside : Bs.formula.side with
  | previous =>
      have hti : sourceIndex P W t.1 t.property =
          P.next⁻¹ (sourceIndex P W s.1 s.property) := by
        apply Subtype.ext
        simpa [cyclicSideVertex, hside] using htIncident'
      have h := congrArg P.next hti
      simpa [cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hside] using h.symm
  | next =>
      have hti : sourceIndex P W t.1 t.property =
          P.next (sourceIndex P W s.1 s.property) := by
        apply Subtype.ext
        simpa [cyclicSideVertex, hside] using htIncident'
      have h := congrArg P.next.symm hti
      simpa [cyclicSideVertex,
        Erdos957Case4NoThree.awayHullVertex, hside] using h.symm

/-- Two same-associated Case-2 secondary rows cannot collide when their
sources are separated by the second away hull vertex.  In the anchor frame,
the two intervening flat hull edges each advance almost one unit.  In the
competitor frame, their shared target has one of the three exact canonical
Case-2 distance fingerprints from the incident endpoint and source.  The
pure two-step metric lemma above excludes all three fingerprints. -/
lemma no_case2Secondary_same_association_at_away_second
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side 1) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  let p₁ := Bs.formula.edgeFrame.toCanonical
    (Erdos957Case4NoThree.awayHullVertex P ss Bs.formula.side 0).1
  let p₂ := Bs.formula.edgeFrame.toCanonical st.1
  let q := Bs.formula.edgeFrame.toCanonical v
  have hsides : Bs.formula.side = Bt.formula.side := by
    have hsideAssoc : oppositeCyclicSideAssociation Bs.formula.side =
        oppositeCyclicSideAssociation Bt.formula.side := by
      rw [← Bs.association_eq, ← Bt.association_eq]
      exact hassoc
    cases hs : Bs.formula.side <;> cases ht : Bt.formula.side <;>
      simp [hs, ht, oppositeCyclicSideAssociation] at hsideAssoc ⊢
  have htAway' : st = Erdos957Case4NoThree.awayHullVertex P ss
      Bs.formula.side 1 := htAway
  have hpartner : cyclicSideVertex P st Bt.formula.side =
      Erdos957Case4NoThree.awayHullVertex P ss Bs.formula.side 0 := by
    rw [← hsides]
    cases hside : Bs.formula.side with
    | previous =>
        simp [st, ss, htAway', cyclicSideVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_two]
    | next =>
        simp [st, ss, htAway', cyclicSideVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_two]
  have hp₁ :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_prefix_bounds
      Bs.formula F (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0
  have h₁x : (399 / 400 : ℝ) < p₁ 0 := by
    have hh := hp₁.2.1
    norm_num at hh
    change (399 / 400 : ℝ) <
      (Bs.formula.edgeFrame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P ss
          Bs.formula.side 0).1) 0
    simpa only [ss] using hh
  have h₁s : |p₁ 1| ≤ p₁ 0 / 10 := by
    rw [abs_of_neg hp₁.1]
    exact hp₁.2.2
  have h₂x : (399 / 400 : ℝ) < p₂ 0 - p₁ 0 := by
    change (399 / 400 : ℝ) <
      (Bs.formula.edgeFrame.toCanonical st.1) 0 -
        (Bs.formula.edgeFrame.toCanonical
          (Erdos957Case4NoThree.awayHullVertex P ss
            Bs.formula.side 0).1) 0
    rw [htAway']
    exact
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.away_second_increment_gt
        Bs.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
  have hedgeActual : dist
      ((Erdos957Case4NoThree.awayHullVertex P ss
        Bs.formula.side 0).1 : Point) (st.1 : Point) = 1 := by
    rw [← hpartner]
    simpa [dist_comm] using Bt.formula.side_unit
  have hedge : dist p₁ p₂ = 1 := by
    exact (Bs.formula.edgeFrame.dist_eq _ _).trans hedgeActual
  have hedgeSq := Erdos957Cases24.dist_sq_eq_coordinates p₁ p₂
  rw [hedge] at hedgeSq
  norm_num at hedgeSq
  have h₂s : |p₂ 1 - p₁ 1| ≤ (p₂ 0 - p₁ 0) / 10 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg ((p₂ 1 - p₁ 1) -
        (p₂ 0 - p₁ 0) / 10),
        sq_nonneg ((p₂ 1 - p₁ 1) +
          (p₂ 0 - p₁ 0) / 10)]
  have hpartnerCoord : Bt.formula.edgeFrame.toCanonical
      (Erdos957Case4NoThree.awayHullVertex P ss Bs.formula.side 0).1 =
        Erdos957Cases24.Case2.uPrev := by
    rw [← hpartner]
    exact Bt.formula.side_edge_coordinate
  have hsourceCoord : Bt.formula.edgeFrame.toCanonical st.1 =
      Erdos957Cases24.Case2.u := by
    rw [← Bt.formula.source_actual,
      Bt.formula.edgeFrame.toCanonical_actual]
  have hdistPartner : dist q p₁ = dist
      (Bt.formula.edgeFrame.toCanonical v)
        Erdos957Cases24.Case2.uPrev := by
    calc
      _ = dist (v : Point)
          ((Erdos957Case4NoThree.awayHullVertex P ss
            Bs.formula.side 0).1 : Point) :=
        Bs.formula.edgeFrame.dist_eq _ _
      _ = dist (Bt.formula.edgeFrame.toCanonical v)
          (Bt.formula.edgeFrame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P ss
              Bs.formula.side 0).1) := by
        rw [Bt.formula.edgeFrame.dist_eq]
      _ = _ := by rw [hpartnerCoord]
  have hdistSource : dist q p₂ = dist
      (Bt.formula.edgeFrame.toCanonical v)
        Erdos957Cases24.Case2.u := by
    calc
      _ = dist (v : Point) (st.1 : Point) :=
        Bs.formula.edgeFrame.dist_eq _ _
      _ = dist (Bt.formula.edgeFrame.toCanonical v)
          (Bt.formula.edgeFrame.toCanonical st.1) := by
        rw [Bt.formula.edgeFrame.dist_eq]
      _ = _ := by rw [hsourceCoord]
  have hfpCanonical :=
    case2_secondary_incident_source_sq_distance_cases
      Bt.formula.target_edge_coordinate_cases
  have hfp :
      (dist q p₁ ^ 2 = 4 ∧ dist q p₂ ^ 2 = 3) ∨
      (dist q p₁ ^ 2 = 7 ∧ dist q p₂ ^ 2 = 4) ∨
      (dist q p₁ ^ 2 = 7 ∧ dist q p₂ ^ 2 = 3) := by
    rw [hdistPartner, hdistSource]
    simpa [dist_comm] using hfpCanonical
  exact no_case2Secondary_fingerprint_after_two_flat_steps
    h₁x h₁s h₂x h₂s hedge
    Bs.formula.target_edge_coordinate_cases hfp

/-- The second incident placement is the row-exchanged form of the checked
second-away exclusion. -/
lemma no_case2Secondary_same_association_at_incident_second
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (htIncident : sourceIndex P W t.1 t.property =
      incidentHullVertex P (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side 1) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  have hsides : Bs.formula.side = Bt.formula.side := by
    have hsideAssoc : oppositeCyclicSideAssociation Bs.formula.side =
        oppositeCyclicSideAssociation Bt.formula.side := by
      rw [← Bs.association_eq, ← Bt.association_eq]
      exact hassoc
    cases hs : Bs.formula.side <;> cases ht : Bt.formula.side <;>
      simp [hs, ht, oppositeCyclicSideAssociation] at hsideAssoc ⊢
  apply no_case2Secondary_same_association_at_away_second
    T S htRole hsRole hassoc.symm
  change ss = Erdos957Case4NoThree.awayHullVertex P st
    Bt.formula.side 1
  rw [← hsides]
  have htIncident' : st = incidentHullVertex P ss
      Bs.formula.side 1 := htIncident
  cases hside : Bs.formula.side with
  | previous =>
      have h := congrArg (fun z => (P.next ^ 2) z) htIncident'
      simpa [Erdos957Case4NoThree.awayHullVertex, incidentHullVertex,
        hside, pow_two] using h.symm
  | next =>
      have h := congrArg (fun z => ((P.next⁻¹) ^ 2) z) htIncident'
      simpa [Erdos957Case4NoThree.awayHullVertex, incidentHullVertex,
        hside, pow_two] using h.symm

/-- A Case-2 secondary competitor cannot occur three hull steps through the
incident endpoint.  The anchor-frame horizontal gap is already greater
than two, whereas every Case-2 secondary is within distance two of its own
source. -/
lemma no_case2Secondary_competitor_at_incident_third
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (htIncident : sourceIndex P W t.1 t.property =
      incidentHullVertex P (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side 2) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  let q := Bs.formula.edgeFrame.toCanonical v
  let z := Bs.formula.edgeFrame.toCanonical st.1
  have hdist : dist z q ≤ 2 := by
    rw [Bs.formula.edgeFrame.dist_eq]
    exact
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.source_target_dist_le_two
        Bt.formula
  have hdistSq : dist z q ^ 2 ≤ 4 := by
    nlinarith [dist_nonneg (x := z) (y := q)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hdistSq
  have hqx : 0 ≤ q 0 := Bs.formula.target_horizontal_bounds.1
  have htIncident' : st = incidentHullVertex P ss Bs.formula.side 2 := by
    exact htIncident
  have hzx : z 0 < -(3 * (399 / 400 : ℝ)) := by
    change (Bs.formula.edgeFrame.toCanonical st.1) 0 < _
    rw [htIncident']
    exact
      Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.incident_prefix_fst_lt
        Bs.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 2
  nlinarith [sq_nonneg (q 0 - z 0), sq_nonneg (q 1 - z 1)]

/-- The third-away placement is the preceding metric exclusion viewed from
the other row.  Equal Case-2 associations again identify the normalized
side, and reversing three cyclic steps turns away into incident. -/
lemma no_case2Secondary_same_association_at_away_third
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Classical.choice (nonempty_case2SecondaryArrivalFormula
          S.target S.descriptor hsRole)).formula.side 2) : False := by
  let Bs := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  let Bt := Classical.choice (nonempty_case2SecondaryArrivalFormula
    T.target T.descriptor htRole)
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  have hsides : Bs.formula.side = Bt.formula.side := by
    have hsideAssoc : oppositeCyclicSideAssociation Bs.formula.side =
        oppositeCyclicSideAssociation Bt.formula.side := by
      rw [← Bs.association_eq, ← Bt.association_eq]
      exact hassoc
    cases hs : Bs.formula.side <;> cases ht : Bt.formula.side <;>
      simp [hs, ht, oppositeCyclicSideAssociation] at hsideAssoc ⊢
  apply no_case2Secondary_competitor_at_incident_third
    T S htRole hsRole
  change ss = incidentHullVertex P st Bt.formula.side 2
  rw [← hsides]
  have htAway' : st = Erdos957Case4NoThree.awayHullVertex P ss
      Bs.formula.side 2 := by
    exact htAway
  cases hside : Bs.formula.side with
  | previous =>
      have h := congrArg (fun z => ((P.next⁻¹) ^ 3) z) htAway'
      simpa [Erdos957Case4NoThree.awayHullVertex, incidentHullVertex,
        hside] using h.symm
  | next =>
      have h := congrArg (fun z => (P.next ^ 3) z) htAway'
      simpa [Erdos957Case4NoThree.awayHullVertex, incidentHullVertex,
        hside] using h.symm

/-- Two same-associated Case-2 secondary arrivals in the genuine
seven-vertex window have the same emitting source.  This is the
residual-free Case-2/Case-2 component: all six nonzero cyclic offsets are
excluded by the preceding rigid-chart lemmas. -/
theorem case2Secondary_same_association_source_eq
    {rows : HasRealizedSourceRows P W F.chart}
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_contra hst
  let B := Classical.choice (nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole)
  by_cases htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0
  · exact (no_case2Secondary_same_association_at_away_first
      S T hsRole htRole hassoc htAway).elim
  by_cases htIncident : sourceIndex P W t.1 t.property =
      cyclicSideVertex P (sourceIndex P W s.1 s.property) B.formula.side
  · exact (no_case2Secondary_same_association_at_incident_first
      S T hsRole htRole hassoc htIncident).elim
  by_cases htAwaySecond : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1
  · exact (no_case2Secondary_same_association_at_away_second
      S T hsRole htRole hassoc htAwaySecond).elim
  by_cases htIncidentSecond : sourceIndex P W t.1 t.property =
      incidentHullVertex P (sourceIndex P W s.1 s.property)
        B.formula.side 1
  · exact (no_case2Secondary_same_association_at_incident_second
      S T hsRole htRole hassoc htIncidentSecond).elim
  by_cases htIncidentThird : sourceIndex P W t.1 t.property =
      incidentHullVertex P (sourceIndex P W s.1 s.property)
        B.formula.side 2
  · exact (no_case2Secondary_competitor_at_incident_third
      S T hsRole htRole htIncidentThird).elim
  by_cases htAwayThird : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 2
  · exact (no_case2Secondary_same_association_at_away_third
      S T hsRole htRole hassoc htAwayThird).elim
  have horbit :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  cases hside : B.formula.side with
  | previous =>
      rcases horbit with h | h | h | h | h | h
      · exact htIncidentThird (by
          simpa [incidentHullVertex, hside] using h)
      · exact htIncidentSecond (by
          simpa [incidentHullVertex, hside] using h)
      · exact htIncident (by simpa [cyclicSideVertex, hside] using h)
      · exact htAway (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact htAwaySecond (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact htAwayThird (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
  | next =>
      rcases horbit with h | h | h | h | h | h
      · exact htAwayThird (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact htAwaySecond (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact htAway (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exact htIncident (by simpa [cyclicSideVertex, hside] using h)
      · exact htIncidentSecond (by
          simpa [incidentHullVertex, hside] using h)
      · exact htIncidentThird (by
          simpa [incidentHullVertex, hside] using h)

/-! ## Side-free Case-2 exceptional triple dispatch -/

/-- At degree five the Case-2 selector cannot have reached its terminal
`e` branch.  Strict support already bounds the canonical endpoint `e` by
degree four; rigid-chart transport identifies that count with the actual
target count. -/
lemma Case2SecondaryFormula.endpoint_actual_unitDegree_le_four
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    Erdos957Case24Bridge.unitDegree A
      (D.edgeFrame.actual Erdos957Cases24.Case2.e) ≤ 4 := by
  have hb : Erdos957Cases24.Case2.b ∈ D.edgeFrame.image A := by
    exact Finset.mem_image.mpr
      ⟨(D.outer : Point), D.outer.property, D.outer_edge_coordinate⟩
  have heDegree : Erdos957Case24Bridge.unitDegree
      (D.edgeFrame.image A) Erdos957Cases24.Case2.e ≤ 4 :=
    Erdos957Case24Bridge.Case2.unitDegree_e_le_four_of_strict_support
      (D.edgeFrame.image_oneSeparated hA) D.strict_support hb
  rw [D.edgeFrame.unitDegree_image_actual A] at heDegree
  exact heDegree

/-- At degree five the Case-2 selector cannot have reached its terminal
`e` branch.  Strict support already bounds the canonical endpoint `e` by
degree four; rigid-chart transport identifies that count with the actual
target count. -/
lemma Case2SecondaryFormula.target_ne_e_of_degree_five
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hdegree : (unitDistanceGraph A).degree v = 5) :
    D.edgeFrame.toCanonical v ≠ Erdos957Cases24.Case2.e := by
  have heDegree :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.endpoint_actual_unitDegree_le_four
      hA D
  intro he
  have hactual : D.edgeFrame.actual Erdos957Cases24.Case2.e = (v : Point) := by
    change D.edgeFrame.toCanonical.symm Erdos957Cases24.Case2.e = (v : Point)
    rw [← he]
    exact D.edgeFrame.toCanonical.symm_apply_apply (v : Point)
  rw [hactual,
    ← Erdos957CaseClassification.ActualCase24Rows.graph_degree_eq_unitDegree] at heDegree
  omega

/-- At degree five the exceptional Case-2 target is therefore one of the
two genuine low continuations.  Keeping this disjunction explicit is useful
for the remaining mixed Case-2/Case-4 degree-count argument: the `e` branch
has already been eliminated by strict support, while no choice between `w`
and `wNext` is made here. -/
lemma Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hdegree : (unitDistanceGraph A).degree v = 5) :
    D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.w ∨
      D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.wNext := by
  rcases D.target_edge_coordinate_cases with hw | hwNext | he
  · exact Or.inl hw
  · exact Or.inr hwNext
  · exact
      (Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.target_ne_e_of_degree_five
        hA D hdegree he).elim

/-- At a degree-five Case-2 target, a second Case-2 source in the genuine
seven-window can only occupy the incident endpoint or one of the first two
away positions.  The second and third incident positions and the third away
position are already farther than two unit edges from either surviving
canonical target (`w` or `wNext`).  This is the metric orbit reduction used
by the weighted exceptional-triple dispatch; it makes no association or
pairwise-uniqueness claim. -/
lemma Case2SecondaryFormula.competitor_near_slots_of_degree_five
    (hA : IsOneSeparated A)
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (hdistLe : dist ((sourceIndex P W t.1 t.property).1 : Point)
      (v : Point) ≤ 2)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 := by
  let ss := sourceIndex P W s.1 s.property
  let st := sourceIndex P W t.1 t.property
  let z := D.edgeFrame.toCanonical st.1
  let q := D.edgeFrame.toCanonical v
  have htarget :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
      hA D hdegree
  have hdistLe' : dist z q ≤ 2 := by
    rw [D.edgeFrame.dist_eq]
    exact hdistLe
  have hsq : (z 0 - q 0) ^ 2 + (z 1 - q 1) ^ 2 ≤ 4 := by
    rw [← Erdos957Cases24.dist_sq_eq_coordinates]
    nlinarith [dist_nonneg (x := z) (y := q)]
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have noIncident (k : Fin 3) (hk : 1 ≤ k.1)
      (ht : st = incidentHullVertex P ss D.side k) : False := by
    have hmetric :=
      Erdos957Case4NoThree.sideNormalizedFrame_incident_prefix_metric_bounds
        F ss D.side D.edgeFrame D.edgeFrame_spec hi k
    have hmetric' :
        (((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
            -(D.edgeFrame.toCanonical st.1) 0 ∧
          -(D.edgeFrame.toCanonical st.1) 1 ≤
            (-(D.edgeFrame.toCanonical st.1) 0) / 10) := by
      rw [ht]
      exact hmetric
    change (((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 ∧
      -z 1 ≤ (-z 0) / 10) at hmetric'
    rcases hmetric' with ⟨hx, hy⟩
    rcases htarget with hw | hwNext
    · dsimp only [q] at hsq
      rw [hw] at hsq
      simp only [Erdos957Cases24.Case2.w,
        Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one] at hsq
      have hfactor : (798 / 400 : ℝ) ≤
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by
        have hk' : (2 : ℕ) ≤ k.1 + 1 := by omega
        have hkReal : (2 : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast hk'
        calc
          (798 / 400 : ℝ) = 2 * (399 / 400 : ℝ) := by norm_num
          _ ≤ ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) :=
            mul_le_mul_of_nonneg_right hkReal (by norm_num)
      have hxNeg : z 0 < -(399 / 200 : ℝ) := by linarith
      have hxLower : -(2 : ℝ) ≤ z 0 := by
        nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
      have hyLower : -(1 / 5 : ℝ) ≤ z 1 := by linarith
      have hsqrtLower : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
        nlinarith [Erdos957Cases24.sqrtThree_sq,
          Erdos957Cases24.sqrtThree_pos]
      nlinarith [sq_nonneg (z 0),
        sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
    · dsimp only [q] at hsq
      rw [hwNext] at hsq
      simp only [Erdos957Cases24.Case2.wNext,
        Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one] at hsq
      have hfactor : (798 / 400 : ℝ) ≤
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by
        have hk' : (2 : ℕ) ≤ k.1 + 1 := by omega
        have hkReal : (2 : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast hk'
        calc
          (798 / 400 : ℝ) = 2 * (399 / 400 : ℝ) := by norm_num
          _ ≤ ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) :=
            mul_le_mul_of_nonneg_right hkReal (by norm_num)
      have hxNeg : z 0 < -(399 / 200 : ℝ) := by linarith
      nlinarith [Erdos957Cases24.sqrtThree_sq,
        Erdos957Cases24.sqrtThree_pos,
        sq_nonneg (z 0 - 1),
        sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
  have noAwayThird
      (ht : st = Erdos957Case4NoThree.awayHullVertex P ss D.side 2) :
      False := by
    have hmetric := Case2SecondaryFormula.away_prefix_bounds D F hi 2
    have hmetric' :
        (D.edgeFrame.toCanonical st.1) 1 < 0 ∧
          (3 : ℝ) * (399 / 400 : ℝ) <
            (D.edgeFrame.toCanonical st.1) 0 ∧
          -(D.edgeFrame.toCanonical st.1) 1 ≤
            (D.edgeFrame.toCanonical st.1) 0 / 10 := by
      rw [ht]
      exact hmetric
    change z 1 < 0 ∧ (3 : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 at hmetric'
    rcases hmetric' with ⟨hy0, hx, hy⟩
    rcases htarget with hw | hwNext
    · dsimp only [q] at hsq
      rw [hw] at hsq
      simp only [Erdos957Cases24.Case2.w,
        Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one] at hsq
      nlinarith [sq_nonneg (z 0),
        sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
    · dsimp only [q] at hsq
      rw [hwNext] at hsq
      simp only [Erdos957Cases24.Case2.wNext,
        Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one] at hsq
      have hxUpper : z 0 ≤ 3 := by
        nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
      have hyLower : -(3 / 10 : ℝ) ≤ z 1 := by linarith
      have hsqrtLower : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
        nlinarith [Erdos957Cases24.sqrtThree_sq,
          Erdos957Cases24.sqrtThree_pos]
      nlinarith [sq_nonneg (z 0 - 1),
        sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
  have horbit :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  cases hside : D.side with
  | previous =>
      rcases horbit with h | h | h | h | h | h
      · exact (noIncident 2 (by norm_num) (by
          simpa [ss, st, incidentHullVertex, hside] using h)).elim
      · exact (noIncident 1 (by norm_num) (by
          simpa [ss, st, incidentHullVertex, hside] using h)).elim
      · exact Or.inl (by
          simpa [ss, st, incidentHullVertex, hside] using h)
      · exact Or.inr (Or.inl (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inr (Or.inr (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact (noAwayThird (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside]
            using h)).elim
  | next =>
      rcases horbit with h | h | h | h | h | h
      · exact (noAwayThird (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside]
            using h)).elim
      · exact Or.inr (Or.inr (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inr (Or.inl (by
          simpa [ss, st, Erdos957Case4NoThree.awayHullVertex, hside] using h))
      · exact Or.inl (by
          simpa [ss, st, incidentHullVertex, hside] using h)
      · exact (noIncident 1 (by norm_num) (by
          simpa [ss, st, incidentHullVertex, hside] using h)).elim
      · exact (noIncident 2 (by norm_num) (by
          simpa [ss, st, incidentHullVertex, hside] using h)).elim

/-- Case-2 specialization of the degree-five near-slot reduction. -/
lemma Case2SecondaryFormula.case2_competitor_near_slots_of_degree_five
    (hA : IsOneSeparated A)
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 := by
  apply Case2SecondaryFormula.competitor_near_slots_of_degree_five
    hA D F _ hdegree htWindow hst
  rcases E.source_target_sq_distance_cases with h | h <;>
    nlinarith [dist_nonneg
      (x := ((sourceIndex P W t.1 t.property).1 : Point)) (y := (v : Point))]

/-- Case-4 split-right specialization of the same degree-five near-slot
reduction.  It uses only the retained honest two-edge source path. -/
lemma Case2SecondaryFormula.case4SplitRight_competitor_near_slots_of_degree_five
    (hA : IsOneSeparated A)
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (E : Case4SplitRightFormula (P := P)
      (source := sourceIndex P W t.1 t.property) v)
    (F : P.FlatAlignedFrameData)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    sourceIndex P W t.1 t.property =
        incidentHullVertex P (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 0 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) D.side 1 := by
  exact Case2SecondaryFormula.competitor_near_slots_of_degree_five
    hA D F E.source_target_dist_le_two hdegree htWindow hst

/-- Degree six at the retained Case-2 middle recovers the complete
five-point canonical display in the row's rigid chart.  This packages the
membership facts needed by the remaining degree-count arguments. -/
lemma Case2SecondaryFormula.displayedFiveAtV_subset
    (hA : IsOneSeparated A)
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v) :
    Erdos957Cases24.Case4.displayedFiveAtV ⊆ D.edgeFrame.image A := by
  have huActual : D.edgeFrame.actual Erdos957Cases24.Case2.u ∈ A := by
    rw [D.source_actual]
    exact source.1.property
  have hu : Erdos957Cases24.Case2.u ∈ D.edgeFrame.image A :=
    D.edgeFrame.actual_mem_image_iff.mp huActual
  have huPrevActual : D.edgeFrame.actual Erdos957Cases24.Case2.uPrev ∈ A := by
    rw [D.side_actual]
    exact (cyclicSideVertex P source D.side).property
  have huPrev : Erdos957Cases24.Case2.uPrev ∈ D.edgeFrame.image A :=
    D.edgeFrame.actual_mem_image_iff.mp huPrevActual
  have hmiddleDegree : Erdos957Case24Bridge.unitDegree
      (D.edgeFrame.image A) Erdos957Cases24.Case4.v = 6 := by
    change Erdos957Case24Bridge.unitDegree (D.edgeFrame.image A)
      Erdos957Cases24.Case2.v = 6
    rw [D.edgeFrame.unitDegree_image_actual A, D.middle_actual,
      ← Erdos957CaseClassification.ActualCase24Rows.graph_degree_eq_unitDegree]
    exact D.middle_degree_six
  exact
    Erdos957CaseClassification.ActualCase24Rows.case4_displayedFiveAtV_subset_of_degree_six
      (D.edgeFrame.image_oneSeparated hA) huPrev hu hmiddleDegree

/-- A produced split Case-4 row cannot use a Case-2 emitter as the other
endpoint of its selected common edge.  Pair coherence would force the
partner row to expose a split-right target, whereas a realized Case-2
secondary target certifies that the same row has the disjoint Case-2 shape.
This is the exact adjacent-edge coherence exclusion used by the corrected
mixed collision dispatch. -/
lemma no_case2Secondary_at_incident_partner_of_case4SplitRight
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (Qt : CommonPairedCase4Rows Q.rows t.1 t.property)
    (hsPartner : sourceIndex P W s.1 s.property =
      cyclicSideVertex P (sourceIndex P W t.1 t.property)
        Qt.twoExtreme.side) : False := by
  have hp : cyclicSideVertex P (sourceIndex P W t.1 t.property)
      Qt.twoExtreme.side ∈ sourceVertices P W := by
    rw [← hsPartner]
    exact s.property
  rcases Qt.partner_absent_or_coherent with habsent | hcoherent
  · exact habsent hp
  obtain ⟨partnerMiddleTarget, partnerSecondaryTarget,
      hpartnerMiddleRole, hpartnerSecondaryRole,
      hpartnerMiddleVertex, hpartnerSecondaryVertex,
      _hpartnerSecondaryAssociation⟩ := hcoherent hp
  have hsVertex : s.1 =
      cyclicSideVertex P (sourceIndex P W t.1 t.property)
        Qt.twoExtreme.side := by
    apply Subtype.ext
    simpa [sourceIndex] using congrArg Subtype.val hsPartner
  have hsSource : s =
      ⟨cyclicSideVertex P (sourceIndex P W t.1 t.property)
          Qt.twoExtreme.side, hp⟩ := by
    apply Subtype.ext
    exact hsVertex
  subst s
  have hcase2 := S.target.target_at_role
  rw [hsRole] at hcase2
  cases hrow : Q.rows
      (cyclicSideVertex P (sourceIndex P W t.1 t.property)
        Qt.twoExtreme.side) hp <;>
    simp [hrow, RealizedSourceRow.targetAtRole] at hcase2 hpartnerSecondaryRole

/-- A degree-five Case-2 secondary target has no distinct direct-role
competitor in its genuine seven-source window.  The checked orbit reduction
places every direct source in one of the first two shallow-cone slots; unit
adjacency from either slot forces the Case-2 target to be `e`, contradicting
`target_ne_e_of_degree_five`. -/
lemma Case2SecondaryFormula.no_direct_competitor_at_degree_five
    (hA : IsOneSeparated A)
    {s t : Source P W} {v : Vertex A}
    (D : Case2SecondaryFormula (P := P)
      (source := sourceIndex P W s.1 s.property) v)
    (F : P.FlatAlignedFrameData)
    (htadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 v)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t)
    (hdegree : (unitDistanceGraph A).degree v = 5) : False := by
  have horbit :=
    Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
      D F htadj htWindow hst
  have hcone :
      -(D.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 1 ≤
        (D.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 0 / 5 := by
    rcases horbit with ht | ht
    · rw [ht]
      exact Case2SecondaryFormula.away_cone_div_five D F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0
    · rw [ht]
      exact Case2SecondaryFormula.away_cone_div_five D F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 1
  have he :=
    Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
      D hcone htadj
  exact Case2SecondaryFormula.target_ne_e_of_degree_five hA D hdegree he

/-- Both exceptional secondary roles always carry exactly one doubled
token, independently of the degree branch selected by their source row. -/
lemma RealizedPositiveTarget.token_eq_one_of_exceptional_secondary
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v)
    (hrole : D.role = PairCases.TargetRoleName.case2Secondary ∨
      D.role = PairCases.TargetRoleName.case4SplitRight) :
    R.localCase.tokens v = 1 := by
  rw [D.token_eq_roleWeight]
  rcases hrole with hrole | hrole
  · cases R with
    | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
        simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case2 middle hdegree htwo hmiddleNot T normalized row =>
        simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case3 middle hdegree hone middleCoord row hmiddleVertex =>
        cases row <;>
          simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case4 middle hdegree htwo T normalized row hmiddleVertex =>
        cases row <;>
          simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
  · cases R with
    | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
        simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case2 middle hdegree htwo hmiddleNot T normalized row =>
        simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case3 middle hdegree hone middleCoord row hmiddleVertex =>
        cases row <;>
          simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
    | case4 middle hdegree htwo T normalized row hmiddleVertex =>
        cases row <;>
          simp [hrole, RealizedSourceRow.roleWeight, ArrivalWeight.tokens]

/-- Every realized positive target carries at most two doubled tokens. -/
lemma RealizedPositiveTarget.token_le_two
    {source : {p // p ∈ P.H}} {R : RealizedSourceRow P F.chart source}
    {v : Vertex A} (D : RealizedPositiveTarget R v) :
    R.localCase.tokens v ≤ 2 := by
  rw [D.token_eq_roleWeight]
  cases R.roleWeight D.role <;> simp [ArrivalWeight.tokens]

/-- Arithmetic core of the corrected mixed-triple interface: at a target
of degree at most four, two exceptional half arrivals and one arbitrary
realized arrival always fit the capacity twelve. -/
lemma mixed_triple_fits_of_degree_le_four
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v)
    (hsHalf : (rows s.1 s.property).localCase.tokens v = 1)
    (htHalf : (rows t.1 t.property).localCase.tokens v = 1)
    (hdegree : (unitDistanceGraph A).degree v ≤ 4) :
    2 * (unitDistanceGraph A).degree v +
        (rows s.1 s.property).localCase.tokens v +
        (rows t.1 t.property).localCase.tokens v +
        (rows u.1 u.property).localCase.tokens v ≤ 12 := by
  have hu := RealizedPositiveTarget.token_le_two U.target
  omega

/-- The four genuinely mixed competitor multisets left after the checked
all-Case-2 and two-direct arguments.  Each field is an actual three-arrival
geometry statement.  In particular, no field claims the false pairwise
uniqueness of a Case-2 half arrival against a Case-4 half arrival. -/
structure Case2SecondaryNoThreeResiduals
    (rows : HasRealizedSourceRows P W F.chart) where
  case2_direct : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case2Secondary →
    IsDirectTargetRole U.target.role →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  case2_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case2Secondary →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  direct_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    IsDirectTargetRole T.target.role →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  two_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case4SplitRight →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

/-- Corrected geometric frontier for mixed exceptional triples.  The paper
allows three contributors whenever their total weight fits.  Consequently
these fields exclude only the genuinely overcharging situation: three half
arrivals at a degree-five target.  A whole third arrival is handled
separately by `LocalCase.whole_target_degree_le_four`. -/
structure Case2SecondaryDegreeFiveResiduals
    (rows : HasRealizedSourceRows P W F.chart) where
  case2_direct : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case2Secondary →
    IsDirectTargetRole U.target.role →
    (rows u.1 u.property).localCase.tokens v = 1 →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  case2_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case2Secondary →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  direct_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    IsDirectTargetRole T.target.role →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    (rows t.1 t.property).localCase.tokens v = 1 →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  two_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case4SplitRight →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

/-- After the degree-five endpoint exclusion, only the two configurations
containing no direct source remain.  They are precisely the cross-role
Case-2/Case-4 split geometry; the two fields involving a direct role are
discharged below from the shallow-cone `e` forcing theorem. -/
structure Case2SecondarySplitDegreeFiveResiduals
    (rows : HasRealizedSourceRows P W F.chart) where
  case2_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case2Secondary →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False
  two_split_right : ∀ {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case4SplitRight →
    U.target.role = PairCases.TargetRoleName.case4SplitRight →
    (unitDistanceGraph A).degree v = 5 →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    s ≠ t → s ≠ u → t ≠ u → False

/-- Fill the two direct-role fields of the weighted Case-2 frontier with
the checked degree-five shallow-cone contradiction. -/
theorem case2SecondaryDegreeFiveResiduals_of_split_residuals
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    (K : Case2SecondarySplitDegreeFiveResiduals (F := F) rows) :
    Case2SecondaryDegreeFiveResiduals (F := F) rows where
  case2_direct := by
    intro s t u v S T U hsRole htRole huDirect huHalf hdegree
      htWindow huWindow hst hsu htu
    obtain ⟨D⟩ := exists_case2SecondaryFormula S.target hsRole
    exact Case2SecondaryFormula.no_direct_competitor_at_degree_five
      hA D F (U.target.adj_source_of_directRole huDirect)
        huWindow hsu hdegree
  case2_split_right := K.case2_split_right
  direct_split_right := by
    intro s t u v S T U hsRole htDirect huRole htHalf hdegree
      htWindow huWindow hst hsu htu
    obtain ⟨D⟩ := exists_case2SecondaryFormula S.target hsRole
    exact Case2SecondaryFormula.no_direct_competitor_at_degree_five
      hA D F (T.target.adj_source_of_directRole htDirect)
        htWindow hst hdegree
  two_split_right := K.two_split_right

/-- If two arrivals are half-weight and a degree-five realization with a
third half arrival is excluded, the three selected contributions satisfy
the exact local capacity inequality. -/
lemma mixed_triple_fits_of_no_degree_five_three_halves
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v)
    (hsHalf : (rows s.1 s.property).localCase.tokens v = 1)
    (htHalf : (rows t.1 t.property).localCase.tokens v = 1)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hexclude : (rows u.1 u.property).localCase.tokens v = 1 →
      (unitDistanceGraph A).degree v = 5 → False) :
    2 * (unitDistanceGraph A).degree v +
        (rows s.1 s.property).localCase.tokens v +
        (rows t.1 t.property).localCase.tokens v +
        (rows u.1 u.property).localCase.tokens v ≤ 12 := by
  rcases (rows u.1 u.property).localCase.positive_weight U.positive with
      huHalf | huWhole
  · by_cases hfour : (unitDistanceGraph A).degree v ≤ 4
    · exact mixed_triple_fits_of_degree_le_four S T U hsHalf htHalf hfour
    · exact (hexclude huHalf (by omega)).elim
  · have hfour :=
      (rows u.1 u.property).localCase.whole_target_degree_le_four huWhole
    exact mixed_triple_fits_of_degree_le_four S T U hsHalf htHalf hfour

private lemma three_arrival_associations_have_equal_pair
    (a b c : ArrivalAssociation) :
    a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- Exact capacity estimate for any three distinct realized arrivals with a
Case-2-secondary anchor.  The all-Case-2 and two-direct configurations are
already impossible by the checked formula geometry.  Each genuinely mixed
configuration is reduced to one degree-five leaf from
`Case2SecondaryDegreeFiveResiduals`; degree at most four and whole arrivals
are discharged arithmetically. -/
theorem case2_secondary_triple_fits_of_degree_five_residuals
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    (locality : SourceLocalityCertificates P W F)
    (K : Case2SecondaryDegreeFiveResiduals (F := F) rows) :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) rows s v)
      (T : RealizedArrivalAt (F := F) rows t v)
      (U : RealizedArrivalAt (F := F) rows u v),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u →
      2 * (unitDistanceGraph A).degree v +
          (rows s.1 s.property).localCase.tokens v +
          (rows t.1 t.property).localCase.tokens v +
          (rows u.1 u.property).localCase.tokens v ≤ 12 := by
  intro s t u v S T U hsRole htWindow huWindow hst hsu htu
  have hsHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary S.target
    (Or.inl hsRole)
  have hdegree : (unitDistanceGraph A).degree v ≤ 5 := by
    rw [S.target.vertex_eq]
    exact S.target.target.degree_le_five
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  by_cases ht2 : T.target.role = PairCases.TargetRoleName.case2Secondary
  · have htHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary T.target
      (Or.inl ht2)
    by_cases hu2 : U.target.role = PairCases.TargetRoleName.case2Secondary
    · rcases three_arrival_associations_have_equal_pair
          S.descriptor.association T.descriptor.association
          U.descriptor.association with hST | hSU | hTU
      · exact (hst (case2Secondary_same_association_source_eq
          S T hsRole ht2 htWindow hST)).elim
      · exact (hsu (case2Secondary_same_association_source_eq
          S U hsRole hu2 huWindow hSU)).elim
      · have huFromT := locality.competing_source_in_window htPos huPos
        exact (htu (case2Secondary_same_association_source_eq
          T U ht2 hu2 huFromT hTU)).elim
    · by_cases hu4 : U.target.role = PairCases.TargetRoleName.case4SplitRight
      · exact mixed_triple_fits_of_no_degree_five_three_halves
          S T U hsHalf htHalf hdegree
          (fun _huHalf hfive ↦ K.case2_split_right S T U hsRole ht2 hu4
            hfive htWindow huWindow hst hsu htu)
      · have huDirect : IsDirectTargetRole U.target.role := by
          cases hrole : U.target.role <;>
            simp_all [IsDirectTargetRole]
        exact mixed_triple_fits_of_no_degree_five_three_halves
          S T U hsHalf htHalf hdegree
          (fun huHalf hfive ↦ K.case2_direct S T U hsRole ht2 huDirect
            huHalf hfive htWindow huWindow hst hsu htu)
  · by_cases ht4 : T.target.role = PairCases.TargetRoleName.case4SplitRight
    · have htHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary T.target
        (Or.inr ht4)
      by_cases hu2 : U.target.role = PairCases.TargetRoleName.case2Secondary
      · have huHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary U.target
          (Or.inl hu2)
        have hfit := mixed_triple_fits_of_no_degree_five_three_halves
          S U T hsHalf huHalf hdegree
          (fun _htHalf hfive ↦ K.case2_split_right S U T hsRole hu2 ht4
            hfive huWindow htWindow hsu hst htu.symm)
        omega
      · by_cases hu4 : U.target.role = PairCases.TargetRoleName.case4SplitRight
        · exact mixed_triple_fits_of_no_degree_five_three_halves
            S T U hsHalf htHalf hdegree
            (fun _huHalf hfive ↦ K.two_split_right S T U hsRole ht4 hu4
              hfive htWindow huWindow hst hsu htu)
        · have huDirect : IsDirectTargetRole U.target.role := by
            cases hrole : U.target.role <;>
              simp_all [IsDirectTargetRole]
          have hfit := mixed_triple_fits_of_no_degree_five_three_halves
            S T U hsHalf htHalf hdegree
            (fun huHalf hfive ↦ K.direct_split_right S U T hsRole huDirect ht4
              huHalf hfive huWindow htWindow hsu hst htu.symm)
          exact hfit
    · have htDirect : IsDirectTargetRole T.target.role := by
        cases hrole : T.target.role <;>
          simp_all [IsDirectTargetRole]
      by_cases hu2 : U.target.role = PairCases.TargetRoleName.case2Secondary
      · have huHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary U.target
          (Or.inl hu2)
        have hfit := mixed_triple_fits_of_no_degree_five_three_halves
          S U T hsHalf huHalf hdegree
          (fun htHalf hfive ↦ K.case2_direct S U T hsRole hu2 htDirect
            htHalf hfive huWindow htWindow hsu hst htu.symm)
        omega
      · by_cases hu4 : U.target.role = PairCases.TargetRoleName.case4SplitRight
        · have huHalf := RealizedPositiveTarget.token_eq_one_of_exceptional_secondary U.target
            (Or.inr hu4)
          have hfit := mixed_triple_fits_of_no_degree_five_three_halves
            S U T hsHalf huHalf hdegree
            (fun htHalf hfive ↦ K.direct_split_right S T U hsRole htDirect hu4
              htHalf hfive htWindow huWindow hst hsu htu)
          omega
        · have huDirect : IsDirectTargetRole U.target.role := by
            cases hrole : U.target.role <;>
              simp_all [IsDirectTargetRole]
          obtain ⟨D⟩ := exists_case2SecondaryFormula S.target hsRole
          exact (Case2SecondaryFormula.no_two_direct_competitors_in_window
            hA D F
            (T.target.adj_source_of_directRole htDirect)
            (U.target.adj_source_of_directRole huDirect)
            htWindow huWindow hst hsu htu).elim

/-- Exact `SecondaryRoleCollisionKernels.case2_secondary_no_three` field
assembled from the checked direct/direct and Case-2/Case-2 geometry plus the
four honest mixed triple leaves above. -/
theorem case2_secondary_no_three_of_residuals
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    (locality : SourceLocalityCertificates P W F)
    (K : Case2SecondaryNoThreeResiduals (F := F) rows) :
    ∀ {s t u : Source P W} {v : Vertex A}
      (Ds : RealizedPositiveTarget (rows s.1 s.property) v)
      (Dt : RealizedPositiveTarget (rows t.1 t.property) v)
      (Du : RealizedPositiveTarget (rows u.1 u.property) v),
      Ds.role = PairCases.TargetRoleName.case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False := by
  intro s t u v Ds Dt Du hsRole htWindow huWindow hst hsu htu
  let S := realizedArrivalAtOfTarget (F := F) rows s v Ds
  let T := realizedArrivalAtOfTarget (F := F) rows t v Dt
  let U := realizedArrivalAtOfTarget (F := F) rows u v Du
  have hsPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) s v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using S.positive
  have htPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) t v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using T.positive
  have huPos : 0 < sourceTokens P W F.chart
      (localCasesOfRealizedRows (F := F) rows) u v := by
    simpa [sourceTokens, selectedCase, localCasesOfRealizedRows] using U.positive
  by_cases ht2 : Dt.role = PairCases.TargetRoleName.case2Secondary
  · by_cases hu2 : Du.role = PairCases.TargetRoleName.case2Secondary
    · rcases three_arrival_associations_have_equal_pair
          S.descriptor.association T.descriptor.association
          U.descriptor.association with hST | hSU | hTU
      · exact hst (case2Secondary_same_association_source_eq
          S T hsRole ht2 htWindow hST)
      · exact hsu (case2Secondary_same_association_source_eq
          S U hsRole hu2 huWindow hSU)
      · have huFromT := locality.competing_source_in_window htPos huPos
        exact htu (case2Secondary_same_association_source_eq
          T U ht2 hu2 huFromT hTU)
    · by_cases hu4 : Du.role = PairCases.TargetRoleName.case4SplitRight
      · exact K.case2_split_right S T U hsRole ht2 hu4
          htWindow huWindow hst hsu htu
      · have huDirect : IsDirectTargetRole Du.role := by
          cases hrole : Du.role <;>
            simp_all [IsDirectTargetRole]
        exact K.case2_direct S T U hsRole ht2 huDirect
          htWindow huWindow hst hsu htu
  · by_cases ht4 : Dt.role = PairCases.TargetRoleName.case4SplitRight
    · by_cases hu2 : Du.role = PairCases.TargetRoleName.case2Secondary
      · exact K.case2_split_right S U T hsRole hu2 ht4
          huWindow htWindow hsu hst htu.symm
      · by_cases hu4 : Du.role = PairCases.TargetRoleName.case4SplitRight
        · exact K.two_split_right S T U hsRole ht4 hu4
            htWindow huWindow hst hsu htu
        · have huDirect : IsDirectTargetRole Du.role := by
            cases hrole : Du.role <;>
              simp_all [IsDirectTargetRole]
          exact K.direct_split_right S U T hsRole huDirect ht4
            huWindow htWindow hsu hst htu.symm
    · have htDirect : IsDirectTargetRole Dt.role := by
        cases hrole : Dt.role <;>
          simp_all [IsDirectTargetRole]
      by_cases hu2 : Du.role = PairCases.TargetRoleName.case2Secondary
      · exact K.case2_direct S U T hsRole hu2 htDirect
          huWindow htWindow hsu hst htu.symm
      · by_cases hu4 : Du.role = PairCases.TargetRoleName.case4SplitRight
        · exact K.direct_split_right S T U hsRole htDirect hu4
            htWindow huWindow hst hsu htu
        · have huDirect : IsDirectTargetRole Du.role := by
            cases hrole : Du.role <;>
              simp_all [IsDirectTargetRole]
          obtain ⟨D⟩ := exists_case2SecondaryFormula Ds hsRole
          exact Case2SecondaryFormula.no_two_direct_competitors_in_window
            hA D F
            (Dt.adj_source_of_directRole htDirect)
            (Du.adj_source_of_directRole huDirect)
            htWindow huWindow hst hsu htu

/-- The three genuinely formula-sensitive projections left after the checked
metric dispatch.  This is an explicit geometric frontier, not a capacity or
collision assumption: the direct field is only a signed-coordinate
consequence of its exact role, while the two exceptional fields retain both
arrival descriptors. -/
lemma degree_eq_five_of_coherent_case4SplitLeft
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {t : Source P W} {v : Vertex A}
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hrole : T.target.role = PairCases.TargetRoleName.case4SplitLeft) :
    (unitDistanceGraph A).degree v = 5 := by
  have hsplit : (Q.rows t.1 t.property).IsCase4Split := by
    have htarget := T.target.target_at_role
    rw [hrole] at htarget
    cases hrow : Q.rows t.1 t.property with
    | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
        simp [hrow, RealizedSourceRow.targetAtRole] at htarget
    | case2 middle hdegree htwo hmiddleNot twoExtreme normalized row =>
        simp [hrow, RealizedSourceRow.targetAtRole] at htarget
    | case3 middle hdegree hone middleCoord row hmiddleVertex =>
        cases row <;>
          simp [hrow, RealizedSourceRow.targetAtRole] at htarget
    | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
        cases row with
        | whole middleTarget hm hfour =>
            simp [hrow, RealizedSourceRow.targetAtRole] at htarget
        | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
            exact ⟨lowTarget, by
              simp [hrow, RealizedSourceRow.targetAtRole]⟩
        | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
            exact ⟨sideTarget, by
              simp [hrow, RealizedSourceRow.targetAtRole]⟩
        | pairedSplit commonFrame farthest branch right hright middleTarget
            secondaryTarget hsource hm hs hne =>
            exact ⟨secondaryTarget, by
              simp [hrow, RealizedSourceRow.targetAtRole]⟩
  let Qt := Q.case4_pair t.1 t.property hsplit
  have htarget := T.target.target_at_role
  rw [hrole, Qt.current_middle_role] at htarget
  have htargetEq := Option.some.inj htarget
  have hvMiddle : v = Qt.middle := by
    calc
      v = T.target.target.vertex := T.target.vertex_eq
      _ = Qt.currentMiddleTarget.vertex := by rw [htargetEq]
      _ = Qt.middle := Qt.current_middle_vertex
  rw [hvMiddle]
  exact Qt.middle_degree_five

private def IsPairedDirectArrivalFormula
    {source : {p // p ∈ P.H}} {v : Vertex A}
    {association : ArrivalAssociation} :
    DirectArrivalFormula F.chart source v association → Prop
  | .paired _ _ _ _ => True
  | _ => False

private lemma role_eq_case4Primary_or_splitLeft_of_paired_direct_formula
    {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P F.chart source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (E : RealizedArrivalDescriptor R D.role D.target)
    (hdirect : IsDirectTargetRole D.role)
    (hpaired : IsPairedDirectArrivalFormula
      (Erdos957DirectSameSide.directArrivalFormula D E hdirect)) :
    D.role = PairCases.TargetRoleName.case4Primary ∨
      D.role = PairCases.TargetRoleName.case4SplitLeft := by
  rcases D with ⟨role, target, htarget, hv⟩
  subst v
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      cases role with
      | case1Left =>
          have heq : row.left = target := by
            simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
          subst target
          simp [Erdos957DirectSameSide.directArrivalFormula,
            IsPairedDirectArrivalFormula] at hpaired
      | case1Right =>
          have heq : row.right = target := by
            simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
          subst target
          simp [Erdos957DirectSameSide.directArrivalFormula,
            IsPairedDirectArrivalFormula] at hpaired
      | case2Outer | case2Secondary | case3Middle | case3Secondary |
          case4Primary | case4SecondaryLow | case4SplitLeft | case4SplitRight =>
          simp [RealizedSourceRow.targetAtRole] at htarget
  | case2 middle hdegree htwo hmiddleNotHull twoExtreme normalized row =>
      cases role with
      | case2Outer =>
          have heq : row.outer = target := by
            simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
          subst target
          simp [Erdos957DirectSameSide.directArrivalFormula,
            IsPairedDirectArrivalFormula] at hpaired
      | case2Secondary =>
          simp [IsDirectTargetRole] at hdirect
      | case1Left | case1Right | case3Middle | case3Secondary |
          case4Primary | case4SecondaryLow | case4SplitLeft | case4SplitRight =>
          simp [RealizedSourceRow.targetAtRole] at htarget
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row with
      | low middleTarget hm hu hfour =>
          cases role with
          | case3Middle =>
              have heq : middleTarget = target := by
                simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
              subst target
              change False at hpaired
              exact hpaired.elim
          | case1Left | case1Right | case2Outer | case2Secondary |
              case3Secondary | case4Primary | case4SecondaryLow |
              case4SplitLeft | case4SplitRight =>
              simp [RealizedSourceRow.targetAtRole] at htarget
      | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
          cases role with
          | case3Middle =>
              have heq : middleTarget = target := by
                simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
              subst target
              change False at hpaired
              exact hpaired.elim
          | case3Secondary =>
              have heq : secondaryTarget = target := by
                simpa [RealizedSourceRow.targetAtRole] using Option.some.inj htarget
              subst target
              simp [Erdos957DirectSameSide.directArrivalFormula,
                IsPairedDirectArrivalFormula] at hpaired
          | case1Left | case1Right | case2Outer | case2Secondary |
              case4Primary | case4SecondaryLow | case4SplitLeft | case4SplitRight =>
              simp [RealizedSourceRow.targetAtRole] at htarget
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hm hfour =>
          cases role with
          | case4Primary => exact Or.inl rfl
          | case1Left | case1Right | case2Outer | case2Secondary |
              case3Middle | case3Secondary | case4SecondaryLow |
              case4SplitLeft | case4SplitRight =>
              simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          cases role with
          | case4SplitLeft => exact Or.inr rfl
          | case4SplitRight => simp [IsDirectTargetRole] at hdirect
          | case1Left | case1Right | case2Outer | case2Secondary |
              case3Middle | case3Secondary | case4Primary | case4SecondaryLow =>
              simp [RealizedSourceRow.targetAtRole] at htarget
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          cases role with
          | case4SplitLeft => exact Or.inr rfl
          | case4SplitRight => simp [IsDirectTargetRole] at hdirect
          | case1Left | case1Right | case2Outer | case2Secondary |
              case3Middle | case3Secondary | case4Primary | case4SecondaryLow =>
              simp [RealizedSourceRow.targetAtRole] at htarget
      | pairedSplit commonFrame farthest branch right hright middleTarget
          secondaryTarget hsource hm hs hne =>
          cases role with
          | case4SplitLeft => exact Or.inr rfl
          | case4SplitRight => simp [IsDirectTargetRole] at hdirect
          | case1Left | case1Right | case2Outer | case2Secondary |
              case3Middle | case3Secondary | case4Primary | case4SecondaryLow =>
              simp [RealizedSourceRow.targetAtRole] at htarget

/-- The direct-coordinate field needed by the Case-2 same-side reducer is
already forced by coherent realized geometry.  A distinct direct source is
in one of the first two away slots.  One-separation puts it past `x = 2`;
the exact direct formula then gives the cyclic association, opposite the
Case-2 secondary association.  The paired first-slot form is necessarily a
degree-five Case-4 split-left middle and is excluded by the checked
degree-five Case-2 contact lemma. -/
lemma coherent_case2Secondary_direct_fst_le
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (ht2 : T.target.role ≠ PairCases.TargetRoleName.case2Secondary)
    (ht4 : T.target.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htPrimary : T.target.role ≠ PairCases.TargetRoleName.case4Primary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    (B.formula.edgeFrame.toCanonical
      (sourceIndex P W t.1 t.property).1) 0 ≤ 3 / 2 := by
  by_contra hx
  have hst : s ≠ t := by
    intro h
    subst t
    have hadj := T.target.direct_target_adj ht2 ht4
    exact B.formula.not_source_adj_target hadj
  have htDirect : IsDirectTargetRole T.target.role := by
    cases hrole : T.target.role <;>
      simp_all [IsDirectTargetRole]
  have hadj := T.target.adj_source_of_directRole htDirect
  have horbit := Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
    B.formula F hadj htWindow hst
  have hi := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have hit := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W t
  have hcone :
      -(B.formula.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 1 ≤
        (B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 0 / 5 := by
    rcases horbit with ht | ht
    · rw [ht]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F hi 0
    · rw [ht]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F hi 1
  have hy :
      (B.formula.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 1 < 0 := by
    rcases horbit with ht | ht
    · rw [ht]
      exact (Case2SecondaryFormula.away_prefix_bounds B.formula F hi 0).1
    · rw [ht]
      exact (Case2SecondaryFormula.away_prefix_bounds B.formula F hi 1).1
  have hgt : (2 : ℝ) <
      (B.formula.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 0 :=
    Case2SecondaryFormula.direct_competitor_fst_gt_two_of_shallow_cone
      hA B.formula (sourceIndex P W t.1 t.property).property hcone hy hadj
  generalize hFT : Erdos957DirectSameSide.directArrivalFormula
    T.target T.descriptor htDirect = FT
  have hdirectAssoc :
      T.descriptor.association = cyclicSideAssociation B.formula.side := by
    rcases horbit with ht | ht
    · cases FT with
      | singleton hone middleCoord htarget hassociation =>
          exact Case2SecondaryFormula.singleton_association_at_away_first_of_fst_gt_two
            B.formula F hi hit ht hgt hadj htarget hassociation
      | outer O =>
          apply Case2SecondaryFormula.outer_association_of_shallow_position
            (t := sourceIndex P W t.1 t.property) B.formula F
          · linarith
          · exact hy
          · rw [ht]
            exact (Case2SecondaryFormula.away_prefix_bounds
              B.formula F hi 0).2.2
          · exact hadj
          · exact O
      | paired middle twoExtreme htarget hassociation =>
          have htSplitLeft :
              T.target.role = PairCases.TargetRoleName.case4SplitLeft := by
            rcases role_eq_case4Primary_or_splitLeft_of_paired_direct_formula
                T.target T.descriptor htDirect (by rw [hFT]; trivial) with
              hprimary | hsplit
            · exact (htPrimary hprimary).elim
            · exact hsplit
          have hdegree := degree_eq_five_of_coherent_case4SplitLeft Q T htSplitLeft
          exact (Case2SecondaryFormula.no_direct_competitor_at_degree_five
            hA B.formula F hadj htWindow hst hdegree).elim
    · cases FT with
      | singleton hone middleCoord htarget hassociation =>
          exact Case2SecondaryFormula.singleton_association_at_away_second
            B.formula F hi hit ht hadj htarget hassociation
      | outer O =>
          exact Case2SecondaryFormula.outer_association_at_away_second
            B.formula F hi ht hadj O
      | paired middle twoExtreme htarget hassociation =>
          exact Case2SecondaryFormula.paired_association_at_away_second
            B.formula F hi ht twoExtreme htarget hassociation
  rw [B.association_eq, hdirectAssoc] at hassoc
  cases hside : B.formula.side <;>
    simp [hside, oppositeCyclicSideAssociation,
      cyclicSideAssociation] at hassoc

structure Case2SecondarySameSideResiduals
    (rows : HasRealizedSourceRows P W F.chart) where
  direct_fst_le : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor),
    T.target.role ≠ PairCases.TargetRoleName.case2Secondary →
    T.target.role ≠ PairCases.TargetRoleName.case4SplitRight →
    T.target.role ≠ PairCases.TargetRoleName.case4Primary →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association →
    (B.formula.edgeFrame.toCanonical
      (sourceIndex P W t.1 t.property).1) 0 ≤ 3 / 2
  case4_split_right : ∀ {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v),
    S.target.role = PairCases.TargetRoleName.case2Secondary →
    T.target.role = PairCases.TargetRoleName.case4SplitRight →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    S.descriptor.association = T.descriptor.association → s = t

/-- Exact pairwise Case-2 field consumed by
`RoleAnchoredSameSideKernels`.  All orbit, support, one-separation, and whole
Case-4 branches are discharged here; only the three formula projections
named by `Case2SecondarySameSideResiduals` remain external. -/
theorem case2_secondary_same_side_source_unique_of_residuals
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    (K : Case2SecondarySameSideResiduals (F := F) rows)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) : s = t := by
  by_contra hst
  obtain ⟨B⟩ := nonempty_case2SecondaryArrivalFormula
    S.target S.descriptor hsRole
  by_cases ht2 : T.target.role = PairCases.TargetRoleName.case2Secondary
  · by_cases htAway : sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property)
          (Classical.choice (nonempty_case2SecondaryArrivalFormula
            S.target S.descriptor hsRole)).formula.side 0
    · exact (no_case2Secondary_same_association_at_away_first
        S T hsRole ht2 hassoc htAway).elim
    · by_cases htIncident : sourceIndex P W t.1 t.property =
          cyclicSideVertex P (sourceIndex P W s.1 s.property)
            (Classical.choice (nonempty_case2SecondaryArrivalFormula
              S.target S.descriptor hsRole)).formula.side
      · exact (no_case2Secondary_same_association_at_incident_first
          S T hsRole ht2 hassoc htIncident).elim
      · by_cases htAwaySecond : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.awayHullVertex P
              (sourceIndex P W s.1 s.property)
              (Classical.choice (nonempty_case2SecondaryArrivalFormula
                S.target S.descriptor hsRole)).formula.side 1
        · exact (no_case2Secondary_same_association_at_away_second
            S T hsRole ht2 hassoc htAwaySecond).elim
        · by_cases htIncidentSecond : sourceIndex P W t.1 t.property =
            incidentHullVertex P (sourceIndex P W s.1 s.property)
              (Classical.choice (nonempty_case2SecondaryArrivalFormula
                S.target S.descriptor hsRole)).formula.side 1
          · exact (no_case2Secondary_same_association_at_incident_second
              S T hsRole ht2 hassoc htIncidentSecond).elim
          · by_cases htIncidentThird : sourceIndex P W t.1 t.property =
                incidentHullVertex P (sourceIndex P W s.1 s.property)
                  (Classical.choice (nonempty_case2SecondaryArrivalFormula
                    S.target S.descriptor hsRole)).formula.side 2
            · exact (no_case2Secondary_competitor_at_incident_third
                S T hsRole ht2 htIncidentThird).elim
            · by_cases htAwayThird : sourceIndex P W t.1 t.property =
                  Erdos957Case4NoThree.awayHullVertex P
                    (sourceIndex P W s.1 s.property)
                    (Classical.choice
                      (nonempty_case2SecondaryArrivalFormula
                        S.target S.descriptor hsRole)).formula.side 2
              · exact (no_case2Secondary_same_association_at_away_third
                  S T hsRole ht2 hassoc htAwayThird).elim
              · have horbit :=
                    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
                      htWindow hst
                cases hside : (Classical.choice
                    (nonempty_case2SecondaryArrivalFormula
                      S.target S.descriptor hsRole)).formula.side with
                | previous =>
                    rcases horbit with h | h | h | h | h | h
                    · exact htIncidentThird (by
                        simpa [incidentHullVertex, hside] using h)
                    · exact htIncidentSecond (by
                        simpa [incidentHullVertex, hside] using h)
                    · exact htIncident (by
                        simpa [cyclicSideVertex, hside] using h)
                    · exact htAway (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                    · exact htAwaySecond (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                    · exact htAwayThird (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                | next =>
                    rcases horbit with h | h | h | h | h | h
                    · exact htAwayThird (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                    · exact htAwaySecond (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                    · exact htAway (by
                        simpa [Erdos957Case4NoThree.awayHullVertex, hside]
                          using h)
                    · exact htIncident (by
                        simpa [cyclicSideVertex, hside] using h)
                    · exact htIncidentSecond (by
                        simpa [incidentHullVertex, hside] using h)
                    · exact htIncidentThird (by
                        simpa [incidentHullVertex, hside] using h)
  by_cases ht4 : T.target.role = PairCases.TargetRoleName.case4SplitRight
  · exact hst (K.case4_split_right S T hsRole ht4 htWindow hassoc)
  have hadj := T.target.direct_target_adj ht2 ht4
  by_cases htPrimary : T.target.role = PairCases.TargetRoleName.case4Primary
  · exact no_case2Secondary_case4Primary_same_association_in_window
      S.target T.target S.descriptor T.descriptor hsRole htPrimary
      htWindow hassoc hst
  have horbit :=
    Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
      B.formula F hadj htWindow hst
  have hcone :
      -(B.formula.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 1 ≤
        (B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 0 / 5 := by
    rcases horbit with h | h
    · rw [h]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0
    · rw [h]
      exact Case2SecondaryFormula.away_cone_div_five B.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 1
  have hy :
      (B.formula.edgeFrame.toCanonical
        (sourceIndex P W t.1 t.property).1) 1 < 0 := by
    rcases horbit with h | h
    · rw [h]
      exact (Case2SecondaryFormula.away_prefix_bounds B.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0).1
    · rw [h]
      exact (Case2SecondaryFormula.away_prefix_bounds B.formula F
        (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 1).1
  exact Case2SecondaryFormula.no_direct_competitor_of_shallow_cone_of_fst_le
    hA B.formula (sourceIndex P W t.1 t.property).property hcone
    (K.direct_fst_le S T B ht2 ht4 htPrimary htWindow hassoc) hy hadj

/-- Record-field form of
`case2_secondary_same_side_source_unique_of_residuals`.  This is exactly the
`case2_secondary` component requested by `RoleAnchoredSameSideKernels`; in
particular it does not assume either of the other two role kernels. -/
theorem Case2SecondarySameSideResiduals.case2_secondary_role_kernel
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    (K : Case2SecondarySameSideResiduals (F := F) rows) :
    ∀ {s t : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) rows s v)
      (T : RealizedArrivalAt (F := F) rows t v),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      S.descriptor.association = T.descriptor.association → s = t := by
  intro s t v S T hsRole htWindow hassoc
  exact case2_secondary_same_side_source_unique_of_residuals
    hA K S T hsRole htWindow hassoc

end Erdos957Case2SecondaryNoThree

#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.competitor_above_target_of_shallow_cone
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.competitor_fst_le_five_halves_of_shallow_cone
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_adj_incident_partner
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_competitor_fst_gt_two_of_shallow_cone
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_two_direct_competitors_of_shallow_cone'
#print axioms Erdos957Case2SecondaryNoThree.Case2Case4WholeSameAssociationPlacement.no_collision_of_shallow_frame
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_direct_competitor_of_shallow_cone_of_fst_le
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_competitor_eq_away_first_or_second
#print axioms Erdos957Case2SecondaryNoThree.Case2Case4WholeSameAssociationPlacement.no_collision_of_flat_window
#print axioms Erdos957Case2SecondaryNoThree.no_case2Secondary_case4Primary_same_association_in_window
#print axioms Erdos957Case2SecondaryNoThree.eq_case2_v_or_uNext_of_dist_u_one_dist_wNext_sqrtThree
#print axioms Erdos957Case2SecondaryNoThree.no_case2Secondary_same_association_at_away_first
#print axioms Erdos957Case2SecondaryNoThree.no_case2Secondary_same_association_at_incident_first
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_two_direct_competitors_in_window
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.competitor_within_two_eq_away_first_second_or_third
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_competitor_eq_away_first_second_or_third
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case4SplitRight_competitor_eq_away_first_second_or_third
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.direct_case4SplitRight_competitors_away_placements
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_direct_competitors_away_placements
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.side_target_sq_distance_cases
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.not_side_adj_target
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.source_target_sq_eq_three_of_target_eq_e
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_case2_at_away_first_direct_at_away_second
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_direct_competitors_away_placements_three
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_side_opposite_of_direct_away_zero_case2_away_one
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_side_opposite_of_direct_away_one_case2_away_two
#print axioms Erdos957Case2SecondaryNoThree.case2Secondary_same_association_source_eq
#print axioms Erdos957Case2SecondaryNoThree.case2_secondary_no_three_of_residuals
#print axioms Erdos957Case2SecondaryNoThree.case2_secondary_same_side_source_unique_of_residuals
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondarySameSideResiduals.case2_secondary_role_kernel
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.target_ne_e_of_degree_five
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.case2_competitor_near_slots_of_degree_five
#print axioms Erdos957Case2SecondaryNoThree.Case2SecondaryFormula.no_direct_competitor_at_degree_five
#print axioms Erdos957Case2SecondaryNoThree.case2SecondaryDegreeFiveResiduals_of_split_residuals
#print axioms Erdos957Case2SecondaryNoThree.case2_secondary_triple_fits_of_degree_five_residuals
