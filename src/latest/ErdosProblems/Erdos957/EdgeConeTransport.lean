import ErdosProblems.Erdos957.FlatPrefixCone

/-!
# Transporting the flat-prefix cone to an incident-edge chart

The geometric chart comparison reduces to the two elementary estimates in
this file.  If `(c,s)` is a unit-edge direction within four degrees of the
positive horizontal axis, rotating the bisector coordinates `(x,y)` into
that edge frame preserves a slightly wider shallow cone.  The deliberately
slack rational constants avoid any hidden appeal to a chart identity.
-/

noncomputable section

namespace Erdos957EdgeConeTransport

/-- A `1/10` shallow cone remains inside the `1/5` shallow cone after a
small edge-frame rotation.  The assumptions `c≥399/400` and `|s|≤7/100`
are the rational consequences of the checked four-degree polar bounds. -/
lemma shallow_cone_under_small_rotation
    {c s x y : ℝ}
    (hc : (399 / 400 : ℝ) ≤ c)
    (hs : |s| ≤ (7 / 100 : ℝ))
    (hx : 0 ≤ x) (hy : y ≤ 0)
    (hcone : -y ≤ x / 10) :
    -(c * y - s * x) ≤ (c * x + s * y) / 5 := by
  have hc0 : 0 ≤ c := by norm_num at hc ⊢; linarith
  have hsUpper : s ≤ (7 / 100 : ℝ) := le_trans (le_abs_self s) hs
  have hA0 : 0 ≤ x / 5 + y := by linarith
  have hA : x / 10 ≤ x / 5 + y := by linarith
  have hcA : (399 / 400 : ℝ) * (x / 5 + y) ≤
      c * (x / 5 + y) := by
    exact mul_le_mul_of_nonneg_right hc hA0
  have hB0 : 0 ≤ x - y / 5 := by linarith
  have hB : x - y / 5 ≤ (51 / 50 : ℝ) * x := by linarith
  have hsB : s * (x - y / 5) ≤
      (7 / 100 : ℝ) * (x - y / 5) := by
    exact mul_le_mul_of_nonneg_right hsUpper hB0
  have hBscale : (7 / 100 : ℝ) * (x - y / 5) ≤
      (7 / 100 : ℝ) * ((51 / 50 : ℝ) * x) := by
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have hmargin : 0 ≤
      (399 / 400 : ℝ) * (x / 10) -
        (7 / 100 : ℝ) * ((51 / 50 : ℝ) * x) := by
    nlinarith
  nlinarith

/-- The `x>29/10` three-step estimate retains `x>5/2` in the same rotated
edge frame. -/
lemma fst_gt_five_halves_under_small_rotation
    {c s x y : ℝ}
    (hc : (399 / 400 : ℝ) ≤ c)
    (hs : |s| ≤ (7 / 100 : ℝ))
    (hy : y ≤ 0) (hcone : -y ≤ x / 10)
    (hx : (29 / 10 : ℝ) < x) :
    (5 / 2 : ℝ) < c * x + s * y := by
  have hx0 : 0 ≤ x := by linarith
  have hsUpper : s ≤ (7 / 100 : ℝ) := le_trans (le_abs_self s) hs
  have hcy : (399 / 400 : ℝ) * x ≤ c * x := by
    exact mul_le_mul_of_nonneg_right hc hx0
  have hylower : -(x / 10) ≤ y := by linarith
  have herr : -(7 / 100 : ℝ) * (x / 10) ≤
      (7 / 100 : ℝ) * y := by
    calc
      -(7 / 100 : ℝ) * (x / 10) =
          (7 / 100 : ℝ) * (-(x / 10)) := by ring
      _ ≤ (7 / 100 : ℝ) * y :=
        mul_le_mul_of_nonneg_left hylower (by norm_num)
  have hsy : (7 / 100 : ℝ) * y ≤ s * y := by
    exact mul_le_mul_of_nonpos_right hsUpper hy
  have hsy' : -(7 / 100 : ℝ) * (x / 10) ≤ s * y := by
    exact herr.trans hsy
  nlinarith

/-! ## Sign transport with a fixed longitudinal margin -/

/-- A negative longitudinal displacement of at least `99 / 200` keeps its
sign after a small rotation.  The transverse component is allowed its full
unit-distance bound, so this lemma can be used without a separate cone
estimate for the target vector. -/
lemma fst_neg_under_small_rotation
    {c s x y : ℝ}
    (hc : (399 / 400 : ℝ) ≤ c)
    (hs : |s| ≤ (7 / 100 : ℝ))
    (hx : x ≤ -(99 / 200 : ℝ))
    (hy : |y| ≤ 1) :
    c * x + s * y < 0 := by
  have hx0 : x ≤ 0 := by linarith
  have hcx : c * x ≤ (399 / 400 : ℝ) * x := by
    exact mul_le_mul_of_nonpos_right hc hx0
  have hsyAbs : |s * y| ≤ (7 / 100 : ℝ) := by
    rw [abs_mul]
    calc
      |s| * |y| ≤ (7 / 100 : ℝ) * 1 := by gcongr
      _ = (7 / 100 : ℝ) := by ring
  have hsy : s * y ≤ (7 / 100 : ℝ) :=
    (le_abs_self (s * y)).trans hsyAbs
  nlinarith

/-- The positive counterpart of `fst_neg_under_small_rotation`. -/
lemma fst_pos_under_small_rotation
    {c s x y : ℝ}
    (hc : (399 / 400 : ℝ) ≤ c)
    (hs : |s| ≤ (7 / 100 : ℝ))
    (hx : (99 / 200 : ℝ) ≤ x)
    (hy : |y| ≤ 1) :
    0 < c * x + s * y := by
  have hx0 : 0 ≤ x := by linarith
  have hcx : (399 / 400 : ℝ) * x ≤ c * x := by
    exact mul_le_mul_of_nonneg_right hc hx0
  have hsyAbs : |s * y| ≤ (7 / 100 : ℝ) := by
    rw [abs_mul]
    calc
      |s| * |y| ≤ (7 / 100 : ℝ) * 1 := by gcongr
      _ = (7 / 100 : ℝ) := by ring
  have hsy : -(7 / 100 : ℝ) ≤ s * y :=
    (abs_le.mp hsyAbs).1
  nlinarith

end Erdos957EdgeConeTransport

#print axioms Erdos957EdgeConeTransport.shallow_cone_under_small_rotation
#print axioms Erdos957EdgeConeTransport.fst_gt_five_halves_under_small_rotation
#print axioms Erdos957EdgeConeTransport.fst_neg_under_small_rotation
#print axioms Erdos957EdgeConeTransport.fst_pos_under_small_rotation
