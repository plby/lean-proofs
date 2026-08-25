import StackExchange.Puzzling139335.CornerSupport
import StackExchange.Puzzling139335.CornerSupport.Equality.Axes
import StackExchange.Puzzling139335.CornerSupport.Equality.Edges
import StackExchange.Puzzling139335.CornerSupport.Equality.Coordinates
import StackExchange.Puzzling139335.CornerSupport.Equality.Parallelogram

/-!
# Rigidity of four cyclically ordered supporting corners

Once the four outward bisectors form an orthogonal cross, equality in their
support projections forces the four corner positions to form a rectangle.
The support inequalities at the two opposite corners contain the whole set
in that rectangle.
-/

open Set

namespace Puzzling139335.CornerSupport.Equality

/-- Four supporting corners whose bisectors occur in cyclic cross order
are the vertices of a nondegenerate rectangle, and their hull contains the set. -/
theorem ordered_support_corners_form_rectangle {P : Set Plane} {a b c d : Plane}
    (ha : SupportCorner P a) (hb : SupportCorner P b)
    (hc : SupportCorner P c) (hd : SupportCorner P d)
    (hab : a ≠ b) (had : a ≠ d)
    (hcOpp : hc.bisector = -ha.bisector) (hdOpp : hd.bisector = -hb.bisector)
    (hOrth : inner ℝ ha.bisector hb.bisector = 0) :
    (b - a ≠ 0) ∧ (d - a ≠ 0) ∧ inner ℝ (b - a) (d - a) = 0 ∧
      c = a + (b - a) + (d - a) ∧
      convexHull ℝ P = convexHull ℝ ({a, b, c, d} : Set Plane) := by
  let B := bisectorBasis ha.bisector hb.bisector
    ha.bisector_norm_sq hb.bisector_norm_sq hOrth
  let W : ℝ := ‖b - a‖
  let H : ℝ := ‖d - a‖
  let L : ℝ := ‖c - b‖
  let K : ℝ := ‖c - d‖
  have hB0 : B 0 = (1 / 2 : ℝ) • (hb.bisector - ha.bisector) :=
    bisectorBasis_zero _ _ _ _ _
  have hB1 : B 1 = -(1 / 2 : ℝ) • (hb.bisector + ha.bisector) :=
    bisectorBasis_one _ _ _ _ _
  have hBsum : B 0 + B 1 = -ha.bisector := bisectorBasis_sum _ _ _ _ _
  have hABne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hADne : d - a ≠ 0 := sub_ne_zero.mpr had.symm
  have hW : 0 < W := norm_pos_iff.mpr hABne
  have hH : 0 < H := norm_pos_iff.mpr hADne
  have hOrthBA : inner ℝ hb.bisector ha.bisector = 0 := by
    rw [real_inner_comm]
    exact hOrth
  have hOrthAD : inner ℝ ha.bisector hd.bisector = 0 := by
    rw [hdOpp, inner_neg_right, hOrth, neg_zero]
  have hOrthBC : inner ℝ hb.bisector hc.bisector = 0 := by
    rw [hcOpp, inner_neg_right, hOrthBA, neg_zero]
  have hOrthDC : inner ℝ hd.bisector hc.bisector = 0 := by
    rw [hdOpp, hcOpp, inner_neg_left, inner_neg_right, hOrthBA]
    simp
  have hAB : b - a = W • B 0 := by
    rw [edge_eq_smul_bisector_difference ha hb hOrth, hB0]
    dsimp [W]
    rw [smul_smul]
    congr 1
    ring
  have hAD : d - a = H • B 1 := by
    rw [edge_eq_smul_bisector_difference ha hd hOrthAD, hdOpp, hB1]
    dsimp [H]
    ext i
    simp
    ring
  have hBC : c - b = L • B 1 := by
    rw [edge_eq_smul_bisector_difference hb hc hOrthBC, hcOpp, hB1]
    dsimp [L]
    ext i
    simp
    ring
  have hDC : c - d = K • B 0 := by
    rw [edge_eq_smul_bisector_difference hd hc hOrthDC, hdOpp, hcOpp, hB0]
    dsimp [K]
    ext i
    simp
    ring
  have hCA₁ : c - a = W • B 0 + L • B 1 := by
    calc
      c - a = (b - a) + (c - b) := by abel
      _ = W • B 0 + L • B 1 := by rw [hAB, hBC]
  have hCA₂ : c - a = H • B 1 + K • B 0 := by
    calc
      c - a = (d - a) + (c - d) := by abel
      _ = H • B 1 + K • B 0 := by rw [hAD, hDC]
  have hLH : L = H := by
    have hCoord := congrArg (fun z : Plane => inner ℝ (B 1) z) (hCA₁.symm.trans hCA₂)
    simpa [inner_add_right, inner_smul_right, B.inner_eq_ite] using hCoord
  have hbEq : b = a + W • B 0 := by
    calc
      b = a + (b - a) := by abel
      _ = a + W • B 0 := by rw [hAB]
  have hdEq : d = a + H • B 1 := by
    calc
      d = a + (d - a) := by abel
      _ = a + H • B 1 := by rw [hAD]
  have hcEq : c = a + W • B 0 + H • B 1 := by
    calc
      c = a + (c - a) := by abel
      _ = a + W • B 0 + H • B 1 := by rw [hCA₁, hLH]; abel
  have haSum : ha.bisector = -(B 0 + B 1) := by rw [hBsum]; simp
  have hcSum : hc.bisector = B 0 + B 1 := by rw [hcOpp, hBsum]
  have hBox : ∀ x ∈ P, inner ℝ (B 0) (x - a) ∈ Icc (0 : ℝ) W ∧
      inner ℝ (B 1) (x - a) ∈ Icc (0 : ℝ) H := by
    intro x hx
    have hlo := coords_nonneg_of_bisector_eq_neg_sum ha B haSum hx
    have hhi := coords_nonpos_of_bisector_eq_sum hc B hcSum hx
    have hxc : x - c = (x - a) - (c - a) := by abel
    have hhi' : inner ℝ (B 0) (x - a) - W ≤ 0 ∧
        inner ℝ (B 1) (x - a) - H ≤ 0 := by
      simpa [hxc, hCA₁, hLH, inner_sub_right, inner_add_right,
        inner_smul_right, B.inner_eq_ite] using hhi
    exact ⟨⟨hlo.1, by linarith [hhi'.1]⟩, ⟨hlo.2, by linarith [hhi'.2]⟩⟩
  have hHull := convexHull_eq_rectangle_of_orthonormal_bounds P a B W H hW hH
    ha.mem (hbEq ▸ hb.mem) (hcEq ▸ hc.mem) (hdEq ▸ hd.mem) hBox
  rw [← hcEq, ← hbEq, ← hdEq] at hHull
  refine ⟨hABne, hADne, ?_, ?_, hHull⟩
  · rw [hAB, hAD]
    simp [inner_smul_left, inner_smul_right, B.inner_eq_ite]
  · rw [hAB, hAD]
    exact hcEq

end Puzzling139335.CornerSupport.Equality
