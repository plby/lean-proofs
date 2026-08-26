import Mathlib.Tactic

/-! # Palette bounds for the small-class refinement -/

namespace Erdos19

theorem small_class_extra_colors_bound (n s w : ℕ) (hn : 0 < n) (hs : 0 < s) :
    ((w / (n / s + 1)) * (n / (n / s / 2 + 1))) * n ≤ 2 * s * s * w := by
  let A := n / s
  let x := w / (A + 1)
  let y := n / (A / 2 + 1)
  have hx : x * (A + 1) ≤ w := Nat.div_mul_le_self _ _
  have hy : y * (A / 2 + 1) ≤ n := Nat.div_mul_le_self _ _
  have hbudget : (x * y) * ((A + 1) * (A / 2 + 1)) ≤ w * n := by
    nlinarith only [Nat.mul_le_mul hx hy]
  have hA : n ≤ s * (A + 1) := (Nat.lt_mul_div_succ n hs).le
  have hhalf : A + 1 ≤ 2 * (A / 2 + 1) := by omega
  have hB : n ≤ (2 * s) * (A / 2 + 1) := by
    nlinarith only [hA, Nat.mul_le_mul_left s hhalf]
  have hdenom : n * n ≤ (2 * s * s) * ((A + 1) * (A / 2 + 1)) := by
    nlinarith only [Nat.mul_le_mul hA hB]
  have hprod : ((x * y) * n) * n ≤ (2 * s * s * w) * n := by
    nlinarith only [Nat.mul_le_mul_left (x * y) hdenom,
      Nat.mul_le_mul_left (2 * s * s) hbudget]
  exact Nat.le_of_mul_le_mul_right hprod hn

theorem small_class_palette_margins (n s w t q m : ℕ) (hn : 0 < n) (hs : 100 ≤ s)
    (ht : n ≤ 8 * t) (htn : t ≤ n) (hq : 100 * q ≤ 51 * t)
    (hw : 1600 * s * s * w ≤ n * n)
    (hm : m ≤ q + (w / (n / s + 1)) * (n / (n / s / 2 + 1))) :
    100 * m ≤ 52 * t ∧ m + n / s ≤ t ∧ 4 * m ≤ 3 * n := by
  have hspos : 0 < s := by omega
  let E := (w / (n / s + 1)) * (n / (n / s / 2 + 1))
  have hE := small_class_extra_colors_bound n s w hn hspos
  change E * n ≤ 2 * s * s * w at hE
  have hEmul : (800 * E) * n ≤ n * n := by nlinarith only [hE, hw]
  have hEsmall : 800 * E ≤ n := Nat.le_of_mul_le_mul_right hEmul hn
  have hA : 100 * (n / s) ≤ n := by
    exact (Nat.mul_le_mul_right (n / s) hs).trans (by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self n s)
  dsimp only [E] at hEsmall
  omega

theorem edge_size_le_small_class_scale (n s r : ℕ) (hs : 0 < s) (hr : 2 ≤ r)
    (hweight : 2 * s * s * (r * (r - 1)) < n * n) : r ≤ n / s := by
  apply (Nat.le_div_iff_mul_le hs).mpr
  have hrsub : r - 1 + 1 = r := by omega
  have hrweight : r * r ≤ 2 * (r * (r - 1)) := by nlinarith only [hr, hrsub]
  have hsq : (r * s) * (r * s) < n * n := by
    nlinarith only [Nat.mul_le_mul_left (s * s) hrweight, hweight]
  nlinarith only [hsq]

#print axioms small_class_palette_margins
#print axioms edge_size_le_small_class_scale

end Erdos19
