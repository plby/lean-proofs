import ErdosProblems.Erdos633b.DoubledMetric
import ErdosProblems.Erdos633b.DoubledSmallMetric
import ErdosProblems.Erdos633b.DoubledSubdivision
import ErdosProblems.Erdos633b.DoubledDimensions
import ErdosProblems.Erdos633b.GroupTwoNormalization

/-! Each of the four triangles carries an actual patch of the same reference tile. -/

namespace Erdos633b.DoubledCoordinates

open Sixty DoubledDimensions

noncomputable def abd_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![point d 0 0, bigB d c m, pointD d a b m]) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      S.support ((m * c) ^ 2) := by
  apply quadratic_patch_permuted _ S (Equiv.swap 0 2) (m * c) (mul_pos hm hc)
  intro i
  rw [abd_sides d he a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hm) (by exact_mod_cast hrel) S hp]
  rw [reference_sides d hd he a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hrel)]
  push_cast
  congr 1
  fin_cases i <;> rfl

noncomputable def bdg_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![bigB d c m, pointD d a b m, pointG d a b m]) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      S.support ((m * c) ^ 2) := by
  apply quadratic_patch_permuted _ S (Equiv.swap 0 1) (m * c) (mul_pos hm hc)
  intro i
  rw [bdg_sides d he a b c m (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hm) (by exact_mod_cast hrel) S hp]
  rw [reference_sides d hd he a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hrel)]
  push_cast
  congr 1
  fin_cases i <;> rfl

noncomputable def aef_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![point d 0 0, pointE d a b (outerScale a b c),
      pointF d a b c (outerScale a b c)]) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast hb))
      S.support (smallScale a b c ^ 2) := by
  apply quadratic_patch_permuted _ S ((Equiv.swap 0 1).trans (Equiv.swap 0 2))
    (smallScale a b c) (smallScale_pos a b c ha hb hc)
  intro i
  rw [aef_sides d he a b c (outerScale a b c) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast outerScale_pos a b c hb hc)
    (by exact_mod_cast hrel) S hp, smallScale_eq a b c hb]
  rw [reference_sides d hd he a b c (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hrel)]
  congr 1
  fin_cases i <;> rfl

noncomputable def cfg_patch (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![bigC d a b c (outerScale a b c), pointF d a b c (outerScale a b c),
      pointG d a b (outerScale a b c)]) :
    Patch (groupTwoReference d hd a b (by exact_mod_cast ha) (by exact_mod_cast ha.trans hab))
      S.support (cornerScale a b c ^ 2 * (commonScale a b ^ 2 * b * (a + b))) := by
  apply (case_four_integer_patch d hd he a b c ha (ha.trans hab) hc hrel).quadraticEnlargePermuted
    S (Equiv.swap 1 2) (cornerScale a b c) (cornerScale_pos a b c ha hab hc)
  intro i
  rw [cfg_sides d he a b c (outerScale a b c) (by exact_mod_cast ha) (by exact_mod_cast hab)
    (by exact_mod_cast hc) (by exact_mod_cast outerScale_pos a b c (ha.trans hab) hc)
    (by exact_mod_cast hrel) S hp, cornerScale_eq a b c (ha.trans hab) hab.le,
    caseFourOuter_sides d hd he a b c ha (ha.trans hab) hc hrel]
  rw [mul_assoc]
  congr 2
  fin_cases i <;> rfl

end Erdos633b.DoubledCoordinates
