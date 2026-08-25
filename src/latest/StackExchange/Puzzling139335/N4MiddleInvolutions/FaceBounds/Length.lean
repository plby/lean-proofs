import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

/-! From coordinate spans to Euclidean lengths and finite cardinality. -/

open Set
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

theorem dist_le_abs_coordinate_sum (a b : Plane) :
    dist a b ≤ |a 0 - b 0| + |a 1 - b 1| := by
  have hdist := plane_dist_sq a b
  have hx := abs_nonneg (a 0 - b 0)
  have hy := abs_nonneg (a 1 - b 1)
  have hxy := mul_nonneg hx hy
  have hsx := sq_abs (a 0 - b 0)
  have hsy := sq_abs (a 1 - b 1)
  have hd := dist_nonneg (x := a) (y := b)
  nlinarith

theorem sum_dist_le_coordinate_sums {ι : Type*} [Fintype ι]
    (a b : ι → Plane) :
    ∑ i, dist (a i) (b i) ≤
      (∑ i, |a i 0 - b i 0|) + ∑ i, |a i 1 - b i 1| := by
  calc
    ∑ i, dist (a i) (b i) ≤
        ∑ i, (|a i 0 - b i 0| + |a i 1 - b i 1|) :=
      Finset.sum_le_sum fun i _ => dist_le_abs_coordinate_sum (a i) (b i)
    _ = _ := Finset.sum_add_distrib

theorem card_le_three_of_sum_dist_lt_four {ι : Type*} [Fintype ι]
    (a b : ι → Plane) (hlen : ∀ i, 1 ≤ dist (a i) (b i))
    (hsum : ∑ i, dist (a i) (b i) < 4) : Fintype.card ι ≤ 3 := by
  have hcard : (Fintype.card ι : ℝ) ≤ ∑ i, dist (a i) (b i) := by
    calc
      (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hlen i
  have hlt : Fintype.card ι < 4 := by exact_mod_cast hcard.trans_lt hsum
  omega

end Puzzling139335.N4MiddleInvolutions.FaceBounds
