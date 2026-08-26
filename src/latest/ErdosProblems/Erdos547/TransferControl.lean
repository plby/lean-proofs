import ErdosProblems.Erdos547.FractionalTransfer

/-!
# Support, distance, and saturation under fractional transfers
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

theorem transfer_positive (μ : FractionalMatching G) {x y z : V}
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1)
    (hstrict : t < μ.weight z y) {u v : V} (huv : 0 < μ.weight u v) :
    0 < (μ.transfer hxy hzy hxz t ht he hx).weight u v := by
  classical
  have hinc := edgeIncrement_nonneg x y ht u v
  change 0 < μ.weight u v + edgeIncrement x y t u v - edgeIncrement z y t u v
  by_cases hp : (u = z ∧ v = y) ∨ (u = y ∧ v = z)
  · have hz : edgeIncrement z y t u v = t := if_pos hp
    have hsmall : t < μ.weight u v := by
      rcases hp with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · simpa only [hu, hv] using hstrict
      · simpa only [hu, hv, μ.symmetric y z] using hstrict
    rw [hz]
    linarith
  · have hz : edgeIncrement z y t u v = 0 := if_neg hp
    rw [hz, sub_zero]
    linarith

theorem transfer_load_dist_le (μ : FractionalMatching G) {x y z : V}
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1) (u : V) :
    |(μ.transfer hxy hzy hxz t ht he hx).load u - μ.load u| ≤ t := by
  classical
  rw [transfer_load]
  by_cases hux : u = x
  · subst u
    simp [hxz, abs_of_nonneg ht]
  · by_cases huz : u = z
    · subst u
      simp [hxz.symm, sub_sub_cancel_left, abs_of_nonneg ht]
    · simp [hux, huz, ht]

theorem transfer_saturation (μ : FractionalMatching G) (w : EdgeWeights G) (c : V)
    {x y z : V} (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1)
    (hcx : μ.load x + t ≤ w.weight c x) (hcz : μ.load z ≤ w.weight c z) :
    w.saturation (μ.transfer hxy hzy hxz t ht he hx).load c = w.saturation μ.load c := by
  classical
  have hp (u : V) :
      min (w.weight c u) ((μ.transfer hxy hzy hxz t ht he hx).load u) =
        min (w.weight c u) (μ.load u) + (if u = x then t else 0) - (if u = z then t else 0) := by
    rw [transfer_load]
    by_cases hux : u = x
    · subst u
      simp only [ite_true, if_neg hxz, sub_zero]
      rw [min_eq_right hcx, min_eq_right (by linarith)]
    · by_cases huz : u = z
      · subst u
        simp only [if_neg hxz.symm, ite_true, add_zero]
        rw [min_eq_right hcz, min_eq_right (by linarith)]
      · simp only [if_neg hux, if_neg huz, add_zero, sub_zero]
  simp only [EdgeWeights.saturation, hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.transfer_saturation
