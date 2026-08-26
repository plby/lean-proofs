import ErdosProblems.Erdos547.BoundedFractional

/-!
# Moving fractional weight along a two-edge path

The middle vertex keeps its load, while one end gains precisely the load
lost at the other. All edge and vertex capacities are checked explicitly.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem edgeIncrement_supported {a b u v : V} (hab : G.Adj a b) (t : ℝ)
    (huv : ¬ G.Adj u v) : edgeIncrement a b t u v = 0 := by
  classical
  rw [edgeIncrement]
  apply if_neg
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact huv hab
  · exact huv hab.symm

namespace FractionalMatching

def transferWeight (μ : FractionalMatching G) (x y z : V) (t : ℝ) (u v : V) : ℝ :=
  μ.weight u v + edgeIncrement x y t u v - edgeIncrement z y t u v

open scoped Classical in
theorem sum_transferWeight (μ : FractionalMatching G) {x y z : V}
    (hxy : x ≠ y) (hzy : z ≠ y) (hxz : x ≠ z) (t : ℝ) (u : V) :
    (∑ v, μ.transferWeight x y z t u v) =
      μ.load u + (if u = x then t else 0) - (if u = z then t else 0) := by
  classical
  simp only [transferWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_edgeIncrement hxy, sum_edgeIncrement hzy]
  by_cases hux : u = x
  · subst u
    simp [hxy, hxz, load]
  · by_cases huz : u = z
    · subst u
      simp [hzy, hxz.symm, load]
    · by_cases huy : u = y
      · subst u
        simp [hxy.symm, hzy.symm, load]
      · simp [hux, huz, huy, load]

def transfer (μ : FractionalMatching G) {x y z : V} (hxy : G.Adj x y) (hzy : G.Adj z y)
    (hxz : x ≠ z) (t : ℝ) (ht : 0 ≤ t) (he : t ≤ μ.weight z y)
    (hx : μ.load x + t ≤ 1) : FractionalMatching G where
  weight := μ.transferWeight x y z t
  symmetric u v := by
    rw [transferWeight, transferWeight, μ.symmetric u v,
      edgeIncrement_symmetric x y t u v, edgeIncrement_symmetric z y t u v]
  nonnegative u v := by
    classical
    have hinc := edgeIncrement_nonneg x y ht u v
    have hsub : edgeIncrement z y t u v ≤ μ.weight u v := by
      rw [edgeIncrement]
      split_ifs with huv
      · rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · simpa only [hu, hv] using he
        · simpa only [hu, hv, μ.symmetric y z] using he
      · exact μ.nonnegative u v
    dsimp [transferWeight]
    linarith
  supported u v huv := by
    rw [transferWeight, μ.supported u v huv, edgeIncrement_supported hxy t huv,
      edgeIncrement_supported hzy t huv]
    ring
  capacity u := by
    classical
    rw [sum_transferWeight μ hxy.ne hzy.ne hxz]
    by_cases hux : u = x
    · subst u
      simpa [hxz] using hx
    · rw [if_neg hux, add_zero]
      split_ifs <;> linarith [μ.load_le_one u]

open scoped Classical in
theorem transfer_load (μ : FractionalMatching G) {x y z : V}
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1) (u : V) :
    (μ.transfer hxy hzy hxz t ht he hx).load u =
      μ.load u + (if u = x then t else 0) - (if u = z then t else 0) :=
  μ.sum_transferWeight hxy.ne hzy.ne hxz t u

theorem transfer_total (μ : FractionalMatching G) {x y z : V}
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1) :
    (μ.transfer hxy hzy hxz t ht he hx).total = μ.total := by
  classical
  have h := (μ.transfer hxy hzy hxz t ht he hx).sum_load
  simp only [transfer_load, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, μ.sum_load] at h
  linarith

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.transfer_load
