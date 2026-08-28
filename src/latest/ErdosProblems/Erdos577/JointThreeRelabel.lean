import ErdosProblems.Erdos577.JointThreeExtreme

/-! Preserve every local prohibition under the explicit reflection of the high vertices. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PairRows.with_labels {v : Quadrilateral G} {x y z w : V} (h : PairRows v x y z w)
    (v' : Quadrilateral G) (hv : v'.support = v.support)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v' i)) : PairRows v' x y z w where
  x_out := by simpa only [hv] using h.x_out
  y_out := by simpa only [hv] using h.y_out
  z_out := by simpa only [hv] using h.z_out
  w_out := by simpa only [hv] using h.w_out
  x_pos := by simpa only [hv] using h.x_pos
  x_bound := by simpa only [hv] using h.x_bound
  y_bound := by simpa only [hv] using h.y_bound
  nine := by simpa only [hv] using h.nine
  three := hthree
  no_xz_w := by simpa only [hv] using h.no_xz_w
  no_xw_z := by simpa only [hv] using h.no_xw_z
  no_zw_x := by simpa only [hv] using h.no_zw_x
  no_xz_y := by simpa only [hv] using h.no_xz_y
  no_xw_y := by simpa only [hv] using h.no_xw_y
  no_zw_y := by simpa only [hv] using h.no_zw_y

lemma FinalRows.with_labels {v : Quadrilateral G} {x y z w : V} (h : FinalRows v x y z w)
    (v' : Quadrilateral G) (hv : v'.support = v.support)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v' i))
    (hx : ¬(G.Adj x (v' 0) ∧ G.Adj x (v' 2)))
    (hy : ¬(G.Adj y (v' 0) ∧ G.Adj y (v' 2))) : FinalRows v' x y z w where
  toPairRows := h.toPairRows.with_labels v' hv hthree
  distinct := h.distinct
  pair_edge := h.pair_edge
  no_high_x := hx
  no_high_y := hy
  gain := by
    intro u hu t b ht hb htb hcover
    rw [hv] at hcover ⊢
    exact h.gain u hu t b ht hb htb hcover
  factor := by simpa only [hv] using h.factor
  low := by
    intro u hu q hq hdiag hrow s t hst hs ht
    exact h.low u hu q (hq.trans hv) hdiag hrow s t hst hs ht

lemma FinalRows.reflect_highs {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) : FinalRows (v.rotate 2).reverse x y z w := by
  have hv : (v.rotate 2).reverse.support = v.support := by
    rw [Quadrilateral.reverse_support, Quadrilateral.rotate_support]
  refine h.with_labels _ hv ?_ ?_ ?_
  · intro i hi
    fin_cases i
    · exact h.three 2 (by decide)
    · exact h.three 1 (by decide)
    · exact h.three 0 (by decide)
    · exact False.elim (hi rfl)
  · rintro ⟨hx0, hx2⟩
    exact h.no_high_x ⟨hx2, hx0⟩
  · rintro ⟨hy0, hy2⟩
    exact h.no_high_y ⟨hy2, hy0⟩

theorem FinalRows.three_last_false {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (u : V) (hu : u = x ∨ u = y) (hu2 : G.Adj u (v 2)) (hu3 : G.Adj u (v 3)) : False :=
  h.reflect_highs.three_extreme_false
    (by simpa only [Quadrilateral.reverse_support, Quadrilateral.rotate_support] using hz)
    u hu hu2 hu3

end Erdos577.JointFinal
