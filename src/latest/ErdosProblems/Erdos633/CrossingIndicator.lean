import ErdosProblems.Erdos633.TriangleCrossing

/-!
# Crossing number as the actual triangle indicator

The three determinant signs are identified with positive barycentric
coordinates. Away from the three supporting lines and vertex heights,
the integer crossing number is exactly the orientation sign on the
triangle interior and zero elsewhere.
-/

namespace Erdos633

open scoped BigOperators

theorem planeDet_sub_sub (a b z : ℂ) :
    planeDet (a - z) (b - z) = orientedDoubleArea a b z := by
  simp only [planeDet, orientedDoubleArea, Complex.sub_re, Complex.sub_im]
  ring

noncomputable def Triangle.edgeDet (P : Triangle) (z : ℂ) (k : Fin 3) : ℝ :=
  planeDet (P.edgeStart k - z) (P.edgeEnd k - z)

theorem Triangle.edgeDet_eq (P : Triangle) (z : ℂ) (k : Fin 3) :
    P.edgeDet z k = orientedDoubleArea P.a P.b P.c * P.barycentric z k := by
  rw [Triangle.edgeDet, planeDet_sub_sub, P.orientedDoubleArea_edge]

theorem Triangle.sum_edgeDet (P : Triangle) (z : ℂ) :
    P.edgeDet z 0 + P.edgeDet z 1 + P.edgeDet z 2 =
      orientedDoubleArea P.a P.b P.c := by
  simp [Triangle.edgeDet, Triangle.edgeStart, Triangle.edgeEnd, planeDet,
    orientedDoubleArea]
  ring

theorem Triangle.all_edgeDet_pos_iff (P : Triangle) (z : ℂ) :
    (∀ k : Fin 3, 0 < P.edgeDet z k) ↔
      0 < orientedDoubleArea P.a P.b P.c ∧ z ∈ interior P.carrier := by
  constructor
  · intro h
    have hs := P.sum_edgeDet z
    have hd : 0 < orientedDoubleArea P.a P.b P.c := by
      linarith [h 0, h 1, h 2]
    refine ⟨hd, (P.mem_interior_iff_barycentric z).mpr ?_⟩
    intro k
    have hk := h k
    rw [P.edgeDet_eq] at hk
    exact pos_of_mul_pos_right hk hd.le
  · rintro ⟨hd, hz⟩ k
    rw [P.edgeDet_eq]
    exact mul_pos hd ((P.mem_interior_iff_barycentric z).mp hz k)

theorem Triangle.all_edgeDet_neg_iff (P : Triangle) (z : ℂ) :
    (∀ k : Fin 3, P.edgeDet z k < 0) ↔
      orientedDoubleArea P.a P.b P.c < 0 ∧ z ∈ interior P.carrier := by
  constructor
  · intro h
    have hs := P.sum_edgeDet z
    have hd : orientedDoubleArea P.a P.b P.c < 0 := by
      linarith [h 0, h 1, h 2]
    refine ⟨hd, (P.mem_interior_iff_barycentric z).mpr ?_⟩
    intro k
    have hk := h k
    rw [P.edgeDet_eq] at hk
    have hp : 0 < (-orientedDoubleArea P.a P.b P.c) * P.barycentric z k := by
      simpa only [neg_mul] using neg_pos.mpr hk
    exact pos_of_mul_pos_right hp (neg_nonneg.mpr hd.le)
  · rintro ⟨hd, hz⟩ k
    rw [P.edgeDet_eq]
    exact mul_neg_of_neg_of_pos hd ((P.mem_interior_iff_barycentric z).mp hz k)

theorem Triangle.detSign_eq_indicator (P : Triangle) (z : ℂ) :
    (triangleDetSign (P.a - z) (P.b - z) (P.c - z) : ℝ) =
      (interior P.carrier).indicator (fun _ => P.orientationSign) z := by
  classical
  change (triangleDetSign (P.a - z) (P.b - z) (P.c - z) : ℝ) =
    if z ∈ interior P.carrier then P.orientationSign else 0
  have hp : (0 < planeDet (P.a - z) (P.b - z) ∧
      0 < planeDet (P.b - z) (P.c - z) ∧ 0 < planeDet (P.c - z) (P.a - z)) ↔
      ∀ k : Fin 3, 0 < P.edgeDet z k := by
    constructor
    · rintro ⟨h2, h0, h1⟩ k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
    · intro h
      exact ⟨h 2, h 0, h 1⟩
  have hn : (planeDet (P.a - z) (P.b - z) < 0 ∧
      planeDet (P.b - z) (P.c - z) < 0 ∧ planeDet (P.c - z) (P.a - z) < 0) ↔
      ∀ k : Fin 3, P.edgeDet z k < 0 := by
    constructor
    · rintro ⟨h2, h0, h1⟩ k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
    · intro h
      exact ⟨h 2, h 0, h 1⟩
  by_cases hi : z ∈ interior P.carrier
  · by_cases hd : 0 < orientedDoubleArea P.a P.b P.c
    · have hpos := hp.mpr ((P.all_edgeDet_pos_iff z).mpr ⟨hd, hi⟩)
      simp [triangleDetSign, hpos, hi, hd, Triangle.orientationSign]
    · have hd' : orientedDoubleArea P.a P.b P.c < 0 :=
        lt_of_le_of_ne (le_of_not_gt hd) P.nondegenerate
      have hneg := hn.mpr ((P.all_edgeDet_neg_iff z).mpr ⟨hd', hi⟩)
      have hpos : ¬(0 < planeDet (P.a - z) (P.b - z) ∧
          0 < planeDet (P.b - z) (P.c - z) ∧ 0 < planeDet (P.c - z) (P.a - z)) :=
        fun h => hd ((P.all_edgeDet_pos_iff z).mp (hp.mp h)).1
      simp [triangleDetSign, hpos, hneg, hi, hd, Triangle.orientationSign]
  · have hpos : ¬(0 < planeDet (P.a - z) (P.b - z) ∧
        0 < planeDet (P.b - z) (P.c - z) ∧ 0 < planeDet (P.c - z) (P.a - z)) :=
      fun h => hi ((P.all_edgeDet_pos_iff z).mp (hp.mp h)).2
    have hneg : ¬(planeDet (P.a - z) (P.b - z) < 0 ∧
        planeDet (P.b - z) (P.c - z) < 0 ∧ planeDet (P.c - z) (P.a - z) < 0) :=
      fun h => hi ((P.all_edgeDet_neg_iff z).mp (hn.mp h)).2
    simp [triangleDetSign, hpos, hneg, hi]

noncomputable def Triangle.crossingAt (P : Triangle) (z : ℂ) : ℤ :=
  rayTriangleCrossing (P.a - z) (P.b - z) (P.c - z)

def Triangle.CrossingRegular (P : Triangle) (z : ℂ) : Prop :=
  (∀ k : Fin 3, (P.vertex k).im ≠ z.im) ∧ (∀ k : Fin 3, P.barycentric z k ≠ 0)

theorem Triangle.crossingAt_eq_sum_edges (P : Triangle) (z : ℂ) :
    P.crossingAt z = ∑ k : Fin 3, edgeCrossingAt z (P.edgeStart k) (P.edgeEnd k) := by
  simp [Triangle.crossingAt, rayTriangleCrossing, edgeCrossingAt,
    Fin.sum_univ_succ, Triangle.edgeStart, Triangle.edgeEnd]
  ring

theorem Triangle.crossingAt_eq_indicator (P : Triangle) (z : ℂ)
    (hz : P.CrossingRegular z) :
    (P.crossingAt z : ℝ) =
      (interior P.carrier).indicator (fun _ => P.orientationSign) z := by
  have hd (k : Fin 3) : P.edgeDet z k ≠ 0 := by
    rw [P.edgeDet_eq]
    exact mul_ne_zero P.nondegenerate (hz.2 k)
  have ha : (P.a - z).im ≠ 0 := sub_ne_zero.mpr (hz.1 0)
  have hb : (P.b - z).im ≠ 0 := sub_ne_zero.mpr (hz.1 1)
  have hc : (P.c - z).im ≠ 0 := sub_ne_zero.mpr (hz.1 2)
  unfold Triangle.crossingAt
  rw [rayTriangleCrossing_eq_detSign _ _ _ ha hb hc (hd 2) (hd 0) (hd 1)]
  exact P.detSign_eq_indicator z

end Erdos633
