import StackExchange.Puzzling139335.AcuteCorner
import StackExchange.Puzzling139335.N5.TypeReduction

/-!
# Acute support points in the incidence table

An actual full square-corner neighborhood is incompatible with a
forty-five-degree supporting cone. Every two-corner placement must use
each such support point as one of its corner endpoints.
-/

open Set Metric

namespace Puzzling139335.N6

open AcuteCorner

/-- The two short perpendicular rays in a full square corner cannot fit
inside a forty-five-degree cone. -/
theorem not_supports45_of_fullCorner {P : Set Plane} {v : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P v) : ¬ Supports45 P v := by
  intro hacute
  obtain ⟨f, hfv, _, ε, hε, hnear⟩ := hfull.exists_normalized
  have hacute' : Supports45 (f '' P) 0 := by
    simpa only [hfv] using hacute.image f
  let t := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hx : dist (!₂[t, 0] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  have hy : dist (!₂[0, t] : Plane) 0 = t := by
    apply (sq_eq_sq₀ dist_nonneg ht.le).mp
    rw [plane_dist_sq]
    simp
  have hpx : (!₂[t, 0] : Plane) ∈ f '' P := by
    apply hnear
    refine ⟨mem_ball.mpr (by rw [hx]; exact htε), ?_⟩
    simpa [unitSquare] using And.intro ht.le ht1
  have hpy : (!₂[0, t] : Plane) ∈ f '' P := by
    apply hnear
    refine ⟨mem_ball.mpr (by rw [hy]; exact htε), ?_⟩
    simpa [unitSquare] using And.intro ht.le ht1
  have hbound := hacute'.pair_bound hpx hpy
  simp only [sub_zero, det, dot, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, zero_mul, sub_zero, add_zero] at hbound
  have hpos : 0 < t * t := mul_pos ht ht
  rw [abs_of_pos hpos] at hbound
  exact (not_le_of_gt hpos) hbound

/-- A used acute support point is never one of the full corner types. -/
theorem supports45_not_mem_fullCornerTypes (d : SquareDissection) {v : Plane}
    (hsupport : Supports45 (d.piece 0) v) : v ∉ N5.fullCornerTypes d := by
  intro hv
  exact not_supports45_of_fullCorner
    (N5.isFullSquareCorner_of_mem_fullCornerTypes d hv) hsupport

/-- Every two-corner tile uses an acute supporting prototype point at one
of its actual square-corner incidences. -/
theorem supports45_occurs_in_two_corner_tile (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) (hcount : d.tileCornerCount i = 2)
    {v : Plane} (hv : v ∈ d.piece 0) (hsupport : Supports45 (d.piece 0) v) :
    ∃ j : Fin 4, corner j ∈ d.piece i ∧ d.intrinsicCorner i j = v := by
  classical
  change (Finset.univ.filter fun j => corner j ∈ d.piece i).card = 2 at hcount
  obtain ⟨j, k, hjk, hset⟩ := Finset.card_eq_two.mp hcount
  have hj : corner j ∈ d.piece i := by
    have hmem : j ∈ Finset.univ.filter fun j => corner j ∈ d.piece i := by
      rw [hset]
      simp
    exact (Finset.mem_filter.mp hmem).2
  have hk : corner k ∈ d.piece i := by
    have hmem : k ∈ Finset.univ.filter fun j => corner j ∈ d.piece i := by
      rw [hset]
      simp
    exact (Finset.mem_filter.mp hmem).2
  rcases d.support45_preimage_eq_of_two_corners hc i j k hjk hj hk
      (d.placement i) (d.placement_image i) hv hsupport with h | h
  · exact ⟨j, hj, h.symm⟩
  · exact ⟨k, hk, h.symm⟩

/-- A tile omitting an acute support type has at most one square corner. -/
theorem tileCornerCount_le_one_of_omits_support45 (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) {v : Plane}
    (hv : v ∈ d.piece 0) (hsupport : Supports45 (d.piece 0) v)
    (homit : ∀ j, corner j ∈ d.piece i → d.intrinsicCorner i j ≠ v) :
    d.tileCornerCount i ≤ 1 := by
  have hle := d.tileCornerCount_le_two hc i
  by_contra hnot
  have hcount : d.tileCornerCount i = 2 := by omega
  obtain ⟨j, hj, htype⟩ := supports45_occurs_in_two_corner_tile d hc i hcount hv hsupport
  exact homit j hj htype

end Puzzling139335.N6
