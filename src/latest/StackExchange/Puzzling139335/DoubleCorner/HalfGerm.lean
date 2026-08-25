import StackExchange.Puzzling139335.DoubleCorner.HalfGerm.Closure
import StackExchange.Puzzling139335.DoubleCorner.RotationCone
import StackExchange.Puzzling139335.BoundaryGerm

/-!
# The actual half-quadrant germs at a double corner

Opposite diagonal supports and local coverage by two closed pieces force
the pieces themselves to agree locally with the two 45-degree cones.
Closedness supplies the axis and diagonal boundary rays from the strict
sectors; no polygonal boundary hypothesis is used.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner

open AcuteCorner PlaneIsometries

/-- A small point of the first quadrant belongs to the unit square. -/
theorem mem_unitSquare_of_mem_ball_of_nonneg {p : Plane} {r : ℝ}
    (hr : r ≤ 1) (hp : p ∈ ball (0 : Plane) r)
    (hp0 : 0 ≤ p 0) (hp1 : 0 ≤ p 1) : p ∈ unitSquare := by
  have hnorm : ‖p‖ < r := by simpa only [mem_ball, dist_zero_right] using hp
  have hupper (i : Fin 2) : p i ≤ 1 := by
    have hi : |p i| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i
    exact (le_abs_self _).trans (hi.trans (hnorm.le.trans hr))
  exact ⟨⟨hp0, hupper 0⟩, ⟨hp1, hupper 1⟩⟩

private theorem inter_eq_of_closed_of_dense_subset {P C D U : Set Plane}
    (hclosed : IsClosed P) (hsub : P ⊆ C) (hclosure : closure D = C)
    (hU : IsOpen U) (hlocal : U ∩ D ⊆ P) : U ∩ P = U ∩ C := by
  apply subset_antisymm (fun p hp => ⟨hp.1, hsub hp.2⟩)
  rintro p ⟨hpU, hpC⟩
  refine ⟨hpU, ?_⟩
  apply closure_minimal hlocal hclosed
  apply hU.inter_closure
  exact ⟨hpU, hclosure.symm ▸ hpC⟩

/-- If two closed pieces with opposite diagonal supports cover the local
square, then they fill their respective half-quadrants on the same ball. -/
theorem halfCone_equalities_of_local_cover {P Q : Set Plane} {r : ℝ}
    (hr : r ≤ 1) (hPclosed : IsClosed P) (hQclosed : IsClosed Q)
    (hP : P ⊆ cone45) (hQ : Q ⊆ upperCone45)
    (hcover : ball (0 : Plane) r ∩ unitSquare ⊆ P ∪ Q) :
    ball (0 : Plane) r ∩ P = ball (0 : Plane) r ∩ cone45 ∧
      ball (0 : Plane) r ∩ Q = ball (0 : Plane) r ∩ upperCone45 := by
  constructor
  · apply inter_eq_of_closed_of_dense_subset hPclosed hP closure_strictCone45 isOpen_ball
    rintro p ⟨hpball, hpstrict⟩
    have hpS : p ∈ unitSquare := mem_unitSquare_of_mem_ball_of_nonneg hr hpball
      (hpstrict.1.le.trans hpstrict.2.le) hpstrict.1.le
    rcases hcover ⟨hpball, hpS⟩ with hpP | hpQ
    · exact hpP
    · exact False.elim ((not_lt_of_ge (hQ hpQ).2) hpstrict.2)
  · apply inter_eq_of_closed_of_dense_subset hQclosed hQ closure_strictUpperCone45 isOpen_ball
    rintro p ⟨hpball, hpstrict⟩
    have hpS : p ∈ unitSquare := mem_unitSquare_of_mem_ball_of_nonneg hr hpball
      hpstrict.1.le (hpstrict.1.le.trans hpstrict.2.le)
    rcases hcover ⟨hpball, hpS⟩ with hpP | hpQ
    · exact False.elim ((not_lt_of_ge (hP hpP).2) hpstrict.2)
    · exact hpQ

/-- The radius can be reduced to stay inside the coordinate side bounds. -/
theorem exists_halfCone_equalities_of_local_cover {P Q : Set Plane} {ε : ℝ}
    (hε : 0 < ε) (hPclosed : IsClosed P) (hQclosed : IsClosed Q)
    (hP : P ⊆ cone45) (hQ : Q ⊆ upperCone45)
    (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ Q) :
    ∃ r > 0,
      ball (0 : Plane) r ∩ P = ball (0 : Plane) r ∩ cone45 ∧
        ball (0 : Plane) r ∩ Q = ball (0 : Plane) r ∩ upperCone45 := by
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  apply halfCone_equalities_of_local_cover (min_le_right ε 1) hPclosed hQclosed hP hQ
  rintro p ⟨hpball, hpS⟩
  exact hcover ⟨ball_subset_ball (min_le_left ε 1) hpball, hpS⟩

theorem halfCone_germs_of_local_cover {P Q : Set Plane} {ε : ℝ}
    (hε : 0 < ε) (hPclosed : IsClosed P) (hQclosed : IsClosed Q)
    (hP : P ⊆ cone45) (hQ : Q ⊆ upperCone45)
    (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ Q) :
    SameBoundaryGerm P cone45 0 ∧ SameBoundaryGerm Q upperCone45 0 := by
  obtain ⟨r, hr, hPeq, hQeq⟩ := exists_halfCone_equalities_of_local_cover
    hε hPclosed hQclosed hP hQ hcover
  exact ⟨⟨r, hr, hPeq⟩, ⟨r, hr, hQeq⟩⟩

/-- Equality of actual region germs gives equality of frontier germs. -/
theorem frontier_germ_of_germ {P Q : Set Plane} {v : Plane}
    (h : SameBoundaryGerm P Q v) : SameBoundaryGerm (frontier P) (frontier Q) v := by
  obtain ⟨r, hr, heq⟩ := h
  refine ⟨r, hr, ?_⟩
  have heq' : P ∩ ball v r = Q ∩ ball v r := by
    simpa only [inter_comm] using heq
  have hf := congrArg (fun A : Set Plane => frontier A ∩ ball v r) heq'
  rw [frontier_inter_open_inter isOpen_ball, frontier_inter_open_inter isOpen_ball] at hf
  simpa only [inter_comm] using hf

/-- The actual frontiers agree with the half-quadrant frontiers near the
double corner, including their straight initial boundary rays. -/
theorem halfCone_frontier_germs_of_local_cover {P Q : Set Plane} {ε : ℝ}
    (hε : 0 < ε) (hPclosed : IsClosed P) (hQclosed : IsClosed Q)
    (hP : P ⊆ cone45) (hQ : Q ⊆ upperCone45)
    (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ Q) :
    SameBoundaryGerm (frontier P) (frontier cone45) 0 ∧
      SameBoundaryGerm (frontier Q) (frontier upperCone45) 0 := by
  obtain ⟨hPgerm, hQgerm⟩ := halfCone_germs_of_local_cover hε hPclosed hQclosed hP hQ hcover
  exact ⟨frontier_germ_of_germ hPgerm, frontier_germ_of_germ hQgerm⟩

/-- Applying the actual square-fit support calculation gives the full
germs for a corner rotation with sine at least its positive cosine. -/
theorem positive_rotation_halfCone_germs {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s ε : ℝ} (hc : 0 < c) (hcs : c ≤ s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hPclosed : IsClosed P) (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hε : 0 < ε) (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ e '' P) :
    SameBoundaryGerm P cone45 0 ∧ SameBoundaryGerm (e '' P) upperCone45 0 := by
  obtain ⟨hbelow, habove⟩ := positive_rotation_square_cones e hc hcs he hP heP
  apply halfCone_germs_of_local_cover hε hPclosed
    (e.toHomeomorph.isClosedMap P hPclosed) hbelow (fun p hp => habove p hp) hcover

/-- The equal sine-and-cosine specialization fills both 45-degree sectors. -/
theorem rotation45_halfCone_germs {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c ε : ℝ} (hc : 0 < c)
    (he : ∀ p, e p = directCoordinates c c 0 p)
    (hPclosed : IsClosed P) (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hε : 0 < ε) (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ e '' P) :
    SameBoundaryGerm P cone45 0 ∧ SameBoundaryGerm (e '' P) upperCone45 0 :=
  positive_rotation_halfCone_germs e hc le_rfl he hPclosed hP heP hε hcover

theorem negative_rotation_halfCone_germs {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s ε : ℝ} (hc : 0 < c) (hcs : c ≤ -s)
    (he : ∀ p, e p = directCoordinates c s 0 p)
    (hPclosed : IsClosed P) (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hε : 0 < ε) (hcover : ball (0 : Plane) ε ∩ unitSquare ⊆ P ∪ e '' P) :
    SameBoundaryGerm P upperCone45 0 ∧ SameBoundaryGerm (e '' P) cone45 0 := by
  obtain ⟨habove, hbelow⟩ := negative_rotation_square_cones e hc hcs he hP heP
  have hcover' : ball (0 : Plane) ε ∩ unitSquare ⊆ e '' P ∪ P := by
    simpa only [union_comm] using hcover
  obtain ⟨himage, hsource⟩ := halfCone_germs_of_local_cover hε
    (e.toHomeomorph.isClosedMap P hPclosed) hPclosed hbelow (fun p hp => habove p hp) hcover'
  exact ⟨hsource, himage⟩

end Puzzling139335.DoubleCorner
