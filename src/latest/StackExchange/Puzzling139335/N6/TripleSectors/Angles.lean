import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Existence
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Congruence
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Trisection

/-!
# Three congruent actual sector germs divide the square corner into thirds

The hypotheses refer to actual Jordan pieces, their actual two straight
boundary branches, a genuine local cover, and actual origin-fixing
congruences.  Equal angular widths, interval adjacency, and thirty-degree
angles are conclusions.
-/

open Set Metric

namespace Puzzling139335.N6.TripleSectors.Angles

namespace RaySectorGerm

/-- The actual region congruence preserves the angle between its actual rays. -/
theorem width_eq_of_congruence {P Q : Set Plane}
    (g : RaySectorGerm P) (h : RaySectorGerm Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) (he : e '' P = Q) :
    g.upper - g.lower = h.upper - h.lower := by
  rw [← g.angle_eq_width, ← h.angle_eq_width]
  exact Congruence.angle_eq_of_region_congruence g.boundary_germ h.boundary_germ
    e he0 he g.det_pos.ne'

/-- An actual origin-fixing congruence sends the normalized endpoint rays to
the target endpoint rays, with only the direct and swapped possibilities. -/
theorem angular_endpoints_match {P Q : Set Plane}
    (g : RaySectorGerm P) (h : RaySectorGerm Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) (he : e '' P = Q) :
    (e (ThreeCorners.ray g.lower) = ThreeCorners.ray h.lower ∧
      e (ThreeCorners.ray g.upper) = ThreeCorners.ray h.upper) ∨
    (e (ThreeCorners.ray g.lower) = ThreeCorners.ray h.upper ∧
      e (ThreeCorners.ray g.upper) = ThreeCorners.ray h.lower) := by
  simpa only [g.normalized_left_eq, g.normalized_right_eq,
    h.normalized_left_eq, h.normalized_right_eq] using
    Congruence.normalized_rays_match_of_region_congruence
      g.boundary_germ h.boundary_germ e he0 he g.det_pos.ne'

end RaySectorGerm

/-- Three congruent Jordan pieces with actual straight local branches,
disjoint interiors, and a genuine local square-corner cover have angles
`π/6`, and their actual endpoint rays occur at `0, π/6, π/3, π/2` in order. -/
theorem exists_raySectorGerms_trisection {P : Fin 3 → Set Plane}
    (hP : ∀ i, IsJordanRegion (P i))
    (hquadrant : ∀ i x, x ∈ P i → 0 ≤ x 0 ∧ 0 ≤ x 1)
    (hcount : ∀ i, HasStraightBranchCount (frontier (P i)) 0 2)
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : ∃ R > 0, ball (0 : Plane) R ∩ {x | 0 ≤ x 0 ∧ 0 ≤ x 1} ⊆ ⋃ i, P i)
    (hcong : ∀ i j, ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, e 0 = 0 ∧ e '' P i = P j) :
    ∃ g : ∀ i, RaySectorGerm (P i),
      (∀ i, (g i).upper - (g i).lower = Real.pi / 6) ∧
      ∃ σ : Equiv.Perm (Fin 3),
        (g (σ 0)).lower = 0 ∧ (g (σ 0)).upper = Real.pi / 6 ∧
        (g (σ 1)).lower = Real.pi / 6 ∧ (g (σ 1)).upper = Real.pi / 3 ∧
        (g (σ 2)).lower = Real.pi / 3 ∧ (g (σ 2)).upper = Real.pi / 2 := by
  classical
  let g : ∀ i, RaySectorGerm (P i) := fun i =>
    Classical.choice (nonempty_raySectorGerm (hP i) (hquadrant i) (hcount i))
  have hwidth : ∀ i j, (g i).upper - (g i).lower = (g j).upper - (g j).lower := by
    intro i j
    obtain ⟨e, he0, he⟩ := hcong i j
    exact (g i).width_eq_of_congruence (g j) e he0 he
  refine ⟨g, ?_, ?_⟩
  · exact fun i => width_eq_pi_div_six_of_equal_widths
      (fun i => (g i).toAngularGerm) hdis hcover hwidth i
  · exact exists_ordering_of_equal_widths
      (fun i => (g i).toAngularGerm) hdis hcover hwidth

end Puzzling139335.N6.TripleSectors.Angles
