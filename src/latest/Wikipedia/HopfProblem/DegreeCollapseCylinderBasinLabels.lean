import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Actual endpoint phase formulas determine cylinder basin labels

A finite phase shift along the complete original flow preserves endpoint
limits. Thus the proved coordinate-plane basins in the endpoint charts
give exact basin labels on every time slice of the regular cylinder.
All inverse-coordinate and source memberships are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E Z M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace M]

theorem cylinder_phase_basin_coordinates (F : Flow ℝ M)
    (Φ : Z × ℝ → M) (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Ξ : E → M) (v : E → ℝ)
    (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u))
    (Basin : M → Prop) (hshift : ∀ t x, Basin (F t x) ↔ Basin x)
    (R : E → Prop) (hbasin : ∀ u ∈ Q.source, Basin (Ξ u) ↔ R u) :
    ∀ z ∈ Q.target, ∀ b : ℝ, Basin (Φ (z, b)) ↔ R (Q.symm z) := by
  intro z hz b
  have hu := Q.map_target' hz
  have hi : Q (Q.symm z) = z := Q.right_inv' hz
  have hphase' : Ξ (Q.symm z) = F (v (Q.symm z)) (Φ (z, 0)) := by
    rw [hphase (Q.symm z) hu, hi, hflow z hz]
  have hend : Basin (Ξ (Q.symm z)) ↔ Basin (Φ (z, 0)) := by
    rw [hphase']
    exact hshift _ _
  have hslice : Basin (Φ (z, b)) ↔ Basin (Φ (z, 0)) := by
    rw [hflow z hz b]
    exact hshift _ _
  exact hslice.trans (hend.symm.trans (hbasin _ hu))

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem cylinder_outgoing_basin_labels (F : Flow ℝ M)
    (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Ξ : (A × B) → M) (v : (A × B) → ℝ)
    (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) {q : M}
    (hbasin : ∀ u ∈ Q.source, Tendsto (fun t => F t (Ξ u)) atBot (𝓝 q) ↔ u.2 = 0) :
    ∀ z ∈ Q.target, ∀ b : ℝ,
      Tendsto (fun t => F t (Φ (z, b))) atBot (𝓝 q) ↔
        ∃ x : A, (x, (0 : B)) ∈ Q.source ∧ Q (x, 0) = z := by
  have hcoord := cylinder_phase_basin_coordinates F Φ Q hflow Ξ v hphase
    (fun x => Tendsto (fun t => F t x) atBot (𝓝 q))
    (fun t x => MorseCancellation.flow_time_atBot_limit_iff F t x q)
    (fun u : A × B => u.2 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    have hpair : Q.symm z = ((Q.symm z).1, (0 : B)) := Prod.ext rfl hu
    refine ⟨(Q.symm z).1, hpair ▸ Q.map_target' hz, ?_⟩
    rw [← hpair]
    exact Q.right_inv' hz
  · rintro ⟨x, hx, hQx⟩
    have hi : Q.symm (Q (x, (0 : B))) = (x, 0) := Q.left_inv' hx
    rw [← hQx, hi]

theorem cylinder_incoming_basin_labels (F : Flow ℝ M)
    (Φ : Z × ℝ → M)
    (P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ P.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0)))
    (Ξ : (A × B) → M) (v : (A × B) → ℝ)
    (hphase : ∀ u ∈ P.source, Ξ u = Φ (P u, v u)) {p : M}
    (hbasin : ∀ u ∈ P.source, Tendsto (fun t => F t (Ξ u)) atTop (𝓝 p) ↔ u.1 = 0) :
    ∀ z ∈ P.target, ∀ b : ℝ,
      Tendsto (fun t => F t (Φ (z, b))) atTop (𝓝 p) ↔
        ∃ y ∈ P.source, y.1 = 0 ∧ P y = z := by
  have hcoord := cylinder_phase_basin_coordinates F Φ P hflow Ξ v hphase
    (fun x => Tendsto (fun t => F t x) atTop (𝓝 p))
    (fun t x => MorseCancellation.flow_time_atTop_limit_iff F t x p)
    (fun u : A × B => u.1 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    exact ⟨P.symm z, P.map_target' hz, hu, P.right_inv' hz⟩
  · rintro ⟨y, hy, hy0, hPy⟩
    have hi : P.symm (P y) = y := P.left_inv' hy
    rw [← hPy, hi]
    exact hy0

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
