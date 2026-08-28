import Wikipedia.HopfProblem.CuspHoneycombStrata
import Wikipedia.HopfProblem.CuspCollapseStabilizersGroups

/-!
# Exact fibre-torus stabilizers on the actual honeycomb strata

The original toric branch labels determine the zero-coordinate pattern in
any toric chart. Combining the chart stabilizer calculation with the actual
honeycomb branch correspondence gives the trivial group on one-cell
strata, the vertex-difference circle on two-cell strata, and the full fibre
torus at the actual three-cell vertices.
-/

open Set Topology

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

/-- A toric point with exactly one branch label has trivial fibre stabilizer. -/
theorem compactFibre_stabilizer_eq_bot_of_branchVertices_singleton
    (x : Space) (v : Fin 2 → ℤ) (hx : branchVertices x = {v}) :
    MulAction.stabilizer CompactFibreTorus x = ⊥ := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hv : inclusion s z ∈ rayDivisor v := by
    change v ∈ branchVertices (inclusion s z)
    rw [hx]
    exact mem_singleton v
  obtain ⟨j, _, hjv⟩ := (mem_rayDivisor_inclusion v s z).mp hv
  apply compactFibre_stabilizer_eq_bot_of_at_most_one_zero s z j
  intro i hij hzi
  have hi : s.vertex i ∈ branchVertices (inclusion s z) :=
    (mem_rayDivisor_vertex s i z).mpr hzi
  have hiv : s.vertex i = v := by simpa only [hx, mem_singleton_iff] using hi
  exact hij (s.vertex_injective (hiv.trans hjv.symm))

/-- Two distinct toric branch labels determine the exact embedded edge
circle, with no choice of chart or orientation left in the conclusion. -/
theorem compactFibre_stabilizer_eq_edgeCircle_of_branchVertices_pair
    (x : Space) (v w : Fin 2 → ℤ) (hvw : v ≠ w)
    (hx : branchVertices x = {v, w}) :
    MulAction.stabilizer CompactFibreTorus x = edgeCircle (w - v) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  have hv : inclusion s z ∈ rayDivisor v := by
    change v ∈ branchVertices (inclusion s z)
    rw [hx]
    exact mem_insert v {w}
  have hw : inclusion s z ∈ rayDivisor w := by
    change w ∈ branchVertices (inclusion s z)
    rw [hx]
    exact mem_insert_of_mem v (mem_singleton w)
  obtain ⟨j, hzj, hjv⟩ := (mem_rayDivisor_inclusion v s z).mp hv
  obtain ⟨k, hzk, hkw⟩ := (mem_rayDivisor_inclusion w s z).mp hw
  have hjk : j ≠ k := by
    intro h
    exact hvw (hjv.symm.trans ((congrArg s.vertex h).trans hkw))
  have hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0 := by
    intro i hij hik hzi
    have hi : s.vertex i ∈ branchVertices (inclusion s z) :=
      (mem_rayDivisor_vertex s i z).mpr hzi
    rw [hx, mem_insert_iff, mem_singleton_iff] at hi
    rcases hi with hiv | hiw
    · exact hij (s.vertex_injective (hiv.trans hjv.symm))
    · exact hik (s.vertex_injective (hiw.trans hkw.symm))
  simpa only [hjv, hkw] using
    compactFibre_stabilizer_eq_edgeCircle_of_two_zero s z j k hjk hzj hzk hz

/-- A point with three actual toric branches is a chart origin and has
the entire compact fibre torus as stabilizer. -/
theorem compactFibre_stabilizer_eq_top_of_branchCount_three
    (x : Space) (hx : branchCount x = 3) :
    MulAction.stabilizer CompactFibreTorus x = ⊤ := by
  obtain ⟨s, rfl⟩ := (branchCount_eq_three x).mp hx
  exact compactFibre_stabilizer_inclusion_zero s

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace ToricFan CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane
local notation "Lattice" => CuspHoneycombTiling.Lattice

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- On an actual one-cell honeycomb stratum the fibre torus acts freely. -/
theorem honeycombHomeomorph_stabilizer_eq_bot (y : Plane) (v : Lattice)
    (hcells : {u : Lattice | y ∈ cell u} = {v}) :
    MulAction.stabilizer CompactFibreTorus ((honeycombHomeomorph C₀ y).1 : Space) = ⊥ :=
  compactFibre_stabilizer_eq_bot_of_branchVertices_singleton _ v
    ((honeycombHomeomorph_branchVertices C₀ y).trans hcells)

/-- In particular, the action is free over every actual open hexagon interior. -/
theorem honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior
    (y : Plane) (v : Lattice) (hy : y ∈ interior (cell v)) :
    MulAction.stabilizer CompactFibreTorus ((honeycombHomeomorph C₀ y).1 : Space) = ⊥ :=
  honeycombHomeomorph_stabilizer_eq_bot C₀ y v
    ((containingCells_eq_singleton_iff y v).mpr hy)

/-- On the actual open common edge of the cells labelled `v` and `w`,
the stabilizer is exactly their difference circle in the original fibre torus. -/
theorem honeycombHomeomorph_stabilizer_eq_edgeCircle
    (y : Plane) (v w : Lattice) (hvw : v ≠ w)
    (hcells : {u : Lattice | y ∈ cell u} = {v, w}) :
    MulAction.stabilizer CompactFibreTorus ((honeycombHomeomorph C₀ y).1 : Space) =
      edgeCircle (w - v) :=
  compactFibre_stabilizer_eq_edgeCircle_of_branchVertices_pair _ v w hvw
    ((honeycombHomeomorph_branchVertices C₀ y).trans hcells)

/-- Exactly three containing honeycomb cells give the full fibre-torus stabilizer. -/
theorem honeycombHomeomorph_stabilizer_eq_top_of_three (y : Plane)
    (hcells : {v : Lattice | y ∈ cell v}.ncard = 3) :
    MulAction.stabilizer CompactFibreTorus ((honeycombHomeomorph C₀ y).1 : Space) = ⊤ :=
  compactFibre_stabilizer_eq_top_of_branchCount_three _
    ((honeycombHomeomorph_branchCount C₀ y).trans hcells)

/-- Every actual triangle barycenter has the full fibre-torus stabilizer. -/
theorem honeycombHomeomorph_stabilizer_triangleBarycenter (s : Triangle) :
    MulAction.stabilizer CompactFibreTorus
      ((honeycombHomeomorph C₀ (triangleBarycenter s)).1 : Space) = ⊤ := by
  rw [honeycombHomeomorph_triangleBarycenter_coe]
  exact compactFibre_stabilizer_inclusion_zero s

end Wikipedia.HopfProblem.CuspHoneycomb
