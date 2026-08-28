import Mathlib.Topology.ContinuousMap.Compact

/-!
# Attainment of a finite family of compact sup norms

A nonzero finite dependent family of continuous maps on compact spaces
attains its product sup norm at a point of one component. Empty index
types and empty component spaces require no extra assumptions: nonzero
families are handled directly by the strict sup-norm inequalities.
-/

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {ι : Type*} [Fintype ι] {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
  {E : Type*} [NormedAddCommGroup E]

/-- Every component value is bounded by the norm of the complete finite family. -/
theorem norm_apply_le_norm (F : ∀ i, C(X i, E)) (i : ι) (x : X i) :
    ‖F i x‖ ≤ ‖F‖ :=
  ((F i).norm_coe_le_norm x).trans (norm_le_pi_norm F i)

/-- A nonzero finite family attains its sup norm, without assuming any
component space or the index type is nonempty in advance. -/
theorem exists_norm_apply_eq_norm (F : ∀ i, C(X i, E)) (hF : F ≠ 0) :
    ∃ i, ∃ x : X i, ‖F i x‖ = ‖F‖ := by
  classical
  by_contra h
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF
  apply (lt_irrefl ‖F‖)
  apply (pi_norm_lt_iff hpos).mpr
  intro i
  apply ((F i).norm_lt_iff hpos).mpr
  intro x
  refine lt_of_le_of_ne (norm_apply_le_norm F i x) ?_
  intro hix
  exact h ⟨i, x, hix⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
