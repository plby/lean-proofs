import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspChart

/-!
# Comparing a descended function with the actual cusp chart

An eventual identity high in the upper half-plane becomes an identity
on an actual cusp neighborhood in the triangle orbit quotient.  The
coordinate is the fixed-width chart used in the compactification.
-/

open Filter

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- An eventual cusp-coordinate formula descends to a sufficiently high
cusp image, expressed in the actual fixed-width compactification chart. -/
theorem exists_cuspImage_eq_of_eventually_atImInfty
    {f : TriangleOrbitSpace → ℂ} {g : ℂ → ℂ}
    (h : ∀ᶠ z in UpperHalfPlane.atImInfty,
      f (triangleOrbitProjection z) = g (Triangle.cuspQ z)) :
    ∃ Y : ℝ, Triangle.width ≤ Y ∧ ∀ q ∈ Triangle.cuspImage Y,
      f q = g (Triangle.cuspFullChart Triangle.width le_rfl (triangleOpenInclusion q)) := by
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp h
  refine ⟨max Triangle.width A, le_max_left _ _, ?_⟩
  intro q hq
  obtain ⟨z, hz, rfl⟩ := (Triangle.mem_cuspImage _ _).mp hq
  have hzwidth : z ∈ Triangle.horodisc Triangle.width :=
    (le_max_left _ _).trans_lt hz
  rw [Triangle.cuspFullChart_mk Triangle.width le_rfl ⟨z, hzwidth⟩]
  exact hA z ((le_max_right _ _).trans hz.le)

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
