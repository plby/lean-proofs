import Wikipedia.HopfProblem.DegreeCollapseUnitSphereEquiv

/-!
# The two actual points of a one-dimensional unit sphere

A normalized continuous linear equivalence to the real line shows that any
two distinct points exhaust the unit sphere. A predicate holding at exactly
one of them therefore has cardinality one, without supplied finite data.
-/

noncomputable section

open Set Metric Function

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem unitSphere_eq_two_points_of_finrank_one (hdim : Module.finrank ℝ V = 1)
    (u v : sphere (0 : V) 1) (huv : u ≠ v) (w : sphere (0 : V) 1) : w = u ∨ w = v := by
  obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hdim)
  let e := UnitSphereEquiv.homeomorph L
  have hpoint (z : sphere (0 : V) 1) : (e z : ℝ) = 1 ∨ (e z : ℝ) = -1 := by
    have hz : |(e z : ℝ)| = |(1 : ℝ)| := by
      simpa only [Real.norm_eq_abs, abs_one] using mem_sphere_zero_iff_norm.mp (e z).property
    exact abs_eq_abs.mp hz
  have hne : (e u : ℝ) ≠ (e v : ℝ) := fun h => huv (e.injective (Subtype.ext h))
  have heq : (e w : ℝ) = (e u : ℝ) ∨ (e w : ℝ) = (e v : ℝ) := by
    rcases hpoint u with hu | hu <;> rcases hpoint v with hv | hv <;>
      rcases hpoint w with hw | hw <;> simp_all
  exact heq.elim (fun h => Or.inl (e.injective (Subtype.ext h)))
    (fun h => Or.inr (e.injective (Subtype.ext h)))

theorem ncard_unitSphere_predicate_one (hdim : Module.finrank ℝ V = 1)
    (P : sphere (0 : V) 1 → Prop) (u v : sphere (0 : V) 1) (hu : P u) (hv : ¬P v) :
    {z | P z}.ncard = 1 := by
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  apply Set.ncard_eq_one.mpr
  refine ⟨u, ?_⟩
  ext z
  constructor
  · intro hz
    rcases unitSphere_eq_two_points_of_finrank_one hdim u v huv z with h | h
    · exact h
    · exact False.elim (hv (h ▸ hz))
  · intro hz
    exact (mem_singleton_iff.mp hz) ▸ hu

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
