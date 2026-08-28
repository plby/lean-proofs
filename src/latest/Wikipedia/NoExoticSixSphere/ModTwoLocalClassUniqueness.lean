import Wikipedia.NoExoticSixSphere.ModTwoLocalClass

/-!
# Uniqueness of the actual nonzero mod-two local class

The native local group is marked by the two-element coefficient module.
Consequently its constructed chart class is its unique nonzero element.
This will let actual local isomorphisms transport the class without making
an orientation choice on chart transitions.
-/

noncomputable section

namespace NoExoticSixSphere.ModTwoLocalClass

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M]

/-- Every nonzero class in the original local group is the constructed chart class. -/
theorem eq_chartClass_of_ne_zero (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source)
    (a : Group 2 x (n + 3)) (ha : a ≠ 0) : a = chartClass n e x hx := by
  let F := chartEquiv n 2 (by decide) e x hx
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  apply F.injective
  rcases hz (F a) with h | h
  · exact (ha (F.injective (h.trans F.map_zero.symm))).elim
  · exact h.trans (chartEquiv_class n e x hx).symm

variable [ChartedSpace E M]

theorem eq_manifoldClass_of_ne_zero (x : M) (a : Group 2 x (n + 3)) (ha : a ≠ 0) :
    a = manifoldClass (E := E) n x :=
  eq_chartClass_of_ne_zero n (chartAt E x) x (mem_chart_source E x) a ha

/-- An actual injective linear map between local groups preserves their canonical classes. -/
theorem injective_map_manifoldClass
    {N : Type} [TopologicalSpace N] [T1Space N] [ChartedSpace E N]
    (x : M) (y : N) (f : Group 2 x (n + 3) →ₗ[ℤ] Group 2 y (n + 3))
    (hf : Function.Injective f) :
    f (manifoldClass (E := E) n x) = manifoldClass (E := E) n y := by
  apply eq_manifoldClass_of_ne_zero (E := E) n y
  intro h
  exact manifoldClass_ne_zero (E := E) n x (hf (h.trans f.map_zero.symm))

end NoExoticSixSphere.ModTwoLocalClass
