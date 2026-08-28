import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMaps

/-!
# Detecting agreement of native line-bundle maps

Two preferred-fibre multiplier maps that agree on one nonzero vector
agree on the entire fibre. In particular all their extracted chart
units agree. This allows agreement on a dense generic set to be proved
using the common image of a genuine nonzero meromorphic-section value,
before applying holomorphic continuation to the local gauge units.
-/

noncomputable section

open Bundle Set Topology

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
    (A : TransitionData M ι) (B : TransitionData M η) (h h' : M → ℂˣ)

/-- The actual native chart frame is nonzero at every point of its chart. -/
theorem localFrame_ne_zero (i : ι) {x : M} (hx : x ∈ A.baseSet i) :
    localFrame A i x ≠ 0 := by
  intro hz
  have he : id (α := ℂ) (localFrame A i x) = 0 := hz
  rw [localFrame_preferred A i hx] at he
  exact A.transition_ne_zero i (A.indexAt x) x he

/-- Agreement of the actual maps on one nonzero vector determines the
preferred unit multiplier, by cancellation in the actual scalar fibre. -/
theorem multiplier_eq_of_image_eq (x : M) (v : A.core.Fiber x) (hv : v ≠ 0)
    (he : preferredMap A B h ⟨x, v⟩ = preferredMap A B h' ⟨x, v⟩) : h x = h' x := by
  apply Units.ext
  have hs := congrArg (fun q : B.core.TotalSpace => id (α := ℂ) q.2) he
  change (h x : ℂ) * id (α := ℂ) v = (h' x : ℂ) * id (α := ℂ) v at hs
  exact mul_right_cancel₀ (show id (α := ℂ) v ≠ 0 from hv) hs

/-- The same hypothesis gives equality on every vector of that original fibre. -/
theorem preferredMap_eq_on_fiber_of_image_eq (x : M) (v : A.core.Fiber x) (hv : v ≠ 0)
    (he : preferredMap A B h ⟨x, v⟩ = preferredMap A B h' ⟨x, v⟩)
    (w : A.core.Fiber x) :
    preferredMap A B h ⟨x, w⟩ = preferredMap A B h' ⟨x, w⟩ := by
  change (⟨x, (h x : ℂ) * id (α := ℂ) w⟩ : B.core.TotalSpace) =
    ⟨x, (h' x : ℂ) * id (α := ℂ) w⟩
  rw [multiplier_eq_of_image_eq A B h h' x v hv he]

/-- All extracted original-chart gauge units agree when the actual maps
have a common image of a nonzero source vector. -/
theorem chartUnit_eq_of_image_eq (i : ι × η) (x : M) (v : A.core.Fiber x) (hv : v ≠ 0)
    (he : preferredMap A B h ⟨x, v⟩ = preferredMap A B h' ⟨x, v⟩) :
    chartUnit A B h i x = chartUnit A B h' i x :=
  chartUnit_eq_of_multiplier_eq A B h i (multiplier_eq_of_image_eq A B h h' x v hv he)

/-- It suffices to compare the images of the actual source chart frame. -/
theorem chartUnit_eq_of_frameImage_eq (i : ι × η) {x : M}
    (hx : x ∈ A.baseSet i.1)
    (he : preferredMap A B h (localFrameMap A i.1 x) =
      preferredMap A B h' (localFrameMap A i.1 x)) :
    chartUnit A B h i x = chartUnit A B h' i x :=
  chartUnit_eq_of_image_eq A B h h' i x (localFrame A i.1 x)
    (localFrame_ne_zero A i.1 hx) he

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps
