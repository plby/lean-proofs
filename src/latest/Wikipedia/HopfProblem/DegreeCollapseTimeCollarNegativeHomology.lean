import Wikipedia.HopfProblem.DegreeCollapseTimeCollarSplitting

/-!
# The actual negative-half inclusion when the positive-half homology vanishes

The original Mayer--Vietoris sum is surjective one degree above vanishing
overlap homology. If the positive summand vanishes, this is surjectivity
of the original negative-half inclusion. Combining with the independently
proved injectivity retains the actual map, not an abstract group isomorphism.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open SingularMayerVietoris

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem halvesHomologySum_surjective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Surjective (C.halvesHomologySum (k + 1)) := by
  have hb := (C.open_halves_right_surjective k).comp
    (C.halvesToOpenHomologyEquiv (k + 1)).surjective
  have he : (rightHomologyMap (C.positiveOpen : Set M)
      (C.reverse.positiveOpen : Set M) (k + 1)) ∘
      C.halvesToOpenHomologyEquiv (k + 1) = C.halvesHomologySum (k + 1) :=
    funext (C.open_halves_right_original_sum (k + 1))
  rw [he] at hb
  exact hb

include C in
theorem negativeInclusion_homology_surjective (k : ℕ)
    [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology (NonnegativeHalf t) (k + 1))] :
    Surjective (singularHomologyMap (halfInclusion (fun p ↦ -t p)) (k + 1)) := by
  intro z
  obtain ⟨⟨x, y⟩, he⟩ := C.halvesHomologySum_surjective k z
  have hx : x = 0 := Subsingleton.elim _ _
  refine ⟨y, ?_⟩
  simpa only [halvesHomologySum_apply, hx, map_zero, zero_add] using he

include C in
theorem negativeInclusion_homology_bijective (k : ℕ)
    [Subsingleton (SingularHomology B k)] [Subsingleton (SingularHomology B (k + 1))]
    [Subsingleton (SingularHomology (NonnegativeHalf t) (k + 1))] :
    Bijective (singularHomologyMap (halfInclusion (fun p ↦ -t p)) (k + 1)) :=
  ⟨C.negativeInclusion_homology_injective (k + 1), C.negativeInclusion_homology_surjective k⟩

include C in
theorem negativeInclusion_homology_bijective_of_ambient_zero (k : ℕ)
    [Subsingleton (SingularHomology B k)] [Subsingleton (SingularHomology M k)] :
    Bijective (singularHomologyMap (halfInclusion (fun p ↦ -t p)) k) :=
  ⟨C.negativeInclusion_homology_injective k, fun _z => ⟨0, Subsingleton.elim _ _⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
