import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsNative

/-!
# A native line-bundle nontriviality criterion

A genuine holomorphic fibre-linear trivialization supplies a nowhere
zero holomorphic section by pulling back the constant vector one.
Thus vanishing of the entire native holomorphic section space rules
out such a trivialization.  Applied separately to every positive tensor
power, this proves non-torsion; vanishing for the first power alone
would not suffice.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  (A : TransitionData M ι)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Triviality means an actual holomorphic, complex-fibre-linear
biholomorphism of the native total space with the ordinary product. -/
def HolomorphicallyTrivial : Prop :=
  ∃ e : Diffeomorph (I.prod I₁) (I.prod I₁) A.core.TotalSpace (M × ℂ) ω,
    ∀ x, ∃ φ : A.core.Fiber x ≃L[ℂ] ℂ, ∀ v, e ⟨x, v⟩ = (x, φ v)

/-- The pullback of one through an actual fibre-linear trivialization
is a genuine holomorphic section which is nowhere zero. -/
theorem exists_nonzero_section_of_holomorphicallyTrivial
    (h : HolomorphicallyTrivial I A) :
    ∃ s : ContMDiffSection I ℂ ω A.core.Fiber, ∀ x, s x ≠ 0 := by
  rcases h with ⟨e, he⟩
  choose φ hφ using he
  let s : ∀ x, A.core.Fiber x := fun x => (φ x).symm 1
  have hmap : (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) =
      fun x => e.symm (x, (1 : ℂ)) := by
    funext x
    have hv : e ⟨x, s x⟩ = (x, (1 : ℂ)) := by
      rw [hφ]
      exact congrArg (fun z : ℂ => (x, z)) ((φ x).apply_symm_apply 1)
    exact (e.symm_apply_apply (⟨x, s x⟩ : A.core.TotalSpace)).symm.trans
      (congrArg e.symm hv)
  have hs : ContMDiff I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) := by
    rw [hmap]
    exact e.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  refine ⟨⟨s, hs⟩, ?_⟩
  intro x hz
  have ht := congrArg (φ x) hz
  change φ x ((φ x).symm 1) = φ x 0 at ht
  rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at ht
  exact one_ne_zero ht

/-- This criterion concerns the whole section space, not a particular
candidate section or a chosen local frame. -/
theorem not_holomorphicallyTrivial_of_sections_zero [Nonempty M]
    (hzero : ∀ s : ContMDiffSection I ℂ ω A.core.Fiber, s = 0) :
    ¬ HolomorphicallyTrivial I A := by
  intro ht
  obtain ⟨s, hs⟩ := exists_nonzero_section_of_holomorphicallyTrivial I A ht
  obtain ⟨x⟩ := ‹Nonempty M›
  have hx := congrArg (fun t : ContMDiffSection I ℂ ω A.core.Fiber => t x) (hzero s)
  exact hs x hx

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle
