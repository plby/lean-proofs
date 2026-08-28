import Wikipedia.HopfProblem.SchwarzReflectionMorera

/-!
# Continuous removability on an open complex domain

This local property says that a continuous complex-valued function is
holomorphic if it is holomorphic away from the specified exceptional set.
The real-axis case is supplied by the proved rectangle form of Morera's
theorem, with no boundary differentiability assumption.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

/-- Local removability for continuous functions.  The ambient domain need
not be open; the property is tested on all of its open subsets. -/
def ContinuousRemovable (Ω S : Set ℂ) : Prop :=
  ∀ V : Set ℂ, IsOpen V → V ⊆ Ω → ∀ f : ℂ → ℂ,
    ContinuousOn f V →
      (∀ z ∈ V \ S, DifferentiableAt ℂ f z) → DifferentiableOn ℂ f V

theorem continuousRemovable_empty (Ω : Set ℂ) : ContinuousRemovable Ω ∅ := by
  intro V _ _ f _ hd z hz
  exact (hd z ⟨hz, notMem_empty z⟩).differentiableWithinAt

theorem ContinuousRemovable.mono_domain {Ω Ω' S : Set ℂ}
    (hS : ContinuousRemovable Ω S) (hΩ : Ω' ⊆ Ω) : ContinuousRemovable Ω' S := by
  intro V hV hVΩ f hf hd
  exact hS V hV (hVΩ.trans hΩ) f hf hd

/-- Only containment of exceptional sets inside the ambient domain is
needed to restrict a removability statement. -/
theorem ContinuousRemovable.mono_set_on {Ω S T : Set ℂ}
    (hS : ContinuousRemovable Ω S) (hTS : ∀ z ∈ Ω, z ∈ T → z ∈ S) :
    ContinuousRemovable Ω T := by
  intro V hV hVΩ f hf hd
  apply hS V hV hVΩ f hf
  intro z hz
  exact hd z ⟨hz.1, fun hT => hz.2 (hTS z (hVΩ hz.1) hT)⟩

theorem ContinuousRemovable.mono_set {Ω S T : Set ℂ}
    (hS : ContinuousRemovable Ω S) (hTS : T ⊆ S) : ContinuousRemovable Ω T :=
  hS.mono_set_on (fun _ _ hz => hTS hz)

/-- The actual real axis is continuously removable on every ambient domain. -/
theorem continuousRemovable_realAxis (Ω : Set ℂ) :
    ContinuousRemovable Ω {z : ℂ | z.im = 0} := by
  intro V hV _ f hf hd
  exact SchwarzReflection.differentiableOn_of_continuousOn_off_real hV hf
    (fun z hz him => hd z ⟨hz, him⟩)

end Wikipedia.HopfProblem.TriangleUniformizationGluing
