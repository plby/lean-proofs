import Wikipedia.SmoothSixDPoincare.MapSmoothingPatch

/-!
# Finite relative smoothing of manifold-valued maps

At every step the map remains smooth on the original neighborhood of the
fixed set. Consequently every subsequent Euclidean approximation can preserve
that fixed set exactly, and the actual relative homotopies concatenate.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X]
  [TopologicalSpace N] [ChartedSpace K N]

/-- Treat finitely many plateaus while preserving old smoothness and a relative homotopy. -/
theorem exists_finite_patch_smoothing_within_target {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch I J (X := X) (N := N))
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : ∀ i, (p i).chart.source ⊆ O) (hmaps : MapsTo f D O) (s : Finset ι) :
    ∃ f' : C(X, N), (∀ j, (p j).Compatible f') ∧ HomotopicRelWithin f f' C D O ∧
      ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) →
        ContMDiffAt I J ∞ f' x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hcompatible, HomotopicRelWithin.refl f C hmaps, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hc₁, hhom₁, hsm₁⟩ := ih
    have hf₁U : ContMDiffOn I J ∞ f₁ U := by
      intro x hx
      exact (hsm₁ x (Or.inl ((hfU x hx).contMDiffAt (hU.mem_nhds hx)))).contMDiffWithinAt
    obtain ⟨f₂, hc₂, hhom₂, hsm₂⟩ :=
      exists_smoothing_patch_step_within_target p i f₁ hc₁ hC hU hCU hf₁U
        (hsource i) hhom₁.mapsTo_right
    refine ⟨f₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply hsm₂ x
    rcases hx with hold | ⟨j, hj, hplateau⟩
    · exact Or.inl (hsm₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hplateau
      · exact Or.inl (hsm₁ x (Or.inr ⟨j, hjs, hplateau⟩))

/-- Forgetting the controlled target gives the original finite smoothing API. -/
theorem exists_finite_patch_smoothing {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch I J (X := X) (N := N))
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (s : Finset ι) :
    ∃ f' : C(X, N), (∀ j, (p j).Compatible f') ∧ f.HomotopicRel f' C ∧
      ∀ x, (ContMDiffAt I J ∞ f x ∨ ∃ i ∈ s, x ∈ (p i).plateau) →
        ContMDiffAt I J ∞ f' x := by
  obtain ⟨f', hc, hrel, hsm⟩ :=
    exists_finite_patch_smoothing_within_target p f hcompatible hC hU hCU hfU
      (fun _ => subset_univ _) (mapsTo_univ f univ) s
  exact ⟨f', hc, hrel.homotopicRel, hsm⟩

/-- A finite covering by the actual plateaus yields a globally smooth relative representative. -/
theorem exists_smoothing_of_finite_patches {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch I J (X := X) (N := N))
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hcover : ∀ x, ∃ i, x ∈ (p i).plateau) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', _, hhom, hsm⟩ :=
    exists_finite_patch_smoothing p f hcompatible hC hU hCU hfU Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hsm x (Or.inr ⟨i, Finset.mem_univ i, hi⟩)

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing
