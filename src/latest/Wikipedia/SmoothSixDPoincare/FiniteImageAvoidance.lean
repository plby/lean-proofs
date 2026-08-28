import Wikipedia.SmoothSixDPoincare.ImageAvoidancePatch

/-!
# Finite induction for relative smooth image avoidance

Every step retains the future chart conditions and all previous avoidance.
Concatenating the actual relative homotopies gives a global relative homotopy.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.GeneralPosition

variable {E E' G H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [TopologicalSpace N] [ChartedSpace K N] [LindelofSpace (X × Y)]

/-- Treat a finite collection of actual chart patches, relative to `C`. -/
theorem exists_finite_patch_avoidance {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C)
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (s : Finset ι) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧
      ∀ x, (f x ∉ range g ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ range g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRel.refl f, ?_⟩
    intro x hx
    simpa using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, havoid₂⟩ := exists_patch_step p i f₁ g hf₁ hg hc₁ hdim
    refine ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hnonzero⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hnonzero
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hnonzero⟩))

/-- Covering all initial intersections by finitely many patches removes every intersection. -/
theorem exists_avoidance_of_finite_patches {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C)
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hcover : ∀ x, f x ∈ range g → ∃ i, (p i).cutoff x ≠ 0) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧
      Disjoint (range f') (range g) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨f', hf', _, hhom, havoid⟩ :=
    exists_finite_patch_avoidance p f g hf hg hcompatible hdim Finset.univ
  refine ⟨f', hf', hhom, disjoint_left.mpr ?_⟩
  rintro z ⟨x, rfl⟩ hz
  apply havoid x _ hz
  by_cases hx : f x ∈ range g
  · obtain ⟨i, hi⟩ := hcover x hx
    exact Or.inr ⟨i, Finset.mem_univ i, hi⟩
  · exact Or.inl hx

end Wikipedia.SmoothSixDPoincare.GeneralPosition
