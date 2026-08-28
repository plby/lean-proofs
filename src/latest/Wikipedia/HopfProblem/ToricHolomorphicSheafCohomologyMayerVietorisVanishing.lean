import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietorisSections

/-!
# Genuine Mayer–Vietoris vanishing for a union of opens

Higher union cohomology vanishes when the relevant component and
intersection groups vanish. Degree one uses the actual surjectivity of
the difference of the section restriction maps.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U V : Opens X)

/-- If the component groups in degree `n+1` and intersection group in
degree `n` vanish, the actual union group in degree `n+1` vanishes. -/
theorem union_successor_subsingleton (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F n (U ⊓ V))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) U)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) V)] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U ⊔ V)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro a
  obtain ⟨b, rfl⟩ := connecting_surjective F U V n a
  have hb : b = 0 := @Subsingleton.elim (CategoryTheory.Sheaf.H'.{0} F n (U ⊓ V))
    inferInstance b 0
  exact (congrArg (connecting F U V n) hb).trans (map_zero _)

/-- Exactness makes the degree-one union group zero when the genuine
degree-zero difference is onto and the component degree-one groups vanish. -/
theorem union_one_subsingleton_of_cohomology_difference
    (h : Function.Surjective (restrictionDifference F U V 0))
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 U)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 V)] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U ⊔ V)) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro a
  obtain ⟨b, rfl⟩ := connecting_surjective F U V 0 a
  obtain ⟨s, rfl⟩ := h b
  exact ConcreteCategory.congr_hom ((square U V).fromBiprod_δ F 0 1 rfl) s

/-- Surjectivity of the literal difference of section restrictions is
the only additional degree-zero input needed for actual H¹ of the union. -/
theorem union_one_subsingleton
    (h : Function.Surjective (sectionsDifference F U V))
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 U)]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 V)] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U ⊔ V)) :=
  union_one_subsingleton_of_cohomology_difference F U V
    (restrictionDifference_zero_surjective F U V h)

/-- Positive-degree acyclicity of both opens and their intersection,
together with actual section-difference surjectivity, gives acyclicity
of their union in all positive degrees. -/
theorem union_higher_subsingleton
    (hU : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) U))
    (hV : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) V))
    (hI : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U ⊓ V)))
    (h : Function.Surjective (sectionsDifference F U V)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U ⊔ V)) := by
  cases n with
  | zero =>
      have := hU 0
      have := hV 0
      exact union_one_subsingleton F U V h
  | succ n =>
      have := hU (n + 1)
      have := hV (n + 1)
      have := hI n
      exact union_successor_subsingleton F U V (n + 1)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris
