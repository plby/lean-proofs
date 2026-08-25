import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals.Ordered

/-!
# Closed side coverage absorbs finitely many exceptional contacts

A finite subset cannot supply a missing contact of a closed cover of an
interval.  This applies in particular when the fourth piece has at most one
contact on a side of the square.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.BoundaryIntervals

/-- A closed subset containing a nondegenerate interval apart from finitely
many parameters contains the whole interval. -/
theorem closed_contains_interval_of_finite_exception {a b : ℝ} {C F : Set ℝ}
    (hab : a < b) (hC : IsClosed C) (hF : F.Finite)
    (hcover : Icc a b \ F ⊆ C) : Icc a b ⊆ C := by
  have hdense : Dense Fᶜ := by
    exact ((dense_univ : Dense (univ : Set ℝ)).sdiff_finite hF).mono
      (fun _ ht => ht.2)
  have hsmall : Ioo a b ∩ Fᶜ ⊆ C := by
    intro t ht
    exact hcover ⟨Ioo_subset_Icc_self ht.1, ht.2⟩
  have hopen : Ioo a b ⊆ C :=
    (hdense.open_subset_closure_inter isOpen_Ioo).trans (closure_minimal hsmall hC)
  have hclosed := closure_minimal hopen hC
  rwa [closure_Ioo hab.ne] at hclosed

variable {X : Type*} [TopologicalSpace X]

/-- Removing finitely many exceptional parameters from the coverage hypothesis
does not weaken a closed two-piece cover of a continuous side. -/
theorem cover_of_finite_parameter_exception {γ : ℝ → X} {P Q : Set X} {F : Set ℝ}
    (hγ : Continuous γ) (hP : IsClosed P) (hQ : IsClosed Q) (hF : F.Finite)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ F → γ t ∈ P ∨ γ t ∈ Q) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ Q := by
  have hsub : Icc (0 : ℝ) 1 \ F ⊆ γ ⁻¹' (P ∪ Q) := by
    intro t ht
    exact hcover t ht.1 ht.2
  exact closed_contains_interval_of_finite_exception (by norm_num)
    ((hP.union hQ).preimage hγ) hF hsub

/-- A third set with at most one actual contact on an injectively parametrized
side cannot fill a gap left by two closed pieces. -/
theorem cover_of_subsingleton_contact {γ : ℝ → X} {P Q R : Set X}
    (hγ : Continuous γ) (hγinj : InjOn γ (Icc (0 : ℝ) 1))
    (hP : IsClosed P) (hQ : IsClosed Q)
    (hR : (R ∩ γ '' Icc (0 : ℝ) 1).Subsingleton)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ Q ∨ γ t ∈ R) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ Q := by
  let F : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ γ t ∈ R}
  have hF : F.Subsingleton := by
    intro s hs t ht
    exact hγinj hs.1 ht.1 (hR ⟨hs.2, mem_image_of_mem γ hs.1⟩
      ⟨ht.2, mem_image_of_mem γ ht.1⟩)
  apply cover_of_finite_parameter_exception hγ hP hQ hF.finite
  intro t ht htF
  rcases hcover t ht with htP | htQ | htR
  · exact Or.inl htP
  · exact Or.inr htQ
  · exact False.elim (htF ⟨ht, htR⟩)

/-- The complete cutoff theorem with finitely many exceptional parameters. -/
theorem exists_cutoff_of_finite_parameter_exception {γ : ℝ → X} {P Q : Set X}
    {F : Set ℝ} (hγ : Continuous γ) (hP : IsClosed P) (hQ : IsClosed Q)
    (hNI : Noninterlacing γ P Q)
    (h0P : γ 0 ∈ P) (h0Q : γ 0 ∉ Q) (h1P : γ 1 ∉ P) (h1Q : γ 1 ∈ Q)
    (hF : F.Finite)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ F → γ t ∈ P ∨ γ t ∈ Q) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (γ t ∈ P ↔ t ≤ l) ∧ (γ t ∈ Q ↔ l ≤ t) := by
  exact exists_cutoff_of_noninterlacing hγ hP hQ hNI h0P h0Q h1P h1Q
    (cover_of_finite_parameter_exception hγ hP hQ hF hcover)

/-- The complete cutoff theorem when a third set has at most one contact. -/
theorem exists_cutoff_of_subsingleton_contact {γ : ℝ → X} {P Q R : Set X}
    (hγ : Continuous γ) (hγinj : InjOn γ (Icc (0 : ℝ) 1))
    (hP : IsClosed P) (hQ : IsClosed Q) (hNI : Noninterlacing γ P Q)
    (h0P : γ 0 ∈ P) (h0Q : γ 0 ∉ Q) (h1P : γ 1 ∉ P) (h1Q : γ 1 ∈ Q)
    (hR : (R ∩ γ '' Icc (0 : ℝ) 1).Subsingleton)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∨ γ t ∈ Q ∨ γ t ∈ R) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (γ t ∈ P ↔ t ≤ l) ∧ (γ t ∈ Q ↔ l ≤ t) := by
  exact exists_cutoff_of_noninterlacing hγ hP hQ hNI h0P h0Q h1P h1Q
    (cover_of_subsingleton_contact hγ hγinj hP hQ hR hcover)

end Puzzling139335.N4TwoOneOne.BoundaryIntervals
