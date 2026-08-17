import ErdosProblems.Erdos83.Compression

namespace Erdos83

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The finite set of all `k`-uniform, two-intersecting families on `Fin N`. -/
noncomputable def candidateFamilies (N k : ℕ) :
    Finset (Finset (Finset (Fin N))) :=
  (Finset.univ : Finset (Finset (Finset (Fin N)))).filter fun F =>
    Uniform k F ∧ TwoIntersecting F

@[simp] lemma mem_candidateFamilies {N k : ℕ} {F : Finset (Finset (Fin N))} :
    F ∈ candidateFamilies N k ↔ Uniform k F ∧ TwoIntersecting F := by
  simp [candidateFamilies]

/-- Every valid uniform two-intersecting family occurs in the finite candidate set. -/
lemma mem_candidateFamilies_of_valid {N k : ℕ} {F : Finset (Finset (Fin N))}
    (huniform : Uniform k F) (hinter : TwoIntersecting F) :
    F ∈ candidateFamilies N k :=
  mem_candidateFamilies.mpr ⟨huniform, hinter⟩

/-- The candidate set is nonempty: it always contains the empty family. -/
lemma candidateFamilies_nonempty (N k : ℕ) : (candidateFamilies N k).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [Uniform, TwoIntersecting]

/--
There is a maximum-cardinality uniform two-intersecting family which is left-compressed.

We first maximize cardinality over the finite candidate set. Among all candidates with that
maximum cardinality we minimize `familyWeight`. A nontrivial left shift preserves validity and
cardinality but strictly lowers the weight, so the selected family is fixed by every left shift.
-/
theorem exists_extremal_leftCompressed (N k : ℕ) :
    ∃ Fmax : Finset (Finset (Fin N)),
      Uniform k Fmax ∧
      TwoIntersecting Fmax ∧
      (∀ F : Finset (Finset (Fin N)),
        Uniform k F → TwoIntersecting F → F.card ≤ Fmax.card) ∧
      LeftCompressed Fmax := by
  obtain ⟨F₀, hF₀cand, hF₀max⟩ :=
    Finset.exists_max_image (candidateFamilies N k) Finset.card
      (candidateFamilies_nonempty N k)
  let maximumCandidates :=
    (candidateFamilies N k).filter fun F => F.card = F₀.card
  have hF₀maximum : F₀ ∈ maximumCandidates := by
    simp [maximumCandidates, hF₀cand]
  obtain ⟨Fmax, hFmaxMaximum, hFmaxMin⟩ :=
    Finset.exists_min_image maximumCandidates familyWeight ⟨F₀, hF₀maximum⟩
  have hFmaxCand : Fmax ∈ candidateFamilies N k := by
    exact (Finset.mem_filter.mp hFmaxMaximum).1
  have hFmaxCard : Fmax.card = F₀.card := by
    exact (Finset.mem_filter.mp hFmaxMaximum).2
  have huniform : Uniform k Fmax := (mem_candidateFamilies.mp hFmaxCand).1
  have hinter : TwoIntersecting Fmax := (mem_candidateFamilies.mp hFmaxCand).2
  refine ⟨Fmax, huniform, hinter, ?_, ?_⟩
  · intro F hFuniform hFinter
    have hFcand : F ∈ candidateFamilies N k :=
      mem_candidateFamilies_of_valid hFuniform hFinter
    simpa [hFmaxCard] using hF₀max F hFcand
  · intro i j hij
    by_contra hshift
    have hshiftUniform : Uniform k (familyShift i j Fmax) :=
      huniform.familyShift i j
    have hshiftInter : TwoIntersecting (familyShift i j Fmax) :=
      hinter.familyShift i j
    have hshiftCand : familyShift i j Fmax ∈ candidateFamilies N k :=
      mem_candidateFamilies_of_valid hshiftUniform hshiftInter
    have hshiftCard : (familyShift i j Fmax).card = F₀.card := by
      rw [card_familyShift, hFmaxCard]
    have hshiftMaximum : familyShift i j Fmax ∈ maximumCandidates := by
      exact Finset.mem_filter.mpr ⟨hshiftCand, hshiftCard⟩
    have hmin := hFmaxMin (familyShift i j Fmax) hshiftMaximum
    have hlt := familyWeight_familyShift_lt hij hshift
    omega

end Erdos83
