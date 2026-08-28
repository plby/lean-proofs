import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalFreeBasic

/-!
# Arbitrary-rank submodules of free integral modules

Every submodule of a free integral module is free.  After well-ordering an
ambient basis, the lifts of the nonzero leading-ideal generators form a
basis: independence is triangular, and spanning follows by well-founded
descent of the largest support coordinate.  This applies in particular to
images of differentials in actual singular-chain modules, with no finite
generation assumption on those modules or images.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation

open Module Submodule Submodule.IsPrincipal

namespace LocalFree

variable {ι : Type*} [LinearOrder ι] (N : Submodule ℤ (ι →₀ ℤ))

theorem leadingFamily_linearIndependent : LinearIndependent ℤ (leadingFamily N) := by
  apply triangular_linearIndependent (leadingFamily N)
    (fun i => (Finsupp.lapply i.val).comp N.subtype)
  · intro i
    exact leadingFamily_diagonal_ne_zero N i
  · intro i j hij
    exact leadingFamily_above N i j hij

/-- The leading vectors span each closed initial support segment. -/
theorem mem_span_leadingFamily_of_bounded [WellFoundedLT ι] (i : ι) :
    ∀ x : N, (∀ j, i < j → x.val j = 0) →
      x ∈ Submodule.span ℤ (Set.range (leadingFamily N)) := by
  apply wellFounded_lt.induction i
  intro i ih x hx
  have below : ∀ y : N, (∀ j, i ≤ j → y.val j = 0) →
      y ∈ Submodule.span ℤ (Set.range (leadingFamily N)) := by
    intro y hy
    by_cases hyzero : y = 0
    · simpa only [hyzero] using
        (Submodule.zero_mem (Submodule.span ℤ (Set.range (leadingFamily N))))
    have hyval : y.val ≠ 0 := fun h => hyzero (Subtype.ext h)
    obtain ⟨j, hj, hjmax⟩ := exists_largest_support y.val hyval
    exact ih j (lt_of_not_ge fun hij => hj (hy j hij)) y hjmax
  obtain ⟨r, hr⟩ := generator_dvd_coefficient N i x hx
  by_cases hg : generator (leadingIdeal N i) = 0
  · apply below x
    intro j hij
    rcases eq_or_lt_of_le hij with rfl | hij
    · simpa only [hg, zero_mul] using hr
    · exact hx j hij
  · let k : LeadingIndex N := ⟨i, hg⟩
    have hy : x - r • leadingFamily N k ∈
        Submodule.span ℤ (Set.range (leadingFamily N)) := by
      apply below
      intro j hij
      change x.val j - r * (leadingVector N i).val j = 0
      rcases eq_or_lt_of_le hij with rfl | hij
      · rw [leadingVector_diagonal, hr, mul_comm, sub_self]
      · rw [hx j hij, leadingVector_above N i j hij, mul_zero, sub_self]
    have hv : r • leadingFamily N k ∈
        Submodule.span ℤ (Set.range (leadingFamily N)) :=
      Submodule.smul_mem _ r (Submodule.subset_span ⟨k, rfl⟩)
    simpa only [sub_add_cancel] using Submodule.add_mem _ hy hv

theorem leadingFamily_span_eq_top [WellFoundedLT ι] :
    Submodule.span ℤ (Set.range (leadingFamily N)) = ⊤ := by
  apply top_unique
  intro x _
  by_cases hx : x = 0
  · simpa only [hx] using
      (Submodule.zero_mem (Submodule.span ℤ (Set.range (leadingFamily N))))
  obtain ⟨i, _, hi⟩ := exists_largest_support x.val (fun h => hx (Subtype.ext h))
  exact mem_span_leadingFamily_of_bounded N i x hi

/-- The actual triangular basis of an arbitrary submodule of a well-ordered free module. -/
def leadingBasis [WellFoundedLT ι] : Basis (LeadingIndex N) ℤ N :=
  Basis.mk (leadingFamily_linearIndependent N) (leadingFamily_span_eq_top N).ge

end LocalFree

/-- An arbitrary submodule of an integral finitely-supported function module is free. -/
theorem finsupp_submodule_free_int {ι : Type*} (N : Submodule ℤ (ι →₀ ℤ)) :
    @Module.Free ℤ N _ _ N.module := by
  obtain ⟨horder, hwf⟩ := exists_wellFoundedLT ι
  let := horder
  let := hwf
  exact Module.Free.of_basis (LocalFree.leadingBasis N)

/-- Every submodule of a free integral module is free, without a rank bound. -/
theorem submodule_free_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] (N : Submodule ℤ M) : @Module.Free ℤ N _ _ N.module := by
  cases Subsingleton.elim ‹Module ℤ M› (AddCommGroup.toIntModule M)
  let b := Module.Free.chooseBasis ℤ M
  let : Module.Free ℤ (N.map b.repr.toLinearMap) :=
    finsupp_submodule_free_int (N.map b.repr.toLinearMap)
  exact Module.Free.of_equiv (b.repr.submoduleMap N).symm

/-- Every submodule of a free integral module is projective, without a rank bound. -/
theorem submodule_projective_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] (N : Submodule ℤ M) : @Module.Projective ℤ _ N _ N.module := by
  let := submodule_free_int N
  infer_instance

end Wikipedia.HopfProblem.SingularCohomologyFreeEvaluation
