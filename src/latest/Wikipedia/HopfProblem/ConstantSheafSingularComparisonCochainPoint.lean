import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Additive singular cochains of a point

Evaluation on the unique singular simplex identifies every cochain group
of `Unit` with the given coefficient group.  The native coboundary then
alternates between zero and the identity.  This proves exactness in every
positive degree directly on the original singular cochains.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

/-- The unique singular simplex of a point in each degree. -/
def pointSimplex (n : ℕ) : SingularSimplex Unit n :=
  ContinuousMap.const _ ()

/-- Evaluation on the unique actual singular simplex. -/
def pointCochainEquiv (A : AddCommGrpCat.{0}) (n : ℕ) : Cochains Unit A n ≃+ A where
  toFun φ := φ (simplexChain Unit n (pointSimplex n))
  invFun a := cochainFromValues Unit A n (fun _ => a)
  left_inv φ := by
    apply cochain_ext Unit A n
    intro σ
    rw [cochainFromValues_simplex]
    exact congrArg (fun τ => φ (simplexChain Unit n τ)) (Subsingleton.elim _ _)
  right_inv a := cochainFromValues_simplex Unit A n (fun _ => a) (pointSimplex n)
  map_add' _ _ := rfl

@[simp]
theorem pointCochainEquiv_apply (A : AddCommGrpCat.{0}) (n : ℕ)
    (φ : Cochains Unit A n) :
    pointCochainEquiv A n φ = φ (simplexChain Unit n (pointSimplex n)) := rfl

/-- Every actual singular simplex has the same cochain value. -/
theorem pointCochain_simplex (A : AddCommGrpCat.{0}) (n : ℕ)
    (φ : Cochains Unit A n) (σ : SingularSimplex Unit n) :
    φ (simplexChain Unit n σ) = pointCochainEquiv A n φ := by
  exact congrArg (fun τ => φ (simplexChain Unit n τ)) (Subsingleton.elim _ _)

/-- In these literal simplex coordinates, the coboundary is zero in
even degrees and the identity in odd degrees. -/
theorem pointCochain_d_value (A : AddCommGrpCat.{0}) (n : ℕ)
    (φ : Cochains Unit A n) :
    pointCochainEquiv A (n + 1) ((singularCochainComplex Unit A).d n (n + 1) φ) =
      if Even n then 0 else pointCochainEquiv A n φ := by
  rw [pointCochainEquiv_apply, singularCochainComplex_d_simplex]
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • pointCochainEquiv A n φ) = _
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
  by_cases hn : Even n
  · simp [Nat.even_add, hn]
  · simp [Nat.even_add, hn]

/-- Every positive-degree closed cochain on the point is an actual
coboundary, with arbitrary abelian coefficients. -/
theorem point_closed_exact (A : AddCommGrpCat.{0}) (n : ℕ)
    (φ : Cochains Unit A (n + 1))
    (hφ : (singularCochainComplex Unit A).d (n + 1) (n + 2) φ = 0) :
    ∃ ψ : Cochains Unit A n, (singularCochainComplex Unit A).d n (n + 1) ψ = φ := by
  by_cases hn : Even n
  · have hv : pointCochainEquiv A (n + 1) φ = 0 := by
      have h := congrArg (pointCochainEquiv A (n + 2)) hφ
      rw [pointCochain_d_value] at h
      simpa only [Nat.even_add_one, hn, not_true_eq_false, if_false, map_zero] using h
    refine ⟨0, ?_⟩
    apply (pointCochainEquiv A (n + 1)).injective
    simpa only [map_zero] using hv.symm
  · refine ⟨(pointCochainEquiv A n).symm (pointCochainEquiv A (n + 1) φ), ?_⟩
    apply (pointCochainEquiv A (n + 1)).injective
    rw [pointCochain_d_value, if_neg hn, AddEquiv.apply_symm_apply]

/-- The original coefficient-general singular cochain complex of the
point is exact in every positive degree. -/
theorem pointCochain_exactAt (A : AddCommGrpCat.{0}) (n : ℕ) :
    (singularCochainComplex Unit A).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (by simp) (by simp [Nat.add_assoc]), ShortComplex.ab_exact_iff]
  exact point_closed_exact A n

/-- Positive cohomology vanishes for the actual native cochain complex,
not for a replacement rank model. -/
theorem point_cohomology_isZero (A : AddCommGrpCat.{0}) (n : ℕ) :
    IsZero ((singularCochainComplex Unit A).homology (n + 1)) :=
  (pointCochain_exactAt A n).isZero_homology

theorem point_cohomology_subsingleton (A : AddCommGrpCat.{0}) (n : ℕ) :
    Subsingleton ((singularCochainComplex Unit A).homology (n + 1)) :=
  AddCommGrpCat.subsingleton_of_isZero (point_cohomology_isZero A n)

/-- Every degree-zero cochain on the point is closed. -/
theorem point_zero_closed (A : AddCommGrpCat.{0}) (φ : Cochains Unit A 0) :
    (singularCochainComplex Unit A).d 0 1 φ = 0 := by
  apply (pointCochainEquiv A 1).injective
  rw [pointCochain_d_value]
  simp

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
