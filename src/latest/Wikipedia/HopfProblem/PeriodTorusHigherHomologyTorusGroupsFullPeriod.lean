import Wikipedia.HopfProblem.PeriodTorusHigherHomologyFullPeriodTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups

/-!
# Actual integral homology of arbitrary full period tori

The actual homeomorphism from a full period torus to four circles transports
the proved all-degree singular homology calculation. No special form of the
full period matrix is required: the groups are free of binomial rank and
vanish above degree four.

The coordinates are the recursive Mayer--Vietoris coordinates of the circle
product calculation. This file does not identify them with an exterior-power
marking or assert naturality for changes of period matrix.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open PeriodTorusHigherHomology SingularMayerVietoris

variable (p : FullPeriodMatrix)

/-- The actual integral singular homology of any full complex period torus
is the free integral module of binomial rank in every degree. -/
def singularHomologyEquiv (n : ℕ) :
    SingularHomology p.Torus n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv p.productTorusHomeomorph n).trans
    (productTorusHomologyEquiv 4 n)

/-- The coordinate equivalence uses the actual homology map induced by the
proved period-torus homeomorphism. -/
@[simp] theorem singularHomologyEquiv_apply (n : ℕ) (a : SingularHomology p.Torus n) :
    p.singularHomologyEquiv n a = productTorusHomologyEquiv 4 n
      (singularHomologyMap (p.productTorusHomeomorph : C(p.Torus, ProductTorus 4)) n a) :=
  rfl

/-- The actual singular homology modules of every full period torus are free. -/
theorem singularHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology p.Torus n) :=
  Module.Free.of_equiv (p.singularHomologyEquiv n).symm

/-- The actual singular homology modules of every full period torus are
finitely generated over the integers. -/
theorem singularHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology p.Torus n) :=
  Module.Finite.of_surjective (p.singularHomologyEquiv n).symm.toLinearMap
    (p.singularHomologyEquiv n).symm.surjective

/-- The integral Betti numbers of an arbitrary full period torus. -/
theorem singularHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology p.Torus n) = Nat.choose 4 n := by
  rw [(p.singularHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 4 n

/-- There is no integral homology torsion for any full period matrix. -/
theorem singularHomology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology p.Torus n) := by
  let := p.singularHomology_free n
  infer_instance

/-- Above degree four the actual singular homology has a single element. -/
theorem singularHomology_subsingleton_of_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology p.Torus n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (p.singularHomologyEquiv n).injective.subsingleton

/-- The actual singular homology object is zero above degree four. -/
theorem singularHomology_isZero_of_lt {n : ℕ} (hn : 4 < n) :
    IsZero (SingularHomology p.Torus n) := by
  let := p.singularHomology_subsingleton_of_lt hn
  exact ModuleCat.isZero_of_subsingleton _

/-- Every actual singular homology class above degree four is zero. -/
theorem singularHomology_eq_zero_of_lt {n : ℕ} (hn : 4 < n)
    (a : SingularHomology p.Torus n) : a = 0 :=
  @Subsingleton.elim (SingularHomology p.Torus n)
    (p.singularHomology_subsingleton_of_lt hn) a 0

/-- The actual second integral singular homology of an arbitrary full
period torus is free of rank six. -/
abbrev singularH2Equiv : SingularHomology p.Torus 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  p.singularHomologyEquiv 2

/-- The actual third integral singular homology of an arbitrary full
period torus is free of rank four. -/
abbrev singularH3Equiv : SingularHomology p.Torus 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  p.singularHomologyEquiv 3

/-- The actual fourth integral singular homology of an arbitrary full
period torus is infinite cyclic. -/
def singularH4Equiv : SingularHomology p.Torus 4 ≃ₗ[ℤ] ℤ :=
  (p.singularHomologyEquiv 4).trans (integerBinomialZeroEquiv 4).symm

end Wikipedia.HopfProblem.FullPeriodMatrix
