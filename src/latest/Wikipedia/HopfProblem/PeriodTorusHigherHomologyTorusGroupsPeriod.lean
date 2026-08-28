import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroups

/-!
# Actual higher singular homology groups of the period tori

The proved homeomorphisms with the product of four circles transport the
all-degree group calculation to the actual real lattice quotient and the
actual complex period tori. In particular their second and third integral
singular homology groups are respectively free of ranks six and four.

The coordinates retain their recursive Mayer--Vietoris meaning. An
identification with the exterior-power marking is not asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic SingularMayerVietoris

/-- All-degree actual singular homology of the real four-dimensional lattice torus. -/
def realTorusHomologyEquiv (n : ℕ) :
    SingularHomology RealTorus₄ n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv flatTorusCircleHomeomorph n).trans (productTorusHomologyEquiv 4 n)

/-- All-degree actual singular homology of a complex period torus. -/
def periodTorusHomologyEquiv (p : PeriodDomain) (n : ℕ) :
    SingularHomology p.Torus n ≃ₗ[ℤ] binomialModule 4 n :=
  (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) n).trans
    (productTorusHomologyEquiv 4 n)

@[simp] theorem realTorusHomologyEquiv_apply (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    realTorusHomologyEquiv n a = productTorusHomologyEquiv 4 n
      (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a) := rfl

@[simp] theorem periodTorusHomologyEquiv_apply (p : PeriodDomain) (n : ℕ)
    (a : SingularHomology p.Torus n) :
    periodTorusHomologyEquiv p n a = productTorusHomologyEquiv 4 n
      (singularHomologyMap (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) n a) := rfl

theorem realTorus_homology_free (n : ℕ) : Module.Free ℤ (SingularHomology RealTorus₄ n) :=
  Module.Free.of_equiv (realTorusHomologyEquiv n).symm

theorem realTorus_homology_finite (n : ℕ) : Module.Finite ℤ (SingularHomology RealTorus₄ n) :=
  Module.Finite.of_surjective (realTorusHomologyEquiv n).symm.toLinearMap
    (realTorusHomologyEquiv n).symm.surjective

theorem realTorus_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology RealTorus₄ n) = Nat.choose 4 n := by
  rw [(realTorusHomologyEquiv n).finrank_eq]
  exact binomialModule_finrank 4 n

theorem realTorus_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology RealTorus₄ n) := by
  let := realTorus_homology_free n
  infer_instance

theorem realTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology RealTorus₄ n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (realTorusHomologyEquiv n).injective.subsingleton

theorem realTorus_homology_isZero_of_lt {n : ℕ} (hn : 4 < n) :
    IsZero (SingularHomology RealTorus₄ n) := by
  let := realTorus_homology_subsingleton_of_lt hn
  exact ModuleCat.isZero_of_subsingleton _

theorem periodTorus_homology_free (p : PeriodDomain) (n : ℕ) :
    Module.Free ℤ (SingularHomology p.Torus n) :=
  Module.Free.of_equiv (periodTorusHomologyEquiv p n).symm

theorem periodTorus_homology_finite (p : PeriodDomain) (n : ℕ) :
    Module.Finite ℤ (SingularHomology p.Torus n) :=
  Module.Finite.of_surjective (periodTorusHomologyEquiv p n).symm.toLinearMap
    (periodTorusHomologyEquiv p n).symm.surjective

theorem periodTorus_homology_finrank (p : PeriodDomain) (n : ℕ) :
    Module.finrank ℤ (SingularHomology p.Torus n) = Nat.choose 4 n := by
  rw [(periodTorusHomologyEquiv p n).finrank_eq]
  exact binomialModule_finrank 4 n

theorem periodTorus_homology_torsionFree (p : PeriodDomain) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology p.Torus n) := by
  let := periodTorus_homology_free p n
  infer_instance

theorem periodTorus_homology_subsingleton_of_lt (p : PeriodDomain) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology p.Torus n) := by
  let := binomialModule_subsingleton_of_lt hn
  exact (periodTorusHomologyEquiv p n).injective.subsingleton

theorem periodTorus_homology_isZero_of_lt (p : PeriodDomain) {n : ℕ} (hn : 4 < n) :
    IsZero (SingularHomology p.Torus n) := by
  let := periodTorus_homology_subsingleton_of_lt p hn
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual second integral singular homology of the real torus. -/
abbrev realTorusH2Equiv : SingularHomology RealTorus₄ 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  realTorusHomologyEquiv 2

/-- The actual third integral singular homology of the real torus. -/
abbrev realTorusH3Equiv : SingularHomology RealTorus₄ 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  realTorusHomologyEquiv 3

/-- The actual second integral singular homology of every complex period torus. -/
abbrev periodTorusH2Equiv (p : PeriodDomain) : SingularHomology p.Torus 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  periodTorusHomologyEquiv p 2

/-- The actual third integral singular homology of every complex period torus. -/
abbrev periodTorusH3Equiv (p : PeriodDomain) : SingularHomology p.Torus 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  periodTorusHomologyEquiv p 3

/-- The actual top-degree integral singular homology of the real torus. -/
def realTorusH4Equiv : SingularHomology RealTorus₄ 4 ≃ₗ[ℤ] ℤ :=
  (realTorusHomologyEquiv 4).trans (integerBinomialZeroEquiv 4).symm

/-- The actual top-degree integral singular homology of every complex period torus. -/
def periodTorusH4Equiv (p : PeriodDomain) : SingularHomology p.Torus 4 ≃ₗ[ℤ] ℤ :=
  (periodTorusHomologyEquiv p 4).trans (integerBinomialZeroEquiv 4).symm

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
