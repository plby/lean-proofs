import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegral
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasic
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Exhaustiveness of the six integral alternating-form coefficients

Every real alternating form on the actual covering tangent space which
is integral on the genuine period lattice is the transport of a unique
integer six-tuple.  The coefficients are recovered from its values on
the six ordered pairs of actual period columns.  This is a statement
about real bilinear forms and the lattice, without a Hodge or
cohomological comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-- Each actual period-basis column belongs to the actual integral lattice. -/
theorem periodBasis_mem_lattice (p : PeriodDomain) (i : Fin 4) :
    p.basis i ∈ p.lattice := by
  rw [p.lattice_eq_span_basis]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The six coefficient positions exhaust the strictly ordered basis pairs. -/
theorem coefficientPair_covers_lt (i j : Fin 4) (hij : i < j) :
    ∃ k : Fin 6, coefficientPair k = (i, j) := by
  have h : ∀ i j : Fin 4, i < j → ∃ k : Fin 6, coefficientPair k = (i, j) := by
    decide
  exact h i j hij

/-- For alternating real forms, the six ordered period-basis pairings
determine all pairings and therefore determine the form. -/
theorem realForm_eq_of_period_basis_pairs (p : PeriodDomain) (B C : RealForm)
    (hB : ∀ x, B x x = 0) (hC : ∀ x, C x x = 0)
    (hpair : ∀ k : Fin 6,
      B (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2) =
      C (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2)) : B = C := by
  have hlt (i j : Fin 4) (hij : i < j) : B (p.basis i) (p.basis j) =
      C (p.basis i) (p.basis j) := by
    obtain ⟨k, hk⟩ := coefficientPair_covers_lt i j hij
    simpa only [hk] using hpair k
  apply LinearMap.ext_basis p.basis p.basis
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · subst j
    rw [hB, hC]
  · rw [realForm_skew B hB (p.basis j) (p.basis i),
      realForm_skew C hC (p.basis j) (p.basis i), hlt j i hij]

/-- Every alternating real form integral on the genuine lattice has one
and only one integral coefficient vector in the prescribed marking. -/
theorem existsUnique_tangentForm_of_integral (p : PeriodDomain) (B : RealForm)
    (hAlt : ∀ x, B x x = 0) (hIntegral : IntegralOnPeriodLattice p B) :
    ∃! E : Fin 6 → ℤ, tangentForm p E = B := by
  have hcoeff (k : Fin 6) : ∃ n : ℤ,
      B (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2) = (n : ℝ) :=
    hIntegral _ (periodBasis_mem_lattice p _) _ (periodBasis_mem_lattice p _)
  choose E hE using hcoeff
  have hform : tangentForm p E = B := by
    apply realForm_eq_of_period_basis_pairs p _ B (tangentForm_self p E) hAlt
    intro k
    rw [tangentForm_basis_pair, hE k]
  refine ⟨E, hform, ?_⟩
  intro F hF
  exact tangentForm_injective p (hF.trans hform.symm)

/-- Intrinsic alternatingness and lattice-integrality are exactly the
conditions for a unique transported integral coefficient form. -/
theorem existsUnique_tangentForm_iff (p : PeriodDomain) (B : RealForm) :
    (∃! E : Fin 6 → ℤ, tangentForm p E = B) ↔
      (∀ x, B x x = 0) ∧ IntegralOnPeriodLattice p B := by
  constructor
  · rintro ⟨E, rfl, _⟩
    exact ⟨tangentForm_self p E, tangentForm_integral p E⟩
  · rintro ⟨hAlt, hIntegral⟩
    exact existsUnique_tangentForm_of_integral p B hAlt hIntegral

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
