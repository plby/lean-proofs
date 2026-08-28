import Wikipedia.HopfProblem.PeriodTorusThetaBasic
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Holomorphic factors of automorphy for the actual period lattices

A factor assigns a nonzero scalar to every lattice translation and point
of the covering vector space. Its cocycle law is the law for the actual
action `(z,c) ↦ (z+l, factor l z * c)`. The following files construct this
data from integral type-`(1,1)` forms and use the action to construct the
quotient line bundle; no bundle or section correspondence is a field here.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

/-- Genuine analytic factors for translation by the actual lattice. -/
structure FactorOfAutomorphy (p : PeriodDomain) where
  factor : p.lattice → ComplexPlane₂ → ℂˣ
  factor_zero : ∀ z, factor 0 z = 1
  factor_add : ∀ l m z, factor (l + m) z = factor l (z + m) * factor m z
  holomorphic_factor : ∀ l, ContDiff ℂ ω (fun z => (factor l z : ℂ))

namespace FactorOfAutomorphy

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

@[simp] theorem factor_zero_coe (z : ComplexPlane₂) :
    (F.factor 0 z : ℂ) = 1 := by rw [F.factor_zero]; rfl

theorem factor_ne_zero (l : p.lattice) (z : ComplexPlane₂) :
    (F.factor l z : ℂ) ≠ 0 := (F.factor l z).ne_zero

theorem factor_add_coe (l m : p.lattice) (z : ComplexPlane₂) :
    (F.factor (l + m) z : ℂ) = (F.factor l (z + m) : ℂ) * (F.factor m z : ℂ) :=
  congrArg Units.val (F.factor_add l m z)

theorem factor_neg_add (l : p.lattice) (z : ComplexPlane₂) :
    F.factor (-l) (z + l) = (F.factor l z)⁻¹ := by
  have h := F.factor_add (-l) l z
  rw [neg_add_cancel, F.factor_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem factor_add_neg (l : p.lattice) (z : ComplexPlane₂) :
    F.factor l (z - l) = (F.factor (-l) z)⁻¹ := by
  simpa only [neg_neg, Submodule.coe_neg, sub_eq_add_neg] using F.factor_neg_add (-l) z

theorem continuous_factor (l : p.lattice) : Continuous (fun z => (F.factor l z : ℂ)) :=
  (F.holomorphic_factor l).continuous

end FactorOfAutomorphy

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
