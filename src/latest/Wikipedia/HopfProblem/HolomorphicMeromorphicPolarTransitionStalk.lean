import Wikipedia.HopfProblem.HolomorphicMeromorphicValue
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Ratios of associated native holomorphic germs

Two associated nonzero germs have a ratio given by a unit of the original
holomorphic stalk. For actual local holomorphic sections, this makes their
fraction regular at every point, with nonzero ordinary value there.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- The ratio of associated germs is the image of a unit in the actual
categorical holomorphic stalk. -/
theorem exists_unit_fraction (x : M) (p q : HolomorphicStalk I M x)
    (hq : q ≠ 0) (hassoc : Associated p q) :
    ∃ u : (HolomorphicStalk I M x)ˣ,
      ofHolomorphicGerm I M x (u : HolomorphicStalk I M x) =
        ofHolomorphicGerm I M x p / ofHolomorphicGerm I M x q := by
  obtain ⟨u, hu⟩ := hassoc.symm
  refine ⟨u, ?_⟩
  have hq' : ofHolomorphicGerm I M x q ≠ 0 :=
    fun h => hq ((ofHolomorphicGerm_eq_zero_iff I M x q).mp h)
  rw [← hu, map_mul, mul_div_cancel_left₀ _ hq']

/-- A genuine fraction with associated numerator and denominator germs
is regular at every point in its original domain. -/
theorem fraction_regularAt_of_associated {U : Opens M}
    (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0)
    (hassoc : ∀ x : U, Associated (holomorphicGerm I M U x p)
      (holomorphicGerm I M U x q)) (x : U) :
    RegularAt I M (ofFraction I M U p q hq) x := by
  obtain ⟨u, hu⟩ := exists_unit_fraction I M x.val
    (holomorphicGerm I M U x p) (holomorphicGerm I M U x q) (hq x) (hassoc x)
  exact ⟨(u : HolomorphicStalk I M x.val), hu⟩

/-- Evaluation of the actual unit germ is nonzero, so the canonical
ordinary value of the regular fraction is nonzero as well. -/
theorem fraction_value_ne_zero_of_associated {U : Opens M}
    (p q : HolomorphicFunctionSheaf.Section I M U)
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0)
    (hassoc : ∀ x : U, Associated (holomorphicGerm I M U x p)
      (holomorphicGerm I M U x q)) (x : U) :
    value I M (ofFraction I M U p q hq) x ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_unit_fraction I M x.val
    (holomorphicGerm I M U x p) (holomorphicGerm I M U x q) (hq x) (hassoc x)
  rw [value_eq_of_holomorphicGerm I M (ofFraction I M U p q hq) x
    (u : HolomorphicStalk I M x.val) hu]
  exact (HolomorphicFunctionSheaf.isUnit_stalk_iff I M x.val _).mp u.isUnit

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition
