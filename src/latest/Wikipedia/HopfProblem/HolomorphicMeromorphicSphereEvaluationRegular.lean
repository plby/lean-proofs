import Wikipedia.HopfProblem.HolomorphicMeromorphicField
import Wikipedia.HopfProblem.HolomorphicMeromorphicValue

/-!
# Native ordinary values at regular meromorphic germs

At a regular germ the ordinary value is the evaluation of its unique
representative in the actual holomorphic local ring.  Its addition,
multiplication, and negation are consequently compatible with native
section arithmetic at regular points.  A regular germ of nonzero value
is a unit of that local ring, so its reciprocal has the expected value
as well.  No sphere coordinates or rational-function presentations are
used in these local assertions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M] (U : Opens M)

/-- Addition of native sections has the expected ordinary value at a
point where both input germs are regular. -/
theorem value_add_of_regularAt (s t : Section I M U) (x : U)
    (hs : RegularAt I M s x) (ht : RegularAt I M t x) :
    value I M (s + t) x = value I M s x + value I M t x := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  have hsum : ofHolomorphicGerm I M x.val (p + q) = (s + t) x := by
    rw [map_add, hp, hq, section_add_apply]
  rw [value_eq_of_holomorphicGerm I M (s + t) x (p + q) hsum,
    value_eq_of_holomorphicGerm I M s x p hp,
    value_eq_of_holomorphicGerm I M t x q hq, map_add]

/-- Multiplication of native sections has the expected ordinary value
at a point where both input germs are regular. -/
theorem value_mul_of_regularAt (s t : Section I M U) (x : U)
    (hs : RegularAt I M s x) (ht : RegularAt I M t x) :
    value I M (s * t) x = value I M s x * value I M t x := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  have hprod : ofHolomorphicGerm I M x.val (p * q) = (s * t) x := by
    rw [map_mul, hp, hq, section_mul_apply]
  rw [value_eq_of_holomorphicGerm I M (s * t) x (p * q) hprod,
    value_eq_of_holomorphicGerm I M s x p hp,
    value_eq_of_holomorphicGerm I M t x q hq, map_mul]

/-- Negation is compatible with ordinary value at a regular germ. -/
theorem value_neg_of_regularAt (s : Section I M U) (x : U)
    (hs : RegularAt I M s x) : value I M (-s) x = -value I M s x := by
  obtain ⟨p, hp⟩ := hs
  have hneg : ofHolomorphicGerm I M x.val (-p) = (-s) x := by
    rw [map_neg, hp, section_neg_apply]
  rw [value_eq_of_holomorphicGerm I M (-s) x (-p) hneg,
    value_eq_of_holomorphicGerm I M s x p hp, map_neg]

/-- The native zero section has ordinary value zero everywhere. -/
@[simp] theorem value_zero (x : U) : value I M (0 : Section I M U) x = 0 := by
  have hzero : ofHolomorphicGerm I M x.val 0 = (0 : Section I M U) x := by
    rw [map_zero, section_zero_apply]
  rw [value_eq_of_holomorphicGerm I M (0 : Section I M U) x 0 hzero, map_zero]

/-- The native unit section has ordinary value one everywhere. -/
@[simp] theorem value_one (x : U) : value I M (1 : Section I M U) x = 1 := by
  have hone : ofHolomorphicGerm I M x.val 1 = (1 : Section I M U) x := by
    rw [map_one, section_one_apply]
  rw [value_eq_of_holomorphicGerm I M (1 : Section I M U) x 1 hone, map_one]

/-- Native complex constants evaluate to their actual constant value. -/
@[simp] theorem value_algebraMap (c : ℂ) (x : U) :
    value I M (algebraMap ℂ (Section I M U) c) x = c := by
  rw [algebraMap_section, value_ofHolomorphic]
  rfl

/-- The actual inverse section has reciprocal ordinary value whenever
the original germ is regular and its ordinary value is nonzero. -/
theorem value_inv_of_regularAt_ne_zero [ConnectedSpace U]
    (s : Section I M U) (x : U) (hs : RegularAt I M s x)
    (hvalue : value I M s x ≠ 0) :
    value I M s⁻¹ x = (value I M s x)⁻¹ := by
  obtain ⟨p, hp⟩ := hs
  have hv : value I M s x = HolomorphicFunctionSheaf.stalkEval I M x.val p :=
    value_eq_of_holomorphicGerm I M s x p hp
  have hpvalue : HolomorphicFunctionSheaf.stalkEval I M x.val p ≠ 0 := by
    rwa [← hv]
  obtain ⟨u, hu⟩ := (HolomorphicFunctionSheaf.isUnit_stalk_iff I M x.val p).mpr hpvalue
  have hinv : ofHolomorphicGerm I M x.val (↑(u⁻¹)) = (s⁻¹) x := by
    rw [map_units_inv, hu, hp, section_inv_apply]
  rw [value_eq_of_holomorphicGerm I M s⁻¹ x (↑(u⁻¹)) hinv,
    map_units_inv, hu, ← hv]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation
