import Wikipedia.HopfProblem.HolomorphicMeromorphicStalk
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRing

/-!
# Canonical ordinary values of genuine meromorphic functions

At a regular germ the value is evaluation of its unique holomorphic
representative in the original local ring. At a nonregular germ we use
zero as a convention for the ordinary scalar representative. The
meromorphic function itself remains the full fraction-stalk section;
this convention neither identifies distinct germs nor removes poles.

On every local fraction presentation with nonzero denominator value,
the ordinary representative is exactly the actual numerator divided by
the actual denominator.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A fraction germ is regular precisely when it belongs to the
original holomorphic local ring. -/
def RegularAt {U : Opens M} (a : Section I M U) (x : U) : Prop :=
  ∃ p : HolomorphicStalk I M x.val, ofHolomorphicGerm I M x.val p = a x

/-- The ordinary representative, with value zero at nonregular germs.
The underlying meromorphic section always retains its full germ. -/
def value {U : Opens M} (a : Section I M U) (x : U) : ℂ := by
  classical
  exact if h : RegularAt I M a x then
    HolomorphicFunctionSheaf.stalkEval I M x.val (Classical.choose h) else 0

theorem value_eq_of_holomorphicGerm {U : Opens M} (a : Section I M U) (x : U)
    (p : HolomorphicStalk I M x.val) (hp : ofHolomorphicGerm I M x.val p = a x) :
    value I M a x = HolomorphicFunctionSheaf.stalkEval I M x.val p := by
  classical
  have h : RegularAt I M a x := ⟨p, hp⟩
  have he : Classical.choose h = p :=
    ofHolomorphicGerm_injective I M x.val ((Classical.choose_spec h).trans hp.symm)
  simp only [value, dif_pos h, he]

@[simp] theorem value_ofHolomorphic (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    value I M (ofHolomorphic I M U f) x = f x := by
  have he : ofHolomorphicGerm I M x.val (holomorphicGerm I M U x f) =
      ofHolomorphic I M U f x := (ofHolomorphic_apply I M U f x).symm
  exact (value_eq_of_holomorphicGerm I M _ x _ he).trans
    (HolomorphicFunctionSheaf.stalkEval_germ I M U x.val x.property f)

/-- A local denominator with nonzero value is a unit of the actual
holomorphic local ring, so the fraction is a genuine holomorphic germ. -/
theorem exists_holomorphic_fraction_of_denominator_value_ne_zero (x : M)
    (p q : HolomorphicStalk I M x)
    (hq : HolomorphicFunctionSheaf.stalkEval I M x q ≠ 0) :
    ∃ r : HolomorphicStalk I M x,
      ofHolomorphicGerm I M x r = ofHolomorphicGerm I M x p / ofHolomorphicGerm I M x q ∧
      HolomorphicFunctionSheaf.stalkEval I M x r =
        HolomorphicFunctionSheaf.stalkEval I M x p /
          HolomorphicFunctionSheaf.stalkEval I M x q := by
  obtain ⟨u, hu⟩ := (HolomorphicFunctionSheaf.isUnit_stalk_iff I M x q).mpr hq
  refine ⟨p * ↑(u⁻¹), ?_, ?_⟩
  · rw [map_mul, map_units_inv, hu, div_eq_mul_inv]
  · rw [map_mul, map_units_inv, hu, div_eq_mul_inv]

theorem value_eq_fraction_of_denominator_value_ne_zero {U : Opens M}
    (a : Section I M U) (x : U) (p q : HolomorphicStalk I M x.val)
    (ha : a x = ofHolomorphicGerm I M x.val p / ofHolomorphicGerm I M x.val q)
    (hq : HolomorphicFunctionSheaf.stalkEval I M x.val q ≠ 0) :
    value I M a x = HolomorphicFunctionSheaf.stalkEval I M x.val p /
      HolomorphicFunctionSheaf.stalkEval I M x.val q := by
  obtain ⟨r, hr, hre⟩ := exists_holomorphic_fraction_of_denominator_value_ne_zero I M x.val p q hq
  exact (value_eq_of_holomorphicGerm I M a x r (hr.trans ha.symm)).trans hre

/-- Exact ordinary values on the cozero locus of any genuine local
denominator, even when the meromorphic function has poles elsewhere. -/
theorem value_eq_local_fraction {U V : Opens M} (a : Section I M U)
    (p q : HolomorphicFunctionSheaf.Section I M V) (x : M) (hxU : x ∈ U) (hxV : x ∈ V)
    (ha : a ⟨x, hxU⟩ = fraction I M V p q ⟨x, hxV⟩) (hq : q ⟨x, hxV⟩ ≠ 0) :
    value I M a ⟨x, hxU⟩ = p ⟨x, hxV⟩ / q ⟨x, hxV⟩ := by
  have hpv : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M V ⟨x, hxV⟩ p) = p ⟨x, hxV⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M V x hxV p
  have hqv : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M V ⟨x, hxV⟩ q) = q ⟨x, hxV⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M V x hxV q
  have hqg : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M V ⟨x, hxV⟩ q) ≠ 0 := fun h => hq (hqv.symm.trans h)
  have he := value_eq_fraction_of_denominator_value_ne_zero I M a ⟨x, hxU⟩
    (holomorphicGerm I M V ⟨x, hxV⟩ p) (holomorphicGerm I M V ⟨x, hxV⟩ q) ha hqg
  exact he.trans (congrArg₂ HDiv.hDiv hpv hqv)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
