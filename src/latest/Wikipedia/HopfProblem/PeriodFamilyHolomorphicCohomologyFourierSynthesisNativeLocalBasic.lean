import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeFamilyBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroBasic

/-!
# Literal local scalar values on the original total-space open

A smaller ambient base open determines its literal open in the original
base and the original full inverse image under the family projection.
The ambient scalar is extended by zero only to name a function. All
regularity will be proved solely on this full inverse image, with no
claim about its boundary or the complementary base points.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local

open FourierParameter PeriodTorusLineBundleClassification
open PeriodFamilyHigherDirectImage

/-- The actual smaller ambient open, viewed as an open of the original base. -/
def baseOpen (U V : Opens ℂ) : Opens U :=
  ⟨(Subtype.val : U → ℂ) ⁻¹' (V : Set ℂ), V.isOpen.preimage continuous_subtype_val⟩

@[simp] theorem mem_baseOpen (U V : Opens ℂ) (b : U) :
    b ∈ baseOpen U V ↔ (b : ℂ) ∈ V := Iff.rfl

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The original full total-space inverse image, with its unchanged topology and open atlas. -/
abbrev preimageOpen (V : Opens ℂ) : Opens P.TotalSpace :=
  Zero.basePreimage P (baseOpen U V)

@[simp] theorem mem_preimageOpen (V : Opens ℂ) (x : P.TotalSpace) :
    x ∈ preimageOpen P V ↔ (x.1 : ℂ) ∈ V := Iff.rfl

/-- The original covering preimage is exactly the smaller-base part of the original vector cover. -/
theorem quotientMap_preimage (V : Opens ℂ) :
    P.quotientMap ⁻¹' (preimageOpen P V : Set P.TotalSpace) =
      {q : U × ComplexPlane₂ | (q.1 : ℂ) ∈ V} := rfl

/-- Ambient notation for the local scalar; no smoothness outside the smaller base is asserted. -/
def ambientScalar (f : SmoothFamily V (Fin 4)) (x : P.TotalSpace) : ℂ :=
  ambientValue f ((x.1 : ℂ), unitTorusMark x.2)

/-- On the original inverse image this is exactly the given smaller-base family. -/
theorem ambientScalar_apply (f : SmoothFamily V (Fin 4)) (x : P.TotalSpace)
    (hx : x ∈ preimageOpen P V) :
    ambientScalar P f x = f (⟨(x.1 : ℂ), hx⟩, unitTorusMark x.2) :=
  ambientValue_apply f (⟨(x.1 : ℂ), hx⟩ : V) (unitTorusMark x.2)

/-- The covering identity holds for the ambient notation as well, without a regularity claim. -/
theorem ambientScalar_quotientMap (f : SmoothFamily V (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    ambientScalar P f (P.quotientMap (b, z)) =
      ambientValue f ((b : ℂ), torusQuotient ((P.periodEquiv b).symm z)) := by
  change ambientValue f
    ((b : ℂ), unitTorusMark (standardLattice.mkQ ((P.periodEquiv b).symm z))) = _
  rw [unitTorusMark_mkQ]

/-- An actual point of the original total-space inverse image,
represented on its original cover. -/
def coverPoint (hVU : V ≤ U) (b : V) (z : ComplexPlane₂) : preimageOpen P V :=
  ⟨P.quotientMap (Set.inclusion hVU b, z), b.property⟩

@[simp] theorem coverPoint_val (hVU : V ≤ U) (b : V) (z : ComplexPlane₂) :
    (coverPoint P hVU b z : P.TotalSpace) = P.quotientMap (Set.inclusion hVU b, z) := rfl

/-- The original smaller-base covering formula uses the original period map
at the included point. -/
theorem ambientScalar_coverPoint (hVU : V ≤ U) (f : SmoothFamily V (Fin 4))
    (b : V) (z : ComplexPlane₂) :
    ambientScalar P f (coverPoint P hVU b z) =
      f (b, torusQuotient ((P.periodEquiv (Set.inclusion hVU b)).symm z)) := by
  rw [coverPoint_val, ambientScalar_quotientMap]
  exact ambientValue_apply f b _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local
