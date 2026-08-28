import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Cartier presentations by actual holomorphic fractions

The data here include holomorphic numerators and denominators on an open
cover, a dense open set on which they are nonzero, and holomorphic unit
transition functions.  The cross-multiplication identity is required on
the entire overlap, including its zeros and poles.  Thus the associated
line is the actual analytic `VectorBundleCore` of the unit cocycle, not a
line assigned a divisor name.

The local fractions glue to a genuine nonvanishing holomorphic section
on the specified dense open set.  No support or multiplicity is assigned
merely from a numerator: those require separate local factorization
theorems for the particular presentation.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobal

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H]

structure CartierData (I : ModelWithCorners ℂ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (ι : Type*) where
  transitions : HolomorphicCharacterBundle.TransitionData M ι
  isHolomorphic : transitions.IsHolomorphic I
  numerator : ι → M → ℂ
  denominator : ι → M → ℂ
  numerator_holomorphic : ∀ i, ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
    (numerator i) (transitions.baseSet i)
  denominator_holomorphic : ∀ i, ContMDiffOn I (modelWithCornersSelf ℂ ℂ) ω
    (denominator i) (transitions.baseSet i)
  genericSet : TopologicalSpace.Opens M
  genericSet_dense : Dense (genericSet : Set M)
  numerator_ne_zero : ∀ i x, x ∈ transitions.baseSet i → x ∈ genericSet →
    numerator i x ≠ 0
  denominator_ne_zero : ∀ i x, x ∈ transitions.baseSet i → x ∈ genericSet →
    denominator i x ≠ 0
  ratio : ∀ i j x, x ∈ transitions.baseSet i ∩ transitions.baseSet j →
    numerator j x * denominator i x =
      (transitions.transition i j x : ℂ) * numerator i x * denominator j x

namespace CartierData

variable {I : ModelWithCorners ℂ E H} {M ι : Type*}
  [TopologicalSpace M] [ChartedSpace H M] (D : CartierData I M ι)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

instance transitions_isHolomorphic : D.transitions.IsHolomorphic I := D.isHolomorphic

/-- The analytic line bundle associated to the actual unit cocycle. -/
abbrev associatedBundle : VectorBundleCore ℂ M ℂ ι := D.transitions.core

theorem associatedBundle_contMDiffVectorBundle :
    ContMDiffVectorBundle ω ℂ D.associatedBundle.Fiber I := inferInstance

def localFraction (i : ι) (x : M) : ℂ := D.numerator i x / D.denominator i x

theorem localFraction_ne_zero (i : ι) {x : M}
    (hi : x ∈ D.transitions.baseSet i) (hx : x ∈ D.genericSet) :
    D.localFraction i x ≠ 0 :=
  div_ne_zero (D.numerator_ne_zero i x hi hx) (D.denominator_ne_zero i x hi hx)

theorem localFraction_transition (i j : ι) {x : M}
    (hij : x ∈ D.transitions.baseSet i ∩ D.transitions.baseSet j)
    (hx : x ∈ D.genericSet) :
    (D.transitions.transition i j x : ℂ) * D.localFraction i x =
      D.localFraction j x := by
  change (D.transitions.transition i j x : ℂ) *
      (D.numerator i x / D.denominator i x) = D.numerator j x / D.denominator j x
  rw [← mul_div_assoc]
  exact (div_eq_div_iff (D.denominator_ne_zero i x hij.1 hx)
    (D.denominator_ne_zero j x hij.2 hx)).2 (D.ratio i j x hij).symm

/-- The selected local fraction.  Only its restriction to `genericSet`
is asserted to be a holomorphic, nonzero section. -/
def rawSection (x : M) : D.associatedBundle.Fiber x :=
  D.localFraction (D.transitions.indexAt x) x

def rawSectionMap (x : M) : D.associatedBundle.TotalSpace := ⟨x, D.rawSection x⟩

theorem rawSection_ne_zero {x : M} (hx : x ∈ D.genericSet) : D.rawSection x ≠ 0 :=
  D.localFraction_ne_zero _ (D.transitions.mem_baseSet_at x) hx

theorem rawSection_localCoefficient (i : ι) {x : M}
    (hi : x ∈ D.transitions.baseSet i) (hx : x ∈ D.genericSet) :
    D.transitions.localCoefficient D.rawSection i x = D.localFraction i x :=
  D.localFraction_transition (D.transitions.indexAt x) i
    ⟨D.transitions.mem_baseSet_at x, hi⟩ hx

theorem localFraction_holomorphicAt (i : ι) {x : M}
    (hi : x ∈ D.transitions.baseSet i) (hx : x ∈ D.genericSet) :
    ContMDiffAt I I₁ ω (D.localFraction i) x := by
  have hUi := (D.transitions.isOpen_baseSet i).mem_nhds hi
  exact ((D.numerator_holomorphic i).contMDiffAt hUi).div₀
    ((D.denominator_holomorphic i).contMDiffAt hUi) (D.denominator_ne_zero i x hi hx)

theorem rawSectionMap_holomorphicAt {x : M} (hx : x ∈ D.genericSet) :
    ContMDiffAt I (I.prod I₁) ω D.rawSectionMap x := by
  change ContMDiffAt I (I.prod I₁) ω
    (fun x => (⟨x, D.rawSection x⟩ : D.associatedBundle.TotalSpace)) x
  rw [Bundle.contMDiffAt_section]
  have hUi := (D.transitions.isOpen_baseSet (D.transitions.indexAt x)).mem_nhds
    (D.transitions.mem_baseSet_at x)
  have hG := D.genericSet.isOpen.mem_nhds hx
  apply (D.localFraction_holomorphicAt _ (D.transitions.mem_baseSet_at x) hx).congr_of_eventuallyEq
  filter_upwards [hUi, hG] with y hiy hy
  exact D.rawSection_localCoefficient _ hiy hy

theorem rawSectionMap_holomorphicOn :
    ContMDiffOn I (I.prod I₁) ω D.rawSectionMap D.genericSet :=
  fun _ hx => (D.rawSectionMap_holomorphicAt hx).contMDiffWithinAt

end CartierData

end Wikipedia.HopfProblem.CanonicalGlobal
