import Wikipedia.HopfProblem.EllipticFillingRootSection
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationOrders

/-!
# Reduced elliptic divisor equations on the actual threefold

The local roots on the full cyclic filling are transported through its
original open inclusion. All local equations and transition functions
retain their proved holomorphicity in the original threefold atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ReducedEllipticDivisor

open Elliptic EllipticFilling EllipticGeometry

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace

variable (j : Kind)

local instance rootNativeCharts : ChartedSpace (ℂ × ComplexPlane₂)
    ((specialLocalData j).Space j.twist (mainTwist_admissible j)) :=
  specialFullFillingChartedSpace j

def patch : TopologicalSpace.Opens Space := liftedPatch (some (some j))

def outside : TopologicalSpace.Opens Space :=
  ⟨{x | projectionSphere x ≠ sphereValue j},
    (isClosed_singleton.preimage projectionSphere_continuous).isOpen_compl⟩

theorem mem_outside_or_patch (x : Space) : x ∈ outside j ∨ x ∈ patch j := by
  by_cases hx : projectionSphere x = sphereValue j
  · exact Or.inr (FibreClassification.elliptic_fibre_mem_liftedPatch j x hx)
  · exact Or.inl hx

/-- The inverse of the unchanged open filling parametrization. -/
def localPoint (x : Space) : LocalSpace j := (nativeParametrization j).symm x

def fillingPoint (x : Space) : SpecialFullFilling j := (localPoint j x).val

theorem inclusion_localPoint {x : Space} (hx : x ∈ patch j) :
    EllipticGeometry.inclusion j (localPoint j x) = x := by
  apply (nativeParametrization j).right_inv'
  rw [nativeParametrization_target]
  exact hx

theorem fillingPoint_holomorphicOn :
    ContMDiffOn IF IF ω (fillingPoint j) (patch j) := by
  have h := contMDiff_subtype_val.comp_contMDiffOn (nativeParametrization j).symm.contMDiffOn
  change ContMDiffOn IF IF ω (fillingPoint j) (nativeParametrization j).target at h
  rw [nativeParametrization_target] at h
  exact h

theorem fillingPoint_parameter {x : Space} (hx : x ∈ patch j) :
    (specialFullFillingProjection j (fillingPoint j x) : ℂ) =
      sphereChart j (projectionSphere x) := by
  conv_rhs => rw [← inclusion_localPoint j hx, sphereChart_projectionSphere_inclusion]
  rfl

theorem fillingPoint_parameter_zero_iff {x : Space} (hx : x ∈ patch j) :
    (specialFullFillingProjection j (fillingPoint j x) : ℂ) = 0 ↔
      projectionSphere x = sphereValue j := by
  have h := projectionSphere_inclusion_eq_value_iff j (localPoint j x)
  rw [inclusion_localPoint j hx] at h
  exact h.symm

abbrev fillingData := Equivariant.Data.RootSection.data
  (specialLocalData j) j.twist (mainTwist_admissible j)

local instance fillingData_holomorphic : (fillingData j).IsHolomorphic IF :=
  Equivariant.Data.RootSection.data_isHolomorphic
    (specialLocalData j) j.twist (mainTwist_admissible j)

def chartSet (i : SpecialFullFilling j) : Set Space :=
  (patch j : Set Space) ∩ fillingPoint j ⁻¹' (fillingData j).baseSet i

theorem isOpen_chartSet (i : SpecialFullFilling j) : IsOpen (chartSet j i) :=
  (fillingPoint_holomorphicOn j).continuousOn.isOpen_inter_preimage (patch j).isOpen
    ((fillingData j).isOpen_baseSet i)

theorem mem_chartSet_at {x : Space} (hx : x ∈ patch j) :
    x ∈ chartSet j ((fillingData j).indexAt (fillingPoint j x)) :=
  ⟨hx, (fillingData j).mem_baseSet_at (fillingPoint j x)⟩

def coefficient (i : SpecialFullFilling j) (x : Space) : ℂ :=
  Equivariant.Data.RootSection.coefficient (specialLocalData j) j.twist
    (mainTwist_admissible j) i (fillingPoint j x)

def rootTransition (i k : SpecialFullFilling j) (x : Space) : ℂˣ :=
  (fillingData j).transition i k (fillingPoint j x)

theorem rootTransition_self (i : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i) : rootTransition j i i x = 1 :=
  (fillingData j).transition_self i (fillingPoint j x) hx.2

theorem rootTransition_comp (i k l : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i ∩ chartSet j k ∩ chartSet j l) :
    rootTransition j k l x * rootTransition j i k x = rootTransition j i l x :=
  (fillingData j).transition_comp i k l (fillingPoint j x) ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩

theorem rootTransition_holomorphicOn (i k : SpecialFullFilling j) :
    ContMDiffOn IF 𝓘(ℂ) ω (fun x => (rootTransition j i k x : ℂ))
      (chartSet j i ∩ chartSet j k) :=
  ((fillingData j).transition_holomorphic IF i k).comp
    ((fillingPoint_holomorphicOn j).mono (fun _ hx => hx.1.1))
    (fun _ hx => ⟨hx.1.2, hx.2.2⟩)

theorem coefficient_holomorphicOn (i : SpecialFullFilling j) :
    ContMDiffOn IF 𝓘(ℂ) ω (coefficient j i) (chartSet j i) :=
  (Equivariant.Data.RootSection.coefficient_holomorphic (specialLocalData j)
    j.twist (mainTwist_admissible j) i).comp
      ((fillingPoint_holomorphicOn j).mono inter_subset_left) (fun _ hx => hx.2)

theorem coefficient_change (i k : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i ∩ chartSet j k) :
    (rootTransition j i k x : ℂ) * coefficient j i x = coefficient j k x :=
  Equivariant.Data.RootSection.coefficient_compatible (specialLocalData j) j.twist
    (mainTwist_admissible j) i k (fillingPoint j x) ⟨hx.1.2, hx.2.2⟩

theorem coefficient_pow (i : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i) :
    coefficient j i x ^ j.order = sphereChart j (projectionSphere x) :=
  (Equivariant.Data.RootSection.coefficient_pow (specialLocalData j) j.twist
    (mainTwist_admissible j) i hx.2).trans (fillingPoint_parameter j hx.1)

theorem coefficient_eq_zero_iff (i : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i) :
    coefficient j i x = 0 ↔ projectionSphere x = sphereValue j :=
  (Equivariant.Data.RootSection.coefficient_eq_zero_iff (specialLocalData j) j.twist
    (mainTwist_admissible j) i hx.2).trans (fillingPoint_parameter_zero_iff j hx.1)

theorem coefficient_ne_zero (i : SpecialFullFilling j) {x : Space}
    (hx : x ∈ chartSet j i) (ho : x ∈ outside j) : coefficient j i x ≠ 0 :=
  (coefficient_eq_zero_iff j i hx).not.mpr ho

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ReducedEllipticDivisor
