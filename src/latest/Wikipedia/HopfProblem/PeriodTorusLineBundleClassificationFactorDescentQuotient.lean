import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentSection
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification

/-!
# Descent of an equivariant native frame through the genuine orbit quotient

The map on representatives is multiplication of the given native frame by
the scalar coordinate. Equivariance proves well-definedness on the actual
diagonal orbit quotient. Its analyticity follows from the actual quotient
covering and from the native frame map, without replacing either atlas.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V]

variable (F : FactorOfAutomorphy p) (s : CoverSection p V)
    (hrel : ∀ (l : p.lattice) (z : ComplexPlane₂) (c : ℂ),
      coverScalarMap s (z + l, (F.factor l z : ℂ) * c) = coverScalarMap s (z, c))

/-- The map `[z,c] ↦ c • s(z)` into the original native total space. -/
def frameQuotientMap : AssociatedSpace F → TotalSpace ℂ V :=
  Quotient.lift (coverScalarMap s) (by
    intro u v huv
    have he : associatedMap F u = associatedMap F v := Quotient.sound huv
    obtain ⟨l, hz, hc⟩ := (associatedMap_eq_iff F u v).mp he
    have hu : u = (v.1 + l, (F.factor l v.1 : ℂ) * v.2) :=
      Prod.ext hz.symm hc.symm
    rw [hu]
    exact hrel l v.1 v.2)

@[simp]
theorem frameQuotientMap_associatedMap (z : ComplexPlane₂) (c : ℂ) :
    frameQuotientMap F s hrel (associatedMap F (z, c)) = coverScalarMap s (z, c) := rfl

@[simp]
theorem frameQuotientMap_preserves_base (u : AssociatedSpace F) :
    (frameQuotientMap F s hrel u).proj = projection F u := by
  obtain ⟨⟨z, c⟩, rfl⟩ := associatedMap_surjective F u
  rfl

variable [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC] in
/-- Analyticity for the original native target and independently constructed
covering-quotient source. -/
theorem frameQuotientMap_contMDiff :
    letI := associatedChartedSpace F
    ContMDiff IP ((IC).prod I₁) ω (frameQuotientMap F s hrel) := by
  let := associatedChartedSpace F
  let := diagonalAction F
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap F) ((IC).prod I₁) ω
  exact coverScalarMap_contMDiff s

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
