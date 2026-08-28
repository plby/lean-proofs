import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyChartsNative
import Wikipedia.HopfProblem.AffineBlowupManifold

/-!
# Genuine holomorphic acyclicity on the two incidence blow-up chart opens

The two opens are the literal targets of the actual incidence-model
parametrizations. Each is genuinely biholomorphic to native affine
two-space, by its actual affine map and inverse coordinates. The original
Ext-defined holomorphic cohomology therefore vanishes on these two opens
in every positive degree. No vanishing on their union is asserted here.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts

open ToricCharts

/-- The actual two incidence-model affine chart targets. -/
def incidenceOpen (b : Bool) : Opens AffineBlowup.Space :=
  ⟨AffineBlowup.affineTarget b, AffineBlowup.affineTarget_isOpen b⟩

/-- Each actual target is exactly the range of its literal affine map. -/
theorem incidenceOpen_eq_range (b : Bool) :
    (incidenceOpen b : Set AffineBlowup.Space) = range (AffineBlowup.affineMap b) := by
  ext x
  constructor
  · intro hx
    exact ⟨AffineBlowup.affineCoords b x, AffineBlowup.affineMap_affineCoords b x hx⟩
  · rintro ⟨z, rfl⟩
    exact AffineBlowup.affineMap_mem_target b z

/-- The actual inverse incidence chart is holomorphic on its actual target. -/
theorem incidenceInverse_holomorphicOn (b : Bool) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2) ω
      (AffineBlowup.affineCoords b) (incidenceOpen b) := by
  have he : (AffineBlowup.parametrization b).symm ∈
      IsManifold.maximalAtlas 𝓘(ℂ, CoordinateSpace 2) ω AffineBlowup.Space :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  exact contMDiffOn_of_mem_maximalAtlas he

/-- The actual incidence affine map and its actual inverse coordinates
give a genuine analytic biholomorphism of the open submanifold. -/
def incidenceBiholomorph (b : Bool) :
    Diffeomorph 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2)
      (CoordinateSpace 2) (incidenceOpen b) ω where
  toEquiv :=
    { toFun z := ⟨AffineBlowup.affineMap b z, AffineBlowup.affineMap_mem_target b z⟩
      invFun x := AffineBlowup.affineCoords b x
      left_inv := AffineBlowup.affineCoords_affineMap b
      right_inv x := Subtype.ext (AffineBlowup.affineMap_affineCoords b x x.property) }
  contMDiff_toFun z := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact AffineBlowup.affineMap_holomorphic b z
  contMDiff_invFun x := by
    apply (contMDiffAt_subtype_iff (f := AffineBlowup.affineCoords b) (x := x)).mpr
    exact (incidenceInverse_holomorphicOn b).contMDiffAt
      ((incidenceOpen b).isOpen.mem_nhds x.property)

@[simp] theorem incidenceBiholomorph_apply (b : Bool) (z : CoordinateSpace 2) :
    (incidenceBiholomorph b z : AffineBlowup.Space) = AffineBlowup.affineMap b z := rfl

@[simp] theorem incidenceBiholomorph_symm_apply (b : Bool) (x : incidenceOpen b) :
    (incidenceBiholomorph b).symm x = AffineBlowup.affineCoords b x := rfl

/-- The two actual opens cover the actual incidence-model blow-up. -/
theorem incidenceOpen_cover (x : AffineBlowup.Space) : ∃ b : Bool, x ∈ incidenceOpen b := by
  obtain ⟨b, z, rfl⟩ := AffineBlowup.affineMap_jointly_surjective x
  exact ⟨b, AffineBlowup.affineMap_mem_target b z⟩

theorem incidenceOpen_iSup : iSup incidenceOpen = ⊤ := by
  apply le_antisymm le_top
  intro x _
  exact Opens.mem_iSup.mpr (incidenceOpen_cover x)

/-- Genuine holomorphic cohomology on the actual open submanifold is
identified with genuine cohomology on the native affine two-space. -/
def incidenceCohomologyEquiv (b : Bool) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (incidenceOpen b)) n ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (CoordinateSpace 2)) n :=
  Biholomorph.cohomologyEquiv (incidenceBiholomorph b) n

/-- Unconditional positive-degree vanishing on either actual incidence chart. -/
theorem incidence_higher_subsingleton (b : Bool) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (incidenceOpen b))
      (n + 1)) := by
  let e := incidenceCohomologyEquiv b (n + 1)
  exact ⟨fun a c => e.injective ((native_higher_subsingleton n).elim (e a) (e c))⟩

theorem incidence_higher_eq_zero (b : Bool) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (incidenceOpen b))
      (n + 1)) : a = 0 :=
  (incidence_higher_subsingleton b n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts
