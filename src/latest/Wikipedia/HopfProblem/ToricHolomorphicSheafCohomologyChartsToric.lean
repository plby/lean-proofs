import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyChartsNative
import Wikipedia.HopfProblem.ToricComponentManifold
import Wikipedia.HopfProblem.ToricHexagon

/-!
# Genuine holomorphic acyclicity on the actual toric affine chart opens

Each actual coordinate-hyperplane parametrization is an analytic
biholomorphism from native complex two-space to its actual open range in
the ray divisor. The inverse is proved analytic using that very chart in
the already constructed maximal atlas. The six zero-ray chart ranges
form an actual open cover, and every one of their genuine holomorphic
cohomology groups vanishes in positive degree.

This does not assert acyclicity of the entire compact ray divisor.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts

open ToricCharts ToricSpace ToricComponent

variable {v : Fin 2 → ℤ}

/-- The literal open range of an actual affine inclusion into the ray divisor. -/
def affineOpen (c : ChartIndex v) : Opens (rayDivisor v) :=
  ⟨range (affineInclusion c), (affineInclusion_openEmbedding c).isOpen_range⟩

@[simp] theorem affineOpen_coe (c : ChartIndex v) :
    (affineOpen c : Set (rayDivisor v)) = range (affineInclusion c) := rfl

/-- The actual inverse chart is analytic on its actual range, because
its inverse parametrization belongs to the constructed maximal atlas. -/
theorem affineInverse_holomorphicOn (c : ChartIndex v) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2) ω
      (parametrization c).symm (affineOpen c) := by
  have he : (parametrization c).symm ∈
      IsManifold.maximalAtlas 𝓘(ℂ, CoordinateSpace 2) ω (rayDivisor v) :=
    IsManifold.subset_maximalAtlas (mem_range_self c)
  simpa only [OpenPartialHomeomorph.symm_source, ToricComponent.parametrization_target,
    affineOpen_coe]
    using contMDiffOn_of_mem_maximalAtlas he

/-- The actual affine chart, as a genuine biholomorphism onto its literal
open-submanifold range. Neither direction is a supplied hypothesis. -/
def affineBiholomorph (c : ChartIndex v) :
    Diffeomorph 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2)
      (CoordinateSpace 2) (affineOpen c) ω where
  toEquiv :=
    { toFun z := ⟨affineInclusion c z, mem_range_self z⟩
      invFun x := (parametrization c).symm x
      left_inv z := (parametrization c).left_inv (mem_univ z)
      right_inv x := by
        apply Subtype.ext
        apply (parametrization c).right_inv
        rw [ToricComponent.parametrization_target]
        exact x.property }
  contMDiff_toFun z := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact affineInclusion_holomorphic c z
  contMDiff_invFun x := by
    apply (contMDiffAt_subtype_iff (f := (parametrization c).symm) (x := x)).mpr
    exact (affineInverse_holomorphicOn c).contMDiffAt
      ((affineOpen c).isOpen.mem_nhds x.property)

@[simp] theorem affineBiholomorph_apply (c : ChartIndex v) (z : CoordinateSpace 2) :
    (affineBiholomorph c z : rayDivisor v) = affineInclusion c z := rfl

@[simp] theorem affineBiholomorph_symm_apply (c : ChartIndex v) (x : affineOpen c) :
    (affineBiholomorph c).symm x = (parametrization c).symm x := rfl

/-- The genuine cohomology comparison with native affine two-space. -/
def affineCohomologyEquiv (c : ChartIndex v) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (affineOpen c)) n ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (CoordinateSpace 2)) n :=
  Biholomorph.cohomologyEquiv (affineBiholomorph c) n

/-- Actual holomorphic sheaf cohomology vanishes on each actual toric
affine chart range in every positive degree. -/
theorem affine_higher_subsingleton (c : ChartIndex v) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (affineOpen c))
      (n + 1)) := by
  let e := affineCohomologyEquiv c (n + 1)
  exact ⟨fun a b => e.injective ((native_higher_subsingleton n).elim (e a) (e b))⟩

/-- The six literal affine chart ranges in the actual zero-ray divisor. -/
def zeroOpen (i : Fin 6) : Opens (rayDivisor 0) := affineOpen (zeroChart i)

@[simp] theorem zeroOpen_coe (i : Fin 6) :
    (zeroOpen i : Set (rayDivisor 0)) = range (affineInclusion (zeroChart i)) := rfl

/-- Every actual zero-ray point lies in one of the six actual chart ranges. -/
theorem zeroOpen_cover (x : rayDivisor 0) : ∃ i : Fin 6, x ∈ zeroOpen i := by
  obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  exact ⟨i, mem_range_self z⟩

/-- The genuine finite open cover, as an equality in the actual lattice of opens. -/
theorem zeroOpen_iSup : iSup zeroOpen = ⊤ := by
  apply le_antisymm le_top
  intro x _
  exact Opens.mem_iSup.mpr (zeroOpen_cover x)

/-- The chart map of the six-open cover is the literal affine inclusion. -/
abbrev zeroBiholomorph (i : Fin 6) :
    Diffeomorph 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2)
      (CoordinateSpace 2) (zeroOpen i) ω :=
  affineBiholomorph (zeroChart i)

@[simp] theorem zeroBiholomorph_apply (i : Fin 6) (z : CoordinateSpace 2) :
    (zeroBiholomorph i z : rayDivisor 0) = affineInclusion (zeroChart i) z := rfl

/-- Unconditional positive-degree vanishing on each of the six actual
zero-ray chart opens, for the actual holomorphic function sheaf there. -/
theorem zero_higher_subsingleton (i : Fin 6) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (zeroOpen i))
      (n + 1)) :=
  affine_higher_subsingleton (zeroChart i) n

theorem zero_higher_eq_zero (i : Fin 6) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (zeroOpen i))
      (n + 1)) : a = 0 :=
  (zero_higher_subsingleton i n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts
