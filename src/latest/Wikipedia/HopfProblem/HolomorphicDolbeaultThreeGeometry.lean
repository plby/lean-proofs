import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometrySmooth
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometryTopology
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLocallyFineSmooth
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultSmooth

/-!
# Smooth-sheaf acyclicity in the original period-family atlas

The real smoothness proved here is the real smoothness of the original
complex quotient atlas. Together with the actual Hausdorff and sigma-compact
topology, it supplies genuine smooth partitions of unity. Thus the actual
smooth complex-function sheaf is locally fine and has zero positive-degree
native Ext cohomology, both on the family and on every inherited open.

In particular these open-set statements apply to the literal full inverse
image of every base open. No replacement of the atlas or cohomology theory,
nor any holomorphic acyclicity assumption, is involved.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry

open HolomorphicSheafCohomology

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local notation "IR₃" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)

/-- Local fineness of the actual smooth-function sheaf in the unchanged
period-family atlas, supplied by genuine smooth partitions of unity. -/
theorem total_smooth_locallyFine :
    letI := P.totalChartedSpace
    LocallyFine (SmoothFunctions.additiveSheaf IR₃ P.TotalSpace) := by
  let := P.totalChartedSpace
  let : IsManifold IR₃ ∞ P.TotalSpace := totalSpace_realManifold P
  let : T2Space P.TotalSpace := totalSpace_t2 P
  let : SigmaCompactSpace P.TotalSpace := totalSpace_sigmaCompact P
  exact SmoothFunctions.locallyFine IR₃ P.TotalSpace

/-- All positive native Ext cohomology of the original smooth-function
sheaf vanishes, with no compactness or acyclicity premise. -/
theorem total_smooth_higher_subsingleton (n : ℕ) :
    letI := P.totalChartedSpace
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (SmoothFunctions.additiveSheaf IR₃ P.TotalSpace) (n + 1)) := by
  let := P.totalChartedSpace
  let : IsManifold IR₃ ∞ P.TotalSpace := totalSpace_realManifold P
  let : T2Space P.TotalSpace := totalSpace_t2 P
  let : SigmaCompactSpace P.TotalSpace := totalSpace_sigmaCompact P
  exact SmoothFunctions.higher_subsingleton IR₃ P.TotalSpace n

/-- The same actual fineness assertion on each inherited total-space open. -/
theorem open_smooth_locallyFine (Ω : Opens P.TotalSpace) :
    letI := P.totalChartedSpace
    LocallyFine (SmoothFunctions.additiveSheaf IR₃ Ω) := by
  let := P.totalChartedSpace
  let : IsManifold IR₃ ∞ Ω := open_realManifold P Ω
  let : T2Space Ω := open_t2 P Ω
  let : SigmaCompactSpace Ω := open_sigmaCompact P Ω
  exact SmoothFunctions.locallyFine IR₃ Ω

/-- The actual inherited smooth-function sheaf on any original open has
zero positive-degree native Ext cohomology. This includes every full
inverse image of a base open. -/
theorem open_smooth_higher_subsingleton (Ω : Opens P.TotalSpace) (n : ℕ) :
    letI := P.totalChartedSpace
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (SmoothFunctions.additiveSheaf IR₃ Ω) (n + 1)) := by
  let := P.totalChartedSpace
  let : IsManifold IR₃ ∞ Ω := open_realManifold P Ω
  let : T2Space Ω := open_t2 P Ω
  let : SigmaCompactSpace Ω := open_sigmaCompact P Ω
  exact SmoothFunctions.higher_subsingleton IR₃ Ω n

/-- Literal open restriction of the original smooth-function sheaf has
the same vanishing, via the proved sheaf isomorphism given by flattening
nested open subtypes. No new smooth structure is chosen. -/
theorem restricted_smooth_higher_subsingleton (Ω : Opens P.TotalSpace) (n : ℕ) :
    letI := P.totalChartedSpace
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((OpenRestriction.restriction (X := TopCat.of P.TotalSpace) Ω).obj
        (SmoothFunctions.additiveSheaf IR₃ P.TotalSpace)) (n + 1)) := by
  let := P.totalChartedSpace
  let e := ((CategoryTheory.Sheaf.functorH _ (n + 1)).mapIso
    (OpenDolbeault.smoothSheafIso IR₃ Ω)).addCommGroupIsoToAddEquiv
  have hs := open_smooth_higher_subsingleton P Ω n
  exact ⟨fun a b => e.injective (hs.elim (e a) (e b))⟩

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry
