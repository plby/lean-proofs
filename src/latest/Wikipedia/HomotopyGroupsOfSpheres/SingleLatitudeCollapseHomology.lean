import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeCollapseHomology

/-! # The actual single-latitude collapse induces homology isomorphisms -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse

open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open Wikipedia.HopfProblem.SingularMayerVietoris

theorem collapse_homology_bijective (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Function.Bijective (singularHomologyMap (collapse n hn) (k + 2)) := by
  obtain ⟨p, hp⟩ := collapse_surjective n hn
    (quotient (n + 1) (LatitudeCubeCollapse.cubeCenter (n + 1)))
  exact SpherePinch.homologyMap_bijective (collapse n hn) (point (n + 1))
    (collapse_isQuotientMap n hn) (collapse_injective_off_point n hn) p
    (hp ▸ LatitudeCubeCollapse.quotient_cubeCenter_ne_point (n + 1)) k

end Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeCollapse
