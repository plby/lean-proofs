import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportMayerVietorisLeft

/-!
# The degree-zero start of original integral compact-support Mayer--Vietoris

A genuine overlap class killed by both original open inclusions has a
representative killed on both actual compact supports. The proved
degree-zero injectivity for supported integral cohomology annihilates
that representative. This gives the initial injection in the original
compact-support sequence without a cover hypothesis.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris

open IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V)

theorem eq_zero_of_firstMap_zero (a : Cohomology (U ∩ V : Set X) 0)
    (ha : firstMap U V hU hV 0 a = 0) : a = 0 := by
  obtain ⟨A, B, hAU, hBV, d, hd, he⟩ :=
    exists_supported_kernel_representative U V hU hV 0 a ha
  have hd0 : d = 0 := IntegralSupportedCohomology.intersectionMap_zero_injective
    (A : Set X) (B : Set X) A.isCompact.isClosed B.isCompact.isClosed
    (hd.trans (IntegralSupportedCohomology.intersectionMap (A : Set X) (B : Set X) 0).map_zero.symm)
  exact he.symm.trans
    ((congrArg (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
      (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) 0) hd0).trans
      (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
        (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) 0).map_zero)

/-- The genuine initial overlap map is injective on actual degree-zero integral cohomology. -/
theorem firstMap_zero_injective : Function.Injective (firstMap U V hU hV 0) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply eq_zero_of_firstMap_zero U V hU hV (a - b)
  exact ((firstMap U V hU hV 0).map_sub a b).trans (sub_eq_zero.mpr hab)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris
