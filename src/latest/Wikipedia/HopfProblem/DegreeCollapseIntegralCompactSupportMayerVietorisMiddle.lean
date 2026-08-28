import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCoverCompactSupportAgreement
import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCohomologyExact

/-!
# Middle exactness for the actual compact-support Mayer--Vietoris maps

The two maps from the overlap and the difference of ambient extensions
are the genuine open-inclusion maps on compact-support cohomology.
Equal ambient extensions are realized on one subordinate compact pair;
original relative Mayer--Vietoris then constructs an overlap class.
This proves middle exactness, not yet the connecting-map portions of
the compact-support sequence.
-/

noncomputable section

open NoExoticSixSphere

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris

open IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V)

/-- The original open inclusion of the overlap into the left neighborhood. -/
def leftMap (p : ℕ) : Cohomology (U ∩ V : Set X) p →ₗ[ℤ] Cohomology U p :=
  openMap (subsetInclusion (Set.inter_subset_left : U ∩ V ⊆ U))
    (subsetInclusion_isOpenEmbedding Set.inter_subset_left (hU.inter hV)) p

/-- The original open inclusion of the overlap into the right neighborhood. -/
def rightMap (p : ℕ) : Cohomology (U ∩ V : Set X) p →ₗ[ℤ] Cohomology V p :=
  openMap (subsetInclusion (Set.inter_subset_right : U ∩ V ⊆ V))
    (subsetInclusion_isOpenEmbedding Set.inter_subset_right (hU.inter hV)) p

/-- Both actual overlap inclusions on the original directed-limit groups. -/
def firstMap (p : ℕ) :
    Cohomology (U ∩ V : Set X) p →ₗ[ℤ] (Cohomology U p × Cohomology V p) :=
  (leftMap U V hU hV p).prod (rightMap U V hU hV p)

/-- The difference of the two original ambient extension maps. -/
def differenceMap (p : ℕ) : (Cohomology U p × Cohomology V p) →ₗ[ℤ] Cohomology X p :=
  (inclusion U hU p).comp (LinearMap.fst ℤ _ _) -
    (inclusion V hV p).comp (LinearMap.snd ℤ _ _)

theorem firstMap_apply (p : ℕ) (c : Cohomology (U ∩ V : Set X) p) :
    firstMap U V hU hV p c = (leftMap U V hU hV p c, rightMap U V hU hV p c) := rfl

theorem differenceMap_apply (p : ℕ) (a : Cohomology U p × Cohomology V p) :
    differenceMap U V hU hV p a = inclusion U hU p a.1 - inclusion V hV p a.2 := rfl

/-- Both composites are the actual ambient inclusion of the overlap. -/
theorem difference_first_zero (p : ℕ) (c : Cohomology (U ∩ V : Set X) p) :
    differenceMap U V hU hV p (firstMap U V hU hV p c) = 0 := by
  have hL := inclusion_subsetInclusion (Set.inter_subset_left : U ∩ V ⊆ U)
    (hU.inter hV) hU p c
  have hR := inclusion_subsetInclusion (Set.inter_subset_right : U ∩ V ⊆ V)
    (hU.inter hV) hV p c
  change inclusion U hU p (leftMap U V hU hV p c) -
    inclusion V hV p (rightMap U V hU hV p c) = 0
  exact sub_eq_zero.mpr (hL.trans hR.symm)

variable (hcover : U ∪ V = Set.univ)

include hcover

/-- Equal genuine ambient extensions lift together from the original overlap space. -/
theorem exists_lift_of_agree (p : ℕ) (a : Cohomology U p) (b : Cohomology V p)
    (hab : inclusion U hU p a = inclusion V hV p b) :
    ∃ c : Cohomology (U ∩ V : Set X) p,
      leftMap U V hU hV p c = a ∧ rightMap U V hU hV p c = b := by
  obtain ⟨P, a', b', ha, hb, he⟩ := IntegralOpenCoverCompactSupports.exists_matching_representatives
    U V hU hV hcover p a b hab
  let A := imageCompact U P.1
  let B := imageCompact V P.2
  let I := A ⊓ B
  have hAU : (A : Set X) ⊆ U := imageCompact_subset U P.1
  have hBV : (B : Set X) ⊆ V := imageCompact_subset V P.2
  have hIA : (I : Set X) ⊆ A := Set.inter_subset_left
  have hIB : (I : Set X) ⊆ B := Set.inter_subset_right
  have hIU : (I : Set X) ⊆ U := hIA.trans hAU
  have hIV : (I : Set X) ⊆ V := hIB.trans hBV
  have hIW : (I : Set X) ⊆ U ∩ V := fun _ hx => ⟨hIU hx, hIV hx⟩
  obtain ⟨c, hcA, hcB⟩ := IntegralSupportedCohomology.exists_intersection_lift
    (A : Set X) (B : Set X) A.isCompact.isClosed B.isCompact.isClosed p a' b' he
  refine ⟨neighborhoodOf (U ∩ V) (hU.inter hV) I hIW p c, ?_, ?_⟩
  · exact (openMap_neighborhoodOf (Set.inter_subset_left : U ∩ V ⊆ U)
      (hU.inter hV) hU I hIW hIU p c).trans
      ((neighborhoodOf_extend U hU hIA hIU hAU p c).symm.trans
        ((congrArg (neighborhoodOf U hU A hAU p) hcA).trans ha))
  · exact (openMap_neighborhoodOf (Set.inter_subset_right : U ∩ V ⊆ V)
      (hU.inter hV) hV I hIW hIV p c).trans
      ((neighborhoodOf_extend V hV hIB hIV hBV p c).symm.trans
        ((congrArg (neighborhoodOf V hV B hBV p) hcB).trans hb))

/-- Middle exactness uses the actual compact-support groups and the original overlap maps. -/
theorem exact_middle (p : ℕ) :
    LinearMap.range (firstMap U V hU hV p) = LinearMap.ker (differenceMap U V hU hV p) := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨c, rfl⟩
    exact difference_first_zero U V hU hV p c
  · intro ha
    have hab : inclusion U hU p a.1 = inclusion V hV p a.2 :=
      sub_eq_zero.mp (show inclusion U hU p a.1 - inclusion V hV p a.2 = 0 from ha)
    obtain ⟨c, hcL, hcR⟩ := exists_lift_of_agree U V hU hV hcover p a.1 a.2 hab
    exact ⟨c, Prod.ext hcL hcR⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris
