import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportConnectingRepresentatives

/-!
# Compact-support exactness at the genuine ambient cohomology group

The original difference maps into the kernel of the constructed
connecting map. Conversely, a zero overlap class becomes zero on a
larger compact overlap support. Enlarge both support pieces to contain
that compact set and apply the proved original supported exactness.
-/

noncomputable section

open NoExoticSixSphere

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris

open IntegralCompactSupportCohomology IntegralOpenCoverCompactSupports
open IntegralSupportedCohomology (extend extend_trans)

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

/-- The actual ambient difference is annihilated by the constructed connecting map. -/
theorem connecting_difference_zero (p : ℕ) (a : Cohomology U p × Cohomology V p) :
    connecting U V hU hV p hcover (differenceMap U V hU hV p a) = 0 := by
  obtain ⟨K, b, hb⟩ := IntegralCompactSupportCohomology.exists_representative U p a.1
  obtain ⟨L, c, hc⟩ := IntegralCompactSupportCohomology.exists_representative V p a.2
  let A := imageCompact U K
  let B := imageCompact V L
  let b' := IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p b
  let c' := IntegralOpenSupport.extension V hV (L : Set V) L.isCompact p c
  have hA := imageCompact_subset U K
  have hB := imageCompact_subset V L
  have he := differenceMap_neighborhood U V hU hV A B hA hB p b' c'
  have hpair : (neighborhoodOf U hU A hA p b', neighborhoodOf V hV B hB p c') = a :=
    Prod.ext ((neighborhoodOf_extension U hU K p b).trans hb)
      ((neighborhoodOf_extension V hV L p c).trans hc)
  have he' := congrArg (differenceMap U V hU hV p) hpair
  apply (congrArg (connecting U V hU hV p hcover) (he'.symm.trans he)).trans
  apply (connecting_of_supports U V hU hV p hcover A B hA hB
    (IntegralSupportedCohomology.unionDifference (A : Set X) (B : Set X) p (b', c'))).trans
  have hz : IntegralSupportedCohomology.connecting (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed p
      (IntegralSupportedCohomology.unionDifference (A : Set X) (B : Set X) p (b', c')) = 0 :=
    (IntegralSupportedCohomology.connecting_exact_right (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed p).le ⟨(b', c'), rfl⟩
  exact (congrArg (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
    (fun _ hx => ⟨hA hx.1, hB hx.2⟩) (p + 1)) hz).trans
    (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
      (fun _ hx => ⟨hA hx.1, hB hx.2⟩) (p + 1)).map_zero

/-- Exactness at the original ambient compact-support group, in every degree. -/
theorem exact_right (p : ℕ) :
    LinearMap.range (differenceMap U V hU hV p) =
      LinearMap.ker (connecting U V hU hV p hcover) := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    exact connecting_difference_zero U V hU hV hcover p b
  · intro ha
    obtain ⟨K, b, rfl⟩ :=
      IntegralOpenCoverCompactSupports.exists_representative U V hU hV hcover p a
    let A := imageCompact U K.1
    let B := imageCompact V K.2
    let I := intersectionCompact U V K
    let d := IntegralSupportedCohomology.connecting (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed p b
    have hz : neighborhoodOf (U ∩ V) (hU.inter hV) I
        (intersectionCompact_subset U V K) (p + 1) d = 0 :=
      (connecting_of U V hU hV p hcover K b).symm.trans ha
    obtain ⟨N, hIN, hNW, hdz⟩ := (neighborhoodOf_eq_zero_iff (U ∩ V) (hU.inter hV)
      I (intersectionCompact_subset U V K) (p + 1) d).mp hz
    obtain ⟨P, hKP, hNP⟩ := exists_intersection_upper U V K N hNW
    let C := imageCompact U P.1
    let D := imageCompact V P.2
    have hAC : (A : Set X) ⊆ C := Set.image_mono hKP.1
    have hBD : (B : Set X) ⊆ D := Set.image_mono hKP.2
    let b' := extend (unionCompact_mono U V hKP) p b
    have he := IntegralSupportedCohomology.connecting_extend hAC hBD
      A.isCompact.isClosed B.isCompact.isClosed C.isCompact.isClosed D.isCompact.isClosed p b
    have hdP : IntegralSupportedCohomology.connecting (C : Set X) (D : Set X)
        C.isCompact.isClosed D.isCompact.isClosed p b' = 0 := by
      apply he.symm.trans
      exact (LinearMap.congr_fun (extend_trans hIN hNP (p + 1)) d).trans
        ((congrArg (extend hNP (p + 1)) hdz).trans (extend hNP (p + 1)).map_zero)
    obtain ⟨c, hc⟩ := (IntegralSupportedCohomology.connecting_exact_right (C : Set X) (D : Set X)
      C.isCompact.isClosed D.isCompact.isClosed p).ge hdP
    have hCU := imageCompact_subset U P.1
    have hDV := imageCompact_subset V P.2
    refine ⟨(neighborhoodOf U hU C hCU p c.1, neighborhoodOf V hV D hDV p c.2), ?_⟩
    apply (differenceMap_neighborhood U V hU hV C D hCU hDV p c.1 c.2).trans
    apply (congrArg (of X p (C ⊔ D)) hc).trans
    exact of_transition X p (K := unionCompact U V K) (L := unionCompact U V P)
      (unionCompact_mono U V hKP) b

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris
