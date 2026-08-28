import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCapConnectingTransport
import Wikipedia.HopfProblem.DegreeCollapseIntegralCoherentSupportRestriction

/-!
# The signed integral cap square on actual compact supports

Original excision and support coherence prove the relative compatibility
equation for each subordinate compact pair. The signed relative cap
square therefore applies to these classes and to their original
neighborhood cap map. The result works inside arbitrary open subsets.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology
open IntegralCompactSupportCohomology (insideCompact insideEquiv neighborhoodOf image_insideCompact)

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d) (hc : Compatible X d c)
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)

include hc in
/-- Both original pair maps send the constructed restricted classes to the same class. -/
theorem classes_connecting_compatible (K L : Compacts X)
    (hKU : (K : Set X) ⊆ U) (hLV : (L : Set X) ⊆ V) :
    homologyLinearMap (RelativeCoefficients.subtypePairMap (ModuleCat.of ℤ ℤ) (U ∩ V)
      ((K ⊓ L : Compacts X) : Set X)ᶜ) d
      (restrictToOpen (U ∩ V) (hU.inter hV) c
        (insideCompact (U ∩ V) (K ⊓ L) (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩))) =
    homologyLinearMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
      (Set.compl_subset_compl.mpr
        (show (K ⊓ L : Compacts X).carrier ⊆ (K ⊔ L : Compacts X).carrier from
          fun _ hx => Or.inl hx.1))) d (c (K ⊔ L)) :=
  (restrictToOpen_inclusion_as (U ∩ V) (hU.inter hV) c
    (insideCompact (U ∩ V) (K ⊓ L) (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩)) (K ⊓ L)
    (image_insideCompact (U ∩ V) (K ⊓ L) (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩))).trans
      (hc (K ⊓ L) (K ⊔ L) (fun _ hx => Or.inl hx.1)).symm

/-- The original homological and supported cohomological connecting maps
have the signed cap square. -/
theorem component_connecting (hcover : U ∪ V = Set.univ) (K L : Compacts X)
    (hKU : (K : Set X) ⊆ U) (hLV : (L : Set X) ⊆ V)
    (p q : ℕ) (h : p + q + 1 = d)
    (a : IntegralSupportedCohomology.Cohomology ((K ⊔ L : Compacts X) : Set X) p) :
    connectingHomomorphism U V hU hV hcover q
        (IntegralCompactSupportCap.componentMap ((K ⊔ L : Compacts X) : Set X)
          (p := p) (q := q + 1) (by omega) (c (K ⊔ L)) a) =
      -((-1 : ℤ) ^ p) • capOnOpen (U ∩ V) (hU.inter hV) c hc
        (p := p + 1) (q := q) (by omega)
        (neighborhoodOf (U ∩ V) (hU.inter hV) (K ⊓ L)
          (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩) (p + 1)
          (IntegralSupportedCohomology.connecting (K : Set X) (L : Set X)
            K.isCompact.isClosed L.isCompact.isClosed p a)) := by
  let hI : (K ⊓ L : Compacts X).carrier ⊆ U ∩ V := fun _ hx => ⟨hKU hx.1, hLV hx.2⟩
  let hKL : (K ⊓ L : Compacts X).carrier ⊆ (K ⊔ L : Compacts X).carrier :=
    fun _ hx => Or.inl hx.1
  let N := insideCompact (U ∩ V) (K ⊓ L) hI
  let G := restrictToOpen (U ∩ V) (hU.inter hV) c N
  let b := IntegralSupportedCohomology.connecting (K : Set X) (L : Set X)
    K.isCompact.isClosed L.isCompact.isClosed p a
  have hFG := classes_connecting_compatible c hc U V hU hV K L hKU hLV
  have hR := IntegralRelativeCapMayerVietoris.connecting_cap_congr (X := X)
    (p := p) (q := q) (n := d) U (K : Set X)ᶜ V (L : Set X)ᶜ
    hU hV hcover K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl
    (support_complement_cover U (K : Set X) hKU)
    (support_complement_cover V (L : Set X) hLV)
    ((K ⊔ L : Compacts X) : Set X)ᶜ ((K ⊓ L : Compacts X) : Set X)ᶜ
    (Set.compl_union (K : Set X) (L : Set X)) (Set.compl_inter (K : Set X) (L : Set X))
    (Set.compl_subset_compl.mpr hKL) h a (c (K ⊔ L)) G hFG
  let J := IntegralSupportedCohomology.interComplementEquiv (K : Set X) (L : Set X) (p + 1)
  have hδ := (congrArg J.symm
    (IntegralSupportedCohomology.connecting_toRelative (K : Set X) (L : Set X)
      K.isCompact.isClosed L.isCompact.isClosed p a)).symm.trans (J.symm_apply_apply b)
  let pull := RelativeIntegralCap.cohomologyPullback (subtypeInclusion (U ∩ V))
    (show Set.MapsTo (subtypeInclusion (U ∩ V))
      (RelativeSingularHomology.overlapIn (U ∩ V) ((K ⊓ L : Compacts X) : Set X)ᶜ)
      ((K ⊓ L : Compacts X) : Set X)ᶜ from fun _ hx => hx) (p + 1)
  have hi := LinearMap.congr_fun
    (IntegralCompactSupportCohomology.insideEquiv_toRelative (U ∩ V) (hU.inter hV)
      (K ⊓ L) hI (p + 1)) b
  have ht := (capOnOpen_neighborhoodOf (U ∩ V) (hU.inter hV) c hc (K ⊓ L) hI
    (p := p + 1) (q := q) (by omega) b).trans
      (congrArg (fun t => RelativeIntegralCap.capProductInDegree (N : Set (U ∩ V : Set X))ᶜ
        (p := p + 1) (q := q) (n := d) (by omega) t G) hi)
  exact hR.trans ((congrArg (fun t => -((-1 : ℤ) ^ p) •
    RelativeIntegralCap.capProductInDegree (N : Set (U ∩ V : Set X))ᶜ
      (p := p + 1) (q := q) (n := d) (by omega) (pull t) G) hδ).trans
        (congrArg (fun t => -((-1 : ℤ) ^ p) • t) ht.symm))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
