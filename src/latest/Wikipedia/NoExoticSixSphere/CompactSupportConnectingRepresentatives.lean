import Wikipedia.NoExoticSixSphere.CompactSupportConnecting
import Wikipedia.NoExoticSixSphere.CompactSupportNeighborhoodZero
import Wikipedia.NoExoticSixSphere.SupportedModTwoConnectingExact

/-!
# Original representative formulas around compact-support connecting

Named ambient compact subsets of the two open sets give subordinate
support pairs. Their original connecting, intersection-extension, and
union-difference maps agree with the genuine compact-support maps.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportMayerVietoris

open CompactSupportCohomology OpenCoverCompactSupports

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)

/-- Both support pieces can be enlarged so their intersection contains a compact overlap subset. -/
theorem exists_intersection_upper (K : Index U V) (N : Compacts X)
    (hN : (N : Set X) ⊆ U ∩ V) :
    ∃ P : Index U V, K ≤ P ∧ N ≤ intersectionCompact U V P := by
  let A := insideCompact U N (fun _ hx => (hN hx).1)
  let B := insideCompact V N (fun _ hx => (hN hx).2)
  refine ⟨(K.1 ⊔ A, K.2 ⊔ B), ⟨le_sup_left, le_sup_left⟩, ?_⟩
  intro x hx
  exact ⟨⟨⟨x, (hN hx).1⟩, Or.inr hx, rfl⟩, ⟨⟨x, (hN hx).2⟩, Or.inr hx, rfl⟩⟩

variable (hU : IsOpen U) (hV : IsOpen V)

/-- The genuine overlap maps retain the original extensions from an actual intersection support. -/
theorem firstMap_neighborhood_intersection (A B : Compacts X)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V) (p : ℕ)
    (c : Component X p (A ⊓ B)) :
    firstMap U V hU hV p
      (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
        (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) p c) =
      (neighborhoodOf U hU A hAU p (SupportedModTwoCohomology.extend
        (show (A ⊓ B : Compacts X) ≤ A from inf_le_left) p c),
       neighborhoodOf V hV B hBV p (SupportedModTwoCohomology.extend
        (show (A ⊓ B : Compacts X) ≤ B from inf_le_right) p c)) := by
  apply Prod.ext
  · exact (openMap_neighborhoodOf (Set.inter_subset_left : U ∩ V ⊆ U)
      (hU.inter hV) hU (A ⊓ B) (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩)
      (fun _ hx => hAU hx.1) p c).trans
      (neighborhoodOf_extend U hU (show A ⊓ B ≤ A from inf_le_left)
        (fun _ hx => hAU hx.1) hAU p c).symm
  · exact (openMap_neighborhoodOf (Set.inter_subset_right : U ∩ V ⊆ V)
      (hU.inter hV) hV (A ⊓ B) (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩)
      (fun _ hx => hBV hx.2) p c).trans
      (neighborhoodOf_extend V hV (show A ⊓ B ≤ B from inf_le_right)
        (fun _ hx => hBV hx.2) hBV p c).symm

/-- The genuine ambient difference has its original support-level difference representative. -/
theorem differenceMap_neighborhood (A B : Compacts X)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V) (p : ℕ)
    (a : Component X p A) (b : Component X p B) :
    differenceMap U V hU hV p (neighborhoodOf U hU A hAU p a, neighborhoodOf V hV B hBV p b) =
      of X p (A ⊔ B) (SupportedModTwoCohomology.unionDifference (A : Set X) (B : Set X) p
        (a, b)) := by
  change inclusion U hU p (neighborhoodOf U hU A hAU p a) -
    inclusion V hV p (neighborhoodOf V hV B hBV p b) = _
  rw [inclusion_neighborhoodOf U hU A hAU p a, inclusion_neighborhoodOf V hV B hBV p b]
  exact ((of X p (A ⊔ B)).map_sub _ _).trans
    (congrArg₂ (fun x y => x - y)
      (of_transition X p (K := A) (L := A ⊔ B) le_sup_left a)
      (of_transition X p (K := B) (L := A ⊔ B) le_sup_right b)) |>.symm

/-- The connecting formula for any named compact supports inside the two actual open sets. -/
theorem connecting_of_supports (p : ℕ) (hcover : U ∪ V = Set.univ) (A B : Compacts X)
    (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V) (a : Component X p (A ⊔ B)) :
    connecting U V hU hV p hcover (of X p (A ⊔ B) a) =
      neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
        (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) (p + 1)
        (SupportedModTwoCohomology.connecting (A : Set X) (B : Set X)
          A.isCompact.isClosed B.isCompact.isClosed p a) := by
  let P : Index U V := (insideCompact U A hAU, insideCompact V B hBV)
  have hgen (C D : Compacts X) (hC : C = imageCompact U P.1) (hD : D = imageCompact V P.2)
      (hI : (C ⊓ D : Compacts X).carrier ⊆ U ∩ V) (b : Component X p (C ⊔ D)) :
      connecting U V hU hV p hcover (of X p (C ⊔ D) b) =
        neighborhoodOf (U ∩ V) (hU.inter hV) (C ⊓ D) hI (p + 1)
          (SupportedModTwoCohomology.connecting (C : Set X) (D : Set X)
            C.isCompact.isClosed D.isCompact.isClosed p b) := by
    subst C
    subst D
    exact connecting_of U V hU hV p hcover P b
  exact hgen A B (SetLike.coe_injective (image_insideCompact U A hAU).symm)
    (SetLike.coe_injective (image_insideCompact V B hBV).symm)
    (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) a

end NoExoticSixSphere.CompactSupportMayerVietoris
