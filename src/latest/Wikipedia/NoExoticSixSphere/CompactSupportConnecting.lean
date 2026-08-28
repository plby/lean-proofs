import Wikipedia.NoExoticSixSphere.OpenCoverCompactSupportLimit
import Wikipedia.NoExoticSixSphere.SupportedModTwoConnecting
import Wikipedia.NoExoticSixSphere.CompactSupportMayerVietorisMiddle

/-!
# The genuine compact-support Mayer--Vietoris connecting map

On each subordinate compact pair, apply the original closed-support
connecting map and excise its intersection support into the overlap.
Proved naturality and neighborhood compatibility give a compatible
family. The actual cofinal directed-limit equivalence then constructs
the connecting map on ambient compact-support cohomology.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportMayerVietoris

open CompactSupportCohomology OpenCoverCompactSupports

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)

/-- The actual compact intersection of the two original image supports. -/
def intersectionCompact (K : Index U V) : Compacts X :=
  imageCompact U K.1 ⊓ imageCompact V K.2

theorem intersectionCompact_mono : Monotone (intersectionCompact U V) := by
  intro K L h
  exact inf_le_inf (Set.image_mono h.1) (Set.image_mono h.2)

theorem intersectionCompact_subset (K : Index U V) :
    (intersectionCompact U V K : Set X) ⊆ U ∩ V := by
  intro x hx
  exact ⟨imageCompact_subset U K.1 hx.1, imageCompact_subset V K.2 hx.2⟩

variable (hU : IsOpen U) (hV : IsOpen V) (p : ℕ)

/-- Original connecting followed by original excision into the actual overlap neighborhood. -/
def connectingComponent (K : Index U V) :
    UnionComponent U V p K →ₗ[ℤ] Cohomology (U ∩ V : Set X) (p + 1) :=
  (neighborhoodOf (U ∩ V) (hU.inter hV) (intersectionCompact U V K)
    (intersectionCompact_subset U V K) (p + 1)).comp
      (SupportedModTwoCohomology.connecting (imageCompact U K.1 : Set X)
        (imageCompact V K.2 : Set X) (imageCompact U K.1).isCompact.isClosed
        (imageCompact V K.2).isCompact.isClosed p)

/-- The original support connecting maps form a compatible family on the cofinal diagram. -/
theorem connectingComponent_transition (K L : Index U V) (h : K ≤ L)
    (a : UnionComponent U V p K) :
    connectingComponent U V hU hV p L (unionTransition U V p K L h a) =
      connectingComponent U V hU hV p K a := by
  have he := SupportedModTwoCohomology.connecting_extend
    (show (imageCompact U K.1 : Set X) ⊆ imageCompact U L.1 from Set.image_mono h.1)
    (show (imageCompact V K.2 : Set X) ⊆ imageCompact V L.2 from Set.image_mono h.2)
    (imageCompact U K.1).isCompact.isClosed (imageCompact V K.2).isCompact.isClosed
    (imageCompact U L.1).isCompact.isClosed (imageCompact V L.2).isCompact.isClosed p a
  apply (congrArg (neighborhoodOf (U ∩ V) (hU.inter hV) (intersectionCompact U V L)
    (intersectionCompact_subset U V L) (p + 1)) he.symm).trans
  exact neighborhoodOf_extend (U ∩ V) (hU.inter hV) (intersectionCompact_mono U V h)
    (intersectionCompact_subset U V K) (intersectionCompact_subset U V L) (p + 1)
    (SupportedModTwoCohomology.connecting (imageCompact U K.1 : Set X)
      (imageCompact V K.2 : Set X) (imageCompact U K.1).isCompact.isClosed
      (imageCompact V K.2).isCompact.isClosed p a)

variable (hcover : U ∪ V = Set.univ)

/-- The connecting map on the original compact-support direct-limit cohomology groups. -/
def connecting : Cohomology X p →ₗ[ℤ] Cohomology (U ∩ V : Set X) (p + 1) :=
  cofinalLift U V p hU hV hcover (connectingComponent U V hU hV p)
    (connectingComponent_transition U V hU hV p)

/-- Every subordinate support representative retains its actual connecting and excision formula. -/
theorem connecting_of (K : Index U V) (a : UnionComponent U V p K) :
    connecting U V hU hV p hcover (of X p (unionCompact U V K) a) =
      connectingComponent U V hU hV p K a :=
  cofinalLift_of U V p hU hV hcover (connectingComponent U V hU hV p)
    (connectingComponent_transition U V hU hV p) K a

end NoExoticSixSphere.CompactSupportMayerVietoris
