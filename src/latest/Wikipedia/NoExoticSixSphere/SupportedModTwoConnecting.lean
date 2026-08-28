import Wikipedia.NoExoticSixSphere.RelativeModTwoMayerVietorisNaturality
import Wikipedia.NoExoticSixSphere.SupportedModTwoMayerVietoris

/-!
# The original Mayer--Vietoris connecting map for closed supports

Complement identities transport the proved relative connecting map
to the union and intersection of the actual closed supports. Its
naturality is proved for both original support-enlargement maps.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] {U V U' V' : Set X}

/-- Transport only along an equality of the actual subspaces. -/
def setCongr (h : U = V) (p : ℕ) : Cohomology U p ≃ₗ[ℤ] Cohomology V p := by
  subst V
  exact LinearEquiv.refl ℤ _

/-- Equality transport retains the original identity-pair pullback. -/
theorem setCongr_subset (hU : U = U') (hV : V = V') (h : U ⊆ V) (h' : U' ⊆ V')
    (p : ℕ) (a : Cohomology V p) :
    setCongr hU p (cohomologyPullback (ContinuousMap.id X) h p a) =
      cohomologyPullback (ContinuousMap.id X) h' p (setCongr hV p a) := by
  subst U'
  subst V'
  rfl

end NoExoticSixSphere.RelativeModTwoCochains

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X)

/-- The actual union support complement is the intersection of the two original complements. -/
def unionComplementEquiv (p : ℕ) :
    Cohomology (K ∪ L) p ≃ₗ[ℤ] RelativeModTwoCochains.Cohomology (Kᶜ ∩ Lᶜ) p :=
  RelativeModTwoCochains.setCongr (Set.compl_union K L) p

/-- The actual intersection support complement is the union of the two original complements. -/
def interComplementEquiv (p : ℕ) :
    Cohomology (K ∩ L) p ≃ₗ[ℤ] RelativeModTwoCochains.Cohomology (Kᶜ ∪ Lᶜ) p :=
  RelativeModTwoCochains.setCongr (Set.compl_inter K L) p

/-- The connecting map from the actual union support to its intersection support. -/
def connecting (hK : IsClosed K) (hL : IsClosed L) (p : ℕ) :
    Cohomology (K ∪ L) p →ₗ[ℤ] Cohomology (K ∩ L) (p + 1) :=
  (interComplementEquiv K L (p + 1)).symm.toLinearMap.comp
    ((RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).comp
      (unionComplementEquiv K L p).toLinearMap)

/-- The supported connecting map is exactly the transported original relative connecting map. -/
theorem connecting_toRelative (hK : IsClosed K) (hL : IsClosed L)
    (p : ℕ) (a : Cohomology (K ∪ L) p) :
    interComplementEquiv K L (p + 1) (connecting K L hK hL p a) =
      RelativeModTwoMayerVietoris.connecting Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p
        (unionComplementEquiv K L p a) :=
  (interComplementEquiv K L (p + 1)).apply_symm_apply _

variable {K L} {K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L')

/-- The input comparison retains actual support enlargement. -/
theorem unionComplementEquiv_extend (p : ℕ) (a : Cohomology (K ∪ L) p) :
    unionComplementEquiv K' L' p (extend (Set.union_subset_union hK hL) p a) =
      RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id X)
        (Set.inter_subset_inter (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL))
        p (unionComplementEquiv K L p a) :=
  RelativeModTwoCochains.setCongr_subset (Set.compl_union K' L') (Set.compl_union K L)
    (Set.compl_subset_compl.mpr (Set.union_subset_union hK hL)) _ p a

/-- The output comparison retains actual support enlargement. -/
theorem interComplementEquiv_extend (p : ℕ) (a : Cohomology (K ∩ L) p) :
    interComplementEquiv K' L' p (extend (Set.inter_subset_inter hK hL) p a) =
      RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id X)
        (Set.union_subset_union (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL))
        p (interComplementEquiv K L p a) :=
  RelativeModTwoCochains.setCongr_subset (Set.compl_inter K' L') (Set.compl_inter K L)
    (Set.compl_subset_compl.mpr (Set.inter_subset_inter hK hL)) _ p a

/-- Naturality for both original support-extension maps, before any direct-limit descent. -/
theorem connecting_extend (hKc : IsClosed K) (hLc : IsClosed L)
    (hK'c : IsClosed K') (hL'c : IsClosed L') (p : ℕ) (a : Cohomology (K ∪ L) p) :
    extend (Set.inter_subset_inter hK hL) (p + 1) (connecting K L hKc hLc p a) =
      connecting K' L' hK'c hL'c p (extend (Set.union_subset_union hK hL) p a) := by
  apply (interComplementEquiv K' L' (p + 1)).injective
  rw [interComplementEquiv_extend hK hL, connecting_toRelative, connecting_toRelative,
    unionComplementEquiv_extend hK hL]
  exact RelativeModTwoMayerVietoris.connecting_naturality
    (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL)
    hK'c.isOpen_compl hL'c.isOpen_compl hKc.isOpen_compl hLc.isOpen_compl p
    (unionComplementEquiv K L p a)

end NoExoticSixSphere.SupportedModTwoCohomology
