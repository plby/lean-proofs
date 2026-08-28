import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCohomologyNaturality

/-!
# The original integral connecting map on closed supports

Complement identities transport only along equal actual subspaces.
The original relative integral connecting map becomes a map from union
support to intersection support, natural for both genuine support
extensions. No sign is discarded in these integral constructions.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] {U V U' V' : Set X}

abbrev subsetPullback (h : U ⊆ V) (p : ℕ) : Cohomology V p →ₗ[ℤ] Cohomology U p :=
  (HomologicalComplex.homologyMap
    (dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h)) p).hom

def setCongr (h : U = V) (p : ℕ) : Cohomology U p ≃ₗ[ℤ] Cohomology V p := by
  subst V
  exact LinearEquiv.refl ℤ _

theorem setCongr_subset (hU : U = U') (hV : V = V') (h : U ⊆ V) (h' : U' ⊆ V')
    (p : ℕ) (a : Cohomology V p) :
    setCongr hU p (subsetPullback h p a) = subsetPullback h' p (setCongr hV p a) := by
  subst U'
  subst V'
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology

variable {X : Type} [TopologicalSpace X] (K L : Set X)

def unionComplementEquiv (p : ℕ) :
    Cohomology (K ∪ L) p ≃ₗ[ℤ]
      IntegralRelativeCohomologyMayerVietoris.Cohomology (Kᶜ ∩ Lᶜ) p :=
  IntegralRelativeCohomologyMayerVietoris.setCongr (Set.compl_union K L) p

def interComplementEquiv (p : ℕ) :
    Cohomology (K ∩ L) p ≃ₗ[ℤ]
      IntegralRelativeCohomologyMayerVietoris.Cohomology (Kᶜ ∪ Lᶜ) p :=
  IntegralRelativeCohomologyMayerVietoris.setCongr (Set.compl_inter K L) p

/-- The genuine integral connecting map between these actual closed supports. -/
def connecting (hK : IsClosed K) (hL : IsClosed L) (p : ℕ) :
    Cohomology (K ∪ L) p →ₗ[ℤ] Cohomology (K ∩ L) (p + 1) :=
  (interComplementEquiv K L (p + 1)).symm.toLinearMap.comp
    ((IntegralRelativeCohomologyMayerVietoris.connecting
      Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p).comp
        (unionComplementEquiv K L p).toLinearMap)

theorem connecting_toRelative (hK : IsClosed K) (hL : IsClosed L)
    (p : ℕ) (a : Cohomology (K ∪ L) p) :
    interComplementEquiv K L (p + 1) (connecting K L hK hL p a) =
      IntegralRelativeCohomologyMayerVietoris.connecting
        Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl p (unionComplementEquiv K L p a) :=
  (interComplementEquiv K L (p + 1)).apply_symm_apply _

variable {K L} {K' L' : Set X} (hK : K ⊆ K') (hL : L ⊆ L')

theorem unionComplementEquiv_extend (p : ℕ) (a : Cohomology (K ∪ L) p) :
    unionComplementEquiv K' L' p (extend (Set.union_subset_union hK hL) p a) =
      IntegralRelativeCohomologyMayerVietoris.subsetPullback
        (Set.inter_subset_inter (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL))
        p (unionComplementEquiv K L p a) :=
  IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (Set.compl_union K' L') (Set.compl_union K L)
    (Set.compl_subset_compl.mpr (Set.union_subset_union hK hL)) _ p a

theorem interComplementEquiv_extend (p : ℕ) (a : Cohomology (K ∩ L) p) :
    interComplementEquiv K' L' p (extend (Set.inter_subset_inter hK hL) p a) =
      IntegralRelativeCohomologyMayerVietoris.subsetPullback
        (Set.union_subset_union (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL))
        p (interComplementEquiv K L p a) :=
  IntegralRelativeCohomologyMayerVietoris.setCongr_subset
    (Set.compl_inter K' L') (Set.compl_inter K L)
    (Set.compl_subset_compl.mpr (Set.inter_subset_inter hK hL)) _ p a

/-- Both original compact-support extensions commute with the original integral connecting map. -/
theorem connecting_extend (hKc : IsClosed K) (hLc : IsClosed L)
    (hK'c : IsClosed K') (hL'c : IsClosed L') (p : ℕ) (a : Cohomology (K ∪ L) p) :
    extend (Set.inter_subset_inter hK hL) (p + 1) (connecting K L hKc hLc p a) =
      connecting K' L' hK'c hL'c p (extend (Set.union_subset_union hK hL) p a) := by
  apply (interComplementEquiv K' L' (p + 1)).injective
  rw [interComplementEquiv_extend hK hL, connecting_toRelative, connecting_toRelative,
    unionComplementEquiv_extend hK hL]
  exact IntegralRelativeCohomologyMayerVietoris.connecting_naturality
    (Set.compl_subset_compl.mpr hK) (Set.compl_subset_compl.mpr hL)
    hK'c.isOpen_compl hL'c.isOpen_compl hKc.isOpen_compl hLc.isOpen_compl p
    (unionComplementEquiv K L p a)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportedCohomology
