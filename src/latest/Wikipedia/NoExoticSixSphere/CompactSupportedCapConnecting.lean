import Wikipedia.NoExoticSixSphere.RelativeCapConnectingTransport
import Wikipedia.NoExoticSixSphere.SmallCapFundamentalClass
import Mathlib.Topology.Sets.Compacts

/-!
# The original cap connecting square on subordinate compact supports

The constructed fundamental classes satisfy the original relative
compatibility equation. Applying the proved relative cap square and
the actual complement transports gives the connecting identity on
each subordinate compact-support pair.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportedCapMap

open ModTwoCapProduct (Coefficient)
open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  [ChartedSpace E (U ∩ V : Set M)]

/-- The original ambient compact-supported cap followed by actual homological connecting. -/
def capThenConnecting (K L : Compacts M) (p q : ℕ) (h : p + q + 1 = n + 3) :
    SupportedModTwoCohomology.Cohomology ((K ⊔ L : Compacts M) : Set M) p →ₗ[ℤ]
      ModHomology 2 (U ∩ V : Set M) q := by
  let D : SupportedModTwoCohomology.Cohomology ((K ⊔ L : Compacts M) : Set M) p →ₗ[ℤ]
      ModHomology 2 M (q + 1) :=
    dualityMap (E := E) (M := M) n ((K ⊔ L : Compacts M) : Set M) (K ⊔ L).isCompact
      p (q + 1) ((Nat.add_assoc p q 1).symm.trans h)
  exact (ModTwoMayerVietoris.connecting U V hU hV hcover q).comp D

/-- Actual supported cohomological connecting, restriction, then the original neighborhood cap. -/
def connectingThenCap (K L : Compacts M)
    (hKU : (K : Set M) ⊆ U) (hLV : (L : Set M) ⊆ V)
    (p q : ℕ) (h : p + q + 1 = n + 3) :
    SupportedModTwoCohomology.Cohomology ((K ⊔ L : Compacts M) : Set M) p →ₗ[ℤ]
      ModHomology 2 (U ∩ V : Set M) q := by
  let T : Set M := U ∩ V
  let I : Set M := (K ⊓ L : Compacts M)
  let hI : I ⊆ T := fun _ hx => ⟨hKU hx.1, hLV hx.2⟩
  let δ : SupportedModTwoCohomology.Cohomology ((K ⊔ L : Compacts M) : Set M) p →ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology I (p + 1) :=
    SupportedModTwoCohomology.connecting (K : Set M) (L : Set M)
      K.isCompact.isClosed L.isCompact.isClosed p
  let r : SupportedModTwoCohomology.Cohomology I (p + 1) →ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology (supportIn T I) (p + 1) :=
    (SupportedModTwoCohomology.neighborhoodEquiv T I (hU.inter hV)
      (K ⊓ L).isCompact.isClosed hI (p + 1)).toLinearMap
  let D : SupportedModTwoCohomology.Cohomology (supportIn T I) (p + 1) →ₗ[ℤ]
      ModHomology 2 T q :=
    dualityMap (E := E) (M := T) n (supportIn T I)
      (supportIn_isCompact T I (K ⊓ L).isCompact hI) (p + 1) q
      ((Nat.add_right_comm p 1 q).trans h)
  exact D.comp (r.comp δ)

include hU hV in
/-- The two original pair maps send the constructed fundamental classes to the same class. -/
theorem fundamentalClass_connecting_compatible (K L : Compacts M)
    (hKU : (K : Set M) ⊆ U) (hLV : (L : Set M) ⊆ V) :
    homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient (U ∩ V)
      ((K ⊓ L : Compacts M).carrier)ᶜ) (n + 3)
      (CompactSupportedFundamentalClass.fundamentalClass (E := E) n
        (supportIn (U ∩ V) ((K ⊓ L : Compacts M) : Set M))
        (supportIn_isCompact (U ∩ V) ((K ⊓ L : Compacts M) : Set M) (K ⊓ L).isCompact
          (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩))) =
    homologyLinearMap (RelativeCoefficients.subsetMap Coefficient
      (Set.compl_subset_compl.mpr
        (show (K ⊓ L : Compacts M).carrier ⊆ (K ⊔ L : Compacts M).carrier from
          fun _ hx => Or.inl hx.1))) (n + 3)
      (CompactSupportedFundamentalClass.fundamentalClass (E := E) n
        ((K ⊔ L : Compacts M) : Set M) (K ⊔ L).isCompact) :=
  (CompactSupportedFundamentalClass.inclusion_fundamentalClass (E := E) n
    (U ∩ V) (hU.inter hV) ((K ⊓ L : Compacts M) : Set M) (K ⊓ L).isCompact
      (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩)).trans
    (CompactSupportedFundamentalClass.restrict_fundamentalClass (E := E) n
      (show (K ⊓ L : Compacts M).carrier ⊆ (K ⊔ L : Compacts M).carrier from
        fun _ hx => Or.inl hx.1) (K ⊓ L).isCompact (K ⊔ L).isCompact).symm

/-- Genuine connecting commutes with cap on every original subordinate compact-support pair. -/
theorem dualityMap_connecting (K L : Compacts M)
    (hKU : (K : Set M) ⊆ U) (hLV : (L : Set M) ⊆ V)
    (p q : ℕ) (h : p + q + 1 = n + 3)
    (a : SupportedModTwoCohomology.Cohomology ((K ⊔ L : Compacts M) : Set M) p) :
    capThenConnecting (E := E) n U V hU hV hcover K L p q h a =
      connectingThenCap (E := E) n U V hU hV K L hKU hLV p q h a := by
  dsimp only [capThenConnecting, connectingThenCap, LinearMap.comp_apply]
  let hI : (K ⊓ L : Compacts M).carrier ⊆ U ∩ V := fun _ hx => ⟨hKU hx.1, hLV hx.2⟩
  let hKL : (K ⊓ L : Compacts M).carrier ⊆ (K ⊔ L : Compacts M).carrier :=
    fun _ hx => Or.inl hx.1
  have hFG := fundamentalClass_connecting_compatible (E := E) n U V hU hV K L hKU hLV
  let F : (RelativeCoefficients.complex Coefficient ((K ⊔ L : Compacts M).carrier)ᶜ).homology
      (n + 3) := CompactSupportedFundamentalClass.fundamentalClass (E := E) n
        ((K ⊔ L : Compacts M) : Set M) (K ⊔ L).isCompact
  let G : (RelativeCoefficients.complex Coefficient
      (RelativeSingularHomology.overlapIn (U ∩ V) ((K ⊓ L : Compacts M).carrier)ᶜ)).homology
      (n + 3) := CompactSupportedFundamentalClass.fundamentalClass (E := E) n
        (supportIn (U ∩ V) ((K ⊓ L : Compacts M) : Set M))
        (supportIn_isCompact (U ∩ V) ((K ⊓ L : Compacts M) : Set M) (K ⊓ L).isCompact hI)
  have hR := RelativeCapMayerVietoris.connecting_cap_congr (X := M)
    (p := p) (q := q) (n := n + 3) U (K : Set M)ᶜ V (L : Set M)ᶜ
    hU hV hcover K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl
    (SupportedModTwoCohomology.neighborhood_complement_cover U (K : Set M) hKU)
    (SupportedModTwoCohomology.neighborhood_complement_cover V (L : Set M) hLV)
    ((K ⊔ L : Compacts M).carrier)ᶜ ((K ⊓ L : Compacts M).carrier)ᶜ
    (Set.compl_union (K : Set M) (L : Set M)) (Set.compl_inter (K : Set M) (L : Set M))
    (Set.compl_subset_compl.mpr hKL) h a F G hFG
  let J := SupportedModTwoCohomology.interComplementEquiv (K : Set M) (L : Set M) (p + 1)
  have hδ := (congrArg J.symm
    (SupportedModTwoCohomology.connecting_toRelative (K : Set M) (L : Set M)
      K.isCompact.isClosed L.isCompact.isClosed p a)).symm.trans
        (J.symm_apply_apply (SupportedModTwoCohomology.connecting (K : Set M) (L : Set M)
          K.isCompact.isClosed L.isCompact.isClosed p a))
  exact hR.trans (congrArg (fun t => dualityMap (E := E) (M := (U ∩ V : Set M)) n
    (supportIn (U ∩ V) ((K ⊓ L : Compacts M) : Set M))
    (supportIn_isCompact (U ∩ V) ((K ⊓ L : Compacts M) : Set M) (K ⊓ L).isCompact hI)
    (p + 1) q ((Nat.add_right_comm p 1 q).trans h)
    (SupportedModTwoCohomology.neighborhoodEquiv (U ∩ V) ((K ⊓ L : Compacts M) : Set M)
      (hU.inter hV) (K ⊓ L).isCompact.isClosed hI (p + 1) t)) hδ)

end NoExoticSixSphere.CompactSupportedCapMap
