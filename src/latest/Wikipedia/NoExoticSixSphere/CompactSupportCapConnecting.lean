import Wikipedia.NoExoticSixSphere.CompactSupportedCapConnecting
import Wikipedia.NoExoticSixSphere.CompactSupportCapMap
import Wikipedia.NoExoticSixSphere.CompactSupportConnectingRepresentatives

/-!
# The actual compact-support cap connecting square

The compact-supported component square descends along the original
cofinal compact-support representatives. Both vertical maps use the
constructed fundamental classes, and both connecting maps are the
original maps obtained from their actual short exact sequences.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

open CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

omit [ChartedSpace E M] in
/-- A neighborhood representative retains the original compact-supported neighborhood cap. -/
theorem dualityMap_neighborhoodOf (U : Set M) (hU : IsOpen U) [ChartedSpace E U]
    (K : Compacts M) (hKU : (K : Set M) ⊆ U) (p q : ℕ) (h : p + q = n + 3)
    (a : Component M p K) :
    dualityMap (E := E) n U p q h (neighborhoodOf U hU K hKU p a) =
      CompactSupportedCapMap.dualityMap (E := E) n
        (SupportedRelativeHomology.supportIn U (K : Set M))
        (SupportedRelativeHomology.supportIn_isCompact U (K : Set M) K.isCompact hKU) p q h
        (SupportedModTwoCohomology.neighborhoodEquiv U (K : Set M)
          hU K.isCompact.isClosed hKU p a) := rfl

variable (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  [ChartedSpace E (U ∩ V : Set M)]

/-- The two genuine connecting maps commute with the original compact-support cap maps. -/
theorem dualityMap_connecting (p q : ℕ) (h : p + q + 1 = n + 3) (a : Cohomology M p) :
    ModTwoMayerVietoris.connecting U V hU hV hcover q
        (dualityMap (E := E) n M p (q + 1) ((Nat.add_assoc p q 1).symm.trans h) a) =
      dualityMap (E := E) n (U ∩ V : Set M) (p + 1) q ((Nat.add_right_comm p 1 q).trans h)
        (CompactSupportMayerVietoris.connecting U V hU hV p hcover a) := by
  obtain ⟨S, b, rfl⟩ := OpenCoverCompactSupports.exists_representative U V hU hV hcover p a
  let K := imageCompact U S.1
  let L := imageCompact V S.2
  have hKU : (K : Set M) ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hLV : (L : Set M) ⊆ V := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hconn := CompactSupportMayerVietoris.connecting_of_supports U V hU hV p hcover
    K L hKU hLV b
  apply (congrArg (ModTwoMayerVietoris.connecting U V hU hV hcover q)
    (dualityMap_of (E := E) n M p (q + 1) ((Nat.add_assoc p q 1).symm.trans h) (K ⊔ L) b)).trans
  apply (CompactSupportedCapMap.dualityMap_connecting (E := E) n U V hU hV hcover
    K L hKU hLV p q h b).trans
  apply (dualityMap_neighborhoodOf (E := E) n (U ∩ V) (hU.inter hV) (K ⊓ L)
    (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩) (p + 1) q ((Nat.add_right_comm p 1 q).trans h)
    (SupportedModTwoCohomology.connecting (K : Set M) (L : Set M)
      K.isCompact.isClosed L.isCompact.isClosed p b)).symm.trans
  exact congrArg (dualityMap (E := E) n (U ∩ V : Set M) (p + 1) q
    ((Nat.add_right_comm p 1 q).trans h)) hconn.symm

end NoExoticSixSphere.CompactSupportCapMap
