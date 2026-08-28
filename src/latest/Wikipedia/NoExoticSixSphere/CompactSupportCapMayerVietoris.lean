import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenEmbedding
import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenInclusion
import Wikipedia.NoExoticSixSphere.CompactSupportCapConnecting
import Wikipedia.NoExoticSixSphere.ModTwoMayerVietorisExact

/-!
# The original cap maps form the Mayer--Vietoris comparison diagram

The product vertical map has signs `(+,-)`, so that the genuine
cohomological difference map corresponds to the genuine homological
sum map. All three squares are proved for the actual cap maps.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMayerVietoris

open CompactSupportCapMap CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (U V : Set M) [ChartedSpace E U] [ChartedSpace E V]

/-- The two original cap maps with the signs required by the actual two sequences. -/
def productMap (p q : ℕ) (h : p + q = n + 3) :
    (Cohomology U p × Cohomology V p) →ₗ[ℤ] (ModHomology 2 U q × ModHomology 2 V q) :=
  (dualityMap (E := E) n U p q h).prodMap (-dualityMap (E := E) n V p q h)

omit [ChartedSpace E M] in
/-- Bijectivity of the two actual cap maps gives bijectivity of their signed product. -/
theorem productMap_bijective (p q : ℕ) (h : p + q = n + 3)
    (hDU : Function.Bijective (dualityMap (E := E) n U p q h))
    (hDV : Function.Bijective (dualityMap (E := E) n V p q h)) :
    Function.Bijective (productMap (E := E) n U V p q h) := by
  constructor
  · intro a b hab
    exact Prod.ext (hDU.1 (congrArg Prod.fst hab))
      (hDV.1 (neg_injective (congrArg Prod.snd hab)))
  · intro b
    obtain ⟨aU, haU⟩ := hDU.2 b.1
    obtain ⟨aV, haV⟩ := hDV.2 (-b.2)
    refine ⟨(aU, aV), Prod.ext haU ?_⟩
    change -dualityMap (E := E) n V p q h aV = b.2
    rw [haV, neg_neg]

variable (hU : IsOpen U) (hV : IsOpen V) [ChartedSpace E (U ∩ V : Set M)]

omit [ChartedSpace E M] [ChartedSpace E V] in
/-- Cap commutes with the original left overlap inclusion. -/
theorem left_square (p q : ℕ) (h : p + q = n + 3)
    (a : Cohomology (U ∩ V : Set M) p) :
    dualityMap (E := E) n U p q h (CompactSupportMayerVietoris.leftMap U V hU hV p a) =
      modHomologyMap 2 (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) q
        (dualityMap (E := E) n (U ∩ V : Set M) p q h a) :=
  dualityMap_openEmbedding (E := E) n (subsetInclusion Set.inter_subset_left)
    (subsetInclusion_isOpenEmbedding Set.inter_subset_left (hU.inter hV)) p q h a

omit [ChartedSpace E M] [ChartedSpace E U] in
/-- Cap commutes with the original right overlap inclusion. -/
theorem right_square (p q : ℕ) (h : p + q = n + 3)
    (a : Cohomology (U ∩ V : Set M) p) :
    dualityMap (E := E) n V p q h (CompactSupportMayerVietoris.rightMap U V hU hV p a) =
      modHomologyMap 2 (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) q
        (dualityMap (E := E) n (U ∩ V : Set M) p q h a) :=
  dualityMap_openEmbedding (E := E) n (subsetInclusion Set.inter_subset_right)
    (subsetInclusion_isOpenEmbedding Set.inter_subset_right (hU.inter hV)) p q h a

omit [ChartedSpace E M] in
/-- The first square uses the actual signed homological intersection map. -/
theorem first_square (p q : ℕ) (h : p + q = n + 3) :
    (ModTwoMayerVietoris.firstMap U V q).comp
        (dualityMap (E := E) n (U ∩ V : Set M) p q h) =
      (productMap (E := E) n U V p q h).comp
        (CompactSupportMayerVietoris.firstMap U V hU hV p) := by
  apply LinearMap.ext
  intro a
  apply (ModTwoMayerVietoris.firstMap_apply U V q
    (dualityMap (E := E) n (U ∩ V : Set M) p q h a)).trans
  exact Prod.ext (left_square (E := E) n U V hU hV p q h a).symm
    (congrArg Neg.neg (right_square (E := E) n U V hU hV p q h a).symm)

omit [ChartedSpace E (U ∩ V : Set M)] in
/-- The actual homological sum and cohomological difference commute with the signed caps. -/
theorem second_square (p q : ℕ) (h : p + q = n + 3) :
    (ModTwoMayerVietoris.secondMap U V q).comp (productMap (E := E) n U V p q h) =
      (dualityMap (E := E) n M p q h).comp
        (CompactSupportMayerVietoris.differenceMap U V hU hV p) := by
  apply LinearMap.ext
  intro a
  apply (ModTwoMayerVietoris.secondMap_apply U V q
    (productMap (E := E) n U V p q h a)).trans
  change modHomologyMap 2 (subtypeInclusion U) q (dualityMap (E := E) n U p q h a.1) +
      modHomologyMap 2 (subtypeInclusion V) q (-dualityMap (E := E) n V p q h a.2) =
    dualityMap (E := E) n M p q h (inclusion U hU p a.1 - inclusion V hV p a.2)
  rw [map_neg, map_sub, dualityMap_openInclusion, dualityMap_openInclusion, sub_eq_add_neg]

variable (hcover : U ∪ V = Set.univ)

omit [ChartedSpace E U] [ChartedSpace E V] in
/-- The connecting square retains both original connecting maps and both actual caps. -/
theorem connecting_square (p q : ℕ) (h : p + q + 1 = n + 3) :
    (ModTwoMayerVietoris.connecting U V hU hV hcover q).comp
        (dualityMap (E := E) n M p (q + 1) ((Nat.add_assoc p q 1).symm.trans h)) =
      (dualityMap (E := E) n (U ∩ V : Set M) (p + 1) q
        ((Nat.add_right_comm p 1 q).trans h)).comp
          (CompactSupportMayerVietoris.connecting U V hU hV p hcover) :=
  LinearMap.ext (dualityMap_connecting (E := E) n U V hU hV hcover p q h)

end NoExoticSixSphere.CompactSupportCapMayerVietoris
