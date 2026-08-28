import Wikipedia.HopfProblem.DegreeCollapseIntegralCoherentCapNaturality
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCapConnecting

/-!
# The original signed integral compact-support cap diagram

The pair of cap maps has signs (+,-), matching cohomological difference
with homological sum. The two inclusion squares commute, and the
connecting square has precisely the proved integer factor -(-1)^p.
All groups and maps are the original integral constructions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open FirstHurewicz SingularMayerVietoris IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d) (hc : Compatible X d c)
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)

/-- The actual cap maps with the signs required by the two original exact sequences. -/
def productMap {p q : ℕ} (h : p + q = d) :
    (Cohomology U p × Cohomology V p) →ₗ[ℤ]
      (SingularHomology U q × SingularHomology V q) :=
  (capOnOpen U hU c hc h).prodMap (-capOnOpen V hV c hc h)

theorem productMap_bijective {p q : ℕ} (h : p + q = d)
    (hDU : Function.Bijective (capOnOpen U hU c hc h))
    (hDV : Function.Bijective (capOnOpen V hV c hc h)) :
    Function.Bijective (productMap c hc U V hU hV h) := by
  constructor
  · intro a b hab
    exact Prod.ext (hDU.1 (congrArg Prod.fst hab))
      (hDV.1 (neg_injective (congrArg Prod.snd hab)))
  · intro b
    obtain ⟨aU, haU⟩ := hDU.2 b.1
    obtain ⟨aV, haV⟩ := hDV.2 (-b.2)
    refine ⟨(aU, aV), Prod.ext haU ?_⟩
    exact (congrArg Neg.neg haV).trans (neg_neg b.2)

/-- The actual cohomological overlap maps match the original signed intersection map. -/
theorem first_square {p q : ℕ} (h : p + q = d) :
    (leftHomologyMap U V q).comp (capOnOpen (U ∩ V) (hU.inter hV) c hc h) =
      (productMap c hc U V hU hV h).comp
        (IntegralCompactSupportMayerVietoris.firstMap U V hU hV p) := by
  apply LinearMap.ext
  intro a
  apply (leftHomologyMap_apply U V q (capOnOpen (U ∩ V) (hU.inter hV) c hc h a)).trans
  exact Prod.ext
    (capOnOpen_subsetInclusion c hc (Set.inter_subset_left : U ∩ V ⊆ U)
      (hU.inter hV) hU h a)
    (congrArg Neg.neg
      (capOnOpen_subsetInclusion c hc (Set.inter_subset_right : U ∩ V ⊆ V)
        (hU.inter hV) hV h a))

/-- The original homological sum matches the cohomological difference through the signed pair. -/
theorem second_square {p q : ℕ} (h : p + q = d) :
    (rightHomologyMap U V q).comp (productMap c hc U V hU hV h) =
      (IntegralCompactSupportCap.withClasses h c hc).comp
        (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p) := by
  apply LinearMap.ext
  intro a
  apply (rightHomologyMap_apply U V q (productMap c hc U V hU hV h a)).trans
  change singularHomologyMap (subtypeInclusion U) q (capOnOpen U hU c hc h a.1) +
      singularHomologyMap (subtypeInclusion V) q (-capOnOpen V hV c hc h a.2) =
    IntegralCompactSupportCap.withClasses h c hc (inclusion U hU p a.1 - inclusion V hV p a.2)
  rw [map_neg, map_sub, withClasses_inclusion, withClasses_inclusion, sub_eq_add_neg]

/-- Both original connecting maps retain the integer sign in the actual linear-map square. -/
theorem connecting_square (hcover : U ∪ V = Set.univ) {p q : ℕ} (h : p + q + 1 = d) :
    (connectingHomomorphism U V hU hV hcover q).comp
        (IntegralCompactSupportCap.withClasses (p := p) (q := q + 1) (by omega) c hc) =
      (-((-1 : ℤ) ^ p) • capOnOpen (U ∩ V) (hU.inter hV) c hc
        (p := p + 1) (q := q) (by omega)).comp
          (IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover) :=
  LinearMap.ext (withClasses_connecting c hc U V hU hV hcover p q h)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport
