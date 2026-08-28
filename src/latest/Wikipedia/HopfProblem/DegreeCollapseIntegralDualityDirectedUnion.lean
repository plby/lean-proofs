import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportDirectedCover
import Wikipedia.HopfProblem.DegreeCollapseIntegralDualityGluing

/-!
# Directed-open-union closure of actual integral cap duality

Original compact-support representatives and integral singular classes
lift to cover members. An actual bounding chain detects zero in a
larger member, where cap is injective. The original cap maps and
above-dimension vanishing consequently pass to the directed union.
No homology inclusion is assumed injective.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open SingularMayerVietoris NoExoticSixSphere IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d) (hc : Compatible X d c)
  {ι : Type*} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)

include hdir hcover

/-- An actual ambient cap zero is detected in a larger member of the directed cover. -/
theorem eq_zero_of_directed_cap_zero (p q : ℕ) (h : p + q = d)
    (hD : ∀ i, Function.Injective (capOnOpen (U i) (hU i) c hc h))
    (a : Cohomology X p) (ha : IntegralCompactSupportCap.withClasses h c hc a = 0) : a = 0 := by
  obtain ⟨i, b, rfl⟩ := exists_directed_cover_representative U hU hdir hcover p a
  have hi : singularHomologyMap (subtypeInclusion (U i)) q
      (capOnOpen (U i) (hU i) c hc h b) = 0 :=
    (withClasses_inclusion c hc (U i) (hU i) h b).trans ha
  obtain ⟨j, hij, hj⟩ := DirectedOpenCover.homology_eventually_zero U hU hdir hcover
    (ModuleCat.of ℤ ℤ) i q (capOnOpen (U i) (hU i) c hc h b) hi
  let f := subsetInclusion hij
  let hf := subsetInclusion_isOpenEmbedding hij (hU i)
  have hb : openMap f hf p b = 0 := hD j
    ((capOnOpen_subsetInclusion c hc hij (hU i) (hU j) h b).symm.trans
      (hj.trans (capOnOpen (U j) (hU j) c hc h).map_zero.symm))
  exact (inclusion_subsetInclusion hij (hU i) (hU j) p b).symm.trans
    ((congrArg (inclusion (U j) (hU j) p) hb).trans (inclusion (U j) (hU j) p).map_zero)

/-- Bijections on all cover members give bijectivity of the original ambient integral cap. -/
theorem bijective_of_directed_cover (p q : ℕ) (h : p + q = d)
    (hD : ∀ i, Function.Bijective (capOnOpen (U i) (hU i) c hc h)) :
    Function.Bijective (IntegralCompactSupportCap.withClasses h c hc) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    apply eq_zero_of_directed_cap_zero c hc U hU hdir hcover p q h (fun i => (hD i).1)
    exact ((IntegralCompactSupportCap.withClasses h c hc).map_sub a b).trans
      (sub_eq_zero.mpr hab)
  · intro a
    obtain ⟨i, b, hb⟩ := DirectedOpenCover.exists_homology_class U hU hdir hcover
      (ModuleCat.of ℤ ℤ) q a
    obtain ⟨z, hz⟩ := (hD i).2 b
    refine ⟨inclusion (U i) (hU i) p z, ?_⟩
    exact (withClasses_inclusion c hc (U i) (hU i) h z).symm.trans
      ((congrArg (singularHomologyMap (subtypeInclusion (U i)) q) hz).trans hb)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

open IntegralCoherentSupport IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  {ι : Type*} [Nonempty ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)

include hU hdir hcover in
/-- The universal primitive-family duality property is closed under directed open covers. -/
theorem Duality.of_directed_cover (hD : ∀ i, Duality d (U i)) : Duality d X := by
  constructor
  · intro c hc hp p q h
    exact IntegralCoherentSupport.bijective_of_directed_cover c hc U hU hdir hcover p q h
      (fun i => (hD i).capOnOpen_bijective (U i) (hU i) c hc hp p q h)
  · intro p hp
    exact subsingleton_of_directed_cover U hU hdir hcover p (fun i => (hD i).2 p hp)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
