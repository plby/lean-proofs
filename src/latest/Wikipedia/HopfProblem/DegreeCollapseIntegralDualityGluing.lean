import Wikipedia.HopfProblem.DegreeCollapseIntegralCapOpenCover
import Wikipedia.HopfProblem.DegreeCollapseIntegralPrimitiveSupportRestriction
import Wikipedia.HopfProblem.DegreeCollapseIntegralEuclideanLikeDuality

/-!
# Euclidean base and binary gluing for actual integral cap duality

The property quantifies over coherent primitive families on the actual
space, so that it can be used on every open subset. Original excision
preserves those hypotheses. The Euclidean calculation and the signed
five lemma prove the base case and binary closure, including degree
zero and above-dimension cohomology. Global assembly remains separate.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X]
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover in
/-- Above-dimension vanishing glues through the original integral compact-support exact row. -/
theorem subsingleton_of_cover (p : ℕ) [Subsingleton (Cohomology U p)]
    [Subsingleton (Cohomology V p)] [Subsingleton (Cohomology (U ∩ V : Set X) (p + 1))] :
    Subsingleton (Cohomology X p) := by
  have hz (a : Cohomology X p) : a = 0 := by
    obtain ⟨b, hb⟩ := (IntegralCompactSupportMayerVietoris.exact_right U V hU hV hcover p).ge
      (show IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover a = 0 from
        Subsingleton.elim _ _)
    exact hb.symm.trans
      ((congrArg (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p)
        (Subsingleton.elim b 0)).trans
          (IntegralCompactSupportMayerVietoris.differenceMap U V hU hV p).map_zero)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

open IntegralCoherentSupport IntegralCompactSupportCohomology

/-- Actual cap bijectivity for every coherent primitive family,
with the required endpoint vanishing. -/
def Duality (d : ℕ) (X : Type) [TopologicalSpace X] [T2Space X] : Prop :=
  (∀ (c : ClassFamily X d) (hc : Compatible X d c), Primitive X d c →
    ∀ p q (h : p + q = d), Function.Bijective (IntegralCompactSupportCap.withClasses h c hc)) ∧
  ∀ p, d < p → Subsingleton (Cohomology X p)

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}

/-- Apply open-subset duality to the family restricted by original integral excision. -/
theorem Duality.capOnOpen_bijective (U : Set X) (hU : IsOpen U) (hD : Duality d U)
    (c : ClassFamily X d) (hc : Compatible X d c) (hp : Primitive X d c)
    (p q : ℕ) (h : p + q = d) : Function.Bijective (capOnOpen U hU c hc h) :=
  hD.1 (restrictToOpen U hU c) (restrictToOpen_compatible U hU c hc)
    (restrictToOpen_primitive U hU c hp) p q h

section Euclidean

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The actual Euclidean calculation proves the universal primitive-family property. -/
theorem duality_of_euclidean_homeomorph (e : X ≃ₜ E) : Duality (n + 3) X := by
  refine ⟨fun c hc hp p q h =>
    IntegralEuclideanLikeCap.withClasses_bijective n e c hc hp p q h, ?_⟩
  intro p hp
  exact IntegralEuclideanLikeCap.cohomology_subsingleton n e p (Nat.ne_of_gt hp)

theorem euclidean_duality : Duality (n + 3) E :=
  duality_of_euclidean_homeomorph n (Homeomorph.refl E)

end Euclidean

variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover in
/-- Binary closure holds for the original cap maps in all complementary and endpoint degrees. -/
theorem Duality.of_open_cover (hDU : Duality d U) (hDV : Duality d V)
    (hDI : Duality d (U ∩ V : Set X)) : Duality d X := by
  constructor
  · intro c hc hp p q h
    exact IntegralCoherentSupport.bijective_of_cover c hc U V hU hV hcover
      (fun a b hab => hDU.capOnOpen_bijective U hU c hc hp a b hab)
      (fun a b hab => hDV.capOnOpen_bijective V hV c hc hp a b hab)
      (fun a b hab => hDI.capOnOpen_bijective (U ∩ V) (hU.inter hV) c hc hp a b hab)
      (hDI.2 (d + 1) (by omega)) p q h
  · intro p hp
    let := hDU.2 p hp
    let := hDV.2 p hp
    let := hDI.2 (p + 1) (by omega)
    exact subsingleton_of_cover U V hU hV hcover p

section Manifold

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

/-- Once the universal property is proved, it applies to the actual constructed manifold cap. -/
theorem Duality.constructedMap_bijective (hD : Duality (n + 3) M)
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (IntegralCompactSupportCap.dualityMap (E := E) n M p q h) :=
  hD.1 (manifoldFamily (E := E) n) (manifoldFamily_compatible (E := E) n)
    (manifoldFamily_primitive (E := E) n) p q h

end Manifold

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
