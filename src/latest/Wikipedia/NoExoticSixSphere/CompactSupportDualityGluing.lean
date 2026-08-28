import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenCover
import Wikipedia.NoExoticSixSphere.CompactSupportCapHomeomorph
import Wikipedia.NoExoticSixSphere.EuclideanCompactSupportDuality

/-!
# Euclidean base case and binary gluing for original cap duality

The property records bijectivity of the actual cap maps and vanishing
of actual compact-support cohomology above the dimension. The latter
supplies the homological degree-zero gluing endpoint. The Euclidean
case, homeomorphism transport, and binary open-cover closure are proved.
Directed-union and arbitrary manifold-cover assembly remain separate
obligations; no global duality assumption is introduced as an instance.
-/

noncomputable section

namespace NoExoticSixSphere.CompactSupportCohomology

variable {M : Type} [TopologicalSpace M] [T2Space M]
  (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover in
/-- Actual compact-support vanishing glues using the original exact sequence. -/
theorem subsingleton_of_cover (p : ℕ) [Subsingleton (Cohomology U p)]
    [Subsingleton (Cohomology V p)] [Subsingleton (Cohomology (U ∩ V : Set M) (p + 1))] :
    Subsingleton (Cohomology M p) := by
  have hz (a : Cohomology M p) : a = 0 := by
    obtain ⟨b, hb⟩ := (CompactSupportMayerVietoris.exact_right U V hU hV hcover p).ge
      (show CompactSupportMayerVietoris.connecting U V hU hV p hcover a = 0 from
        Subsingleton.elim _ _)
    exact hb.symm.trans ((congrArg (CompactSupportMayerVietoris.differenceMap U V hU hV p)
      (Subsingleton.elim b 0)).trans
        (CompactSupportMayerVietoris.differenceMap U V hU hV p).map_zero)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end NoExoticSixSphere.CompactSupportCohomology

namespace NoExoticSixSphere.CompactSupportCapMap

open CompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Bijectivity of the actual caps, with actual cohomology vanishing beyond their dimension. -/
def Duality (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] : Prop :=
  (∀ p q (h : p + q = n + 3), Function.Bijective (dualityMap (E := E) n M p q h)) ∧
    ∀ p, n + 3 < p → Subsingleton (Cohomology M p)

/-- The checked Euclidean calculation supplies both parts of the actual duality property. -/
theorem euclidean_duality : Duality (E := E) n E := by
  refine ⟨euclidean_bijective E n, ?_⟩
  intro p hp
  exact euclidean_subsingleton E n p (Nat.ne_of_gt hp)

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y]

/-- Both parts transport along the original homeomorphism-induced maps. -/
theorem Duality.of_homeomorph (e : X ≃ₜ Y) (hD : Duality (E := E) n X) :
    Duality (E := E) n Y := by
  refine ⟨fun p q h => bijective_of_homeomorph (E := E) n e p q h (hD.1 p q h), ?_⟩
  intro p hp
  let := hD.2 p hp
  exact (homeomorphEquiv e p).symm.injective.subsingleton

/-- An actual charted space homeomorphic to the full Euclidean model has actual cap duality. -/
theorem duality_of_euclidean_homeomorph (e : E ≃ₜ X) : Duality (E := E) n X :=
  Duality.of_homeomorph (E := E) n e (euclidean_duality (E := E) n)

variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
  [ChartedSpace E U] [ChartedSpace E V] [ChartedSpace E (U ∩ V : Set X)]

include hU hV hcover in
/-- Binary open-cover closure retains the original cap maps in every degree. -/
theorem Duality.of_open_cover (hDU : Duality (E := E) n U) (hDV : Duality (E := E) n V)
    (hDI : Duality (E := E) n (U ∩ V : Set X)) : Duality (E := E) n X := by
  refine ⟨CompactSupportCapMayerVietoris.bijective_of_cover (E := E) n U V hU hV hcover
    hDU.1 hDV.1 hDI.1 (hDI.2 (n + 4) (by omega)), ?_⟩
  intro p hp
  let := hDU.2 p hp
  let := hDV.2 p hp
  let := hDI.2 (p + 1) (by omega)
  exact subsingleton_of_cover U V hU hV hcover p

end NoExoticSixSphere.CompactSupportCapMap
