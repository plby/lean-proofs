import Wikipedia.HopfProblem.DegreeCollapseIntegralSupportedCapConnecting
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportConnectingRepresentatives

/-!
# The original signed integral compact-support cap connecting square

The supported square descends through the actual cofinal compact pairs.
For the constructed manifold family, both cap maps are exactly the
original maps defined from the primitive fundamental classes. Neither
an orientation choice nor a compatible-class premise is added there.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

open SingularMayerVietoris IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X] [T2Space X] {d : ℕ}
  (c : ClassFamily X d) (hc : Compatible X d c)
  (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

/-- The actual compact-support connecting map and original homological
connecting retain the sign. -/
theorem withClasses_connecting (p q : ℕ) (h : p + q + 1 = d) (a : Cohomology X p) :
    connectingHomomorphism U V hU hV hcover q
        (IntegralCompactSupportCap.withClasses (p := p) (q := q + 1) (by omega) c hc a) =
      -((-1 : ℤ) ^ p) • capOnOpen (U ∩ V) (hU.inter hV) c hc
        (p := p + 1) (q := q) (by omega)
        (IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover a) := by
  obtain ⟨S, b, rfl⟩ := IntegralOpenCoverCompactSupports.exists_representative U V hU hV hcover p a
  let K := imageCompact U S.1
  let L := imageCompact V S.2
  have hKU : (K : Set X) ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hLV : (L : Set X) ⊆ V := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hconn := IntegralCompactSupportMayerVietoris.connecting_of_supports U V hU hV p hcover
    K L hKU hLV b
  exact (congrArg (connectingHomomorphism U V hU hV hcover q)
    (IntegralCompactSupportCap.withClasses_of (p := p) (q := q + 1) (by omega)
      c hc (K ⊔ L) b)).trans
    ((component_connecting c hc U V hU hV hcover K L hKU hLV p q h b).trans
      (congrArg (fun t => -((-1 : ℤ) ^ p) • capOnOpen (U ∩ V) (hU.inter hV) c hc
        (p := p + 1) (q := q) (by omega) t) hconn.symm))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCoherentSupport

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap

open SingularMayerVietoris IntegralCompactSupportCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]
  (U V : Set M) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

/-- Both original connecting maps satisfy the signed square for the constructed fundamental caps. -/
theorem dualityMap_connecting (p q : ℕ) (h : p + q + 1 = n + 3) (a : Cohomology M p) :
    connectingHomomorphism U V hU hV hcover q
        (dualityMap (E := E) n M p (q + 1) (by omega) a) =
      -((-1 : ℤ) ^ p) • IntegralOpenFundamentalClass.dualityMap (E := E) n
        (U ∩ V) (hU.inter hV) (p + 1) q (by omega)
        (IntegralCompactSupportMayerVietoris.connecting U V hU hV p hcover a) :=
  IntegralCoherentSupport.withClasses_connecting
    (IntegralCoherentSupport.manifoldFamily (E := E) n)
    (IntegralCoherentSupport.manifoldFamily_compatible (E := E) n)
    U V hU hV hcover p q h a

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCap
