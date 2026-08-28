import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCuspCoefficient
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGeneric

/-!
# The actual generic coefficient extends at infinity and vanishes there

The descended cusp coefficient agrees with the already constructed
generic base coefficient. The comparison is forced by the two exact
representations in the same original nonzero canonical fibre and by
surjectivity of the actual sphere projection. Thus the extension concerns
the genuine generic coefficient of every native canonical section.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Equality with the actual generic descended coefficient on the entire overlap. -/
theorem localCoefficient_eq_generic (U : Opens RiemannSphere) (s : PreimageSection U)
    (p : localBase U) (hp : p.val ∈ Generic.genericBase) :
    localCoefficient U s p = Generic.baseCoefficient U s
      ⟨p.val, ⟨p.property.1, hp⟩⟩ := by
  obtain ⟨x, hx⟩ := Threefold.baseProjection_surjective (localBase U) p
  have hproj : Threefold.projectionSphere x.val = p.val := congrArg Subtype.val hx
  have hxg : Threefold.projectionSphere x.val ∈ Generic.genericBase := hproj.symm ▸ hp
  let xg : Threefold.basePreimage (Generic.genericPart U) :=
    ⟨x.val, ⟨x.property.1, hxg⟩⟩
  have hxr : x.val ∈ Threefold.regularLocus :=
    regular_of_projection_ne_infty U x hxg.1
  have hc := localCoefficient_smul_regular U s x hxr
  have hg := Generic.baseCoefficient_smul_regular U s xg hxr
  have hframe : id (α := ℂ) (GlobalRegular.globalSection ⟨x.val, hxr⟩) ≠ 0 :=
    GlobalRegular.globalSection_ne_zero ⟨x.val, hxr⟩
  have heq : localCoefficient U s (Threefold.baseProjection (localBase U) x) =
      Generic.baseCoefficient U s (Threefold.baseProjection (Generic.genericPart U) xg) := by
    apply mul_right_cancel₀ hframe
    exact hc.trans hg.symm
  have hbase : Threefold.baseProjection (Generic.genericPart U) xg =
      (⟨p.val, ⟨p.property.1, hp⟩⟩ : Generic.genericPart U) := Subtype.ext hproj
  rw [hx, hbase] at heq
  exact heq

/-- Every actual canonical section has a holomorphic extension of its true generic coefficient
near the cusp value, and that extension lies in the ideal of infinity. -/
theorem exists_local_extension (U : Opens RiemannSphere) (s : PreimageSection U)
    (hU : (∞ : RiemannSphere) ∈ U) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U) (hV : (∞ : RiemannSphere) ∈ V),
      ∃ H : Threefold.BaseSection V,
        (∀ (p : V) (hp : p.val ∈ Generic.genericBase), H p =
          Generic.baseCoefficient U s ⟨p.val, ⟨hVU p.property, hp⟩⟩) ∧
        H ⟨∞, hV⟩ = 0 := by
  refine ⟨localBase U, localBase_le U, infty_mem_localBase hU, localCoefficient U s,
    ?_, localCoefficient_infty s hU⟩
  intro p hp
  exact localCoefficient_eq_generic U s p hp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp
