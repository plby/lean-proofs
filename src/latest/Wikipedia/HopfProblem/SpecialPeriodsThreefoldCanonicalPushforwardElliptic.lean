import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticLocalExtension
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGeneric

/-!
# Unconditional elliptic extension of the actual canonical pushforward coefficient

For every original base open and every holomorphic section of the
original canonical bundle on its full preimage, the actual descended
generic coefficient extends holomorphically across the second elliptic
value.  The neighborhood and its base section are genuine original
sphere objects, and agreement holds pointwise on the entire overlap.
The proof uses the actual section recovery from scalar descent and the
proved native order-two versus base order-four removability argument.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- An actual local holomorphic extension of the actual descended
coefficient at the second elliptic value, for every canonical section.
No local representation, order, or removability hypothesis is supplied. -/
theorem exists_local_extension (U : Opens RiemannSphere) (s : PreimageSection U)
    (hU : ((1 : ℂ) : RiemannSphere) ∈ U) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U), ((1 : ℂ) : RiemannSphere) ∈ V ∧
      ∃ H : Threefold.BaseSection V, ∀ p : V, ∀ hp : (p : RiemannSphere) ∈ Generic.genericBase,
        H p = Generic.baseCoefficient U s ⟨p, ⟨hVU p.property, hp⟩⟩ := by
  have hW : ((1 : ℂ) : RiemannSphere) ∉ Generic.genericPart U :=
    fun h => h.2.2 rfl
  have hWfinite : ∀ q : ℂ, (q : RiemannSphere) ∈ U → q ≠ 1 →
      (q : RiemannSphere) ∈ Generic.genericPart U := by
    intro q hq hn
    exact ⟨hq, by simp, fun he => hn (OnePoint.coe_injective he)⟩
  have hrep : ∀ x : Threefold.basePreimage U,
      ∀ hxW : Threefold.projectionSphere x.val ∈ Generic.genericPart U,
      x.val ∈ Threefold.regularLocus →
      s x = Generic.baseCoefficient U s ⟨Threefold.projectionSphere x.val, hxW⟩ •
        GlobalMeromorphicSection.rawSection x.val := by
    intro x hxW _
    exact (Generic.baseCoefficient_smul_rawSection U s ⟨x.val, hxW⟩).symm
  obtain ⟨V, hVU, hV, H, hH⟩ := exists_baseSection_extension_of_nativeSection U
    (Generic.genericPart U) s hU hW hWfinite (Generic.baseCoefficient U s) hrep
  exact ⟨V, hVU, hV, H, fun p hp => hH p ⟨hVU p.property, hp⟩⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
