import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardExtension
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardElliptic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf

/-!
# Descent of every native canonical section to the actual vanishing ideal

The genuine generic coefficient of an arbitrary native canonical section
extends on every original sphere open. At the second elliptic point this
uses the proved order-four versus order-two removability argument; at
infinity it uses the actual regularized cusp frame. Density forces the
local extensions to agree, and the resulting actual holomorphic function
vanishes at infinity whenever infinity belongs to its domain.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Descent

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Actual local extension exists near every point of the original open;
the two exceptional points use their proved native geometric theorems. -/
theorem locally_extends (U : Opens RiemannSphere) (s : PreimageSection U) (p : U) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U), p.val ∈ V ∧
      ∃ h : Threefold.BaseSection V, ∀ q : V, ∀ hq : q.val ∈ Generic.genericBase,
        h q = Generic.baseCoefficient U s ⟨q.val, ⟨hVU q.property, hq⟩⟩ := by
  by_cases hpInf : p.val = (∞ : RiemannSphere)
  · refine ⟨Cusp.localBase U, Cusp.localBase_le U,
      ⟨p.property, hpInf ▸ Cusp.infty_mem_basePatch⟩, Cusp.localCoefficient U s, ?_⟩
    exact Cusp.localCoefficient_eq_generic U s
  · by_cases hpOne : p.val = ((1 : ℂ) : RiemannSphere)
    · obtain ⟨V, hVU, hV, h, hh⟩ := Elliptic.exists_local_extension U s
        (hpOne ▸ p.property)
      exact ⟨V, hVU, hpOne ▸ hV, h, hh⟩
    · refine ⟨Generic.genericPart U, Generic.genericPart_le U,
        ⟨p.property, hpInf, hpOne⟩, Generic.baseCoefficient U s, ?_⟩
      intro q hq
      rfl

/-- The actual generic coefficient has a unique holomorphic extension
on the entire original base open. -/
theorem existsUnique_coefficient (U : Opens RiemannSphere) (s : PreimageSection U) :
    ∃! h : Threefold.BaseSection U, ∀ p : U, ∀ hp : p.val ∈ Generic.genericBase,
      h p = Generic.baseCoefficient U s ⟨p.val, ⟨p.property, hp⟩⟩ :=
  CanonicalPushforwardExtension.existsUnique_extension 𝓘(ℂ) RiemannSphere
    Generic.genericBase U Generic.genericBase_dense (Generic.baseCoefficient U s)
      (locally_extends U s)

/-- The actual holomorphic extension of the native section's generic coefficient. -/
def coefficient (U : Opens RiemannSphere) (s : PreimageSection U) : Threefold.BaseSection U :=
  (existsUnique_coefficient U s).choose

theorem coefficient_eq_generic (U : Opens RiemannSphere) (s : PreimageSection U)
    (p : U) (hp : p.val ∈ Generic.genericBase) :
    coefficient U s p = Generic.baseCoefficient U s ⟨p.val, ⟨p.property, hp⟩⟩ :=
  (existsUnique_coefficient U s).choose_spec.1 p hp

/-- Any actual holomorphic extension is this same coefficient. -/
theorem coefficient_unique (U : Opens RiemannSphere) (s : PreimageSection U)
    (h : Threefold.BaseSection U)
    (hh : ∀ p : U, ∀ hp : p.val ∈ Generic.genericBase,
      h p = Generic.baseCoefficient U s ⟨p.val, ⟨p.property, hp⟩⟩) :
    h = coefficient U s :=
  (existsUnique_coefficient U s).choose_spec.2 h hh

/-- On the full cusp base open, the glued extension is the actual
reciprocal-coordinate multiple of the descended native frame ratio. -/
theorem coefficient_eq_cusp (U : Opens RiemannSphere) (s : PreimageSection U)
    (p : Cusp.localBase U) :
    coefficient U s ⟨p.val, p.property.1⟩ = Cusp.localCoefficient U s p := by
  have he : HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere
      (Cusp.localBase_le U) (coefficient U s) = Cusp.localCoefficient U s := by
    apply CanonicalPushforwardExtension.section_eq_of_dense 𝓘(ℂ) RiemannSphere
      Generic.genericBase_dense (Cusp.localBase U)
    intro q hq
    exact (coefficient_eq_generic U s ⟨q.val, q.property.1⟩ hq).trans
      (Cusp.localCoefficient_eq_generic U s q hq).symm
  exact congrArg (fun h : Threefold.BaseSection (Cusp.localBase U) => h p) he

/-- The actual coefficient vanishes at infinity; the order-one ideal
condition is a theorem about the genuine holomorphic function. -/
theorem coefficient_infty (U : Opens RiemannSphere) (s : PreimageSection U)
    (hU : (∞ : RiemannSphere) ∈ U) : coefficient U s ⟨∞, hU⟩ = 0 :=
  (coefficient_eq_cusp U s ⟨∞, Cusp.infty_mem_localBase hU⟩).trans
    (Cusp.localCoefficient_infty s hU)

/-- The descended section of the actual ideal of infinity. -/
def idealSection (U : Opens RiemannSphere) (s : PreimageSection U) : NegativeOneSection U :=
  ⟨coefficient U s, coefficient_infty U s⟩

@[simp] theorem idealSection_val (U : Opens RiemannSphere) (s : PreimageSection U) :
    (idealSection U s).val = coefficient U s := rfl

theorem idealSection_eq_generic (U : Opens RiemannSphere) (s : PreimageSection U)
    (p : U) (hp : p.val ∈ Generic.genericBase) :
    (idealSection U s).val p =
      Generic.baseCoefficient U s ⟨p.val, ⟨p.property, hp⟩⟩ :=
  coefficient_eq_generic U s p hp

/-- Recovery holds in the original native canonical fibre on the full
generic preimage, not merely in an assigned scalar presentation. -/
theorem coefficient_smul_rawSection (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (Generic.genericPart U)) :
    coefficient U s (Threefold.baseProjection U (Generic.preimagePoint U x)) •
      GlobalMeromorphicSection.rawSection x.val = s (Generic.preimagePoint U x) :=
  (congrArg (fun c : ℂ => c • GlobalMeromorphicSection.rawSection x.val)
    (coefficient_eq_generic U s
      (Threefold.baseProjection U (Generic.preimagePoint U x)) x.property.2)).trans
      (Generic.baseCoefficient_smul_rawSection U s x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Descent
