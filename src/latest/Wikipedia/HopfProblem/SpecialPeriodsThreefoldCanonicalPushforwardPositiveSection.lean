import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBasePoint

/-!
# The actual positive infinity section of the dual base line

The line is the already constructed dual of the original sphere ideal
bundle, with its unchanged native core.  The local coefficients `1` and
the reciprocal coordinate `w` glue to a globally holomorphic section.
Its sole zero is the actual point at infinity, including the chart centre.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The unchanged positive line, already constructed as the dual of the ideal line. -/
abbrev data := PowersBase.data

theorem data_eq_dual : data = CanonicalGlobalLineBundle.dual CanonicalGlobal.BaseTwist.data :=
  rfl

/-- The actual original native core, not a separately named divisor line. -/
abbrev bundle := data.core

theorem bundle_holomorphic : ContMDiffVectorBundle ω ℂ bundle.Fiber 𝓘(ℂ) :=
  PowersBase.bundle_holomorphic

/-- The full continuous complex-linear dual of each original ideal-bundle fibre. -/
abbrev fiberDualEquiv (p : RiemannSphere) :
    bundle.Fiber p ≃L[ℂ] (CanonicalGlobal.BaseTwist.bundle.Fiber p →L[ℂ] ℂ) :=
  PowersBase.fiberDualEquiv p

theorem fiberDualEquiv_localTriv (b : Bool) (p : RiemannSphere)
    (c : bundle.Fiber p) (v : CanonicalGlobal.BaseTwist.bundle.Fiber p) :
    fiberDualEquiv p c v =
      (bundle.localTriv b ⟨p, c⟩).2 * (CanonicalGlobal.BaseTwist.bundle.localTriv b ⟨p, v⟩).2 :=
  PowersBase.fiberDualEquiv_localTriv b p c v

/-- Literal local coefficients of the infinity-divisor section. -/
def coefficient : Bool → RiemannSphere → ℂ
  | false, _ => 1
  | true, p => CanonicalGlobal.BaseTwist.infinityCoordinate p

theorem coefficient_holomorphic (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (coefficient b) (data.baseSet b) := by
  cases b
  · exact contMDiffOn_const
  · exact CanonicalGlobal.BaseTwist.infinityCoordinate_holomorphicOn

/-- The local functions glue through the existing dual transition, which is `w`. -/
theorem coefficient_compatible : data.IsCompatible coefficient := by
  intro a b p hp
  cases a <;> cases b
  · change (↑((CanonicalGlobal.BaseTwist.data.transition false false p)⁻¹) : ℂ) * 1 = 1
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      CanonicalGlobal.BaseTwist.transition_self, inv_one, Units.val_one, one_mul]
  · rw [PowersBase.transition_false_true hp]
    exact mul_one _
  · rw [PowersBase.transition_true_false ⟨hp.2, hp.1⟩]
    exact CanonicalGlobal.BaseTwist.finiteCoordinate_mul_infinityCoordinate ⟨hp.2, hp.1⟩
  · change (↑((CanonicalGlobal.BaseTwist.data.transition true true p)⁻¹) : ℂ) *
      coefficient true p = coefficient true p
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      CanonicalGlobal.BaseTwist.transition_self, inv_one, Units.val_one, one_mul]

/-- The zero locus is asserted only on the actual chart, never at an omitted chart point. -/
theorem coefficient_eq_zero_iff (b : Bool) (p : RiemannSphere)
    (hp : p ∈ data.baseSet b) : coefficient b p = 0 ↔ p = (∞ : RiemannSphere) := by
  cases b
  · constructor
    · intro h
      exact (one_ne_zero h).elim
    · intro h
      subst p
      exact (infty_not_mem_finiteChart hp).elim
  · induction p using OnePoint.rec with
    | infty => simp only [coefficient, CanonicalGlobal.BaseTwist.infinityCoordinate_infty]
    | coe z =>
      have hz : z ≠ 0 := (coe_mem_infinityChart_iff z).mp hp
      simp only [coefficient, CanonicalGlobal.BaseTwist.infinityCoordinate_coe,
        inv_ne_zero hz, OnePoint.coe_ne_infty]

/-- The genuine global section in the unchanged native bundle fibres. -/
def sectionValue : ∀ p : RiemannSphere, bundle.Fiber p :=
  data.sectionFromLocal coefficient

def sectionMap (p : RiemannSphere) : bundle.TotalSpace := ⟨p, sectionValue p⟩

@[simp] theorem sectionMap_proj (p : RiemannSphere) : (sectionMap p).proj = p := rfl

/-- Holomorphicity holds into the original native bundle total space. -/
theorem sectionMap_holomorphic :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω sectionMap :=
  data.sectionFromLocal_holomorphic 𝓘(ℂ) coefficient coefficient_compatible
    coefficient_holomorphic

/-- The same section as a native bundled holomorphic section. -/
def holomorphicSection : ContMDiffSection 𝓘(ℂ) ℂ ω bundle.Fiber :=
  data.holomorphicSectionFromLocal 𝓘(ℂ) coefficient coefficient_compatible
    coefficient_holomorphic

@[simp] theorem holomorphicSection_apply (p : RiemannSphere) :
    holomorphicSection p = sectionValue p := rfl

theorem section_localCoefficient (b : Bool) {p : RiemannSphere}
    (hp : p ∈ data.baseSet b) :
    data.localCoefficient sectionValue b p = coefficient b p :=
  data.localCoefficient_sectionFromLocal coefficient coefficient_compatible b hp

/-- The actual native section has exactly one zero, the actual point at infinity. -/
theorem section_eq_zero_iff (p : RiemannSphere) :
    sectionValue p = 0 ↔ p = (∞ : RiemannSphere) :=
  coefficient_eq_zero_iff (data.indexAt p) p (data.mem_baseSet_at p)

theorem section_ne_zero_iff (p : RiemannSphere) :
    sectionValue p ≠ 0 ↔ p ≠ (∞ : RiemannSphere) :=
  not_congr (section_eq_zero_iff p)

theorem section_finite_coefficient (z : ℂ) :
    data.localCoefficient sectionValue false (z : RiemannSphere) = 1 :=
  section_localCoefficient false (coe_mem_finiteChart z)

/-- Literal `w`, including `w = 0`, in the unchanged reciprocal parametrization. -/
theorem section_infinity_coefficient (w : ℂ) :
    data.localCoefficient sectionValue true (RiemannSphere.infinityParametrization w) = w := by
  rw [section_localCoefficient true (infinityParametrization_mem w)]
  exact CanonicalGlobal.BaseTwist.infinityCoordinate_infinityParametrization w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive
