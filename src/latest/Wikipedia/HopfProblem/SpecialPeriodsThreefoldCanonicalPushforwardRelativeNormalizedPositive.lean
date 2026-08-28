import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeNormalizedBasic

/-!
# The actual positive divisor of the normalized relative pushforward

The image of the normalized relative section is the existing native
positive-line section on the sphere. Its genuine finite and reciprocal
bundle coefficients are `1` and `w`, so its base zero divisor is the
reduced point at infinity. The zero and order assertions here concern
this base pushforward image, not the relative section on the threefold.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The actual value of the image under the proved global direct-image equivalence. -/
def normalizedPushforwardValue (p : RiemannSphere) : Positive.bundle.Fiber p :=
  canonicalSectionPositiveEquiv ⊤ (normalizedSection ⊤) ⟨p, trivial⟩

@[simp] theorem normalizedPushforwardValue_eq_sectionValue (p : RiemannSphere) :
    normalizedPushforwardValue p = Positive.sectionValue p :=
  normalizedSection_positive_apply ⊤ ⟨p, trivial⟩

/-- The normalization agrees with the original Cartier section in the original fibres. -/
theorem normalizedPushforwardValue_eq_rawSection (p : RiemannSphere) :
    normalizedPushforwardValue p = Positive.actualCartier.rawSection p :=
  (normalizedPushforwardValue_eq_sectionValue p).trans (Positive.actualCartier_rawSection p).symm

theorem normalizedPushforwardValue_eq : normalizedPushforwardValue = Positive.sectionValue :=
  funext normalizedPushforwardValue_eq_sectionValue

/-- The corresponding map to the original positive bundle total space. -/
def normalizedPushforwardMap (p : RiemannSphere) : Positive.bundle.TotalSpace :=
  ⟨p, normalizedPushforwardValue p⟩

@[simp] theorem normalizedPushforwardMap_proj (p : RiemannSphere) :
    (normalizedPushforwardMap p).proj = p := rfl

theorem normalizedPushforwardMap_eq_sectionMap :
    normalizedPushforwardMap = Positive.sectionMap := by
  funext p
  exact congrArg (fun c : Positive.bundle.Fiber p => (⟨p, c⟩ : Positive.bundle.TotalSpace))
    (normalizedPushforwardValue_eq_sectionValue p)

theorem normalizedPushforwardMap_holomorphic :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω normalizedPushforwardMap := by
  rw [normalizedPushforwardMap_eq_sectionMap]
  exact Positive.sectionMap_holomorphic

/-- The only zero of the image on the actual sphere is its point at infinity. -/
theorem normalizedPushforwardValue_eq_zero_iff (p : RiemannSphere) :
    normalizedPushforwardValue p = 0 ↔ p = (∞ : RiemannSphere) := by
  rw [normalizedPushforwardValue_eq_sectionValue]
  exact Positive.section_eq_zero_iff p

theorem normalizedPushforwardValue_ne_zero_iff (p : RiemannSphere) :
    normalizedPushforwardValue p ≠ 0 ↔ p ≠ (∞ : RiemannSphere) :=
  not_congr (normalizedPushforwardValue_eq_zero_iff p)

@[simp] theorem normalizedPushforwardValue_infty :
    normalizedPushforwardValue (∞ : RiemannSphere) = 0 :=
  (normalizedPushforwardValue_eq_zero_iff _).mpr rfl

theorem normalizedPushforwardValue_finite_ne_zero (z : ℂ) :
    normalizedPushforwardValue (z : RiemannSphere) ≠ 0 :=
  (normalizedPushforwardValue_ne_zero_iff _).mpr (OnePoint.coe_ne_infty z)

theorem normalizedPushforwardValue_zeroSet :
    {p : RiemannSphere | normalizedPushforwardValue p = 0} = {(∞ : RiemannSphere)} :=
  Set.ext normalizedPushforwardValue_eq_zero_iff

/-- Every valid original native chart reads the prescribed geometric coefficient. -/
theorem normalizedPushforwardValue_localCoefficient (b : Bool) (p : RiemannSphere)
    (hp : p ∈ Positive.data.baseSet b) :
    (Positive.bundle.localTriv b ⟨p, normalizedPushforwardValue p⟩).2 =
      Positive.coefficient b p := by
  rw [normalizedPushforwardValue_eq_sectionValue]
  exact Positive.section_localCoefficient b hp

theorem normalizedPushforwardValue_finiteChartCoefficient {p : RiemannSphere}
    (hp : p ∈ finiteChart) :
    (Positive.bundle.localTriv false ⟨p, normalizedPushforwardValue p⟩).2 = 1 :=
  normalizedPushforwardValue_localCoefficient false p hp

theorem normalizedPushforwardValue_infinityChartCoefficient {p : RiemannSphere}
    (hp : p ∈ infinityChart) :
    (Positive.bundle.localTriv true ⟨p, normalizedPushforwardValue p⟩).2 =
      CanonicalGlobal.BaseTwist.infinityCoordinate p :=
  normalizedPushforwardValue_localCoefficient true p hp

theorem normalizedPushforward_finiteCoefficient (z : ℂ) :
    (Positive.bundle.localTriv false
      ⟨(z : RiemannSphere), normalizedPushforwardValue (z : RiemannSphere)⟩).2 = 1 :=
  normalizedPushforwardValue_finiteChartCoefficient (coe_mem_finiteChart z)

/-- Literal reciprocal-coordinate coefficient, including the actual chart centre. -/
theorem normalizedPushforward_infinityCoefficient (w : ℂ) :
    (Positive.bundle.localTriv true ⟨RiemannSphere.infinityParametrization w,
      normalizedPushforwardValue (RiemannSphere.infinityParametrization w)⟩).2 = w :=
  (normalizedPushforwardValue_infinityChartCoefficient (infinityParametrization_mem w)).trans
    (CanonicalGlobal.BaseTwist.infinityCoordinate_infinityParametrization w)

theorem normalizedPushforward_finiteCoefficient_eq_one :
    (fun z : ℂ => (Positive.bundle.localTriv false
      ⟨(z : RiemannSphere), normalizedPushforwardValue (z : RiemannSphere)⟩).2) =
        fun _ : ℂ => (1 : ℂ) := funext normalizedPushforward_finiteCoefficient

theorem normalizedPushforward_infinityCoefficient_eq_id :
    (fun w : ℂ => (Positive.bundle.localTriv true
      ⟨RiemannSphere.infinityParametrization w,
        normalizedPushforwardValue (RiemannSphere.infinityParametrization w)⟩).2) = id :=
  funext normalizedPushforward_infinityCoefficient

theorem normalizedPushforward_finiteCoefficient_analyticAt (z : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => (Positive.bundle.localTriv false
      ⟨(u : RiemannSphere), normalizedPushforwardValue (u : RiemannSphere)⟩).2) z := by
  rw [normalizedPushforward_finiteCoefficient_eq_one]
  exact analyticAt_const

theorem normalizedPushforward_infinityCoefficient_analyticAt (w : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => (Positive.bundle.localTriv true
      ⟨RiemannSphere.infinityParametrization u,
        normalizedPushforwardValue (RiemannSphere.infinityParametrization u)⟩).2) w := by
  rw [normalizedPushforward_infinityCoefficient_eq_id]
  exact analyticAt_id

/-- The genuine native reciprocal-chart coefficient has a simple analytic zero. -/
theorem normalizedPushforward_infinity_analyticOrderAt :
    analyticOrderAt (fun w : ℂ => (Positive.bundle.localTriv true
      ⟨RiemannSphere.infinityParametrization w,
        normalizedPushforwardValue (RiemannSphere.infinityParametrization w)⟩).2) 0 = 1 := by
  rw [normalizedPushforward_infinityCoefficient_eq_id]
  exact analyticOrderAt_id

theorem normalizedPushforward_infinity_meromorphicOrderAt :
    meromorphicOrderAt (fun w : ℂ => (Positive.bundle.localTriv true
      ⟨RiemannSphere.infinityParametrization w,
        normalizedPushforwardValue (RiemannSphere.infinityParametrization w)⟩).2) 0 = 1 := by
  rw [normalizedPushforward_infinityCoefficient_eq_id]
  exact meromorphicOrderAt_id

/-- Every finite point has order zero in the original finite bundle chart. -/
theorem normalizedPushforward_finite_analyticOrderAt (z : ℂ) :
    analyticOrderAt (fun u : ℂ => (Positive.bundle.localTriv false
      ⟨(u : RiemannSphere), normalizedPushforwardValue (u : RiemannSphere)⟩).2) z = 0 := by
  rw [normalizedPushforward_finiteCoefficient_eq_one]
  exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero

theorem normalizedPushforward_finite_meromorphicOrderAt (z : ℂ) :
    meromorphicOrderAt (fun u : ℂ => (Positive.bundle.localTriv false
      ⟨(u : RiemannSphere), normalizedPushforwardValue (u : RiemannSphere)⟩).2) z = 0 := by
  classical
  rw [normalizedPushforward_finiteCoefficient_eq_one, meromorphicOrderAt_const]
  simp only [one_ne_zero, if_false]

/-- On every original base open, the image is the restriction of this same global value. -/
theorem normalizedSection_positive_eq_global (U : Opens RiemannSphere) (p : U) :
    canonicalSectionPositiveEquiv U (normalizedSection U) p =
      normalizedPushforwardValue (p : RiemannSphere) :=
  (normalizedSection_positive_apply U p).trans
    (normalizedPushforwardValue_eq_sectionValue p).symm

theorem normalizedSection_positive_eq_zero_iff (U : Opens RiemannSphere) (p : U) :
    canonicalSectionPositiveEquiv U (normalizedSection U) p = 0 ↔
      (p : RiemannSphere) = (∞ : RiemannSphere) := by
  rw [normalizedSection_positive_apply]
  exact Positive.section_eq_zero_iff p

theorem normalizedSection_positive_localCoefficient (b : Bool) (U : Opens RiemannSphere)
    (p : U) (hp : (p : RiemannSphere) ∈ Positive.data.baseSet b) :
    (Positive.bundle.localTriv b
      ⟨(p : RiemannSphere), canonicalSectionPositiveEquiv U (normalizedSection U) p⟩).2 =
        Positive.coefficient b (p : RiemannSphere) := by
  rw [normalizedSection_positive_apply]
  exact Positive.section_localCoefficient b hp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
