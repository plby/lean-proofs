import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionMultiplicative
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopology

/-!
# The original global delta-circle action

Real time in the constructed vertical flow descends through the actual
period-one additive circle. The resulting action is a restriction of the
existing global multiplicative action, not a new action on an abstract
space. Its formulas on every original piece and on the genuine gluing
overlaps are the already proved unmodified translation formulas.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open VerticalAction.Exponential

local notation "Circle" => PeriodTorusHigherHomology.CircleTopology.Circle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The original normalized exponential restricted to real time. -/
def realParameterAddHom : ℝ →+ Additive ℂˣ where
  toFun t := Additive.ofMul (normalizedExponential (t : ℂ))
  map_zero' := by
    change normalizedExponential ((0 : ℝ) : ℂ) = 1
    exact normalizedExponential_zero
  map_add' s t := by
    change normalizedExponential ((s + t : ℝ) : ℂ) =
      normalizedExponential (s : ℂ) * normalizedExponential (t : ℂ)
    rw [Complex.ofReal_add, normalizedExponential_add]

/-- Descent through the literal integral subgroup of the real line. -/
def circleParameterAddHom : Circle →+ Additive ℂˣ :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℝ)) realParameterAddHom (by
    intro t ht
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
    have he : t = (k : ℝ) := by simpa only [zsmul_one] using hk.symm
    change normalizedExponential (t : ℂ) = 1
    rw [he]
    simpa only [Complex.ofReal_intCast] using normalizedExponential_int k)

/-- The period-one circle parameter as an actual nonzero complex scalar. -/
def circleParameter (t : Circle) : ℂˣ := Additive.toMul (circleParameterAddHom t)

@[simp] theorem circleParameter_real (t : ℝ) :
    circleParameter (t : Circle) = normalizedExponential (t : ℂ) := rfl

@[simp] theorem circleParameter_zero : circleParameter 0 = 1 :=
  circleParameterAddHom.map_zero

theorem circleParameter_add (s t : Circle) :
    circleParameter (s + t) = circleParameter s * circleParameter t :=
  circleParameterAddHom.map_add s t

theorem circleParameter_continuous : Continuous circleParameter := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  exact normalizedExponential_continuous.comp Complex.continuous_ofReal

/-- The genuine period-one delta-circle action on the unchanged threefold. -/
@[instance_reducible]
def circleAction : AddAction Circle Space where
  vadd t x := VerticalAction.actionBiholomorph (circleParameter t) x
  zero_vadd x := by
    let := VerticalAction.action
    change VerticalAction.actionBiholomorph (circleParameter 0) x = x
    rw [circleParameter_zero]
    exact one_smul ℂˣ x
  add_vadd s t x := by
    let := VerticalAction.action
    change VerticalAction.actionBiholomorph (circleParameter (s + t)) x =
      VerticalAction.actionBiholomorph (circleParameter s)
        (VerticalAction.actionBiholomorph (circleParameter t) x)
    rw [circleParameter_add]
    exact mul_smul (circleParameter s) (circleParameter t) x

/-- The actual jointly continuous action, in circle-first order. -/
def actionMap : C(Circle × Space, Space) :=
  ⟨fun p => VerticalAction.actionBiholomorph (circleParameter p.1) p.2, by
    let := VerticalAction.action
    exact VerticalAction.action_holomorphic.continuous.comp
      ((circleParameter_continuous.comp continuous_fst).prodMk continuous_snd)⟩

@[simp] theorem actionMap_apply (t : Circle) (x : Space) :
    actionMap (t, x) = VerticalAction.actionBiholomorph (circleParameter t) x := rfl

@[simp] theorem circleAction_vadd (t : Circle) (x : Space) :
    letI := circleAction
    t +ᵥ x = actionMap (t, x) := rfl

theorem circleAction_continuous :
    letI := circleAction
    ContinuousVAdd Circle Space := by
  let := circleAction
  exact ⟨actionMap.continuous⟩

/-- Real time projects to the original flow with its unchanged `e₂`
normalization; no sign or scale is introduced. -/
@[simp] theorem actionMap_real (t : ℝ) (x : Space) :
    actionMap ((t : Circle), x) = VerticalAction.flow (t : ℂ) x := by
  rw [actionMap_apply, circleParameter_real, VerticalAction.actionBiholomorph_exponential]

/-- On all four original patches this is exactly the existing local
translation, including both full elliptic and cusp central fibres. -/
theorem actionMap_real_inclusion (t : ℝ) (i : Index) (x : localPiece i) :
    actionMap ((t : Circle), inclusion i x) =
      inclusion i (VerticalAction.localFlow i (t : ℂ) x) := by
  rw [actionMap_real, VerticalAction.flow_inclusion]

/-- The original gauges and full overlap maps intertwine these actual
real translations; this is the frozen gluing equality itself. -/
theorem real_localFlow_overlap (i : Puncture) (t : ℝ) (x : localPiece (some i))
    (hx : x ∈ (localOverlap i).source) :
    localOverlap i (VerticalAction.localFlow (some i) (t : ℂ) x) =
      VerticalAction.localFlow none (t : ℂ) (localOverlap i x) :=
  VerticalAction.localFlow_overlap i (t : ℂ) x hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
