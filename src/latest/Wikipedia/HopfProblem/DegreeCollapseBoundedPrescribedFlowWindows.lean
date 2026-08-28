import Wikipedia.HopfProblem.DegreeCollapsePrescribedFlowWindows
import Wikipedia.HopfProblem.DegreeCollapseAttachingBranchBasinControl

/-!
# Arbitrarily small surgery windows for the exact prescribed complete flow

The native field-germ construction accepts a separate positive radius bound
at each critical point. Taking those bounds below the distance to a regular
cut produces fresh separated windows which avoid the cut, while retaining
the complete field, flow, and original signed critical charts.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem exists_adapted_windows_with_prescribed_flow_lt
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (c : ∀ p : criticalPoints E f, SignedMorseChart (E := E) f p.val)
    (hmodel : ∀ p : criticalPoints E f, ∀ᶠ x in 𝓝 p.val, V x = (c p).descentField x)
    (ε : criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ S : AdaptedSurgeryWindows E f, S.field = V ∧ S.flow = F ∧
      (∀ p, (S.data p).chart = c p) ∧ ∀ p, (S.data p).radius < ε p := by
  have hfinite := finite_criticalPoints hf hm
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii hfinite hinj
  have hex (p : criticalPoints E f) := exists_morseSurgeryData_of_field_germ_lt hf hfinite
    hV F hF hzero hdesc (c p) (fun x hx hfx => hinj hx p.property hfx) (hmodel p)
      (lt_min (hr p) (hε p))
  choose d hd hchart hisolated hgerm using hex
  have hdr (p : criticalPoints E f) : (d p).radius < r p :=
    (hd p).trans_le (min_le_left _ _)
  have hde (p : criticalPoints E f) : (d p).radius < ε p :=
    (hd p).trans_le (min_le_right _ _)
  have hseparated (p q : criticalPoints E f) (hpq : f p < f q) :
      f p + (d p).radius ^ 2 < f q - (d q).radius ^ 2 := by
    have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)]
    have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr (hdr q)) (add_pos (hr q) (d q).radius_pos)]
    linarith [hgap p q hpq]
  exact ⟨{
    finite := hfinite
    distinct := hinj
    data := d
    isolated := hisolated
    separated := hseparated
    field := V
    flow := F
    smooth := hV
    integral := hF
    zero := hzero
    descent := hdesc
    model_germ := hgerm }, rfl, rfl, hchart, hde⟩

open Classical in
theorem AdaptedSurgeryWindows.exists_same_flow_windows_avoiding_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) :
    ∃ T : AdaptedSurgeryWindows E f, T.field = S.field ∧ T.flow = S.flow ∧
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
      (∀ p : criticalPoints E f, f p < a → T.toSurgeryWindows.upper p < a) ∧
      ∀ p : criticalPoints E f, a < f p → a < T.toSurgeryWindows.lower p := by
  let ε : criticalPoints E f → ℝ := fun p => Real.sqrt |f p - a|
  have hε (p : criticalPoints E f) : 0 < ε p := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (sub_ne_zero.mpr (fun h => ha p.val h p.property))
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ := exists_adapted_windows_with_prescribed_flow_lt
    hf hm S.distinct S.smooth S.flow S.integral S.zero S.descent
      (fun p => (S.data p).chart) S.critical_model_germ ε hε
  have hsq (p : criticalPoints E f) : (T.data p).radius ^ 2 < |f p - a| := by
    have hp := mul_pos (sub_pos.mpr (hsmall p)) (add_pos (hε p) (T.data p).radius_pos)
    have heq : (ε p) ^ 2 = |f p - a| := Real.sq_sqrt (abs_nonneg _)
    nlinarith
  refine ⟨T, hfield, hflow, hcharts, ?_, ?_⟩
  · intro p hp
    have hh := hsq p
    rw [abs_of_neg (sub_neg.mpr hp)] at hh
    change f p + (T.data p).radius ^ 2 < a
    linarith
  · intro p hp
    have hh := hsq p
    rw [abs_of_pos (sub_pos.mpr hp)] at hh
    change a < f p - (T.data p).radius ^ 2
    linarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
