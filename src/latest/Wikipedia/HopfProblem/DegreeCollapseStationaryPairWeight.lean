import Wikipedia.HopfProblem.DegreeCollapseCompactRegularBandSections
import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderPlateauWeights
import Wikipedia.HopfProblem.DegreeCollapseSmoothBasinWeightBand
import Wikipedia.HopfProblem.DegreeCollapseNativeNoReturn

/-!
# Constructed stationary pair weight for the same no-connection flow

Compact entire endpoint sections on the middle level are constructed from
the original small core blocks and regular-band transport. Absence of the
selected connection makes these sections disjoint. Native smooth separation,
the actual cylinder, core exit germs, and endpoint extension construct a
stationary weight smooth on the whole pair band with the required full
critical germs. The field and its complete flow are never replaced.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
open Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

open Classical in
theorem exists_stationary_pair_weight {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    {p q : M} (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    {rp rq l a u : ℝ} (hrp : 0 < rp) (hrq : 0 < rq) (hla : l < a) (hau : a < u)
    (hpair : ∀ z ∈ criticalPoints E f, f z ∈ Icc l u → z = p ∨ z = q)
    (hbp : closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
      closedBall (0 : cp.PositiveCoordinates) (2 * rp) ⊆ cp.splitChart.target)
    (hbq : closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
      closedBall (0 : cq.PositiveCoordinates) (2 * rq) ⊆ cq.splitChart.target)
    (hfp : ∀ z ∈ closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
      closedBall (0 : cp.PositiveCoordinates) (2 * rp),
      ∀ᶠ y in 𝓝 (cp.splitChart.symm z), V y = cp.descentField y)
    (hfq : ∀ z ∈ closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
      closedBall (0 : cq.PositiveCoordinates) (2 * rq),
      ∀ᶠ y in 𝓝 (cq.splitChart.symm z), V y = cq.descentField y)
    (hpa : f p + rp ^ 2 ≤ a) (haq : a ≤ f q - rq ^ 2)
    (hbandp : ∀ x, f x ∈ Icc (f p + rp ^ 2) a → x ∉ criticalPoints E f)
    (hbandq : ∀ x, f x ∈ Icc a (f q - rq ^ 2) → x ∉ criticalPoints E f)
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => F t x) atBot (𝓝 q) ∧
      Tendsto (fun t => F t x) atTop (𝓝 p))) :
    ∃ W : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ W (f ⁻¹' Icc l u) ∧
      (∀ x, W x ∈ Icc (0 : ℝ) 1) ∧ (∀ x t, W (F t x) = W x) ∧
      (W =ᶠ[𝓝 p] fun _ => 1) ∧ (W =ᶠ[𝓝 q] fun _ => 0) := by
  have hpa' : f p < a := by nlinarith [sq_pos_of_pos hrp]
  have haq' : a < f q := by nlinarith [sq_pos_of_pos hrq]
  have hreg : ∀ x, f x = a → x ∉ criticalPoints E f := by
    intro x hx
    exact hbandp x (by rw [hx]; exact ⟨hpa, le_rfl⟩)
  have hboundp : ∀ x, f x = f p + rp ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandp x (by rw [hx]; exact ⟨le_rfl, hpa⟩))
  have hboundq : ∀ x, f x = f q - rq ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandq x (by rw [hx]; exact ⟨haq, le_rfl⟩))
  let L := {x : M // f x = a}
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  letI : CompactSpace L := isCompact_iff_compactSpace.mp
    (isClosed_eq hf.continuous continuous_const).isCompact
  let S₀ : Set L := {x | Tendsto (fun t => F t (x : M)) atBot (𝓝 q)}
  let S₁ : Set L := {x | Tendsto (fun t => F t (x : M)) atTop (𝓝 p)}
  have hS₁ : IsCompact S₁ :=
    (isCompact_forward_section_iff_of_regular_band hf hV hdesc F hF hpa hbandp p).mpr
      (isCompact_native_belt_basin cp hf hV F hF rp hrp hbp hfp hboundp)
  have hS₀ : IsCompact S₀ :=
    (isCompact_backward_section_iff_of_regular_band hf hV hdesc F hF haq hbandq q).mp
      (isCompact_native_attaching_basin cq hf hV F hF rq hrq hbq hfq hboundq)
  have hdisj : Disjoint S₀ S₁ := disjoint_left.mpr (fun x hx₀ hx₁ => hnoconnection x ⟨hx₀, hx₁⟩)
  obtain ⟨z, hz⟩ := intermediate_value_univ p q hf.continuous ⟨hpa'.le, haq'.le⟩
  obtain ⟨A, hAsource, hAtarget, hAformula, -⟩ := exists_native_level_flow_cylinder hf hreg hV F hF
    (fun x hx => hdesc x (hreg x hx)) (⟨z, hz⟩ : L)
  obtain ⟨w, hw, hwrange, hwinv, hw₀, hw₁⟩ := exists_native_cylinder_plateau_weight
    A hAsource F Subtype.val hAformula hS₀.isClosed hS₁.isClosed hdisj
  have hmono := FlowConstruction.antitone_flow_height hf F hF hzero hdesc
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hbasinp := levelBasin_eq_of_regular_band hf hV hdesc F hF hpa hbandp
  have hbasinq := levelBasin_eq_of_regular_band hf hV hdesc F hF haq hbandq
  have hcorep (v : PuncturedHandle.UnitSphere cp.PositiveCoordinates) :
      w =ᶠ[𝓝 (cp.beltCoreMap rp hrp hbp v : M)] fun _ => 1 := by
    let x : M := cp.beltCoreMap rp hrp hbp v
    have hx : x ∈ A.target := by
      rw [hAtarget, ← hbasinp]
      exact ⟨0, by simpa only [F.map_zero_apply] using (cp.beltCoreMap rp hrp hbp v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₁ x hx
    have hh := native_belt_core_forward_limit cp hV₁ F hF rp hrp hbp hfp v
    apply (flow_time_atTop_limit_iff F (A.symm x).2 ((A.symm x).1 : M) p).mp
    rw [hmap]
    exact hh
  have hcoreq (v : PuncturedHandle.UnitSphere cq.NegativeCoordinates) :
      w =ᶠ[𝓝 (cq.attachingCoreMap rq hrq hbq v : M)] fun _ => 0 := by
    let x : M := cq.attachingCoreMap rq hrq hbq v
    have hx : x ∈ A.target := by
      rw [hAtarget, hbasinq]
      exact ⟨0, by simpa only [F.map_zero_apply] using (cq.attachingCoreMap rq hrq hbq v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₀ x hx
    have hh := native_attaching_core_backward_limit cq hV₁ F hF rq hrq hbq hfq v
    apply (flow_time_atBot_limit_iff F (A.symm x).2 ((A.symm x).1 : M) q).mp
    rw [hmap]
    exact hh
  have hstationary : ∀ x ∈ levelBasin F f a, ∀ t, w (F t x) = w x := by
    simpa only [hAtarget] using hwinv
  have hpw : ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = 1 :=
    eventually_constant_basin_weight_of_belt_neighborhood cp hf.continuous hV₁ F hF hmono
      hrp hbp hfp hpa' hstationary (U := interior {x | w x = 1}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcorep v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 1}) hx)
  have hqw : ∀ᶠ x in 𝓝 q, x ∈ levelBasin F f a → w x = 0 :=
    eventually_constant_basin_weight_of_attaching_neighborhood cq hf.continuous hV₁ F hF hmono
      hrq hbq hfq haq' hstationary (U := interior {x | w x = 0}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcoreq v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 0}) hx)
  have hB : IsOpen (levelBasin F f a) := hAtarget ▸ A.open_target
  have hwB : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w (levelBasin F f a) := hAtarget ▸ hw
  refine ⟨extendedBasinWeight F f a w, ?_,
    extendedBasinWeight_mem_Icc F f a w (fun x _ => hwrange x),
    extendedBasinWeight_flow F hf.continuous a w hstationary,
    extendedBasinWeight_lower_germ F hf.continuous.continuousAt hpa' hpw,
    extendedBasinWeight_upper_germ F hf.continuous.continuousAt haq' hqw⟩
  exact contMDiffOn_extendedBasinWeight_pair_band F hf.continuous hinj hmono
    (fun x hx => FlowConstruction.strictAnti_flow_height hf hV₁ F hF hzero hdesc hx)
    hla hau hpa' haq' hpair hB hwB hstationary hpw hqw

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
