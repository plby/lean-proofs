import Wikipedia.HopfProblem.DegreeCollapseMatchedCubicTimeFormulas
import Wikipedia.HopfProblem.DegreeCollapseControlledFieldGermChart
import Wikipedia.HopfProblem.DegreeCollapseSignedCubicBlockChange
import Wikipedia.HopfProblem.DegreeCollapseNativePhaseCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativeRegularCubicChart
import Wikipedia.HopfProblem.DegreeCollapseMatchedCubicFieldGluing

/-!
# A full cubic field chart assembled from the corrected native cylinder

Absorb the actual incoming holonomy blocks, restrict both endpoint charts
to the changed field germs with controlled model domains, and convert the
actual corrected vertical cylinder to cubic coordinates. The original
slice equations give the two full overlap identities. Critical endpoints
are excluded from the regular cylinder by its native vertical field.
The closed-axis gluing theorem then constructs the full cubic field chart.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {Z E M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {m : ℕ} {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x}

open Classical in
theorem exists_full_cubic_chart_from_corrected_cylinder
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    {U : Set Z} (hAsource : A.source = U ×ˢ univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield : ∀ y ∈ A.target, V y =
      FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (L₁ : MorseHandle.NegativeSpace σ ≃L[ℝ] MorseHandle.NegativeSpace σ)
    (L₂ : MorseHandle.PositiveSpace σ ≃L[ℝ] MorseHandle.PositiveSpace σ)
    (Q P : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → Z)
    (v₀ v₁ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) → ℝ)
    {Oq Op : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hOq : IsOpen Oq) (hOp : IsOpen Op) (h0q : 0 ∈ Oq) (h0p : 0 ∈ Op)
    (hQU : ∀ u ∈ Oq, Q u ∈ U) (hPU : ∀ u ∈ Op, P u ∈ U)
    {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq : ∀ u ∈ Oq, cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq) ∈
      closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep : ∀ u ∈ Op, cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp) ∈
      closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq : ∀ u ∈ Oq, Φq (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tq)) =
      A (Q u, Tq + v₀ u))
    (hphasep : ∀ u ∈ Op, Φp (cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, Tp)) =
      A (P u, Tp + v₁ u))
    (Ξ : PartialDiffeomorph
      𝓘(ℝ, (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ)
      𝓘(ℝ, E) ((MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ) M ∞)
    {O : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)}
    (hO : IsOpen O) (h0O : 0 ∈ O) (hΞsource : Ξ.source = O ×ˢ univ)
    (hΞtarget : Ξ.target = A.target)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΞfield : ∀ y ∈ Ξ.target, W y = FlowConstruction.partialChartField Ξ.symm
      (fun _ : (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ) × ℝ => (0, 1)) y)
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    (hWq : ∀ᶠ y in 𝓝 (Φq (-a, 0)), W y = V y)
    (hWp : ∀ᶠ y in 𝓝 (Φp (a, 0)), W y = V y)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hleft : ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
      ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright : ∀ᶠ u in 𝓝 (0 : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ),
      ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
      (∀ y ∈ Φ.target, W y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
      Φ (-a, 0) = Φq (-a, 0) ∧ Φ (a, 0) = Φp (a, 0) ∧ Φ (0, 0) = Ξ (0, 0) := by
  let e := MorseHandle.splitCoordinates σ
  let L := L₁.prodCongr L₂
  let T := splitTransverseChange e L₁ L₂
  let D := transverseFieldChange T
  have hqsrc : (-a, (0 : Fin m → ℝ)) ∈ Φq.source := hboxq (mem_closedBall_self hRq.le)
  have hpsrc : (a, (0 : Fin m → ℝ)) ∈ Φp.source := hboxp (mem_closedBall_self hRp.le)
  obtain ⟨Ψq, rq, hrq, hΨqbox, hΨqsub, _, hΨqmap, hΨqfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart Φq (cubicDescent σ (-(a ^ 2)))
      V W hqfield hqsrc hWq isOpen_ball (mem_ball_self hRq)
  have hcontrolq : closedBall (-a, (0 : Fin m → ℝ)) rq ⊆
      closedBall (-a, (0 : Fin m → ℝ)) Rq :=
    fun p hp => ball_subset_closedBall (hΨqsub (hΨqbox hp)).2
  obtain ⟨ΦpB, _, hpBsource, hpBaxis, hpBfield, hpBflow⟩ :=
    exists_signed_block_changed_cubic_chart σ hσ L₁ L₂ Φp V (-(a ^ 2)) hpfield
  have hDcenter : D (a, 0) = (a, 0) := by change (a, T 0) = (a, 0); rw [map_zero]
  have hOpcoord : IsOpen (D ⁻¹' ball (a, (0 : Fin m → ℝ)) Rp) :=
    isOpen_ball.preimage D.continuous
  have hpO : (a, (0 : Fin m → ℝ)) ∈ D ⁻¹' ball (a, (0 : Fin m → ℝ)) Rp := by
    change D (a, 0) ∈ ball (a, (0 : Fin m → ℝ)) Rp
    rw [hDcenter]
    exact mem_ball_self hRp
  have hWpB : ∀ᶠ y in 𝓝 (ΦpB (a, 0)), W y = V y := by rw [hpBaxis]; exact hWp
  obtain ⟨Ψp, rp, hrp, hΨpbox, hΨpsub, _, hΨpmap, hΨpfield⟩ :=
    FieldChartGluing.exists_controlled_field_germ_chart ΦpB (cubicDescent σ (-(a ^ 2)))
      V W hpBfield ((hpBsource a).mpr hpsrc) hWpB hOpcoord hpO
  have hnewp (z : Fin m → ℝ) (t : ℝ) : Ψp (cubicFlowCylinder σ a (z, t)) =
      Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) := by
    have hh := hpBflow a t (e z)
    change ΦpB (cubicFlowCylinder σ a (e.symm (e z), t)) =
      Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) at hh
    rw [e.symm_apply_apply] at hh
    exact (hΨpmap _).trans hh
  have hcontrolp (z : Fin m → ℝ) (t : ℝ)
      (hp : cubicFlowCylinder σ a (z, t) ∈ closedBall (a, (0 : Fin m → ℝ)) rp) :
      cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ closedBall (a, (0 : Fin m → ℝ)) Rp := by
    have hb : D (cubicFlowCylinder σ a (z, t)) ∈ ball (a, (0 : Fin m → ℝ)) Rp :=
      (hΨpsub (hΨpbox hp)).2
    have hc : D (cubicFlowCylinder σ a (z, t)) =
        cubicFlowCylinder σ a (e.symm (L (e z)), t) :=
      signed_block_change_cubic_cylinder σ hσ L₁ L₂ a t z
    rw [hc] at hb
    exact ball_subset_closedBall hb
  let R := PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hRtarget : R.target = O := by
    ext u
    change (u ∈ (univ : Set (MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)) ∧ u ∈ O) ↔ u ∈ O
    simp only [mem_univ, true_and]
  have hR0 : (0 : Fin m → ℝ) ∈ R.source := by
    change (0 : Fin m → ℝ) ∈ univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨mem_univ _, h0O⟩
  obtain ⟨B₀, hBsource, hBtarget, hBmap, hBfield⟩ :=
    FlowSuspension.exists_native_phase_cylinder Ξ hΞsource R hRtarget
      (fun _ => (0 : ℝ)) contDiff_const W hΞfield
  obtain ⟨Φm, hmTarget, hmidAxis, _, hmField, _, hcompose⟩ :=
    exists_regular_cubic_chart_of_native_vertical_field σ ha B₀ hBsource hR0 W hW hBfield G hG
  have hmid (z : Fin m → ℝ) (t : ℝ) : Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t) := by
    rw [hcompose, hBmap]
    change Ξ (e z, t + 0) = Ξ (e z, t)
    rw [add_zero]
  have hmTargetA : Φm.target = A.target := hmTarget.trans (hBtarget.trans hΞtarget)
  have hzeroAt (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
      {c : ℝ} (hc : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (hcrit : c ^ 2 = a ^ 2)
      (hf : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) : V (Φ (c, 0)) = 0 := by
    rw [hf _ (Φ.map_source' hc)]
    apply (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) (Φ.map_source' hc)).mpr
    have hi : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hc
    rw [hi]
    ext i <;> simp [cubicDescent, hcrit]
  have hzeroq : V (Φq (-a, 0)) = 0 := hzeroAt Φq hqsrc (by ring) hqfield
  have hzerop : V (Φp (a, 0)) = 0 := hzeroAt Φp hpsrc rfl hpfield
  have hAregular (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    intro hz
    rw [hAfield y hy] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hy).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqval : Ψq (-a, 0) = Φq (-a, 0) := hΨqmap _
  have hpval : Ψp (a, 0) = Φp (a, 0) := (hΨpmap _).trans (hpBaxis a)
  have hqnot : Ψq (-a, 0) ∉ Φm.target := by
    rw [hqval, hmTargetA]
    exact fun h => hAregular _ h hzeroq
  have hpnot : Ψp (a, 0) ∉ Φm.target := by
    rw [hpval, hmTargetA]
    exact fun h => hAregular _ h hzerop
  obtain ⟨hmatchq, hmatchp⟩ := matched_cubic_time_formulas σ ha Φq Φp A hAsource
    hV hqfield hpfield hAfield F hF e L Q P v₀ v₁ hOq hOp h0q h0p hQU hPU
    hboxq hboxp hsliceq hslicep hphaseq hphasep Ψq Ψp Φm Ξ hΨqmap hnewp hmid
    hcontrolq hcontrolp hleft hright
  obtain ⟨Φ, haxis, hfield, hΦq, hΦp, hΦmid, _, _⟩ :=
    exists_matched_full_cubic_field_chart σ ha Ψq Φm Ψp W hΨqfield hmField hΨpfield
      hrq hrp hΨqbox hΨpbox (fun s hs => hmidAxis ⟨hs, rfl⟩) hqnot hpnot
      (by rw [hqval, hpval]; exact hne) hmatchq hmatchp
  have hmid0 : Φm (0, 0) = Ξ (0, 0) := by
    have hh := hmid 0 0
    simpa only [cubicFlowCylinder_zero_time, map_zero] using hh
  exact ⟨Φ, haxis, hfield, hΦq.trans hqval, hΦp.trans hpval,
    (hΦmid 0 ⟨by linarith, ha⟩).trans hmid0⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
