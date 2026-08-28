import Wikipedia.HopfProblem.DegreeCollapseNormalizedConnectionCylinder
import Wikipedia.HopfProblem.DegreeCollapseActualConnectionSliceData
import Wikipedia.HopfProblem.DegreeCollapseSliceDataCancellation

/-!
# All native local cancellation data from the original Morse connection

The actual isolated connection constructs the regular inner band, level
point, normalized field and cylinder, matching endpoint charts, exact
basins, clocks, transverse maps, phases, and their common domain. The
remaining local criterion is transversality of the actual label sheets.
Given it, the original smooth Morse function loses exactly this pair.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ}

structure NativeConnectionCancellationData (f : M → ℝ) (p q : M) (m : ℕ) where
  σ : Fin m → ℝ
  signs : ∀ i, σ i = -1 ∨ σ i = 1
  field : (y : M) → TangentSpace 𝓘(ℝ, E) y
  smooth_field : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun y => (⟨y, field y⟩ : TangentBundle 𝓘(ℝ, E) M))
  flow : Flow ℝ M
  integral : ∀ y, IsMIntegralCurve (fun t => flow t y) field
  zero : ∀ y ∈ criticalPoints E f, field y = 0
  descent : ∀ y, y ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (field y) < 0
  Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  endpointQ : Φq (-(1 / 2 : ℝ), 0) = q
  endpointP : Φp (1 / 2, 0) = p
  fieldQ : ∀ y ∈ Φq.target, field y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y
  fieldP : ∀ y ∈ Φp.target, field y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y
  A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞
  vertical : ∀ y ∈ A.target, field y = FlowConstruction.partialChartField A.symm
    (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y
  speed : ℝ
  positive_speed : 0 < speed
  height : ℝ
  height_formula : ∀ z ∈ A.source, z.2 ∈ Ioo (0 : ℝ) 1 → f (A z) = height - speed * z.2
  Rq : ℝ
  Rp : ℝ
  Tq : ℝ
  Tp : ℝ
  positive_Rq : 0 < Rq
  positive_Rp : 0 < Rp
  boxQ : closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Φq.source
  boxP : closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Φp.source
  basinQ : ∀ z ∈ Φq.source, Tendsto (fun t => flow t (Φq z)) atBot (𝓝 q) ↔
    ∀ i, σ i = 1 → z.2 i = 0
  basinP : ∀ z ∈ Φp.source, Tendsto (fun t => flow t (Φp z)) atTop (𝓝 p) ↔
    ∀ i, σ i = -1 → z.2 i = 0
  unique : ∀ y, Tendsto (fun t => flow t y) atBot (𝓝 q) →
    Tendsto (fun t => flow t y) atTop (𝓝 p) → ∃ t, flow t (A (0, 0)) = y
  slices : NativeEndpointSliceData σ (1 / 2) Φq Φp A Rq Rp Tq Tp

def NativeConnectionCancellationData.Transverse {f : M → ℝ} {p q : M}
    (D : NativeConnectionCancellationData (E := E) f p q m) : Prop :=
  NativeTransversality.At
    𝓘(ℝ, MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, Fin m → ℝ)
    (fun x => D.slices.Q (x, 0)) (fun y => D.slices.P (0, y)) 0 0

theorem NativeConnectionCancellationData.cancel {f : M → ℝ} {p q : M}
    (D : NativeConnectionCancellationData (E := E) f p q m) (htrans : D.Transverse)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f)
    (hpq : f p < f q) {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ y ∈ criticalPoints E f, f y ∈ Icc c d → y = p ∨ y = q) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ y, y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f ∧ y ≠ p ∧ y ≠ q) ∧
      ∀ y, f y ∉ Ioo c d → g =ᶠ[𝓝 y] f := by
  have hh := cancel_native_endpoint_slice_data D.σ D.signs (by norm_num) D.Φq D.Φp D.A
    D.slices htrans hf hm D.positive_speed D.height_formula D.field D.smooth_field
    D.fieldQ D.fieldP D.vertical D.flow D.integral D.zero D.descent hinj
    D.positive_Rq D.positive_Rp D.boxQ D.boxP
    (by simpa only [D.endpointQ] using D.basinQ)
    (by simpa only [D.endpointP] using D.basinP)
    (by simpa only [D.endpointQ, D.endpointP] using D.unique)
    (by rw [D.endpointP]; exact hp) (by rw [D.endpointQ]; exact hq)
    (by rw [D.endpointP, D.endpointQ]; exact hpq)
    (by rw [D.endpointP]; exact hc) (by rw [D.endpointQ]; exact hd)
    (by simpa only [D.endpointP, D.endpointQ] using hpair)
  simpa only [D.endpointP, D.endpointQ] using hh

open Classical in
theorem exists_native_connection_cancellation_data {f : M → ℝ} {p q x : M}
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hpc : p ∈ criticalPoints E f) (hqc : q ∈ criticalPoints E f) (hpq : f p < f q)
    {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ y ∈ criticalPoints E f, f y ∈ Icc c d → y = p ∨ y = q)
    (hp : Tendsto (fun t => F t x) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t x) atBot (𝓝 q))
    (hunique : ∀ y, Tendsto (fun t => F t y) atBot (𝓝 q) →
      Tendsto (fun t => F t y) atTop (𝓝 p) → ∃ t, F t x = y)
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y)
    (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ D : NativeConnectionCancellationData (E := E) f p q m,
      (∀ y ∈ criticalPoints E f, ∀ᶠ z in 𝓝 y, D.field z = V z) ∧
      (∀ y, range (fun t => D.flow t y) = range (fun t => F t y) ∧
        (∀ z, Tendsto (fun t => D.flow t y) atTop (𝓝 z) ↔ Tendsto (fun t => F t y) atTop (𝓝 z)) ∧
        ∀ z, Tendsto (fun t => D.flow t y) atBot (𝓝 z) ↔ Tendsto (fun t => F t y) atBot (𝓝 z)) ∧
      ∃ t, F t x = D.A 0 := by
  obtain ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hneg, hgerms,
      hmono, hp₀, hq₀, hunique₀, _, h0U, hAsource, hAaxis, hheight, hAfield,
      hgeometry, hreference⟩ :=
    FlowTimeChange.exists_normalized_connection_cylinder hf hdim V hV hzero hdesc F hF
      hpq hc hd hpair hp hq hunique
  have hgp : ∀ᶠ y in 𝓝 p, W y = cp.descentField y := by
    filter_upwards [hgerms p hpc, heqp] with y h₁ h₂
    exact h₁.trans h₂
  have hgq : ∀ᶠ y in 𝓝 q, W y = cq.descentField y := by
    filter_upwards [hgerms q hqc, heqq] with y h₁ h₂
    exact h₁.trans h₂
  obtain ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp, hqval, hpval,
      hqbox, hpbox, hqfield, hpfield, hqbasin, hpbasin, hBsub, _, hBmap, hBfield, ⟨D⟩⟩ :=
    exists_actual_connection_slice_data cp cq hf.continuous hdim hindex hW G hG hmono
      hxp hxq hp₀ hq₀ hgp hgq A hAsource h0U hAfield hAaxis
  have hB0 : B (0, 0) = x₀ := by rw [hBmap, hAaxis, G.map_zero_apply]
  refine ⟨{
    σ := σ
    signs := hσ
    field := W
    smooth_field := hW
    flow := G
    integral := hG
    zero := hzeros
    descent := hneg
    Φq := Ψq
    Φp := Ψp
    endpointQ := hqval
    endpointP := hpval
    fieldQ := hqfield
    fieldP := hpfield
    A := B
    vertical := hBfield
    speed := r
    positive_speed := hr
    height := b
    height_formula := ?_
    Rq := Rq
    Rp := Rp
    Tq := Tq
    Tp := Tp
    positive_Rq := hRq
    positive_Rp := hRp
    boxQ := hqbox
    boxP := hpbox
    basinQ := hqbasin
    basinP := hpbasin
    unique := ?_
    slices := D
  }, hgerms, hgeometry, ?_⟩
  · intro z hz ht
    rw [hBmap]
    exact hheight z (hBsub hz) ⟨ht.1.le, ht.2.le⟩
  · intro y hyq hyp
    rw [hB0]
    exact hunique₀ y hyq hyp
  · change ∃ t, F t x = B (0, 0)
    rw [hB0]
    exact hreference

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
