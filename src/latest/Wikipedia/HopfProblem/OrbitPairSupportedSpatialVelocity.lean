import Wikipedia.HopfProblem.OrbitPairNativeClockDerivative
import Wikipedia.HopfProblem.OrbitPairLocalClock
import Wikipedia.HopfProblem.OrbitPairNativeSpatialReparametrization

/-!
# Prescribed small time velocity by a supported spatial source motion

The selected time slice is fixed pointwise. The time derivative of the
spatial map at the selected source point is an arbitrary sufficiently
small vector, and its spatial derivative is the identity. The motion is
supported in a prescribed time region and spatial neighborhood.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_radius_supported_spatial_velocity
    {T : Set ℝ} (hT : IsOpen T) {t : ℝ} (ht : t ∈ T)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∃ D : ℝ → Diffeomorph I I M M ∞,
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => D p.1 p.2) ∧
        (∀ y, D t y = y) ∧
        (∀ s y, s ∉ T ∨ y ∉ U → D s y = y) ∧
        (mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M => D p.1 p.2) (t, x) :
            ℝ × E →L[ℝ] E) =
          ContinuousLinearMap.snd ℝ ℝ E + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a := by
  let Φ := NativeCenteredChart.chart (I := I) x
  let V : Set E := Φ.source ∩ Φ ⁻¹' U
  have hV : IsOpen V :=
    Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hU
  have h0 : (0 : E) ∈ V := by
    refine ⟨NativeCenteredChart.zero_mem_source x, ?_⟩
    change Φ 0 ∈ U
    rw [NativeCenteredChart.chart_zero]
    exact hx
  obtain ⟨β, hβV, hcompact, hβ, -, hβone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hV.mem_nhds h0)
  obtain ⟨κ, hκ, -, hbound, hzero, hderiv, hfixedTime⟩ :=
    ClockVelocity.exists_local_clock hT ht
  obtain ⟨ε, hε, hall⟩ := ClockVelocity.exists_radius_clockAmbient Φ hβ hcompact
    (fun u hu => (hβV hu).1) hκ hbound
  refine ⟨ε, hε, ?_⟩
  intro a ha
  obtain ⟨hA, hD, hfixed, -⟩ := hall a ha
  choose D hDeq using hD
  have hAeq : (fun p : ℝ × M => D p.1 p.2) = ClockVelocity.clockAmbient Φ β κ a :=
    funext (fun p => hDeq p.1 p.2)
  refine ⟨D, hAeq.symm ▸ hA, ?_, ?_, ?_⟩
  · intro y
    rw [hDeq]
    exact hfixed t y (Or.inl hzero)
  · intro s y hy
    rw [hDeq]
    apply hfixed s y
    rcases hy with hs | hy
    · exact Or.inl (hfixedTime s hs)
    · right
      rintro ⟨u, hu, heq⟩
      exact hy (heq ▸ (hβV hu).2)
  · have hd := ClockVelocity.nativeDerivative_centeredClockFamily
      (I := I) (J := I) (F := fun p : ℝ × M => p.2) (t, x) a
      contMDiff_snd hA hβ hβone hκ hzero hderiv
    let P : ℝ × E →L[ℝ] E :=
      mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M => p.2) (t, x)
    let A : ℝ × E →L[ℝ] E :=
      mfderiv (𝓘(ℝ, ℝ).prod I) I (ClockVelocity.clockAmbient Φ β κ a) (t, x)
    have hs : P = ContinuousLinearMap.snd ℝ ℝ E := mfderiv_snd
    change A = P + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a at hd
    rw [hs] at hd
    let D₀ : ℝ × E →L[ℝ] E :=
      mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M => D p.1 p.2) (t, x)
    have he : D₀ = A := by
      dsimp only [D₀, A]
      rw [hAeq]
    exact he.trans hd

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization
