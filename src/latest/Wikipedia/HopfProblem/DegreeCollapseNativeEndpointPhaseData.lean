import Wikipedia.HopfProblem.DegreeCollapseGlobalNativeTransitionPhase
import Wikipedia.HopfProblem.DegreeCollapseEndpointVerticalChart

/-!
# Original endpoint slices construct actual transverse charts and phases

Put the time coordinate last without changing the native vertical field.
The genuine transition between an endpoint flow chart and the original
full cylinder then constructs the transverse partial diffeomorphism and
global smooth phase. Restriction gives the actual endpoint box domain.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E M : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_time_last_native_transition_phase
    (A C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hA : ∀ x ∈ A.target, V x = FlowConstruction.partialChartField A.symm
      (fun _ : Z × ℝ => (0, 1)) x)
    (hC : ∀ x ∈ C.target, V x = FlowConstruction.partialChartField C.symm
      (fun _ : Z × ℝ => (0, 1)) x)
    {T : ℝ} (hpA : ((0 : Z), T) ∈ A.source) (hpC : ((0 : Z), T) ∈ C.source)
    (hpoint : A (0, T) = C (0, T)) :
    ∃ (ε : ℝ) (P : PartialDiffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) Z Z ∞) (v : Z → ℝ),
      0 < ε ∧ (0 : Z) ∈ P.source ∧ P 0 = 0 ∧ v 0 = 0 ∧ ContDiff ℝ ∞ v ∧
      ∀ t ∈ Ioo (T - ε) (T + ε), ∀ z ∈ P.source,
        (z, t) ∈ A.source ∧ (P z, t + v z) ∈ C.source ∧
          A (z, t) = C (P z, t + v z) := by
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ Z
  let D := e.toDiffeomorph.toPartialDiffeomorph
  have hpush (p : ℝ × Z) (_ : p ∈ D.source) :
      fderiv ℝ D p (1, 0) = ((0 : Z), (1 : ℝ)) := by
    change fderiv ℝ e p (1, 0) = ((0 : Z), (1 : ℝ))
    rw [e.fderiv]
    rfl
  have hfield (B : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞)
      (hB : ∀ x ∈ B.target, V x = FlowConstruction.partialChartField B.symm
        (fun _ : Z × ℝ => (0, 1)) x) :
      ∀ x ∈ (D.trans B).target, V x = FlowConstruction.partialChartField (D.trans B).symm
        (fun _ : ℝ × Z => (1, 0)) x := by
    intro x hx
    exact (hB x hx.1).trans
      (MorseCancellation.partialChartField_of_model_conjugacy D B
        (fun _ : ℝ × Z => (1, 0)) (fun _ : Z × ℝ => (0, 1)) hpush hx).symm
  have hAs : (T, (0 : Z)) ∈ (D.trans A).source := ⟨mem_univ _, hpA⟩
  have hCs : (T, (0 : Z)) ∈ (D.trans C).source := ⟨mem_univ _, hpC⟩
  obtain ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, hformula⟩ :=
    exists_global_native_transition_phase (D.trans A) (D.trans C) V
      (hfield A hA) (hfield C hC) hAs hCs hpoint
  refine ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, ?_⟩
  intro t ht z hz
  have hh := hformula t ht z hz
  exact ⟨hh.1.2, hh.2.1.2, hh.2.2⟩

open MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}

theorem exists_native_endpoint_slice_phase (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : A.source = U ×ˢ univ) (h0U : 0 ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hΦ : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (hA : ∀ y ∈ A.target, V y = FlowConstruction.partialChartField A.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    {c r δ T : ℝ} (hδ : 0 < δ)
    (hbox : closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source)
    (hslice : ∀ z : Fin m → ℝ, ‖z‖ ≤ δ →
      cubicFlowCylinder σ a (z, T) ∈ ball (c, (0 : Fin m → ℝ)) r)
    (hpoint : Φ (cubicFlowCylinder σ a (0, T)) = A (0, T)) :
    ∃ (P : PartialDiffeomorph 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin m → ℝ)
        (Fin m → ℝ) (Fin m → ℝ) ∞) (v : (Fin m → ℝ) → ℝ),
      (0 : Fin m → ℝ) ∈ P.source ∧ P 0 = 0 ∧ v 0 = 0 ∧ ContDiff ℝ ∞ v ∧
      P.target ⊆ U ∧
      (∀ z ∈ P.source, cubicFlowCylinder σ a (z, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r) ∧
      ∀ z ∈ P.source, Φ (cubicFlowCylinder σ a (z, T)) = A (P z, T + v z) := by
  let C := cubicFlowCylinderChart σ ha
  let B := C.trans Φ
  have hB0 : ((0 : Fin m → ℝ), T) ∈ B.source :=
    ⟨mem_univ _, hbox (ball_subset_closedBall (hslice 0 (by simpa using hδ.le)))⟩
  have hBfield : ∀ y ∈ B.target, V y = FlowConstruction.partialChartField B.symm
      (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y := by
    intro y hy
    exact (hΦ y hy.1).trans
      (partialChartField_of_model_conjugacy C Φ
        (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) (cubicDescent σ (-(a ^ 2)))
        (fun p _ => cubicFlowCylinder_pushforward_vertical σ a p) hy).symm
  have hA0 : ((0 : Fin m → ℝ), T) ∈ A.source := by
    rw [hsource]
    exact ⟨h0U, mem_univ _⟩
  obtain ⟨ε, P, v, hε, hP0, hPfix, hv0, hv, hformula⟩ :=
    FlowSuspension.exists_time_last_native_transition_phase B A V hBfield hA hB0 hA0 hpoint
  let Q := PartialChart.restrictSource P (isOpen_ball : IsOpen (ball (0 : Fin m → ℝ) δ))
  have hT : T ∈ Ioo (T - ε) (T + ε) := ⟨by linarith, by linarith⟩
  have hQ0 : (0 : Fin m → ℝ) ∈ Q.source := ⟨hP0, mem_ball_self hδ⟩
  refine ⟨Q, v, hQ0, hPfix, hv0, hv, ?_, ?_, ?_⟩
  · intro z hz
    have hu := Q.map_target' hz
    have hh := (hformula T hT (Q.symm z) hu.1).2.1
    rw [hsource] at hh
    have hi : P (Q.symm z) = z := Q.right_inv' hz
    exact hi ▸ hh.1
  · intro z hz
    exact ball_subset_closedBall (hslice z
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz.2)))
  · intro z hz
    exact (hformula T hT z hz.1).2.2

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
