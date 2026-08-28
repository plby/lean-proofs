import Wikipedia.SmoothSixDPoincare.InducedSheetChart
import Wikipedia.SmoothSixDPoincare.SphereChartOrientation

/-!
# The fixed sphere signs in an actual retained ambient sheet chart

Recover the native sphere chart from the full clean ambient chart. Its
outward orientation is consistent along the retained center interval.
The exact parametrization identity then compares the fixed sphere normal
Jacobians with the actual normal determinants in the retained sheet chart.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V A B E M : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- The sphere's fixed normal signs agree with the normal determinants in the actual
ambient sheet chart at both retained endpoints. No source parametrization is supplied. -/
theorem opposite_normalJacobians_iff_retained_sheet
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) 𝓘(ℝ, E) ((ℝ × A) × B) M ∞)
    (F : Metric.sphere (0 : V) 1 → M) (hF : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ F)
    (hinjF : Injective F) (hiF : ∀ x, Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) F x))
    (hclean : ∀ z ∈ Φ.source, Φ z ∈ range F ↔ z.2 = 0)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, ((t, (0 : A)), (0 : B)) ∈ Φ.source)
    (hdim : Module.finrank ℝ (ℝ × A) = n)
    (q : M → (ℝ × A)) (r : (ℝ × (ℝ × A)) ≃L[ℝ] V)
    (x₀ x₁ : Metric.sphere (0 : V) 1)
    (hx₀ : F x₀ = Φ ((0, 0), 0)) (hx₁ : F x₁ = Φ ((1, 0), 0))
    (hq₀ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₀))
    (hq₁ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x₁))
    (hi₀ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀).IsInvertible)
    (hi₁ : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁).IsInvertible) :
    normalJacobian r x₀ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀) *
      normalJacobian r x₁ (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁) < 0 ↔
      (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0)).det *
        (fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0)).det < 0 := by
  let _ : Nonempty (Metric.sphere (0 : V) 1) := ⟨x₀⟩
  obtain ⟨c, hcS, _, hFc, _⟩ := NativeSheetCoordinates.exists_induced_sheet_chart Φ F
    hF hinjF hclean (by simpa only [finrank_euclideanSpace_fin] using hdim.symm) hiF
  let a : ℝ → (ℝ × A) := fun t => (t, 0)
  have ha : ContinuousOn a (Icc (0 : ℝ) 1) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have haS : MapsTo a (Icc (0 : ℝ) 1) c.source := by
    intro t ht
    rw [hcS]
    exact hline t ht
  have h₀ : c (a 0) = x₀ := hinjF ((hFc _ (haS (by simp))).trans hx₀.symm)
  have h₁ : c (a 1) = x₁ := hinjF ((hFc _ (haS (by simp))).trans hx₁.symm)
  let A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) :=
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₀
  let A₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) :=
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x₁
  have hsign := opposite_normalJacobians_iff_chartDet c r a ha haS A₀ A₁ hi₀ hi₁
  have hcoeff (t : ℝ) (x : Metric.sphere (0 : V) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (hx : c (a t) = x) (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × A) ∞ q (F x)) :
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x :
        EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)).comp
        (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) :
          (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
      fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (t, 0) := by
    have hqF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ × A) ∞ (q ∘ F) (c (a t)) := by
      rw [hx]
      exact hq.comp x hF.contMDiffAt
    have hchain := mfderiv_comp (a t) (hqF.mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) (haS ht))
    have heq : ((q ∘ F) ∘ c) =ᶠ[𝓝 (a t)] (fun w => q (Φ (w, 0))) := by
      filter_upwards [c.open_source.mem_nhds (haS ht)] with w hw
      exact congrArg q (hFc w hw)
    have hpoint : (mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) (c (a t)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A)) =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ × A) (q ∘ F) x := by rw [hx]
    rw [mfderiv_eq_fderiv] at hchain
    have h := hchain.symm.trans heq.fderiv_eq
    exact (congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] (ℝ × A) =>
      L.comp (mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a t) :
        (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n))) hpoint).symm.trans h
  rw [h₀, h₁] at hsign
  let C₀ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 0)
  let C₁ : (ℝ × A) →L[ℝ] EuclideanSpace ℝ (Fin n) := mfderiv 𝓘(ℝ, ℝ × A) (𝓡 n) c (a 1)
  have hc₀ : A₀.comp C₀ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (0, 0) :=
    hcoeff 0 x₀ (by simp) h₀ hq₀
  have hc₁ : A₁.comp C₁ = fderiv ℝ (fun w : ℝ × A => q (Φ (w, 0))) (1, 0) :=
    hcoeff 1 x₁ (by simp) h₁ hq₁
  change normalJacobian r x₀ A₀ * normalJacobian r x₁ A₁ < 0 ↔
    (A₀.comp C₀).det * (A₁.comp C₁).det < 0 at hsign
  rw [hc₀, hc₁] at hsign
  exact hsign

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates
