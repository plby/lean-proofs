import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationModel
import Wikipedia.HopfProblem.DegreeCollapseLocalFunctionReplacement
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve

/-!
# A descending field adapted to the exact cubic charts

The polynomial model field is tangent to the scalar axis and strictly
decreases the cubic at every regular point. Its native pullback is smooth,
vanishes at the actual critical points, and retains that strict descent.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ} (σ : Fin m → ℝ)

def cubicDescent (t : ℝ) (p : Model m) : Model m :=
  (-(p.1 ^ 2 + t), fun i => -σ i * p.2 i)

theorem contDiff_cubicDescent (t : ℝ) : ContDiff ℝ ∞ (cubicDescent σ t) := by
  unfold cubicDescent
  fun_prop

theorem cubicDescent_axis (t s : ℝ) :
    cubicDescent σ t (s, 0) = (-(s ^ 2 + t)) • (1, (0 : Fin m → ℝ)) := by
  simp [cubicDescent]
  rfl

theorem differential_cubicDescent (t : ℝ) (p : Model m) :
    differential σ t p (cubicDescent σ t p) =
      -(p.1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * p.2 i) ^ 2 := by
  rw [differential_apply]
  simp only [cubicDescent]
  have hs : (∑ i, 2 * σ i * p.2 i * (-σ i * p.2 i)) =
      -2 * ∑ i, (σ i * p.2 i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- Strict descent follows from the actual nonzero differential, without extra sign assumptions. -/
theorem cubicDescent_strict {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p ≠ 0) :
    fderiv ℝ (cubic σ t) p (cubicDescent σ t p) < 0 := by
  rw [fderiv_cubic, differential_cubicDescent]
  by_contra hh
  have hsum : 0 ≤ ∑ i, (σ i * p.2 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : p.1 ^ 2 + t = 0 := by nlinarith [sq_nonneg (p.1 ^ 2 + t)]
  have hz : (∑ i, (σ i * p.2 i) ^ 2) = 0 := by
    have hle := le_of_not_gt hh
    rw [hx] at hle
    linarith
  have hy (i : Fin m) : σ i * p.2 i = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp hz
      i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  apply hp
  rw [fderiv_cubic]
  apply ContinuousLinearMap.ext
  intro v
  rw [differential_apply, hx]
  simp only [zero_mul, zero_add, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  calc
    2 * σ i * p.2 i * v.2 i = 2 * (σ i * p.2 i) * v.2 i := by ring
    _ = 0 := by rw [hy, mul_zero, zero_mul]

theorem cubicDescent_zero_of_critical {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p = 0) : cubicDescent σ t p = 0 := by
  rw [fderiv_cubic] at hp
  have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hp
  have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
  apply Prod.ext
  · simpa only [cubicDescent, Prod.fst_zero, neg_eq_zero] using hx'
  · funext i
    have hi := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hp
    have hi' : 2 * σ i * p.2 i = 0 := by
      simpa [differential_apply, Pi.single_apply] using hi
    change -σ i * p.2 i = 0
    nlinarith

variable {B M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

def nativeCubicDescent
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    (x : M) → TangentSpace 𝓘(ℝ, B) x :=
  FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)

theorem contMDiffOn_nativeCubicDescent [CompleteSpace B] [IsManifold 𝓘(ℝ, B) ∞ M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, nativeCubicDescent σ Φ t x⟩ : TangentBundle 𝓘(ℝ, B) M)) Φ.target :=
  FlowConstruction.contMDiffOn_partialChartField Φ.symm (contDiff_cubicDescent σ t)

/-- The actual critical set in a cubic chart agrees with the polynomial critical set. -/
theorem native_cubic_critical_iff
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {f : M → ℝ} {b t : ℝ}
    (hmodel : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    {x : M} (hx : x ∈ Φ.target) :
    x ∈ ManifoldMorse.criticalPoints B f ↔ fderiv ℝ (cubic σ t) (Φ.symm x) = 0 := by
  have h := LocalFunctionReplacement.replace_critical_iff Φ f
    ((contDiff_const (c := b)).add (contDiff_cubic σ t)) hx
  rw [LocalFunctionReplacement.replace_self Φ hmodel, fderiv_const_add] at h
  exact h

theorem nativeCubicDescent_zero
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {f : M → ℝ} {b t : ℝ}
    (hmodel : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    {x : M} (hx : x ∈ Φ.target) (hcrit : x ∈ ManifoldMorse.criticalPoints B f) :
    nativeCubicDescent σ Φ t x = 0 := by
  have hz := cubicDescent_zero_of_critical σ ((native_cubic_critical_iff σ Φ hmodel hx).mp hcrit)
  unfold nativeCubicDescent FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, hz, map_zero, map_zero]

/-- The exact sum-of-squares descent speed in the original manifold. -/
theorem nativeCubicDescent_speed
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b t : ℝ}
    (hmodel : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (nativeCubicDescent σ Φ t x) =
      -((Φ.symm x).1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * (Φ.symm x).2 i) ^ 2 := by
  have hcoord : (f ∘ Φ) =ᶠ[𝓝 (Φ.symm x)] (fun p => b + cubic σ t p) := by
    filter_upwards [Φ.open_source.mem_nhds (Φ.map_target' hx)] with p hp
    exact hmodel p hp
  have hder : fderiv ℝ (f ∘ Φ) (Φ.symm x) =
      fderiv ℝ (fun p => b + cubic σ t p) (Φ.symm x) := hcoord.fderiv_eq
  rw [fderiv_const_add, fderiv_cubic] at hder
  unfold nativeCubicDescent
  rw [FlowConstruction.mvfderiv_partialChartField hf Φ.symm _ hx]
  change fderiv ℝ (f ∘ Φ) (Φ.symm x) (cubicDescent σ t (Φ.symm x)) = _
  rw [hder, differential_cubicDescent]

/-- The model's strict descent is retained in the original native tangent bundle. -/
theorem nativeCubicDescent_strict
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b t : ℝ}
    (hmodel : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    {x : M} (hx : x ∈ Φ.target) (hreg : x ∉ ManifoldMorse.criticalPoints B f) :
    mvfderiv 𝓘(ℝ, B) f x (nativeCubicDescent σ Φ t x) < 0 := by
  have hcoord : (f ∘ Φ) =ᶠ[𝓝 (Φ.symm x)] (fun p => b + cubic σ t p) := by
    filter_upwards [Φ.open_source.mem_nhds (Φ.map_target' hx)] with p hp
    exact hmodel p hp
  have hder : fderiv ℝ (f ∘ Φ) (Φ.symm x) =
      fderiv ℝ (fun p => b + cubic σ t p) (Φ.symm x) := hcoord.fderiv_eq
  rw [fderiv_const_add] at hder
  unfold nativeCubicDescent
  rw [FlowConstruction.mvfderiv_partialChartField hf Φ.symm _ hx]
  change fderiv ℝ (f ∘ Φ) (Φ.symm x) (cubicDescent σ t (Φ.symm x)) < 0
  rw [hder]
  exact cubicDescent_strict σ (fun h => hreg ((native_cubic_critical_iff σ Φ hmodel hx).mpr h))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
