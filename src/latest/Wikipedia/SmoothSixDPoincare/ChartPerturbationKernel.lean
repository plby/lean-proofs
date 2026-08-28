import Wikipedia.SmoothSixDPoincare.NativeImmersionChart
import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Tangential derivative kernels survive weighted chart translations

In every direction annihilated by the scalar-weight derivative, the old and
new map derivatives have the same kernel. Thus multiplying a defining function
by a source cutoff preserves the trivial-common-kernel condition along its
zero set. This condition can be retained throughout finite boundary repair.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

/-- A chart translation preserves derivative kernels in every direction in the kernel of
the weight derivative. This concerns the actual native derivatives on the target manifold. -/
theorem derivative_eq_zero_iff_of_weight_derivative_eq_zero
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {β : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {a : F} (ha : Valid c f β a)
    {x v : E} (hweight : fderiv ℝ β x v = 0) :
    mfderiv 𝓘(ℝ, E) J (perturb c f β a) x v = 0 ↔ mfderiv 𝓘(ℝ, E) J f x v = 0 := by
  by_cases hx : f x ∈ c.source
  · have hsmooth := contMDiff_perturb c hf hβ.contMDiff hsupport ha
    have hgx := perturb_mem_source c f β ha hx
    have hcf : ContDiffAt ℝ ∞ (c ∘ f) x :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp x hf.contMDiffAt)
        |>.contDiffAt
    have hcd : HasFDerivAt (fun y => c (f y) + β y • a)
        (fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a) x :=
      (hcf.differentiableAt (by simp)).hasFDerivAt.add
        ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)
    have heq : (c ∘ perturb c f β a) =ᶠ[𝓝 x] (fun y => c (f y) + β y • a) := by
      filter_upwards [(c.open_source.preimage hf.continuous).mem_nhds hx] with y hy
      exact chart_perturb c f β ha hy
    have hderiv : fderiv ℝ (c ∘ perturb c f β a) x =
        fderiv ℝ (c ∘ f) x + (fderiv ℝ β x).smulRight a :=
      heq.fderiv_eq.trans hcd.fderiv
    rw [← ManifoldImmersion.fderiv_chart_eq_zero_iff c
      (hsmooth.mdifferentiableAt (by simp)) hgx v,
      ← ManifoldImmersion.fderiv_chart_eq_zero_iff c
        (hf.mdifferentiableAt (by simp)) hx v, hderiv]
    change fderiv ℝ (c ∘ f) x v + fderiv ℝ β x v • a = 0 ↔ fderiv ℝ (c ∘ f) x v = 0
    rw [hweight, zero_smul, add_zero]
  · have hn : x ∉ tsupport β := fun ht => hx (hsupport ht)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hn
    have heq : perturb c f β a =ᶠ[𝓝 x] f := by
      filter_upwards [hzero] with y hy
      exact perturb_eq_of_zero c f β a hy
    rw [heq.mfderiv_eq]
    rfl

/-- A cutoff times a defining function annihilates every tangent direction along its zero set. -/
theorem fderiv_cutoff_mul_eq_zero {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hρ : ContDiff ℝ ∞ ρ) {x v : E} (hx : ρ x = 0) (hv : fderiv ℝ ρ x v = 0) :
    fderiv ℝ (fun y => ψ y * ρ y) x v = 0 := by
  rw [fderiv_fun_mul (hψ.differentiable (by simp) x) (hρ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    hx, hv, mul_zero, zero_mul, add_zero]

/-- The common-kernel condition with a defining function is preserved along its entire zero
set by every valid cutoff-weighted chart translation. -/
theorem common_kernel_preserved_on_zero_set
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N} {ψ ρ : E → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ)
    (hsupport : tsupport (fun y => ψ y * ρ y) ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f (fun y => ψ y * ρ y) a)
    (hcommon : ∀ x, ρ x = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f x v = 0 →
      fderiv ℝ ρ x v = 0 → v = 0) :
    ∀ x, ρ x = 0 → ∀ v,
      mfderiv 𝓘(ℝ, E) J (perturb c f (fun y => ψ y * ρ y) a) x v = 0 →
      fderiv ℝ ρ x v = 0 → v = 0 := by
  intro x hx v hzero hv
  have hweight := fderiv_cutoff_mul_eq_zero hψ hρ hx hv
  have hold := (derivative_eq_zero_iff_of_weight_derivative_eq_zero c hf (hψ.mul hρ)
    hsupport ha hweight).mp hzero
  exact hcommon x hx v hold hv

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
