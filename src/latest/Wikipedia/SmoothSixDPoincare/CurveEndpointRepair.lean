import Wikipedia.SmoothSixDPoincare.CompactBoundaryDerivativeRepair
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Repairing curve endpoint derivatives without moving either endpoint

The scalar defining function `t (1 - t)` has precisely the two endpoint zeros,
with nonzero derivative at each. The constructed native boundary-derivative
repair therefore makes the curve immersive at both endpoints while preserving
their exact values through a relative homotopy.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

def endpointFunction (t : ℝ) : ℝ := t * (1 - t)

theorem contDiff_endpointFunction : ContDiff ℝ ∞ endpointFunction := by
  unfold endpointFunction
  fun_prop

theorem endpointFunction_eq_zero_iff (t : ℝ) : endpointFunction t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [endpointFunction, mul_eq_zero, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

theorem fderiv_endpointFunction (t v : ℝ) :
    fderiv ℝ endpointFunction t v = v * (1 - 2 * t) := by
  have hd : HasDerivAt endpointFunction (1 * (1 - t) + t * (0 - 1)) t :=
    (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have heq : 1 * (1 - t) + t * (0 - 1) = 1 - 2 * t := by ring
  rw [heq] at hd
  rw [hd.hasFDerivAt.fderiv]
  rfl

theorem injective_endpointFunction_derivative {t : ℝ} (ht : endpointFunction t = 0)
    {v : ℝ} (hv : fderiv ℝ endpointFunction t v = 0) : v = 0 := by
  rw [fderiv_endpointFunction] at hv
  rcases (endpointFunction_eq_zero_iff t).mp ht with rfl | rfl
  · simpa using hv
  · norm_num at hv
    exact hv

end Wikipedia.SmoothSixDPoincare.CurveImmersion

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- A smooth curve can be made immersive at both endpoints while fixing their exact values. -/
theorem exists_curve_endpoint_derivative_repair (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧ f.HomotopicRel g ({0, 1} : Set ℝ) ∧
      ∀ t ∈ ({0, 1} : Set ℝ), Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let X := ({0, 1} : Set ℝ)
  let : Fintype X := ((Set.finite_singleton (1 : ℝ)).insert 0).fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z X := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ X := IsManifold.of_discreteTopology _
  let b : X → ℝ := Subtype.val
  have hb : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ b := contMDiff_of_discreteTopology
  have hrange : range b = ({0, 1} : Set ℝ) := by ext t; simp [b, X]
  have hzero : ∀ x, CurveImmersion.endpointFunction (b x) = 0 := by
    intro x
    apply (CurveImmersion.endpointFunction_eq_zero_iff _).mpr
    exact x.property
  have hzset : {t | CurveImmersion.endpointFunction t = 0} = ({0, 1} : Set ℝ) := by
    ext t
    simp only [mem_ofPred_eq, CurveImmersion.endpointFunction_eq_zero_iff,
      mem_insert_iff, mem_singleton_iff]
  have hd : Module.finrank ℝ Z + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  obtain ⟨g, hg, hrel, hi⟩ := exists_compact_boundary_derivative_repair f hf hb
    CurveImmersion.contDiff_endpointFunction hzero hd
    (fun _ ht _ _ hv => CurveImmersion.injective_endpointFunction_derivative ht hv)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [hzset] using hrel
  · simpa only [hrange] using hi

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
