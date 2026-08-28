import Wikipedia.HopfProblem.DegreeCollapseNativeAxisGermChart
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationModel

/-!
# Adjusting the native transverse orientation without changing the cubic

Negating every transverse coordinate fixes the axis and preserves every
signed quadratic transverse form. In odd transverse rank, it reverses the
determinant of the actual endpoint transition. This includes transverse
rank five in the six-dimensional cancellation model.
-/

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def transverseNegation : (ℝ × V) ≃L[ℝ] (ℝ × V) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

theorem transverseNegation_apply (p : ℝ × V) : transverseNegation p = (p.1, -p.2) := rfl

theorem transverseNegation_axis (s : ℝ) : transverseNegation (s, (0 : V)) = (s, 0) := by
  simp only [transverseNegation_apply, neg_zero]

theorem transverseBlock_comp_negation (L : (ℝ × V) →L[ℝ] (ℝ × V)) :
    AxisCoordinates.transverseBlock (L.comp transverseNegation.toContinuousLinearMap) =
      -AxisCoordinates.transverseBlock L := by
  apply ContinuousLinearMap.ext
  intro z
  change (L (0, -z)).2 = -(L (0, z)).2
  have he : ((0 : ℝ), -z) = -(0, z) := by simp
  rw [he, map_neg]
  rfl

theorem det_neg_of_odd (hodd : Odd (Module.finrank ℝ V)) (T : V →L[ℝ] V) :
    (-T).toLinearMap.det = -T.toLinearMap.det := by
  change (-T.toLinearMap).det = _
  rw [← neg_one_smul ℝ T.toLinearMap, LinearMap.det_smul, hodd.neg_one_pow]
  simp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def negateTransverseChart
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞ :=
  transverseNegation.toDiffeomorph.toPartialDiffeomorph.trans Φ

theorem negateTransverseChart_apply
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) (p : ℝ × V) :
    negateTransverseChart Φ p = Φ (transverseNegation p) := rfl

theorem negateTransverseChart_axis
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) (s : ℝ) :
    negateTransverseChart Φ (s, 0) = Φ (s, 0) := by
  rw [negateTransverseChart_apply, transverseNegation_axis]

theorem negateTransverseChart_axis_source
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞) (s : ℝ) :
    (s, (0 : V)) ∈ (negateTransverseChart Φ).source ↔ (s, (0 : V)) ∈ Φ.source := by
  change (s, (0 : V)) ∈ univ ∧ transverseNegation (s, 0) ∈ Φ.source ↔ _
  simp only [mem_univ, transverseNegation_axis, true_and]

/-- The determinant sign change is computed from the actual native transition. -/
theorem det_transition_negateTransverseChart
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    (hodd : Odd (Module.finrank ℝ V)) {s : ℝ}
    (hs : (s, (0 : V)) ∈ (Φ.trans Ψ.symm).source) :
    (AxisCoordinates.transverseBlock
      (fderiv ℝ (Ψ.symm ∘ negateTransverseChart Φ) (s, 0))).toLinearMap.det =
      -(AxisCoordinates.transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))).toLinearMap.det := by
  have hr : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (s, (0 : V)) :=
    ((Φ.trans Ψ.symm).contMDiffOn_toFun.contDiffOn.contDiffAt
      ((Φ.trans Ψ.symm).open_source.mem_nhds hs)).differentiableAt (by simp)
  have hre : DifferentiableAt ℝ (Ψ.symm ∘ Φ) (transverseNegation (s, (0 : V))) := by
    simpa only [transverseNegation_axis] using hr
  have heq : (Ψ.symm ∘ negateTransverseChart Φ) =
      (Ψ.symm ∘ Φ) ∘ (transverseNegation (V := V)) := rfl
  rw [heq, fderiv_comp _ hre (transverseNegation (V := V)).differentiableAt,
    (transverseNegation (V := V)).fderiv, transverseNegation_axis,
    transverseBlock_comp_negation, det_neg_of_odd hodd]

theorem cubic_transverseNegation {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    cubic σ t (transverseNegation p) = cubic σ t p := by
  simp [cubic, transverseNegation_apply]

/-- Every original cubic equation is retained on the reflected chart's actual source. -/
theorem negateTransverseChart_cubic {m : ℕ} (σ : Fin m → ℝ) (t b : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    {f : M → ℝ} (hf : ∀ p ∈ Φ.source, f (Φ p) = b + cubic σ t p)
    {p : Model m} (hp : p ∈ (negateTransverseChart Φ).source) :
    f (negateTransverseChart Φ p) = b + cubic σ t p := by
  have hp' : transverseNegation p ∈ Φ.source := hp.2
  rw [negateTransverseChart_apply, hf _ hp', cubic_transverseNegation]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
