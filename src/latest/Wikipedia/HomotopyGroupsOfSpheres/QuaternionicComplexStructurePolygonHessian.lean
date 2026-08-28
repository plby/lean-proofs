import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonCriticalIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonHessian

/-!
# A negative subspace of the actual complex-structure polygon Hessian

The local energy is the ambient symplectic local energy composed with the
linear model inclusion. Along straight lines their second derivatives agree.
At a restricted critical point this identifies the actual Hessians on the
included directions, so the constrained negative variations give an
injective `n`-dimensional negative subspace.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres

private theorem real_secondDerivative_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hc : fderiv ℝ f 0 = 0) (v : E) :
    deriv (deriv (fun s : ℝ ↦ f (s • v))) 0 = realHessian (E := E) f 0 v v := by
  have hγ : ContDiffAt ℝ 2 (fun s : ℝ ↦ s • v) 0 :=
    (contDiff_id.smul contDiff_const).contDiffAt
  have hf' : ContDiffAt ℝ 2 f ((0 : ℝ) • v) := by simpa only [zero_smul] using hf
  have hc' : fderiv ℝ f ((0 : ℝ) • v) = 0 := by simpa only [zero_smul] using hc
  have h := NoExoticSixSphere.SecondDerivativeAtCritical.deriv_deriv_comp
    (E := E) hf' hγ hc'
  have hd : deriv (fun s : ℝ ↦ s • v) 0 = v :=
    real_deriv_eq_of_hasDerivAt (E := E) (real_hasDerivAt_smul v 0)
  simpa only [zero_smul, hd, realHessian] using h

namespace QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

theorem contDiffAt_localEnergy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    ContDiffAt ℝ ∞ (localEnergy a b τ v) 0 := by
  have hf : ContDiffAt ℝ ∞
      (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v))
      (modelInclusion v 0) := by
    simpa only [map_zero] using Polygon.contDiffAt_localEnergy (toSymplectic a) (toSymplectic b)
      τ (forget v) (admissible_forget a b hv)
  have hL : ContDiff ℝ ∞ (modelInclusion v) :=
    finiteLinearMap_contDiff (E := Model v) (F := VertexSpace.Model n m)
      (modelInclusion v).toLinearMap
  rw [localEnergy_eq]
  exact hf.comp (0 : Model v) hL.contDiffAt

def localHessian (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) : RealHessianForm (Model v) :=
  realHessian (E := Model v) (localEnergy a b τ v) 0

theorem localHessian_diagonal (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) (W : Model v) :
    localHessian a b τ v W W =
      Polygon.localHessian (toSymplectic a) (toSymplectic b) τ (forget v)
        (modelInclusion v W) (modelInclusion v W) := by
  have hc : fderiv ℝ
      (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v)) 0 = 0 := by
    rw [← Polygon.mfderiv_energy_eq_localEnergy (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv)]
    exact critical_forget a b τ v hv hcrit
  have hg := real_secondDerivative_line (E := Model v) (localEnergy a b τ v)
    ((contDiffAt_localEnergy a b τ v hv).of_le (WithTop.coe_le_coe.mpr le_top)) hcrit W
  have hf := real_secondDerivative_line (E := VertexSpace.Model n m)
    (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v))
    ((Polygon.contDiffAt_localEnergy (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv)).of_le (WithTop.coe_le_coe.mpr le_top))
    hc (modelInclusion v W)
  have heq : (fun s : ℝ ↦ localEnergy a b τ v (s • W)) =
      (fun s : ℝ ↦ Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v)
        (s • modelInclusion v W)) := by
    funext s
    rw [localEnergy_eq, Function.comp_apply, map_smul]
  have he := congrArg (fun f : ℝ → ℝ ↦ deriv (deriv f) 0) heq
  rw [hg, hf] at he
  exact he

theorem secondDerivative_eq_localHessian (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0) (W : Model v) :
    deriv (deriv (fun s ↦ energy a b τ (vertexVariation v W s))) 0 =
      localHessian a b τ v ((-(1 / 2) : ℝ) • W) ((-(1 / 2) : ℝ) • W) := by
  rw [localHessian_diagonal a b τ v hv hcrit, map_smul]
  simpa only [energy, forget_vertexVariation] using
    Polygon.secondDerivative_eq_localHessian (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv) (critical_forget a b τ v hv hcrit) (modelInclusion v W)

theorem exists_negative_hessianFamily_of_critical (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (hcrit : fderiv ℝ (localEnergy a b τ v) 0 = 0)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (habove : ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] Model v, Function.Injective L ∧
      ∀ c, c ≠ 0 → localHessian a b τ v (L c) (L c) < 0 := by
  obtain ⟨R, hR, hneg⟩ :=
    exists_negative_vertexFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin n → ℝ) →ₗ[ℝ] Model v :=
    (realScalarOperator (Model v) (-(1 / 2))).toLinearMap.comp R
  have hL : Function.Injective L := by
    intro c d h
    apply hR
    change (-(1 / 2) : ℝ) • R c = (-(1 / 2) : ℝ) • R d at h
    exact (smul_right_injective (M := Model v) (by norm_num : (-(1 / 2) : ℝ) ≠ 0)) h
  refine ⟨L, hL, fun c hc ↦ ?_⟩
  have h := hneg c hc
  rwa [secondDerivative_eq_localHessian a b τ v hv hcrit (R c)] at h

end QuaternionicColumns.ComplexStructurePolygon
end Wikipedia.HomotopyGroupsOfSpheres
