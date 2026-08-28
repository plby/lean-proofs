import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonTangent

/-!
# The differential of polygon energy in complex-structure coordinates

The inverse Cayley chart is the restriction of the symplectic inverse chart.
The chain rule therefore gives the restricted differential. Since every
velocity jump is an allowed anticommuting direction, its vanishing is exactly
the critical-point condition for the restricted energy.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices NoExoticSixSphere.HilbertSchmidt

variable {n m : ℕ}

private theorem real_linear_hasFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) : HasFDerivAt L L x := L.hasFDerivAt

def localEnergy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (W : Model v) : ℝ :=
  energy a b τ ((atVertices v).symm W)

theorem localEnergy_eq (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) :
    localEnergy a b τ v =
      Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v) ∘ modelInclusion v := by
  funext W
  change Polygon.energy (toSymplectic a) (toSymplectic b) τ
    (forget ((atVertices v).symm W)) = _
  rw [forget_chart_symm]
  rfl

theorem hasFDerivAt_localEnergy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    HasFDerivAt (localEnergy a b τ v)
      ((fderiv ℝ (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v)) 0).comp
        (modelInclusion v)) 0 := by
  have hf := ((Polygon.contDiffAt_localEnergy (toSymplectic a) (toSymplectic b) τ
    (forget v) (admissible_forget a b hv)).differentiableAt (by simp)).hasFDerivAt
  have hf' : HasFDerivAt (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v))
      (fderiv ℝ (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v)) 0)
      (modelInclusion v 0) := by simpa only [map_zero] using hf
  rw [localEnergy_eq]
  exact HasFDerivAt.comp (𝕜 := ℝ) (E := Model v) (F := VertexSpace.Model n m) (G := ℝ)
    (0 : Model v) hf' (real_linear_hasFDerivAt (E := Model v) (F := VertexSpace.Model n m)
      (modelInclusion v) 0)

theorem fderiv_localEnergy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    fderiv ℝ (localEnergy a b τ v) 0 =
      (fderiv ℝ (Polygon.localEnergy (toSymplectic a) (toSymplectic b) τ (forget v)) 0).comp
        (modelInclusion v) :=
  realFDeriv_eq_of_hasFDerivAt (E := Model v) (F := ℝ) (hasFDerivAt_localEnergy a b τ v hv)

theorem fderiv_localEnergy_apply (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) (W : Model v) :
    fderiv ℝ (localEnergy a b τ v) 0 W =
      (-4 : ℝ) * ∑ j : Fin m,
        innerForm (Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) j).val
          (W j).val := by
  rw [fderiv_localEnergy a b τ v hv, ContinuousLinearMap.comp_apply,
    ← Polygon.mfderiv_energy_eq_localEnergy (toSymplectic a) (toSymplectic b) τ
      (forget v) (admissible_forget a b hv)]
  exact Polygon.mfderiv_energy_apply (toSymplectic a) (toSymplectic b) τ
    (forget v) (admissible_forget a b hv) (modelInclusion v W)

theorem fderiv_localEnergy_eq_zero_iff (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (v : ComplexStructureVertices.Space n m)
    (hv : v ∈ admissible a b m) :
    fderiv ℝ (localEnergy a b τ v) 0 = 0 ↔
      Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) = 0 := by
  constructor
  · intro hzero
    let Z := Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v)
    have he := fderiv_localEnergy_apply a b τ v hv (jumpDirection a b τ v hv)
    rw [hzero, zero_apply] at he
    have hsum : ∑ j : Fin m, squareNorm (Z j).val = 0 := by
      change 0 = (-4 : ℝ) * ∑ j : Fin m, squareNorm (Z j).val at he
      linarith only [he]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) ↦ squareNorm_nonneg (Z j).val)).mp hsum
    funext j
    apply Subtype.ext
    exact (squareNorm_eq_zero_iff _).mp (hterm j (Finset.mem_univ j))
  · intro hzero
    apply ContinuousLinearMap.ext
    intro W
    have he := fderiv_localEnergy_apply a b τ v hv W
    have hz : (-4 : ℝ) * ∑ j : Fin m,
        innerForm (Polygon.velocityJump (toSymplectic a) (toSymplectic b) τ (forget v) j).val
          (W j).val = 0 := by simp [hzero, innerForm]
    exact he.trans hz

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
