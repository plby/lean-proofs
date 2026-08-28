import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumEnergy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonRealization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponentialPolygon

/-! # Sampling minimum rotations into the actual complex-structure polygon model -/

noncomputable section

open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices Exponential

variable {n m : ℕ} {a : ComplexStructures.Space n}

def rotationVertices (τ : Fin (m + 2) → ℝ) (P : AnticommutingStructures.Space a) :
    ComplexStructureVertices.Space n m :=
  fun i ↦ AnticommutingStructures.rotation P (τ i.castSucc.succ * Real.pi)

theorem continuous_rotationVertices (a : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    Continuous (rotationVertices (a := a) τ) := by
  apply continuous_pi
  intro i
  let phase : C(AnticommutingStructures.Space a, ℝ × AnticommutingStructures.Space a) :=
    ⟨fun P ↦ (τ i.castSucc.succ * Real.pi, P), continuous_const.prodMk continuous_id⟩
  let rot : C(ℝ × AnticommutingStructures.Space a, ComplexStructures.Space n) :=
    ⟨fun p ↦ AnticommutingStructures.rotation p.2 p.1,
      AnticommutingStructures.continuous_rotation a⟩
  exact (rot.comp phase).continuous

theorem forget_rotationVertices (τ : Fin (m + 2) → ℝ) (P : AnticommutingStructures.Space a) :
    forget (rotationVertices τ P) = Polygon.exponentialVertices (toSymplectic a) τ
      (Real.pi • (AnticommutingStructures.generatorParameter P).val.val) := by
  funext i
  change toSymplectic (AnticommutingStructures.rotation P (τ i.castSucc.succ * Real.pi)) = _
  rw [AnticommutingStructures.rotation_toSymplectic]
  simp only [Polygon.exponentialVertices, smul_smul]

theorem rotation_endpoint (a b : ComplexStructures.Space n)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (P : AnticommutingStructures.Space a) :
    toSymplectic a * exp (Real.pi • (AnticommutingStructures.generatorParameter P).val.val) =
      toSymplectic b := by
  have he : exp (Real.pi • (AnticommutingStructures.generatorParameter P).val.val) =
      Cayley.relative a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [ComplexStructures.exp_pi, ComplexStructures.antipode_operator]
    exact hanti.symm
  rw [he, Cayley.relative, mul_inv_cancel_left]

theorem compatibleTarget_of_norm_lt {K : SkewSpace n} (hK : ‖K‖ < ShortLog.radius n) :
    K ∈ compatibleTarget n := by
  apply ShortLog.radius_closedBall n
  rw [mem_closedBall, dist_zero_right K]
  exact hK.le

variable (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (P : AnticommutingStructures.Space a)
    (hsmall : ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)

include hzero hone hanti hsmall

theorem generator_rotationVertices (i : Fin (m + 1)) :
    generator a b (rotationVertices τ P) i = (τ i.succ - τ i.castSucc) •
      (Real.pi • (AnticommutingStructures.generatorParameter P).val.val) := by
  rw [← generator_forget, forget_rotationVertices]
  exact Polygon.generator_exponentialVertices (toSymplectic a) (toSymplectic b)
    τ hzero hone _ (rotation_endpoint a b hanti P)
    (fun j ↦ compatibleTarget_of_norm_lt (hsmall j)) i

theorem rotationVertices_admissible : rotationVertices τ P ∈ admissible a b m := by
  apply admissible_of_forget a b
  · rw [forget_rotationVertices]
    exact Polygon.exponentialVertices_admissible (toSymplectic a) (toSymplectic b) τ hzero hone _
      (rotation_endpoint a b hanti P) (fun i ↦ compatibleTarget_of_norm_lt (hsmall i))
  · intro i
    rw [generator_rotationVertices a b τ hzero hone hanti P hsmall]
    exact hsmall i

theorem path_rotationVertices (hτ : StrictMono τ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    path a b τ hτ (rotationVertices τ P)
      (rotationVertices_admissible a b τ hzero hone hanti P hsmall) t =
        AnticommutingStructures.rotation P (t * Real.pi) := by
  apply toSymplectic_injective
  rw [path_toSymplectic, forget_rotationVertices,
    Polygon.path_exponentialVertices (toSymplectic a) (toSymplectic b) τ hτ hzero hone _
      (rotation_endpoint a b hanti P) (fun i ↦ compatibleTarget_of_norm_lt (hsmall i)) ht,
    AnticommutingStructures.rotation_toSymplectic, smul_smul]

theorem energy_rotationVertices (hτ : StrictMono τ) :
    energy a b τ (rotationVertices τ P) = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2 := by
  rw [energy, forget_rotationVertices,
    Polygon.energy_exponentialVertices (toSymplectic a) (toSymplectic b) τ hτ hzero hone _
      (rotation_endpoint a b hanti P) (fun i ↦ compatibleTarget_of_norm_lt (hsmall i))]
  apply (QuaternionicColumns.squareNorm_eq_iff_complexStructure
    (Real.pi • (AnticommutingStructures.generatorParameter P).val.val) ?_).mpr
      ⟨(AnticommutingStructures.generatorParameter P).val, rfl⟩
  rw [ComplexStructures.exp_pi, ComplexStructures.antipode_operator]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
