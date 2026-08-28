import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrixRotation
import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Explicit based two-cubes from symmetric unitary matrices

Pointwise division by the reference rotation makes the matrix family equal
to the identity on all four edges and at the reference parameter. This
gives a continuous map into Mathlib's native double-loop space. Its comparison
with the composite homotopy isomorphism is a separate step.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns

variable {N : Type*} [Fintype N] [DecidableEq N]

def basedRotation (s t : ℝ) (B : Space N) : SpGroup N :=
  rotation s t B * (rotation s t identity)⁻¹

theorem basedRotation_identity (s t : ℝ) :
    basedRotation s t (identity : Space N) = 1 := mul_inv_cancel _

theorem basedRotation_zero_left (t : ℝ) (B : Space N) : basedRotation 0 t B = 1 := by
  simp only [basedRotation, rotation_zero, inv_one, mul_one]

theorem basedRotation_pi_left (t : ℝ) (B : Space N) : basedRotation Real.pi t B = 1 := by
  rw [basedRotation, rotation_pi t B identity, mul_inv_cancel]

theorem basedRotation_zero_right (s : ℝ) (B : Space N) : basedRotation s 0 B = 1 := by
  rw [basedRotation, rotation_boundary s B identity, mul_inv_cancel]

theorem basedRotation_pi_right (s : ℝ) (B : Space N) : basedRotation s Real.pi B = 1 := by
  rw [basedRotation, rotation_boundary_pi s B identity, mul_inv_cancel]

theorem continuous_basedRotation :
    Continuous (fun z : (ℝ × ℝ) × Space N ↦ basedRotation z.1.1 z.1.2 z.2) := by
  have href : Continuous (fun z : (ℝ × ℝ) × Space N ↦
      rotation z.1.1 z.1.2 (identity : Space N)) :=
    continuous_rotation.comp (continuous_fst.prodMk continuous_const)
  exact continuous_rotation.mul href.inv

private def basedRotationMap : C((ℝ × ℝ) × Space N, SpGroup N) :=
  ⟨fun z ↦ basedRotation z.1.1 z.1.2 z.2, continuous_basedRotation⟩

def cubeAngles : C(Space N × (Fin 2 → I), (ℝ × ℝ) × Space N) where
  toFun z := (((z.2 0 : ℝ) * Real.pi, (z.2 1 : ℝ) * Real.pi), z.1)
  continuous_toFun := by
    have h₀ : Continuous (fun z : Space N × (Fin 2 → I) ↦ (z.2 0 : ℝ) * Real.pi) :=
      (continuous_subtype_val.comp ((continuous_apply 0).comp continuous_snd)).mul_const _
    have h₁ : Continuous (fun z : Space N × (Fin 2 → I) ↦ (z.2 1 : ℝ) * Real.pi) :=
      (continuous_subtype_val.comp ((continuous_apply 1).comp continuous_snd)).mul_const _
    exact (h₀.prodMk h₁).prodMk continuous_fst

def twoCubeFamily : C(Space N × (Fin 2 → I), SpGroup N) :=
  basedRotationMap.comp cubeAngles

theorem twoCubeFamily_boundary (B : Space N) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : twoCubeFamily (B, u) = 1 := by
  obtain ⟨r, hr⟩ := hu
  change basedRotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi) B = 1
  fin_cases r <;> rcases hr with hr | hr
  · change u 0 = 0 at hr
    rw [hr]
    simp only [Set.Icc.coe_zero, zero_mul]
    exact basedRotation_zero_left _ B
  · change u 0 = 1 at hr
    rw [hr]
    simpa only [Set.Icc.coe_one, one_mul] using basedRotation_pi_left ((u 1 : ℝ) * Real.pi) B
  · change u 1 = 0 at hr
    rw [hr]
    simp only [Set.Icc.coe_zero, zero_mul]
    exact basedRotation_zero_right _ B
  · change u 1 = 1 at hr
    rw [hr]
    simpa only [Set.Icc.coe_one, one_mul] using basedRotation_pi_right ((u 0 : ℝ) * Real.pi) B

def twoCube (B : Space N) : GenLoop (Fin 2) (SpGroup N) 1 :=
  ⟨twoCubeFamily.curry B, twoCubeFamily_boundary B⟩

def twoCubeMap : C(Space N, GenLoop (Fin 2) (SpGroup N) 1) where
  toFun := twoCube
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact twoCubeFamily.curry.continuous

theorem twoCubeMap_apply (B : Space N) (u : Fin 2 → I) :
    twoCubeMap B u =
      rotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi) B *
        (rotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi) identity)⁻¹ := rfl

theorem twoCubeMap_identity : twoCubeMap (identity : Space N) = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact basedRotation_identity _ _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
