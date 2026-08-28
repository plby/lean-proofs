import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSections

/-!
# The standard action of `Sp(2)` on the quaternionic seven-sphere

The action is ordinary matrix multiplication. The preceding frame-completion
lemma proves that it preserves the unit sphere, and matrix associativity
supplies the action laws.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

local notation "ℍ" => Quaternion ℝ

/-- The usual matrix action on the quaternionic plane. -/
def planeAction (A : SpTwo) (v : QuaternionPlane) : QuaternionPlane :=
  WithLp.toLp 2 (A.val 0 0 * v.fst + A.val 0 1 * v.snd,
    A.val 1 0 * v.fst + A.val 1 1 * v.snd)

theorem planeAction_projection (A B : SpTwo) :
    planeAction A (projection B).val = (projection (A * B)).val := by
  apply (WithLp.equiv 2 (ℍ × ℍ)).injective
  apply Prod.ext <;> simp [planeAction, projection, Matrix.mul_apply, Fin.sum_univ_two]

theorem planeAction_mem (A : SpTwo) (v : BaseSphere) : planeAction A v.val ∈ BaseSphere := by
  obtain ⟨B, rfl⟩ := projection_surjective v
  rw [planeAction_projection]
  exact (projection (A * B)).property

/-- The natural action on the actual sphere. -/
def sphereAction (A : SpTwo) (v : BaseSphere) : BaseSphere :=
  ⟨planeAction A v.val, planeAction_mem A v⟩

@[simp] theorem sphereAction_projection (A B : SpTwo) :
    sphereAction A (projection B) = projection (A * B) :=
  Subtype.ext (planeAction_projection A B)

@[simp] theorem sphereAction_north (A : SpTwo) : sphereAction A north = projection A := by
  rw [← projection_one, sphereAction_projection, mul_one]

@[simp] theorem sphereAction_one (v : BaseSphere) : sphereAction 1 v = v := by
  obtain ⟨B, rfl⟩ := projection_surjective v
  rw [sphereAction_projection, one_mul]

theorem sphereAction_mul (A B : SpTwo) (v : BaseSphere) :
    sphereAction (A * B) v = sphereAction A (sphereAction B v) := by
  obtain ⟨C, rfl⟩ := projection_surjective v
  simp only [sphereAction_projection, mul_assoc]

@[simp] theorem sphereAction_inv_cancel (A : SpTwo) (v : BaseSphere) :
    sphereAction A (sphereAction A⁻¹ v) = v := by
  rw [← sphereAction_mul, mul_inv_cancel, sphereAction_one]

@[simp] theorem sphereAction_inv_projection (A : SpTwo) :
    sphereAction A⁻¹ (projection A) = north := by
  rw [sphereAction_projection, inv_mul_cancel, projection_one]

theorem continuous_planeAction :
    Continuous (fun z : SpTwo × QuaternionPlane => planeAction z.1 z.2) := by
  unfold planeAction
  apply (WithLp.prod_continuous_toLp 2 ℍ ℍ).comp
  apply Continuous.prodMk
  · exact (((continuous_subtype_val.comp continuous_fst).matrix_elem 0 0).mul
        ((WithLp.continuous_fst 2 ℍ ℍ).comp continuous_snd)).add
      (((continuous_subtype_val.comp continuous_fst).matrix_elem 0 1).mul
        ((WithLp.continuous_snd 2 ℍ ℍ).comp continuous_snd))
  · exact (((continuous_subtype_val.comp continuous_fst).matrix_elem 1 0).mul
        ((WithLp.continuous_fst 2 ℍ ℍ).comp continuous_snd)).add
      (((continuous_subtype_val.comp continuous_fst).matrix_elem 1 1).mul
        ((WithLp.continuous_snd 2 ℍ ℍ).comp continuous_snd))

theorem continuous_sphereAction : Continuous (fun z : SpTwo × BaseSphere =>
    sphereAction z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_planeAction.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- The quaternionic Hermitian pairing of two sphere vectors. -/
def hermitianPairing (u v : BaseSphere) : ℍ :=
  star u.val.fst * v.val.fst + star u.val.snd * v.val.snd

@[simp] theorem hermitianPairing_self (v : BaseSphere) : hermitianPairing v v = 1 := by
  have h := (mem_baseSphere_iff v.val).mp v.property
  simp only [hermitianPairing, Quaternion.star_mul_self, ← Quaternion.coe_add, h,
    Quaternion.coe_one]

theorem continuous_hermitianPairing :
    Continuous (fun z : BaseSphere × BaseSphere => hermitianPairing z.1 z.2) := by
  have h₁ : Continuous (fun z : BaseSphere × BaseSphere => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : BaseSphere × BaseSphere => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact (((WithLp.continuous_fst 2 ℍ ℍ).comp h₁).star.mul
      ((WithLp.continuous_fst 2 ℍ ℍ).comp h₂)).add
    (((WithLp.continuous_snd 2 ℍ ℍ).comp h₁).star.mul
      ((WithLp.continuous_snd 2 ℍ ℍ).comp h₂))

theorem sphereAction_inv_fst (A : SpTwo) (v : BaseSphere) :
    (sphereAction A⁻¹ v).val.fst = hermitianPairing (projection A) v := rfl

theorem projection_inv_mul_eq_north_iff (A B : SpTwo) :
    projection (A⁻¹ * B) = north ↔ projection A = projection B := by
  rw [← sphereAction_projection]
  constructor
  · intro h
    have hh := congrArg (sphereAction A) h
    simpa only [sphereAction_inv_cancel, sphereAction_north] using hh.symm
  · intro h
    rw [← h, sphereAction_inv_projection]

/-- The stabilizer of the first basis vector is an actual closed subgroup. -/
def northSubgroup : Subgroup SpTwo where
  carrier := {A | projection A = north}
  one_mem' := projection_one
  mul_mem' {A B} hA hB := by
    rw [Set.mem_ofPred_eq, ← sphereAction_projection, hB, sphereAction_north, hA]
  inv_mem' {A} hA := by
    have h := sphereAction_inv_projection A
    rw [hA, sphereAction_north] at h
    exact h

theorem isClosed_northSubgroup : IsClosed (northSubgroup : Set SpTwo) :=
  isClosed_singleton.preimage projection.continuous

open HopfProblem.UnitQuaternionSphere in
/-- The fiber identification also respects its native subgroup multiplication. -/
def northFiberMulEquiv : UnitQuaternions ≃* northSubgroup where
  toEquiv := northFiberHomeomorph.toEquiv
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul fiberInclusion q r

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
