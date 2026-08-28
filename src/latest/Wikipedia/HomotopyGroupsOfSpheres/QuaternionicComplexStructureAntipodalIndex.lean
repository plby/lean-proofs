import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointAntipodalDiagonalization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexMixingMatrices

/-!
# Independent negative directions in the anticommuting quaternionic model

The simultaneous eigenframe transports `k`-mixing matrices into the actual
anticommuting skew space at the base complex structure. The strict
commutator estimate holds on every nonzero parameter direction.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator NoExoticSixSphere.SkewSpectralPlane
open ComplexStructures

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

def transportedComplexMixingLinear (U : SpGroup (Fin (n + 1))) :
    (Fin n → ℝ) →ₗ[ℝ] SkewSpace n where
  toFun c := skewOfMatrix n (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.k c))
    (conjugateMatrix_skew U⁻¹ _ (mixingMatrix_skew _ QuaternionicScalars.star_k c))
  map_add' c d := by
    apply Subtype.ext
    change realAction n (conjugateMatrix U⁻¹ (mixingMatrix _ (c + d))) = _
    rw [mixingMatrix_add, conjugateMatrix_add, realAction_add]
    rfl
  map_smul' r c := by
    apply Subtype.ext
    change realAction n (conjugateMatrix U⁻¹ (mixingMatrix _ (r • c))) = _
    rw [mixingMatrix_smul, conjugateMatrix_smul, realAction_smul]
    rfl

theorem transportedComplexMixingLinear_injective (U : SpGroup (Fin (n + 1))) :
    Function.Injective (transportedComplexMixingLinear U) := by
  intro c d h
  apply mixingMatrix_injective QuaternionicScalars.k QuaternionicScalars.k_ne_zero
  apply conjugateMatrix_injective U⁻¹
  exact realAction_injective n (congrArg Subtype.val h)

theorem squareNorm_transportedComplexMixing (U : SpGroup (Fin (n + 1))) (c : Fin n → ℝ) :
    squareNorm (transportedComplexMixingLinear U c).val =
      squareNorm (complexMixingLinear n c).val := squareNorm_realAction_conjugateMatrix U⁻¹ _

theorem transportedComplexMixing_commutator_norm (K : SkewSpace n)
    (U : SpGroup (Fin (n + 1))) (α : Fin (n + 1) → ℝ)
    (hd : conjugateMatrix U (coefficients n K.val) =
      Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i)) (c : Fin n → ℝ) :
    squareNorm (commutator K.val (transportedComplexMixingLinear U c).val) =
      squareNorm (commutator (realAction n (Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i)))
        (complexMixingLinear n c).val) := by
  have hcancel : conjugateMatrix U
      (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.k c)) =
        mixingMatrix QuaternionicScalars.k c := by
    simpa only [inv_inv] using
      conjugateMatrix_inv_cancel U⁻¹ (mixingMatrix QuaternionicScalars.k c)
  have h := squareNorm_commutator_conjugateMatrix U (coefficients n K.val)
    (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.k c))
  rw [hd, hcancel, realAction_coefficients n K.val K.property.2] at h
  exact h.symm

theorem transportedComplexMixing_anticommute (J : Space n) (U : SpGroup (Fin (n + 1)))
    (hJ : conjugateMatrix U (coefficients n J.val.val) =
      Matrix.diagonal (fun _ ↦ QuaternionicScalars.j)) (c : Fin n → ℝ) :
    J.val.val * (transportedComplexMixingLinear U c).val =
      -((transportedComplexMixingLinear U c).val * J.val.val) := by
  let A := conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.k c)
  have hcancel : conjugateMatrix U A = mixingMatrix QuaternionicScalars.k c := by
    simpa only [A, inv_inv] using
      conjugateMatrix_inv_cancel U⁻¹ (mixingMatrix QuaternionicScalars.k c)
  have hm : coefficients n J.val.val * A = -(A * coefficients n J.val.val) := by
    apply conjugateMatrix_injective U
    rw [conjugateMatrix_product, conjugateMatrix_neg, conjugateMatrix_product, hJ, hcancel]
    exact j_complexMixing_anticommute c
  have he := congrArg (realRepresentation n) hm
  have hcoeff : realRepresentation n (coefficients n J.val.val) = J.val.val :=
    realAction_coefficients n J.val.val J.val.property.2
  rw [map_mul, map_neg, map_mul, hcoeff] at he
  exact he

def restrictedMixingLinear (J : Space n) (U : SpGroup (Fin (n + 1)))
    (hJ : conjugateMatrix U (coefficients n J.val.val) =
      Matrix.diagonal (fun _ ↦ QuaternionicScalars.j)) : (Fin n → ℝ) →ₗ[ℝ] AntiSkewSpace J where
  toFun c := ⟨(transportedComplexMixingLinear U c).val,
    ⟨(transportedComplexMixingLinear U c).property, transportedComplexMixing_anticommute J U hJ c⟩⟩
  map_add' c d := Subtype.ext
    (congrArg (fun A : SkewSpace n ↦ A.val) ((transportedComplexMixingLinear U).map_add c d))
  map_smul' r c := Subtype.ext
    (congrArg (fun A : SkewSpace n ↦ A.val) ((transportedComplexMixingLinear U).map_smul r c))

theorem restrictedMixingLinear_toSkew (J : Space n) (U : SpGroup (Fin (n + 1)))
    (hJ : conjugateMatrix U (coefficients n J.val.val) =
      Matrix.diagonal (fun _ ↦ QuaternionicScalars.j)) (c : Fin n → ℝ) :
    antiSkewToSkew J (restrictedMixingLinear J U hJ c) = transportedComplexMixingLinear U c := rfl

theorem restrictedMixingLinear_injective (J : Space n) (U : SpGroup (Fin (n + 1)))
    (hJ : conjugateMatrix U (coefficients n J.val.val) =
      Matrix.diagonal (fun _ ↦ QuaternionicScalars.j)) :
    Function.Injective (restrictedMixingLinear J U hJ) := by
  intro c d h
  apply transportedComplexMixingLinear_injective U
  exact congrArg (antiSkewToSkew J) h

theorem exists_anticommuting_negativeFamily (J : Space n) (K : SkewSpace n)
    (hJK : J.val.val * K.val = -(K.val * J.val.val))
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ T : (Fin n → ℝ) →ₗ[ℝ] AntiSkewSpace J, Function.Injective T ∧
      ∀ c, c ≠ 0 → 4 * Real.pi ^ 2 * squareNorm (T c).val <
        squareNorm (commutator K.val (T c).val) := by
  obtain ⟨U, m, hm, hdK, hdJ⟩ := exists_fast_joint_antipodal_diagonalization J K hJK hexp hnot
  let α : Fin (n + 1) → ℝ := fun a ↦ (2 * (m a : ℝ) + 1) * Real.pi
  have hfast : 3 * Real.pi ≤ α 0 := by
    have hm' : (1 : ℝ) ≤ m 0 := by exact_mod_cast hm
    dsimp [α]
    nlinarith [Real.pi_pos]
  have hslow (a : Fin n) : Real.pi ≤ α a.succ := by
    dsimp [α]
    nlinarith [Real.pi_pos, Nat.cast_nonneg' (α := ℝ) (m a.succ)]
  refine ⟨restrictedMixingLinear J U hdJ, restrictedMixingLinear_injective J U hdJ, ?_⟩
  intro c hc
  change 4 * Real.pi ^ 2 * squareNorm (transportedComplexMixingLinear U c).val <
    squareNorm (commutator K.val (transportedComplexMixingLinear U c).val)
  rw [squareNorm_transportedComplexMixing, transportedComplexMixing_commutator_norm K U α hdK]
  exact diagonal_complexMixing_commutator_strict α hfast hslow c hc

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
