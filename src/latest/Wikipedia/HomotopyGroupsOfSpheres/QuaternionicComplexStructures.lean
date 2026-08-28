import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalars
import Wikipedia.NoExoticSixSphere.OrthogonalComplexStructures

/-!
# Quaternionic-linear orthogonal complex structures

The minimum-path parameter space is the actual locus `J² = -1` in the
quaternionic skew-adjoint operators. Its topology is the subspace topology.
The sine-cosine exponential formula and compactness are inherited from
the corresponding proved statements about real orthogonal operators.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization

local notation "ℍ" => Quaternion ℝ

def locus (n : ℕ) : Set (SkewSpace n) :=
  {J | J.val.comp J.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))}

abbrev Space (n : ℕ) := locus n

variable {n : ℕ}

def toOrthogonal (J : Space n) :
    NoExoticSixSphere.OrthogonalComplexStructures.Space (4 * n + 4) :=
  ⟨toOrthogonalSkew n J.val, J.property⟩

theorem continuous_toOrthogonal : Continuous (toOrthogonal (n := n)) :=
  ((continuous_toOrthogonalSkew n).comp continuous_subtype_val).subtype_mk _

def toSymplectic (J : Space n) : symplecticSubgroup n :=
  ⟨NoExoticSixSphere.OrthogonalComplexStructures.toOrthogonal (toOrthogonal J),
    (mem_symplecticSubgroup_iff n _).mpr J.val.property.2⟩

theorem toSymplectic_operator (J : Space n) : (toSymplectic J).val.val.val = J.val.val := rfl

theorem continuous_toSymplectic : Continuous (toSymplectic (n := n)) :=
  (NoExoticSixSphere.OrthogonalComplexStructures.continuous_toOrthogonal.comp
    continuous_toOrthogonal).subtype_mk _

theorem square_apply (J : Space n) (v : Vector (4 * n + 4)) :
    J.val.val (J.val.val v) = -v := DFunLike.congr_fun J.property v

theorem norm_apply (J : Space n) (v : Vector (4 * n + 4)) : ‖J.val.val v‖ = ‖v‖ :=
  NoExoticSixSphere.OrthogonalComplexStructures.norm_apply (toOrthogonal J) v

theorem exp_smul (J : Space n) (t : ℝ) :
    (Exponential.exp (t • J.val)).val.val.val =
      Real.cos t • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) +
        Real.sin t • J.val.val := by
  change (NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (t • J.val))).val.val = _
  rw [map_smul]
  exact NoExoticSixSphere.OrthogonalComplexStructures.exp_smul (toOrthogonal J) t

def antipode (n : ℕ) : symplecticSubgroup n :=
  symplecticHomeomorph n (-1 : SpGroup (Fin (n + 1)))

theorem antipode_operator (n : ℕ) :
    (antipode n).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  change realRepresentation n (-1) = -1
  rw [map_neg, map_one]

theorem exp_pi (J : Space n) : Exponential.exp (Real.pi • J.val) = antipode n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [exp_smul, antipode_operator, Real.cos_pi, Real.sin_pi,
    zero_smul ℝ J.val.val, add_zero]
  exact neg_one_smul ℝ _

theorem exp_half_pi (J : Space n) :
    Exponential.exp ((Real.pi / 2) • J.val) = toSymplectic J := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [exp_smul, toSymplectic_operator, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_smul ℝ (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)), zero_add]
  exact one_smul ℝ _

theorem isClosed_locus (n : ℕ) : IsClosed (locus n) :=
  isClosed_eq (continuous_subtype_val.clm_comp continuous_subtype_val) continuous_const

theorem norm_le_one (J : Space n) : ‖J.val‖ ≤ 1 :=
  NoExoticSixSphere.OrthogonalComplexStructures.norm_le_one (toOrthogonal J)

theorem isCompact_locus (n : ℕ) : IsCompact (locus n) := by
  apply (isCompact_closedBall (0 : SkewSpace n) 1).of_isClosed_subset (isClosed_locus n)
  intro J hJ
  change dist J (0 : SkewSpace n) ≤ 1
  have hd : dist J (0 : SkewSpace n) = ‖J‖ := dist_zero_right J
  rw [hd]
  exact norm_le_one ⟨J, hJ⟩

instance compactSpace (n : ℕ) : CompactSpace (Space n) :=
  isCompact_iff_compactSpace.mp (isCompact_locus n)

/-- The diagonal quaternion `i`, acting by left multiplication in every coordinate. -/
def standardMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  Matrix.diagonal (fun _ => QuaternionicScalars.i)

theorem standardMatrix_star (n : ℕ) : star (standardMatrix n) = -(standardMatrix n) := by
  apply Matrix.ext
  intro a b
  change star (Matrix.diagonal (fun _ : Fin (n + 1) => QuaternionicScalars.i) b a) =
    -(Matrix.diagonal (fun _ : Fin (n + 1) => QuaternionicScalars.i) a b)
  by_cases h : a = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq] using QuaternionicScalars.star_i
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h),
      star_zero, neg_zero]

theorem standardMatrix_square (n : ℕ) : standardMatrix n * standardMatrix n = -1 := by
  simp only [standardMatrix, Matrix.diagonal_mul_diagonal, QuaternionicScalars.i_mul_i]
  rw [← Matrix.diagonal_neg, Matrix.diagonal_one]

def standardSkew (n : ℕ) : SkewSpace n :=
  ⟨realAction n (standardMatrix n), ⟨by
    change (realAction n (standardMatrix n)).adjoint = -(realAction n (standardMatrix n))
    rw [← realAction_star, standardMatrix_star]
    exact (realRepresentation n).map_neg _, realAction_mem_commutant n _⟩⟩

def standard (n : ℕ) : Space n :=
  ⟨standardSkew n, by
    change realRepresentation n (standardMatrix n) * realRepresentation n (standardMatrix n) = -1
    rw [← map_mul, standardMatrix_square, map_neg, map_one]⟩

instance nonempty (n : ℕ) : Nonempty (Space n) := ⟨standard n⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
