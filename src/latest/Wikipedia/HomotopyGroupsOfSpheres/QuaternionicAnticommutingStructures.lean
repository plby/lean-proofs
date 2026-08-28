import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures

/-!
# Anticommuting quaternionic complex structures

For a fixed quaternionic complex structure `J₀`, the second parameter space is
the actual closed locus of complex structures anticommuting with `J₀`.
The rotation `cos θ J₀ + sin θ J` stays in the original complex-structure
space. These are geometric maps, with no homotopy comparison asserted here.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

namespace ComplexStructures

def negative {n : ℕ} (J : Space n) : Space n :=
  ⟨-J.val, by
    apply ContinuousLinearMap.ext
    intro x
    change -J.val.val (-J.val.val x) = -x
    rw [map_neg, neg_neg]
    exact square_apply J x⟩

theorem negative_negative {n : ℕ} (J : Space n) : negative (negative J) = J := by
  apply Subtype.ext
  exact neg_neg J.val

end ComplexStructures

namespace AnticommutingStructures

variable {n : ℕ}

def locus (J₀ : ComplexStructures.Space n) : Set (ComplexStructures.Space n) :=
  {J | J₀.val.val * J.val.val = -(J.val.val * J₀.val.val)}

abbrev Space (J₀ : ComplexStructures.Space n) := locus J₀

theorem isClosed_locus (J₀ : ComplexStructures.Space n) : IsClosed (locus J₀) := by
  have hJ : Continuous (fun J : ComplexStructures.Space n ↦ J.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact isClosed_eq (continuous_const.clm_comp hJ) ((hJ.clm_comp continuous_const).neg)

instance compactSpace (J₀ : ComplexStructures.Space n) : CompactSpace (Space J₀) :=
  isCompact_iff_compactSpace.mp (isClosed_locus J₀).isCompact

private theorem linearCombination_square {A : Type*} [Ring A] [Algebra ℝ A]
    (J K : A) (hJ : J * J = -1) (hK : K * K = -1) (hJK : J * K = -(K * J))
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (c • J + s • K) * (c • J + s • K) = -1 := by
  have hcross : (c * s) • (J * K) + (s * c) • (K * J) = 0 := by
    rw [hJK, smul_neg, mul_comm s c, neg_add_cancel]
  calc
    (c • J + s • K) * (c • J + s • K) =
        ((c * c) • (J * J) + (s * s) • (K * K)) +
          ((c * s) • (J * K) + (s * c) • (K * J)) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
      rw [mul_comm s c]
      abel
    _ = (c * c + s * s) • (-1 : A) := by rw [hcross, add_zero, hJ, hK, add_smul]
    _ = -1 := by rw [← pow_two c, ← pow_two s, hcs, one_smul]

def rotation {J₀ : ComplexStructures.Space n} (J : Space J₀) (θ : ℝ) :
    ComplexStructures.Space n :=
  ⟨Real.cos θ • J₀.val + Real.sin θ • J.val.val, by
    change (Real.cos θ • J₀.val.val + Real.sin θ • J.val.val.val) *
      (Real.cos θ • J₀.val.val + Real.sin θ • J.val.val.val) = -1
    exact linearCombination_square J₀.val.val J.val.val.val J₀.property J.val.property
      J.property _ _ (by nlinarith only [Real.sin_sq_add_cos_sq θ])⟩

theorem rotation_zero {J₀ : ComplexStructures.Space n} (J : Space J₀) :
    rotation J 0 = J₀ := by
  apply Subtype.ext
  change Real.cos 0 • J₀.val + Real.sin 0 • J.val.val = J₀.val
  rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]

theorem rotation_pi {J₀ : ComplexStructures.Space n} (J : Space J₀) :
    rotation J Real.pi = ComplexStructures.negative J₀ := by
  apply Subtype.ext
  change Real.cos Real.pi • J₀.val + Real.sin Real.pi • J.val.val = -J₀.val
  rw [Real.cos_pi, Real.sin_pi, zero_smul, add_zero]
  exact neg_one_smul ℝ J₀.val

theorem rotation_half_pi {J₀ : ComplexStructures.Space n} (J : Space J₀) :
    rotation J (Real.pi / 2) = J.val := by
  apply Subtype.ext
  change Real.cos (Real.pi / 2) • J₀.val + Real.sin (Real.pi / 2) • J.val.val = J.val.val
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]

private theorem continuous_add_maps {Y V : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup V] {f g : Y → V} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun y ↦ f y + g y) := hf.add hg

theorem continuous_rotation (J₀ : ComplexStructures.Space n) :
    Continuous (fun z : ℝ × Space J₀ ↦ rotation z.2 z.1) := by
  have hJ : Continuous (fun z : ℝ × Space J₀ ↦ z.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hc := (Real.continuous_cos.comp continuous_fst).smul
    (continuous_const : Continuous (fun _ : ℝ × Space J₀ ↦ J₀.val))
  have hs := (Real.continuous_sin.comp continuous_fst).smul hJ
  exact (continuous_add_maps (V := SkewSpace n) hc hs).subtype_mk _

/-- Diagonal left multiplication by the quaternion `j`. -/
def jMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ) :=
  Matrix.diagonal (fun _ ↦ QuaternionicScalars.j)

theorem jMatrix_star (n : ℕ) : star (jMatrix n) = -(jMatrix n) := by
  apply Matrix.ext
  intro a b
  change star (Matrix.diagonal (fun _ : Fin (n + 1) ↦ QuaternionicScalars.j) b a) =
    -(Matrix.diagonal (fun _ : Fin (n + 1) ↦ QuaternionicScalars.j) a b)
  by_cases h : a = b
  · subst b
    simpa only [Matrix.diagonal_apply_eq] using QuaternionicScalars.star_j
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h),
      star_zero, neg_zero]

theorem jMatrix_square (n : ℕ) : jMatrix n * jMatrix n = -1 := by
  simp only [jMatrix, Matrix.diagonal_mul_diagonal, QuaternionicScalars.j_mul_j]
  rw [← Matrix.diagonal_neg, Matrix.diagonal_one]

def jSkew (n : ℕ) : SkewSpace n :=
  ⟨realAction n (jMatrix n), ⟨by
    change (realAction n (jMatrix n)).adjoint = -(realAction n (jMatrix n))
    rw [← realAction_star, jMatrix_star]
    exact (realRepresentation n).map_neg _, realAction_mem_commutant n _⟩⟩

def jStructure (n : ℕ) : ComplexStructures.Space n :=
  ⟨jSkew n, by
    change realRepresentation n (jMatrix n) * realRepresentation n (jMatrix n) = -1
    rw [← map_mul, jMatrix_square, map_neg, map_one]⟩

def standard (n : ℕ) : Space (ComplexStructures.standard n) :=
  ⟨jStructure n, by
    change realRepresentation n (ComplexStructures.standardMatrix n) *
      realRepresentation n (jMatrix n) =
        -(realRepresentation n (jMatrix n) *
          realRepresentation n (ComplexStructures.standardMatrix n))
    rw [← map_mul, ← map_mul, ← map_neg]
    apply congrArg (realRepresentation n)
    simp only [ComplexStructures.standardMatrix, jMatrix, Matrix.diagonal_mul_diagonal]
    rw [Matrix.diagonal_neg]
    apply congrArg Matrix.diagonal
    exact funext (fun _ ↦ QuaternionicScalars.i_mul_j_eq_neg_j_mul_i)⟩

instance nonempty_standard (n : ℕ) : Nonempty (Space (ComplexStructures.standard n)) :=
  ⟨standard n⟩

end AnticommutingStructures

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
