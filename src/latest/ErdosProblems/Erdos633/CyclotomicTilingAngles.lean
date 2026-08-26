import ErdosProblems.Erdos633.CyclotomicTrigonometry
import ErdosProblems.Erdos633.ConjugateAngleFormula

/-!
# Cyclotomic embeddings in the actual tiling angle equations

The embeddings are constructed, not assumed: their action on cosine squares
comes from the explicit root-power formula. The remaining normalization task
is to put an arbitrary rational-angle tiling into the stated coefficient field.
-/

namespace Erdos633

theorem exp_int_mul_mem_realRootCoordinates (θ : ℝ) (q m : ℤ)
    (hq : (q : ℝ) * θ = Real.pi / 2) :
    Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) ∈
      complexCoordinateSubfield (realRootField (Complex.exp ((θ : ℂ) * Complex.I))) := by
  apply (exp_angle_mem_complexCoordinateSubfield_iff _ _).mpr
  exact ⟨cos_int_mul_mem_realRootField θ m, sin_int_mul_mem_realRootField θ q m hq⟩

theorem Triangle.exists_cosineSquare_rotation_embedding (R : Triangle)
    (θ : ℝ) (n k : ℕ) (m : Fin 3 → ℤ) (hn : 0 < n)
    (hθ : θ = 2 * Real.pi / n) (hk : k.Coprime n)
    (hR : R.CoordinatesIn (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hangle : ∀ j, R.cornerAngle j = (m j : ℝ) * θ) :
    ∃ σ : realRootField (Complex.exp ((θ : ℂ) * Complex.I)) →+* ℝ,
      ∀ j : Fin 3,
        σ ((R.toFieldTriangle
          (realRootField (Complex.exp ((θ : ℂ) * Complex.I))) hR).cosineSquare j) =
          Real.cos ((k : ℝ) * R.cornerAngle j) ^ 2 := by
  let F := realRootField (Complex.exp ((θ : ℂ) * Complex.I))
  let RF := R.toFieldTriangle F hR
  obtain ⟨σ, hσ⟩ := exists_real_rotation_embedding θ n k hn hθ hk
  refine ⟨σ, fun j => ?_⟩
  let c : F := ⟨Real.cos ((m j : ℝ) * θ), cos_int_mul_mem_realRootField θ (m j)⟩
  have hc : (algebraMap F ℝ) (c ^ 2) =
      Real.cos ((RF.realize (algebraMap F ℝ)).cornerAngle j) ^ 2 := by
    rw [R.toFieldTriangle_realize F hR, hangle j]
    rfl
  have heq : RF.cosineSquare j = c ^ 2 :=
    RF.cosineSquare_eq_of_realize (algebraMap F ℝ) j (c ^ 2) hc
  change σ (RF.cosineSquare j) = _
  rw [heq, map_pow, hσ (m j), hangle j]

theorem CongruentTiling.rational_conjugation_identity_of_cyclotomic_coordinates
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (α β γ : ℚ) (θ : ℝ) (m : Fin 3 → ℤ)
    (hθ : θ = 2 * Real.pi / (4 * α.den * β.den * γ.den))
    (hP : P.CoordinatesIn (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hR : R.CoordinatesIn (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hQ : ∀ i : Fin N, (T.labelledTile i).CoordinatesIn
      (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ))
    (hm : ∀ j, R.cornerAngle j = (m j : ℝ) * θ)
    (hg : T.outerCornerCount 2 = 0) :
    RationalCornerConjugationIdentity α β γ (T.outerCornerCount 0) (T.outerCornerCount 1) := by
  apply T.rational_corner_conjugation_identity
    (realRootField (Complex.exp ((θ : ℂ) * Complex.I))) hP hR hQ α β γ hangle hg
  intro k hk
  have hn : 0 < 4 * α.den * β.den * γ.den := by
    have ha := α.den_pos
    have hb := β.den_pos
    have hc := γ.den_pos
    positivity
  have hθ' : θ = 2 * Real.pi / ((4 * α.den * β.den * γ.den : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ
  obtain ⟨σ, hσ⟩ := R.exists_cosineSquare_rotation_embedding θ
    (4 * α.den * β.den * γ.den) k m hn hθ' hk hR hm
  refine ⟨σ, fun j => ?_⟩
  rw [hσ j, hangle j]
  congr 2
  ring

theorem CongruentTiling.rational_conjugation_identity_of_cyclotomic_rotations
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (α β γ : ℚ) (θ : ℝ) (q : ℤ) (m : Fin 3 → ℤ)
    (hθ : θ = 2 * Real.pi / (4 * α.den * β.den * γ.den))
    (hq : (q : ℝ) * θ = Real.pi / 2)
    (hR : R.CoordinatesIn (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (ha : P.a ∈ complexCoordinateSubfield
      (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hbase : P.unitEdgeVector 2 ∈ complexCoordinateSubfield
      (realRootField (Complex.exp ((θ : ℂ) * Complex.I))))
    (hc : R.sideLength 2 ∈ realRootField (Complex.exp ((θ : ℂ) * Complex.I)))
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ))
    (hm : ∀ j, R.cornerAngle j = (m j : ℝ) * θ)
    (hg : T.outerCornerCount 2 = 0) :
    RationalCornerConjugationIdentity α β γ (T.outerCornerCount 0) (T.outerCornerCount 1) := by
  let F := realRootField (Complex.exp ((θ : ℂ) * Complex.I))
  have hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    have h := exp_int_mul_mem_realRootCoordinates θ q (m 0) hq
    have h0 : R.angleA = (m 0 : ℝ) * θ := hm 0
    rwa [← h0] at h
  have hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    have h := exp_int_mul_mem_realRootCoordinates θ q (m 1) hq
    have h1 : R.angleB = (m 1 : ℝ) * θ := hm 1
    rwa [← h1] at h
  obtain ⟨hP, hQ⟩ := T.coefficient_field_vertices F ha hbase hA hB hc
  exact T.rational_conjugation_identity_of_cyclotomic_coordinates
    α β γ θ m hθ hP hR hQ hangle hm hg

noncomputable def rationalAngleRootStep (α β γ : ℚ) : ℝ :=
  2 * Real.pi / (4 * α.den * β.den * γ.den)

def rationalAngleNumerators (α β γ : ℚ) : Fin 3 → ℤ :=
  ![2 * α.num * β.den * γ.den, 2 * β.num * α.den * γ.den,
    2 * γ.num * α.den * β.den]

theorem rationalAngleRootStep_quarter (α β γ : ℚ) :
    (((α.den * β.den * γ.den : ℕ) : ℤ) : ℝ) * rationalAngleRootStep α β γ =
      Real.pi / 2 := by
  have ha : (α.den : ℝ) ≠ 0 := by exact_mod_cast α.den_nz
  have hb : (β.den : ℝ) ≠ 0 := by exact_mod_cast β.den_nz
  have hc : (γ.den : ℝ) ≠ 0 := by exact_mod_cast γ.den_nz
  unfold rationalAngleRootStep
  push_cast
  field_simp
  ring

theorem rationalAngleNumerators_mul_step (α β γ : ℚ) (j : Fin 3) :
    (rationalAngleNumerators α β γ j : ℝ) * rationalAngleRootStep α β γ =
      Real.pi * (![α, β, γ] j : ℝ) := by
  have ha : (α.den : ℝ) ≠ 0 := by exact_mod_cast α.den_nz
  have hb : (β.den : ℝ) ≠ 0 := by exact_mod_cast β.den_nz
  have hc : (γ.den : ℝ) ≠ 0 := by exact_mod_cast γ.den_nz
  fin_cases j <;> dsimp [rationalAngleNumerators, rationalAngleRootStep] <;>
    rw [Rat.cast_def] <;> push_cast <;> field_simp <;> ring

/-- All residue and embedding data are now derived from rational angles.
Only geometric normalization into the coefficient field remains an input. -/
theorem CongruentTiling.rational_conjugation_identity_normalized
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (α β γ : ℚ)
    (hR : R.CoordinatesIn
      (realRootField (Complex.exp ((rationalAngleRootStep α β γ : ℂ) * Complex.I))))
    (ha : P.a ∈ complexCoordinateSubfield
      (realRootField (Complex.exp ((rationalAngleRootStep α β γ : ℂ) * Complex.I))))
    (hbase : P.unitEdgeVector 2 ∈ complexCoordinateSubfield
      (realRootField (Complex.exp ((rationalAngleRootStep α β γ : ℂ) * Complex.I))))
    (hc : R.sideLength 2 ∈
      realRootField (Complex.exp ((rationalAngleRootStep α β γ : ℂ) * Complex.I)))
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ))
    (hg : T.outerCornerCount 2 = 0) :
    RationalCornerConjugationIdentity α β γ (T.outerCornerCount 0) (T.outerCornerCount 1) := by
  apply T.rational_conjugation_identity_of_cyclotomic_rotations α β γ
    (rationalAngleRootStep α β γ) ((α.den * β.den * γ.den : ℕ) : ℤ)
    (rationalAngleNumerators α β γ) rfl (rationalAngleRootStep_quarter α β γ)
    hR ha hbase hc hangle _ hg
  intro j
  exact (hangle j).trans (rationalAngleNumerators_mul_step α β γ j).symm

end Erdos633
