import ErdosProblems.Erdos633.ConjugateCornerAngles

/-!
# Squared angle cosines under real field embeddings

The square of an angle cosine is a rational expression in the three squared
side lengths. This expression transports through every real field embedding
without making an unjustified sign choice for a conjugated side length.
-/

namespace Erdos633

open scoped EuclideanGeometry

theorem cosine_sq_eq_normSq_expression (p q r : ℂ) (hpq : p ≠ q) (hpr : p ≠ r) :
    Real.cos (∠ q p r) ^ 2 =
      (Complex.normSq (q - p) + Complex.normSq (r - p) - Complex.normSq (r - q)) ^ 2 /
        (4 * Complex.normSq (q - p) * Complex.normSq (r - p)) := by
  simp only [normSq_sub_eq_dist_sq]
  have hcos : dist q r ^ 2 = dist p q ^ 2 + dist p r ^ 2 -
      2 * dist p q * dist p r * Real.cos (∠ q p r) := by
    simpa only [← pow_two, dist_comm q p, dist_comm r p] using
      EuclideanGeometry.law_cos q p r
  have hnum : dist p q ^ 2 + dist p r ^ 2 - dist q r ^ 2 =
      2 * dist p q * dist p r * Real.cos (∠ q p r) := by linarith
  rw [hnum]
  field_simp [ne_of_gt (dist_pos.mpr hpq), ne_of_gt (dist_pos.mpr hpr)]
  ring

def fieldCosineSquare {F : Type*} [Field F] (p q r : F × F) : F :=
  (fieldSquaredDistance p q + fieldSquaredDistance p r - fieldSquaredDistance q r) ^ 2 /
    (4 * fieldSquaredDistance p q * fieldSquaredDistance p r)

theorem map_fieldCosineSquare {F : Type*} [Field F] (σ : F →+* ℝ)
    (p q r : F × F) (hpq : fieldPoint σ p ≠ fieldPoint σ q)
    (hpr : fieldPoint σ p ≠ fieldPoint σ r) :
    σ (fieldCosineSquare p q r) =
      Real.cos (∠ (fieldPoint σ q) (fieldPoint σ p) (fieldPoint σ r)) ^ 2 := by
  simpa only [fieldCosineSquare, map_div₀, map_pow, map_sub, map_add, map_mul,
    map_ofNat, ← normSq_fieldPoint_sub] using
    (cosine_sq_eq_normSq_expression (fieldPoint σ p) (fieldPoint σ q)
      (fieldPoint σ r) hpq hpr).symm

def FieldTriangle.cosineSquare {F : Type*} [Field F] (P : FieldTriangle F)
    (k : Fin 3) : F :=
  ![fieldCosineSquare P.a P.b P.c, fieldCosineSquare P.b P.a P.c,
    fieldCosineSquare P.c P.a P.b] k

theorem FieldTriangle.map_cosineSquare {F : Type*} [Field F]
    (P : FieldTriangle F) (σ : F →+* ℝ) (k : Fin 3) :
    σ (P.cosineSquare k) = Real.cos ((P.realize σ).cornerAngle k) ^ 2 := by
  fin_cases k
  · exact map_fieldCosineSquare σ P.a P.b P.c
      (P.realize σ).a_ne_b (P.realize σ).swapBC.a_ne_b
  · exact map_fieldCosineSquare σ P.b P.a P.c
      (P.realize σ).a_ne_b.symm (P.realize σ).rotate.a_ne_b
  · exact map_fieldCosineSquare σ P.c P.a P.b
      (P.realize σ).swapBC.a_ne_b.symm (P.realize σ).rotate.a_ne_b.symm

theorem FieldTriangle.cosineSquare_eq_of_realize {F : Type*} [Field F]
    (P : FieldTriangle F) (τ : F →+* ℝ) (k : Fin 3) (x : F)
    (hx : τ x = Real.cos ((P.realize τ).cornerAngle k) ^ 2) :
    P.cosineSquare k = x := by
  apply τ.injective
  exact (P.map_cosineSquare τ k).trans hx.symm

theorem FieldTriangle.cosine_sq_transfer {F : Type*} [Field F]
    (P : FieldTriangle F) (τ σ : F →+* ℝ) (k : Fin 3) (x : F)
    (hx : τ x = Real.cos ((P.realize τ).cornerAngle k) ^ 2) :
    Real.cos ((P.realize σ).cornerAngle k) ^ 2 = σ x := by
  rw [← P.map_cosineSquare σ k, P.cosineSquare_eq_of_realize τ k x hx]

theorem angle_eq_or_supplement_of_cos_sq (x y : ℝ)
    (hx : x ∈ Set.Icc 0 Real.pi) (hy : y ∈ Set.Icc 0 Real.pi)
    (h : Real.cos x ^ 2 = Real.cos y ^ 2) : x = y ∨ x = Real.pi - y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact Or.inl (Real.injOn_cos hx hy h)
  · right
    apply Real.injOn_cos hx ⟨by linarith [hy.2], by linarith [hy.1]⟩
    simpa only [Real.cos_pi_sub] using h

theorem Triangle.cornerAngles_eq_of_cos_sq (P : Triangle) (θ : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < θ k) (hlt : ∀ k, θ k < Real.pi)
    (hsum : ∑ k : Fin 3, θ k = Real.pi)
    (hcos : ∀ k, Real.cos (P.cornerAngle k) ^ 2 = Real.cos (θ k) ^ 2) :
    P.cornerAngle = θ := by
  have hchoice (k : Fin 3) : P.cornerAngle k = θ k ∨
      P.cornerAngle k = Real.pi - θ k :=
    angle_eq_or_supplement_of_cos_sq _ _
      ⟨(P.cornerAngle_pos k).le, (P.cornerAngle_lt_pi k).le⟩
      ⟨(hpos k).le, (hlt k).le⟩ (hcos k)
  have hP := P.sum_cornerAngle
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum hP
  change θ 0 + (θ 1 + θ 2) = Real.pi at hsum
  change P.cornerAngle 0 + (P.cornerAngle 1 + P.cornerAngle 2) = Real.pi at hP
  have h₀ := hpos 0
  have h₁ := hpos 1
  have h₂ := hpos 2
  have hπ := Real.pi_pos
  rcases hchoice 0 with h0 | h0 <;>
    rcases hchoice 1 with h1 | h1 <;>
    rcases hchoice 2 with h2 | h2
  all_goals
    funext k
    fin_cases k <;> dsimp <;> linarith

end Erdos633
