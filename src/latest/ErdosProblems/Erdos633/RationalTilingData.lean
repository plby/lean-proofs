import ErdosProblems.Erdos633.TilingNormalization

/-!
# Rational corner data from arbitrary geometric tilings

Every rational-angle tiling is normalized geometrically. Its normalized
corner counts satisfy all cyclotomic conjugate equations while the original
outer and reference angles are retained. Thus the finite arithmetic data
below are extracted from a genuine tiling, not added as an assumption.
-/

namespace Erdos633

open scoped BigOperators

structure RationalCornerData (ω : Fin 3 → ℝ) (α β γ : ℚ) where
  counts : Fin 3 → Fin 3 → ℕ
  positive : 0 < α ∧ 0 < β ∧ 0 < γ
  angle_sum : α + β + γ = 1
  row_pos : ∀ i, ∃ j, 0 < counts i j
  angle_eq : ∀ i, (∑ j : Fin 3, (counts i j : ℝ) *
    (Real.pi * (![α, β, γ] j : ℝ))) = ω i
  conjugate_sum : ∀ k : ℕ, k.Coprime (4 * α.den * β.den * γ.den) →
    (∑ j : Fin 3, ((∑ i : Fin 3, counts i j : ℕ) : ℚ) *
      rationalConjugateAngle α β γ k (![α, β, γ] j)) = 1

theorem rational_angle_rotations_mem (R : Triangle) (α β γ : ℚ)
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ)) :
    ∀ j : Fin 3, Complex.exp ((R.cornerAngle j : ℂ) * Complex.I) ∈
      complexCoordinateSubfield
        (realRootField (Complex.exp ((rationalAngleRootStep α β γ : ℂ) * Complex.I))) := by
  intro j
  have h := exp_int_mul_mem_realRootCoordinates (rationalAngleRootStep α β γ)
    ((α.den * β.den * γ.den : ℕ) : ℤ) (rationalAngleNumerators α β γ j)
    (rationalAngleRootStep_quarter α β γ)
  rw [rationalAngleNumerators_mul_step, ← hangle j] at h
  exact h

theorem CongruentTiling.exists_rationalCornerData
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (α β γ : ℚ)
    (hangle : ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ)) :
    Nonempty (RationalCornerData P.cornerAngle α β γ) := by
  let θ := rationalAngleRootStep α β γ
  let F := realRootField (Complex.exp ((θ : ℂ) * Complex.I))
  have hrot := rational_angle_rotations_mem R α β γ hangle
  obtain ⟨P', R', U, hPangle, hRangle, hRcoords, hPa, hbase, hc⟩ :=
    T.exists_field_normalization F (hrot 0) (hrot 1)
  have hangle' (j : Fin 3) : R'.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ) :=
    (hRangle j).trans (hangle j)
  have hrot' := rational_angle_rotations_mem R' α β γ hangle'
  have hPaF : P'.a ∈ complexCoordinateSubfield F := by
    rw [hPa]
    exact (complexCoordinateSubfield F).zero_mem
  have hcF : R'.sideLength 2 ∈ F := by rw [hc]; exact F.one_mem
  obtain ⟨hPcoords, hQcoords⟩ := U.coefficient_field_vertices F hPaF hbase
    (hrot' 0) (hrot' 1) hcF
  obtain ⟨hp, hs⟩ := R.rational_angle_triple_data α β γ hangle
  refine ⟨{
    counts := fun i j => U.cornerCount (P'.vertex i) j
    positive := hp
    angle_sum := hs
    row_pos := U.outer_cornerCount_pos
    angle_eq := ?_
    conjugate_sum := ?_ }⟩
  · intro i
    calc
      (∑ j : Fin 3, (U.cornerCount (P'.vertex i) j : ℝ) *
          (Real.pi * (![α, β, γ] j : ℝ))) =
          ∑ j : Fin 3, (U.cornerCount (P'.vertex i) j : ℝ) * R'.cornerAngle j := by
        simp only [hangle']
      _ = P'.cornerAngle i := U.outer_angle_count_identity i
      _ = P.cornerAngle i := hPangle i
  · intro k hk
    have hn : 0 < 4 * α.den * β.den * γ.den := by
      have ha := α.den_pos
      have hb := β.den_pos
      have hg := γ.den_pos
      positivity
    have hθ : θ = 2 * Real.pi / ((4 * α.den * β.den * γ.den : ℕ) : ℝ) := by
      simp only [θ, rationalAngleRootStep, Nat.cast_mul, Nat.cast_ofNat]
    have hm (j : Fin 3) : R'.cornerAngle j = (rationalAngleNumerators α β γ j : ℝ) * θ :=
      (hangle' j).trans (rationalAngleNumerators_mul_step α β γ j).symm
    obtain ⟨σ, hσ⟩ := R'.exists_cosineSquare_rotation_embedding θ
      (4 * α.den * β.den * γ.den) k (rationalAngleNumerators α β γ)
      hn hθ hk hRcoords hm
    apply U.rational_conjugate_outer_total F σ hPcoords hRcoords hQcoords
      α β γ k hangle' hk
    intro j
    rw [hσ j, hangle' j]
    congr 2
    ring

theorem Triangle.CommensurableAngles.exists_rational_triple {R : Triangle}
    (hR : R.CommensurableAngles) :
    ∃ α β γ : ℚ, ∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ) := by
  have hr (j : Fin 3) : ∃ q : ℚ, (q : ℝ) = R.cornerAngle j / Real.pi :=
    (mem_rationalReals_iff _).mp (hR j)
  choose f hf using hr
  refine ⟨f 0, f 1, f 2, fun j => ?_⟩
  have he : R.cornerAngle j = Real.pi * (f j : ℝ) := by
    rw [hf j]
    field_simp
  fin_cases j <;> exact he

theorem CongruentTiling.rationalCornerData_of_commensurableAngles
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (hR : R.CommensurableAngles) :
    ∃ α β γ : ℚ,
      (∀ j : Fin 3, R.cornerAngle j = Real.pi * (![α, β, γ] j : ℝ)) ∧
      Nonempty (RationalCornerData P.cornerAngle α β γ) := by
  obtain ⟨α, β, γ, hangle⟩ := hR.exists_rational_triple
  exact ⟨α, β, γ, hangle, T.exists_rationalCornerData α β γ hangle⟩

end Erdos633
