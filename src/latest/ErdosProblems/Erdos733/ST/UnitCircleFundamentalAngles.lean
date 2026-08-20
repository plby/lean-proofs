import ErdosProblems.Erdos733.ST.UnitCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleFundamentalAngles]
lemma UnitCircleFundamentalAngles
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p) :
    ∃ θ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ,
      (∀ x, 0 ≤ θ x ∧ θ x < 2 * Real.pi) ∧
      (∀ x,
        x.1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (θ x) else Real.sin (θ x))) ∧
      Function.Injective θ := by
-- BODY
  let coordComplex : EuclideanSpace ℝ (Fin 2) → ℂ :=
    fun v => ⟨v (0 : Fin 2), v (1 : Fin 2)⟩
  have hcoord_norm :
      ∀ v : EuclideanSpace ℝ (Fin 2), ‖coordComplex v‖ = ‖v‖ := by
    intro v
    have hsq : ‖coordComplex v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk,
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ)]
      rw [Fin.sum_univ_two]
      simp [sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hfund :
      ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
        ∃ θ : ℝ,
          0 ≤ θ ∧ θ < 2 * Real.pi ∧
          x.1 =
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then Real.cos θ else Real.sin θ) := by
    intro x
    let z : ℂ := coordComplex (x.1 - p)
    let θ : ℝ := toIcoMod Real.two_pi_pos 0 (Complex.arg z)
    refine ⟨θ, ?_, ?_, ?_⟩
    · exact left_le_toIcoMod Real.two_pi_pos 0 (Complex.arg z)
    · simpa [zero_add, θ] using toIcoMod_lt_right Real.two_pi_pos 0 (Complex.arg z)
    · have hxcircle : dist x.1 p = 1 := hS x.2
      have hvnorm : ‖x.1 - p‖ = 1 := by
        simpa [UnitCircle, dist_eq_norm] using hxcircle
      have hznorm : ‖z‖ = 1 := by
        simpa [z, hcoord_norm] using hvnorm
      have hangle : (θ : Real.Angle) = (Complex.arg z : Real.Angle) := by
        simp [θ]
      have hcos : Real.cos θ = (x.1 - p) (0 : Fin 2) := by
        have hcang := congrArg Real.Angle.cos hangle
        simp only [Real.Angle.cos_coe] at hcang
        have hc : Real.cos (Complex.arg z) = z.re := by
          have h := Complex.norm_mul_cos_arg z
          rw [hznorm, one_mul] at h
          exact h
        simpa [z, coordComplex] using hcang.trans hc
      have hsin : Real.sin θ = (x.1 - p) (1 : Fin 2) := by
        have hsang := congrArg Real.Angle.sin hangle
        simp only [Real.Angle.sin_coe] at hsang
        have hs : Real.sin (Complex.arg z) = z.im := by
          have h := Complex.norm_mul_sin_arg z
          rw [hznorm, one_mul] at h
          exact h
        simpa [z, coordComplex] using hsang.trans hs
      ext i
      fin_cases i <;>
        simp [hcos, hsin, sub_eq_add_neg, add_comm, add_left_comm]
  let θ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S} → ℝ :=
    fun x => Classical.choose (hfund x)
  have hθ_spec :
      ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ S},
        0 ≤ θ x ∧ θ x < 2 * Real.pi ∧
          x.1 =
            p + WithLp.toLp 2
              (fun i : Fin 2 =>
                if i = 0 then Real.cos (θ x) else Real.sin (θ x)) := by
    intro x
    exact Classical.choose_spec (hfund x)
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(hθ_spec x).1, (hθ_spec x).2.1⟩
  · intro x
    exact (hθ_spec x).2.2
  · intro x y hxy
    apply Subtype.ext
    calc
      x.1 =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (θ x) else Real.sin (θ x)) :=
        (hθ_spec x).2.2
      _ =
          p + WithLp.toLp 2
            (fun i : Fin 2 =>
              if i = 0 then Real.cos (θ y) else Real.sin (θ y)) := by
        simp [hxy]
      _ = y.1 := ((hθ_spec y).2.2).symm
