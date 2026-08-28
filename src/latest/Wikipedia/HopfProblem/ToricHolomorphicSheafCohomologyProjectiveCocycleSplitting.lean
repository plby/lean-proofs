import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycleUniqueness

/-!
# Three actual Laurent decompositions for projective chart cocycles

The coordinates are `[1:x:y]`, `[u:1:v]`, and `[t:s:1]`.
The cocycle relation uses their literal projective coordinate change.
All six entire functions below are supplied by the proved parametric
Cauchy-integral splitting on the actual punctured affine chart.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle

theorem swap_entire {f : ℂ × ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => f (q.2, q.1)) univ := by
  intro q _
  exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
    (hf (q.2, q.1) (mem_univ _)) (analyticAt_snd.prod analyticAt_fst)

theorem exists_first_coordinate_splitting {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.1 ≠ 0}) :
    ∃ p m : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ p univ ∧
      AnalyticOnNhd ℂ m univ ∧ (∀ y, m (0, y) = 0) ∧
      ∀ x y : ℂ, x ≠ 0 → f (x, y) = p (x, y) + m (x⁻¹, y) := by
  have hs : AnalyticOnNhd ℂ (fun q : ℂ × ℂ => f (q.2, q.1)) {q | q.2 ≠ 0} := by
    intro q hq
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
      (hf (q.2, q.1) hq) (analyticAt_snd.prod analyticAt_fst)
  obtain ⟨p, m, hp, hm, hm₀, heq⟩ := Laurent.exists_entire_parametric_splitting hs
  exact ⟨fun q => p (q.2, q.1), fun q => m (q.2, q.1),
    swap_entire hp, swap_entire hm, hm₀, fun x y hx => heq y x hx⟩

/-- The three functions of an additive cocycle, written in the actual
projective overlap coordinates. -/
structure ChartCocycle where
  zeroOne : ℂ × ℂ → ℂ
  zeroTwo : ℂ × ℂ → ℂ
  oneTwo : ℂ × ℂ → ℂ
  zeroOne_analytic : AnalyticOnNhd ℂ zeroOne {q | q.1 ≠ 0}
  zeroTwo_analytic : AnalyticOnNhd ℂ zeroTwo {q | q.2 ≠ 0}
  oneTwo_analytic : AnalyticOnNhd ℂ oneTwo {q | q.2 ≠ 0}
  cocycle : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
    zeroOne (x, y) + oneTwo (x⁻¹, y / x) = zeroTwo (x, y)

/-- This record stores constructed Cauchy-integral decompositions, with
their actual analytic functions and exact pointwise identities. -/
structure LaurentData (h : ChartCocycle) where
  A : ℂ × ℂ → ℂ
  B : ℂ × ℂ → ℂ
  C : ℂ × ℂ → ℂ
  D : ℂ × ℂ → ℂ
  E : ℂ × ℂ → ℂ
  F : ℂ × ℂ → ℂ
  A_analytic : AnalyticOnNhd ℂ A univ
  B_analytic : AnalyticOnNhd ℂ B univ
  C_analytic : AnalyticOnNhd ℂ C univ
  D_analytic : AnalyticOnNhd ℂ D univ
  E_analytic : AnalyticOnNhd ℂ E univ
  F_analytic : AnalyticOnNhd ℂ F univ
  B_zero : ∀ y : ℂ, B (0, y) = 0
  D_zero : ∀ u : ℂ, D (u, 0) = 0
  F_zero : ∀ x : ℂ, F (x, 0) = 0
  zeroOne_eq : ∀ x y : ℂ, x ≠ 0 →
    h.zeroOne (x, y) = A (x, y) + B (x⁻¹, y)
  oneTwo_eq : ∀ u v : ℂ, v ≠ 0 →
    h.oneTwo (u, v) = C (u, v) + D (u, v⁻¹)
  zeroTwo_eq : ∀ x y : ℂ, y ≠ 0 →
    h.zeroTwo (x, y) - A (x, y) = E (x, y) + F (x, y⁻¹)

theorem exists_laurentData (h : ChartCocycle) : Nonempty (LaurentData h) := by
  obtain ⟨A, B, hA, hB, hB₀, hAB⟩ := exists_first_coordinate_splitting h.zeroOne_analytic
  obtain ⟨C, D, hC, hD, hD₀, hCD⟩ :=
    Laurent.exists_entire_parametric_splitting h.oneTwo_analytic
  have hrem : AnalyticOnNhd ℂ (fun q => h.zeroTwo q - A q) {q | q.2 ≠ 0} :=
    h.zeroTwo_analytic.sub (hA.mono (subset_univ _))
  obtain ⟨E, F, hE, hF, hF₀, hEF⟩ := Laurent.exists_entire_parametric_splitting hrem
  exact ⟨⟨A, B, C, D, E, F, hA, hB, hC, hD, hE, hF,
    hB₀, hD₀, hF₀, hAB, hCD, hEF⟩⟩

namespace LaurentData

variable {h : ChartCocycle} (L : LaurentData h)

theorem triple_identity (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    L.E (x, y) + L.F (x, y⁻¹) =
      L.B (x⁻¹, y) + L.C (x⁻¹, y / x) + L.D (x⁻¹, x * y⁻¹) := by
  have he := h.cocycle x y hx hy
  rw [L.zeroOne_eq x y hx, L.oneTwo_eq _ _ (div_ne_zero hy hx)] at he
  have hEF := L.zeroTwo_eq x y hy
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at he ⊢
  linear_combination -he - hEF

end LaurentData

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ProjectiveCocycle
