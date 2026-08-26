/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Transfer of a simple real root to a nearby polynomial.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootSeparation

namespace Erdos521

theorem polynomial_signs_around_root (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1) (n : ℕ)
    {x δ ρ : ℝ} (_hδ : 0 < δ) (hρ : 0 < ρ)
    (hI : Set.Icc (x - ρ) (x + ρ) ⊆ Set.Icc (-1 : ℝ) 1)
    (hscale : (n + 1 : ℝ) ^ 3 * ρ ≤ δ / 2)
    (hroot : (polynomial ε n).eval x = 0)
    (hderiv : δ < |(polynomial ε n).derivative.eval x|) :
    ((polynomial ε n).eval (x - ρ) ≤ -(δ * ρ / 2) ∧
      δ * ρ / 2 ≤ (polynomial ε n).eval (x + ρ)) ∨
    ((polynomial ε n).eval (x + ρ) ≤ -(δ * ρ / 2) ∧
      δ * ρ / 2 ≤ (polynomial ε n).eval (x - ρ)) := by
  let p := polynomial ε n
  change δ < |p.derivative.eval x| at hderiv
  let I := Set.Icc (x - ρ) (x + ρ)
  have hxI : x ∈ I := ⟨by linarith, by linarith⟩
  have hlI : x - ρ ∈ I := ⟨le_rfl, by linarith⟩
  have hrI : x + ρ ∈ I := ⟨by linarith, le_rfl⟩
  have hlip (t : ℝ) (ht : t ∈ I) : |p.derivative.eval t - p.derivative.eval x| ≤ δ / 2 := by
    have htx : |t - x| ≤ ρ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (polynomial_derivative_lipschitz ε hε n (hI hxI) (hI ht)).trans
      ((mul_le_mul_of_nonneg_left htx (by positivity : 0 ≤ (n + 1 : ℝ) ^ 3)).trans hscale)
  by_cases hp : 0 ≤ p.derivative.eval x
  · have hpos : δ < p.derivative.eval x := by simpa only [abs_of_nonneg hp] using hderiv
    have hbound (t : ℝ) (ht : t ∈ interior I) : δ / 2 ≤ deriv (fun y ↦ p.eval y) t := by
      rw [Polynomial.deriv]
      have h := (abs_le.mp (hlip t (interior_subset ht))).1
      linarith
    have hgrowth := (convex_Icc (x - ρ) (x + ρ)).mul_sub_le_image_sub_of_le_deriv
      p.continuous.continuousOn p.differentiableOn hbound
    have hl := hgrowth (x - ρ) hlI x hxI (by linarith)
    have hr := hgrowth x hxI (x + ρ) hrI (by linarith)
    change p.eval x = 0 at hroot
    apply Or.inl
    constructor <;> nlinarith
  · have hneg : p.derivative.eval x < -δ := by
      have h := hderiv
      change δ < |p.derivative.eval x| at h
      rw [abs_of_neg (lt_of_not_ge hp)] at h
      linarith
    have hbound (t : ℝ) (ht : t ∈ interior I) : deriv (fun y ↦ p.eval y) t ≤ -δ / 2 := by
      rw [Polynomial.deriv]
      have h := (abs_le.mp (hlip t (interior_subset ht))).2
      linarith
    have hgrowth := (convex_Icc (x - ρ) (x + ρ)).image_sub_le_mul_sub_of_deriv_le
      p.continuous.continuousOn p.differentiableOn hbound
    have hl := hgrowth (x - ρ) hlI x hxI (by linarith)
    have hr := hgrowth x hxI (x + ρ) hrI (by linarith)
    change p.eval x = 0 at hroot
    apply Or.inr
    constructor <;> nlinarith

theorem polynomial_root_transfer (ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1) (n : ℕ)
    (q : Polynomial ℝ) {x δ ρ η : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hI : Set.Icc (x - ρ) (x + ρ) ⊆ Set.Icc (-1 : ℝ) 1)
    (hscale : (n + 1 : ℝ) ^ 3 * ρ ≤ δ / 2) (hη : η < δ * ρ / 2)
    (hroot : (polynomial ε n).eval x = 0)
    (hderiv : δ < |(polynomial ε n).derivative.eval x|)
    (hclose : ∀ t ∈ Set.Icc (x - ρ) (x + ρ), |q.eval t - (polynomial ε n).eval t| ≤ η) :
    ∃ y ∈ Set.Icc (x - ρ) (x + ρ), q.eval y = 0 := by
  have hl := abs_le.mp (hclose (x - ρ) ⟨le_rfl, by linarith⟩)
  have hr := abs_le.mp (hclose (x + ρ) ⟨by linarith, le_rfl⟩)
  rcases polynomial_signs_around_root ε hε n hδ hρ hI hscale hroot hderiv with hsign | hsign
  · have hleft : q.eval (x - ρ) ≤ 0 := by linarith [hsign.1, hl.2]
    have hright : 0 ≤ q.eval (x + ρ) := by linarith [hsign.2, hr.1]
    exact intermediate_value_Icc (by linarith : x - ρ ≤ x + ρ) q.continuous.continuousOn ⟨hleft, hright⟩
  · have hleft : 0 ≤ q.eval (x - ρ) := by linarith [hsign.2, hl.1]
    have hright : q.eval (x + ρ) ≤ 0 := by linarith [hsign.1, hr.2]
    exact intermediate_value_Icc' (by linarith : x - ρ ≤ x + ρ) q.continuous.continuousOn ⟨hright, hleft⟩

end Erdos521
