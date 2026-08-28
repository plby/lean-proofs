import Wikipedia.SmoothSixDPoincare.IsolatedMorseBand

/-!
# Separated squared-radius windows around finitely many distinct values

Choose an isolating radius at every point, then halve it. Every ordered
pair of critical values has a strict gap between the resulting windows.
The indexing remains the original finite set of points.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

/-- Finitely many distinct values admit pairwise ordered, strictly separated windows. -/
theorem exists_separated_value_radii {X : Type*} {f : X → ℝ} {K : Set X}
    (hK : K.Finite) (hinj : InjOn f K) :
    ∃ r : K → ℝ, (∀ p, 0 < r p) ∧
      ∀ p q : K, f p < f q → f p + (r p) ^ 2 < f q - (r q) ^ 2 := by
  have hex : ∀ p : K, ∃ ρ > (0 : ℝ), ρ < 1 ∧
      ∀ x ∈ K, f x ∈ Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p.val := by
    intro p
    exact exists_isolating_radius hK p.val (fun x hx hfx => hinj hx p.property hfx) zero_lt_one
  choose ρ hρ hρ₁ hisolated using hex
  refine ⟨fun p => ρ p / 2, fun p => half_pos (hρ p), ?_⟩
  intro p q hpq
  have hupper : f p + (ρ p) ^ 2 < f q := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated p q.val q.property ⟨by nlinarith [sq_nonneg (ρ p)], h⟩
    exact (ne_of_lt hpq) (congrArg f heq).symm
  have hlower : f p < f q - (ρ q) ^ 2 := by
    apply lt_of_not_ge
    intro h
    have heq := hisolated q p.val p.property ⟨h, by nlinarith [sq_nonneg (ρ q)]⟩
    exact (ne_of_lt hpq) (congrArg f heq)
  nlinarith

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
