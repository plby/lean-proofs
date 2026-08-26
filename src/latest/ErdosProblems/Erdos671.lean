import ErdosProblems.Erdos671.Proof

open ContinuousMap Filter Set
open scoped BigOperators Topology

namespace Erdos671

/-- The fundamental Lagrange polynomial evaluated at a real point. -/
noncomputable def basisValue {n : ℕ} (X : Row n) (i : X.ι) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x - X.node j) / (X.node i - X.node j)

noncomputable def interpolation {n : ℕ} (X : Row n) (f : C(Interval, ℝ))
    (x : ℝ) : ℝ := ∑ i, f (X.node i) * basisValue X i x

noncomputable def lebesgueFunction {n : ℕ} (X : Row n) (x : ℝ) : ℝ :=
  ∑ i, |basisValue X i x|

/-- Both questions: Lebesgue functions are cofinally unbounded everywhere,
and each continuous function has a point of convergence of all interpolants. -/
theorem erdos_671 :
    ∃ X : ∀ n : ℕ, Row (n + 1),
      (∀ x : Interval, ∀ A : ℝ, ∀ N : ℕ,
        ∃ n ≥ N, A ≤ lebesgueFunction (X n) x) ∧
      ∀ f : C(Interval, ℝ), ∃ x : Interval,
        Tendsto (fun n ↦ interpolation (X n) f x) atTop (𝓝 (f x)) ∧
        ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgueFunction (X n) x := by
  have hI {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (x : ℝ) :
      interpolation X f x = interpolant X f x := by
    simp only [interpolation, interpolant, fundamental_eq_prod, basisValue]
  have hL {n : ℕ} (X : Row n) (x : ℝ) : lebesgueFunction X x = lebesgue X x := by
    simp only [lebesgueFunction, lebesgue, fundamental_eq_prod, basisValue]
  obtain ⟨X, _, hU, hC⟩ := source_erdos_671
  exact ⟨X, by simpa only [hL] using hU, by simpa only [hI, hL] using hC⟩

end Erdos671
