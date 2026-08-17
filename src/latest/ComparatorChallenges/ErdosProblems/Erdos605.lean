import Mathlib

/-!
# Erdős Problem 605

An explicit point--line incidence construction.  The detailed mathematics and
Leanization plan are in `tex/605.tex`.
-/

open Filter Set
open scoped Topology

namespace Erdos605

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable def pairDistance {n : ℕ} (x : Fin n → E3) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ dist (x i) (x j), fun _ _ ↦ dist_comm _ _⟩

/-- A finite set of non-diagonal `Sym2` values counts unordered geometric pairs. -/
def Erdos605Statement : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
    ∃ center : E3, ∃ radius : ℝ, 0 < radius ∧ ∀ n : ℕ,
      ∃ x : Fin n → E3, ∃ d : ℝ, ∃ E : Finset (Sym2 (Fin n)),
        Function.Injective x ∧
        (∀ i, dist (x i) center = radius) ∧
        0 < d ∧
        (∀ e ∈ E, ¬ e.IsDiag ∧ pairDistance x e = d) ∧
        f n * (n : ℝ) ≤ (E.card : ℝ)

/-! ## The all-`n` scale -/

def scale (n : ℕ) : ℕ :=
  Nat.findGreatest (fun q ↦ 3 * q ^ 3 ≤ n) n


theorem erdos_605 : Erdos605Statement := by
  sorry

end Erdos605
