import Mathlib
import ErdosProblems.Erdos336.CyclicFiberSmoothing

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rank-one full-fibre endgame with the sharp one-third cost
-/

namespace Erdos336

/-- A convenient integer ceiling for the Deléglise--Plagne quadratic bound. -/
def rankOneCoverCost (H : ℕ) : ℕ :=
  ((H + 1) ^ 2 + 3 * H + 2) / 3

lemma rankOneCoverCost_ceiling (H : ℕ) :
    (H + 1) ^ 2 + 3 * H ≤ 3 * rankOneCoverCost H := by
  dsimp [rankOneCoverCost]
  omega

/-- Once the geometric interval-cover estimate and a full-fibre core are
available, endpoint smoothing gives full exact coverage with leading cost
`H²/3`.  This is the complete arithmetic/group-theoretic rank-one endgame. -/
theorem full_coverage_of_rankOne_core_and_interval_bound
    {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 0 < m)
    (π : G →+ ZMod m) {A : Set G} {β : ZMod m}
    {p q : G} {M L t H : ℕ}
    (hp : p ∈ A) (hq : q ∈ A)
    (hstep : π q = π p + (L : ZMod m))
    (hcore : ∀ s : ℕ, s ≤ M → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly A t y)
    (hLM : L ≤ M) (hLpos : 0 < L)
    (hinterval : 3 * m ≤ L * (H + 1) ^ 2 + 3 * H) :
    ∀ y : G,
      GroupRepExactly A (t + rankOneCoverCost H) y := by
  have hceil := rankOneCoverCost_ceiling H
  have hscaled : 3 * m ≤ 3 * (rankOneCoverCost H * L) := by
    calc
      3 * m ≤ L * (H + 1) ^ 2 + 3 * H := hinterval
      _ ≤ L * ((H + 1) ^ 2 + 3 * H) := by
        nlinarith
      _ ≤ L * (3 * rankOneCoverCost H) :=
        Nat.mul_le_mul_left L hceil
      _ = 3 * (rankOneCoverCost H * L) := by ring
  have hmKL : m ≤ rankOneCoverCost H * L := by omega
  have hwidth : m - 1 ≤ rankOneCoverCost H * L + M := by omega
  exact cyclic_full_fiber_endpoint_smoothing hm π hp hq hstep hcore
    hwidth hLM

/-- The rank-one cover cost is exactly `H²/3 + O(H)` in a simple pointwise
form useful for later asymptotics. -/
theorem rankOneCoverCost_bound (H : ℕ) :
    3 * rankOneCoverCost H ≤ H ^ 2 + 5 * H + 5 := by
  have hd := Nat.mul_div_le ((H + 1) ^ 2 + 3 * H + 2) 3
  dsimp [rankOneCoverCost]
  calc
    3 * (((H + 1) ^ 2 + 3 * H + 2) / 3) ≤
        (H + 1) ^ 2 + 3 * H + 2 := hd
    _ ≤ H ^ 2 + 5 * H + 5 := by nlinarith

end Erdos336
