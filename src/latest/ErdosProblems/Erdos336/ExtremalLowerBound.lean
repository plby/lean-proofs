import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.LowerPeriodicBasis

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lower bound for every extremal function in Problem 336
-/

namespace Erdos336

/-- Increasing the allowed variable representation order preserves
admissibility. -/
theorem Admissible.mono_variable_order
    {r r' k : ℕ} (hrr' : r ≤ r') (hadm : Admissible r k) :
    Admissible r' k := by
  obtain ⟨A, ⟨N, hN⟩, hexact⟩ := hadm
  refine ⟨A, ⟨N, ?_⟩, hexact⟩
  intro n hn
  obtain ⟨j, hjr, hrep⟩ := hN n hn
  exact ⟨j, hjr.trans hrr', hrep⟩

/-- The periodic construction at the largest multiple of three below `r`
gives a pointwise lower bound for every extremal function. -/
theorem extremal_lower_bound_floor_thirds
    {H : ℕ → ℕ} (hH : IsExtremalFunction H)
    {r : ℕ} (hr : 3 ≤ r) :
    3 * (r / 3) ^ 2 + 4 * (r / 3) ≤ H r := by
  let u := r / 3
  have hu : 1 ≤ u := by dsimp [u]; omega
  have h3u : 3 * u ≤ r := by dsimp [u]; omega
  have hadm0 : Admissible (3 * u) (3 * u ^ 2 + 4 * u) :=
    Erdos336.Problem336.lowerPeriodic_admissible u hu
  have hadm : Admissible r (3 * u ^ 2 + 4 * u) :=
    hadm0.mono_variable_order h3u
  exact (hH r (by omega)).2 _ hadm

end Erdos336
