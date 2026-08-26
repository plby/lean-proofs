import Mathlib
import ErdosProblems.Erdos550.WholeMatchingSplit

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lower-capacity form of the whole-edge split

The probabilistic split theorem returns two absolute-error estimates.  This
wrapper converts them directly into the two lower bounds used by the
off--Turán allocation.
-/

open Finset

namespace Erdos550

theorem exists_whole_matching_split_lower
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : NNReal) (hp : p ≤ 1)
    (wX wY : κ → ℝ) (M t needX needY : ℝ)
    (hX0 : ∀ i, 0 ≤ wX i) (hXM : ∀ i, wX i ≤ M)
    (hY0 : ∀ i, 0 ≤ wY i) (hYM : ∀ i, wY i ≤ M)
    (ht : 0 < t)
    (hroom : (Fintype.card κ : ℝ) * M ^ 2 / 2 < t ^ 2)
    (hneedX : needX + t ≤ p.toReal * ∑ i, wX i)
    (hneedY : needY + t ≤ (1 - p.toReal) * ∑ i, wY i) :
    ∃ K : Finset κ,
      needX ≤ ∑ i ∈ K, wX i ∧
      needY ≤ ∑ i ∈ Finset.univ \ K, wY i := by
  obtain ⟨K, hX, hY⟩ :=
    exists_whole_matching_split p hp wX wY M t
      hX0 hXM hY0 hYM ht hroom
  refine ⟨K, ?_, ?_⟩
  · have hdev := (abs_lt.mp hX).1
    linarith
  · have hdev := (abs_lt.mp hY).1
    linarith

end Erdos550
