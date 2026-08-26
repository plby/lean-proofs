import ErdosProblems.Erdos590

/-!
# Finite localizations of thin families

The positive game proof repeatedly localizes finite Boolean vectors and
bounded body or leaf indices. These are finite-color consequences of
the proved two-color Nash--Williams theorem. They do not homogenize an
unbounded natural-valued coloring.
-/

namespace Erdos591.Positive.Game

open Erdos590.Larson.NashWilliams

theorem thin_simultaneous_bool {I : Type*} (S : Finset I)
    (F : Set (Finset ℕ)) (hthin : FinThin F) (color : I → Finset ℕ → Bool)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ H, H ⊆ M ∧ H.Infinite ∧ ∀ i ∈ S, ∃ b : Bool,
      ∀ u, u ∈ F → (↑u : Set ℕ) ⊆ H → color i u = b := by
  classical
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, Set.Subset.rfl, hM, by simp⟩
  | @insert i S hi ih =>
      obtain ⟨L, hLM, hL, b, hb⟩ := nashWilliams_two F hthin (color i) hM
      obtain ⟨H, hHL, hH, hS⟩ := ih hL
      refine ⟨H, hHL.trans hLM, hH, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨b, fun u hu huH => hb u hu (huH.trans hHL)⟩
      · exact hS j hj

/-- The finite-color Nash--Williams theorem, derived by successively
deciding the Boolean indicator of each of the finitely many colors. -/
theorem thin_finite_color {C : Type*} [Finite C]
    (F : Set (Finset ℕ)) (hthin : FinThin F) (color : Finset ℕ → C)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ H, H ⊆ M ∧ H.Infinite ∧ ∃ c : C,
      ∀ u, u ∈ F → (↑u : Set ℕ) ⊆ H → color u = c := by
  classical
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨H, hHM, hH, hbool⟩ := thin_simultaneous_bool (Finset.univ : Finset C)
    F hthin (fun c u => decide (color u = c)) hM
  refine ⟨H, hHM, hH, ?_⟩
  by_cases hex : ∃ u, u ∈ F ∧ (↑u : Set ℕ) ⊆ H
  · obtain ⟨u, hu, huH⟩ := hex
    obtain ⟨b, hb⟩ := hbool (color u) (Finset.mem_univ _)
    have hbt : true = b := by simpa using hb u hu huH
    refine ⟨color u, ?_⟩
    intro v hv hvH
    have hvb := hb v hv hvH
    rw [← hbt] at hvb
    exact of_decide_eq_true hvb
  · exact ⟨color ∅, fun u hu huH => (hex ⟨u, hu, huH⟩).elim⟩

/-- A bounded natural-valued observable may be localized without any
claim about infinite-color Ramsey theory. Values outside the bound are
clamped only outside the hypotheses where the conclusion is used. -/
theorem thin_bounded_color (F : Set (Finset ℕ)) (hthin : FinThin F)
    (color : Finset ℕ → ℕ) (k : ℕ) {M : Set ℕ} (hM : M.Infinite)
    (hbound : ∀ u, u ∈ F → (↑u : Set ℕ) ⊆ M → color u ≤ k) :
    ∃ H, H ⊆ M ∧ H.Infinite ∧ ∃ c ≤ k,
      ∀ u, u ∈ F → (↑u : Set ℕ) ⊆ H → color u = c := by
  let bounded (u : Finset ℕ) : Fin (k + 1) :=
    ⟨min (color u) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  obtain ⟨H, hHM, hH, c, hc⟩ := thin_finite_color F hthin bounded hM
  refine ⟨H, hHM, hH, c.val, Nat.le_of_lt_succ c.isLt, ?_⟩
  intro u hu huH
  have heq := congrArg Fin.val (hc u hu huH)
  simpa [bounded, min_eq_left (hbound u hu (huH.trans hHM))] using heq

#print axioms thin_finite_color
#print axioms thin_bounded_color

end Erdos591.Positive.Game
