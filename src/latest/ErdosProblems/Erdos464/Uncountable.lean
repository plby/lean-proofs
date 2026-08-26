/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 464.
Informal author: Bernard de Mathan.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/464#post-7120
https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17
Original Lean version: 4.28.0, confirmed by the user who supplied the source files.
The original Mathlib revision and a license notice were not supplied.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos464

/-!
# Uncountability from a binary Cantor scheme, and extracting an irrational point
-/

/-- The space of infinite binary sequences is uncountable. -/
lemma not_countable_bool_arrow : ¬ Countable (ℕ → Bool) := by
  have h : Cardinal.aleph0 < Cardinal.mk (ℕ → Bool) := by
    rw [Cardinal.mk_arrow]
    simp only [Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id]
    calc Cardinal.aleph0 < 2 ^ Cardinal.aleph0 := Cardinal.cantor _
      _ = _ := by norm_num
  intro hc
  rw [← Cardinal.mk_le_aleph0_iff] at hc
  exact absurd hc (not_le.mpr h)

/-
If a binary scheme of nonempty closed sets in `ℝ` is antitone, has pairwise disjoint children,
and vanishing diameter, and every branch intersection lands inside `S`, then `S` is uncountable.
-/
lemma not_countable_of_cantorScheme (A : List Bool → Set ℝ)
    (hanti : CantorScheme.Antitone A)
    (hclosed : ∀ l, IsClosed (A l))
    (hnonempty : ∀ l, (A l).Nonempty)
    (hdisj : CantorScheme.Disjoint A)
    (hdiam : CantorScheme.VanishingDiam A)
    {S : Set ℝ}
    (hsub : ∀ (x : ℕ → Bool), (⋂ n, A (PiNat.res x n)) ⊆ S) :
    ¬ S.Countable := by
  -- Set `g : (ℕ → Bool) → ℝ := fun x => (inducedMap A).snd ⟨x, by rw [htot]; trivial⟩`.
  set g : (ℕ → Bool) → ℝ := fun x => (CantorScheme.inducedMap A).snd ⟨x, by
    apply (CantorScheme.ClosureAntitone.map_of_vanishingDiam hdiam (hanti.closureAntitone hclosed) hnonempty).ge; simp⟩
  generalize_proofs at *;
  -- Show that `g` is injective.
  have hg_inj : Function.Injective g := by
    intro x y hxy;
    exact funext fun n => by have := hdisj.map_injective hxy; aesop;
  -- Show that `g x ∈ S` for all x.
  have hg_mem : ∀ x : ℕ → Bool, g x ∈ S := by
    exact fun x => hsub x <| Set.mem_iInter.2 fun n => CantorScheme.map_mem _ _;
  intro hS_countable
  have h_countable_image : Set.Countable (Set.range g) := by
    exact hS_countable.mono ( Set.range_subset_iff.mpr hg_mem );
  exact not_countable_bool_arrow <| Set.countable_univ_iff.mp <| Set.Countable.mono ( fun x => by aesop ) <| h_countable_image.preimage hg_inj

/-
A non-countable subset of `ℝ` contains an irrational number.
-/
lemma exists_irrational_of_not_countable {S : Set ℝ} (h : ¬ S.Countable) :
    ∃ θ ∈ S, Irrational θ := by
  contrapose! h;
  exact Set.Countable.mono ( fun x hx => by unfold Irrational at *; aesop ) ( Set.countable_range ( fun q : ℚ => ( q : ℝ ) ) )

end Erdos464
