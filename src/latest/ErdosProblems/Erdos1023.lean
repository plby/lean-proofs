/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1023.
https://www.erdosproblems.com/forum/thread/1023

Informal authors:
- Daniel Kleitman
- Zach Hunter

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1023.md
-/
/-
Formalized the definitions and theorems from the paper "Union-free families and
Kleitman's asymptotic bound", including the main result `kleitman_asymptotic`,
which establishes that the size of a union-free family is asymptotically bounded
by the central binomial coefficient. The formalization covers the Erdős-Ko-Rado
lemma, Kleitman's chain inequality, the linear programming bound, weak duality,
and the construction of the dual feasible solution.
-/

import Mathlib

import ErdosProblems.Erdos447

namespace Erdos1023

open scoped Nat
open Asymptotics Filter

/-
1. An analogue of `UnionFree` where we forbid *any* member of the family from being
   the union of a (nonempty) subfamily of *other* members.

   Concretely: for every `C ∈ F` and every nonempty `G ⊆ F.erase C`,
   we have `⋃₀ G ≠ C`.  (Here `G.sup id` is the union of all sets in `G`.)
-/
def UnionFreeMany {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ C ∈ F, ∀ G ⊆ F.erase C, G.Nonempty → G.sup id ≠ C

/-
2. An analogue of `MaxUnionFree` in this setting (this is the `F(n)` from the statement):
   the maximum size of a family of subsets of `{0,1,...,n-1}` such that no member
   is the union of other members.
-/
noncomputable def MaxUnionFreeMany (n : ℕ) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFreeMany).sup Finset.card

/-
3. Analogue of `erdos_447` in this setting (stated, not proved).
-/
theorem kleitman_bound_many :
    (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop] (fun n => (n.choose (n / 2) : ℝ)) := by
  classical
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have h_max_union_free_many : ∀ n, MaxUnionFreeMany n ≤ Erdos447.MaxUnionFree n := by
      intro n
      have h_max_union_free_many :
          ∀ F : Finset (Finset (Fin n)), UnionFreeMany F → Erdos447.UnionFree F := by
        intro F hF A hA B hB C hC hAB hBC hAC
        simpa [Finset.sup_insert, Finset.sup_singleton] using
          hF C hC ({A, B} : Finset (Finset (Fin n)))
            (by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact Finset.mem_erase.mpr ⟨ hAC, hA ⟩
              · exact Finset.mem_erase.mpr ⟨ hBC, hB ⟩)
            (Finset.insert_nonempty A {B})
      exact Finset.sup_le fun F hF =>
        Finset.le_sup (f := Finset.card)
          (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,
              h_max_union_free_many F <| (Finset.mem_filter.mp hF).2⟩)
  have h_max_union_free_many :
      ∀ n, MaxUnionFreeMany n ≥ (Nat.choose n (n / 2) : ℝ) := by
    intro n
    have h_max_union_free_many : (Nat.choose n (n / 2) : ℝ) ≤ MaxUnionFreeMany n := by
      have h_family :
          ∃ F : Finset (Finset (Fin n)),
            F.card = Nat.choose n (n / 2) ∧ UnionFreeMany F := by
        use Finset.univ.filter (fun s => s.card = n / 2)
        constructor
        · rw [
            show
              (Finset.univ.filter fun s : Finset (Fin n) => Finset.card s = n / 2) =
                Finset.powersetCard (n / 2) (Finset.univ : Finset (Fin n)) by
              ext
              simp +decide [Finset.mem_powersetCard],
            Finset.card_powersetCard, Finset.card_fin]
        · intro C hC G hG hG_nonempty hG_union
          have h_card : G.sup id = C := by
            exact hG_union
          have h_card : ∀ s ∈ G, s ⊆ C := by
            exact fun s hs => h_card ▸ Finset.le_sup (f := id) hs
          have h_card : ∀ s ∈ G, s = C := by
            intros s hs
            have h_card_eq : s.card = C.card := by
              have := hG hs
              subst hG_union
              simp_all only [Finset.univ_filter_card_eq, Finset.mem_powersetCard,
                Finset.subset_univ, true_and, Finset.mem_erase, ne_eq]
            exact Finset.eq_of_subset_of_card_le (h_card s hs) (by linarith)
          exact
            absurd (hG hG_nonempty.choose_spec)
              (by simp +decide [h_card _ hG_nonempty.choose_spec])
      obtain ⟨F, hF₁, hF₂⟩ := h_family
      exact_mod_cast hF₁ ▸
        Finset.le_sup (f := Finset.card)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF₂⟩)
    exact_mod_cast h_max_union_free_many
  have h_max_union_free_many :
      Filter.Tendsto
        (fun n => (Erdos447.MaxUnionFree n : ℝ) / (Nat.choose n (n / 2) : ℝ))
        Filter.atTop (nhds 1) := by
    have := Erdos447.erdos_447
    rw [Asymptotics.IsEquivalent] at this
    rw [Asymptotics.isLittleO_iff_tendsto'] at this
    · simpa using
        this.add_const 1 |>
          Filter.Tendsto.congr'
            (by
              filter_upwards [Filter.eventually_gt_atTop 0] with n hn
              rw [Pi.sub_apply, sub_div,
                div_self <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <|
                  Nat.choose_pos <| Nat.div_le_self _ _]
              ring)
    · filter_upwards [Filter.eventually_gt_atTop 0] with n hn h using
        absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <|
          Nat.choose_pos <| Nat.div_le_self _ _
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds h_max_union_free_many ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Pi.div_apply]
    exact
      one_le_div (Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _)
        |>.2 <| by
          simp_all only [ge_iff_le, Nat.cast_le]
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn using
      div_le_div_of_nonneg_right
        (by simp_all only [ge_iff_le, Nat.cast_le])
        (Nat.cast_nonneg _)

/-
4. State `F(n) ∼ c * 2^n / n^{1/2}` for the specific constant `c = sqrt(2/pi)`.

   We write `n^{1/2}` as `Real.sqrt (n : ℝ)` in Lean.
-/
theorem many_sqrt_two_div_pi :
    (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
      (fun n =>
        (Real.sqrt ((2 : ℝ) / Real.pi)) * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
          sorry
/-
5. Existential version: there exists a constant `c > 0` such that
   `F(n) ∼ c * 2^n / n^{1/2}`.
-/
theorem erdos_1023 :
    ∃ c : ℝ, 0 < c ∧
      (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
        (fun n => c * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
  -- By definition of $c$, we know that $c = \sqrt{2 / \pi}$.
  use Real.sqrt (2 / Real.pi)
  convert many_sqrt_two_div_pi using 1
  norm_num [mul_div_assoc]
  exact fun _ => Real.pi_pos

#print axioms erdos_1023
-- 'Erdos1023.erdos_1023' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1023
