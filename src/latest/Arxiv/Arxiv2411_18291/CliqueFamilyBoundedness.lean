import Arxiv.Arxiv2411_18291.CliqueRefinement
import Arxiv.Arxiv2411_18291.GreedyFamilyBounds

/-!
# Bounded clique boundaries, with multiplicities

The paper bounds the boundary multigraph of a clique family, not just its
underlying simple graph. An edge multiplicity bound and a sparse support
graph imply the required boundary bound. Unions satisfy the sum of the
two bounds even when the clique families overlap.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def IsCliqueFamilyBounded (r : ℕ) (D : Finset (Block V q)) (θ : ℝ) : Prop :=
  ∀ S : Block V r,
    ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) < θ * Fintype.card V

theorem degree_mono_int {J K : Block V r → ℤ} (hJK : ∀ e, J e ≤ K e) (S : Finset V) :
    degree J S ≤ degree K S := by
  apply sum_le_sum
  intro e _
  by_cases he : S ⊆ e.val
  · simpa only [if_pos he] using hJK e
  · simp only [if_neg he, le_refl]

theorem boundary_indicator_le_support (D : Finset (Block V q)) (G : Hypergraph V r)
    {M : ℕ} (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (hsupport : cliqueSupport r D ⊆ G) (e : Block V r) :
    boundary r (indicator D) e ≤ (M : ℤ) * indicator G e := by
  rw [boundary_indicator]
  by_cases he : e ∈ G
  · rw [indicator_apply_of_mem he, mul_one]
    exact_mod_cast hmult e
  · rw [indicator_apply_of_notMem he, mul_zero]
    have hzero : (D.filter fun Q => e.val ⊆ Q.val).card = 0 := by
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      obtain ⟨hQD, heQ⟩ := mem_filter.mp hQ
      exact he (hsupport (mem_biUnion.mpr ⟨Q, hQD, (mem_cliqueEdges _ _).mpr heQ⟩))
    simp only [hzero, Nat.cast_zero, le_refl]

theorem boundary_degree_le_support (D : Finset (Block V q)) (G : Hypergraph V r)
    {M : ℕ} (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (hsupport : cliqueSupport r D ⊆ G) (S : Finset V) :
    degree (boundary r (indicator D)) S ≤ (M : ℤ) * degree (indicator G) S := by
  have h := degree_mono_int (boundary_indicator_le_support D G hmult hsupport) S
  simpa only [degree, mul_sum, mul_ite, mul_zero] using h

theorem IsGraphBounded.cliqueFamilyBounded {G : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded G θ) (D : Finset (Block V q)) {M : ℕ} (hM : 0 < M)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (hsupport : cliqueSupport (r + 1) D ⊆ G) : IsCliqueFamilyBounded r D (M * θ) := by
  intro S
  have hdeg := boundary_degree_le_support D G hmult hsupport S.val
  rw [degree_indicator] at hdeg
  have hreal : ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) ≤
      (M : ℝ) * (G.filter fun e => S.val ⊆ e.val).card := by exact_mod_cast hdeg
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    _ ≤ _ := hreal
    _ < (M : ℝ) * (θ * Fintype.card V) := mul_lt_mul_of_pos_left (hG S) hMreal
    _ = _ := (mul_assoc _ _ _).symm

theorem boundary_indicator_union_le (D E : Finset (Block V q)) (e : Block V r) :
    boundary r (indicator (D ∪ E)) e ≤
      boundary r (indicator D) e + boundary r (indicator E) e := by
  simp only [boundary_indicator, filter_union]
  exact_mod_cast card_union_le (s := D.filter fun Q => e.val ⊆ Q.val)
    (t := E.filter fun Q => e.val ⊆ Q.val)

theorem IsCliqueFamilyBounded.union {D E : Finset (Block V q)} {θ θ' : ℝ}
    (hD : IsCliqueFamilyBounded r D θ) (hE : IsCliqueFamilyBounded r E θ') :
    IsCliqueFamilyBounded r (D ∪ E) (θ + θ') := by
  intro S
  have hdeg := degree_mono_int (boundary_indicator_union_le (r := r + 1) D E) S.val
  have hsum : degree (fun e => boundary (r + 1) (indicator D) e +
      boundary (r + 1) (indicator E) e) S.val =
      degree (boundary (r + 1) (indicator D)) S.val +
        degree (boundary (r + 1) (indicator E)) S.val := by
    unfold degree
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> simp only [add_zero]
  rw [hsum] at hdeg
  have hreal : ((degree (boundary (r + 1) (indicator (D ∪ E))) S.val : ℤ) : ℝ) ≤
      ((degree (boundary (r + 1) (indicator D)) S.val : ℤ) : ℝ) +
        ((degree (boundary (r + 1) (indicator E)) S.val : ℤ) : ℝ) := by exact_mod_cast hdeg
  exact hreal.trans_lt (by simpa only [add_mul] using add_lt_add (hD S) (hE S))

end Arxiv2411_18291
