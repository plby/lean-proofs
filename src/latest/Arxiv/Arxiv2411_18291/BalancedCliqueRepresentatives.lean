import Arxiv.Arxiv2411_18291.BalancedFiniteChoices
import Arxiv.Arxiv2411_18291.GroupedCliqueCounts

/-!
# Balanced representatives of disjoint clique groups

Choose one clique in every nonempty group. Counting its face incidences
with weight equal to the group size has expected degree bounded by the
original clique family. The finite tail criterion gives representatives
whose weighted face degrees are simultaneously at most twice that bound.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def representativeDegree (G : Finset (Finset (Block V q))) (Q : G → Block V q)
    (T : Finset V) : ℕ := ∑ c : G, if T ⊆ (Q c).val then c.val.card else 0

theorem exists_balanced_clique_representatives (hqr : r + 1 ≤ q)
    (D : Finset (Block V q)) (G : Finset (Finset (Block V q)))
    (hne : ∀ c ∈ G, c.Nonempty) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    {θ C : ℝ} (hD : IsCliqueFamilyBounded r D θ) (hC : 0 < C)
    (hcard : ∀ c ∈ G, (c.card : ℝ) ≤ C)
    (hsmall : Fintype.card (Block V r) *
      Real.exp (-(θ * Fintype.card V / (3 * C))) < 1) :
    ∃ Q : G → Block V q, (∀ c, Q c ∈ c.val) ∧ ∀ T : Block V r,
      (representativeDegree G Q T.val : ℝ) ≤ 2 * θ * Fintype.card V := by
  classical
  let : MeasurableSpace (Block V q) := ⊤
  let : ∀ c : G, Nonempty c.val := fun c => by
    obtain ⟨Q, hQ⟩ := hne c.val c.property
    exact ⟨⟨Q, hQ⟩⟩
  let s (T : Block V r) (c : G) : Finset c.val := univ.filter fun Q => T.val ⊆ Q.val.val
  have hsize (c : G) : (Fintype.card c.val : ℝ) ≤ C := by
    simpa only [Fintype.card_coe] using hcard c.val c.property
  have hmean (T : Block V r) (_ : T ∈ (univ : Finset (Block V r))) :
      (∑ c : G, ((s T c).card : ℝ)) ≤ θ * Fintype.card V := by
    have hcount : (∑ c : G, ((s T c).card : ℝ)) ≤
        ((D.filter fun Q => T.val ⊆ Q.val).card : ℝ) := by
      exact_mod_cast grouped_filter_card_le D G hsub hdis (fun Q => T.val ⊆ Q.val)
    have hface : ((D.filter fun Q => T.val ⊆ Q.val).card : ℝ) ≤
        ((degree (boundary (r + 1) (indicator D)) T.val : ℤ) : ℝ) := by
      exact_mod_cast face_clique_count_le_boundary_degree hqr D T
    exact hcount.trans (hface.trans (hD T).le)
  obtain ⟨ω, hω⟩ := RandomFiniteChoice.exists_balanced_choices
    (univ : Finset (Block V r)) s hC hsize hmean (by simpa only [card_univ] using hsmall)
  refine ⟨fun c => (ω c).val, fun c => (ω c).property, fun T => ?_⟩
  have heq : (∑ c : G, RandomFiniteChoice.weightedMember c (s T c) ω) =
      (representativeDegree G (fun c => (ω c).val) T.val : ℝ) := by
    simp only [representativeDegree, Nat.cast_sum]
    apply sum_congr rfl
    intro c _
    simp only [RandomFiniteChoice.weightedMember, Set.indicator, Set.mem_ofPred_eq,
      s, mem_filter, mem_univ, true_and, Fintype.card_coe, Nat.cast_ite, Nat.cast_zero]
  have h := hω T (mem_univ T)
  rw [heq] at h
  simpa only [mul_assoc] using h

end Arxiv2411_18291
