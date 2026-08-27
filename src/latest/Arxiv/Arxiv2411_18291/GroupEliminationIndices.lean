import Arxiv.Arxiv2411_18291.BalancedCliqueRepresentatives

/-!
# One elimination index for every nonrepresentative group member

The old clique occurs once in this index set. Representative repetitions
are controlled by the weighted representative degree, so balanced choices
provide the root bounds needed for simultaneous elimination placements.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q : ℕ}

abbrev GroupEliminationIndex (G : Finset (Finset (Block V q))) (Q : G → Block V q) :=
  Σ c : G, ↥(c.val.erase (Q c))

theorem groupEliminationRight_mem (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D) (Q : G → Block V q)
    (i : GroupEliminationIndex G Q) : i.2.val ∈ D :=
  hsub i.1.val i.1.property (mem_erase.mp i.2.property).2

theorem groupEliminationRight_injective (G : Finset (Finset (Block V q)))
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val) (Q : G → Block V q) :
    Function.Injective (fun i : GroupEliminationIndex G Q => i.2.val) := by
  rintro ⟨c, x⟩ ⟨d, y⟩ hxy
  change x.val = y.val at hxy
  have hcd : c = d := by
    by_contra hne
    exact disjoint_left.mp (hdis hne) (mem_erase.mp x.property).2
      (hxy.symm ▸ (mem_erase.mp y.property).2)
  subst d
  exact congrArg (Sigma.mk c) (Subtype.ext hxy)

theorem groupEliminationLeft_degree_le (G : Finset (Finset (Block V q)))
    (Q : G → Block V q) (T : Finset V) :
    familyDegree (fun i : GroupEliminationIndex G Q => Q i.1) T ≤ representativeDegree G Q T := by
  classical
  have heq : familyDegree (fun i : GroupEliminationIndex G Q => Q i.1) T =
      ∑ c : G, (c.val.erase (Q c)).card * (if T ⊆ (Q c).val then 1 else 0) := by
    rw [familyDegree, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
    apply sum_congr rfl
    intro c _
    change (∑ _P : ↥(c.val.erase (Q c)), if T ⊆ (Q c).val then 1 else 0) = _
    simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, Nat.cast_id]
  rw [heq]
  apply sum_le_sum
  intro c _
  by_cases hT : T ⊆ (Q c).val
  · simp only [if_pos hT, mul_one]
    exact card_le_card (erase_subset _ _)
  · simp only [if_neg hT, mul_zero, le_refl]

theorem groupEliminationRight_degree_le (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val) (Q : G → Block V q) (T : Finset V) :
    familyDegree (fun i : GroupEliminationIndex G Q => i.2.val) T ≤
      (D.filter fun P => T ⊆ P.val).card := by
  classical
  have hrep (P : Block V q) :
      (univ.filter fun i : GroupEliminationIndex G Q => i.2.val = P).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact groupEliminationRight_injective G hdis Q
      ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
  simpa only [one_mul] using repeated_clique_degree_le D
    (fun i : GroupEliminationIndex G Q => i.2.val) (groupEliminationRight_mem D G hsub Q) hrep T

theorem representative_not_eliminated (G : Finset (Finset (Block V q)))
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (hQ : ∀ c, Q c ∈ c.val) (c : G) (i : GroupEliminationIndex G Q) :
    Q c ≠ i.2.val := by
  intro h
  have hci : c = i.1 := by
    by_contra hne
    exact disjoint_left.mp (hdis hne) (hQ c) (h.symm ▸ (mem_erase.mp i.2.property).2)
  have hne := (mem_erase.mp i.2.property).1
  exact hne (h.symm.trans (congrArg Q hci))

end Arxiv2411_18291
