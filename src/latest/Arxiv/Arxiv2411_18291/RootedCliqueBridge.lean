import Arxiv.Arxiv2411_18291.RootedCliqueAvoidance

/-!
# Choosing a rooted clique meeting two prescribed cliques only in its root

The forbidden vertices are the union of the two prescribed cliques.
The previously proved collision bound leaves a bridge whenever the rooted
candidate family has positive size above twice that vertex budget.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {a q : ℕ}

theorem private_disjoint_inter_eq {e P Q : Finset V} (heP : e ⊆ P) (heQ : e ⊆ Q)
    (hdis : Disjoint (Q \ e) P) : Q ∩ P = e := by
  apply Subset.antisymm
  · intro v hv
    by_contra hve
    exact disjoint_left.mp hdis (mem_sdiff.mpr ⟨(mem_inter.mp hv).1, hve⟩)
      (mem_inter.mp hv).2
  · exact subset_inter heQ heP

variable [Fintype V]

theorem exists_rooted_clique_bridge (D : Finset (Block V q)) (e : Block V a)
    (haq : a < q) (hD : ∀ R ∈ D, e.val ⊆ R.val) (P Q : Block V q)
    (heP : e.val ⊆ P.val) (heQ : e.val ⊆ Q.val) {L : ℝ} (hL : 0 < L)
    (hsize : L ≤ D.card)
    (hbudget : ((2 * q : ℕ) : ℝ) * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2) :
    ∃ R ∈ D, R.val ∩ P.val = e.val ∧ R.val ∩ Q.val = e.val := by
  have hU : (P.val ∪ Q.val).card ≤ 2 * q := by
    have hc := card_union_le P.val Q.val
    rw [P.property, Q.property] at hc
    omega
  have hsmall : (P.val ∪ Q.val).card * (Fintype.card V : ℝ) ^ (q - a - 1) ≤ L / 2 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hU) (by positivity)).trans hbudget
  have hhalf := avoidingRootedCliques_card_half D e haq hD (P.val ∪ Q.val) hsize hsmall
  have hpos : (0 : ℝ) < (avoidingRootedCliques D e (P.val ∪ Q.val)).card :=
    (half_pos hL).trans_le hhalf
  obtain ⟨R, hR⟩ := card_pos.mp (Nat.cast_pos.mp hpos)
  have hRD := (mem_filter.mp hR).1
  have hdis := (mem_filter.mp hR).2
  exact ⟨R, hRD,
    private_disjoint_inter_eq heP (hD R hRD) (hdis.mono_right subset_union_left),
    private_disjoint_inter_eq heQ (hD R hRD) (hdis.mono_right subset_union_right)⟩

end Arxiv2411_18291
