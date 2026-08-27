import Arxiv.Arxiv2411_18291.PreciseTypicalCliqueCount

/-!
# Normalized clique-count estimates

Divide the rooted count by its factorial, then specialize to actual
cliques through a host edge, through a smaller face, or with no root.
The main term and its relative error are explicit.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

def cliqueMainTerm (n p : ℝ) (q r a : ℕ) : ℝ :=
  n ^ (q - a) * p ^ (q.choose r - a.choose r) / (q - a).factorial

theorem cliqueMainTerm_nonneg {n p : ℝ} (hn : 0 ≤ n) (hp : 0 ≤ p) (q r a : ℕ) :
    0 ≤ cliqueMainTerm n p q r a := by
  unfold cliqueMainTerm
  positivity

theorem cliqueMainTerm_pos {n p : ℝ} (hn : 0 < n) (hp : 0 < p) (q r a : ℕ) :
    0 < cliqueMainTerm n p q r a := by
  unfold cliqueMainTerm
  positivity

theorem relative_count_divide {x y d ε : ℝ} (hd : 0 < d) (h : |d * x - y| ≤ ε * y) :
    |x - y / d| ≤ ε * (y / d) := by
  have heq : x - y / d = (d * x - y) / d := by
    field_simp
  rw [heq, abs_div, abs_of_pos hd]
  exact (div_le_div_of_nonneg_right h hd.le).trans_eq (by ring)

variable {V : Type*} [Fintype V] [DecidableEq V] {r q a h : ℕ}

theorem cliqueEdges_empty_of_small (I : Block V a) (har : a < r) : cliqueEdges r I = ∅ := by
  apply card_eq_zero.mp
  rw [card_cliqueEdges, Nat.choose_eq_zero_of_lt har]

theorem IsTypical.rootedCliques_relative {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (I : Block V a) (haq : a ≤ q) :
    |((rootedCliques G I q).card : ℝ) - cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a| ≤
      (η * q * 2 ^ q) * cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a := by
  have ht : a + (q - a) = q := Nat.add_sub_of_le haq
  have hc := hT.rootedCliques_relative_error hqh hcη hη hη1 hsize I (q - a) ht.le
  rw [ht] at hc
  exact relative_count_divide (by exact_mod_cast Nat.factorial_pos (q - a)) hc

theorem IsTypical.cliqueFamily_root_relative {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (I : Block V a) (haq : a ≤ q) (hI : cliqueEdges (r + 1) I ⊆ G) :
    |(((cliqueFamily G q).filter fun Q => I.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a| ≤
      (η * q * 2 ^ q) * cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a := by
  rw [← rootedCliques_eq_filter_cliqueFamily G I hI]
  exact hT.rootedCliques_relative hqh hcη hη hη1 hsize I haq

theorem IsTypical.cliqueFamily_small_root_relative {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (I : Block V a) (haq : a ≤ q) (har : a < r + 1) :
    |(((cliqueFamily G q).filter fun Q => I.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a| ≤
      (η * q * 2 ^ q) * cliqueMainTerm (Fintype.card V) (density G) q (r + 1) a := by
  apply hT.cliqueFamily_root_relative hqh hcη hη hη1 hsize I haq
  rw [cliqueEdges_empty_of_small I har]
  exact empty_subset G

theorem IsTypical.cliqueFamily_edge_relative {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1)))
    (hqr : r + 1 ≤ q) {e : Block V (r + 1)} (he : e ∈ G) :
    |(((cliqueFamily G q).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm (Fintype.card V) (density G) q (r + 1) (r + 1)| ≤
      (η * q * 2 ^ q) * cliqueMainTerm (Fintype.card V) (density G) q (r + 1) (r + 1) := by
  apply hT.cliqueFamily_root_relative hqh hcη hη hη1 hsize e hqr
  intro f hf
  have hfe : f = e := Subtype.ext (eq_of_subset_of_card_le ((mem_cliqueEdges _ _).mp hf)
    (by rw [e.property, f.property]))
  exact hfe.symm ▸ he

theorem IsTypical.cliqueFamily_relative {G : Hypergraph V (r + 1)} {c η : ℝ}
    (hT : IsTypical G c h) (hqh : q.choose (r + 1) ≤ h) (hcη : c ≤ η)
    (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density G ^ q.choose (r + 1))) :
    |((cliqueFamily G q).card : ℝ) - cliqueMainTerm (Fintype.card V) (density G) q (r + 1) 0| ≤
      (η * q * 2 ^ q) * cliqueMainTerm (Fintype.card V) (density G) q (r + 1) 0 := by
  let I : Block V 0 := ⟨∅, card_empty⟩
  have hc := hT.cliqueFamily_small_root_relative hqh hcη hη hη1 hsize I (Nat.zero_le q)
    (Nat.succ_pos r)
  simpa only [I, empty_subset, filter_true] using hc

end Arxiv2411_18291
