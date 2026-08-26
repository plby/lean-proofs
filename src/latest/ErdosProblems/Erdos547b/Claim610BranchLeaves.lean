/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615SourceSelection
import ErdosProblems.Erdos547b.LeafImbalance

/-!
# Unbalanced tree branches have many leaves

This is the branchwise use of Zhao Fact 6.9 in Claim 6.10.  The bipartition
is the canonical distance-parity coloring rooted at the branch root.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim610BranchLeaves

open Finset Fintype SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem finTwo_eq_zero_or_one (c : Fin 2) : c = 0 ∨ c = 1 := by
  have hc := c.isLt
  by_cases hz : c.val = 0
  · left
    exact Fin.ext hz
  · right
    apply Fin.ext
    omega

/-- One class of the canonical rooted bipartition of a tree. -/
def treeColourClass (T : SimpleGraph V) (hT : T.IsTree) (root : V)
    (c : Fin 2) : Finset V :=
  Finset.univ.filter fun v => hT.coloringTwoOfVert root v = c

@[simp] theorem mem_treeColourClass
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) (c : Fin 2) (v : V) :
    v ∈ treeColourClass T hT root c ↔
      hT.coloringTwoOfVert root v = c := by
  simp [treeColourClass]

theorem treeColourClass_zero_union_one
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    treeColourClass T hT root 0 ∪ treeColourClass T hT root 1 =
      Finset.univ := by
  ext v
  have hc := (hT.coloringTwoOfVert root v).isLt
  simp only [Finset.mem_union, mem_treeColourClass, Finset.mem_univ, iff_true]
  omega

theorem treeColourClass_zero_disjoint_one
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    Disjoint (treeColourClass T hT root 0)
      (treeColourClass T hT root 1) := by
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  rw [mem_treeColourClass] at hv0 hv1
  omega

/-- The canonical color classes form a proper bipartition as soon as the
tree has at least two vertices. -/
theorem canonical_isProperBipartition
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (root : V)
    (hcard : 2 ≤ Fintype.card V) :
    Erdos547b.IsProperBipartition T
      (treeColourClass T hT root 0) (treeColourClass T hT root 1) := by
  let color := hT.coloringTwoOfVert root
  have hnontrivial : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hdeg : 0 < T.degree root :=
    hT.preconnected.degree_pos_of_nontrivial root
  obtain ⟨w, hrw⟩ := (T.degree_pos_iff_exists_adj root).mp hdeg
  refine {
    bipartite := ?_
    cover := ?_
    left_nonempty := ?_
    right_nonempty := ?_ }
  · refine {
      disjoint := by
        exact Finset.disjoint_coe.mpr
          (treeColourClass_zero_disjoint_one T hT root)
      mem_of_adj := ?_ }
    intro v w hvw
    have hne := color.valid hvw
    change
      (v ∈ treeColourClass T hT root 0 ∧
          w ∈ treeColourClass T hT root 1) ∨
        (v ∈ treeColourClass T hT root 1 ∧
          w ∈ treeColourClass T hT root 0)
    simp only [mem_treeColourClass]
    change (color v = 0 ∧ color w = 1) ∨
      (color v = 1 ∧ color w = 0)
    rcases finTwo_eq_zero_or_one (color v) with hv | hv <;>
      rcases finTwo_eq_zero_or_one (color w) with hw | hw <;> simp_all
  · rw [← Finset.coe_union, treeColourClass_zero_union_one,
      Finset.coe_univ]
  · refine ⟨root, ?_⟩
    rw [mem_treeColourClass]
    exact Erdos547b.RegularPair.coloringTwoOfVert_root T hT root
  · refine ⟨w, ?_⟩
    rw [mem_treeColourClass]
    have hne := color.valid hrw
    have hroot : color root = 0 :=
      Erdos547b.RegularPair.coloringTwoOfVert_root T hT root
    rcases finTwo_eq_zero_or_one (color w) with hw | hw
    · exfalso
      apply hne
      rw [hroot, hw]
    · change color w = 1
      exact hw

/-- The two canonical class cardinalities add to the order of the tree. -/
theorem card_treeColourClass_add
    (T : SimpleGraph V) (hT : T.IsTree) (root : V) :
    #(treeColourClass T hT root 0) + #(treeColourClass T hT root 1) =
      Fintype.card V := by
  rw [← Finset.card_union_of_disjoint
    (treeColourClass_zero_disjoint_one T hT root),
    treeColourClass_zero_union_one, Finset.card_univ]

/-- Zhao Fact 6.9 in the sharpened real ratio form used by Claim 6.10.
The extra one is exactly what pays for the possible loss of the rooted
branch vertex when the branch is reattached to its component root. -/
theorem many_leaves_of_ratio_not_between_add_one
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (root : V)
    (hcard : 2 ≤ Fintype.card V)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ¬(alpha <
        (#(treeColourClass T hT root 0) : ℝ) / Fintype.card V ∧
      (#(treeColourClass T hT root 0) : ℝ) / Fintype.card V <
        1 - alpha)) :
    (1 - 2 * alpha) * Fintype.card V + 1 ≤
      (#(Erdos547b.leavesIn T (Finset.univ : Finset V)) : ℕ) := by
  classical
  let A := treeColourClass T hT root 0
  let B := treeColourClass T hT root 1
  have hproper := canonical_isProperBipartition T hT root hcard
  have hsumNat : A.card + B.card = Fintype.card V :=
    card_treeColourClass_add T hT root
  have hsizePos : (0 : ℝ) < Fintype.card V := by positivity
  have hcases :
      (A.card : ℝ) / Fintype.card V ≤ alpha ∨
        1 - alpha ≤ (A.card : ℝ) / Fintype.card V := by
    by_cases hleft : (A.card : ℝ) / Fintype.card V ≤ alpha
    · exact Or.inl hleft
    · right
      by_contra hright
      apply hunbalanced
      exact ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
  have hleavesA : Erdos547b.leavesIn T A ⊆
      Erdos547b.leavesIn T (Finset.univ : Finset V) := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'.2⟩
  have hleavesB : Erdos547b.leavesIn T B ⊆
      Erdos547b.leavesIn T (Finset.univ : Finset V) := by
    intro v hv
    have hv' := (Finset.mem_filter.mp hv)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'.2⟩
  rcases hcases with hratio | hratio
  · have hAalpha : (A.card : ℝ) ≤ alpha * Fintype.card V :=
      (div_le_iff₀ hsizePos).mp hratio
    have hAleB : A.card ≤ B.card := by
      by_contra h
      have hBA : B.card < A.card := Nat.lt_of_not_ge h
      have hhalf : (Fintype.card V : ℝ) / 2 < A.card := by
        have hreal : (Fintype.card V : ℝ) < 2 * (A.card : ℝ) := by
          exact_mod_cast (by omega : Fintype.card V < 2 * A.card)
        linarith
      have halphaSize : alpha * Fintype.card V ≤
          (Fintype.card V : ℝ) / 2 := by
        nlinarith
      linarith
    have hfact := Erdos547b.card_leavesIn_larger_part T A B hT hproper hAleB
    have hfactR : (B.card - A.card + 1 : ℝ) ≤
        (Erdos547b.leavesIn T B).card := by exact_mod_cast hfact
    have htarget : (1 - 2 * alpha) * Fintype.card V + 1 ≤
        (B.card - A.card + 1 : ℝ) := by
      push_cast
      have hsumR : (A.card : ℝ) + B.card = Fintype.card V := by
        exact_mod_cast hsumNat
      nlinarith
    exact htarget.trans (hfactR.trans (by
      exact_mod_cast Finset.card_le_card hleavesB))
  · have hBalpha : (B.card : ℝ) ≤ alpha * Fintype.card V := by
      have hA : (1 - alpha) * Fintype.card V ≤ A.card :=
        (le_div_iff₀ hsizePos).mp hratio
      have hsumR : (A.card : ℝ) + B.card = Fintype.card V := by
        exact_mod_cast hsumNat
      nlinarith
    have hBleA : B.card ≤ A.card := by
      by_contra h
      have hAB : A.card < B.card := Nat.lt_of_not_ge h
      have hhalf : (Fintype.card V : ℝ) / 2 < B.card := by
        have hreal : (Fintype.card V : ℝ) < 2 * (B.card : ℝ) := by
          exact_mod_cast (by omega : Fintype.card V < 2 * B.card)
        linarith
      have halphaSize : alpha * Fintype.card V ≤
          (Fintype.card V : ℝ) / 2 := by
        nlinarith
      linarith
    have hproperSymm : Erdos547b.IsProperBipartition T B A := {
      bipartite := hproper.bipartite.symm
      cover := by simpa only [Set.union_comm] using hproper.cover
      left_nonempty := hproper.right_nonempty
      right_nonempty := hproper.left_nonempty }
    have hfact := Erdos547b.card_leavesIn_larger_part T B A hT hproperSymm hBleA
    have hfactR : (A.card - B.card + 1 : ℝ) ≤
        (Erdos547b.leavesIn T A).card := by exact_mod_cast hfact
    have htarget : (1 - 2 * alpha) * Fintype.card V + 1 ≤
        (A.card - B.card + 1 : ℝ) := by
      push_cast
      have hsumR : (A.card : ℝ) + B.card = Fintype.card V := by
        exact_mod_cast hsumNat
      nlinarith
    exact htarget.trans (hfactR.trans (by
      exact_mod_cast Finset.card_le_card hleavesA))

/-- The slightly weaker display without the integral `+1`. -/
theorem many_leaves_of_ratio_not_between
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (root : V)
    (hcard : 2 ≤ Fintype.card V)
    (alpha : ℝ) (halpha0 : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hunbalanced : ¬(alpha <
        (#(treeColourClass T hT root 0) : ℝ) / Fintype.card V ∧
      (#(treeColourClass T hT root 0) : ℝ) / Fintype.card V <
        1 - alpha)) :
    (1 - 2 * alpha) * Fintype.card V ≤
      (#(Erdos547b.leavesIn T (Finset.univ : Finset V)) : ℕ) := by
  have h := many_leaves_of_ratio_not_between_add_one T hT root hcard alpha
    halpha0 halphaHalf hunbalanced
  linarith

end Erdos547b.ZhaoClaim610BranchLeaves

#print axioms Erdos547b.ZhaoClaim610BranchLeaves.canonical_isProperBipartition
#print axioms Erdos547b.ZhaoClaim610BranchLeaves.many_leaves_of_ratio_not_between_add_one
#print axioms Erdos547b.ZhaoClaim610BranchLeaves.many_leaves_of_ratio_not_between
