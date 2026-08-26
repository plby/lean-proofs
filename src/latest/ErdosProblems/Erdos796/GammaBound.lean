import ErdosProblems.Erdos796.MultiplicativeSidon
import ErdosProblems.Erdos796.GammaBasic
import ErdosProblems.Erdos796.KST
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A uniform upper bound for the cofactor functional

This file isolates the finite factor-graph argument used to show that the
variational constant `Gamma` is finite.  The first lemmas are deliberately
stated for an arbitrary choice of factorizations: this separates the
combinatorial `C₄` argument from the number-theoretic construction of balanced
factors.
-/

namespace Erdos796

open scoped BigOperators

namespace GammaBound

/-- The multiplication map on a factor edge. -/
def edgeProduct (e : ℕ × ℕ) : ℕ := e.1 * e.2

/-- Any injectively chosen factor graph of a compatible fibre is `C₄`-free.

The proof uses four distinct fibre elements around a putative four-cycle.
The opposite corners give the same product in two different ways, hence four
ordered representations, contradicting the bound `productRepCount ≤ 2`.
-/
theorem c4Free_of_factor_edges
    {U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hmem : ∀ e ∈ E, edgeProduct e ∈ U)
    (hinj : Set.InjOn edgeProduct (E : Set (ℕ × ℕ)))
    (hrep : ∀ m : ℕ, productRepCount U U m ≤ 2) :
    Bipartite.C4Free E := by
  intro x₁ x₂ y₁ y₂ h11 h12 h21 h22
  by_contra hdeg
  push Not at hdeg
  rcases hdeg with ⟨hxx, hyy⟩
  let a := x₁ * y₁
  let b := x₁ * y₂
  let c := x₂ * y₁
  let d := x₂ * y₂
  have haU : a ∈ U := hmem (x₁, y₁) h11
  have hbU : b ∈ U := hmem (x₁, y₂) h12
  have hcU : c ∈ U := hmem (x₂, y₁) h21
  have hdU : d ∈ U := hmem (x₂, y₂) h22
  have hab : a ≠ b := by
    intro hab
    exact hyy (congrArg Prod.snd (hinj h11 h12 hab))
  have hac : a ≠ c := by
    intro hac
    exact hxx (congrArg Prod.fst (hinj h11 h21 hac))
  have had : a ≠ d := by
    intro had
    exact hxx (congrArg Prod.fst (hinj h11 h22 had))
  have hdb : d ≠ b := by
    intro hdb
    exact hxx (congrArg Prod.fst (hinj h22 h12 hdb)).symm
  have hprod : a * d = b * c := by
    dsimp [a, b, c, d]
    ring
  let T : Finset (ℕ × ℕ) := {(a, d), (d, a), (b, c)}
  have hTcard : T.card = 3 := by
    simp [T, had, hab, hdb]
  have hTsub : T ⊆ (U ×ˢ U).filter (fun uv => uv.1 * uv.2 = a * d) := by
    intro z hz
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simp [haU, hdU]
    · simp [haU, hdU, mul_comm]
    · simp [hbU, hcU, hprod]
  have hthree : 3 ≤ productRepCount U U (a * d) := by
    rw [productRepCount]
    rw [← hTcard]
    exact Finset.card_le_card hTsub
  have := hrep (a * d)
  omega

/-- `edgeCount` really is the cardinality of an edge set supported on the
displayed two vertex classes. -/
theorem edgeCount_eq_card_of_subset_product
    {E : Finset (ℕ × ℕ)} {L R : Finset ℕ} (hE : E ⊆ L ×ˢ R) :
    Bipartite.edgeCount E L R = E.card := by
  have hmap : Set.MapsTo Prod.snd (E : Set (ℕ × ℕ)) (R : Set ℕ) := by
    intro e he
    exact (Finset.mem_product.mp (hE he)).2
  have hfiber (y : ℕ) (hy : y ∈ R) :
      (E.filter fun e => e.2 = y).card = Bipartite.leftDegree E L y := by
    rw [Bipartite.leftDegree]
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      have heE := (Finset.mem_filter.mp he).1
      have hey := (Finset.mem_filter.mp he).2
      have heLR := Finset.mem_product.mp (hE heE)
      exact Finset.mem_filter.mpr
        ⟨heLR.1, by simpa [← hey] using! heE⟩
    · intro e₁ he₁ e₂ he₂ hfst
      apply Prod.ext hfst
      exact (Finset.mem_filter.mp he₁).2.trans
        (Finset.mem_filter.mp he₂).2.symm
    · intro x hx
      have hxL := (Finset.mem_filter.mp hx).1
      have hxyE := (Finset.mem_filter.mp hx).2
      refine ⟨(x, y), Finset.mem_filter.mpr ⟨hxyE, rfl⟩, rfl⟩
  calc
    Bipartite.edgeCount E L R =
        ∑ y ∈ R, (E.filter fun e => e.2 = y).card := by
          apply Finset.sum_congr rfl
          intro y hy
          exact (hfiber y hy).symm
    _ = E.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise hmap

/-- The elementary inequality used to count degree excess in the large-prime
factor graph. -/
theorem degree_le_one_add_choose_two (d : ℕ) :
    d ≤ 1 + Nat.choose d 2 := by
  rcases d with _ | _ | d
  · simp
  · simp
  · rw [Nat.choose_succ_succ]
    rw [Nat.choose_one_right]
    omega

/-- A `C₄`-free graph has at most one base edge per right vertex, plus one
edge for every possible unordered pair of left neighbours.  This is the
sharper form needed for the large-prime part of the factor graph. -/
theorem edgeCount_le_card_add_choose
    {E : Finset (ℕ × ℕ)} (hfree : Bipartite.C4Free E)
    (L R : Finset ℕ) :
    Bipartite.edgeCount E L R ≤ R.card + Nat.choose L.card 2 := by
  have hpair := Bipartite.sum_choose_leftDegree_le_choose hfree L R
  calc
    Bipartite.edgeCount E L R =
        ∑ y ∈ R, Bipartite.leftDegree E L y := rfl
    _ ≤ ∑ y ∈ R, (1 + Nat.choose (Bipartite.leftDegree E L y) 2) := by
      apply Finset.sum_le_sum
      intro y hy
      exact degree_le_one_add_choose_two _
    _ = R.card + ∑ y ∈ R,
        Nat.choose (Bipartite.leftDegree E L y) 2 := by
      simp [Finset.sum_add_distrib]
    _ ≤ R.card + Nat.choose L.card 2 := Nat.add_le_add_left hpair _

end GammaBound

end Erdos796
