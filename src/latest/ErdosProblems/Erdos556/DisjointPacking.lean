import ErdosProblems.Erdos556.Basic

/-!
# Greedy packing of bounded sets

These finite statements separate the packing and deletion arguments from
the graph-theoretic construction of connecting paths.
-/

namespace Erdos556

open Finset

theorem exists_disjoint_family {E : Type*} [DecidableEq E]
    (P : Finset E → Prop) (L b m : ℕ) (hbound : m * L ≤ b)
    (havoid : ∀ S : Finset E, S.card ≤ b →
      ∃ T : Finset E, P T ∧ T.card ≤ L ∧ Disjoint S T) :
    ∃ R : Fin m → Finset E, (∀ i, P (R i) ∧ (R i).card ≤ L) ∧
      Pairwise (fun i j => Disjoint (R i) (R j)) := by
  induction m with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ m ih =>
      obtain ⟨R, hR, hD⟩ := ih (by nlinarith)
      let S := (univ : Finset (Fin m)).biUnion R
      have hS : S.card ≤ b := by
        calc
          S.card ≤ ∑ i : Fin m, (R i).card := card_biUnion_le
          _ ≤ ∑ _i : Fin m, L := sum_le_sum (fun i _ => (hR i).2)
          _ = m * L := by simp
          _ ≤ b := by nlinarith
      obtain ⟨T, hT, hsize, hST⟩ := havoid S hS
      have hTR (i : Fin m) : Disjoint T (R i) :=
        hST.symm.mono_right (subset_biUnion_of_mem R (mem_univ i))
      refine ⟨Fin.cons T R, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hT, hsize⟩
        · exact hR j
      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro h; exact (h rfl).elim
        · intro _; exact hTR j
        · intro _; exact (hTR i).symm
        · intro h
          exact hD (fun he => h (congrArg Fin.succ he))

/-- A set meeting every member of a disjoint family has at least as many
vertices as the family has members. Empty members cause no exception. -/
theorem card_le_of_meets_disjoint_family {E I : Type*} [DecidableEq E]
    [Fintype I] (R : I → Finset E) (T : Finset E)
    (hD : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hmeet : ∀ i, ¬ Disjoint T (R i)) : Fintype.card I ≤ T.card := by
  classical
  have hx : ∀ i, ∃ x, x ∈ T ∧ x ∈ R i := by
    intro i
    simpa only [Finset.disjoint_left, not_forall, not_not, exists_prop] using hmeet i
  choose x hxT hxR using hx
  let f : I → T := fun i => ⟨x i, hxT i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : x i = x j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (hD hne) (hxR i) (heq ▸ hxR j)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem exists_disjoint_of_card_lt {E I : Type*} [DecidableEq E]
    [Fintype I] (R : I → Finset E) (T : Finset E)
    (hD : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hcard : T.card < Fintype.card I) : ∃ i, Disjoint T (R i) := by
  by_contra h
  push Not at h
  exact (Nat.not_le_of_gt hcard) (card_le_of_meets_disjoint_family R T hD h)

#print axioms exists_disjoint_family
#print axioms exists_disjoint_of_card_lt

end Erdos556
