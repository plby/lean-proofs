import ErdosProblems.Erdos587.GreedyDenseFiber

/-!
Assemble dense fibers from disjoint sets of original elements. The mixed
sumset of the fibers, after one translation, lies in genuine subset sums
of their union; the number of used elements is tracked explicitly.
-/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem subsetSum_add_subset_union {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {A B : Finset G} (hdisjoint : Disjoint A B) :
    A.subsetSum + B.subsetSum ⊆ (A ∪ B).subsetSum := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨U, hUA, rfl⟩ := Finset.mem_subsetSum_iff.mp ha
  obtain ⟨V, hVB, rfl⟩ := Finset.mem_subsetSum_iff.mp hb
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨U ∪ V, Finset.union_subset_union hUA hVB, ?_⟩
  exact Finset.sum_union (hdisjoint.mono hUA hVB)

/-- Repeated greedy selection uses disjoint original elements, so mixed
fiber sums remain subset sums rather than sums with repetitions. -/
theorem exists_disjoint_dense_fibers (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (h M r q : ℕ)
    (hh : 0 < h) (hM : 1 ≤ M)
    (hbudget : q * (2 * (Nat.log 2 (P.dilate h).boxCard + 1) * h) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card) :
    let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
    ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ Xs : List (Finset ℤ),
      Xs.length = q ∧
      (∀ X ∈ Xs, X ⊆ (P.dilate h).carrier ∧
        (P.dilate h).boxCard < (M * c ^ P.rank) * X.card) ∧
      ∃ z : ℤ, ({z} : Finset ℤ) + nvFinsetListSum Xs ⊆ U.subsetSum := by
  let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
  change q * (c * h) ≤ r at hbudget
  change ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ Xs : List (Finset ℤ),
    Xs.length = q ∧
    (∀ X ∈ Xs, X ⊆ (P.dilate h).carrier ∧
      (P.dilate h).boxCard < (M * c ^ P.rank) * X.card) ∧
    ∃ z : ℤ, ({z} : Finset ℤ) + nvFinsetListSum Xs ⊆ U.subsetSum
  revert hbudget
  induction q with
  | zero =>
      intro _
      refine ⟨∅, Finset.empty_subset A, by simp, [], rfl, ?_, 0, ?_⟩
      · simp
      · simp
  | succ q ih =>
      intro hbudget
      have hprev : q * (c * h) ≤ r :=
        (Nat.mul_le_mul_right (c * h) (Nat.le_succ q)).trans hbudget
      obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ := ih hprev
      have hcard : A.card = (A \ U).card + U.card := by
        rw [Finset.card_sdiff_of_subset hUA, Nat.sub_add_cancel (Finset.card_le_card hUA)]
      have hremaining : ∀ D ⊆ A \ U, (A \ U).card ≤ D.card + c * h →
          2 * (P.dilate h).boxCard < M * (h • insert 0 D).card := by
        intro D hD hcost
        apply hdense D (hD.trans Finset.sdiff_subset)
        have htotal : U.card + c * h ≤ r := by
          rw [Nat.succ_mul] at hbudget
          omega
        omega
      have hone : (2 * h) * (Nat.log 2 (P.dilate h).boxCard + 1) ≤ c * h := by
        exact le_of_eq (by dsimp [c]; ring)
      obtain ⟨S, hS, hScard, w, X, hX, hXsum, hXcard⟩ :=
        exists_greedy_dense_fiber P (A \ U) hzero
          (Finset.sdiff_subset.trans hA) h M (c * h) hh hM hone hremaining
      have hdisjoint : Disjoint S U := by
        apply Finset.disjoint_left.mpr
        intro x hxS hxU
        exact (Finset.mem_sdiff.mp (hS hxS)).2 hxU
      refine ⟨S ∪ U, Finset.union_subset (hS.trans Finset.sdiff_subset) hUA,
        ?_, X :: Xs, by simp [hlen], ?_, w + z, ?_⟩
      · calc
          (S ∪ U).card ≤ S.card + U.card := Finset.card_union_le _ _
          _ ≤ c * h + q * (c * h) := Nat.add_le_add hScard hUcard
          _ = (q + 1) * (c * h) := by ring
      · intro Y hY
        rcases List.mem_cons.mp hY with rfl | hY
        · exact ⟨hX, hXcard⟩
        · exact hXs Y hY
      · have hcover : (({w} : Finset ℤ) + X) +
            (({z} : Finset ℤ) + nvFinsetListSum Xs) ⊆ (S ∪ U).subsetSum :=
          (Finset.add_subset_add hXsum hsum).trans (subsetSum_add_subset_union hdisjoint)
        rw [nvFinsetListSum_cons, ← Finset.singleton_add_singleton, add_add_add_comm]
        exact hcover

end Erdos587.CFP
