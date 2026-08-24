import ErdosProblems.Erdos587.GreedyMultiscale
import ErdosProblems.Erdos587.DenseFiberBlocks

/-!
Constant-density fibers from multiscale greedy growth. The subset-size
constant and the density loss are independent of the final fold count.
-/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem exists_multiscale_dense_fiber
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h K n F r : ℕ) (T : ℕ → ℕ) (hh : 0 < h)
    (hratio : ∀ j < n, T (j + 1) ≤ K * T j)
    (hinitial : (2 * h) * (Nat.log 2 (T 0) + 1) ≤ 2 ^ n * h)
    (hbudget : (4 * K + 1) * (2 ^ n * h) ≤ r)
    (hmodel : (P.dilate (2 ^ n * h)).boxCard ≤ F * T n)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card) :
    ∃ S ⊆ A, S.card ≤ (4 * K + 1) * (2 ^ n * h) ∧ ∃ z : ℤ, ∃ X : Finset ℤ,
      X ⊆ (P.dilate (2 ^ n * h)).carrier ∧ ({z} : Finset ℤ) + X ⊆ S.subsetSum ∧
      (P.dilate (2 ^ n * h)).boxCard ≤ (4 * F * (4 * K + 1) ^ P.rank) * X.card := by
  let H := 2 ^ n * h
  let c := 4 * K + 1
  obtain ⟨S, hSA, hScard, hSsize⟩ := exists_linear_size_dense_subsetSums A h K n r T
    hh hratio hinitial hbudget hdense
  have hsub : S.subsetSum ⊆ ((P.dilate H).dilate c).carrier := by
    simpa only [GeneralizedAP.dilate_dilate] using
      P.subsetSum_subset_dilate hzero S (hSA.trans hA) (c * H) hScard
  have hc : 0 < c := by dsimp [c]; positivity
  have hcover := hsub.trans ((P.dilate H).carrier_dilate_subset_offsets_add hc)
  have hFcard : ((P.dilate H).dilationCoverOffsets c).card ≤ c ^ P.rank := by
    simpa only [GeneralizedAP.rank_dilate] using (P.dilate H).card_dilationCoverOffsets_le c
  obtain ⟨z, _hz, hXsub, hXcard, hpiece, hpieceEq⟩ := exists_dense_cover_fiber
    S.subsetSum (P.dilate H).carrier ((P.dilate H).dilationCoverOffsets c)
      S.subsetSum_nonempty hcover hFcard
  let X := nvCoverFiber S.subsetSum (P.dilate H).carrier z
  refine ⟨S, hSA, hScard, z, X, hXsub, ?_, ?_⟩
  · rwa [hpieceEq] at hpiece
  · calc
      (P.dilate H).boxCard ≤ F * T n := hmodel
      _ ≤ F * (4 * S.subsetSum.card) := Nat.mul_le_mul_left F hSsize
      _ ≤ F * (4 * (c ^ P.rank * X.card)) :=
        Nat.mul_le_mul_left F (Nat.mul_le_mul_left 4 hXcard)
      _ = (4 * F * c ^ P.rank) * X.card := by ring

/-- The multiscale fibers can be selected repeatedly from disjoint sets,
with one fixed density and one fixed per-block budget. -/
theorem exists_disjoint_multiscale_dense_fibers
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h K n F r q : ℕ) (T : ℕ → ℕ) (hh : 0 < h)
    (hratio : ∀ j < n, T (j + 1) ≤ K * T j)
    (hinitial : (2 * h) * (Nat.log 2 (T 0) + 1) ≤ 2 ^ n * h)
    (hbudget : q * ((4 * K + 1) * (2 ^ n * h)) ≤ r)
    (hmodel : (P.dilate (2 ^ n * h)).boxCard ≤ F * T n)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card) :
    ∃ U ⊆ A, U.card ≤ q * ((4 * K + 1) * (2 ^ n * h)) ∧
      ∃ Xs : List (Finset ℤ), Xs.length = q ∧
        (∀ X ∈ Xs, X ⊆ (P.dilate (2 ^ n * h)).carrier ∧
          (P.dilate (2 ^ n * h)).boxCard ≤ (4 * F * (4 * K + 1) ^ P.rank) * X.card) ∧
        ∃ z : ℤ, ({z} : Finset ℤ) + nvFinsetListSum Xs ⊆ U.subsetSum := by
  let H := 2 ^ n * h
  let c := 4 * K + 1
  change q * (c * H) ≤ r at hbudget
  change ∃ U ⊆ A, U.card ≤ q * (c * H) ∧ ∃ Xs : List (Finset ℤ), Xs.length = q ∧
    (∀ X ∈ Xs, X ⊆ (P.dilate H).carrier ∧
      (P.dilate H).boxCard ≤ (4 * F * c ^ P.rank) * X.card) ∧
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
      have hprev : q * (c * H) ≤ r :=
        (Nat.mul_le_mul_right (c * H) (Nat.le_succ q)).trans hbudget
      obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ := ih hprev
      have hcard : A.card = (A \ U).card + U.card := by
        rw [Finset.card_sdiff_of_subset hUA, Nat.sub_add_cancel (Finset.card_le_card hUA)]
      have hremaining : ∀ D ⊆ A \ U, (A \ U).card ≤ D.card + c * H → ∀ j ≤ n,
          2 * T j < 4 * ((2 ^ j * h) • insert 0 D).card := by
        intro D hD hcost j hj
        apply hdense D (hD.trans Finset.sdiff_subset) _ j hj
        have htotal : U.card + c * H ≤ r := by
          rw [Nat.succ_mul] at hbudget
          omega
        omega
      obtain ⟨S, hS, hScard, w, X, hX, hXsum, hXcard⟩ :=
        exists_multiscale_dense_fiber P (A \ U) hzero (Finset.sdiff_subset.trans hA)
          h K n F (c * H) T hh hratio hinitial (le_refl _) hmodel hremaining
      have hdisjoint : Disjoint S U := by
        apply Finset.disjoint_left.mpr
        intro x hxS hxU
        exact (Finset.mem_sdiff.mp (hS hxS)).2 hxU
      refine ⟨S ∪ U, Finset.union_subset (hS.trans Finset.sdiff_subset) hUA,
        ?_, X :: Xs, by simp [hlen], ?_, w + z, ?_⟩
      · calc
          (S ∪ U).card ≤ S.card + U.card := Finset.card_union_le _ _
          _ ≤ c * H + q * (c * H) := Nat.add_le_add hScard hUcard
          _ = (q + 1) * (c * H) := by ring
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
