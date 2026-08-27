import ErdosProblems.Erdos587.HooleyCoordinateFiber
import ErdosProblems.Erdos587.DenseFiberBlocks

/-! # Disjoint dense coordinate fibers retain exact subset-sum provenance -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

theorem delta_exists_disjoint_coordinate_fibers {d : ℕ} (A : Finset (Fin d → ℤ))
    (L : Fin d → ℕ) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (h M r q : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (nvCoordBox (fun i => 2 * (h * L i))).card < M * (h • insert 0 D).card) :
    let T := (nvCoordBox (fun i => 2 * (h * L i))).card
    let c := 2 * (Nat.log 2 T + 1)
    q * (c * h) ≤ r →
    ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ Xs : List (Finset (Fin d → ℤ)),
      Xs.length = q ∧
      (∀ X ∈ Xs, X ⊆ nvCoordBox (fun i => 2 * (h * L i)) ∧ T < (M * c ^ d) * X.card) ∧
      ∃ z : Fin d → ℤ, ({z} : Finset (Fin d → ℤ)) + nvFinsetListSum Xs ⊆ U.subsetSum := by
  classical
  let T := (nvCoordBox (fun i => 2 * (h * L i))).card
  let c := 2 * (Nat.log 2 T + 1)
  dsimp only
  induction q with
  | zero =>
    intro _
    refine ⟨∅, Finset.empty_subset A, by simp, [], rfl, ?_, 0, ?_⟩
    · simp
    · simp
  | succ q ih =>
    intro hbudget
    change (q + 1) * (c * h) ≤ r at hbudget
    have hprev : q * (c * h) ≤ r :=
      (Nat.mul_le_mul_right (c * h) (Nat.le_succ q)).trans hbudget
    obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ := ih hprev
    change U.card ≤ q * (c * h) at hUcard
    have hcard : A.card = (A \ U).card + U.card := by
      rw [Finset.card_sdiff_of_subset hUA, Nat.sub_add_cancel (Finset.card_le_card hUA)]
    have hremaining : ∀ D ⊆ A \ U, (A \ U).card ≤ D.card + c * h →
        2 * T < M * (h • insert 0 D).card := by
      intro D hD hcost
      apply hdense D (hD.trans Finset.sdiff_subset)
      have htotal : U.card + c * h ≤ r := by rw [Nat.succ_mul] at hbudget; omega
      omega
    have hone : (2 * h) * (Nat.log 2 T + 1) ≤ c * h := le_of_eq (by dsimp [c]; ring)
    obtain ⟨S, hS, hScard, w, X, hX, hXsum, hXcard⟩ :=
      delta_exists_greedy_coordinate_fiber (A \ U) L
        (fun a ha => hA a (Finset.mem_sdiff.mp ha).1) h M (c * h) hh hM hone hremaining
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
    · have hcover : (({w} : Finset (Fin d → ℤ)) + X) +
          (({z} : Finset (Fin d → ℤ)) + nvFinsetListSum Xs) ⊆ (S ∪ U).subsetSum :=
        (Finset.add_subset_add hXsum hsum).trans (subsetSum_add_subset_union hdisjoint)
      rw [nvFinsetListSum_cons, ← Finset.singleton_add_singleton, add_add_add_comm]
      exact hcover

end Erdos587.CFP
