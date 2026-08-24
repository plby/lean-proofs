import ErdosProblems.Erdos587.GreedyDensity
import ErdosProblems.Erdos587.GAPDilationCover
import ErdosProblems.Erdos587.NVDevelopment

/-!
A small greedy subset supplies a dense translated fiber in the fixed
high-fold model. Pigeonholing the dilation cover costs only a logarithmic
factor per coordinate and preserves actual subset-sum provenance.
-/

open scoped Pointwise BigOperators

namespace Erdos587.GeneralizedAP

theorem subsetSum_subset_dilate (P : GeneralizedAP) (hzero : (0 : ℤ) ∈ P.carrier)
    (S : Finset ℤ) (hS : S ⊆ P.carrier) (n : ℕ) (hcard : S.card ≤ n) :
    S.subsetSum ⊆ (P.dilate n).carrier := by
  rw [← P.nsmul_carrier]
  intro x hx
  obtain ⟨W, hWS, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  have hw : W.val.sum ∈ W.val.card • P.carrier :=
    multiset_sum_mem_nsmul P.carrier (fun y hy => hS (hWS hy))
  have hsum : (∑ y ∈ W, y) ∈ W.card • P.carrier := by
    change W.sum id ∈ W.val.card • P.carrier
    rw [← Finset.sum_val]
    exact hw
  exact Finset.nsmul_subset_nsmul_right hzero
    ((Finset.card_le_card hWS).trans hcard) hsum

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

/-- One block of distinct original elements supplies a dense translated
fiber in `h*P`, using at most `2*h*(log₂(T)+1)` elements, where `T` is the
coefficient volume of `h*P`. -/
theorem exists_greedy_dense_fiber (P : GeneralizedAP) (A : Finset ℤ)
    (hzero : (0 : ℤ) ∈ P.carrier) (hA : A ⊆ P.carrier) (h M r : ℕ)
    (hh : 0 < h) (hM : 1 ≤ M)
    (hbudget : (2 * h) * (Nat.log 2 (P.dilate h).boxCard + 1) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card) :
    let T := (P.dilate h).boxCard
    let c := 2 * (Nat.log 2 T + 1)
    ∃ S ⊆ A, S.card ≤ c * h ∧ ∃ z : ℤ, ∃ X : Finset ℤ,
      X ⊆ (P.dilate h).carrier ∧ ({z} : Finset ℤ) + X ⊆ S.subsetSum ∧
        T < (M * c ^ P.rank) * X.card := by
  let T := (P.dilate h).boxCard
  let c := 2 * (Nat.log 2 T + 1)
  obtain ⟨S, hSA, hScard, hSsize⟩ := exists_small_subset_with_dense_subsetSums
    A h M T r hh hM hbudget hdense
  have hScard' : S.card ≤ c * h := by
    have heq : (2 * h) * (Nat.log 2 T + 1) = c * h := by dsimp [c]; ring
    simpa only [heq] using hScard
  have hsub : S.subsetSum ⊆ ((P.dilate h).dilate c).carrier := by
    simpa only [GeneralizedAP.dilate_dilate] using
      P.subsetSum_subset_dilate hzero S (hSA.trans hA) (c * h) hScard'
  have hc : 0 < c := by dsimp [c]; positivity
  have hcover := hsub.trans ((P.dilate h).carrier_dilate_subset_offsets_add hc)
  have hFcard : ((P.dilate h).dilationCoverOffsets c).card ≤ c ^ P.rank := by
    simpa only [GeneralizedAP.rank_dilate] using (P.dilate h).card_dilationCoverOffsets_le c
  obtain ⟨z, _hz, hXsub, hXcard, hpiece, hpieceEq⟩ := exists_dense_cover_fiber
    S.subsetSum (P.dilate h).carrier ((P.dilate h).dilationCoverOffsets c)
      S.subsetSum_nonempty hcover hFcard
  let X := nvCoverFiber S.subsetSum (P.dilate h).carrier z
  refine ⟨S, hSA, hScard', z, X, hXsub, ?_, ?_⟩
  · rwa [hpieceEq] at hpiece
  · exact hSsize.trans_le (by
      calc
        M * S.subsetSum.card ≤ M * (c ^ P.rank * X.card) := Nat.mul_le_mul_left M hXcard
        _ = (M * c ^ P.rank) * X.card := by ring)

end Erdos587.CFP
