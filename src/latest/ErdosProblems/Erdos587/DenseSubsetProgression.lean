import ErdosProblems.Erdos587.DenseFiberBlocks
import ErdosProblems.Erdos587.ReserveHomogeneity

/-!
Fill a standardized proper progression using disjoint greedy blocks.
Unlike the unrestricted high-fold filling theorem, the resulting carrier
lies in subset sums of an explicitly bounded subset of the original set.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem exists_standardized_GAP_in_subsetSums
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hproper : P.TProper h)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card) :
    let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
    let D := M * c ^ P.rank
    let q := nvDenseCount D P.rank
    let F := GeneralizedAP.nvStandardSideFactor (P.dilate h) D q
    q * (c * h) ≤ r →
    ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ Q : GeneralizedAP,
      Q.rank = P.rank ∧ Q.Proper ∧ Q.carrier ⊆ U.subsetSum ∧
      Q.StepMultipliersBoundedByConstant P (2 * q * F) ∧
      ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i = h * P.length j / F := by
  let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
  let D := M * c ^ P.rank
  let q := nvDenseCount D P.rank
  let F := GeneralizedAP.nvStandardSideFactor (P.dilate h) D q
  dsimp only
  intro hbudget
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := Nat.mul_pos (by omega) (pow_pos hc _)
  obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ :=
    exists_disjoint_dense_fibers P A hzero hA h M r q hh hM hbudget hdense
  have hlen' : Xs.length = nvDenseCount D (P.dilate h).rank := hlen
  obtain ⟨R, hrank, hrproper, hrstep, hrexc, hrside, hrsub, hrcard⟩ :=
    (P.dilate h).exists_large_proper_GAP_of_dense_different_summands_proper
      D hD hproper Xs hlen' (fun X hX => (hXs X hX).1)
        (fun X hX => (hXs X hX).2.le)
  have hout : GeneralizedAP.DenseProperOutput (P.dilate h) D Xs R :=
    ⟨hrank, hrproper, hrstep, hrexc, hrside, hrsub, hrcard⟩
  obtain ⟨S, hstandard, huniform⟩ := hout.exists_uniformStandard hD
  obtain ⟨hSrank, hSproper, _hSstep, hSsides, hSsub, _hScard⟩ := hstandard
  refine ⟨U, hUA, hUcard, S.translateBy z, hSrank, S.proper_translateBy hSproper z,
    ?_, ?_, ?_⟩
  · rw [S.carrier_translateBy]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply hsum
    exact Finset.mem_add.mpr ⟨z, Finset.mem_singleton_self z, x, hSsub hx, add_comm z x⟩
  · intro i j hij
    have hi := huniform i j hij
    rw [hlen] at hi
    exact hi
  · intro i j hij
    have hi := hSsides i j hij
    rw [hlen] at hi
    exact hi

end Erdos587.CFP
