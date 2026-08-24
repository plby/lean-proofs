import ErdosProblems.Erdos587.DenseSubsetProgression
import ErdosProblems.Erdos587.DenseHighFold

/-!
Construct a homogeneous proper GAP in actual subset sums at the selected
high-fold scale. This combines disjoint dense blocks with the stable
reserve correction and records the full deletion and multiplier budgets.
It does not yet amplify the selected scale to the final required scale.
-/

open scoped Pointwise BigOperators

namespace Erdos587.CFP

theorem exists_homogeneous_GAP_in_subsetSums
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hproper : P.TProper h) (hpos : ∀ i, 0 < P.length i)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A) :
    let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
    let D := M * c ^ P.rank
    let q := nvDenseCount D P.rank
    let F := GeneralizedAP.nvStandardSideFactor (P.dilate h) D q
    let B := 2 * q * F
    F ≤ h → q * (c * h) + B ^ P.rank ≤ r →
    ∃ W ⊆ A, W.card ≤ q * (c * h) + B ^ P.rank ∧ ∃ Q : GeneralizedAP,
      Q.rank = P.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      Q.carrier ⊆ W.subsetSum ∧ Q.StepMultipliersBoundedByConstant P B ∧
      ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i = h * P.length j / F := by
  classical
  let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
  let D := M * c ^ P.rank
  let q := nvDenseCount D P.rank
  let F := GeneralizedAP.nvStandardSideFactor (P.dilate h) D q
  let B := 2 * q * F
  dsimp only
  intro hscale hbudget
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := Nat.mul_pos (by omega) (pow_pos hc _)
  have hF : 0 < F := by
    change 0 < GeneralizedAP.nvDenseProperFactor D (P.dilate h).rank *
      (q + 1) ^ (P.dilate h).rank
    exact Nat.mul_pos (GeneralizedAP.nvDenseProperFactor_pos hD) (pow_pos (by omega) _)
  obtain ⟨U, hUA, hUcard, Q, hQrank, hQproper, hQsum, hQstep, hQside⟩ :=
    exists_standardized_GAP_in_subsetSums P A hzero hA h M r hh hM hproper hdense
      ((Nat.le_add_right _ _).trans hbudget)
  have hQpos : ∀ i, 0 < Q.length i := by
    intro i
    let j := Fin.cast hQrank i
    rw [hQside i j rfl]
    exact standardized_side_pos (hpos j) hF hscale
  have hmult : ∀ j : Fin P.rank, ∃ a : ℤ, a ≠ 0 ∧ |a| ≤ (B : ℤ) ∧
      Q.step (Fin.cast hQrank.symm j) = a * P.step j := by
    intro j
    exact standardized_step_multiplier_nonzero P Q hQproper hQpos B hQstep
      (Fin.cast hQrank.symm j) j rfl
  choose a hane habs haeq using hmult
  have hsteps : ∀ i : Fin Q.rank, ∀ j : Fin P.rank,
      i.val = j.val → Q.step i = a j * P.step j := by
    intro i j hij
    have hidx : Fin.cast hQrank.symm j = i := Fin.ext hij.symm
    simpa only [hidx] using haeq j
  have hreserve : U.card + B ^ P.rank ≤ r :=
    (Nat.add_le_add_right hUcard _).trans hbudget
  obtain ⟨S, hS, hScard, hproper', hhom, hsum⟩ :=
    exists_homogeneous_translate_from_reserve P Q A U hzero hA hUA hQproper
      hQsum hQrank a hane B r habs hsteps hreserve hstable
  refine ⟨U ∪ S, Finset.union_subset hUA (hS.trans Finset.sdiff_subset), ?_,
    Q.translateBy (∑ x ∈ S, x), hQrank, hproper', hhom, hsum, hQstep, hQside⟩
  calc
    (U ∪ S).card ≤ U.card + S.card := Finset.card_union_le _ _
    _ ≤ q * (c * h) + B ^ P.rank := Nat.add_le_add hUcard (by omega)

end Erdos587.CFP
