import ErdosProblems.Erdos587.PolynomialDenseStandard
import ErdosProblems.Erdos587.DenseFiberBlocks
import ErdosProblems.Erdos587.ReserveHomogeneity
import ErdosProblems.Erdos587.DenseHighFold

/-!
Selected-scale subset-sum progressions with polynomial filling costs.
Disjoint greedy blocks supply the dense summands, polynomial-count filling
gives uniform steps and side lengths, and a stable disjoint reserve makes
the base homogeneous. All size and reserve budgets remain explicit.
-/

open scoped Pointwise BigOperators

namespace Erdos587.GeneralizedAP

theorem card_carrier_translateBy (Q : GeneralizedAP) (z : ℤ) :
    (Q.translateBy z).carrier.card = Q.carrier.card := by
  rw [Q.carrier_translateBy]
  exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem exists_standardized_GAP_in_subsetSums_polynomial
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hproper : P.TProper h)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card) :
    let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
    let D := M * c ^ P.rank
    let q := denseBoxCount D P.rank
    let F := denseStandardFactor D P.rank
    q * (c * h) ≤ r →
    ∃ U ⊆ A, U.card ≤ q * (c * h) ∧ ∃ Q : GeneralizedAP,
      Q.rank = P.rank ∧ Q.Proper ∧ Q.carrier ⊆ U.subsetSum ∧
      Q.StepMultipliersBoundedByConstant P (2 * q * F) ∧
      (∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i = h * P.length j / F) ∧
      Q.carrier.card = ∏ i : Fin P.rank, (h * P.length i / F + 1) := by
  let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
  let D := M * c ^ P.rank
  let q := denseBoxCount D P.rank
  let F := denseStandardFactor D P.rank
  dsimp only
  intro hbudget
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := Nat.mul_pos (by omega) (pow_pos hc _)
  obtain ⟨U, hUA, hUcard, Xs, hlen, hXs, z, hsum⟩ :=
    exists_disjoint_dense_fibers P A hzero hA h M r q hh hM hbudget hdense
  have hlen' : Xs.length = denseBoxCount D (P.dilate h).rank := hlen
  obtain ⟨S, hSrank, hSproper, hSsub, hSstep, hSside, hScard⟩ :=
    exists_standardized_GAP_of_dense_summands (P.dilate h) D hD hproper Xs hlen'
      (fun X hX => (hXs X hX).1) (fun X hX => (hXs X hX).2.le)
  refine ⟨U, hUA, hUcard, S.translateBy z, hSrank, S.proper_translateBy hSproper z,
    ?_, ?_, ?_, ?_⟩
  · rw [S.carrier_translateBy]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hsum (Finset.mem_add.mpr
      ⟨z, Finset.mem_singleton_self z, x, hSsub hx, add_comm z x⟩)
  · intro i j hij
    exact hSstep i j hij
  · intro i j hij
    exact hSside i j hij
  · rw [S.card_carrier_translateBy]
    exact hScard

theorem exists_homogeneous_GAP_in_subsetSums_polynomial
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hproper : P.TProper h) (hpos : ∀ i, 0 < P.length i)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A) :
    let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
    let D := M * c ^ P.rank
    let q := denseBoxCount D P.rank
    let F := denseStandardFactor D P.rank
    let B := denseStepBound D P.rank
    F ≤ h → q * (c * h) + B ^ P.rank ≤ r →
    ∃ W ⊆ A, W.card ≤ q * (c * h) + B ^ P.rank ∧ ∃ Q : GeneralizedAP,
      Q.rank = P.rank ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      Q.carrier ⊆ W.subsetSum ∧ Q.StepMultipliersBoundedByConstant P B ∧
      (∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
        Q.length i = h * P.length j / F) ∧
      Q.carrier.card = ∏ i : Fin P.rank, (h * P.length i / F + 1) := by
  classical
  let c := 2 * (Nat.log 2 (P.dilate h).boxCard + 1)
  let D := M * c ^ P.rank
  let q := denseBoxCount D P.rank
  let F := denseStandardFactor D P.rank
  let B := denseStepBound D P.rank
  dsimp only
  intro hscale hbudget
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := Nat.mul_pos (by omega) (pow_pos hc _)
  have hF : 0 < F := denseStandardFactor_pos hD
  obtain ⟨U, hUA, hUcard, Q, hQrank, hQproper, hQsum, hQstep, hQside, hQcard⟩ :=
    exists_standardized_GAP_in_subsetSums_polynomial P A hzero hA h M r hh hM hproper hdense
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
    Q.translateBy (∑ x ∈ S, x), hQrank, hproper', hhom, hsum, hQstep, hQside, ?_⟩
  · calc
      (U ∪ S).card ≤ U.card + S.card := Finset.card_union_le _ _
      _ ≤ q * (c * h) + B ^ P.rank := Nat.add_le_add hUcard (by omega)
  · rw [Q.card_carrier_translateBy]
    exact hQcard

end Erdos587.CFP
