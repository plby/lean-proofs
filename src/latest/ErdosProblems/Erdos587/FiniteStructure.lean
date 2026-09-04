import ErdosProblems.Erdos587.MultiscaleBudgets
import ErdosProblems.Erdos587.SubgroupStableMultiscale

/-!
The finite homogeneous structural theorem needed for the upper bound.
The only input conditions are interval containment and displayed numerical
budgets. The progression has rank one or two, long individual sides, large
cardinality, actual subset-sum containment, and a fixed base/span ratio.
-/

open scoped Pointwise BigOperators
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem exists_finite_homogeneous_structure (b : ℕ) :
    ∃ C K F₀ S : ℕ, 0 < C ∧ 0 < K ∧ 0 < F₀ ∧ 0 < S ∧
      ∀ (A : Finset ℤ) (L t k n H : ℕ), H = 2 ^ (k + n) →
        A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) → 0 < t → L ≤ t * b → C ≤ 2 ^ t →
        C * 2 ^ (t + t) ≤ 2 ^ k → k + n ≤ L → 4 * (L + 1) ≤ 2 ^ n →
        4 * freimanTSizeFactor K 2 ≤ H → F₀ ≤ H →
        2 * (6 * (L + 1) ^ 2 + 3) *
          (((4 * freimanTSizeFactor K 2) ^ 2 + 1) * (S * H)) + 2 ≤ A.card →
        2 * 2 ^ freimanRank K * freimanTSizeFactor K 2 * (2 ^ L + 1) < H ^ 2 * A.card →
        ∃ W ⊆ A, W.card ≤ S * H ∧ ∃ Q : GeneralizedAP,
          1 ≤ Q.rank ∧ Q.rank ≤ 2 ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
          Q.carrier ⊆ W.subsetSum ∧ (∀ i, H ≤ (2 * F₀) * Q.length i) ∧
          H ^ Q.rank * A.card ≤ 2 * (2 * F₀) ^ Q.rank * Q.carrier.card ∧
          Q.upperEndpoint ≤ ((S * (2 * F₀) : ℕ) : ℤ) * Q.coefficientSpan := by
  classical
  obtain ⟨C, K, hC, hK, hmodels⟩ := exists_uniform_stable_rank_two_model b
  let M := freimanTSizeFactor K 2
  let c := 4 * K + 1
  let D (d : ℕ) := 4 * M * c ^ d
  let f (d : ℕ) := denseStandardFactor (D d) d
  let q (d : ℕ) := denseBoxCount (D d) d
  let Bstep (d : ℕ) := denseStepBound (D d) d
  let F₀ := 1 + (Finset.range 3).sup f
  let S := 1 + (Finset.range 3).sup (fun d => q d * c + Bstep d ^ d)
  have hM : 0 < M := freimanTSizeFactor_pos hK (by omega)
  have hc : 0 < c := by dsimp [c]; omega
  have hD (d : ℕ) : 0 < D d := by dsimp [D]; positivity
  have hf (d : ℕ) : 0 < f d := denseStandardFactor_pos (hD d)
  have hF₀ : 0 < F₀ := by dsimp [F₀]; omega
  have hS : 0 < S := by dsimp [S]; omega
  have hfbound (d : ℕ) (hd : d ≤ 2) : f d ≤ F₀ := by
    exact (Finset.le_sup (f := f) (Finset.mem_range.mpr (by omega))).trans
      (Nat.le_add_left _ _)
  have hsbound (d : ℕ) (hd : d ≤ 2) : q d * c + Bstep d ^ d ≤ S := by
    exact (Finset.le_sup (f := fun d => q d * c + Bstep d ^ d)
      (Finset.mem_range.mpr (by omega))).trans (Nat.le_add_left _ _)
  refine ⟨C, K, F₀, S, hC, hK, hF₀, hS, ?_⟩
  intro A L t k n H hHeq hA ht hambient hscale hbase hwindow hgap hMscale hFscale hcard hlarge
  let r := S * H
  let R := ((4 * M) ^ 2 + 1) * r
  obtain ⟨B, hBA, hcost, hhalf, P, hPrank, hpos, hproper, hzero, hBP, hmodel, hratio, hdense⟩ :=
    hmodels A L t k n R hA ht hambient hscale hbase hwindow hcard
      (by simpa only [← hHeq] using hlarge)
  rw [← hHeq] at hproper hmodel
  have hHpos : 0 < H := by rw [hHeq]; positivity
  have hfold (j : ℕ) : 2 ^ (k + j) = 2 ^ j * 2 ^ k := by rw [pow_add]; ring
  have hH : H = 2 ^ n * 2 ^ k := hHeq.trans (hfold n)
  let T (j : ℕ) := (dyadicSumsetWithZero B (k + j)).card
  have hmodelT : (P.dilate (2 ^ n * 2 ^ k)).boxCard ≤ M * T n := by
    simpa only [← hH] using hmodel
  have hdenseT : ∀ E ⊆ B, B.card ≤ E.card + R → ∀ j ≤ n,
      2 * T j < 4 * ((2 ^ j * 2 ^ k) • insert 0 E).card := by
    intro E hEB hremove j hj
    simpa only [T, dyadicSumsetWithZero, hfold] using hdense E hEB hremove j hj
  obtain ⟨B₀, hB₀B, _hremove, _hfinite, _hindex, hstable, hdense₀⟩ :=
    exists_subgroupStable_multiscale_subset P B hzero
      ((Finset.subset_insert 0 B).trans hBP) (2 ^ k) n M r 2 T hM hPrank hpos
        (by simpa only [← hH] using hMscale) hmodelT hdenseT
  have hinitial : (2 * 2 ^ k) * (Nat.log 2 (T 0) + 1) ≤ 2 ^ n * 2 ^ k := by
    simpa only [T, Nat.add_zero] using multiscale_initial_budget_of_interval B L k n
      (hBA.trans hA) (by omega) hgap
  have hfscale : f P.rank ≤ H := (hfbound P.rank hPrank).trans hFscale
  have hblock : q P.rank * (c * H) + Bstep P.rank ^ P.rank ≤ r := by
    have hres : Bstep P.rank ^ P.rank ≤ Bstep P.rank ^ P.rank * H := by
      simpa using Nat.mul_le_mul_left (Bstep P.rank ^ P.rank) hHpos
    calc
      q P.rank * (c * H) + Bstep P.rank ^ P.rank ≤
          q P.rank * (c * H) + Bstep P.rank ^ P.rank * H := Nat.add_le_add_left hres _
      _ = (q P.rank * c + Bstep P.rank ^ P.rank) * H := by ring
      _ ≤ S * H := Nat.mul_le_mul_right H (hsbound P.rank hPrank)
  obtain ⟨W, hWB₀, hWcard, Q, hQrank, hQproper, hQhom, hQsum, _hQstep,
      hQside, hQcard, hQspan⟩ :=
    exists_homogeneous_GAP_in_subsetSums_multiscale P B₀ hzero
      (hB₀B.trans ((Finset.subset_insert 0 B).trans hBP)) (2 ^ k) K n M r T
      (by positivity) hM (by simpa only [← hH] using hproper) hpos hratio hinitial
      hmodelT hdense₀ hstable (by simpa only [← hH] using hfscale)
      (by simpa only [← hH] using hblock)
  have hWlinear : W.card ≤ S * H := by
    have hWcard' : W.card ≤ q P.rank * (c * H) + Bstep P.rank ^ P.rank := by
      simpa only [← hH] using hWcard
    exact hWcard'.trans hblock
  have hside : ∀ i : Fin Q.rank, ∀ j : Fin P.rank, i.val = j.val →
      Q.length i = H * P.length j / f P.rank := by
    simpa only [← hH] using hQside
  have hcardQ : Q.carrier.card = ∏ i : Fin P.rank, (H * P.length i / f P.rank + 1) := by
    simpa only [← hH] using hQcard
  have hPrankpos : 0 < P.rank := by
    have hcard' : 2 * ((6 * (L + 1) ^ 2 + 3) * R) + 2 ≤ A.card := by
      simpa only [mul_assoc] using hcard
    have hBcard : 2 ≤ B.card := by omega
    by_contra hn
    have hz : P.rank = 0 := by omega
    have hle := (Finset.card_le_card ((Finset.subset_insert 0 B).trans hBP)).trans
      P.card_carrier_le_box
    let : IsEmpty (Fin P.rank) := ⟨fun i => by have hi := i.isLt; omega⟩
    change B.card ≤ P.boxCard at hle
    simp [GeneralizedAP.boxCard] at hle
    omega
  refine ⟨W, hWB₀.trans (hB₀B.trans hBA), hWlinear, Q,
    by omega, hQrank.le.trans hPrank,
    hQproper, hQhom, hQsum, ?_, ?_, ?_⟩
  · intro i
    let j := Fin.cast hQrank i
    have hsidebound : H * P.length j ≤ 2 * f P.rank * Q.length i := by
      rw [hside i j rfl]
      exact standardized_side_lower (hpos j) (hf P.rank) hfscale
    have hbasebound : H ≤ H * P.length j := by
      simpa using Nat.mul_le_mul_left H (hpos j)
    exact hbasebound.trans (hsidebound.trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (hfbound P.rank hPrank))))
  · have hlower := standardized_card_lower_from_parent P Q A B H (f P.rank) hQrank
      (hf P.rank) hpos ((Finset.subset_insert 0 B).trans hBP) hhalf hcardQ
    exact hlower.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (hfbound P.rank hPrank)) Q.rank)))
  · apply hQspan.trans
    apply mul_le_mul_of_nonneg_right _ Q.coefficientSpan_nonneg
    exact_mod_cast Nat.mul_le_mul (hsbound P.rank hPrank)
      (Nat.mul_le_mul_left 2 (hfbound P.rank hPrank))

end Erdos587.CFP
