import ErdosProblems.Erdos964.AffineValueProgressions
import ErdosProblems.Erdos964.SemiprimeIntervals

/-!
# The coprime part of the affine second-sum count

The actual count of affine values in a finite set is expressed as a sum
of reduced-residue progression counts. Semiprime interval distribution
then bounds its error, retaining the exact affine endpoint translations.
-/

namespace Erdos964

open scoped BigOperators

def affineCoprimeValueCount (A B : Fin 3 → ℕ) (j : Fin 3) (N q : ℕ) (S : Finset ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter (fun n =>
    (q ∣ ∏ i, (A i * n + B i) ∧ q.Coprime (A j * n + B j)) ∧ A j * n + B j ∈ S)).card

theorem sum_indicator_residue_eq_count (S T : Finset ℕ) (hST : S ⊆ T) (q a : ℕ) :
    (∑ m ∈ T.filter (fun m => m ≡ a [MOD q]), if m ∈ S then (1 : ℝ) else 0) =
      (finiteResidueCount S q a : ℝ) := by
  have hfilter : (T.filter (fun m => m ≡ a [MOD q])).filter (fun m => m ∈ S) =
      S.filter (fun m => m ≡ a [MOD q]) := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨hST h.1, h.2⟩, h.1⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem affineCoprimeValueCount_eq_residue_sum (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q : ℕ) (hA : 0 < A j) (hq : 0 < q) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico (A j * N + B j) (A j * (2 * N) + B j)) :
    (affineCoprimeValueCount A B j N q S : ℝ) =
      ∑ c ∈ affineCoprimeProductRoots A B j q,
        (finiteResidueCount S (A j * q) (A j * c + B j) : ℝ) := by
  have hcount : (affineCoprimeValueCount A B j N q S : ℝ) =
      ∑ n ∈ (Finset.Ico N (2 * N)).filter
        (fun n => q ∣ ∏ i, (A i * n + B i) ∧ q.Coprime (A j * n + B j)),
        if A j * n + B j ∈ S then (1 : ℝ) else 0 := by
    rw [affineCoprimeValueCount, Finset.natCast_card_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    simp only [ite_and]
  rw [hcount, sum_affine_coprime_product_classes A B j N q hq]
  apply Finset.sum_congr rfl
  intro c _
  rw [sum_affine_interval_residue (A j) (B j) N q c hA
    (fun m => if m ∈ S then (1 : ℝ) else 0)]
  exact sum_indicator_residue_eq_count S _ hS _ _

theorem affineCoprimeValueCount_error_le (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q : ℕ) (hA : 0 < A j) (hq : 0 < q) (hBA : (B j).Coprime (A j))
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico (A j * N + B j) (A j * (2 * N) + B j))
    (E : ℝ) (hE : ∀ a, a.Coprime (A j * q) →
      |(finiteResidueCount S (A j * q) a : ℝ) -
        (finiteCoprimeCount S (A j * q) : ℝ) / (A j * q).totient| ≤ E) :
    |(affineCoprimeValueCount A B j N q S : ℝ) -
      (affineCoprimeProductRoots A B j q).card *
        ((finiteCoprimeCount S (A j * q) : ℝ) / (A j * q).totient)| ≤
      (affineCoprimeProductRoots A B j q).card * E := by
  rw [affineCoprimeValueCount_eq_residue_sum A B j N q hA hq S hS]
  have hid : (∑ c ∈ affineCoprimeProductRoots A B j q,
      (finiteResidueCount S (A j * q) (A j * c + B j) : ℝ)) -
      (affineCoprimeProductRoots A B j q).card *
        ((finiteCoprimeCount S (A j * q) : ℝ) / (A j * q).totient) =
      ∑ c ∈ affineCoprimeProductRoots A B j q,
        ((finiteResidueCount S (A j * q) (A j * c + B j) : ℝ) -
          (finiteCoprimeCount S (A j * q) : ℝ) / (A j * q).totient) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hid]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _c ∈ affineCoprimeProductRoots A B j q, E := by
      apply Finset.sum_le_sum
      intro c hc
      apply hE
      exact affine_value_residue_coprime (A j) (B j) q c hBA (Finset.mem_filter.mp hc).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem affineCoprimeValueCount_semiprime_error (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q : ℕ) (hA : 0 < A j) (hq : 0 < q) (hBA : (B j).Coprime (A j))
    (P : Finset ℕ) (L x y : ℕ) (hx : x ∈ Finset.Icc 1 (L ^ 2))
    (hy : y ∈ Finset.Icc 1 (L ^ 2)) (hxy : x ≤ y)
    (hS : semiprimeScaleInterval P L x y ⊆
      Finset.Ico (A j * N + B j) (A j * (2 * N) + B j)) :
    |(affineCoprimeValueCount A B j N q (semiprimeScaleInterval P L x y) : ℝ) -
      (affineCoprimeProductRoots A B j q).card *
        ((finiteCoprimeCount (semiprimeScaleInterval P L x y) (A j * q) : ℝ) /
          (A j * q).totient)| ≤
      (affineCoprimeProductRoots A B j q).card *
        (2 * semiprimeScaleCoprimeMaxDiscrepancy P L (A j * q)) := by
  apply affineCoprimeValueCount_error_le A B j N q hA hq hBA _ hS
  intro a ha
  exact semiprimeScaleInterval_discrepancy_le P L x y (A j * q) a hx hy hxy
    (Nat.mul_pos hA hq) ha

theorem affineCoprimeValueCount_semiprime_range_error (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q : ℕ) (hN : 2 ≤ N) (hA : 0 < A j) (hq : 0 < q) (hBA : (B j).Coprime (A j))
    (P : Finset ℕ) (L : ℕ) (hcap : A j * (2 * N) + B j ≤ L ^ 2 + 1) :
    let x := A j * N + B j - 1
    let y := A j * (2 * N) + B j - 1
    |(affineCoprimeValueCount A B j N q (semiprimeScaleInterval P L x y) : ℝ) -
      (affineCoprimeProductRoots A B j q).card *
        ((finiteCoprimeCount (semiprimeScaleInterval P L x y) (A j * q) : ℝ) /
          (A j * q).totient)| ≤
      (affineCoprimeProductRoots A B j q).card *
        (2 * semiprimeScaleCoprimeMaxDiscrepancy P L (A j * q)) := by
  let x := A j * N + B j - 1
  let y := A j * (2 * N) + B j - 1
  have hAN : 2 ≤ A j * N := by
    simpa only [one_mul] using Nat.mul_le_mul hA hN
  have hlo : 2 ≤ A j * N + B j := by omega
  have hlohi : A j * N + B j ≤ A j * (2 * N) + B j :=
    Nat.add_le_add_right (Nat.mul_le_mul_left (A j) (by omega)) (B j)
  have hxy : x ≤ y := Nat.sub_le_sub_right hlohi 1
  have hx : x ∈ Finset.Icc 1 (L ^ 2) := by
    apply Finset.mem_Icc.mpr
    dsimp only [x]
    omega
  have hy : y ∈ Finset.Icc 1 (L ^ 2) := by
    apply Finset.mem_Icc.mpr
    dsimp only [y]
    omega
  have hS : semiprimeScaleInterval P L x y ⊆
      Finset.Ico (A j * N + B j) (A j * (2 * N) + B j) := by
    intro m hm
    rw [semiprimeScaleInterval_eq_filter P L x y hxy] at hm
    have hm' := Finset.mem_filter.mp hm
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm'.1
    have hupper := (Finset.mem_filter.mp hz).2
    have hlower := hm'.2
    apply Finset.mem_Ico.mpr
    dsimp only [x, y] at hupper hlower
    omega
  exact affineCoprimeValueCount_semiprime_error A B j N q hA hq hBA P L x y hx hy hxy hS

end Erdos964
