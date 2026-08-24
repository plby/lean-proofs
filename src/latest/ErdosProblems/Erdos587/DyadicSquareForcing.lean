import ErdosProblems.Erdos587.StructuralTerminal
import ErdosProblems.Erdos587.NaturalSubsetBridge
import ErdosProblems.Erdos587.CubicBudgets
import ErdosProblems.Erdos587.DyadicScaleBudgets

/-! Square forcing from explicit dyadic numerical budgets alone. -/

namespace Erdos587

open CFP

lemma structural_removal_cost_le {l H U S : ℕ} (hl : 0 < l) (hH : 0 < H) :
    2 * (6 * l ^ 2 + 3) * (U * (S * H)) + 2 ≤
      (18 * U * S + 2) * l ^ 2 * H := by
  have hlsq : 1 ≤ l ^ 2 := one_le_pow₀ hl
  have hmain : 2 * (6 * l ^ 2 + 3) ≤ 18 * l ^ 2 := by omega
  have hlast : 2 ≤ 2 * l ^ 2 * H := by nlinarith only [hlsq, hH]
  calc
    _ ≤ (18 * l ^ 2) * (U * (S * H)) + 2 * l ^ 2 * H :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hmain) hlast
    _ = (18 * U * S + 2) * l ^ 2 * H := by ring

theorem exists_dyadic_finite_square_forcing :
    ∃ Z B : ℕ, 0 < Z ∧ 0 < B ∧ ∀ (t e : ℕ) (A : Finset ℕ),
      let H := 2 ^ (4 * t + e)
      let l := 12 * t + 1
      A ⊆ Finset.Icc 1 (2 ^ (12 * t)) → 0 < t → e ≤ t → Z ≤ 2 ^ t →
      4 * l ≤ 2 ^ t → Z * l ^ 2 * H < A.card →
      Z * (2 ^ (12 * t) + 1) < H ^ 3 →
      (Z : ℝ) * (2 : ℝ) ^ (12 * t) * (4 * (l : ℝ)) ^ (4 * B) ≤ (H : ℝ) ^ 3 →
      ¬ SquareSubsetSumFree A := by
  obtain ⟨C, K, F₀, S, hC, hK, hF₀, hS, hstructure⟩ :=
    exists_finite_homogeneous_structure 12
  let F := 2 * F₀
  let D := 8 * F ^ 2
  let M₀ := freimanTSizeFactor K 2
  let U := (4 * M₀) ^ 2 + 1
  let J := 2 * 2 ^ freimanRank K * M₀
  let R := 18 * U * S + 2
  let E := F ^ 4 * S + 16 * D ^ 2 * S + 1
  have hF : 0 < F := by dsimp [F]; omega
  have hD : 1 ≤ D := by
    have : 0 < D := by dsimp [D]; positivity
    omega
  have hE : 0 < E := by dsimp [E]; omega
  obtain ⟨B, hB, Tmin, hterminal⟩ := exists_structural_terminal ((S * F : ℕ) : ℝ)
    (by positivity)
  obtain ⟨Zmin, hZmin⟩ := exists_nat_gt ((F : ℝ) * Tmin)
  let Z := C + 4 * M₀ + F₀ + S + F + J + R + E + Zmin + 1
  have hZ : 0 < Z := by dsimp [Z]; omega
  have hZC : C ≤ Z := by dsimp [Z]; omega
  have hZM : 4 * M₀ ≤ Z := by dsimp [Z]; omega
  have hZF : F₀ ≤ Z := by dsimp [Z]; omega
  have hZS : S ≤ Z := by dsimp [Z]; omega
  have hZJ : J ≤ Z := by dsimp [Z]; omega
  have hZR : R ≤ Z := by dsimp [Z]; omega
  have hZE : E ≤ Z := by dsimp [Z]; omega
  have hZZmin : Zmin ≤ Z := by dsimp [Z]; omega
  refine ⟨Z, B, hZ, hB, ?_⟩
  intro t e A H l hA ht he hZscale hinitial hcard hlarge hcubic
  have hH : 0 < H := by dsimp [H]; positivity
  have hl : 0 < l := by dsimp [l]; omega
  have hsmallH : 2 ^ t ≤ H := Nat.pow_le_pow_right (by omega) (by omega)
  have hHlarge : Z ≤ H := hZscale.trans hsmallH
  have hHupper : H ≤ 2 ^ (12 * t) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcardH : H ≤ A.card := by
    have hfactor : 1 ≤ Z * l ^ 2 := by
      have : 0 < Z * l ^ 2 := by positivity
      omega
    have : H ≤ Z * l ^ 2 * H := by simpa using Nat.mul_le_mul_right H hfactor
    omega
  have hAI : natToIntFinset A ⊆ Finset.Icc 0 ((2 ^ (12 * t) : ℕ) : ℤ) :=
    natToIntFinset_subset_Icc hA
  have hcost : 2 * (6 * (12 * t + 1) ^ 2 + 3) *
      (((4 * freimanTSizeFactor K 2) ^ 2 + 1) * (S * H)) + 2 ≤
        (natToIntFinset A).card := by
    rw [card_natToIntFinset]
    calc
      _ ≤ R * l ^ 2 * H := structural_removal_cost_le hl hH
      _ ≤ Z * l ^ 2 * H := Nat.mul_le_mul_right H (Nat.mul_le_mul_right _ hZR)
      _ ≤ A.card := hcard.le
  have hrankbudget : 2 * 2 ^ freimanRank K * freimanTSizeFactor K 2 *
      (2 ^ (12 * t) + 1) < H ^ 2 * (natToIntFinset A).card := by
    rw [card_natToIntFinset]
    calc
      _ ≤ Z * (2 ^ (12 * t) + 1) := Nat.mul_le_mul_right _ hZJ
      _ < H ^ 3 := hlarge
      _ = H ^ 2 * H := by ring
      _ ≤ H ^ 2 * A.card := Nat.mul_le_mul_left _ hcardH
  obtain ⟨W, hWA, hWcard, Q, hQlo, hQhi, hQproper, hQhom, hQsum, hQside,
    hQcard, hQspan⟩ := hstructure (natToIntFinset A) (12 * t) t (3 * t) (t + e) H
      (by dsimp [H]; congr 1; omega) hAI ht (by omega) (hZC.trans hZscale)
      (by
        calc
          C * 2 ^ (t + t) ≤ 2 ^ t * 2 ^ (t + t) := Nat.mul_le_mul_right _ (hZC.trans hZscale)
          _ = 2 ^ (3 * t) := by rw [← pow_add]; congr 1; omega)
      (by omega)
      (hinitial.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      (hZM.trans hHlarge) (hZF.trans hHlarge) hcost hrankbudget
  have hQsub : Q.carrier ⊆ natToIntFinset A.subsetSum := by
    rw [← subsetSum_natToIntFinset]
    exact hQsum.trans (Finset.subsetSum_mono hWA)
  have hQscale : H ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card := by
    calc
      H ^ (Q.rank + 1) = H ^ Q.rank * H := by rw [pow_succ]
      _ ≤ H ^ Q.rank * A.card := Nat.mul_le_mul_left _ hcardH
      _ ≤ 2 * F ^ Q.rank * Q.carrier.card := by simpa only [card_natToIntFinset] using hQcard
  have hQupper := Q.upperEndpoint_le_interval_budget W (2 ^ (12 * t)) (S * H)
    (hWA.trans hAI) hWcard hQsum
  have hmin : (F : ℝ) * Tmin ≤ H := by
    exact hZmin.le.trans (by exact_mod_cast hZZmin.trans hHlarge)
  have hSupper : S ≤ 2 ^ (12 * t) := (hZS.trans hZscale).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hlog := log_subset_budget_le_dyadic hS hH hSupper hHupper
  have hLambda : (1 : ℝ) ≤ 4 * (l : ℝ) := by exact_mod_cast (show 1 ≤ 4 * l by omega)
  have hcubicE : (E : ℝ) * (2 : ℝ) ^ (12 * t) * (4 * (l : ℝ)) ^ (4 * B) ≤
      (H : ℝ) ^ 3 := by
    apply le_trans _ hcubic
    gcongr
  have hbudgets := terminal_budgets_of_cubic_surplus B
    (H := (H : ℝ)) (N := (2 : ℝ) ^ (12 * t)) (S := (S : ℝ))
    (F := (F : ℝ)) (D := (D : ℝ)) (E := (E : ℝ)) (Λ := 4 * (l : ℝ))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hD) hLambda
    (by exact_mod_cast (show F ^ 4 * S ≤ E by dsimp [E]; omega))
    (by exact_mod_cast (show 16 * D ^ 2 * S ≤ E by dsimp [E]; omega)) hcubicE
  apply hterminal A Q H F (S * H * 2 ^ (12 * t)) (4 * (l : ℝ))
    hQlo hQhi hQproper hQhom hQsub hH hF hQside hQscale hQupper
    (by exact_mod_cast hQspan) hLambda (by simpa only [l, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat] using hlog) hmin
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbudgets.1
  · simpa only [D, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbudgets.2.1
  · simpa only [D, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbudgets.2.2

end Erdos587
