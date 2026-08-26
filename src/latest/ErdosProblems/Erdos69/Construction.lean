import ErdosProblems.Erdos69.Parameters
import ErdosProblems.Erdos69.CollisionPrimes

/-! # The explicit CRT progression associated with a cancellation pattern -/

open scoped BigOperators

namespace Erdos69.Elementary

abbrev ConstructionShift (m : ℕ) :=
  ↥(retainedShifts m (dilationPrimeCutoff m) (retainedLength m))

def constructionDilation (m : ℕ) : PatternLabel m → ℕ :=
  patternDilation m (dilationPrimeCutoff m)

def constructionOffset (m : ℕ) : PatternLabel m → ℕ :=
  patternOffset m (dilationPrimeCutoff m)

def constructionProduct (m : ℕ) : ℕ := ∏ i, constructionDilation m i

def constructionCollisionProduct (m : ℕ) : ℕ :=
  collisionProduct (fun r : ConstructionShift m ↦ r.val)

def constructionModulus (m : ℕ) : ℕ :=
  augmentedModulus (constructionProduct m) (constructionCollisionProduct m)

def constructionMaxDilation (m : ℕ) : ℕ :=
  roughDilation (dilationPrimeCutoff m) (dilationPrimeCutoff m)

theorem constructionDilation_pos (m : ℕ) (i : PatternLabel m) :
    0 < constructionDilation m i := patternDilation_pos _ _ _

theorem constructionDilation_pairwise (m : ℕ) :
    Pairwise (fun i j : PatternLabel m ↦
      (constructionDilation m i).Coprime (constructionDilation m j)) :=
  patternDilation_pairwise m _ (digitRange_le_dilationPrimeCutoff m)

theorem constructionProduct_pos (m : ℕ) : 0 < constructionProduct m :=
  Finset.prod_pos (fun i _ ↦ constructionDilation_pos m i)

theorem constructionCollisionProduct_pos (m : ℕ) : 0 < constructionCollisionProduct m :=
  collisionProduct_pos _ Subtype.val_injective

theorem constructionModulus_pos (m : ℕ) : 0 < constructionModulus m :=
  augmentedModulus_pos (constructionProduct_pos m)

theorem constructionDilation_dvd_modulus (m : ℕ) (i : PatternLabel m) :
    constructionDilation m i ∣ constructionModulus m :=
  (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans
    (dvd_augmentedModulus (constructionProduct m) (constructionCollisionProduct m))

theorem construction_quotient_coprime (m : ℕ) (i : PatternLabel m) :
    (constructionModulus m / constructionDilation m i).Coprime (constructionDilation m i) := by
  classical
  exact coprime_augmentedModulus_quotient (constructionDilation m)
    (constructionDilation_pos m) (constructionDilation_pairwise m) _ i

theorem constructionDilation_le_max (m : ℕ) (i : PatternLabel m) :
    constructionDilation m i ≤ constructionMaxDilation m := by
  have hd := (patternDigit_lt m i).le.trans (digitRange_le_dilationPrimeCutoff m)
  unfold constructionDilation patternDilation constructionMaxDilation roughDilation
  gcongr

theorem constructionOffset_le (m : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ 6 * m * constructionMaxDilation m := by
  have hm := patternIntercept_le m i
  have hD := constructionDilation_le_max m i
  have hbase : constructionOffset m i ≤ 6 * m * constructionDilation m i := by
    unfold constructionOffset patternOffset constructionDilation patternDilation roughDilation
    nlinarith
  exact hbase.trans (Nat.mul_le_mul_left _ hD)

noncomputable def constructionResidue (m : ℕ) : ℕ :=
  (Nat.chineseRemainderOfFinset (constructionOffset m) (constructionDilation m) Finset.univ
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun i _ j _ hij ↦ constructionDilation_pairwise m hij)).val

theorem constructionResidue_modEq (m : ℕ) (i : PatternLabel m) :
    constructionResidue m ≡ constructionOffset m i [MOD constructionDilation m i] :=
  (Nat.chineseRemainderOfFinset (constructionOffset m) (constructionDilation m) Finset.univ
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun i _ j _ hij ↦ constructionDilation_pairwise m hij)).property i (Finset.mem_univ i)

theorem constructionResidue_lt_product (m : ℕ) :
    constructionResidue m < constructionProduct m :=
  Nat.chineseRemainderOfFinset_lt_prod (constructionOffset m) (constructionDilation m)
    (fun i _ ↦ (constructionDilation_pos m i).ne')
    (fun i _ j _ hij ↦ constructionDilation_pairwise m hij)

noncomputable def constructionBase (m : ℕ) : ℕ :=
  constructionResidue m + constructionModulus m * (6 * m * constructionMaxDilation m + 1)

theorem constructionOffset_le_base (m : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ constructionBase m := by
  have hQ := constructionModulus_pos m
  have hb := constructionOffset_le m i
  unfold constructionBase
  nlinarith

theorem constructionBase_modEq (m : ℕ) (i : PatternLabel m) :
    constructionBase m ≡ constructionOffset m i [MOD constructionDilation m i] := by
  have hQ := constructionDilation_dvd_modulus m i
  have hmul : constructionDilation m i ∣
      constructionModulus m * (6 * m * constructionMaxDilation m + 1) := dvd_mul_of_dvd_left hQ _
  have h := (constructionResidue_modEq m i).add (Nat.modEq_zero_iff_dvd.mpr hmul)
  simpa only [constructionBase, Nat.add_zero] using h

theorem construction_shifts_distinct_mod_prime (m p : ℕ) (hp : p.Prime)
    (hpQ : ¬p ∣ constructionModulus m) :
    ∀ r s : ConstructionShift m, r.val ≡ s.val [MOD p] → r = s :=
  distinct_residues_outside_augmentedModulus _ Subtype.val_injective _ p hp hpQ

noncomputable def constructionCoefficient (m : ℕ) (q : ℝ) (r : ConstructionShift m) : ℝ :=
  shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r.val

def constructionFirstShift (m : ℕ) : ConstructionShift m :=
  ⟨(primorial (dilationPrimeCutoff m) + 1) * (6 * m + 1),
    minimal_mem_retainedShifts m _ _ (retainedLength_pos m)⟩

theorem constructionCoefficient_zero_sum {m : ℕ} (hm : 0 < m) (q : ℝ) :
    (∑ r : ConstructionShift m, constructionCoefficient m q r) = 0 := by
  rw [show (∑ r : ConstructionShift m, constructionCoefficient m q r) =
      ∑ r ∈ retainedShifts m (dilationPrimeCutoff m) (retainedLength m),
        shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r from
      Finset.sum_coe_sort _ _]
  exact sum_shiftCoefficient_zero hm _ _ q

theorem constructionCoefficient_mass_le (m : ℕ) (q : ℝ) :
    (∑ r : ConstructionShift m, |constructionCoefficient m q r|) ≤
      |q| * (9 / 16 : ℝ) ^ m := by
  change (∑ r : ConstructionShift m,
    |shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r.val|) ≤ _
  rw [Finset.sum_coe_sort (retainedShifts m (dilationPrimeCutoff m) (retainedLength m))
    (fun r ↦ |shiftCoefficient m (dilationPrimeCutoff m) (retainedLength m) q r|)]
  exact shiftCoefficient_mass_le m _ _ q

theorem constructionCoefficient_first (m : ℕ) (q : ℝ) :
    constructionCoefficient m q (constructionFirstShift m) = q / 2 ^ (6 * m + 1) :=
  shiftCoefficient_minimal m _ _ (retainedLength_pos m) q

theorem constructionShift_card_le (m : ℕ) :
    Fintype.card (ConstructionShift m) ≤ patternSize m * retainedLength m := by
  simpa only [Fintype.card_coe, patternSize] using
    retainedShifts_card_le m (dilationPrimeCutoff m) (retainedLength m)

noncomputable def constructionPoint (m t : ℕ) : ℕ :=
  constructionBase m + constructionModulus m * t

theorem constructionPoint_pos (m t : ℕ) : 0 < constructionPoint m t := by
  have hQ := constructionModulus_pos m
  unfold constructionPoint constructionBase
  positivity

theorem constructionOffset_le_point (m t : ℕ) (i : PatternLabel m) :
    constructionOffset m i ≤ constructionPoint m t :=
  (constructionOffset_le_base m i).trans (Nat.le_add_right _ _)

theorem constructionPoint_modEq (m t : ℕ) (i : PatternLabel m) :
    constructionPoint m t ≡ constructionOffset m i [MOD constructionDilation m i] := by
  have h := (constructionBase_modEq m i).add
    (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (constructionDilation_dvd_modulus m i) t))
  simpa only [constructionPoint, Nat.add_zero] using h

theorem construction_quotient_affine (m t : ℕ) (i : PatternLabel m) :
    (constructionPoint m t - constructionOffset m i) / constructionDilation m i =
      (constructionBase m - constructionOffset m i) / constructionDilation m i +
        (constructionModulus m / constructionDilation m i) * t := by
  have hdiv := constructionDilation_dvd_modulus m i
  have hmul : constructionDilation m i * (constructionModulus m / constructionDilation m i) =
      constructionModulus m := Nat.mul_div_cancel' hdiv
  have heq : constructionPoint m t - constructionOffset m i =
      (constructionBase m - constructionOffset m i) +
        constructionDilation m i * ((constructionModulus m / constructionDilation m i) * t) := by
    rw [← Nat.mul_assoc, hmul]
    have hb := constructionOffset_le_base m i
    unfold constructionPoint
    omega
  rw [heq, Nat.add_mul_div_left _ _ (constructionDilation_pos m i)]

end Erdos69.Elementary
