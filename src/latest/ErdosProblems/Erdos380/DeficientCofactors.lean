import ErdosProblems.Erdos380.ScaleDivision
import ErdosProblems.Erdos380.TopPrimeDecomposition
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-! # Counting anchors with too few large cofactor factors

The removed factors are allowed to be arbitrary positive integers. This
upper count only costs a fixed power of a harmonic sum.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos380

noncomputable def positiveFactorTuples (Y k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Icc 1 Y)

lemma mem_positiveFactorTuples {Y k : ℕ} {f : Fin k → ℕ} :
    f ∈ positiveFactorTuples Y k ↔ ∀ i, 1 ≤ f i ∧ f i ≤ Y := by
  simp [positiveFactorTuples, Fintype.mem_piFinset]

lemma positiveFactorTuples_prod_pos {Y k : ℕ} {f : Fin k → ℕ}
    (hf : f ∈ positiveFactorTuples Y k) : 0 < ∏ i, f i := by
  exact Finset.prod_pos (fun i _ => lt_of_lt_of_le Nat.zero_lt_one ((mem_positiveFactorTuples.mp hf i).1))

lemma positiveFactorTuples_prod_le {Y k : ℕ} {f : Fin k → ℕ}
    (hf : f ∈ positiveFactorTuples Y k) : (∏ i, f i) ≤ Y ^ k := by
  calc
    (∏ i, f i) ≤ ∏ _ : Fin k, Y := Finset.prod_le_prod' (fun i _ => (mem_positiveFactorTuples.mp hf i).2)
    _ = Y ^ k := by simp

noncomputable def cofactorDeficientSingletons (N Q Y k : ℕ) : Finset ℕ :=
  (singletonBadUpTo N).filter fun n => Q ≤ largestPrimeFactor n ∧ largestPrimeFactor n ≤ Y ∧
    topPrime (singletonCofactor n) k < Q

lemma cofactorDeficientSingletons_card_le_sum (N Q Y k : ℕ) :
    (cofactorDeficientSingletons N Q Y k).card ≤
      ∑ p ∈ Finset.Icc Q Y, ∑ f ∈ positiveFactorTuples Y k,
        smoothCount (N / (p ^ 2 * ∏ i, f i)) Q := by
  classical
  let S := (Finset.Icc Q Y).biUnion fun p => (positiveFactorTuples Y k).biUnion fun f =>
    (Nat.smoothNumbersUpTo (N / (p ^ 2 * ∏ i, f i)) (Q + 1)).image
      (fun b => p ^ 2 * ((∏ i, f i) * b))
  have hsub : cofactorDeficientSingletons N Q Y k ⊆ S := by
    intro n hn
    obtain ⟨hn, hQp, hpY, hthin⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN, hbad⟩ := mem_singletonBadUpTo.mp hn
    let f := (canonicalPrimeRecord n k).2.1
    let b := (canonicalPrimeRecord n k).2.2
    have hf : f ∈ positiveFactorTuples Y k := by
      apply mem_positiveFactorTuples.mpr
      intro i
      exact ⟨one_le_largestPrimeFactor _, (hbad.canonicalPrimeRecord_tuple_le i).trans hpY⟩
    have hb : 0 < b := hbad.canonicalPrimeRecord_cofactor_pos k
    have hp : (largestPrimeFactor n).Prime := largestPrimeFactor_prime (by have := hbad.1; omega)
    have hval : largestPrimeFactor n ^ 2 * ((∏ i, f i) * b) = n := hbad.canonicalPrimeRecord_value k
    have hbQ : largestPrimeFactor b ≤ Q := hthin.le
    have hQ1 : 1 ≤ Q := (one_le_largestPrimeFactor b).trans hbQ
    have hdpos : 0 < largestPrimeFactor n ^ 2 * ∏ i, f i :=
      mul_pos (pow_pos hp.pos 2) (positiveFactorTuples_prod_pos hf)
    have hbN : b ≤ N / (largestPrimeFactor n ^ 2 * ∏ i, f i) := by
      apply (Nat.le_div_iff_mul_le hdpos).mpr
      calc
        b * (largestPrimeFactor n ^ 2 * ∏ i, f i) = largestPrimeFactor n ^ 2 * ((∏ i, f i) * b) := by ring
        _ = n := hval
        _ ≤ N := hnN
    exact Finset.mem_biUnion.mpr ⟨largestPrimeFactor n, Finset.mem_Icc.mpr ⟨hQp, hpY⟩,
      Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨b,
        Nat.mem_smoothNumbersUpTo.mpr ⟨hbN,
          (mem_smoothNumbers_iff_largestPrimeFactor hQ1).mpr ⟨hb.ne', hbQ⟩⟩, hval⟩⟩⟩
  calc
    _ ≤ S.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.Icc Q Y, ((positiveFactorTuples Y k).biUnion fun f =>
        (Nat.smoothNumbersUpTo (N / (p ^ 2 * ∏ i, f i)) (Q + 1)).image
          (fun b => p ^ 2 * ((∏ i, f i) * b))).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun f _ => Finset.card_image_le))

lemma sum_positiveFactorTuples_inv (Y k : ℕ) :
    (∑ f ∈ positiveFactorTuples Y k, ∏ i, (f i : ℝ)⁻¹) =
      (∑ a ∈ Finset.Icc 1 Y, (a : ℝ)⁻¹) ^ k :=
  (Finset.sum_pow' (Finset.Icc 1 Y) (fun a => (a : ℝ)⁻¹) k).symm

lemma cofactorDeficientSingletons_card_bound {N Q Y k : ℕ} {F : ℝ}
    (hQ : 1 ≤ Q) (hY : 1 ≤ Y) (hF : 0 < F)
    (hbound : ∀ p ∈ Finset.Icc Q Y, ∀ f ∈ positiveFactorTuples Y k,
      (smoothCount (N / (p ^ 2 * ∏ i, f i)) Q : ℝ) ≤
        (N : ℝ) / (p ^ 2 * ∏ i, f i : ℕ) / F) :
    ((cofactorDeficientSingletons N Q Y k).card : ℝ) ≤
      2 * N / Q / F * (1 + Real.log Y) ^ k := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hsumQ : (∑ p ∈ Finset.Icc Q Y, ((p : ℝ) ^ 2)⁻¹) ≤ 2 / (Q : ℝ) := by
    have hset : Finset.Icc Q Y = Finset.Ioo (Q - 1) (Y + 1) := by
      ext p
      simp only [Finset.mem_Icc, Finset.mem_Ioo]
      omega
    rw [hset]
    have h := sum_Ioo_inv_sq_le (α := ℝ) (Q - 1) (Y + 1)
    have heq : ((Q - 1 : ℕ) : ℝ) + 1 = Q := by exact_mod_cast (by omega : Q - 1 + 1 = Q)
    rwa [heq] at h
  have hsumY : (∑ a ∈ Finset.Icc 1 Y, (a : ℝ)⁻¹) ≤ 1 + Real.log Y := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log Y
  have hsumf : (∑ f ∈ positiveFactorTuples Y k, ∏ i, (f i : ℝ)⁻¹) ≤ (1 + Real.log Y) ^ k := by
    rw [sum_positiveFactorTuples_inv]
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => by positivity)) hsumY k
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  calc
    ((cofactorDeficientSingletons N Q Y k).card : ℝ) ≤
        ∑ p ∈ Finset.Icc Q Y, ∑ f ∈ positiveFactorTuples Y k,
          (smoothCount (N / (p ^ 2 * ∏ i, f i)) Q : ℝ) := by
      exact_mod_cast cofactorDeficientSingletons_card_le_sum N Q Y k
    _ ≤ ∑ p ∈ Finset.Icc Q Y, ∑ f ∈ positiveFactorTuples Y k,
        (N : ℝ) / (p ^ 2 * ∏ i, f i : ℕ) / F := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.sum_le_sum (hbound p hp)
    _ = ((N : ℝ) / F) * (∑ p ∈ Finset.Icc Q Y, ((p : ℝ) ^ 2)⁻¹) *
        (∑ f ∈ positiveFactorTuples Y k, ∏ i, (f i : ℝ)⁻¹) := by
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, div_eq_mul_inv, mul_inv_rev,
        Finset.prod_inv_distrib]
      ring
    _ ≤ ((N : ℝ) / F) * (2 / Q) * (1 + Real.log Y) ^ k := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsumQ (by positivity)
      · exact hsumf
      · exact Finset.sum_nonneg (fun f _ => Finset.prod_nonneg (fun i _ => by positivity))
      · positivity
    _ = _ := by ring

end Erdos380
