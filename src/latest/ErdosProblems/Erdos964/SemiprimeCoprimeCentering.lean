import ErdosProblems.Erdos964.SemiprimeWeightedMultiples
import BoundedGaps.Maynard.MaynardCoprimeHarmonic

/-!
# Changing to coprime-cardinality centering

Averaging the progression errors over all reduced residue classes bounds
the change of center by the same maximum error. Thus the paper's coprime
centering costs a factor of two, with no new analytic estimate required.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

def finiteCoprimeCount (S : Finset ℕ) (q : ℕ) : ℕ :=
  (S.filter (fun n => n.Coprime q)).card

theorem sum_finiteResidueCount_coprime (S : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    (∑ a ∈ coprimeResidues q, finiteResidueCount S q a) = finiteCoprimeCount S q := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter S (coprimeResidues q) (fun n => n % q)
  have hfilter : S.filter (fun n => n % q ∈ coprimeResidues q) =
      S.filter (fun n => n.Coprime q) := by
    apply Finset.filter_congr
    intro n _
    simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range, Nat.mod_lt n hq,
      true_and]
    change Nat.gcd (n % q) q = 1 ↔ Nat.gcd n q = 1
    rw [(Nat.mod_modEq n q).gcd_eq]
  rw [hfilter] at hfiber
  unfold finiteCoprimeCount
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro a ha
  have halt := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  unfold finiteResidueCount
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Nat.ModEq, Nat.mod_eq_of_lt halt]

theorem finiteResidueCount_coprime_centered_le_two (S : Finset ℕ) (q a : ℕ) (E : ℝ)
    (hq : 0 < q) (ha : a ∈ coprimeResidues q)
    (hE : ∀ b ∈ coprimeResidues q,
      |(finiteResidueCount S q b : ℝ) - (S.card : ℝ) / q.totient| ≤ E) :
    |(finiteResidueCount S q a : ℝ) - (finiteCoprimeCount S q : ℝ) / q.totient| ≤ 2 * E := by
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hsum : (∑ b ∈ coprimeResidues q, (finiteResidueCount S q b : ℝ)) =
      (finiteCoprimeCount S q : ℝ) := by
    exact_mod_cast sum_finiteResidueCount_coprime S q hq
  have hid : (∑ b ∈ coprimeResidues q,
      ((finiteResidueCount S q b : ℝ) - (S.card : ℝ) / q.totient)) =
      (finiteCoprimeCount S q : ℝ) - S.card := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, card_coprimeResidues]
    field_simp
  have hcenter : |(finiteCoprimeCount S q : ℝ) - S.card| ≤ (q.totient : ℝ) * E := by
    rw [← hid]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _b ∈ coprimeResidues q, E := Finset.sum_le_sum hE
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_coprimeResidues]
  have hchange : |(S.card : ℝ) / q.totient - (finiteCoprimeCount S q : ℝ) / q.totient| ≤ E := by
    rw [abs_sub_comm, ← sub_div, abs_div, abs_of_pos hphi]
    exact (div_le_iff₀ hphi).mpr (by simpa only [mul_comm E] using hcenter)
  exact (abs_sub_le _ ((S.card : ℝ) / q.totient) _).trans
    ((add_le_add (hE a ha) hchange).trans_eq (by ring))

theorem semiprimeScale_discrepancy_le_max (P : Finset ℕ) (L q x a : ℕ)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hq : 0 < q) (ha : a ∈ coprimeResidues q) :
    |(finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
      ((semiprimesAtScale P L x).card : ℝ) / q.totient| ≤
        semiprimeScaleMaxDiscrepancy P L q := by
  have hL : 1 ≤ L ^ 2 := (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
  rw [semiprimeScaleMaxDiscrepancy, dif_pos hL, dif_pos hq]
  exact Finset.le_sup'
    (fun z : ℕ × ℕ => |(finiteResidueCount (semiprimesAtScale P L z.1) q z.2 : ℝ) -
      ((semiprimesAtScale P L z.1).card : ℝ) / q.totient|)
    (show (x, a) ∈ (Finset.Icc 1 (L ^ 2)) ×ˢ coprimeResidues q from
      Finset.mem_product.mpr ⟨hx, ha⟩)

noncomputable def semiprimeScaleCoprimeMaxDiscrepancy (P : Finset ℕ) (L q : ℕ) : ℝ :=
  if hL : 1 ≤ L ^ 2 then
    if hq : 0 < q then
      ((Finset.Icc 1 (L ^ 2)) ×ˢ coprimeResidues q).sup'
        ((Finset.nonempty_Icc.mpr hL).product (coprimeResidues_nonempty hq))
        (fun z => |(finiteResidueCount (semiprimesAtScale P L z.1) q z.2 : ℝ) -
          (finiteCoprimeCount (semiprimesAtScale P L z.1) q : ℝ) / q.totient|)
    else 0
  else 0

theorem semiprimeScale_coprime_discrepancy_le_max (P : Finset ℕ) (L q x a : ℕ)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hq : 0 < q) (ha : a.Coprime q) :
    |(finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
      (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ) / q.totient| ≤
        semiprimeScaleCoprimeMaxDiscrepancy P L q := by
  have hL : 1 ≤ L ^ 2 := (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
  have hcop : (a % q).Coprime q := by
    change Nat.gcd (a % q) q = 1
    rw [(Nat.mod_modEq a q).gcd_eq]
    exact ha
  have haq : a % q ∈ coprimeResidues q :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hq), hcop⟩
  have h : |(finiteResidueCount (semiprimesAtScale P L x) q (a % q) : ℝ) -
      (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ) / q.totient| ≤
        semiprimeScaleCoprimeMaxDiscrepancy P L q := by
    rw [semiprimeScaleCoprimeMaxDiscrepancy, dif_pos hL, dif_pos hq]
    exact Finset.le_sup'
      (fun z : ℕ × ℕ => |(finiteResidueCount (semiprimesAtScale P L z.1) q z.2 : ℝ) -
        (finiteCoprimeCount (semiprimesAtScale P L z.1) q : ℝ) / q.totient|)
      (show (x, a % q) ∈ (Finset.Icc 1 (L ^ 2)) ×ˢ coprimeResidues q from
        Finset.mem_product.mpr ⟨hx, haq⟩)
  have hcount : finiteResidueCount (semiprimesAtScale P L x) q (a % q) =
      finiteResidueCount (semiprimesAtScale P L x) q a := by
    unfold finiteResidueCount
    congr 1
    apply Finset.filter_congr
    intro n _
    simp only [Nat.ModEq, Nat.mod_mod]
  rw [hcount] at h
  exact h

theorem semiprimeScale_coprime_interval_discrepancy_le (P : Finset ℕ) (L q x y a : ℕ)
    (hx : x ∈ Finset.Icc 1 (L ^ 2)) (hy : y ∈ Finset.Icc 1 (L ^ 2))
    (hq : 0 < q) (ha : a.Coprime q) :
    |((finiteResidueCount (semiprimesAtScale P L y) q a : ℝ) -
        (finiteResidueCount (semiprimesAtScale P L x) q a : ℝ)) -
      ((finiteCoprimeCount (semiprimesAtScale P L y) q : ℝ) -
        (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ)) / q.totient| ≤
        2 * semiprimeScaleCoprimeMaxDiscrepancy P L q := by
  have hdy := semiprimeScale_coprime_discrepancy_le_max P L q y a hy hq ha
  have hdx := semiprimeScale_coprime_discrepancy_le_max P L q x a hx hq ha
  have htri := abs_sub_le
    ((finiteResidueCount (semiprimesAtScale P L y) q a : ℝ) -
      (finiteCoprimeCount (semiprimesAtScale P L y) q : ℝ) / q.totient) 0
    ((finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
      (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ) / q.totient)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have hid : ((finiteResidueCount (semiprimesAtScale P L y) q a : ℝ) -
        (finiteResidueCount (semiprimesAtScale P L x) q a : ℝ)) -
      ((finiteCoprimeCount (semiprimesAtScale P L y) q : ℝ) -
        (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ)) / q.totient =
      ((finiteResidueCount (semiprimesAtScale P L y) q a : ℝ) -
        (finiteCoprimeCount (semiprimesAtScale P L y) q : ℝ) / q.totient) -
      ((finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
        (finiteCoprimeCount (semiprimesAtScale P L x) q : ℝ) / q.totient) := by ring
  rw [hid]
  exact htri.trans ((add_le_add hdy hdx).trans_eq (by ring))

theorem semiprimeScaleCoprimeMaxDiscrepancy_nonneg (P : Finset ℕ) (L q : ℕ) :
    0 ≤ semiprimeScaleCoprimeMaxDiscrepancy P L q := by
  by_cases hL : 1 ≤ L ^ 2
  · by_cases hq : 0 < q
    · exact (abs_nonneg _).trans (semiprimeScale_coprime_discrepancy_le_max P L q 1 1
        (Finset.mem_Icc.mpr ⟨le_refl _, hL⟩) hq (Nat.coprime_one_left q))
    · simp only [semiprimeScaleCoprimeMaxDiscrepancy, dif_pos hL, dif_neg hq, le_refl]
  · simp only [semiprimeScaleCoprimeMaxDiscrepancy, dif_neg hL, le_refl]

theorem semiprimeScaleCoprimeMaxDiscrepancy_le_two (P : Finset ℕ) (L q : ℕ) :
    semiprimeScaleCoprimeMaxDiscrepancy P L q ≤ 2 * semiprimeScaleMaxDiscrepancy P L q := by
  unfold semiprimeScaleCoprimeMaxDiscrepancy
  split_ifs with hL hq
  · apply Finset.sup'_le
    intro z hz
    have hz' := Finset.mem_product.mp hz
    apply finiteResidueCount_coprime_centered_le_two _ q z.2 _ hq hz'.2
    intro b hb
    exact semiprimeScale_discrepancy_le_max P L q z.1 b hz'.1 hq hb
  · exact mul_nonneg (by norm_num) (semiprimeScaleMaxDiscrepancy_nonneg P L q)
  · exact mul_nonneg (by norm_num) (semiprimeScaleMaxDiscrepancy_nonneg P L q)

theorem exists_semiprimesAtScale_coprime_weighted_multiples_logSaving (a d m : ℕ) (hm : 0 < m)
    (η θ : ℝ) (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ S : Finset ℕ, S ⊆ Finset.Ioc 0 (modulusCutoff θ L) →
        (∀ q ∈ S, Squarefree q) →
      (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleCoprimeMaxDiscrepancy P L (m * q)) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_semiprimesAtScale_weighted_multiples_logSaving a d m hm η θ hη hθ hθ1
  refine ⟨2 * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower S hS hsq
  calc
    _ ≤ ∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * (2 * semiprimeScaleMaxDiscrepancy P L (m * q)) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (semiprimeScaleCoprimeMaxDiscrepancy_le_two P L (m * q))
        (Nat.cast_nonneg _)
    _ = 2 * ∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleMaxDiscrepancy P L (m * q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ 2 * (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a) :=
      mul_le_mul_of_nonneg_left (hbound L hL P hP hPL hPlower S hS hsq) (by norm_num)
    _ = _ := by ring

end Erdos964
