import ErdosProblems.Erdos964.SemiprimeScaleDistribution

/-!
# Bombieri--Vinogradov for separated semiprime factors

For any prime support `P` between `L^η` and `L`, count products `p r ≤ x`
with `p ∈ P` and `r > L` prime. The sum over moduli up to `L^(2θ)`,
`θ < 1/2`, of the separate maxima over endpoints and reduced residues has
arbitrary logarithmic saving. All constants and thresholds are proved.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def semiprimeScaleMaxDiscrepancy (P : Finset ℕ) (L q : ℕ) : ℝ :=
  if hL : 1 ≤ L ^ 2 then
    if hq : 0 < q then
      ((Finset.Icc 1 (L ^ 2)) ×ˢ coprimeResidues q).sup'
        ((Finset.nonempty_Icc.mpr hL).product (coprimeResidues_nonempty hq))
        (fun z => |(finiteResidueCount (semiprimesAtScale P L z.1) q z.2 : ℝ) -
          ((semiprimesAtScale P L z.1).card : ℝ) / q.totient|)
    else 0
  else 0

theorem semiprimeScaleMaxDiscrepancy_attained (P : Finset ℕ) {L q : ℕ}
    (hL : 0 < L) (hq : 0 < q) :
    ∃ x a : ℕ, x ∈ Finset.Icc 1 (L ^ 2) ∧ a ∈ coprimeResidues q ∧
      semiprimeScaleMaxDiscrepancy P L q =
        |(finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
          ((semiprimesAtScale P L x).card : ℝ) / q.totient| := by
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hne := (Finset.nonempty_Icc.mpr hLsq).product (coprimeResidues_nonempty hq)
  obtain ⟨z, hz, hmax⟩ := Finset.exists_mem_eq_sup' hne
    (fun z => |(finiteResidueCount (semiprimesAtScale P L z.1) q z.2 : ℝ) -
      ((semiprimesAtScale P L z.1).card : ℝ) / q.totient|)
  refine ⟨z.1, z.2, (Finset.mem_product.mp hz).1, (Finset.mem_product.mp hz).2, ?_⟩
  simpa only [semiprimeScaleMaxDiscrepancy, dif_pos hLsq, dif_pos hq] using hmax

theorem semiprimeScaleMaxDiscrepancy_nonneg (P : Finset ℕ) (L q : ℕ) :
    0 ≤ semiprimeScaleMaxDiscrepancy P L q := by
  by_cases hL : 0 < L
  · by_cases hq : 0 < q
    · obtain ⟨x, a, _, _, hmax⟩ := semiprimeScaleMaxDiscrepancy_attained P hL hq
      rw [hmax]
      exact abs_nonneg _
    · simp only [semiprimeScaleMaxDiscrepancy, dif_neg hq]
      split_ifs <;> exact le_rfl
  · have hz : L = 0 := Nat.eq_zero_of_not_pos hL
    simp [semiprimeScaleMaxDiscrepancy, hz]

theorem exists_semiprimesAtScale_max_logSaving (a : ℕ) (η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      (∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L), semiprimeScaleMaxDiscrepancy P L q) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  classical
  obtain ⟨C, hC, L₀, hL₀, hfamily⟩ := exists_semiprimesAtScale_logSaving a η θ hη hθ hθ1
  refine ⟨C, hC, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower
  have hLpos : 0 < L := by have := hL₀.trans hL; omega
  have harg (q : ℕ) : ∃ x a : ℕ, 0 < q →
      x ∈ Finset.Icc 1 (L ^ 2) ∧ a ∈ coprimeResidues q ∧
      semiprimeScaleMaxDiscrepancy P L q =
        |(finiteResidueCount (semiprimesAtScale P L x) q a : ℝ) -
          ((semiprimesAtScale P L x).card : ℝ) / q.totient| := by
    by_cases hq : 0 < q
    · obtain ⟨x, a, hx, ha, hmax⟩ := semiprimeScaleMaxDiscrepancy_attained P hLpos hq
      exact ⟨x, a, fun _ => ⟨hx, ha, hmax⟩⟩
    · exact ⟨1, 0, fun h => False.elim (hq h)⟩
  choose X r hchosen using harg
  have hX (q : ℕ) (hq : 0 < q) (_hqT : q ≤ modulusCutoff θ L) :
      X q ∈ Finset.Icc 1 (L ^ 2) := (hchosen q hq).1
  have hr (q : ℕ) (hq : 0 < q) (_hqT : q ≤ modulusCutoff θ L) : (r q).Coprime q :=
    (Finset.mem_filter.mp (hchosen q hq).2.1).2
  calc
    _ = ∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L),
        |(finiteResidueCount (semiprimesAtScale P L (X q)) q (r q) : ℝ) -
          ((semiprimesAtScale P L (X q)).card : ℝ) / q.totient| := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (hchosen q (Finset.mem_Ioc.mp hq).1).2.2
    _ ≤ _ := hfamily L hL P hP hPL hPlower X hX r hr

/-- Unconditional level of distribution below one half for semiprimes
whose two prime factors lie on opposite sides of `L`, with the smaller
factor above a fixed positive power of `L`. The endpoint and residue
maxima are inside the sum over moduli. -/
theorem semiprime_bombieri_vinogradov (η θ A : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      (∑ q ∈ Finset.Ioc 0 (modulusCutoff (2 * θ) L), semiprimeScaleMaxDiscrepancy P L q) ≤
        C * (L : ℝ) ^ 2 / Real.rpow (Real.log (L : ℝ)) A := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_semiprimesAtScale_max_logSaving ⌈A⌉₊ η (2 * θ) hη (by positivity) (by linarith)
  refine ⟨C, hC, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower
  have hlogOne : 1 ≤ Real.log (L : ℝ) := one_le_log_natCast (by have := hL₀.trans hL; omega)
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hden : Real.rpow (Real.log (L : ℝ)) A ≤ (Real.log (L : ℝ)) ^ ⌈A⌉₊ := by
    calc
      _ ≤ Real.rpow (Real.log (L : ℝ)) (⌈A⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne (Nat.le_ceil A)
      _ = _ := Real.rpow_natCast _ _
  exact (hbound L hL P hP hPL hPlower).trans
    (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlogpos A) hden)

end Erdos964
