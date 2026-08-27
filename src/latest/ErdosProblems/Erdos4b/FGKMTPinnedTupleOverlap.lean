/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedTupleGeometry

/-! # The normalized same-prime contribution to pinned tuple moments -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem product_label_overlap_mass_le {α β : Type*} (I : Finset α) (P : Finset β)
    (b : α × β → ℝ) (N : α × β → Finset ℤ)
    (hb : ∀ j ∈ I ×ˢ P, 0 ≤ b j) (hsum : ∑ j ∈ I ×ˢ P, b j = 1)
    (hsep : ∀ i ∈ I ×ˢ P, ∀ j ∈ I ×ˢ P, i.2 ≠ j.2 → Disjoint (N i) (N j))
    {B : ℝ} (hcap : ∀ j ∈ I ×ˢ P, b j ≤ B) :
    residueTupleOverlapMass (I ×ˢ P) b N ≤ (I.card : ℝ) * B := by
  classical
  have hfiber (i : α × β) (hi : i ∈ I ×ˢ P) :
      (∑ j ∈ I ×ˢ P, if Disjoint (N i) (N j) then 0 else b i * b j) ≤
        b i * ((I.card : ℝ) * B) := by
    have hp := (Finset.mem_product.mp hi).2
    calc
      _ ≤ ∑ j ∈ I ×ˢ P, if j.2 = i.2 then b i * b j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases heq : j.2 = i.2
        · rw [if_pos heq]
          split_ifs
          · exact mul_nonneg (hb i hi) (hb j hj)
          · exact le_rfl
        · rw [if_neg heq, if_pos (hsep i hi j hj (Ne.symm heq))]
      _ = b i * (∑ j ∈ I ×ˢ P, if j.2 = i.2 then b j else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        split_ifs <;> simp
      _ = b i * (∑ a ∈ I, b (a, i.2)) := by
        congr 1
        simp [Finset.sum_product, hp]
      _ ≤ b i * (∑ _a ∈ I, B) := by
        apply mul_le_mul_of_nonneg_left _ (hb i hi)
        exact Finset.sum_le_sum fun a ha => hcap (a, i.2) (Finset.mem_product.mpr ⟨ha, hp⟩)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ I ×ˢ P, b i * ((I.card : ℝ) * B) :=
      Finset.sum_le_sum fun i hi => hfiber i hi
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem SourceProbabilityData.pinnedNormalizedWeight_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (hB : 0 < D.pinnedTotalMass q)
    {j : Fin D.dimension × ℕ} (hj : j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x) :
    D.pinnedNormalizedWeight q j ≤ (x : ℝ) ^ (-2 / 3 + e : ℝ) / D.pinnedTotalMass q := by
  exact div_le_div_of_nonneg_right (D.mass_atom_bound j.2 (Finset.mem_product.mp hj).2 _) hB.le

theorem SourceProbabilityData.pinnedTuple_overlap_mass_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (hB : 0 < D.pinnedTotalMass q)
    (hsep : ∀ i ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
      ∀ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x, i.2 ≠ j.2 →
        Disjoint ((D.pinnedResidueTuple q i).erase q) ((D.pinnedResidueTuple q j).erase q)) :
    residueTupleOverlapMass (Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x)
        (D.pinnedNormalizedWeight q) (fun j => (D.pinnedResidueTuple q j).erase q) ≤
      (D.dimension : ℝ) * (x : ℝ) ^ (-2 / 3 + e : ℝ) / D.pinnedTotalMass q := by
  have h := product_label_overlap_mass_le Finset.univ (commonPinnedPrimeSet (x / 2) x)
    (D.pinnedNormalizedWeight q) (fun j => (D.pinnedResidueTuple q j).erase q)
    (fun j hj => D.pinnedNormalizedWeight_nonneg q hB hj)
    (D.pinnedNormalizedWeight_sum_one q hB) hsep
    (fun j hj => D.pinnedNormalizedWeight_le q hB hj)
  simpa only [Finset.card_univ, Fintype.card_fin, mul_div_assoc] using h

theorem eventually_pinnedTuple_overlap_mass_le {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ q ∈ sourceSievingPrimes c x,
      residueTupleOverlapMass (Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x)
          (D.pinnedNormalizedWeight q) (fun j => (D.pinnedResidueTuple q j).erase q) ≤
        4 * (D.dimension : ℝ) * Real.log (x : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + e : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_pinnedResidueTuple_ranges hc,
    eventually_pinnedTotalMass_lower hc, hlog.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hranges hB hL
  intro D q hq
  have hBq := hB D q hq
  have hBpos : 0 < D.pinnedTotalMass q :=
    (by positivity : (0 : ℝ) < 1 / (4 * Real.log (x : ℝ) ^ 2)).trans_le hBq
  refine (D.pinnedTuple_overlap_mass_le q hBpos ((hranges D).2.2 q)).trans ?_
  calc
    _ ≤ (D.dimension : ℝ) * (x : ℝ) ^ (-2 / 3 + e : ℝ) /
        (1 / (4 * Real.log (x : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hBq
    _ = _ := by
      simp only [div_eq_mul_inv, one_mul, inv_inv]
      ring

end

end Erdos4b.FGKMT
