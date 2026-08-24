import ErdosProblems.Erdos587.FirstDerivativeTest
import ErdosProblems.Erdos587.MonotoneBands

/-! Separate one unit increment strip into an oscillatory middle and short boundary pieces. -/

open scoped BigOperators

namespace Erdos587

noncomputable def phaseIncrement (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n + 1) - f n

theorem norm_phase_sum_on_increment_band (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {δ : ℝ}
    (hδ : 0 < δ) (hd : MonotoneOn (phaseIncrement f) (Set.Iio N)) :
    ‖∑ n ∈ monotoneBand (phaseIncrement f) N ((k : ℝ) + δ) ((k : ℝ) + 1 - δ), phase (f n)‖ ≤
      1 / δ := by
  classical
  let S := monotoneBand (phaseIncrement f) N ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
  by_cases hs : S.Nonempty
  · let lo := S.min' hs
    let hi := S.max' hs
    have hlohi : lo ≤ hi := Finset.min'_le_max' S hs
    have hhiS : hi ∈ S := Finset.max'_mem S hs
    have hhiN : hi < N := ((mem_monotoneBand _ _ _ _ _).mp hhiS).1
    have hS : S = Finset.Icc lo hi := monotoneBand_eq_Icc _ _ _ _ hd hs
    have hmem (n : ℕ) (hn : n ≤ hi - lo) : lo + n ∈ S := by
      rw [hS]
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hb (n : ℕ) (hn : n ≤ hi - lo) :
        (k : ℝ) + δ ≤ phaseIncrement f (lo + n) ∧
          phaseIncrement f (lo + n) ≤ (k : ℝ) + 1 - δ :=
      ((mem_monotoneBand _ _ _ _ _).mp (hmem n hn)).2
    have hbound := norm_phase_sum_le_of_monotone_increments (fun n => f (lo + n)) (hi - lo) k hδ
      (fun n hn => by simpa only [phaseIncrement, Nat.add_assoc] using (hb n hn).1)
      (fun n hn => by simpa only [phaseIncrement, Nat.add_assoc] using (hb n hn).2)
      (fun n hn => by
        have hh := hd (show lo + n < N by omega) (show lo + (n + 1) < N by omega)
          (show lo + n ≤ lo + (n + 1) by omega)
        simpa only [phaseIncrement, Nat.add_assoc] using hh)
    change ‖∑ n ∈ S, phase (f n)‖ ≤ 1 / δ
    rw [hS]
    have hIco : Finset.Ico lo (hi + 1) = Finset.Icc lo hi := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [← hIco, Finset.sum_Ico_eq_sum_range, show hi + 1 - lo = hi - lo + 1 by omega]
    exact hbound
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change ‖∑ n ∈ S, phase (f n)‖ ≤ 1 / δ
    rw [hS, Finset.sum_empty, norm_zero]
    positivity

noncomputable def incrementUnitFiber (f : ℕ → ℝ) (N : ℕ) (k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => Int.floor (phaseIncrement f n) = k)

lemma mem_incrementUnitFiber (f : ℕ → ℝ) (N n : ℕ) (k : ℤ) :
    n ∈ incrementUnitFiber f N k ↔ n < N ∧ Int.floor (phaseIncrement f n) = k := by
  simp only [incrementUnitFiber, Finset.mem_filter, Finset.mem_range]

theorem norm_phase_sum_on_increment_fiber (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {δ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam)
    (hd : MonotoneOn (phaseIncrement f) (Set.Iio N))
    (hstep : ∀ n, n + 1 < N → lam ≤ phaseIncrement f (n + 1) - phaseIncrement f n) :
    ‖∑ n ∈ incrementUnitFiber f N k, phase (f n)‖ ≤ 1 / δ + 2 * δ / lam + 2 := by
  classical
  let P := incrementUnitFiber f N k
  let G := monotoneBand (phaseIncrement f) N ((k : ℝ) + δ) ((k : ℝ) + 1 - δ)
  let L := monotoneBand (phaseIncrement f) N (k : ℝ) ((k : ℝ) + δ)
  let U := monotoneBand (phaseIncrement f) N ((k : ℝ) + 1 - δ) ((k : ℝ) + 1)
  have hGP : G ⊆ P := by
    intro n hn
    obtain ⟨hnN, hlo, hhi⟩ := (mem_monotoneBand _ _ _ _ _).mp hn
    apply (mem_incrementUnitFiber f N n k).mpr
    refine ⟨hnN, Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩⟩
  have hbad : P \ G ⊆ L ∪ U := by
    intro n hn
    obtain ⟨hnP, hnG⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hnN, hfloor⟩ := (mem_incrementUnitFiber f N n k).mp hnP
    obtain ⟨hlo, hhi⟩ := Int.floor_eq_iff.mp hfloor
    by_cases hleft : phaseIncrement f n ≤ (k : ℝ) + δ
    · apply Finset.mem_union.mpr
      exact Or.inl ((mem_monotoneBand _ _ _ _ _).mpr ⟨hnN, hlo, hleft⟩)
    · have hright : (k : ℝ) + 1 - δ ≤ phaseIncrement f n := by
        by_contra hh
        apply hnG
        apply (mem_monotoneBand _ _ _ _ _).mpr
        exact ⟨hnN, by linarith, by linarith⟩
      apply Finset.mem_union.mpr
      exact Or.inr ((mem_monotoneBand _ _ _ _ _).mpr ⟨hnN, hright, hhi.le⟩)
  have hL : (L.card : ℝ) ≤ δ / lam + 1 := by
    calc
      _ ≤ (((k : ℝ) + δ) - k) / lam + 1 :=
        card_monotoneBand_le _ _ hlam (by linarith) hstep
      _ = _ := by ring
  have hU : (U.card : ℝ) ≤ δ / lam + 1 := by
    calc
      _ ≤ (((k : ℝ) + 1) - ((k : ℝ) + 1 - δ)) / lam + 1 :=
        card_monotoneBand_le _ _ hlam (by linarith) hstep
      _ = _ := by ring
  have hcard : ((P \ G).card : ℝ) ≤ 2 * δ / lam + 2 := by
    have hh : (P \ G).card ≤ L.card + U.card :=
      (Finset.card_le_card hbad).trans (Finset.card_union_le L U)
    have hhR : ((P \ G).card : ℝ) ≤ (L.card : ℝ) + U.card := by exact_mod_cast hh
    calc
      _ ≤ (L.card : ℝ) + U.card := hhR
      _ ≤ (δ / lam + 1) + (δ / lam + 1) := add_le_add hL hU
      _ = _ := by ring
  have hbadnorm : ‖∑ n ∈ P \ G, phase (f n)‖ ≤ 2 * δ / lam + 2 := by
    calc
      _ ≤ ∑ n ∈ P \ G, ‖phase (f n)‖ := norm_sum_le _ _
      _ = ((P \ G).card : ℝ) := by simp only [norm_phase, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := hcard
  have hgoodnorm : ‖∑ n ∈ G, phase (f n)‖ ≤ 1 / δ := norm_phase_sum_on_increment_band f N k hδ hd
  change ‖∑ n ∈ P, phase (f n)‖ ≤ _
  rw [← Finset.sum_sdiff hGP]
  calc
    _ ≤ ‖∑ n ∈ P \ G, phase (f n)‖ + ‖∑ n ∈ G, phase (f n)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end Erdos587
