import ErdosProblems.Erdos1148.MaximalNatRuns
import ErdosProblems.Erdos1148.SeparatedVisitCounts
import ErdosProblems.Erdos1148.LongCuspVisitPatterns

/-! # Maximal runs of cusp visits and their logarithmic separation -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def modularCuspVisitTimes (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) : Finset ℕ :=
  (modularCuspVisitPattern H n x).image Fin.val

lemma mem_modularCuspVisitTimes_iff (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) (k : ℕ) :
    k ∈ modularCuspVisitTimes H n x ↔ k < n ∧
      modularRightTranslate (diagonalFlow (k : ℝ)) x ∈ modularCusp H := by
  classical
  constructor
  · intro hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i.isLt, (mem_modularCuspVisitPattern_iff H n x i).mp hi⟩
  · rintro ⟨hkn, hk⟩
    exact Finset.mem_image.mpr ⟨⟨k, hkn⟩,
      (mem_modularCuspVisitPattern_iff H n x ⟨k, hkn⟩).mpr hk, rfl⟩

theorem card_maximal_cusp_runs_le (g : SL(2, ℝ)) {H : ℝ} (hH : 1 < H) (n : ℕ) :
    ((maximalNatRuns (modularCuspVisitTimes H n (modularMk g))).card : ℝ) ≤
      (n : ℝ) / (4 * Real.log H) + 1 := by
  let V := modularCuspVisitTimes H n (modularMk g)
  let s := (maximalNatRuns V).image Prod.fst
  have hrun (a : ℕ) (ha : a ∈ s) : ∃ b, (a, b) ∈ maximalNatRuns V := by
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp ha
    refine ⟨p.2, ?_⟩
    rw [← heq]
    exact hp
  have hmem (a : ℕ) (ha : a ∈ s) : a ∈ V := by
    obtain ⟨b, hb⟩ := hrun a ha
    have h := (mem_maximalNatRuns_iff V (a, b)).mp hb
    exact h.2.1 (Finset.mem_Icc.mpr ⟨le_rfl, h.1⟩)
  have hbound (a : ℕ) (ha : a ∈ s) : a ≤ n :=
    ((mem_modularCuspVisitTimes_iff H n (modularMk g) a).mp (hmem a ha)).1.le
  have hvisits (a : ℕ) (ha : a ∈ s) :
      modularMk (g * diagonalFlow (a : ℝ)) ∈ modularCusp H :=
    ((mem_modularCuspVisitTimes_iff H n (modularMk g) a).mp (hmem a ha)).2
  have hexits (a : ℕ) (ha : a ∈ s) (b : ℕ) (hb : b ∈ s) (hab : a < b) :
      ∃ t ∈ Set.Icc (a : ℝ) (b : ℝ), modularMk (g * diagonalFlow t) ∉ modularCusp H := by
    obtain ⟨d, hd⟩ := hrun b hb
    have hr := (mem_maximalNatRuns_iff V (b, d)).mp hd
    have hbpos : 0 < b := by omega
    have hprev : b - 1 ∉ V := hr.2.2.1.resolve_left (by omega)
    refine ⟨((b - 1 : ℕ) : ℝ), ⟨?_, ?_⟩, ?_⟩
    · exact_mod_cast (show a ≤ b - 1 by omega)
    · exact_mod_cast (show b - 1 ≤ b by omega)
    · intro hcusp
      apply hprev
      apply (mem_modularCuspVisitTimes_iff H n (modularMk g) (b - 1)).mpr
      exact ⟨by have := hbound b hb; omega, hcusp⟩
  have hcard : s.card = (maximalNatRuns V).card :=
    Finset.card_image_of_injOn (maximalNatRuns_fst_injOn V)
  have h := cusp_run_starts_card_le g hH s hbound hvisits hexits
  rwa [hcard] at h

theorem maximal_cusp_run_buffered (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hwindow : Real.exp 1 ≤ H ^ 4) {n : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g)))
    (hstart : modularMk g ∉ modularCusp H)
    (hend : modularMk (g * diagonalFlow (n : ℝ)) ∉ modularCusp H) :
    BufferedCuspExcursion H ((p.2 : ℝ) - p.1)
      (g * diagonalFlow ((p.1 : ℝ) - 2 * Real.log H)) := by
  let V := modularCuspVisitTimes H n (modularMk g)
  have hr := (mem_maximalNatRuns_iff V p).mp hp
  have hmem (k : ℕ) (hk : k ∈ Finset.Icc p.1 p.2) : k < n ∧
      modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H :=
    (mem_modularCuspVisitTimes_iff H n (modularMk g) k).mp (hr.2.1 hk)
  have ha := hmem p.1 (Finset.mem_Icc.mpr ⟨le_rfl, hr.1⟩)
  have hb := hmem p.2 (Finset.mem_Icc.mpr ⟨hr.1, le_rfl⟩)
  have ha0 : p.1 ≠ 0 := by
    intro hz
    apply hstart
    simpa only [hz, Nat.cast_zero, diagonalFlow_zero, mul_one] using ha.2
  have hbefore : modularMk (g * diagonalFlow ((p.1 : ℝ) - 1)) ∉ modularCusp H := by
    intro hcusp
    apply hr.2.2.1.resolve_left ha0
    apply (mem_modularCuspVisitTimes_iff H n (modularMk g) (p.1 - 1)).mpr
    refine ⟨by omega, ?_⟩
    simpa only [Nat.cast_sub (show 1 ≤ p.1 by omega), Nat.cast_one,
      modularRightTranslate_mk] using hcusp
  have hafter : modularMk (g * diagonalFlow ((p.2 : ℝ) + 1)) ∉ modularCusp H := by
    intro hcusp
    by_cases heq : p.2 + 1 = n
    · apply hend
      simpa only [← heq, Nat.cast_add, Nat.cast_one] using hcusp
    · apply hr.2.2.2
      apply (mem_modularCuspVisitTimes_iff H n (modularMk g) (p.2 + 1)).mpr
      exact ⟨by omega, by
        simpa only [Nat.cast_add, Nat.cast_one, modularRightTranslate_mk] using hcusp⟩
  exact bufferedCuspExcursion_of_integer_run g hH hwindow (fun k hk => (hmem k hk).2)
    hbefore hafter

theorem maximal_cusp_runs_buffered_order (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    {n : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g)))
    (hq : q ∈ maximalNatRuns (modularCuspVisitTimes H n (modularMk g))) (hpq : p.1 < q.1) :
    (p.2 : ℝ) + 2 * Real.log H < (q.1 : ℝ) - 2 * Real.log H := by
  let V := modularCuspVisitTimes H n (modularMk g)
  have hp' := (mem_maximalNatRuns_iff V p).mp hp
  have hq' := (mem_maximalNatRuns_iff V q).mp hq
  have hab : p.2 < q.1 := maximalNatRuns_end_lt_start hp hq hpq
  have ha := (mem_modularCuspVisitTimes_iff H n (modularMk g) p.2).mp
    (hp'.2.1 (Finset.mem_Icc.mpr ⟨hp'.1, le_rfl⟩))
  have hb := (mem_modularCuspVisitTimes_iff H n (modularMk g) q.1).mp
    (hq'.2.1 (Finset.mem_Icc.mpr ⟨le_rfl, hq'.1⟩))
  have hexit : modularMk (g * diagonalFlow ((p.2 + 1 : ℕ) : ℝ)) ∉ modularCusp H := by
    intro hcusp
    apply hp'.2.2.2
    exact (mem_modularCuspVisitTimes_iff H n (modularMk g) (p.2 + 1)).mpr ⟨by omega, hcusp⟩
  exact buffered_cusp_intervals_disjoint_of_exit g hH
    ⟨by exact_mod_cast Nat.le_succ p.2, by exact_mod_cast hab⟩ ha.2 hb.2 hexit

end Erdos1148.DukeArithmetic
