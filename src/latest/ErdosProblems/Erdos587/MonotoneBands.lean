import ErdosProblems.Erdos587.FirstDerivativeSum

/-! Interval fibers and cardinality estimates for monotone separated increments. -/

namespace Erdos587

lemma increment_lower_separation (d : ℕ → ℝ) (N : ℕ) (lam : ℝ)
    (hstep : ∀ n, n + 1 < N → lam ≤ d (n + 1) - d n)
    {n m : ℕ} (hn : n < N) (hm : m < N) (hnm : n ≤ m) :
    lam * ((m : ℝ) - n) ≤ d m - d n := by
  have hmono : MonotoneOn (fun n : ℕ => d n - lam * n) (Set.Iio N) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iio
    intro k hk hkN hksN
    have hnext : k + 1 < N := hksN
    have hh := hstep k hnext
    change d k - lam * k ≤ d (k + 1) - lam * ((k + 1 : ℕ) : ℝ)
    push_cast
    linarith
  have hh := hmono hn hm hnm
  change d n - lam * n ≤ d m - lam * m at hh
  nlinarith

lemma increment_upper_separation (d : ℕ → ℝ) (N : ℕ) (Λ : ℝ)
    (hstep : ∀ n, n + 1 < N → d (n + 1) - d n ≤ Λ)
    {n m : ℕ} (hn : n < N) (hm : m < N) (hnm : n ≤ m) :
    d m - d n ≤ Λ * ((m : ℝ) - n) := by
  have hh := increment_lower_separation (fun n => -d n) N (-Λ)
    (fun n hn => by have := hstep n hn; linarith) hn hm hnm
  nlinarith

noncomputable def monotoneBand (d : ℕ → ℝ) (N : ℕ) (a b : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n => a ≤ d n ∧ d n ≤ b)

lemma mem_monotoneBand (d : ℕ → ℝ) (N n : ℕ) (a b : ℝ) :
    n ∈ monotoneBand d N a b ↔ n < N ∧ a ≤ d n ∧ d n ≤ b := by
  simp only [monotoneBand, Finset.mem_filter, Finset.mem_range]

theorem monotoneBand_eq_Icc (d : ℕ → ℝ) (N : ℕ) (a b : ℝ)
    (hd : MonotoneOn d (Set.Iio N)) (hs : (monotoneBand d N a b).Nonempty) :
    monotoneBand d N a b = Finset.Icc ((monotoneBand d N a b).min' hs)
      ((monotoneBand d N a b).max' hs) := by
  classical
  let S := monotoneBand d N a b
  have hlo := (mem_monotoneBand d N (S.min' hs) a b).mp (Finset.min'_mem S hs)
  have hhi := (mem_monotoneBand d N (S.max' hs) a b).mp (Finset.max'_mem S hs)
  apply Finset.ext
  intro n
  constructor
  · intro hn
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
  · intro hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hnN : n < N := hnhi.trans_lt hhi.1
    apply (mem_monotoneBand d N n a b).mpr
    exact ⟨hnN, hlo.2.1.trans (hd hlo.1 hnN hnlo), (hd hnN hhi.1 hnhi).trans hhi.2.2⟩

theorem card_le_of_separated_values (S : Finset ℕ) (d : ℕ → ℝ) {a b lam : ℝ}
    (hlam : 0 < lam) (hab : a ≤ b)
    (hd : ∀ n ∈ S, a ≤ d n ∧ d n ≤ b)
    (hsep : ∀ n ∈ S, ∀ m ∈ S, n ≤ m → lam * ((m : ℝ) - n) ≤ d m - d n) :
    (S.card : ℝ) ≤ (b - a) / lam + 1 := by
  classical
  by_cases hs : S.Nonempty
  · let lo := S.min' hs
    let hi := S.max' hs
    have hlo : lo ∈ S := Finset.min'_mem _ _
    have hhi : hi ∈ S := Finset.max'_mem _ _
    have hlohi : lo ≤ hi := Finset.min'_le_max' S hs
    have hsub : S ⊆ Finset.Icc lo hi := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hn, Finset.le_max' _ _ hn⟩
    have hcard : S.card ≤ hi + 1 - lo := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hcardR : (S.card : ℝ) ≤ (hi : ℝ) + 1 - lo := by
      have hh : (S.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa only [Nat.cast_sub (by omega : lo ≤ hi + 1), Nat.cast_add, Nat.cast_one] using hh
    have hspan := hsep lo hlo hi hhi hlohi
    have hwidth : (hi : ℝ) - lo ≤ (b - a) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith [(hd lo hlo).1, (hd hi hhi).2]
    linarith
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hzero, Finset.card_empty, Nat.cast_zero]
    have hh : 0 ≤ (b - a) / lam := div_nonneg (sub_nonneg.mpr hab) hlam.le
    linarith

theorem card_monotoneBand_le (d : ℕ → ℝ) (N : ℕ) {a b lam : ℝ}
    (hlam : 0 < lam) (hab : a ≤ b)
    (hstep : ∀ n, n + 1 < N → lam ≤ d (n + 1) - d n) :
    ((monotoneBand d N a b).card : ℝ) ≤ (b - a) / lam + 1 := by
  apply card_le_of_separated_values (monotoneBand d N a b) d hlam hab
  · intro n hn
    exact ((mem_monotoneBand d N n a b).mp hn).2
  · intro n hn m hm hnm
    exact increment_lower_separation d N lam hstep ((mem_monotoneBand d N n a b).mp hn).1
      ((mem_monotoneBand d N m a b).mp hm).1 hnm

end Erdos587
