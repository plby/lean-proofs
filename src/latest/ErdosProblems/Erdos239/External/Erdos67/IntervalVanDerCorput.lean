import ErdosProblems.Erdos239.External.Erdos67.VanDerCorput

/-!
# The interval form of finite van der Corput differencing

This file specializes the abstract finite-family inequality to translates of
an interval-supported complex sequence.  The translating ambient interval is
`range (N + H)`, so every displayed correlation is an ordinary, non-cyclic
correlation and no wrap-around convention is hidden in the statement.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- Extend `a|[0,N)` by zero after translating its support to `[h,h+N)`.
The ambient interval in the applications below is `range (N+H)`. -/
def intervalTranslate (a : ℕ → ℂ) (N h i : ℕ) : ℂ :=
  if h ≤ i ∧ i < h + N then a (i - h) else 0

theorem sum_intervalTranslate_eq (a : ℕ → ℂ) (N H h : ℕ) (hh : h ≤ H) :
    (∑ i ∈ range (N + H), intervalTranslate a N h i) =
      ∑ n ∈ range N, a n := by
  unfold intervalTranslate
  rw [← Finset.sum_filter]
  have hfilter :
      (range (N + H)).filter (fun i ↦ h ≤ i ∧ i < h + N) = Ico h (h + N) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, sum_Ico_eq_sum_range]
  have hlen : h + N - h = N := by omega
  rw [hlen]
  apply sum_congr rfl
  intro n hn
  have : h + n - h = n := by omega
  rw [this]

/-- A positive-lag correlation on the interval `[0,N)`. -/
def intervalCorrelation (a : ℕ → ℂ) (N r : ℕ) : ℂ :=
  ∑ n ∈ range (N - r), a (n + r) * conj (a n)

/-- Ordered sum of a nonnegative quantity over all nonzero lags below `H`. -/
def orderedLagSum (F : ℕ → ℝ) (H : ℕ) : ℝ :=
  ∑ h ∈ range H, ∑ k ∈ range H,
    if h = k then 0 else F (max h k - min h k)

theorem orderedLagSum_eq_erase (F : ℕ → ℝ) (H : ℕ) :
    orderedLagSum F H =
      ∑ h ∈ range H, ∑ k ∈ (range H).erase h,
        F (max h k - min h k) := by
  unfold orderedLagSum
  apply sum_congr rfl
  intro h hh
  rw [← add_sum_erase (range H)
    (fun k ↦ if h = k then 0 else F (max h k - min h k)) hh]
  simp only [if_pos, zero_add]
  apply sum_congr rfl
  intro k hk
  have hne : h ≠ k := (ne_of_mem_erase hk).symm
  rw [if_neg hne]

private theorem orderedLagSum_succ (F : ℕ → ℝ) (H : ℕ) :
    orderedLagSum F (H + 1) = orderedLagSum F H +
      2 * ∑ k ∈ range H, F (H - k) := by
  unfold orderedLagSum
  simp only [sum_range_succ]
  have hleft :
      (∑ h ∈ range H,
          ((∑ k ∈ range H,
              if h = k then 0 else F (max h k - min h k)) +
            (if h = H then 0 else F (max h H - min h H)))) =
        (∑ h ∈ range H, ∑ k ∈ range H,
            if h = k then 0 else F (max h k - min h k)) +
          ∑ h ∈ range H, F (H - h) := by
    rw [sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro h hh
    have hlt : h < H := mem_range.mp hh
    simp [hlt.ne, hlt.le]
  rw [hleft]
  have hright :
      (∑ k ∈ range H,
          if H = k then 0 else F (max H k - min H k)) =
        ∑ k ∈ range H, F (H - k) := by
    apply sum_congr rfl
    intro k hk
    have hlt : k < H := mem_range.mp hk
    simp [hlt.ne', hlt.le]
  rw [hright]
  simp
  ring

/-- Each nonzero lag occurs at most `2*H` times among the ordered pairs of
shifts below `H`. -/
theorem orderedLagSum_le (F : ℕ → ℝ) (H : ℕ) (hF : ∀ r, 0 ≤ F r) :
    orderedLagSum F H ≤
      2 * H * ∑ r ∈ Ico 1 H, F r := by
  induction H with
  | zero => simp [orderedLagSum]
  | succ H ih =>
      by_cases hHzero : H = 0
      · subst H
        simp [orderedLagSum]
      rw [show H + 1 = Nat.succ H by omega, orderedLagSum_succ]
      have hIco :
          (∑ r ∈ Ico 1 (H + 1), F r) =
            (∑ r ∈ Ico 1 H, F r) + F H := by
        rw [sum_Ico_succ_top (by omega)]
      rw [hIco]
      have hreflect :
          (∑ k ∈ range H, F (H - k)) = ∑ r ∈ Ico 1 (H + 1), F r := by
        rw [sum_Ico_eq_sum_range]
        have hr := sum_range_reflect (fun r ↦ F (r + 1)) H
        calc
          (∑ k ∈ range H, F (H - k)) =
              ∑ k ∈ range H, F (H - 1 - k + 1) := by
                apply sum_congr rfl
                intro k hk
                have hklt := mem_range.mp hk
                congr 1
                omega
          _ = ∑ k ∈ range H, F (k + 1) := hr
          _ = ∑ k ∈ range H, F (1 + k) := by
                apply sum_congr rfl
                intro k hk
                rw [Nat.add_comm]
      rw [hreflect, hIco]
      have hbase : 0 ≤ ∑ r ∈ Ico 1 H, F r :=
        sum_nonneg fun r hr ↦ hF r
      have hlast : 0 ≤ F H := hF H
      push_cast at ih ⊢
      nlinarith

private theorem finiteFamilyCorrelation_intervalTranslate_of_le
    (a : ℕ → ℂ) (N H h k : ℕ) (hHN : H ≤ N)
    (hh : h < H) (hk : k < H) (hhk : h ≤ k) :
    finiteFamilyCorrelation (range (N + H))
        (fun j i ↦ intervalTranslate a N j i) h k =
      intervalCorrelation a N (k - h) := by
  unfold finiteFamilyCorrelation intervalTranslate intervalCorrelation
  have hcombine :
      (∑ i ∈ range (N + H),
          (if h ≤ i ∧ i < h + N then a (i - h) else 0) *
            conj (if k ≤ i ∧ i < k + N then a (i - k) else 0)) =
        ∑ i ∈ range (N + H),
          if (h ≤ i ∧ i < h + N) ∧ (k ≤ i ∧ i < k + N) then
            a (i - h) * conj (a (i - k)) else 0 := by
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [hcombine]
  rw [← Finset.sum_filter]
  have hfilter :
      (range (N + H)).filter
          (fun i ↦ (h ≤ i ∧ i < h + N) ∧ (k ≤ i ∧ i < k + N)) =
        Ico k (h + N) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, sum_Ico_eq_sum_range]
  have hdiff : k - h ≤ N := by omega
  have hlen : h + N - k = N - (k - h) := by omega
  rw [hlen]
  apply sum_congr rfl
  intro n hn
  have hnlt : n < N - (k - h) := mem_range.mp hn
  have hkadd : k + n - k = n := by omega
  have hhadd : k + n - h = n + (k - h) := by omega
  rw [hkadd, hhadd]

private theorem finiteFamilyCorrelation_intervalTranslate_of_lt
    (a : ℕ → ℂ) (N H h k : ℕ) (hHN : H ≤ N)
    (hh : h < H) (_hk : k < H) (hkh : k < h) :
    finiteFamilyCorrelation (range (N + H))
        (fun j i ↦ intervalTranslate a N j i) h k =
      conj (intervalCorrelation a N (h - k)) := by
  unfold finiteFamilyCorrelation intervalTranslate intervalCorrelation
  rw [map_sum]
  simp only [map_mul]
  have hcombine :
      (∑ i ∈ range (N + H),
          (if h ≤ i ∧ i < h + N then a (i - h) else 0) *
            conj (if k ≤ i ∧ i < k + N then a (i - k) else 0)) =
        ∑ i ∈ range (N + H),
          if (h ≤ i ∧ i < h + N) ∧ (k ≤ i ∧ i < k + N) then
            a (i - h) * conj (a (i - k)) else 0 := by
    apply sum_congr rfl
    intro i hi
    split_ifs <;> simp_all
  rw [hcombine]
  rw [← Finset.sum_filter]
  have hfilter :
      (range (N + H)).filter
          (fun i ↦ (h ≤ i ∧ i < h + N) ∧ (k ≤ i ∧ i < k + N)) =
        Ico h (k + N) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilter, sum_Ico_eq_sum_range]
  have hdiff : h - k ≤ N := by omega
  have hlen : k + N - h = N - (h - k) := by omega
  rw [hlen]
  apply sum_congr rfl
  intro n hn
  have hnlt : n < N - (h - k) := mem_range.mp hn
  have hhadd : h + n - h = n := by omega
  have hkadd : h + n - k = n + (h - k) := by omega
  rw [hhadd, hkadd]
  change a n * conj (a (n + (h - k))) =
    conj (a (n + (h - k))) * conj (conj (a n))
  rw [Complex.conj_conj]
  ring

theorem norm_finiteFamilyCorrelation_intervalTranslate
    (a : ℕ → ℂ) (N H h k : ℕ) (hHN : H ≤ N)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖finiteFamilyCorrelation (range (N + H))
        (fun j i ↦ intervalTranslate a N j i) h k‖ =
      ‖intervalCorrelation a N (max h k - min h k)‖ := by
  rcases lt_or_gt_of_ne hne with hhk | hkh
  · rw [finiteFamilyCorrelation_intervalTranslate_of_le
      a N H h k hHN hh hk hhk.le]
    simp [max_eq_right hhk.le, min_eq_left hhk.le]
  · rw [finiteFamilyCorrelation_intervalTranslate_of_lt
      a N H h k hHN hh hk hkh,
      show ‖conj (intervalCorrelation a N (h - k))‖ =
        ‖intervalCorrelation a N (h - k)‖ by rw [Complex.norm_conj]]
    simp [max_eq_left hkh.le, min_eq_right hkh.le]

/-- Standard non-cyclic interval van der Corput inequality, with the full
ordered off-diagonal shift family displayed.  The factor `N+H` is the size of
the zero-extension interval. -/
theorem interval_vanDerCorput_offDiagonal
    (a : ℕ → ℂ) (N H : ℕ) (_hH : 0 < H) (hHN : H ≤ N)
    (ha : ∀ n < N, ‖a n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, a n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          ∑ h ∈ range H, ∑ k ∈ (range H).erase h,
            ‖intervalCorrelation a N (max h k - min h k)‖) := by
  let u : ℕ → ℕ → ℂ := fun h i ↦ intervalTranslate a N h i
  let S : ℂ := ∑ n ∈ range N, a n
  have hsum : ∀ h ∈ range H, ∑ i ∈ range (N + H), u h i = S := by
    intro h hh
    exact sum_intervalTranslate_eq a N H h (mem_range.mp hh).le
  have hvdc := finite_vanDerCorput (range (N + H)) (range H) u S hsum
  have hdiag : ∀ h ∈ range H,
      ‖finiteFamilyCorrelation (range (N + H)) u h h‖ ≤ N := by
    intro h hh
    unfold finiteFamilyCorrelation u intervalTranslate
    calc
      ‖∑ i ∈ range (N + H),
          (if h ≤ i ∧ i < h + N then a (i - h) else 0) *
            conj (if h ≤ i ∧ i < h + N then a (i - h) else 0)‖ ≤
        ∑ i ∈ range (N + H),
          ‖(if h ≤ i ∧ i < h + N then a (i - h) else 0) *
            conj (if h ≤ i ∧ i < h + N then a (i - h) else 0)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ range (N + H),
          if h ≤ i ∧ i < h + N then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro i hi
        split_ifs with his
        · simp only [norm_mul, Complex.norm_conj]
          have hil : i - h < N := by omega
          have hnorm := ha (i - h) hil
          have hnonneg := norm_nonneg (a (i - h))
          nlinarith [sq_nonneg (1 - ‖a (i - h)‖)]
        · simp
      _ = N := by
        rw [← Finset.sum_filter]
        have hfilter :
            (range (N + H)).filter (fun i ↦ h ≤ i ∧ i < h + N) =
              Ico h (h + N) := by
          ext i
          simp only [mem_filter, mem_range, mem_Ico]
          have hhH : h < H := mem_range.mp hh
          constructor
          · exact fun hi ↦ hi.2
          · intro hi
            exact ⟨by omega, hi⟩
        rw [hfilter]
        simp
  have henergy :
      (∑ h ∈ range H, ∑ k ∈ range H,
          ‖finiteFamilyCorrelation (range (N + H)) u h k‖) ≤
        (H : ℝ) * N +
          ∑ h ∈ range H, ∑ k ∈ (range H).erase h,
            ‖intervalCorrelation a N (max h k - min h k)‖ := by
    calc
      (∑ h ∈ range H, ∑ k ∈ range H,
          ‖finiteFamilyCorrelation (range (N + H)) u h k‖) =
        ∑ h ∈ range H,
          (‖finiteFamilyCorrelation (range (N + H)) u h h‖ +
            ∑ k ∈ (range H).erase h,
              ‖finiteFamilyCorrelation (range (N + H)) u h k‖) := by
          apply sum_congr rfl
          intro h hh
          rw [← add_sum_erase (range H)
            (fun k ↦ ‖finiteFamilyCorrelation (range (N + H)) u h k‖) hh]
      _ ≤ ∑ h ∈ range H,
          ((N : ℝ) + ∑ k ∈ (range H).erase h,
            ‖intervalCorrelation a N (max h k - min h k)‖) := by
          apply sum_le_sum
          intro h hh
          apply add_le_add (hdiag h hh)
          apply sum_le_sum
          intro k hk
          have hkH : k < H := mem_range.mp (mem_of_mem_erase hk)
          have hne : h ≠ k := Ne.symm (ne_of_mem_erase hk)
          exact le_of_eq (norm_finiteFamilyCorrelation_intervalTranslate
            a N H h k hHN (mem_range.mp hh) hkH hne)
      _ = (H : ℝ) * N +
          ∑ h ∈ range H, ∑ k ∈ (range H).erase h,
            ‖intervalCorrelation a N (max h k - min h k)‖ := by
          rw [sum_add_distrib]
          simp
  dsimp only [S] at hvdc
  have htrans := hvdc.trans (mul_le_mul_of_nonneg_left henergy
    (by positivity : (0 : ℝ) ≤ (range (N + H)).card))
  simpa only [card_range, Nat.cast_add, Nat.cast_id, u] using htrans

/-- Standard non-cyclic interval van der Corput inequality, with the ordered
off-diagonal family grouped by its positive lag.  The deliberately coarse
factor `2*H` is uniform in the lag and is convenient for iteration. -/
theorem interval_vanDerCorput_lag
    (a : ℕ → ℂ) (N H : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (ha : ∀ n < N, ‖a n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, a n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          2 * H * ∑ r ∈ Ico 1 H, ‖intervalCorrelation a N r‖) := by
  have hvdc := interval_vanDerCorput_offDiagonal a N H hH hHN ha
  have hpair :
      (∑ h ∈ range H, ∑ k ∈ (range H).erase h,
          ‖intervalCorrelation a N (max h k - min h k)‖) ≤
        2 * H * ∑ r ∈ Ico 1 H, ‖intervalCorrelation a N r‖ := by
    have hle := orderedLagSum_le
      (fun r ↦ ‖intervalCorrelation a N r‖) H
      (fun r ↦ norm_nonneg (intervalCorrelation a N r))
    rw [orderedLagSum_eq_erase] at hle
    exact hle
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, a n‖ ^ 2 ≤
        ((N + H : ℕ) : ℝ) *
          ((H : ℝ) * N +
            ∑ h ∈ range H, ∑ k ∈ (range H).erase h,
              ‖intervalCorrelation a N (max h k - min h k)‖) := hvdc
    _ ≤ ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N +
          2 * H * ∑ r ∈ Ico 1 H, ‖intervalCorrelation a N r‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_right hpair ((H : ℝ) * N)) (by positivity)

end

end Erdos67
