import ErdosProblems.Erdos489.OriginalBridge
import ErdosProblems.Erdos489.PeriodicAverage
import ErdosProblems.Erdos489.TruncatedGapCost
import ErdosProblems.Erdos489.FullGapConvergence
import ErdosProblems.Erdos489.HeilbronnRohrbach

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Classical Filter
open scoped Topology BigOperators

/-- A sequence whose one-step shift is positive-periodic has a Cesàro limit. -/
theorem exists_tendsto_average_of_shift_periodic
    (f : ℕ → ℕ) (P : ℕ) (hP : 0 < P)
    (hf : Function.Periodic (fun n => f (n + 1)) P) :
    ∃ L : ℝ, Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f n : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 L) := by
  let L : ℝ := ((∑ n ∈ Finset.range P, f (n + 1) : ℕ) : ℝ) / (P : ℝ)
  have hv : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f (n + 1) : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 L) := by
    exact tendsto_periodic_nat_average (fun n => f (n + 1)) P hP hf
  have hratio : Tendsto (fun x : ℕ => (x : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 1) := tendsto_natCast_div_add_atTop 1
  have hconst : Tendsto (fun x : ℕ => (f 0 : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 0) := by
    have ht := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat (f 0 : ℝ))
    simpa [Nat.cast_add] using ht
  have hcomb : Tendsto (fun x : ℕ =>
      (((∑ n ∈ Finset.range x, f (n + 1) : ℕ) : ℝ) / (x : ℝ)) *
        ((x : ℝ) / ((x : ℝ) + 1)) + (f 0 : ℝ) / ((x : ℝ) + 1))
      atTop (𝓝 L) := by
    simpa using (hv.mul hratio).add hconst
  have hsucc : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range (x + 1), f n : ℕ) : ℝ) / ((x + 1 : ℕ) : ℝ))
      atTop (𝓝 L) := by
    apply hcomb.congr'
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Finset.sum_range_succ']
    norm_num only [Nat.cast_add, Nat.cast_sum, Nat.cast_one]
    field_simp
  exact ⟨L, (tendsto_add_atTop_iff_nat 1).1 (by simpa [Nat.add_comm] using hsucc)⟩

/-- A forward period bounds every enumerated gap by one period. -/
theorem nth_gap_le_of_forward_period
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (P : ℕ) (hP : 0 < P) (hforward : ∀ n, q n → q (n + P)) (i : ℕ) :
    Nat.nth q (i + 1) - Nat.nth q i ≤ P := by
  have hmem := Nat.nth_mem_of_infinite hq i
  have hend := hforward _ hmem
  have hlt : Nat.nth q i < Nat.nth q i + P := by omega
  have hicount : i < Nat.count q (Nat.nth q i + P) :=
    (Nat.lt_nth_iff_count_lt hq).2 hlt
  have hidx : i + 1 ≤ Nat.count q (Nat.nth q i + P) := by omega
  have hmono : Nat.nth q (i + 1) ≤
      Nat.nth q (Nat.count q (Nat.nth q i + P)) :=
    (Nat.nth_strictMono hq).monotone hidx
  rw [Nat.nth_count hend] at hmono
  exact Nat.sub_le_iff_le_add'.2 hmono

/-- A finite forbidden set gives a convergent normalized full gap sum. -/
theorem exists_original_limit_of_finite_forbidden
    (A : Set ℕ) (hAfin : A.Finite) (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      atTop (𝓝 L) := by
  let p := restrictedForbidden A
  let s : Finset ℕ := hAfin.toFinset.filter fun a => 2 ≤ a
  let avoid : ℕ → Prop := fun n => ∀ a ∈ s, ¬a ∣ n
  let P : ℕ := s.prod id
  have hpiff : ∀ a, p a ↔ a ∈ s := by
    intro a
    simp [p, s, restrictedForbidden, hAfin.mem_toFinset]
  have hqiff : ∀ n, 0 < n → (divisorSifted p n ↔ avoid n) := by
    intro n hn
    simp only [divisorSifted, hn, true_and, avoid]
    constructor
    · intro h a ha
      exact h a ((hpiff a).2 ha)
    · intro h a ha
      exact h a ((hpiff a).1 ha)
  have hP : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro a ha
    have ha2 : 2 ≤ a := ((hpiff a).2 ha).2
    exact lt_of_lt_of_le (by omega : 0 < 2) ha2
  have havoid : Function.Periodic avoid P := by
    intro n
    apply propext
    constructor
    · intro hn a ha han
      apply hn a ha
      have hap : a ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem id ha
      exact (Nat.dvd_add_iff_left hap).1 han
    · intro hn a ha han
      apply hn a ha
      have hap : a ∣ P := by
        dsimp [P]
        exact Finset.dvd_prod_of_mem id ha
      exact (Nat.dvd_add_iff_left hap).2 han
  have hforward : ∀ n, divisorSifted p n → divisorSifted p (n + P) := by
    intro n hn
    have hnpos : 0 < n := hn.1
    apply (hqiff (n + P) (by omega)).2
    have hav := (hqiff n hnpos).1 hn
    exact havoid n ▸ hav
  have hBp : Set.Infinite {n | divisorSifted p n} := by
    have heq : {n | divisorSifted p n} = sievedSet A := by
      ext n
      exact divisorSifted_restricted_iff A hB n
    rw [heq]
    exact hB
  let H := P + 1
  have hgap : ∀ i, divisorSiftedGap p i < H := by
    intro i
    have hle := nth_gap_le_of_forward_period (divisorSifted p) hBp P hP hforward i
    simpa [divisorSiftedGap, divisorSiftedEnumeration, H] using (show
      Nat.nth (divisorSifted p) (i + 1) - Nat.nth (divisorSifted p) i < P + 1 by omega)
  have hshiftper : Function.Periodic
      (fun n => truncatedGapCost (divisorSifted p) H (n + 1)) P := by
    have heq : ∀ n, truncatedGapCost (divisorSifted p) H (n + 1) =
        truncatedGapCost avoid H (n + 1) := by
      intro n
      apply truncatedGapCost_eq_of_window_agree
      intro k hk
      exact hqiff (n + 1 + k) (by omega)
    intro n
    change truncatedGapCost (divisorSifted p) H (n + P + 1) =
      truncatedGapCost (divisorSifted p) H (n + 1)
    rw [heq (n + P), heq n]
    have ht := truncatedGapCost_periodic avoid H P havoid (n + 1)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  obtain ⟨L, hlocal⟩ := exists_tendsto_average_of_shift_periodic
    (truncatedGapCost (divisorSifted p) H) P hP hshiftper
  have heqavg : fullGapAverage p = fullTruncatedGapAverage p H := by
    funext x
    rw [fullGapAverage_eq_truncated_add_tail p hBp H x]
    have hempty : (Finset.range (Nat.count (divisorSifted p) x)).filter
        (fun i => H ≤ divisorSiftedGap p i) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      exact (not_le_of_gt (hgap i)) (Finset.mem_filter.mp hi).2
    rw [hempty]
    simp
  have hfull : Tendsto (fullGapAverage p) atTop (𝓝 L) := by
    rw [heqavg]
    exact hlocal
  refine ⟨L, hfull.congr' ?_⟩
  exact Filter.Eventually.of_forall fun x => fullGapAverage_restricted_eq A hB x

end Erdos489
