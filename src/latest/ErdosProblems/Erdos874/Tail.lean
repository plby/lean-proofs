/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos874.Foundations

/-!
# The terminal-interval construction for Erdős Problem 874

This file proves the sharp elementary construction.  The `k` consecutive
integers ending at `N` are admissible exactly when
`(k + 1) ^ 2 ≤ 4 * N + 1`.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

/-- The `k` consecutive integers ending at `N`. -/
def terminalInterval (N k : ℕ) : Finset ℤ :=
  Finset.Ioc ((N : ℤ) - (k : ℤ)) (N : ℤ)

/-- A terminal interval has exactly its advertised number of elements. -/
@[simp] theorem card_terminalInterval (N k : ℕ) :
    (terminalInterval N k).card = k := by
  simp [terminalInterval, Int.card_Ioc]

/-- If `k ≤ N`, the terminal interval lies in `{1, ..., N}`. -/
theorem terminalInterval_bounded {N k : ℕ} (hkN : k ≤ N) :
    terminalInterval N k ⊆ ambient N := by
  intro x hx
  simp only [terminalInterval, Finset.mem_Ioc] at hx
  simp only [mem_ambient]
  constructor
  · have hcast : (k : ℤ) ≤ N := by exact_mod_cast hkN
    omega
  · exact hx.2

private lemma terminalInterval_pos {N k : ℕ} (hkN : k ≤ N) :
    ∀ x ∈ terminalInterval N k, 0 < x := by
  intro x hx
  have hx' := terminalInterval_bounded hkN hx
  exact (mem_ambient.mp hx').1.trans_lt' (by norm_num)

/-- The sum of the first `r` positive integers, kept in a division-free form. -/
private def minPositionSum (r : ℕ) : ℤ :=
  (Finset.range r).sum fun i ↦ (i : ℤ) + 1

/-- The sum of the largest `r` positions in `Finset.Icc 1 k`. -/
private def maxPositionSum (k r : ℕ) : ℤ :=
  (Finset.range r).sum fun i ↦ (k : ℤ) - (i : ℤ)

@[simp] private lemma minPositionSum_zero : minPositionSum 0 = 0 := by
  simp [minPositionSum]

private lemma minPositionSum_succ (r : ℕ) :
    minPositionSum (r + 1) = minPositionSum r + (r : ℤ) + 1 := by
  simp [minPositionSum, Finset.sum_range_succ]
  <;> ring

@[simp] private lemma maxPositionSum_zero (k : ℕ) : maxPositionSum k 0 = 0 := by
  simp [maxPositionSum]

private lemma maxPositionSum_succ (k r : ℕ) :
    maxPositionSum k (r + 1) = maxPositionSum k r + (k : ℤ) - r := by
  simp [maxPositionSum, Finset.sum_range_succ]
  <;> ring

private lemma two_mul_minPositionSum (r : ℕ) :
    2 * minPositionSum r = (r : ℤ) * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [minPositionSum_succ]
      push_cast
      nlinarith [ih]

private lemma two_mul_maxPositionSum (k r : ℕ) :
    2 * maxPositionSum k r = (r : ℤ) * (2 * k - r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [maxPositionSum_succ]
      push_cast
      nlinarith [ih]

private lemma maxPositionSum_succ_succ (k r : ℕ) :
    maxPositionSum (k + 1) (r + 1) =
      ((k + 1 : ℕ) : ℤ) + maxPositionSum k r := by
  have h₁ := two_mul_maxPositionSum (k + 1) (r + 1)
  have h₂ := two_mul_maxPositionSum k r
  push_cast at h₁ ⊢
  nlinarith

private lemma minPositionSum_le_maxPositionSum (k r : ℕ) (hrk : r ≤ k) :
    minPositionSum r ≤ maxPositionSum k r := by
  have h₁ := two_mul_minPositionSum r
  have h₂ := two_mul_maxPositionSum k r
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hrk' : (r : ℤ) ≤ k := by exact_mod_cast hrk
  nlinarith

private lemma adjacent_realization_bridge (k r : ℕ)
    (hr : 0 < r) (hrk : r < k) :
    (k : ℤ) + minPositionSum (r - 1) ≤ maxPositionSum (k - 1) r + 1 := by
  have h₁ := two_mul_minPositionSum (r - 1)
  have h₂ := two_mul_maxPositionSum (k - 1) r
  have hrsub : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  have hksub : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
  rw [hrsub] at h₁
  rw [hksub] at h₂
  have ha : (0 : ℤ) ≤ (r : ℤ) - 1 := by omega
  have hb : (0 : ℤ) ≤ (k : ℤ) - r - 1 := by omega
  have hab := mul_nonneg ha hb
  push_cast at h₁ h₂
  nlinarith

/-- Every integer between the sharp minimum and maximum sums is the sum of
an `r`-element subset of `{1, ..., k}`. -/
private lemma exists_subset_Icc_card_sum :
    ∀ (k r : ℕ), r ≤ k → ∀ z : ℤ,
      minPositionSum r ≤ z → z ≤ maxPositionSum k r →
        ∃ B : Finset ℤ,
          B ⊆ Finset.Icc 1 (k : ℤ) ∧ B.card = r ∧ ∑ x ∈ B, x = z := by
  intro k
  induction k with
  | zero =>
      intro r hr z hlo hhi
      have hr0 : r = 0 := by omega
      subst r
      have hlo' : (0 : ℤ) ≤ z := by simpa using hlo
      have hhi' : z ≤ (0 : ℤ) := by simpa using hhi
      have hz : z = 0 := le_antisymm hhi' hlo'
      exact ⟨∅, Finset.empty_subset _, by simp, by simp [hz]⟩
  | succ k ih =>
      intro r hr z hlo hhi
      cases r with
      | zero =>
          have hlo' : (0 : ℤ) ≤ z := by simpa using hlo
          have hhi' : z ≤ (0 : ℤ) := by simpa using hhi
          have hz : z = 0 := le_antisymm hhi' hlo'
          exact ⟨∅, Finset.empty_subset _, by simp, by simp [hz]⟩
      | succ r =>
          have hrk : r ≤ k := by omega
          by_cases hproper : r + 1 ≤ k
          · by_cases hleft : z ≤ maxPositionSum k (r + 1)
            · obtain ⟨B, hBsub, hBcard, hBsum⟩ :=
                ih (r + 1) hproper z hlo hleft
              refine ⟨B, hBsub.trans ?_, hBcard, hBsum⟩
              intro x hx
              simp only [Finset.mem_Icc] at hx ⊢
              omega
            · have hbridge := adjacent_realization_bridge (k + 1) (r + 1)
                  (by omega) (by omega)
              have hzlower : minPositionSum r ≤ z - (k + 1 : ℕ) := by
                push_cast at hbridge ⊢
                omega
              have hzupper : z - (k + 1 : ℕ) ≤ maxPositionSum k r := by
                rw [maxPositionSum_succ_succ] at hhi
                push_cast at hhi ⊢
                omega
              obtain ⟨B, hBsub, hBcard, hBsum⟩ :=
                ih r hrk (z - (k + 1 : ℕ)) hzlower hzupper
              have htop : ((k + 1 : ℕ) : ℤ) ∉ B := by
                intro hmem
                have hx := hBsub hmem
                simp only [Finset.mem_Icc] at hx
                omega
              refine ⟨insert (((k + 1 : ℕ) : ℤ)) B, ?_, ?_, ?_⟩
              · intro x hx
                simp only [Finset.mem_insert] at hx
                rcases hx with rfl | hx
                · simp
                · have hxb := hBsub hx
                  simp only [Finset.mem_Icc] at hxb ⊢
                  omega
              · rw [Finset.card_insert_of_notMem htop, hBcard]
              · rw [Finset.sum_insert htop, hBsum]
                push_cast
                omega
          · have hre : r = k := by omega
            subst r
            have hzlower : minPositionSum k ≤ z - (k + 1 : ℕ) := by
              rw [minPositionSum_succ] at hlo
              push_cast at hlo ⊢
              omega
            have hzupper : z - (k + 1 : ℕ) ≤ maxPositionSum k k := by
              rw [maxPositionSum_succ_succ] at hhi
              push_cast at hhi ⊢
              omega
            obtain ⟨B, hBsub, hBcard, hBsum⟩ :=
              ih k le_rfl (z - (k + 1 : ℕ)) hzlower hzupper
            have htop : ((k + 1 : ℕ) : ℤ) ∉ B := by
              intro hmem
              have hx := hBsub hmem
              simp only [Finset.mem_Icc] at hx
              omega
            refine ⟨insert (((k + 1 : ℕ) : ℤ)) B, ?_, ?_, ?_⟩
            · intro x hx
              simp only [Finset.mem_insert] at hx
              rcases hx with rfl | hx
              · simp
              · have hxb := hBsub hx
                simp only [Finset.mem_Icc] at hxb ⊢
                omega
            · rw [Finset.card_insert_of_notMem htop, hBcard]
            · rw [Finset.sum_insert htop, hBsum]
              push_cast
              omega

private def shiftEmbedding (b : ℤ) : ℤ ↪ ℤ where
  toFun x := b + x
  inj' := by
    intro x y h
    exact add_left_cancel h

@[simp] private lemma shiftEmbedding_apply (b x : ℤ) :
    shiftEmbedding b x = b + x := rfl

private def shiftFinset (b : ℤ) (B : Finset ℤ) : Finset ℤ :=
  B.map (shiftEmbedding b)

@[simp] private lemma card_shiftFinset (b : ℤ) (B : Finset ℤ) :
    (shiftFinset b B).card = B.card := by
  simp [shiftFinset]

private lemma sum_shiftFinset (b : ℤ) (B : Finset ℤ) :
    (∑ x ∈ shiftFinset b B, x) = B.card * b + ∑ x ∈ B, x := by
  rw [shiftFinset, Finset.sum_map]
  simp only [shiftEmbedding_apply]
  rw [Finset.sum_add_distrib]
  simp [mul_comm]

private lemma shiftFinset_subset_terminalInterval {N k : ℕ} {B : Finset ℤ}
    (hB : B ⊆ Finset.Icc 1 (k : ℤ)) :
    shiftFinset ((N : ℤ) - k) B ⊆ terminalInterval N k := by
  intro x hx
  rw [shiftFinset, Finset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := hB hy
  simp only [Finset.mem_Icc] at hy'
  simp only [terminalInterval, Finset.mem_Ioc]
  simp only [shiftEmbedding_apply]
  constructor <;> omega

private lemma sum_range_lower_identity (N k r : ℕ) :
    (∑ i ∈ Finset.range r, ((N : ℤ) - k + 1 + i)) =
      (r : ℤ) * ((N : ℤ) - k) + minPositionSum r := by
  calc
    _ = ∑ i ∈ Finset.range r,
        (((N : ℤ) - k) + ((i : ℤ) + 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [minPositionSum]
      <;> ring

private lemma terminal_sum_lower {N k r : ℕ} {B : Finset ℤ}
    (hB : B ⊆ terminalInterval N k) (hcard : B.card = r) :
    (r : ℤ) * (2 * N - 2 * k + r + 1) ≤ 2 * ∑ x ∈ B, x := by
  have hbound : ∀ x ∈ B, (N : ℤ) - k + 1 ≤ x := by
    intro x hx
    have hx' := hB hx
    simp only [terminalInterval, Finset.mem_Ioc] at hx'
    omega
  have hsum := Finset.sum_range_le_sum hbound
  rw [hcard, sum_range_lower_identity] at hsum
  have hmin := two_mul_minPositionSum r
  push_cast at hsum ⊢
  nlinarith

private lemma terminal_sum_upper {N k r : ℕ} {B : Finset ℤ}
    (hB : B ⊆ terminalInterval N k) (hcard : B.card = r) :
    2 * ∑ x ∈ B, x ≤ (r : ℤ) * (2 * N - r + 1) := by
  have hbound : ∀ x ∈ B, x ≤ (N : ℤ) := by
    intro x hx
    have hx' := hB hx
    exact (Finset.mem_Ioc.mp hx').2
  have hsum := Finset.sum_le_sum_range hbound
  rw [hcard] at hsum
  change (∑ x ∈ B, x) ≤ maxPositionSum N r at hsum
  have hmax := two_mul_maxPositionSum N r
  nlinarith

private lemma separated_card_bounds {N k r s : ℕ}
    (hkN : k ≤ N) (hrs : r < s) (hsk : s ≤ k)
    (hcrit : (k + 1) ^ 2 ≤ 4 * N + 1) :
    (r : ℤ) * (2 * N - r + 1) <
      (s : ℤ) * (2 * N - 2 * k + s + 1) := by
  have hcrit' : ((k : ℤ) + 1) ^ 2 ≤ 4 * (N : ℤ) + 1 := by
    exact_mod_cast hcrit
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hks : (s : ℤ) ≤ k := by exact_mod_cast hsk
  have hsquare : 0 ≤ (2 * (s : ℤ) - ((k : ℤ) + 1)) ^ 2 := sq_nonneg _
  have hcentral :
      4 * (s : ℤ) * ((k : ℤ) + 1 - s) ≤ ((k : ℤ) + 1) ^ 2 := by
    nlinarith
  have hfour :
      4 * ((s : ℤ) * ((k : ℤ) + 1 - s)) ≤ 4 * (N : ℤ) + 1 := by
    nlinarith
  have hproduct : (s : ℤ) * ((k : ℤ) + 1 - s) ≤ N := by
    omega
  have hrs' : (r : ℤ) ≤ (s : ℤ) - 1 := by omega
  have hsN : (s : ℤ) ≤ N := by
    exact_mod_cast hsk.trans hkN
  have hfac₁ : (0 : ℤ) ≤ ((s : ℤ) - 1) - r := by omega
  have hfac₂ :
      (0 : ℤ) ≤ 2 * (N : ℤ) + 1 - ((s : ℤ) - 1) - r := by
    omega
  have hmono := mul_nonneg hfac₁ hfac₂
  have hupp :
      (r : ℤ) * (2 * N - r + 1) ≤
        ((s : ℤ) - 1) * (2 * N - ((s : ℤ) - 1) + 1) := by
    nlinarith
  have hadj :
      ((s : ℤ) - 1) * (2 * N - ((s : ℤ) - 1) + 1) <
        (s : ℤ) * (2 * N - 2 * k + s + 1) := by
    nlinarith
  exact hupp.trans_lt hadj

private lemma exists_terminal_collision_of_gap {N k r : ℕ}
    (hkN : k ≤ N) (hr : 0 < r) (hrk : r < k)
    (hgap : N + 1 ≤ (r + 1) * (k - r)) :
    ∃ B C : Finset ℤ,
      B ⊆ terminalInterval N k ∧ B.card = r ∧
      C ⊆ terminalInterval N k ∧ C.card = r + 1 ∧
      (∑ x ∈ B, x) = ∑ x ∈ C, x := by
  let b : ℤ := (N : ℤ) - k
  let z : ℤ := b + minPositionSum (r + 1)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact sub_nonneg.mpr (by exact_mod_cast hkN)
  have hzlo : minPositionSum r ≤ z := by
    dsimp [z]
    rw [minPositionSum_succ]
    nlinarith
  have hzhi : z ≤ maxPositionSum k r := by
    have hminr := two_mul_minPositionSum r
    have hminsucc := two_mul_minPositionSum (r + 1)
    have hmaxr := two_mul_maxPositionSum k r
    have hgap' : (N : ℤ) + 1 ≤ ((r + 1) * (k - r) : ℕ) := by
      exact_mod_cast hgap
    have hkr : ((k - r : ℕ) : ℤ) = (k : ℤ) - r := by omega
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hkr] at hgap'
    dsimp [z, b]
    push_cast at hminsucc hmaxr
    nlinarith
  obtain ⟨P, hPsub, hPcard, hPsum⟩ :=
    exists_subset_Icc_card_sum k r (Nat.le_of_lt hrk) z hzlo hzhi
  have hrsucck : r + 1 ≤ k := by omega
  obtain ⟨Q, hQsub, hQcard, hQsum⟩ :=
    exists_subset_Icc_card_sum k (r + 1) hrsucck (minPositionSum (r + 1))
      le_rfl (minPositionSum_le_maxPositionSum k (r + 1) hrsucck)
  refine ⟨shiftFinset b P, shiftFinset b Q, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [b] using shiftFinset_subset_terminalInterval (N := N) (k := k) hPsub
  · simpa [hPcard]
  · simpa [b] using shiftFinset_subset_terminalInterval (N := N) (k := k) hQsub
  · simpa [hQcard]
  · rw [sum_shiftFinset, sum_shiftFinset, hPcard, hQcard, hPsum, hQsum]
    dsimp [z]
    push_cast
    ring

/-- Straus's exact criterion for the terminal interval construction. -/
theorem terminalInterval_isAdmissible_iff {N k : ℕ}
    (hkpos : 1 ≤ k) (hkN : k ≤ N) :
    IsAdmissible (terminalInterval N k) ↔ (k + 1) ^ 2 ≤ 4 * N + 1 := by
  constructor
  · intro hadmissible
    by_contra hcrit
    have hcrit' : 4 * N + 1 < (k + 1) ^ 2 := Nat.lt_of_not_ge hcrit
    have hdetermined :=
      (isAdmissible_iff_card_eq_of_sum_eq (terminalInterval_pos hkN)).mp hadmissible
    rcases Nat.even_or_odd' k with ⟨m, heven | hodd⟩
    · subst k
      have hm : 0 < m := by omega
      have hgap₀ : N + 1 ≤ m * (m + 1) := by nlinarith
      have hsub : 2 * m - m = m := by omega
      have hgap : N + 1 ≤ (m + 1) * (2 * m - m) := by
        rw [hsub, mul_comm]
        exact hgap₀
      obtain ⟨B, C, hBsub, hBcard, hCsub, hCcard, hsum⟩ :=
        exists_terminal_collision_of_gap hkN hm (by omega) hgap
      have := hdetermined B hBsub C hCsub hsum
      omega
    · subst k
      have hm : 0 < m := by
        by_contra hm'
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm'
        subst m
        norm_num at hcrit'
        omega
      have hgap₀ : N + 1 ≤ (m + 1) * (m + 1) := by nlinarith
      have hsub : 2 * m + 1 - m = m + 1 := by omega
      have hgap : N + 1 ≤ (m + 1) * (2 * m + 1 - m) := by
        rwa [hsub]
      obtain ⟨B, C, hBsub, hBcard, hCsub, hCcard, hsum⟩ :=
        exists_terminal_collision_of_gap hkN hm (by omega) hgap
      have := hdetermined B hBsub C hCsub hsum
      omega
  · intro hcrit
    rw [isAdmissible_iff_card_eq_of_sum_eq (terminalInterval_pos hkN)]
    intro B hBsub C hCsub hsum
    by_contra hcards
    rcases lt_or_gt_of_ne hcards with hlt | hgt
    · have hCk : C.card ≤ k := by
        simpa using (Finset.card_le_card hCsub)
      have hupper := terminal_sum_upper hBsub rfl
      have hlower := terminal_sum_lower hCsub rfl
      have hsep := separated_card_bounds hkN hlt hCk hcrit
      nlinarith
    · have hBk : B.card ≤ k := by
        simpa using (Finset.card_le_card hBsub)
      have hupper := terminal_sum_upper hCsub rfl
      have hlower := terminal_sum_lower hBsub rfl
      have hsep := separated_card_bounds hkN hgt hBk hcrit
      nlinarith

/-- The exact length furnished by the terminal-interval construction. -/
def strausLength (N : ℕ) : ℕ :=
  Nat.sqrt (4 * N + 1) - 1

/-- The terminal interval gives the sharp elementary lower bound for the
extremal function `k(N)`. -/
theorem strausLength_le_k (N : ℕ) : strausLength N ≤ k N := by
  by_cases hN : N = 0
  · subst N
    simp [strausLength]
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    let q := strausLength N
    have hsqrt2 : 2 ≤ Nat.sqrt (4 * N + 1) := by
      rw [Nat.le_sqrt']
      nlinarith
    have hqpos : 1 ≤ q := by
      dsimp [q, strausLength]
      omega
    have hsqrtlt : Nat.sqrt (4 * N + 1) < N + 2 := by
      rw [Nat.sqrt_lt']
      nlinarith
    have hqN : q ≤ N := by
      dsimp [q, strausLength]
      omega
    have hqsucc : q + 1 = Nat.sqrt (4 * N + 1) := by
      dsimp [q, strausLength]
      omega
    have hcriterion : (q + 1) ^ 2 ≤ 4 * N + 1 := by
      rw [hqsucc]
      exact Nat.sqrt_le' _
    have hadmissible : IsAdmissible (terminalInterval N q) :=
      (terminalInterval_isAdmissible_iff hqpos hqN).mpr hcriterion
    have hbounded : IsBoundedAdmissible N (terminalInterval N q) :=
      ⟨terminalInterval_bounded hqN, hadmissible⟩
    simpa [q] using card_le_k hbounded

end

end Erdos874
