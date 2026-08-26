/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Stability
import ErdosProblems.Erdos547b.TreePartition
import Mathlib.Data.List.Sort
import Mathlib.Tactic

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma65

theorem list_sum_nonpos {l : List ℝ} (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.sum_cons]
      have hx := h x (by simp)
      have hl : ∀ y ∈ l, y ≤ 0 := by
        intro y hy
        exact h y (by simp [hy])
      linarith [ih hl]

/-- A decreasing finite real sequence with total sum zero has nonnegative
prefix sums. This is the cumulative-sum observation in Zhao's proof of
Fact 6.4. -/
theorem sum_take_nonneg_of_pairwise_ge_of_sum_eq_zero
    (l : List ℝ) (hsorted : l.Pairwise (· ≥ ·)) (htotal : l.sum = 0)
    (j : ℕ) : 0 ≤ (l.take j).sum := by
  by_contra! hneg
  have hx : ∃ x ∈ l.take j, x < 0 := by
    by_contra h
    have hnonneg : ∀ x ∈ l.take j, 0 ≤ x := by
      intro x hxmem
      exact le_of_not_gt fun hxneg => h ⟨x, hxmem, hxneg⟩
    exact (not_le_of_gt hneg) (List.sum_nonneg hnonneg)
  obtain ⟨x, hxp, hxneg⟩ := hx
  have hpw : (l.take j ++ l.drop j).Pairwise (· ≥ ·) := by
    rw [List.take_append_drop]
    exact hsorted
  have hcross := (List.pairwise_append.mp hpw).2.2
  have hq : ∀ y ∈ l.drop j, y ≤ 0 := by
    intro y hy
    exact (hcross x hxp y hy).trans hxneg.le
  have hqsum : (l.drop j).sum ≤ 0 := list_sum_nonpos hq
  have hsum := List.sum_take_add_sum_drop l j
  rw [htotal] at hsum
  linarith
/-- Greedy crossing of a positive target by terms bounded by `Δ`: the
shortest prefix whose sum reaches `s` lies strictly above `s - Δ` and at
most `s`. -/
theorem exists_prefix_sum_gt_sub_le
    (l : List ℝ) {Δ s : ℝ}
    (hnonneg : ∀ x ∈ l, 0 ≤ x) (hbound : ∀ x ∈ l, x ≤ Δ)
    (hspos : 0 < s) (hs : s ≤ l.sum) :
    ∃ j : ℕ, s - Δ < (l.take j).sum ∧ (l.take j).sum ≤ s := by
  induction l generalizing s with
  | nil => simp at hs; linarith
  | cons x l ih =>
      have hx0 : 0 ≤ x := hnonneg x (by simp)
      have hxΔ : x ≤ Δ := hbound x (by simp)
      have hnonneg' : ∀ y ∈ l, 0 ≤ y := by
        intro y hy
        exact hnonneg y (by simp [hy])
      have hbound' : ∀ y ∈ l, y ≤ Δ := by
        intro y hy
        exact hbound y (by simp [hy])
      by_cases hsx : s ≤ x
      · by_cases heq : s = x
        · refine ⟨1, ?_, ?_⟩
          · simp [heq]
            have hΔpos : 0 < Δ := lt_of_lt_of_le hspos (heq ▸ hxΔ)
            linarith
          · simp [heq]
        · refine ⟨0, ?_, by simp [hspos.le]⟩
          simp only [List.take_zero, List.sum_nil]
          have hxs : s < x := lt_of_le_of_ne hsx heq
          linarith
      · have hxs : x < s := lt_of_not_ge hsx
        have htarget : s - x ≤ l.sum := by
          simp only [List.sum_cons] at hs
          linarith
        obtain ⟨j, hjlo, hjhi⟩ := ih hnonneg' hbound' (sub_pos.mpr hxs) htarget
        refine ⟨j + 1, ?_, ?_⟩
        · rw [show j + 1 = Nat.succ j by omega, List.take_succ_cons, List.sum_cons]
          linarith
        · rw [show j + 1 = Nat.succ j by omega, List.take_succ_cons, List.sum_cons]
          linarith

/-- Sorting a finite index list by a real score puts the scores in decreasing
order. -/
theorem pairwise_score_mergeSort {ι : Type*} (score : ι → ℝ) (l : List ι) :
    (l.mergeSort fun i j => decide (score i ≥ score j)).Pairwise
      (fun i j => score i ≥ score j) := by
  have h := List.pairwise_mergeSort
    (le := fun i j => decide (score i ≥ score j))
    (fun i j k hij hjk => by
      simp only [decide_eq_true_eq] at hij hjk ⊢
      exact hjk.trans hij)
    (fun i j => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (score j) (score i)) l
  simpa only [decide_eq_true_eq] using h

/-- **Zhao 2011, Fact 6.4.**  The positivity of `a` and `b` is implicit in
the paper's fractions `s/a` and `t/b`; it is made explicit here because Lean
defines division by zero.  The second conclusion below is the stronger bound
proved in Zhao's argument (`t`, rather than only `t - Δ`). -/
theorem zhaoFact6_4
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ai bi : ι → ℝ) (Δ a b s t : ℝ)
    (hai0 : ∀ i, 0 ≤ ai i) (_hbi0 : ∀ i, 0 ≤ bi i)
    (haiΔ : ∀ i, ai i ≤ Δ) (_hbiΔ : ∀ i, bi i ≤ Δ)
    (hsumA : ∑ i, ai i = a) (hsumB : ∑ i, bi i = b)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (ht : 0 < t)
    (hratio : s / a + t / b ≤ 1) :
    ∃ I₁ I₂ : Finset ι,
      Disjoint I₁ I₂ ∧ I₁ ∪ I₂ = Finset.univ ∧
      s - Δ < ∑ i ∈ I₁, ai i ∧
      (∑ i ∈ I₁, ai i) ≤ s ∧
      t ≤ ∑ i ∈ I₂, bi i := by
  classical
  have hΔ : 0 < Δ := by
    by_contra h
    have hΔ0 : Δ ≤ 0 := le_of_not_gt h
    have hz : ∀ i, ai i = 0 := by
      intro i
      exact le_antisymm ((haiΔ i).trans hΔ0) (hai0 i)
    have : a = 0 := by simpa [hz] using hsumA.symm
    linarith
  have hsa : s < a := by
    have htdiv : 0 < t / b := div_pos ht hb
    have hsdiv : s / a < 1 := by linarith
    exact (div_lt_one ha).mp hsdiv
  let score : ι → ℝ := fun i => ai i / a - bi i / b
  let order : List ι :=
    Finset.univ.toList.mergeSort fun i j => decide (score i ≥ score j)
  have hperm : order.Perm Finset.univ.toList := by
    exact List.mergeSort_perm _ _
  have horderNodup : order.Nodup := by
    rw [List.nodup_mergeSort]
    exact Finset.nodup_toList _
  have hbaseA : (Finset.univ.toList.map ai).sum = ∑ i, ai i := by
    rw [← List.sum_toFinset ai (Finset.nodup_toList Finset.univ)]
    simp
  have hbaseB : (Finset.univ.toList.map bi).sum = ∑ i, bi i := by
    rw [← List.sum_toFinset bi (Finset.nodup_toList Finset.univ)]
    simp
  have horderA : (order.map ai).sum = a := by
    calc
      (order.map ai).sum = (Finset.univ.toList.map ai).sum :=
        (hperm.map ai).sum_eq
      _ = ∑ i, ai i := hbaseA
      _ = a := hsumA
  have horderB : (order.map bi).sum = b := by
    calc
      (order.map bi).sum = (Finset.univ.toList.map bi).sum :=
        (hperm.map bi).sum_eq
      _ = ∑ i, bi i := hbaseB
      _ = b := hsumB
  have horderScore : (order.map score).sum = 0 := by
    have hcalc : (order.map score).sum =
        (order.map ai).sum / a - (order.map bi).sum / b := by
      induction order with
      | nil => simp
      | cons i l ih =>
          simp only [List.map_cons, List.sum_cons, score]
          rw [ih]
          ring
    rw [hcalc, horderA, horderB, div_self ha.ne', div_self hb.ne']
    norm_num
  have hscoreSorted : (order.map score).Pairwise (· ≥ ·) := by
    apply List.Pairwise.map score
      (fun i j hij => hij)
      (pairwise_score_mergeSort score Finset.univ.toList)
  have horderNonneg : ∀ x ∈ order.map ai, 0 ≤ x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hai0 i
  have horderBound : ∀ x ∈ order.map ai, x ≤ Δ := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact haiΔ i
  obtain ⟨j, hjlower, hjupper⟩ :=
    exists_prefix_sum_gt_sub_le (order.map ai) horderNonneg horderBound hs (by
      rw [horderA]
      exact hsa.le)
  let I₁ : Finset ι := (order.take j).toFinset
  let I₂ : Finset ι := Finset.univ \ I₁
  have htakeNodup : (order.take j).Nodup :=
    (List.take_sublist j order).nodup horderNodup
  have hI₁A : ∑ i ∈ I₁, ai i = ((order.map ai).take j).sum := by
    rw [show ((order.map ai).take j) = (order.take j).map ai by simp]
    exact List.sum_toFinset ai htakeNodup
  have hI₁B : ∑ i ∈ I₁, bi i = ((order.map bi).take j).sum := by
    rw [show ((order.map bi).take j) = (order.take j).map bi by simp]
    exact List.sum_toFinset bi htakeNodup
  have hI₁subset : I₁ ⊆ Finset.univ := Finset.subset_univ _
  have hscorePrefix : 0 ≤ ((order.map score).take j).sum :=
    sum_take_nonneg_of_pairwise_ge_of_sum_eq_zero
      (order.map score) hscoreSorted horderScore j
  have hratioPrefix :
      (∑ i ∈ I₁, bi i) / b ≤ (∑ i ∈ I₁, ai i) / a := by
    rw [show ((order.map score).take j) = (order.take j).map score by simp]
      at hscorePrefix
    rw [← List.sum_toFinset score htakeNodup] at hscorePrefix
    change 0 ≤ ∑ i ∈ I₁, (ai i / a - bi i / b) at hscorePrefix
    rw [Finset.sum_sub_distrib] at hscorePrefix
    calc
      (∑ i ∈ I₁, bi i) / b = ∑ i ∈ I₁, bi i / b :=
        Finset.sum_div I₁ bi b
      _ ≤ ∑ i ∈ I₁, ai i / a := by linarith
      _ = (∑ i ∈ I₁, ai i) / a := (Finset.sum_div I₁ ai a).symm
  have hI₁Ale : (∑ i ∈ I₁, ai i) ≤ s := by
    rw [hI₁A]
    exact hjupper
  have hratioPrefix' : (∑ i ∈ I₁, bi i) / b ≤ s / a :=
    hratioPrefix.trans ((div_le_div_iff_of_pos_right ha).2 hI₁Ale)
  have hcompB : (∑ i ∈ I₂, bi i) + (∑ i ∈ I₁, bi i) = b := by
    have h := Finset.sum_sdiff hI₁subset (f := bi)
    simpa only [I₂, hsumB] using h
  have hI₂B : t ≤ ∑ i ∈ I₂, bi i := by
    have htdiv : t / b ≤ 1 - s / a := by linarith
    have hdiv : t / b ≤ (∑ i ∈ I₂, bi i) / b := by
      rw [show (∑ i ∈ I₂, bi i) = b - ∑ i ∈ I₁, bi i by linarith [hcompB]]
      rw [sub_div, div_self hb.ne']
      linarith
    exact (div_le_div_iff_of_pos_right hb).mp hdiv
  refine ⟨I₁, I₂, Finset.disjoint_sdiff, ?_, ?_, hI₁Ale, hI₂B⟩
  · exact Finset.union_sdiff_of_subset hI₁subset
  · rw [hI₁A]
    exact hjlower

/-- The literal conclusion of Fact 6.4, obtained from the stronger second
bound in `zhaoFact6_4`. -/
theorem zhaoFact6_4_source_conclusion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ai bi : ι → ℝ) (Δ a b s t : ℝ)
    (hai0 : ∀ i, 0 ≤ ai i) (hbi0 : ∀ i, 0 ≤ bi i)
    (haiΔ : ∀ i, ai i ≤ Δ) (hbiΔ : ∀ i, bi i ≤ Δ)
    (hsumA : ∑ i, ai i = a) (hsumB : ∑ i, bi i = b)
    (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (ht : 0 < t)
    (hratio : s / a + t / b ≤ 1) :
    ∃ I₁ I₂ : Finset ι,
      Disjoint I₁ I₂ ∧ I₁ ∪ I₂ = Finset.univ ∧
      s - Δ < ∑ i ∈ I₁, ai i ∧
      t - Δ < ∑ i ∈ I₂, bi i := by
  obtain ⟨I₁, I₂, hdis, hunion, hA, _hAle, hB⟩ :=
    zhaoFact6_4 ai bi Δ a b s t hai0 hbi0 haiΔ hbiΔ
      hsumA hsumB ha hb hs ht hratio
  have hΔ : 0 < Δ := by
    by_contra h
    have hΔ0 : Δ ≤ 0 := le_of_not_gt h
    have hz : ∀ i, ai i = 0 := by
      intro i
      exact le_antisymm ((haiΔ i).trans hΔ0) (hai0 i)
    have : a = 0 := by simpa [hz] using hsumA.symm
    linarith
  exact ⟨I₁, I₂, hdis, hunion, hA, lt_of_lt_of_le (sub_lt_self t hΔ) hB⟩

/-!
## Lemma 6.5: the reduced-matching degree core

For a matching edge `i`, Zhao writes `aᵢ = deg(A,i)` and
`bᵢ = deg(B,i)`.  Since an edge has two clusters of size `N`, both are at
most `2N`.  The next theorem is precisely the numerical step in Part 2 of
Lemma 6.5: its single minimum-degree hypothesis produces the partition
`M = Mₐ ∪ Mᵦ` required by Part 1, with the strict `3γn` margins of (6.10).
-/

/-- **Zhao 2011, Lemma 6.5 Part 2, degree core.** -/
theorem zhaoLemma6_5_part2_degree_core
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degAOn degBOn : ι → ℝ)
    (N margin treeSize fa fb degA degB : ℝ)
    (hA0 : ∀ i, 0 ≤ degAOn i) (hB0 : ∀ i, 0 ≤ degBOn i)
    (hAbound : ∀ i, degAOn i ≤ 2 * N)
    (hBbound : ∀ i, degBOn i ≤ 2 * N)
    (hsumA : ∑ i, degAOn i = degA)
    (hsumB : ∑ i, degBOn i = degB)
    (_hN0 : 0 ≤ N) (hmargin : 0 < margin)
    (hcluster : 2 * N < margin)
    (htree0 : 0 ≤ treeSize) (hfa0 : 0 ≤ fa) (hfb0 : 0 ≤ fb)
    (hforest : fa + fb ≤ treeSize)
    (hcapacity : treeSize ≤ min degA degB - 8 * margin) :
    ∃ Mₐ Mᵦ : Finset ι,
      Disjoint Mₐ Mᵦ ∧ Mₐ ∪ Mᵦ = Finset.univ ∧
      fa + 3 * margin < ∑ i ∈ Mₐ, degAOn i ∧
      fb + 3 * margin < ∑ i ∈ Mᵦ, degBOn i := by
  have hminimum : treeSize + 8 * margin ≤ min degA degB := by
    linarith
  have hcapA : treeSize + 8 * margin ≤ degA :=
    hminimum.trans (min_le_left _ _)
  have hcapB : treeSize + 8 * margin ≤ degB :=
    hminimum.trans (min_le_right _ _)
  have hdenom : 0 < treeSize + 8 * margin := by linarith
  have hdegA : 0 < degA := hdenom.trans_le hcapA
  have hdegB : 0 < degB := hdenom.trans_le hcapB
  have hspos : 0 < fa + 4 * margin := by linarith
  have htpos : 0 < fb + 4 * margin := by linarith
  have hsnonneg : 0 ≤ fa + 4 * margin := hspos.le
  have htnonneg : 0 ≤ fb + 4 * margin := htpos.le
  have hsfrac :
      (fa + 4 * margin) / degA ≤
        (fa + 4 * margin) / (treeSize + 8 * margin) :=
    div_le_div_of_nonneg_left hsnonneg hdenom hcapA
  have htfrac :
      (fb + 4 * margin) / degB ≤
        (fb + 4 * margin) / (treeSize + 8 * margin) :=
    div_le_div_of_nonneg_left htnonneg hdenom hcapB
  have hnum : fa + 4 * margin + (fb + 4 * margin) ≤
      treeSize + 8 * margin := by
    linarith
  have hcommon :
      (fa + 4 * margin) / (treeSize + 8 * margin) +
          (fb + 4 * margin) / (treeSize + 8 * margin) ≤ 1 := by
    rw [← add_div]
    exact (div_le_one hdenom).2 hnum
  have hratio :
      (fa + 4 * margin) / degA + (fb + 4 * margin) / degB ≤ 1 := by
    linarith
  obtain ⟨Mₐ, Mᵦ, hdis, hunion, hMa, _hMaUpper, hMb⟩ :=
    zhaoFact6_4 degAOn degBOn (2 * N) degA degB
      (fa + 4 * margin) (fb + 4 * margin)
      hA0 hB0 hAbound hBbound hsumA hsumB hdegA hdegB hspos htpos hratio
  refine ⟨Mₐ, Mᵦ, hdis, hunion, ?_, ?_⟩
  · linarith
  · linarith

/-- Continuation form of Lemma 6.5 Part 2.  Any already-proved Part 1
embedding conclusion can be discharged after the degree core constructs its
matching partition.  Taking `P` to be `T' ⊑ G` gives the logical assembly in
the paper verbatim. -/
theorem zhaoLemma6_5_part2_of_part1
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degAOn degBOn : ι → ℝ)
    (N margin treeSize fa fb degA degB : ℝ)
    (hA0 : ∀ i, 0 ≤ degAOn i) (hB0 : ∀ i, 0 ≤ degBOn i)
    (hAbound : ∀ i, degAOn i ≤ 2 * N)
    (hBbound : ∀ i, degBOn i ≤ 2 * N)
    (hsumA : ∑ i, degAOn i = degA)
    (hsumB : ∑ i, degBOn i = degB)
    (hN0 : 0 ≤ N) (hmargin : 0 < margin)
    (hcluster : 2 * N < margin)
    (htree0 : 0 ≤ treeSize) (hfa0 : 0 ≤ fa) (hfb0 : 0 ≤ fb)
    (hforest : fa + fb ≤ treeSize)
    (hcapacity : treeSize ≤ min degA degB - 8 * margin)
    (P : Prop)
    (part1 : ∀ Mₐ Mᵦ : Finset ι,
      Disjoint Mₐ Mᵦ → Mₐ ∪ Mᵦ = Finset.univ →
      fa + 3 * margin < ∑ i ∈ Mₐ, degAOn i →
      fb + 3 * margin < ∑ i ∈ Mᵦ, degBOn i → P) : P := by
  obtain ⟨Mₐ, Mᵦ, hdis, hunion, hA, hB⟩ :=
    zhaoLemma6_5_part2_degree_core degAOn degBOn
      N margin treeSize fa fb degA degB hA0 hB0 hAbound hBbound
      hsumA hsumB hN0 hmargin hcluster htree0 hfa0 hfb0 hforest hcapacity
  exact part1 Mₐ Mᵦ hdis hunion hA hB

/-- Source-shaped specialization: `N` is the common cluster size, `n` is
Zhao's target tree size, and `margin = γn`.  The natural numbers `treeSize`,
`fa`, and `fb` are respectively `||T'||`, `||Fₐ||`, and `||Fᵦ||`. -/
theorem zhaoLemma6_5_part2_source_parameters
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degAOn degBOn : ι → ℝ)
    (N n treeSize fa fb : ℕ) (γ degA degB : ℝ)
    (hA0 : ∀ i, 0 ≤ degAOn i) (hB0 : ∀ i, 0 ≤ degBOn i)
    (hAbound : ∀ i, degAOn i ≤ 2 * (N : ℝ))
    (hBbound : ∀ i, degBOn i ≤ 2 * (N : ℝ))
    (hsumA : ∑ i, degAOn i = degA)
    (hsumB : ∑ i, degBOn i = degB)
    (hcluster : 2 * (N : ℝ) < γ * (n : ℝ))
    (hforest : fa + fb ≤ treeSize)
    (hcapacity : (treeSize : ℝ) ≤
      min degA degB - 8 * (γ * (n : ℝ))) :
    ∃ Mₐ Mᵦ : Finset ι,
      Disjoint Mₐ Mᵦ ∧ Mₐ ∪ Mᵦ = Finset.univ ∧
      (fa : ℝ) + 3 * (γ * (n : ℝ)) < ∑ i ∈ Mₐ, degAOn i ∧
      (fb : ℝ) + 3 * (γ * (n : ℝ)) < ∑ i ∈ Mᵦ, degBOn i := by
  have hmargin : 0 < γ * (n : ℝ) := by
    have hN : 0 ≤ 2 * (N : ℝ) := by positivity
    linarith
  have hforest' : (fa : ℝ) + (fb : ℝ) ≤ (treeSize : ℝ) := by
    exact_mod_cast hforest
  exact zhaoLemma6_5_part2_degree_core degAOn degBOn
    (N : ℝ) (γ * (n : ℝ)) (treeSize : ℝ) (fa : ℝ) (fb : ℝ) degA degB
    hA0 hB0 hAbound hBbound hsumA hsumB (by positivity) hmargin hcluster
    (by positivity) (by positivity) (by positivity) hforest' hcapacity

/-- Graph-valued version of the continuation theorem.  It turns the
matching-degree hypothesis of Part 2 into the exact tree-copy conclusion as
soon as Lemma 6.5 Part 1 is supplied for every admissible partition. -/
theorem zhaoLemma6_5_part2_tree_embedding
    {ι τ V : Type*} [Fintype ι] [DecidableEq ι]
    (T : SimpleGraph τ) (G : SimpleGraph V)
    (degAOn degBOn : ι → ℝ)
    (N margin treeSize fa fb degA degB : ℝ)
    (hA0 : ∀ i, 0 ≤ degAOn i) (hB0 : ∀ i, 0 ≤ degBOn i)
    (hAbound : ∀ i, degAOn i ≤ 2 * N)
    (hBbound : ∀ i, degBOn i ≤ 2 * N)
    (hsumA : ∑ i, degAOn i = degA)
    (hsumB : ∑ i, degBOn i = degB)
    (hN0 : 0 ≤ N) (hmargin : 0 < margin)
    (hcluster : 2 * N < margin)
    (htree0 : 0 ≤ treeSize) (hfa0 : 0 ≤ fa) (hfb0 : 0 ≤ fb)
    (hforest : fa + fb ≤ treeSize)
    (hcapacity : treeSize ≤ min degA degB - 8 * margin)
    (part1 : ∀ Mₐ Mᵦ : Finset ι,
      Disjoint Mₐ Mᵦ → Mₐ ∪ Mᵦ = Finset.univ →
      (fa + 3 * margin < ∑ i ∈ Mₐ, degAOn i) →
      (fb + 3 * margin < ∑ i ∈ Mᵦ, degBOn i) → (T ⊑ G)) :
    T ⊑ G := by
  exact zhaoLemma6_5_part2_of_part1 degAOn degBOn
    N margin treeSize fa fb degA degB hA0 hB0 hAbound hBbound
    hsumA hsumB hN0 hmargin hcluster htree0 hfa0 hfb0 hforest hcapacity
    (T ⊑ G) part1

#print axioms zhaoFact6_4
#print axioms zhaoFact6_4_source_conclusion
#print axioms zhaoLemma6_5_part2_degree_core
#print axioms zhaoLemma6_5_part2_source_parameters
#print axioms zhaoLemma6_5_part2_tree_embedding

end Erdos547b.ZhaoLemma65
