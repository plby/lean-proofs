/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite cover of a logarithmic endpoint interval by the controlled disks.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointAlmostSure

namespace Erdos521

open MeasureTheory Filter Metric
open scoped BigOperators

noncomputable def intervalRootCount (ε : ℕ → ℝ) (n : ℕ) (l u : ℝ) : ℕ := by
  classical
  exact ((realRoots ε n).filter fun x ↦ x ∈ Set.Icc l u).card

theorem intervalRootCount_aemeasurable (n : ℕ) (l u : ℝ) :
    AEMeasurable (fun ε ↦ intervalRootCount ε n l u) sequenceLaw := by
  apply prefixStatistic_aemeasurable (n + 1)
  intro a b hab
  rw [intervalRootCount, intervalRootCount, realRoots_congr_prefix a b n hab]

theorem card_le_add_sum_of_cover {α ι : Type*} [DecidableEq α]
    (S F₀ : Finset α) (T : Finset ι) (F : ι → Finset α)
    (hcover : ∀ x ∈ S, x ∈ F₀ ∨ ∃ i ∈ T, x ∈ F i) :
    S.card ≤ F₀.card + ∑ i ∈ T, (F i).card := by
  have hsub : S ⊆ F₀ ∪ T.biUnion F := by
    intro x hx
    rcases hcover x hx with h | ⟨i, hi, hix⟩
    · exact Finset.mem_union.mpr (Or.inl h)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, hix⟩))
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (add_le_add le_rfl (Finset.card_biUnion_le)))

theorem exists_positive_interval_cover {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ T : Finset {t : ℝ // 0 < t}, ∀ u ∈ Set.Icc a C,
      ∃ t ∈ T, |u - (t : ℝ)| < (t : ℝ) / 8 := by
  classical
  have hcover : Set.Icc a C ⊆ ⋃ t : {t : ℝ // 0 < t}, ball (t : ℝ) ((t : ℝ) / 8) := by
    intro u hu
    have hu₀ : 0 < u := ha.trans_le hu.1
    exact Set.mem_iUnion.mpr ⟨⟨u, hu₀⟩, by simp [div_pos hu₀ (by norm_num : (0 : ℝ) < 8)]⟩
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : {t : ℝ // 0 < t} ↦ ball (t : ℝ) ((t : ℝ) / 8)) (fun _ ↦ isOpen_ball) hcover
  refine ⟨T, ?_⟩
  intro u hu
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hT hu)
  obtain ⟨htT, hdist⟩ := Set.mem_iUnion.mp ht
  exact ⟨t, htT, by simpa only [mem_ball, Real.dist_eq] using hdist⟩

theorem endpoint_interval_rootCount_le {a C : ℝ} (ha : 0 < a)
    (T : Finset {t : ℝ // 0 < t})
    (hT : ∀ u ∈ Set.Icc a C, ∃ t ∈ T, |u - (t : ℝ)| < (t : ℝ) / 8)
    {n : ℕ} (hn : 1 < n) (ε : ℕ → ℝ) (m : ℕ) :
    intervalRootCount ε m (endpointCenter C n) 1 ≤
      localRootCount ε m (endpointCenter a n) (endpointRadius a n) +
        ∑ t ∈ T, localRootCount ε m (endpointCenter (t : ℝ) n) (endpointRadius ((t : ℝ) / 8) n) := by
  classical
  let q := Real.log n / n
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hq : 0 < q := div_pos hlog hn₀
  apply card_le_add_sum_of_cover
  intro x hx
  obtain ⟨hxroot, hxI⟩ := Finset.mem_filter.mp hx
  let u := (1 - x) / q
  have hu₀ : 0 ≤ u := div_nonneg (sub_nonneg.mpr hxI.2) hq.le
  have huC : u ≤ C := by
    apply (div_le_iff₀ hq).mpr
    have hxlower := hxI.1
    change 1 - C * Real.log n / n ≤ x at hxlower
    dsimp [q]
    rw [mul_div_assoc] at hxlower
    linarith
  have hxu : x = 1 - u * q := by dsimp [u]; field_simp; ring
  have hid (t : ℝ) : |x - endpointCenter t n| = |u - t| * q := by
    rw [hxu]
    have heq : 1 - u * q - endpointCenter t n = -(u - t) * q := by
      dsimp [endpointCenter, q]
      ring
    rw [heq, abs_mul, abs_neg, abs_of_pos hq]
  by_cases hua : u ≤ 2 * a
  · apply Or.inl
    apply Finset.mem_filter.mpr ⟨hxroot, ?_⟩
    rw [hid]
    have hdist : |u - a| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
    have hmul := mul_le_mul_of_nonneg_right hdist hq.le
    simpa only [endpointRadius, q, mul_div_assoc] using hmul
  · obtain ⟨t, ht, hdist⟩ := hT u ⟨by linarith, huC⟩
    apply Or.inr
    refine ⟨t, ht, Finset.mem_filter.mpr ⟨hxroot, ?_⟩⟩
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hdist.le hq.le
    simpa only [endpointRadius, q, mul_div_assoc] using hmul

end Erdos521
