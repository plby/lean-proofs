/-
  Erdős problem 501 — the ZFC core, Section 2 of the profile-certificate draft.

  The two forcing-free measure lemmas.  Everything here is provable in ZFC:
  no forcing, no CH.

  * `Erdos501.pos_measure_Q`                 — Lemma 2.1 (positive-measure selection).
  * `Erdos501.infinite_measure_preservation` — Lemma 2.2 (preservation step).

  Notation matches the paper: for `E ⊆ S × S`,
      row of `t`   :  `E_t = {s | (t,s) ∈ E}`
      column of `s` : `E^s = {t | (t,s) ∈ E}`.
  Hypothesis (2.1) bounds every column: `μ (E^s) ≤ K`.
-/
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

namespace Erdos501

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ]

/-- The row `E_t = {s | (t,s) ∈ E}` is measurable when `E` is. -/
theorem measurableSet_row {E : Set (S × S)} (hE : MeasurableSet E) (t : S) :
    MeasurableSet {s | (t, s) ∈ E} :=
  hE.preimage measurable_prodMk_left

/-- The column `E^s = {t | (t,s) ∈ E}` is measurable when `E` is. -/
theorem measurableSet_col {E : Set (S × S)} (hE : MeasurableSet E) (s : S) :
    MeasurableSet {t | (t, s) ∈ E} :=
  hE.preimage (measurable_id.prodMk measurable_const)

/-- `t ↦ μ (C \ E_t) = μ {s ∈ C | (t,s) ∉ E}` is measurable. -/
theorem measurable_measure_diff_row {E : Set (S × S)} (hE : MeasurableSet E)
    {C : Set S} (hC : MeasurableSet C) :
    Measurable fun t => μ {s | s ∈ C ∧ (t, s) ∉ E} := by
  have hF : MeasurableSet {p : S × S | p.2 ∈ C ∧ p ∉ E} :=
    (hC.preimage measurable_snd).inter hE.compl
  exact measurable_measure_prodMk_left hF

/-- **Lemma 2.1**, measurability of the selection set
`Q(C) = {t ∈ C | μ (C \ E_t) = ∞}`. -/
theorem measurableSet_Q {E : Set (S × S)} (hE : MeasurableSet E)
    {C : Set S} (hC : MeasurableSet C) :
    MeasurableSet {t | t ∈ C ∧ μ {s | s ∈ C ∧ (t, s) ∉ E} = ∞} :=
  hC.inter ((measurable_measure_diff_row hE hC) (measurableSet_singleton ∞))

/-- **Lemma 2.1** (positive-measure selection).  If every column of `E` has
measure `≤ K < ∞` and `μ C = ∞`, then the selection set
`Q(C) = {t ∈ C | μ (C \ E_t) = ∞}` has positive measure. -/
theorem pos_measure_Q {E : Set (S × S)} (hE : MeasurableSet E) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hcol : ∀ s, μ {t | (t, s) ∈ E} ≤ K)
    {C : Set S} (hC : MeasurableSet C) (hCμ : μ C = ∞) :
    0 < μ {t | t ∈ C ∧ μ {s | s ∈ C ∧ (t, s) ∉ E} = ∞} := by
  classical
  set g : S → ℝ≥0∞ := fun t => μ {s | s ∈ C ∧ (t, s) ∉ E} with hg_def
  have hg_meas : Measurable g := measurable_measure_diff_row hE hC
  set Q : Set S := {t | t ∈ C ∧ g t = ∞} with hQ_def
  have hQ_meas : MeasurableSet Q := measurableSet_Q hE hC
  rw [pos_iff_ne_zero]
  intro hQ0
  ------------------------------------------------------------------
  -- `C \ Q` still has infinite measure.
  ------------------------------------------------------------------
  have hCQ : μ (C \ Q) = ∞ := by
    have h1 : μ (C \ Q) ≤ μ C := measure_mono diff_subset
    have h2 : μ C ≤ μ (C \ Q) + μ Q := by
      have hsub : C ⊆ (C \ Q) ∪ Q := by
        intro t ht; by_cases h : t ∈ Q
        · exact Or.inr h
        · exact Or.inl ⟨ht, h⟩
      calc μ C ≤ μ ((C \ Q) ∪ Q) := measure_mono hsub
        _ ≤ μ (C \ Q) + μ Q := measure_union_le _ _
    rw [hQ0, add_zero] at h2
    have hEq : μ (C \ Q) = μ C := le_antisymm h1 h2
    rw [hEq, hCμ]
  have hg_lt : ∀ t ∈ C \ Q, g t ≠ ∞ := by
    rintro t ⟨htC, htQ⟩ h; exact htQ ⟨htC, h⟩
  ------------------------------------------------------------------
  -- A finite-measure `D ⊆ C \ Q` with `μ D > K`.
  ------------------------------------------------------------------
  obtain ⟨j, hDj⟩ : ∃ j, K < μ ((C \ Q) ∩ spanningSets μ j) := by
    have hdir : Directed (· ⊆ ·) fun j => (C \ Q) ∩ spanningSets μ j :=
      Monotone.directed_le fun a b hab => inter_subset_inter_right _ (monotone_spanningSets μ hab)
    have hunion : ⋃ j, (C \ Q) ∩ spanningSets μ j = C \ Q := by
      rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
    have hsup : μ (C \ Q) = ⨆ j, μ ((C \ Q) ∩ spanningSets μ j) := by
      rw [← hdir.measure_iUnion, hunion]
    rw [hCQ] at hsup
    by_contra hcon
    push_neg at hcon
    exact hK (top_le_iff.mp (hsup ▸ iSup_le hcon))
  set D : Set S := (C \ Q) ∩ spanningSets μ j with hD_def
  have hD_meas : MeasurableSet D := (hC.diff hQ_meas).inter (measurableSet_spanningSets μ j)
  have hD_sub : D ⊆ C \ Q := inter_subset_left
  have hD_fin : μ D ≠ ∞ := ne_top_of_le_ne_top (measure_spanningSets_lt_top μ j).ne
    (measure_mono inter_subset_right)
  ------------------------------------------------------------------
  -- `Dk k = {t ∈ D | g t ≤ k}` increases to `D`; pick `k` with `μ (Dk k) > K`.
  ------------------------------------------------------------------
  set Dk : ℕ → Set S := fun k => {t | t ∈ D ∧ g t ≤ (k : ℝ≥0∞)} with hDk_def
  have hDk_meas : ∀ k, MeasurableSet (Dk k) := fun k =>
    hD_meas.inter (hg_meas measurableSet_Iic)
  have hDk_mono : Monotone Dk := fun a b hab t ht =>
    ⟨ht.1, le_trans ht.2 (by exact_mod_cast hab)⟩
  have hDk_union : ⋃ k, Dk k = D := by
    apply Set.eq_of_subset_of_subset
    · rintro t ht; rw [mem_iUnion] at ht; obtain ⟨k, htD, _⟩ := ht; exact htD
    · intro t htD
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hg_lt t (hD_sub htD))
      exact mem_iUnion.mpr ⟨k, htD, hk.le⟩
  obtain ⟨k, hk⟩ : ∃ k, K < μ (Dk k) := by
    have hdir : Directed (· ⊆ ·) Dk := hDk_mono.directed_le
    have hsupD : μ D = ⨆ k, μ (Dk k) := by rw [← hdir.measure_iUnion, hDk_union]
    rw [hsupD] at hDj
    exact lt_iSup_iff.mp hDj
  ------------------------------------------------------------------
  -- The exhaustion `Cn n = C ∩ spanningSets n`.
  ------------------------------------------------------------------
  set Cn : ℕ → Set S := fun n => C ∩ spanningSets μ n with hCn_def
  have hCn_meas : ∀ n, MeasurableSet (Cn n) := fun n =>
    hC.inter (measurableSet_spanningSets μ n)
  have hCn_fin : ∀ n, μ (Cn n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (measure_spanningSets_lt_top μ n).ne (measure_mono inter_subset_right)
  set M : ℕ → ℝ≥0∞ := fun n => μ (Cn n) with hM_def
  set d : ℝ≥0∞ := μ (Dk k) with hd_def
  have hd_fin : d ≠ ∞ := ne_top_of_le_ne_top hD_fin (measure_mono (fun t ht => ht.1))
  have hd_gt : K < d := hk
  ------------------------------------------------------------------
  -- Key inequality, uniform in `n`:  `(M n - k) * d ≤ K * M n`.
  ------------------------------------------------------------------
  have hrow_meas : ∀ n, Measurable fun t => μ ({s | (t, s) ∈ E} ∩ Cn n) := by
    intro n
    have hF : MeasurableSet {p : S × S | p ∈ E ∧ p.2 ∈ Cn n} :=
      hE.inter ((hCn_meas n).preimage measurable_snd)
    exact measurable_measure_prodMk_left hF
  have key : ∀ n, (M n - (k : ℝ≥0∞)) * d ≤ K * M n := by
    intro n
    set G : Set (S × S) := E ∩ (Dk k ×ˢ Cn n) with hG_def
    have hG_meas : MeasurableSet G := hE.inter ((hDk_meas k).prod (hCn_meas n))
    -- (A) product measure = row integral over `Dk k`
    have hA : (μ.prod μ) G = ∫⁻ t in Dk k, μ ({s | (t, s) ∈ E} ∩ Cn n) ∂μ := by
      rw [Measure.prod_apply hG_meas]
      have hfun : (fun t => μ (Prod.mk t ⁻¹' G))
          = (Dk k).indicator (fun t => μ ({s | (t, s) ∈ E} ∩ Cn n)) := by
        funext t
        by_cases ht : t ∈ Dk k
        · rw [indicator_of_mem ht]
          congr 1
          ext s
          simp only [hG_def, mem_preimage, mem_inter_iff, mem_prod, mem_setOf_eq]
          constructor
          · rintro ⟨hEs, _, hCns⟩; exact ⟨hEs, hCns⟩
          · rintro ⟨hEs, hCns⟩; exact ⟨hEs, ht, hCns⟩
        · rw [indicator_of_notMem ht]
          have hempty : Prod.mk t ⁻¹' G = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro s hs
            exact ht hs.2.1
          rw [hempty, measure_empty]
      rw [hfun, lintegral_indicator (hDk_meas k)]
    -- (B) product measure = column integral over `Cn n`
    have hB : (μ.prod μ) G = ∫⁻ s in Cn n, μ ({t | (t, s) ∈ E} ∩ Dk k) ∂μ := by
      rw [Measure.prod_apply_symm hG_meas]
      have hfun : (fun s => μ ((fun t => (t, s)) ⁻¹' G))
          = (Cn n).indicator (fun s => μ ({t | (t, s) ∈ E} ∩ Dk k)) := by
        funext s
        by_cases hs : s ∈ Cn n
        · rw [indicator_of_mem hs]
          congr 1
          ext t
          simp only [hG_def, mem_preimage, mem_inter_iff, mem_prod, mem_setOf_eq]
          constructor
          · rintro ⟨hEt, htDk, _⟩; exact ⟨hEt, htDk⟩
          · rintro ⟨hEt, htDk⟩; exact ⟨hEt, htDk, hs⟩
        · rw [indicator_of_notMem hs]
          have hempty : (fun t => (t, s)) ⁻¹' G = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro t ht'
            exact hs ht'.2.2
          rw [hempty, measure_empty]
      rw [hfun, lintegral_indicator (hCn_meas n)]
    -- lower bound
    have hlow : (M n - (k : ℝ≥0∞)) * d ≤ (μ.prod μ) G := by
      rw [hA]
      have hpt : ∀ t ∈ Dk k, (M n - (k : ℝ≥0∞)) ≤ μ ({s | (t, s) ∈ E} ∩ Cn n) := by
        intro t ht
        have hpart : μ (Cn n ∩ {s | (t, s) ∈ E}) + μ (Cn n \ {s | (t, s) ∈ E}) = M n :=
          measure_inter_add_diff _ (measurableSet_row hE t)
        have hle_k : μ (Cn n \ {s | (t, s) ∈ E}) ≤ (k : ℝ≥0∞) := by
          refine le_trans (measure_mono ?_) ht.2
          intro s hs; exact ⟨hs.1.1, hs.2⟩
        have hMle : M n ≤ μ ({s | (t, s) ∈ E} ∩ Cn n) + (k : ℝ≥0∞) := by
          rw [inter_comm, ← hpart]
          exact add_le_add le_rfl hle_k
        exact tsub_le_iff_right.mpr hMle
      have hcst : ∫⁻ _ in Dk k, (M n - (k : ℝ≥0∞)) ∂μ = (M n - (k : ℝ≥0∞)) * d := by
        rw [setLIntegral_const]
      rw [← hcst]
      exact setLIntegral_mono (hrow_meas n) hpt
    -- upper bound
    have hup : (μ.prod μ) G ≤ K * M n := by
      rw [hB]
      have hcst : ∫⁻ _ in Cn n, K ∂μ = K * M n := by rw [setLIntegral_const]
      rw [← hcst]
      exact setLIntegral_mono measurable_const
        (fun s _ => le_trans (measure_mono inter_subset_left) (hcol s))
    exact le_trans hlow hup
  ------------------------------------------------------------------
  -- Uniform bound `B` on `M n`, contradicting `⨆ M n = μ C = ∞`.
  ------------------------------------------------------------------
  have hdK_ne0 : d - K ≠ 0 := fun h => (not_le.mpr hd_gt) (tsub_eq_zero_iff_le.mp h)
  have hdK_fin : d - K ≠ ∞ := ne_top_of_le_ne_top hd_fin tsub_le_self
  set B : ℝ≥0∞ := K * (k : ℝ≥0∞) * (d - K)⁻¹ + (k : ℝ≥0∞) with hB_def
  have hB_fin : B ≠ ∞ := by
    rw [hB_def]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hK ?_) ?_, ?_⟩
    · exact ENNReal.natCast_ne_top k
    · exact ENNReal.inv_ne_top.mpr hdK_ne0
    · exact ENNReal.natCast_ne_top k
  have hMB : ∀ n, M n ≤ B := by
    intro n
    by_cases hcase : M n ≤ (k : ℝ≥0∞)
    · exact le_trans hcase (by rw [hB_def]; exact le_add_self)
    · push_neg at hcase
      have hkleM : (k : ℝ≥0∞) ≤ M n := le_of_lt hcase
      have hp_fin : M n - (k : ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top (hCn_fin n) tsub_le_self
      have hMeq : M n = (M n - (k : ℝ≥0∞)) + (k : ℝ≥0∞) := (tsub_add_cancel_of_le hkleM).symm
      have hkey := key n
      have hd_eq : d = K + (d - K) := (add_tsub_cancel_of_le (le_of_lt hd_gt)).symm
      have e1 : (M n - (k : ℝ≥0∞)) * d
          = (M n - (k : ℝ≥0∞)) * K + (M n - (k : ℝ≥0∞)) * (d - K) := by
        conv_lhs => rw [hd_eq, mul_add]
      have e2 : K * M n = K * (M n - (k : ℝ≥0∞)) + K * (k : ℝ≥0∞) := by
        rw [← mul_add, ← hMeq]
      rw [e1, e2, mul_comm (M n - (k : ℝ≥0∞)) K] at hkey
      have hKp_fin : K * (M n - (k : ℝ≥0∞)) ≠ ∞ := ENNReal.mul_ne_top hK hp_fin
      have hcancel : (M n - (k : ℝ≥0∞)) * (d - K) ≤ K * (k : ℝ≥0∞) :=
        (ENNReal.add_le_add_iff_left hKp_fin).mp hkey
      have hple : (M n - (k : ℝ≥0∞)) ≤ K * (k : ℝ≥0∞) * (d - K)⁻¹ := by
        have hmul := mul_le_mul_left hcancel (d - K)⁻¹
        rwa [mul_assoc, ENNReal.mul_inv_cancel hdK_ne0 hdK_fin, mul_one] at hmul
      calc M n = (M n - (k : ℝ≥0∞)) + (k : ℝ≥0∞) := hMeq
        _ ≤ K * (k : ℝ≥0∞) * (d - K)⁻¹ + (k : ℝ≥0∞) := by gcongr
        _ = B := by rw [hB_def]
  have hsupM : (⨆ n, M n) = μ C := by
    have hdir : Directed (· ⊆ ·) Cn :=
      Monotone.directed_le fun a b hab => inter_subset_inter_right _ (monotone_spanningSets μ hab)
    have hunion : ⋃ n, Cn n = C := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
    rw [hM_def, ← hdir.measure_iUnion, hunion]
  have hle : (⨆ n, M n) ≤ B := iSup_le hMB
  rw [hsupM, hCμ] at hle
  exact hB_fin (top_le_iff.mp hle)

/-- **Lemma 2.2** (preservation step).  Assume the column bound and that `x`
has null fibers.  If `t ∈ Q(C)` (so `μ (C \ E_t) = ∞`), then removing the
row `E_t`, the column `E^t = {s | (s,t) ∈ E}`, and the fiber `{s | x s = x t}`
from `C` leaves a measurable set of infinite measure. -/
theorem infinite_measure_preservation {E : Set (S × S)} (hE : MeasurableSet E)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hcol : ∀ s, μ {t | (t, s) ∈ E} ≤ K)
    {x : S → ℝ} (hx : Measurable x) (hfib : ∀ a : ℝ, μ {s | x s = a} = 0)
    {C : Set S} (hC : MeasurableSet C) (t : S)
    (htQ : μ {s | s ∈ C ∧ (t, s) ∉ E} = ∞) :
    MeasurableSet (C \ ({s | (t, s) ∈ E} ∪ {s | (s, t) ∈ E} ∪ {s | x s = x t}))
      ∧ μ (C \ ({s | (t, s) ∈ E} ∪ {s | (s, t) ∈ E} ∪ {s | x s = x t})) = ∞ := by
  set row : Set S := {s | (t, s) ∈ E} with hrow_def
  set col : Set S := {s | (s, t) ∈ E} with hcol_def
  set fib : Set S := {s | x s = x t} with hfib_def
  set W : Set S := col ∪ fib with hW_def
  set C' : Set S := C \ (row ∪ col ∪ fib) with hC'_def
  have hrow_meas : MeasurableSet row := measurableSet_row hE t
  have hcol_meas : MeasurableSet col := hE.preimage (measurable_id.prodMk measurable_const)
  have hfib_meas : MeasurableSet fib := hx (measurableSet_singleton (x t))
  have hC'_meas : MeasurableSet C' := hC.diff ((hrow_meas.union hcol_meas).union hfib_meas)
  refine ⟨hC'_meas, ?_⟩
  have hCrow : μ (C \ row) = ∞ := by
    have hEq : C \ row = {s | s ∈ C ∧ (t, s) ∉ E} := by
      ext s; simp only [hrow_def, mem_diff, mem_setOf_eq]
    rw [hEq, htQ]
  have hsub : C \ row ⊆ C' ∪ W := by
    intro s hs
    by_cases hW : s ∈ W
    · exact Or.inr hW
    · refine Or.inl ⟨hs.1, ?_⟩
      simp only [hW_def, mem_union, not_or] at hW
      simp only [mem_union]
      rintro ((h | h) | h)
      · exact hs.2 h
      · exact hW.1 h
      · exact hW.2 h
  have hWfin : μ W ≤ K := by
    calc μ W ≤ μ col + μ fib := measure_union_le _ _
      _ ≤ K + 0 := add_le_add (hcol t) (le_of_eq (hfib (x t)))
      _ = K := add_zero K
  have hchain : μ (C \ row) ≤ μ C' + μ W :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  rw [hCrow] at hchain
  by_contra hC'ne
  exact (ENNReal.add_ne_top.mpr ⟨hC'ne, ne_top_of_le_ne_top hK hWfin⟩) (top_le_iff.mp hchain)

end Erdos501
