/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core

namespace Erdos1166

open Filter MeasureTheory
open scoped BigOperators ENNReal

/-- HLOZ's source location `L_m^k`, using the literal recursive time (2.7). -/
noncomputable def recursiveLevelCreationSite
    (s : ℕ → Site) (m k : ℕ) : Site :=
  s (recursiveExactlyKSitesReachLevel m k s).untopA

/-- The source event `U_m^j` from HLOZ (2.10): throughout
`(T_m^(j-1), T_m^j]`, the path avoids all sites created at the previous
level-`m` thresholds. -/
def hlozAvoidanceEvent (m j : ℕ) : Set (ℕ → Site) :=
  {s | ∀ n : ℕ,
    recursiveExactlyKSitesReachLevel m (j - 1) s < (n : WithTop ℕ) →
    (n : WithTop ℕ) ≤ recursiveExactlyKSitesReachLevel m j s →
    ∀ i : ℕ, 1 ≤ i → i < j →
      s n ≠ recursiveLevelCreationSite s m i}

/-- Direct-threshold version of `U_m^j`, used internally before rewriting
the literal recursive times by `recursiveExactlyKSitesReachLevel_eq`. -/
def hlozDirectAvoidanceEvent (m j : ℕ) : Set (ℕ → Site) :=
  {s | ∀ n : ℕ,
    firstKSitesReachLevel m (j - 1) s < (n : WithTop ℕ) →
    (n : WithTop ℕ) ≤ firstKSitesReachLevel m j s →
    ∀ i : ℕ, 1 ≤ i → i < j →
      s n ≠ levelCreationSite s m i}

theorem localTime_lt_of_visit_Ioc
    (s : ℕ → Site) (x : Site) {a n b : ℕ}
    (han : a < n) (hnb : n ≤ b) (hsn : s n = x) :
    localTime s a x < localTime s b x := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have haq : a ≤ q := by omega
  have hqb : q + 1 ≤ b := by omega
  have hstep : localTime s (q + 1) x = localTime s q x + 1 := by
    rw [localTime_succ]
    simp [hsn]
  have hleft := localTime_mono (s := s) haq x
  have hright := localTime_mono (s := s) hqb x
  omega

theorem localTime_eq_of_avoid_Ioc
    (s : ℕ → Site) (x : Site) {a b : ℕ} (hab : a ≤ b)
    (havoid : ∀ n : ℕ, a < n → n ≤ b → s n ≠ x) :
    localTime s b x = localTime s a x := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      simp [ha]
  | succ b ih =>
      by_cases habEq : a = b + 1
      · simp [habEq]
      · have hab' : a ≤ b := by omega
        have hprev : localTime s b x = localTime s a x := by
          apply ih hab'
          intro n han hnb
          exact havoid n han (by omega)
        rw [localTime_succ, hprev]
        have hne : s (b + 1) ≠ x := havoid (b + 1) (by omega) (by omega)
        simp [hne]

/-- For `m ≥ 2`, the literal source event and the direct-threshold version
are pointwise identical. -/
theorem mem_hlozAvoidanceEvent_iff_direct
    (s : ℕ → Site) (m j : ℕ) (hm : 2 ≤ m) (hj : 2 ≤ j) :
    s ∈ hlozAvoidanceEvent m j ↔ s ∈ hlozDirectAvoidanceEvent m j := by
  have hprev : recursiveExactlyKSitesReachLevel m (j - 1) s =
      firstKSitesReachLevel m (j - 1) s := by
    calc
      _ = recursiveExactlyKSitesReachLevel m ((j - 2) + 1) s := by
        congr 2 <;> omega
      _ = firstExactlyKSitesReachLevel m ((j - 2) + 1) s :=
        recursiveExactlyKSitesReachLevel_eq s m (j - 2) hm
      _ = firstKSitesReachLevel m ((j - 2) + 1) s :=
        firstExactlyKSitesReachLevel_eq s m ((j - 2) + 1) (by omega)
      _ = firstKSitesReachLevel m (j - 1) s := by congr 2 <;> omega
  have hcur : recursiveExactlyKSitesReachLevel m j s =
      firstKSitesReachLevel m j s := by
    calc
      _ = recursiveExactlyKSitesReachLevel m ((j - 1) + 1) s := by
        congr 2 <;> omega
      _ = firstExactlyKSitesReachLevel m ((j - 1) + 1) s :=
        recursiveExactlyKSitesReachLevel_eq s m (j - 1) hm
      _ = firstKSitesReachLevel m ((j - 1) + 1) s :=
        firstExactlyKSitesReachLevel_eq s m ((j - 1) + 1) (by omega)
      _ = firstKSitesReachLevel m j s := by congr 2 <;> omega
  have hsite : ∀ i : ℕ, 1 ≤ i → i < j →
      recursiveLevelCreationSite s m i = levelCreationSite s m i := by
    intro i hi hij
    unfold recursiveLevelCreationSite levelCreationSite
    have ht : recursiveExactlyKSitesReachLevel m i s =
        firstKSitesReachLevel m i s := by
      calc
        _ = recursiveExactlyKSitesReachLevel m ((i - 1) + 1) s := by
          congr 2 <;> omega
        _ = firstExactlyKSitesReachLevel m ((i - 1) + 1) s :=
          recursiveExactlyKSitesReachLevel_eq s m (i - 1) hm
        _ = firstKSitesReachLevel m ((i - 1) + 1) s :=
          firstExactlyKSitesReachLevel_eq s m ((i - 1) + 1) (by omega)
        _ = firstKSitesReachLevel m i s := by congr 2 <;> omega
    rw [ht]
  simp only [hlozAvoidanceEvent, hlozDirectAvoidanceEvent, Set.mem_ofPred_eq]
  rw [hprev, hcur]
  constructor <;> intro h n hn hnj i hi hij
  · simpa only [hsite i hi hij] using h n hn hnj i hi hij
  · simpa only [hsite i hi hij] using h n hn hnj i hi hij

private theorem firstKSitesReachLevel_ne_top_of_le
    (s : ℕ → Site) (m : ℕ) {i k : ℕ} (hik : i ≤ k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    firstKSitesReachLevel m i s ≠ ⊤ := by
  intro hitop
  have hle := firstKSitesReachLevel_mono_k s m hik
  rw [hitop] at hle
  exact hkfinite (top_unique hle)

private theorem firstKSitesReachLevel_untopA_le
    (s : ℕ → Site) (m : ℕ) {i k : ℕ} (hik : i ≤ k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    (firstKSitesReachLevel m i s).untopA ≤
      (firstKSitesReachLevel m k s).untopA := by
  have hifinite := firstKSitesReachLevel_ne_top_of_le s m hik hkfinite
  have hle := firstKSitesReachLevel_mono_k s m hik
  have hiCoe : ((firstKSitesReachLevel m i s).untopA : WithTop ℕ) =
      firstKSitesReachLevel m i s := by
    rw [WithTop.untopA_eq_untop hifinite]
    exact WithTop.coe_untop _ hifinite
  have hkCoe : ((firstKSitesReachLevel m k s).untopA : WithTop ℕ) =
      firstKSitesReachLevel m k s := by
    rw [WithTop.untopA_eq_untop hkfinite]
    exact WithTop.coe_untop _ hkfinite
  exact WithTop.coe_le_coe.mp (hiCoe.trans_le (hle.trans_eq hkCoe.symm))

/-- The finite set `{L_m^1, ..., L_m^k}` of direct level-creation sites. -/
noncomputable def levelCreationSitesUpTo
    (s : ℕ → Site) (m k : ℕ) : Finset Site :=
  (Finset.Icc 1 k).image (levelCreationSite s m)

/-- At a finite positive threshold, its level set consists exactly of the
creation sites `L_m^1, ..., L_m^k`. -/
theorem sitesAtLeastLevel_at_threshold_eq_creationSites
    (s : ℕ → Site) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    sitesAtLeastLevel s (firstKSitesReachLevel m k s).untopA m =
      levelCreationSitesUpTo s m k := by
  let T := firstKSitesReachLevel m k s
  let t : ℕ := T.untopA
  have hsubset : levelCreationSitesUpTo s m k ⊆
      sitesAtLeastLevel s t m := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    have hifinite : firstKSitesReachLevel m i s ≠ ⊤ :=
      firstKSitesReachLevel_ne_top_of_le s m hik hkfinite
    have htime : (firstKSitesReachLevel m i s).untopA ≤ t := by
      exact firstKSitesReachLevel_untopA_le s m hik hkfinite
    have hlocal : localTime s (firstKSitesReachLevel m i s).untopA
        (levelCreationSite s m i) = m :=
      levelCreationSite_localTime_eq s m i hm (by omega) hifinite
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨(firstKSitesReachLevel m i s).untopA,
        Finset.mem_range.mpr (by omega), rfl⟩
    · exact hlocal.ge.trans (localTime_mono (s := s) htime _)
  apply Finset.Subset.antisymm
  · have hcardThreshold :
        (sitesAtLeastLevel s t m).card = k := by
      exact card_at_firstKSitesReachLevel_eq s m k hk hkfinite
    have hinj : Set.InjOn (levelCreationSite s m) (↑(Finset.Icc 1 k)) := by
      intro i hi j hj heq
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      rcases lt_trichotomy i j with hij | hij | hij
      · have hjfinite := firstKSitesReachLevel_ne_top_of_le s m hjk hkfinite
        exact False.elim ((levelCreationSite_ne_of_lt s m hm (by omega) hij
          hjfinite) heq)
      · exact hij
      · have hifinite := firstKSitesReachLevel_ne_top_of_le s m hik hkfinite
        exact False.elim ((levelCreationSite_ne_of_lt s m hm (by omega) hij
          hifinite) heq.symm)
    have hcardCreation : (levelCreationSitesUpTo s m k).card = k := by
      unfold levelCreationSitesUpTo
      rw [(Finset.card_image_iff.mpr hinj), Nat.card_Icc]
      omega
    have heq := Finset.eq_of_subset_of_card_le hsubset (by
      rw [hcardThreshold, hcardCreation])
    rw [← heq]
  · exact hsubset

/-- The `k`-site version of the threshold event in (2.9). -/
def hlozThresholdTimeEventK (m k : ℕ) : Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m k s < firstKSitesReachLevel (m + 1) 1 s}

theorem hlozThresholdTimeEventK_four (m : ℕ) :
    hlozThresholdTimeEventK m 4 = hlozThresholdTimeEvent m := rfl

/-- Before the first level-`m+1` threshold, every inter-threshold segment
avoids all previously created level-`m` sites. -/
theorem hlozThresholdTimeEventK_imp_directAvoidance
    (s : ℕ → Site) (m k j : ℕ) (hm : 0 < m)
    (hj : 2 ≤ j) (hjk : j ≤ k)
    (hM : s ∈ hlozThresholdTimeEventK m k) :
    s ∈ hlozDirectAvoidanceEvent m j := by
  change firstKSitesReachLevel m k s <
    firstKSitesReachLevel (m + 1) 1 s at hM
  have hkfinite : firstKSitesReachLevel m k s ≠ ⊤ := ne_top_of_lt hM
  intro n hnprev hnj i hi hij
  have hjfinite : firstKSitesReachLevel m j s ≠ ⊤ :=
    firstKSitesReachLevel_ne_top_of_le s m hjk hkfinite
  have hifinite : firstKSitesReachLevel m i s ≠ ⊤ :=
    firstKSitesReachLevel_ne_top_of_le s m (by omega) hkfinite
  have hTiPrev : firstKSitesReachLevel m i s ≤
      firstKSitesReachLevel m (j - 1) s :=
    firstKSitesReachLevel_mono_k s m (by omega)
  have hiCoe : ((firstKSitesReachLevel m i s).untopA : WithTop ℕ) =
      firstKSitesReachLevel m i s := by
    rw [WithTop.untopA_eq_untop hifinite]
    exact WithTop.coe_untop _ hifinite
  have htin : (firstKSitesReachLevel m i s).untopA < n := by
    have htin' : ((firstKSitesReachLevel m i s).untopA : WithTop ℕ) <
        (n : WithTop ℕ) := hiCoe.trans_lt (hTiPrev.trans_lt hnprev)
    exact WithTop.coe_lt_coe.mp htin'
  intro hsni
  have hlocalCreation : localTime s (firstKSitesReachLevel m i s).untopA
      (levelCreationSite s m i) = m :=
    levelCreationSite_localTime_eq s m i hm (by omega) hifinite
  have hlocalLt : localTime s (firstKSitesReachLevel m i s).untopA
      (levelCreationSite s m i) < localTime s n (levelCreationSite s m i) :=
    localTime_lt_of_visit_Ioc s (levelCreationSite s m i) htin (le_refl n) hsni
  have hlevel : m + 1 ≤ localTime s n (levelCreationSite s m i) := by
    omega
  have hvisited : levelCreationSite s m i ∈ visitedSites s n := by
    apply Finset.mem_image.mpr
    exact ⟨n, by simp, hsni⟩
  have hplusMem : (sitesAtLeastLevel s n (m + 1)).card ∈ Set.Ici 1 := by
    have hx : levelCreationSite s m i ∈ sitesAtLeastLevel s n (m + 1) :=
      Finset.mem_filter.mpr ⟨hvisited, hlevel⟩
    simp only [Set.mem_Ici]
    have := Finset.card_pos.mpr ⟨_, hx⟩
    omega
  have hplusLe : firstKSitesReachLevel (m + 1) 1 s ≤ (n : WithTop ℕ) :=
    hittingAfter_le_of_mem
      (u := fun q s ↦ (sitesAtLeastLevel s q (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (i := n) (ω := s) (Nat.zero_le n) hplusMem
  have hjkTime := firstKSitesReachLevel_mono_k s m hjk
  have : firstKSitesReachLevel (m + 1) 1 s ≤
      firstKSitesReachLevel m k s :=
    hplusLe.trans (hnj.trans hjkTime)
  exact (not_lt_of_ge this) hM

/-- Avoidance on each successive source interval keeps an earlier creation
site at local time exactly `m` through the later threshold. -/
theorem levelCreationSite_localTime_at_later_threshold_of_directAvoidance
    (s : ℕ → Site) (m i k : ℕ) (hm : 0 < m) (hi : 1 ≤ i)
    (hik : i ≤ k) (hkfinite : firstKSitesReachLevel m k s ≠ ⊤)
    (hU : ∀ j : ℕ, i < j → j ≤ k →
      s ∈ hlozDirectAvoidanceEvent m j) :
    localTime s (firstKSitesReachLevel m k s).untopA
      (levelCreationSite s m i) = m := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases heq : i = k + 1
      · subst i
        exact levelCreationSite_localTime_eq s m (k + 1) hm (by omega) hkfinite
      · have hik' : i ≤ k := by omega
        have hkfinite' : firstKSitesReachLevel m k s ≠ ⊤ :=
          firstKSitesReachLevel_ne_top_of_le s m (Nat.le_succ k) hkfinite
        have hprev : localTime s (firstKSitesReachLevel m k s).untopA
            (levelCreationSite s m i) = m := by
          apply ih hik' hkfinite'
          intro j hij hjk
          exact hU j hij (hjk.trans (Nat.le_succ k))
        have htime : (firstKSitesReachLevel m k s).untopA ≤
            (firstKSitesReachLevel m (k + 1) s).untopA :=
          firstKSitesReachLevel_untopA_le s m (Nat.le_succ k) hkfinite
        have hkCoe : ((firstKSitesReachLevel m k s).untopA : WithTop ℕ) =
            firstKSitesReachLevel m k s := by
          rw [WithTop.untopA_eq_untop hkfinite']
          exact WithTop.coe_untop _ hkfinite'
        have hsuccCoe :
            ((firstKSitesReachLevel m (k + 1) s).untopA : WithTop ℕ) =
              firstKSitesReachLevel m (k + 1) s := by
          rw [WithTop.untopA_eq_untop hkfinite]
          exact WithTop.coe_untop _ hkfinite
        have hsegment := localTime_eq_of_avoid_Ioc s
          (levelCreationSite s m i) htime (by
            intro n hn hnb
            have hUk : s ∈ hlozDirectAvoidanceEvent m (k + 1) :=
              hU (k + 1) (by omega) (le_refl _)
            apply hUk n
            · change firstKSitesReachLevel m k s < (n : WithTop ℕ)
              rw [← hkCoe]
              exact WithTop.coe_lt_coe.mpr hn
            · rw [← hsuccCoe]
              exact WithTop.coe_le_coe.mpr hnb
            · exact hi
            · omega)
        exact hsegment.trans hprev

/-- The converse direction of (2.10), with the necessary explicit finiteness
premise for the last threshold. HLOZ use this on the probability-one set on
which all the displayed thresholds are finite. -/
theorem directAvoidance_imp_hlozThresholdTimeEventK
    (s : ℕ → Site) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤)
    (hU : ∀ j : ℕ, 2 ≤ j → j ≤ k →
      s ∈ hlozDirectAvoidanceEvent m j) :
    s ∈ hlozThresholdTimeEventK m k := by
  let T := firstKSitesReachLevel m k s
  let t : ℕ := T.untopA
  have hTcoe : (t : WithTop ℕ) = T := by
    dsimp only [t, T]
    rw [WithTop.untopA_eq_untop hkfinite]
    exact WithTop.coe_untop _ hkfinite
  have hlevelEq : sitesAtLeastLevel s t m = levelCreationSitesUpTo s m k := by
    exact sitesAtLeastLevel_at_threshold_eq_creationSites s m k hm hk hkfinite
  have hplusEmpty : sitesAtLeastLevel s t (m + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hxplus
    have hxbase : x ∈ sitesAtLeastLevel s t m := by
      rcases Finset.mem_filter.mp hxplus with ⟨hxv, hxl⟩
      exact Finset.mem_filter.mpr ⟨hxv, by omega⟩
    rw [hlevelEq] at hxbase
    rcases Finset.mem_image.mp hxbase with ⟨i, hiIcc, hix⟩
    have hi : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    have hik : i ≤ k := (Finset.mem_Icc.mp hiIcc).2
    have hlocal : localTime s t (levelCreationSite s m i) = m := by
      apply levelCreationSite_localTime_at_later_threshold_of_directAvoidance
        s m i k hm hi hik hkfinite
      intro j hij hjk
      exact hU j (by omega) hjk
    have hxplusLocal : m + 1 ≤ localTime s t x :=
      (Finset.mem_filter.mp hxplus).2
    rw [← hix] at hxplusLocal
    omega
  change T < firstKSitesReachLevel (m + 1) 1 s
  rw [← hTcoe]
  by_contra hnot
  have hplusLe : firstKSitesReachLevel (m + 1) 1 s ≤ (t : WithTop ℕ) := by
    simpa only [not_lt] using hnot
  change hittingAfter
      (fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
      (Set.Ici 1) 0 s ≤ (t : WithTop ℕ) at hplusLe
  have hex : ∃ q ∈ Set.Icc 0 t,
      (sitesAtLeastLevel s q (m + 1)).card ∈ Set.Ici 1 :=
    (hittingAfter_le_iff
      (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (ω := s) (i := t)).mp hplusLe
  rcases hex with ⟨q, hq, hqmem⟩
  have hqnonempty : (sitesAtLeastLevel s q (m + 1)).Nonempty :=
    Finset.card_pos.mp (by
      have : 1 ≤ (sitesAtLeastLevel s q (m + 1)).card := hqmem
      omega)
  rcases hqnonempty with ⟨x, hx⟩
  have hxAtT := sitesAtLeastLevel_mono_time
    (s := s) (m := m + 1) hq.2 hx
  rw [hplusEmpty] at hxAtT
  simpa using hxAtT

/-- Exact pathwise form of HLOZ (2.10), before rewriting to the literal
recursive stopping times. The finiteness conjunct is logically necessary
for arbitrary paths; it is automatic on the almost-sure class used by HLOZ. -/
theorem mem_hlozThresholdTimeEventK_iff_finite_and_directAvoidance
    (s : ℕ → Site) (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    s ∈ hlozThresholdTimeEventK m k ↔
      firstKSitesReachLevel m k s ≠ ⊤ ∧
        ∀ j : ℕ, 2 ≤ j → j ≤ k →
          s ∈ hlozDirectAvoidanceEvent m j := by
  constructor
  · intro hM
    have hkfinite : firstKSitesReachLevel m k s ≠ ⊤ := by
      exact ne_top_of_lt hM
    refine ⟨hkfinite, ?_⟩
    intro j hj hjk
    exact hlozThresholdTimeEventK_imp_directAvoidance s m k j hm hj hjk hM
  · rintro ⟨hkfinite, hU⟩
    exact directAvoidance_imp_hlozThresholdTimeEventK
      s m k hm hk hkfinite hU

/-- Exact pathwise form of (2.10) using HLOZ's literal recursive times and
locations. -/
theorem mem_hlozThresholdTimeEventK_iff_finite_and_avoidance
    (s : ℕ → Site) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k) :
    s ∈ hlozThresholdTimeEventK m k ↔
      firstKSitesReachLevel m k s ≠ ⊤ ∧
        ∀ j : ℕ, 2 ≤ j → j ≤ k → s ∈ hlozAvoidanceEvent m j := by
  rw [mem_hlozThresholdTimeEventK_iff_finite_and_directAvoidance
    s m k (by omega) hk]
  constructor
  · rintro ⟨hfinite, hU⟩
    refine ⟨hfinite, ?_⟩
    intro j hj hjk
    exact (mem_hlozAvoidanceEvent_iff_direct s m j hm hj).mpr (hU j hj hjk)
  · rintro ⟨hfinite, hU⟩
    refine ⟨hfinite, ?_⟩
    intro j hj hjk
    exact (mem_hlozAvoidanceEvent_iff_direct s m j hm hj).mp (hU j hj hjk)

/-- The literal formula printed as (2.10), valid on the finite-threshold
class. This statement is generic in `k` (and hence includes `k ≤ 4`). -/
theorem mem_hlozThresholdTimeEventK_iff_avoidance_of_finite
    (s : ℕ → Site) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    s ∈ hlozThresholdTimeEventK m k ↔
      ∀ j : ℕ, 2 ≤ j → j ≤ k → s ∈ hlozAvoidanceEvent m j := by
  rw [mem_hlozThresholdTimeEventK_iff_finite_and_avoidance s m k hm hk]
  constructor
  · exact And.right
  · exact fun hU ↦ ⟨hfinite, hU⟩

/-- Literal four-site source identity on the finite-threshold class:
`M_m^4 = U_m^2 ∩ U_m^3 ∩ U_m^4`. -/
theorem mem_hlozThresholdTimeEvent_iff_avoidance_two_three_four_of_finite
    (s : ℕ → Site) (m : ℕ) (hm : 2 ≤ m)
    (hfinite : firstKSitesReachLevel m 4 s ≠ ⊤) :
    s ∈ hlozThresholdTimeEvent m ↔
      s ∈ hlozAvoidanceEvent m 2 ∧
      s ∈ hlozAvoidanceEvent m 3 ∧
      s ∈ hlozAvoidanceEvent m 4 := by
  rw [← hlozThresholdTimeEventK_four]
  rw [mem_hlozThresholdTimeEventK_iff_finite_and_avoidance s m 4 hm (by omega)]
  constructor
  · rintro ⟨_, hU⟩
    exact ⟨hU 2 (by omega) (by omega),
      hU 3 (by omega) (by omega), hU 4 (by omega) (by omega)⟩
  · rintro ⟨hU2, hU3, hU4⟩
    refine ⟨hfinite, ?_⟩
    intro j hj hj4
    interval_cases j
    · exact hU2
    · exact hU3
    · exact hU4

/-- Unconditional equality of path events. This is the exact totalized
version of HLOZ (2.10) for the extended-valued stopping times used here. -/
theorem hlozThresholdTimeEvent_eq_finite_inter_avoidances
    (m : ℕ) (hm : 2 ≤ m) :
    hlozThresholdTimeEvent m =
      {s | firstKSitesReachLevel m 4 s ≠ ⊤} ∩
        hlozAvoidanceEvent m 2 ∩
        hlozAvoidanceEvent m 3 ∩
        hlozAvoidanceEvent m 4 := by
  ext s
  rw [← hlozThresholdTimeEventK_four]
  rw [mem_hlozThresholdTimeEventK_iff_finite_and_avoidance s m 4 hm (by omega)]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hfinite, hU⟩
    exact ⟨⟨⟨hfinite, hU 2 (by omega) (by omega)⟩,
      hU 3 (by omega) (by omega)⟩, hU 4 (by omega) (by omega)⟩
  · rintro ⟨⟨⟨hfinite, hU2⟩, hU3⟩, hU4⟩
    refine ⟨hfinite, ?_⟩
    intro j hj hj4
    interval_cases j
    · exact hU2
    · exact hU3
    · exact hU4

end Erdos1166
