/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Basic

/-!
# The maximal-local-time clock for Erdős Problem 1165

This file contains the deterministic change of clock used in the proof of
Hao--Li--Okada--Zheng.  It applies to every lattice-valued path; probability,
recurrence, and the Markov property do not occur here.
-/

open Filter Set

namespace Erdos1165

/-! ## Threshold sets and their one-step evolution -/

/-- Sites whose local time through `n` is at least `m`. -/
def thresholdSites (s : WalkPath) (n m : ℕ) : Finset Point :=
  (visitedSites s n).filter fun x ↦ m ≤ localTime s n x

/-- Number of sites whose local time through `n` is at least `m`. -/
def thresholdCount (s : WalkPath) (n m : ℕ) : ℕ :=
  (thresholdSites s n m).card

@[simp] theorem mem_thresholdSites (s : WalkPath) (n m : ℕ) (x : Point) :
    x ∈ thresholdSites s n m ↔ x ∈ visitedSites s n ∧ m ≤ localTime s n x := by
  simp [thresholdSites]

theorem mem_visitedSites_iff_localTime_pos (s : WalkPath) (n : ℕ) (x : Point) :
    x ∈ visitedSites s n ↔ 0 < localTime s n x := by
  constructor
  · exact localTimePrefix_pos_of_mem_visited
  · intro hx
    by_contra hnot
    have hzero : localTime s n x = 0 :=
      localTimePrefix_eq_zero_of_notMem_visited hnot
    rw [hzero] at hx
    omega

theorem mem_thresholdSites_iff (s : WalkPath) (n m : ℕ) (x : Point) (hm : 0 < m) :
    x ∈ thresholdSites s n m ↔ m ≤ localTime s n x := by
  rw [mem_thresholdSites]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    rw [mem_visitedSites_iff_localTime_pos]
    omega

theorem localTime_succ (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s (n + 1) x = localTime s n x + if s (n + 1) = x then 1 else 0 := by
  unfold localTime localTimePrefix pathPrefix
  nth_rewrite 1 [Fin.univ_castSuccEmb]
  have hfilter :
      ((Finset.univ.map Fin.castSuccEmb).filter
          (fun j : Fin (n + 2) ↦ s (j : ℕ) = x)).card =
        (Finset.univ.filter (fun j : Fin (n + 1) ↦ s (j : ℕ) = x)).card := by
    rw [Finset.filter_map, Finset.card_map]
    rfl
  by_cases h : s (n + 1) = x
  · have hlast : s ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = x := by
      change s (n + 1) = x
      exact h
    rw [Finset.filter_cons]
    simp only [if_pos hlast, Finset.card_cons, hfilter, if_pos h]
  · have hlast : ¬s ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = x := by
      change ¬s (n + 1) = x
      exact h
    rw [Finset.filter_cons]
    simp only [if_neg hlast, hfilter, if_neg h, Nat.add_zero]

theorem localTime_mono_time (s : WalkPath) (x : Point) :
    Monotone fun n ↦ localTime s n x := by
  apply monotone_nat_of_le_succ
  intro n
  rw [localTime_succ]
  omega

theorem thresholdSites_mono_time (s : WalkPath) (m : ℕ) :
    Monotone fun n ↦ thresholdSites s n m := by
  intro a b hab x hx
  by_cases hm : m = 0
  · subst m
    simp only [mem_thresholdSites] at hx ⊢
    refine ⟨?_, Nat.zero_le _⟩
    rw [mem_visitedSites_iff_localTime_pos] at hx ⊢
    exact lt_of_lt_of_le hx.1 (localTime_mono_time s x hab)
  · rw [mem_thresholdSites_iff s a m x (Nat.pos_of_ne_zero hm)] at hx
    rw [mem_thresholdSites_iff s b m x (Nat.pos_of_ne_zero hm)]
    exact hx.trans (localTime_mono_time s x hab)

theorem thresholdCount_mono_time (s : WalkPath) (m : ℕ) :
    Monotone fun n ↦ thresholdCount s n m := by
  intro a b hab
  exact Finset.card_le_card (thresholdSites_mono_time s m hab)

theorem thresholdSites_antitone_level (s : WalkPath) (n : ℕ) :
    Antitone fun m ↦ thresholdSites s n m := by
  intro m q hmq x hx
  rw [mem_thresholdSites] at hx ⊢
  exact ⟨hx.1, hmq.trans hx.2⟩

theorem thresholdCount_antitone_level (s : WalkPath) (n : ℕ) :
    Antitone fun m ↦ thresholdCount s n m := by
  intro m q hmq
  exact Finset.card_le_card (thresholdSites_antitone_level s n hmq)

theorem thresholdSites_succ_subset_insert (s : WalkPath) (n m : ℕ) :
    thresholdSites s (n + 1) m ⊆ insert (s (n + 1)) (thresholdSites s n m) := by
  intro x hx
  by_cases hnew : x = s (n + 1)
  · simp [hnew]
  · simp only [Finset.mem_insert, hnew, false_or]
    have hlocal : localTime s (n + 1) x = localTime s n x := by
      rw [localTime_succ]
      simp [Ne.symm hnew]
    by_cases hm : m = 0
    · subst m
      rw [mem_thresholdSites] at hx ⊢
      refine ⟨?_, Nat.zero_le _⟩
      rw [mem_visitedSites_iff_localTime_pos] at hx ⊢
      simpa [hlocal] using hx.1
    · rw [mem_thresholdSites_iff s (n + 1) m x (Nat.pos_of_ne_zero hm)] at hx
      rw [mem_thresholdSites_iff s n m x (Nat.pos_of_ne_zero hm)]
      simpa [hlocal] using hx

theorem thresholdCount_succ_le (s : WalkPath) (n m : ℕ) :
    thresholdCount s (n + 1) m ≤ thresholdCount s n m + 1 := by
  calc
    thresholdCount s (n + 1) m ≤ (insert (s (n + 1)) (thresholdSites s n m)).card :=
      Finset.card_le_card (thresholdSites_succ_subset_insert s n m)
    _ ≤ thresholdCount s n m + 1 := by
      rw [thresholdCount]
      exact Finset.card_insert_le _ _

theorem thresholdCount_succ_bounds (s : WalkPath) (n m : ℕ) :
    thresholdCount s n m ≤ thresholdCount s (n + 1) m ∧
      thresholdCount s (n + 1) m ≤ thresholdCount s n m + 1 := by
  exact ⟨thresholdCount_mono_time s m (Nat.le_succ n), thresholdCount_succ_le s n m⟩

theorem localTime_le_maxLocalTime (s : WalkPath) (n : ℕ) {x : Point}
    (hx : x ∈ visitedSites s n) : localTime s n x ≤ maxLocalTime s n := by
  exact localTimePrefix_le_maxLocalTimePrefix (pathPrefix s n) hx

theorem localTime_le_time_add_one (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x ≤ n + 1 := by
  unfold localTime localTimePrefix
  calc
    (Finset.univ.filter fun j : Fin (n + 1) ↦ pathPrefix s n j = x).card ≤
        (Finset.univ : Finset (Fin (n + 1))).card :=
      Finset.card_le_card
        (Finset.filter_subset (fun j : Fin (n + 1) ↦ pathPrefix s n j = x) Finset.univ)
    _ = n + 1 := by simp

theorem maxLocalTime_le_time_add_one (s : WalkPath) (n : ℕ) :
    maxLocalTime s n ≤ n + 1 := by
  unfold maxLocalTime maxLocalTimePrefix
  apply Finset.sup_le
  intro x _
  exact localTime_le_time_add_one s n x

theorem maxLocalTime_pos (s : WalkPath) (n : ℕ) : 0 < maxLocalTime s n := by
  obtain ⟨x, hx⟩ := favoriteSites_nonempty s n
  have hxVisited : x ∈ visitedSites s n := by
    rw [favoriteSites, favoritePrefix, Finset.mem_filter] at hx
    exact hx.1
  exact (localTimePrefix_pos_of_mem_visited hxVisited).trans_le
    (localTime_le_maxLocalTime s n hxVisited)

theorem thresholdSites_at_max_eq_favoriteSites (s : WalkPath) (n : ℕ) :
    thresholdSites s n (maxLocalTime s n) = favoriteSites s n := by
  ext x
  simp only [mem_thresholdSites, favoriteSites, favoritePrefix, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, Nat.le_antisymm (localTime_le_maxLocalTime s n hx) hmax⟩
  · rintro ⟨hx, heq⟩
    exact ⟨hx, heq.ge⟩

theorem thresholdCount_at_max_eq_favoriteCount (s : WalkPath) (n : ℕ) :
    thresholdCount s n (maxLocalTime s n) = favoriteCount s n := by
  rw [thresholdCount, favoriteCount, thresholdSites_at_max_eq_favoriteSites]

theorem thresholdCount_eq_zero_iff_forall_lt (s : WalkPath) (n q : ℕ) (hq : 0 < q) :
    thresholdCount s n q = 0 ↔ ∀ x : Point, localTime s n x < q := by
  rw [thresholdCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_thresholdSites_iff s n q _ hq, not_le]

theorem thresholdCount_succ_level_eq_zero_iff (s : WalkPath) (n m : ℕ) :
    thresholdCount s n (m + 1) = 0 ↔ maxLocalTime s n ≤ m := by
  rw [thresholdCount_eq_zero_iff_forall_lt s n (m + 1) (Nat.zero_lt_succ m)]
  constructor
  · intro h
    unfold maxLocalTime maxLocalTimePrefix
    apply Finset.sup_le
    intro x _
    exact Nat.lt_succ_iff.mp (h x)
  · intro h x
    by_cases hx : x ∈ visitedSites s n
    · exact Nat.lt_succ_iff.mpr ((localTime_le_maxLocalTime s n hx).trans h)
    · have hzero : localTime s n x = 0 :=
        localTimePrefix_eq_zero_of_notMem_visited hx
      rw [hzero]
      exact Nat.zero_lt_succ m

/-! ## Level events -/

/-- `M_m^k`: at some time the maximal local time is `m` and there are exactly
`k` favorite sites. -/
def levelFavorite (s : WalkPath) (m k : ℕ) : Prop :=
  ∃ n, maxLocalTime s n = m ∧ favoriteCount s n = k

/-- At some time of maximal-local-time height `m`, there are at least `k`
favorite sites. -/
def levelFavoriteAtLeast (s : WalkPath) (m k : ℕ) : Prop :=
  ∃ n, maxLocalTime s n = m ∧ k ≤ favoriteCount s n

/-- The path-space event corresponding to `M_m^k`. -/
def levelFavoriteSet (m k : ℕ) : Set WalkPath :=
  {s | levelFavorite s m k}

theorem levelFavorite_iff_thresholdCounts (s : WalkPath) (m k : ℕ) (hk : 0 < k) :
    levelFavorite s m k ↔
      ∃ n, thresholdCount s n m = k ∧ thresholdCount s n (m + 1) = 0 := by
  constructor
  · rintro ⟨n, hmax, hcount⟩
    refine ⟨n, ?_, ?_⟩
    · rw [← hmax, thresholdCount_at_max_eq_favoriteCount, hcount]
    · rw [thresholdCount_succ_level_eq_zero_iff, ← hmax]
  · rintro ⟨n, hcount, hnext⟩
    have hmax_le : maxLocalTime s n ≤ m :=
      (thresholdCount_succ_level_eq_zero_iff s n m).mp hnext
    have hnonempty : (thresholdSites s n m).Nonempty := by
      rw [← Finset.card_pos, ← thresholdCount, hcount]
      exact hk
    obtain ⟨x, hx⟩ := hnonempty
    have hm_le : m ≤ maxLocalTime s n :=
      (mem_thresholdSites s n m x).mp hx |>.2 |>.trans
        (localTime_le_maxLocalTime s n ((mem_thresholdSites s n m x).mp hx).1)
    have hmax : maxLocalTime s n = m := Nat.le_antisymm hmax_le hm_le
    refine ⟨n, hmax, ?_⟩
    rw [← thresholdCount_at_max_eq_favoriteCount, hmax, hcount]

theorem levelFavorite_iff_levelFavoriteAtLeast_of_count_le (s : WalkPath) (m k : ℕ)
    (hupper : ∀ n, maxLocalTime s n = m → favoriteCount s n ≤ k) :
    levelFavorite s m k ↔ levelFavoriteAtLeast s m k := by
  constructor
  · rintro ⟨n, hm, hk⟩
    exact ⟨n, hm, hk.ge⟩
  · rintro ⟨n, hm, hk⟩
    exact ⟨n, hm, Nat.le_antisymm (hupper n hm) hk⟩

theorem levelFavoriteAtLeast_iff_thresholdCounts (s : WalkPath) (m k : ℕ) (hk : 0 < k) :
    levelFavoriteAtLeast s m k ↔
      ∃ n, k ≤ thresholdCount s n m ∧ thresholdCount s n (m + 1) = 0 := by
  constructor
  · rintro ⟨n, hmax, hcount⟩
    refine ⟨n, ?_, ?_⟩
    · rwa [← hmax, thresholdCount_at_max_eq_favoriteCount]
    · rw [thresholdCount_succ_level_eq_zero_iff, ← hmax]
  · rintro ⟨n, hcount, hnext⟩
    have hmax_le : maxLocalTime s n ≤ m :=
      (thresholdCount_succ_level_eq_zero_iff s n m).mp hnext
    have hnonempty : (thresholdSites s n m).Nonempty := by
      rw [← Finset.card_pos, ← thresholdCount]
      exact hk.trans_le hcount
    obtain ⟨x, hx⟩ := hnonempty
    have hm_le : m ≤ maxLocalTime s n :=
      (mem_thresholdSites s n m x).mp hx |>.2 |>.trans
        (localTime_le_maxLocalTime s n ((mem_thresholdSites s n m x).mp hx).1)
    have hmax : maxLocalTime s n = m := Nat.le_antisymm hmax_le hm_le
    refine ⟨n, hmax, ?_⟩
    rwa [← thresholdCount_at_max_eq_favoriteCount, hmax]

theorem measurable_thresholdCount (n m : ℕ) :
    Measurable fun s : WalkPath ↦ thresholdCount s n m := by
  change Measurable
    ((fun u : Fin (n + 1) → Point ↦
        ((visitedPrefix u).filter fun x ↦ m ≤ localTimePrefix u x).card) ∘
      fun s : WalkPath ↦ pathPrefix s n)
  exact (measurable_of_countable _).comp (measurable_pathPrefix n)

theorem measurableSet_levelFavoriteSet (m k : ℕ) (hk : 0 < k) :
    MeasurableSet (levelFavoriteSet m k) := by
  have heq : levelFavoriteSet m k =
      ⋃ n : ℕ, {s : WalkPath | thresholdCount s n m = k} ∩
        {s : WalkPath | thresholdCount s n (m + 1) = 0} := by
    ext s
    simp only [levelFavoriteSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact levelFavorite_iff_thresholdCounts s m k hk
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦
    (measurableSet_eq_fun (measurable_thresholdCount n m) measurable_const).inter
      (measurableSet_eq_fun (measurable_thresholdCount n (m + 1)) measurable_const)

/-- The event that `M_m^k` occurs at infinitely many maximal-local-time levels. -/
def frequentLevelFavoriteSet (k : ℕ) : Set WalkPath :=
  {s | ∃ᶠ m in atTop, levelFavorite s m k}

theorem measurableSet_frequentLevelFavoriteSet (k : ℕ) (hk : 0 < k) :
    MeasurableSet (frequentLevelFavoriteSet k) := by
  rw [show frequentLevelFavoriteSet k = limsup (fun m ↦ levelFavoriteSet m k) atTop by
    ext s
    change (∃ᶠ m in atTop, levelFavorite s m k) ↔
      s ∈ limsup (fun m ↦ levelFavoriteSet m k) atTop
    simp only [mem_limsup_iff_frequently_mem, levelFavoriteSet, Set.mem_ofPred_eq]]
  exact MeasurableSet.measurableSet_limsup fun m ↦ measurableSet_levelFavoriteSet m k hk

/-! ## First-passage clocks -/

/-- A threshold is reached if at some finite time at least `k` sites have
local time at least `m`. -/
def ReachesThreshold (s : WalkPath) (m k : ℕ) : Prop :=
  ∃ n, k ≤ thresholdCount s n m

/-- The first time at which `k` sites have reached local-time level `m`, with
value `⊤` when this never happens.  This is the totalized version of
`T_m^k`. -/
noncomputable def thresholdTime (s : WalkPath) (m k : ℕ) : WithTop ℕ :=
  by
    classical
    exact if h : ReachesThreshold s m k then (Nat.find h : WithTop ℕ) else ⊤

theorem thresholdTime_eq_top_iff (s : WalkPath) (m k : ℕ) :
    thresholdTime s m k = ⊤ ↔ ¬ReachesThreshold s m k := by
  unfold thresholdTime
  by_cases h : ReachesThreshold s m k <;> simp [h]

theorem thresholdTime_lt_top_iff (s : WalkPath) (m k : ℕ) :
    thresholdTime s m k < ⊤ ↔ ReachesThreshold s m k := by
  unfold thresholdTime
  by_cases h : ReachesThreshold s m k <;> simp [h]

theorem thresholdTime_eq_coe (s : WalkPath) (m k : ℕ) (h : ReachesThreshold s m k) :
    thresholdTime s m k = (Nat.find h : WithTop ℕ) := by
  simp [thresholdTime, h]

theorem thresholdTime_spec (s : WalkPath) (m k : ℕ) (h : ReachesThreshold s m k) :
    k ≤ thresholdCount s (Nat.find h) m := by
  exact Nat.find_spec h

theorem thresholdTime_min (s : WalkPath) (m k n : ℕ) (h : ReachesThreshold s m k)
    (hn : k ≤ thresholdCount s n m) : Nat.find h ≤ n := by
  exact Nat.find_min' h hn

@[simp] theorem thresholdTime_zero (s : WalkPath) (m : ℕ) :
    thresholdTime s m 0 = 0 := by
  let h : ReachesThreshold s m 0 := ⟨0, Nat.zero_le _⟩
  rw [thresholdTime_eq_coe s m 0 h]
  have hfind : Nat.find h = 0 :=
    Nat.eq_zero_of_le_zero (Nat.find_min' h (Nat.zero_le _))
  rw [hfind]
  rfl

theorem thresholdTime_mono_count (s : WalkPath) (m : ℕ) :
    Monotone fun k ↦ thresholdTime s m k := by
  intro k l hkl
  change thresholdTime s m k ≤ thresholdTime s m l
  by_cases hl : ReachesThreshold s m l
  · let hk : ReachesThreshold s m k :=
      ⟨Nat.find hl, hkl.trans (Nat.find_spec hl)⟩
    rw [thresholdTime_eq_coe s m k hk, thresholdTime_eq_coe s m l hl]
    exact_mod_cast Nat.find_min' hk (hkl.trans (Nat.find_spec hl))
  · rw [(thresholdTime_eq_top_iff s m l).mpr hl]
    exact le_top

theorem thresholdTime_mono_level (s : WalkPath) (k : ℕ) :
    Monotone fun m ↦ thresholdTime s m k := by
  intro m q hmq
  change thresholdTime s m k ≤ thresholdTime s q k
  by_cases hq : ReachesThreshold s q k
  · let hm : ReachesThreshold s m k :=
      ⟨Nat.find hq,
        (Nat.find_spec hq).trans (thresholdCount_antitone_level s (Nat.find hq) hmq)⟩
    rw [thresholdTime_eq_coe s m k hm, thresholdTime_eq_coe s q k hq]
    exact_mod_cast Nat.find_min' hm
      ((Nat.find_spec hq).trans (thresholdCount_antitone_level s (Nat.find hq) hmq))
  · rw [(thresholdTime_eq_top_iff s q k).mpr hq]
    exact le_top

theorem thresholdCount_le_time_add_one (s : WalkPath) (n m : ℕ) :
    thresholdCount s n m ≤ n + 1 := by
  calc
    thresholdCount s n m ≤ (visitedSites s n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ n + 1 := by
      unfold visitedSites visitedPrefix
      calc
        (Finset.univ.image (pathPrefix s n)).card ≤
            (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_image_le
        _ = n + 1 := by simp

/-- Because one visit occurs per unit of time, the first time at which at
least `k > 0` sites reach a level has exactly `k` such sites. -/
theorem thresholdCount_at_thresholdTime (s : WalkPath) (m k : ℕ) (hk : 0 < k)
    (h : ReachesThreshold s m k) :
    thresholdCount s (Nat.find h) m = k := by
  apply Nat.le_antisymm ?_ (Nat.find_spec h)
  cases htime : Nat.find h with
  | zero =>
      have hle : thresholdCount s 0 m ≤ 1 := by
        simpa using thresholdCount_le_time_add_one s 0 m
      omega
  | succ n =>
      have hprev : ¬k ≤ thresholdCount s n m := by
        apply Nat.find_min h
        omega
      have hstep := thresholdCount_succ_le s n m
      omega

/-- Clock ordering is equivalent to reaching the lower threshold while no
site has yet reached the next local-time level. -/
theorem thresholdTime_lt_next_iff_exists (s : WalkPath) (m k : ℕ) :
    thresholdTime s m k < thresholdTime s (m + 1) 1 ↔
      ∃ n, k ≤ thresholdCount s n m ∧ thresholdCount s n (m + 1) = 0 := by
  constructor
  · intro hlt
    have hreach : ReachesThreshold s m k := by
      rw [← thresholdTime_lt_top_iff]
      exact hlt.trans_le le_top
    refine ⟨Nat.find hreach, Nat.find_spec hreach, ?_⟩
    by_contra hne
    have hpositive : 1 ≤ thresholdCount s (Nat.find hreach) (m + 1) :=
      Nat.one_le_iff_ne_zero.mpr hne
    let hnext : ReachesThreshold s (m + 1) 1 := ⟨Nat.find hreach, hpositive⟩
    have hmin : Nat.find hnext ≤ Nat.find hreach := Nat.find_min' hnext hpositive
    rw [thresholdTime_eq_coe s m k hreach,
      thresholdTime_eq_coe s (m + 1) 1 hnext] at hlt
    exact (not_lt_of_ge (by exact_mod_cast hmin)) hlt
  · rintro ⟨n, hn, hnextZero⟩
    let hreach : ReachesThreshold s m k := ⟨n, hn⟩
    by_cases hnext : ReachesThreshold s (m + 1) 1
    · have hnextAfter : n < Nat.find hnext := by
        by_contra hnot
        have hle : Nat.find hnext ≤ n := Nat.le_of_not_gt hnot
        have hpositive : 1 ≤ thresholdCount s n (m + 1) :=
          (Nat.find_spec hnext).trans
            (thresholdCount_mono_time s (m + 1) hle)
        omega
      have hfirst : Nat.find hreach ≤ n := Nat.find_min' hreach hn
      rw [thresholdTime_eq_coe s m k hreach,
        thresholdTime_eq_coe s (m + 1) 1 hnext]
      exact_mod_cast hfirst.trans_lt hnextAfter
    · rw [thresholdTime_eq_coe s m k hreach]
      have htop : thresholdTime s (m + 1) 1 = ⊤ :=
        (thresholdTime_eq_top_iff s (m + 1) 1).mpr hnext
      rw [htop]
      exact WithTop.coe_lt_top _

/-- Exact form of the clock identity.  The one-step bound for threshold
counts is what upgrades "at least `k`" to "exactly `k`" at the first time. -/
theorem thresholdTime_lt_next_iff_exists_eq (s : WalkPath) (m k : ℕ) (hk : 0 < k) :
    thresholdTime s m k < thresholdTime s (m + 1) 1 ↔
      ∃ n, thresholdCount s n m = k ∧ thresholdCount s n (m + 1) = 0 := by
  constructor
  · intro hlt
    have hreach : ReachesThreshold s m k := by
      rw [← thresholdTime_lt_top_iff]
      exact hlt.trans_le le_top
    refine ⟨Nat.find hreach, thresholdCount_at_thresholdTime s m k hk hreach, ?_⟩
    by_contra hne
    have hpositive : 1 ≤ thresholdCount s (Nat.find hreach) (m + 1) :=
      Nat.one_le_iff_ne_zero.mpr hne
    let hnext : ReachesThreshold s (m + 1) 1 := ⟨Nat.find hreach, hpositive⟩
    have hmin : Nat.find hnext ≤ Nat.find hreach := Nat.find_min' hnext hpositive
    rw [thresholdTime_eq_coe s m k hreach,
      thresholdTime_eq_coe s (m + 1) 1 hnext] at hlt
    exact (not_lt_of_ge (by exact_mod_cast hmin)) hlt
  · rintro ⟨n, hn, hnext⟩
    exact (thresholdTime_lt_next_iff_exists s m k).mpr ⟨n, hn.ge, hnext⟩

/-- HLOZ identity `M_m^k = {T_m^k < T_{m+1}^1}`, valid pathwise for every
positive `k`. -/
theorem levelFavorite_iff_thresholdTime_lt (s : WalkPath) (m k : ℕ) (hk : 0 < k) :
    levelFavorite s m k ↔ thresholdTime s m k < thresholdTime s (m + 1) 1 := by
  rw [levelFavorite_iff_thresholdCounts s m k hk,
    thresholdTime_lt_next_iff_exists_eq s m k hk]

/-- Having at least `k` favorites at height `m` is equivalent to having
exactly `k` favorites at some (possibly earlier) time of the same height. -/
theorem levelFavorite_iff_levelFavoriteAtLeast (s : WalkPath) (m k : ℕ) (hk : 0 < k) :
    levelFavorite s m k ↔ levelFavoriteAtLeast s m k := by
  constructor
  · rintro ⟨n, hm, hk'⟩
    exact ⟨n, hm, hk'.ge⟩
  · intro h
    apply (levelFavorite_iff_thresholdTime_lt s m k hk).mpr
    apply (thresholdTime_lt_next_iff_exists s m k).mpr
    exact (levelFavoriteAtLeast_iff_thresholdCounts s m k hk).mp h

/-! ## Returning from the level clock to ordinary time -/

theorem visitedSites_mono_time (s : WalkPath) : Monotone fun n ↦ visitedSites s n := by
  intro a b hab x hx
  rw [mem_visitedSites_iff_localTime_pos] at hx ⊢
  exact hx.trans_le (localTime_mono_time s x hab)

theorem maxLocalTime_mono_time (s : WalkPath) : Monotone fun n ↦ maxLocalTime s n := by
  intro a b hab
  obtain ⟨x, hx⟩ := favoriteSites_nonempty s a
  rw [favoriteSites, favoritePrefix, Finset.mem_filter] at hx
  have hxAtB : x ∈ visitedSites s b := visitedSites_mono_time s hab hx.1
  calc
    maxLocalTime s a = localTime s a x := hx.2.symm
    _ ≤ localTime s b x := localTime_mono_time s x hab
    _ ≤ maxLocalTime s b := localTime_le_maxLocalTime s b hxAtB

/-- The deterministic hypothesis needed to identify infinitely many ordinary
times with infinitely many maximal-local-time levels.  Planar recurrence will
establish this almost surely for the random walk. -/
def MaxLocalTimeDiverges (s : WalkPath) : Prop :=
  Tendsto (maxLocalTime s) atTop atTop

theorem maxLocalTimeDiverges_iff_unbounded (s : WalkPath) :
    MaxLocalTimeDiverges s ↔ ∀ m, ∃ n, m ≤ maxLocalTime s n := by
  rw [MaxLocalTimeDiverges,
    (maxLocalTime_mono_time s).tendsto_atTop_atTop_iff]

/-- HLOZ identity (3.5), first in its "at least `k`" level-event form. -/
theorem frequently_favoriteCount_ge_iff_frequently_levelFavoriteAtLeast
    (s : WalkPath) (k : ℕ) (hdiv : MaxLocalTimeDiverges s) :
    (∃ᶠ n in atTop, k ≤ favoriteCount s n) ↔
      ∃ᶠ m in atTop, levelFavoriteAtLeast s m k := by
  constructor
  · intro hfreq
    refine frequently_atTop.2 fun M ↦ ?_
    have hlarge : ∀ᶠ n in atTop, M ≤ maxLocalTime s n :=
      (tendsto_atTop.1 hdiv M)
    obtain ⟨n, hcount, hmax⟩ := (hfreq.and_eventually hlarge).exists
    exact ⟨maxLocalTime s n, hmax, n, rfl, hcount⟩
  · intro hfreq
    refine frequently_atTop.2 fun N ↦ ?_
    obtain ⟨m, hm, n, hmax, hcount⟩ := (frequently_atTop.1 hfreq) (N + 1)
    refine ⟨n, ?_, hcount⟩
    have hbound := maxLocalTime_le_time_add_one s n
    rw [hmax] at hbound
    omega

/-- HLOZ identity (3.5) in the exact `M_m^k` form used by the proof. -/
theorem frequently_favoriteCount_ge_iff_frequently_levelFavorite
    (s : WalkPath) (k : ℕ) (hk : 0 < k) (hdiv : MaxLocalTimeDiverges s) :
    (∃ᶠ n in atTop, k ≤ favoriteCount s n) ↔
      ∃ᶠ m in atTop, levelFavorite s m k := by
  rw [frequently_favoriteCount_ge_iff_frequently_levelFavoriteAtLeast s k hdiv]
  apply frequently_congr
  filter_upwards [] with m
  exact (levelFavorite_iff_levelFavoriteAtLeast s m k hk).symm

/-- The same infinitely-often identity expressed purely as ordering of the
two threshold clocks. -/
theorem frequently_favoriteCount_ge_iff_frequently_thresholdTime_lt
    (s : WalkPath) (k : ℕ) (hk : 0 < k) (hdiv : MaxLocalTimeDiverges s) :
    (∃ᶠ n in atTop, k ≤ favoriteCount s n) ↔
      ∃ᶠ m in atTop, thresholdTime s m k < thresholdTime s (m + 1) 1 := by
  rw [frequently_favoriteCount_ge_iff_frequently_levelFavorite s k hk hdiv]
  apply frequently_congr
  filter_upwards [] with m
  exact levelFavorite_iff_thresholdTime_lt s m k hk

end Erdos1165
