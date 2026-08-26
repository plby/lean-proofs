import ErdosProblems.Erdos118.RankedRootReserve

/-! The shared next lower root has a prescribed upper rank.
All upper selections after it lie beyond the full lower label. -/

namespace Erdos118.SplicedRootReserve

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

structure Labels (H : Set ℕ) (b k l v r : ℕ) where
  lower : List ℕ
  upper : List ℕ
  shared : ℕ
  next : ℕ
  lowerCard : lower.length = k + 1
  upperCard : upper.length = l + 1
  lowerIncreasing : lower.Pairwise (· < ·)
  upperIncreasing : upper.Pairwise (· < ·)
  first : upper.headD 0 = shared
  sharedLower : shared ∈ lower
  nextLower : next ∈ lower
  nextUpper : next ∈ upper
  increasing : shared < next
  sharedRank : LabelRanks.rank lower shared = v
  nextRank : LabelRanks.rank lower next = v + 1
  upperRank : LabelRanks.rank upper next = r
  lowerGap : ∀ x ∈ lower, x ≤ shared ∨ next ≤ x
  upperFirst : ∀ x ∈ upper, shared ≤ x
  upperGap : ∀ x ∈ upper, x ≤ next ∨ ∀ y ∈ lower, y < x
  intersection : ∀ x, x ∈ lower ∧ x ∈ upper ↔ x = shared ∨ x = next
  lowerFresh : ∀ x ∈ lower, x ∈ H ∧ b < x
  upperFresh : ∀ x ∈ upper, x ∈ H ∧ b < x

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l v r : ℕ)
    (hv : 0 < v) (hvk : v < k + 1) (hr : 2 ≤ r) (hrl : r ≤ l + 1) :
    Nonempty (Labels H b k l v r) := by
  classical
  obtain ⟨L⟩ := RankedRootReserve.labels hH b k (r - 1) v hv hvk (by omega)
  obtain ⟨tail, hlen, hi, hf⟩ := InteriorWords.fresh_list hH
    (max b (max L.lower.sum L.upper.sum)) (l + 1 - r)
  have htailLower : ∀ x ∈ tail, ∀ y ∈ L.lower, y < x := by
    intro x hx y hy
    exact (nat_le_sum_of_mem hy).trans_lt
      (((le_max_left L.lower.sum L.upper.sum).trans (le_max_right b _)).trans_lt (hf x hx).2)
  have htailUpper : ∀ x ∈ tail, ∀ y ∈ L.upper, y < x := by
    intro x hx y hy
    exact (nat_le_sum_of_mem hy).trans_lt
      (((le_max_right L.lower.sum L.upper.sum).trans (le_max_right b _)).trans_lt (hf x hx).2)
  have hne : L.upper ≠ [] := by intro he; have hc := L.upperCard; simp [he] at hc
  have hnext : L.next ∈ L.upper := ((L.intersection L.next).mpr (Or.inr rfl)).2
  have hfilter : (L.upper ++ tail).toFinset.filter (· ≤ L.next) = L.upper.toFinset := by
    ext x
    simp only [List.toFinset_append, Finset.mem_filter, Finset.mem_union, List.mem_toFinset]
    constructor
    · rintro ⟨hx | hx, hle⟩
      · exact hx
      · exact (not_lt_of_ge hle (htailLower x hx L.next L.nextLower)).elim
    · intro hx
      exact ⟨Or.inl hx, (L.upperBounds x hx).2⟩
  refine ⟨{
    lower := L.lower, upper := L.upper ++ tail, shared := L.shared, next := L.next
    lowerCard := L.lowerCard
    upperCard := by simp only [List.length_append, L.upperCard, hlen]; omega
    lowerIncreasing := L.lowerIncreasing
    upperIncreasing := List.pairwise_append.mpr
      ⟨L.upperIncreasing, hi, fun y hy x hx ↦ htailUpper x hx y hy⟩
    first := ?_, sharedLower := L.sharedLower, nextLower := L.nextLower
    nextUpper := List.mem_append_left _ hnext, increasing := L.increasing
    sharedRank := L.sharedRank, nextRank := L.nextRank
    upperRank := by
      rw [LabelRanks.rank, hfilter,
        List.toFinset_card_of_nodup L.upperIncreasing.nodup, L.upperCard]
      omega
    lowerGap := L.lowerGap, upperFirst := ?_, upperGap := ?_, intersection := ?_
    lowerFresh := L.lowerFresh, upperFresh := ?_ }⟩
  · cases he : L.upper with
    | nil => exact (hne he).elim
    | cons a rest => simpa only [he, List.cons_append, List.headD_cons] using L.first
  · intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ (L.upperBounds x hx).1)
      (fun hx ↦ (htailLower x hx L.shared L.sharedLower).le)
  · intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ Or.inl (L.upperBounds x hx).2)
      (fun hx ↦ Or.inr (htailLower x hx))
  · intro x
    constructor
    · rintro ⟨hx, hu⟩
      rcases List.mem_append.mp hu with hu | hu
      · exact (L.intersection x).mp ⟨hx, hu⟩
      · exact (Nat.lt_irrefl x (htailLower x hu x hx)).elim
    · intro hx
      obtain ⟨hl, hu⟩ := (L.intersection x).mpr hx
      exact ⟨hl, List.mem_append_left _ hu⟩
  · intro x hx
    exact (List.mem_append.mp hx).elim (L.upperFresh x)
      (fun hx ↦ ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩)

structure Reserve (H : Set ℕ) (b k l v r : ℕ) (S : Stem) where
  labels : Labels H b k l v r
  lower : S.rootLabel = labels.lower
  below : ∀ x ∈ labels.upper, x < S.root

def Labels.rebase {H K : Set ℕ} {b c k l v r : ℕ} (L : Labels K c k l v r)
    (hKH : K ⊆ H) (hbc : b ≤ c) : Labels H b k l v r where
  lower := L.lower
  upper := L.upper
  shared := L.shared
  next := L.next
  lowerCard := L.lowerCard
  upperCard := L.upperCard
  lowerIncreasing := L.lowerIncreasing
  upperIncreasing := L.upperIncreasing
  first := L.first
  sharedLower := L.sharedLower
  nextLower := L.nextLower
  nextUpper := L.nextUpper
  increasing := L.increasing
  sharedRank := L.sharedRank
  nextRank := L.nextRank
  upperRank := L.upperRank
  lowerGap := L.lowerGap
  upperFirst := L.upperFirst
  upperGap := L.upperGap
  intersection := L.intersection
  lowerFresh := fun x hx ↦ ⟨hKH (L.lowerFresh x hx).1, hbc.trans_lt (L.lowerFresh x hx).2⟩
  upperFresh := fun x hx ↦ ⟨hKH (L.upperFresh x hx).1, hbc.trans_lt (L.upperFresh x hx).2⟩

def Reserve.rebase {H K : Set ℕ} {b c k l v r : ℕ} {S : Stem} (Z : Reserve K c k l v r S)
    (hKH : K ⊆ H) (hbc : b ≤ c) : Reserve H b k l v r S where
  labels := Z.labels.rebase hKH hbc
  lower := Z.lower
  below := Z.below

def Reserve.move {H : Set ℕ} {b k l v r : ℕ} {S : Stem} (Z : Reserve H b k l v r S)
    (T : Stem) (hroot : T.root = S.root) (hlabel : T.rootLabel = S.rootLabel) :
    Reserve H b k l v r T where
  labels := Z.labels
  lower := hlabel.trans Z.lower
  below := by rw [hroot]; exact Z.below

theorem root_reserved {H : Set ℕ} (hH : H.Infinite) (b k l v r : ℕ)
    (hv : 0 < v) (hvk : v < k + 1) (hr : 2 ≤ r) (hrl : r ≤ l + 1) :
    ∃ A : RootResponses.Setup k, ∃ _Z : Reserve H b k l v r A.stem,
      ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x := by
  obtain ⟨L⟩ := labels hH b k l v r hv hvk hr hrl
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt (max b (max L.lower.sum L.upper.sum))
  have hbm : b < m := (le_max_left _ _).trans_lt hm
  have hCm : ∀ x ∈ L.lower, x < m := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left L.lower.sum L.upper.sum).trans (le_max_right b _)).trans_lt hm)
  have hDm : ∀ x ∈ L.upper, x < m := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right L.lower.sum L.upper.sum).trans (le_max_right b _)).trans_lt hm)
  let E : Stem :=
    { root := m, rootLabel := L.lower, done := [], count := Nat.zero_le _
      increasing := List.pairwise_append.mpr
        ⟨L.lowerIncreasing, by simp, fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hCm x hx⟩ }
  have hE : ∀ x ∈ E.decorated, x ∈ H ∧ b < x := by
    intro x hx
    change x ∈ L.lower ++ [m] at hx
    exact (List.mem_append.mp hx).elim (L.lowerFresh x)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hmH, hbm⟩)
  have hCne := List.ne_nil_of_mem L.sharedLower
  have hhead := first_mem hCne
  have hpos : 0 < L.lower.headD 0 := (Nat.zero_le b).trans_lt (L.lowerFresh _ hhead).2
  have hheadm := hCm _ hhead
  obtain ⟨S, w, hroot, hlabel, hcount, _, hdec, _, hw, p, hp⟩ :=
    fill_stem_plain E hH b (L.lower.headD 0 - 1) (by simp [E]) (by dsimp [E]; omega)
  let A : RootResponses.Setup k :=
    { stem := S
      label_length := by rw [hlabel]; exact L.lowerCard
      first_body := by
        rw [hcount, hlabel]
        change L.lower.headD 0 - 1 + 1 = L.lower.headD 0
        omega
      plain := by
        intro a ha
        rw [hp] at ha
        change a ∈ p.map LabelledExtensions.plain at ha
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
        rfl }
  let Z : Reserve H b k l v r A.stem :=
    { labels := L, lower := hlabel
      below := by intro x hx; change x < S.root; rw [hroot]; exact hDm x hx }
  refine ⟨A, Z, ?_⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  exact (List.mem_append.mp hx).elim (hE x) (hw x)

theorem Reserve.index_of_rank {H : Set ℕ} {b k l v r : ℕ} (D : BodyDecision)
    (Z : Reserve H b k l v r D.stem)
    (hrank : LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = v) :
    D.stem.done.length + 1 = Z.labels.shared := by
  have hshared : Z.labels.shared ∈ D.stem.rootLabel := Z.lower ▸ Z.labels.sharedLower
  have hv : LabelRanks.rank D.stem.rootLabel Z.labels.shared = v := Z.lower ▸ Z.labels.sharedRank
  exact LabelRanks.rank_injective D.rootSelected hshared (hrank.trans hv.symm)

def Reserve.rootSetup {H : Set ℕ} {b k l v r : ℕ} {S : Stem} (Z : Reserve H b k l v r S)
    (hindex : S.done.length + 1 = Z.labels.shared) : RootResponses.Setup l :=
  LabelOverlays.rootSetup S Z.labels.upper Z.labels.upperIncreasing Z.below l Z.labels.upperCard
    (hindex.trans Z.labels.first.symm)

theorem Reserve.rootSetup_ordinary {H : Set ℕ} {b k l v r : ℕ} {S : Stem}
    (Z : Reserve H b k l v r S) (hindex : S.done.length + 1 = Z.labels.shared) :
    (Z.rootSetup hindex).stem.ordinary = S.ordinary :=
  LabelOverlays.plainStem_ordinary S Z.labels.upper Z.labels.upperIncreasing Z.below

theorem Reserve.rootSetup_supported {H : Set ℕ} {b k l v r : ℕ} {S : Stem}
    (Z : Reserve H b k l v r S) (hindex : S.done.length + 1 = Z.labels.shared)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (Z.rootSetup hindex).stem.decorated, x ∈ H ∧ b < x :=
  LabelOverlays.plainStem_supported S Z.labels.upper Z.labels.upperIncreasing Z.below
    Z.labels.upperFresh hf

end Erdos118.SplicedRootReserve
