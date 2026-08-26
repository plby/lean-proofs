import ErdosProblems.Erdos118.AlignedRootReserve
import ErdosProblems.Erdos118.LabelRanks

/-! Root overlaps at any prescribed internal lower rank, retaining all
later lower selections. The upper last root is the next lower root. -/

namespace Erdos118.RankedRootReserve

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

structure Labels (H : Set ℕ) (b k l v : ℕ) where
  lower : List ℕ
  upper : List ℕ
  shared : ℕ
  next : ℕ
  lowerCard : lower.length = k + 1
  upperCard : upper.length = l + 1
  lowerIncreasing : lower.Pairwise (· < ·)
  upperIncreasing : upper.Pairwise (· < ·)
  first : upper.headD 0 = shared
  last : upper.getLastD 0 = next
  sharedLower : shared ∈ lower
  nextLower : next ∈ lower
  increasing : shared < next
  sharedRank : LabelRanks.rank lower shared = v
  nextRank : LabelRanks.rank lower next = v + 1
  lowerGap : ∀ x ∈ lower, x ≤ shared ∨ next ≤ x
  upperBounds : ∀ x ∈ upper, shared ≤ x ∧ x ≤ next
  intersection : ∀ x, x ∈ lower ∧ x ∈ upper ↔ x = shared ∨ x = next
  lowerFresh : ∀ x ∈ lower, x ∈ H ∧ b < x
  upperFresh : ∀ x ∈ upper, x ∈ H ∧ b < x

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l v : ℕ)
    (hv : 0 < v) (hvk : v < k + 1) (hl : 0 < l) : Nonempty (Labels H b k l v) := by
  classical
  obtain ⟨C, D, r, c, hCk, hDl, hCi, hDi, hCl, hDl', hDf, hrC, hrc,
    hearly, hinter, hC, hD⟩ := AlignedRootReserve.labels hH b v l hv hl
  have hCne := List.ne_nil_of_mem hrC
  have hDne : D ≠ [] := by intro he; simp [he] at hDl
  have hlastC : C.getLast hCne = c := by
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hCne,
      Option.getD_some] using hCl
  have hlastD : D.getLast hDne = c := by
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hDne,
      Option.getD_some] using hDl'
  have hcC : c ∈ C := hlastC ▸ List.getLast_mem hCne
  have hCmax : ∀ x ∈ C, x ≤ c := fun x hx ↦ hlastC ▸ (hCi.imp Nat.le_of_lt).rel_getLast hx
  have hDmax : ∀ x ∈ D, x ≤ c := fun x hx ↦ hlastD ▸ (hDi.imp Nat.le_of_lt).rel_getLast hx
  have hDmin : ∀ x ∈ D, r ≤ x := by
    intro x hx
    rw [← hDf]
    have he := (hDi.imp Nat.le_of_lt).rel_head hx
    cases hd : D with
    | nil => simp [hd] at hx
    | cons a rest => simpa only [hd, List.head_cons, List.headD_cons] using he
  obtain ⟨tail, htlen, hti, ht⟩ := InteriorWords.fresh_list hH (max b c) (k - v)
  have hct : ∀ x ∈ tail, c < x := fun x hx ↦ (le_max_right _ _).trans_lt (ht x hx).2
  have hfilter : (C ++ tail).toFinset.filter (· ≤ r) = C.toFinset.erase c := by
    ext x
    simp only [List.toFinset_append, Finset.mem_filter, Finset.mem_union,
      List.mem_toFinset, Finset.mem_erase]
    constructor
    · rintro ⟨hx | hx, hxr⟩
      · exact ⟨by omega, hx⟩
      · exact (not_lt_of_ge (hxr.trans hrc.le) (hct x hx)).elim
    · rintro ⟨hxc, hx⟩
      exact ⟨Or.inl hx, hearly x hx (lt_of_le_of_ne (hCmax x hx) hxc)⟩
  have hfilterNext : (C ++ tail).toFinset.filter (· ≤ c) = C.toFinset := by
    ext x
    simp only [List.toFinset_append, Finset.mem_filter, Finset.mem_union, List.mem_toFinset]
    constructor
    · rintro ⟨hx | hx, hxc⟩
      · exact hx
      · exact (not_lt_of_ge hxc (hct x hx)).elim
    · intro hx
      exact ⟨Or.inl hx, hCmax x hx⟩
  refine ⟨{
    lower := C ++ tail, upper := D, shared := r, next := c
    lowerCard := by simp only [List.length_append, hCk, htlen]; omega
    upperCard := hDl
    lowerIncreasing := List.pairwise_append.mpr
      ⟨hCi, hti, fun x hx y hy ↦ (hCmax x hx).trans_lt (hct y hy)⟩
    upperIncreasing := hDi, first := hDf, last := hDl'
    sharedLower := List.mem_append_left _ hrC, nextLower := List.mem_append_left _ hcC
    increasing := hrc
    sharedRank := by
      rw [LabelRanks.rank, hfilter, Finset.card_erase_of_mem (List.mem_toFinset.mpr hcC),
        List.toFinset_card_of_nodup hCi.nodup, hCk]
      omega
    nextRank := by rw [LabelRanks.rank, hfilterNext, List.toFinset_card_of_nodup hCi.nodup, hCk]
    lowerGap := ?_, upperBounds := fun x hx ↦ ⟨hDmin x hx, hDmax x hx⟩
    intersection := ?_, lowerFresh := ?_, upperFresh := hD }⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · by_cases he : x < c
      · exact Or.inl (hearly x hx he)
      · exact Or.inr (Nat.le_of_not_gt he)
    · exact Or.inr (hct x hx).le
  · intro x
    constructor
    · rintro ⟨hx, hxD⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact (hinter x).mp ⟨hx, hxD⟩
      · exact (not_lt_of_ge (hDmax x hxD) (hct x hx)).elim
    · intro hx
      obtain ⟨hxC, hxD⟩ := (hinter x).mpr hx
      exact ⟨List.mem_append_left _ hxC, hxD⟩
  · intro x hx
    exact (List.mem_append.mp hx).elim (hC x)
      (fun hx ↦ ⟨(ht x hx).1, (le_max_left _ _).trans_lt (ht x hx).2⟩)

structure Reserve (H : Set ℕ) (b k l v : ℕ) (S : Stem) where
  labels : Labels H b k l v
  lower : S.rootLabel = labels.lower
  below : ∀ x ∈ labels.upper, x < S.root

def Labels.rebase {H K : Set ℕ} {b c k l v : ℕ} (L : Labels K c k l v)
    (hKH : K ⊆ H) (hbc : b ≤ c) : Labels H b k l v where
  lower := L.lower
  upper := L.upper
  shared := L.shared
  next := L.next
  lowerCard := L.lowerCard
  upperCard := L.upperCard
  lowerIncreasing := L.lowerIncreasing
  upperIncreasing := L.upperIncreasing
  first := L.first
  last := L.last
  sharedLower := L.sharedLower
  nextLower := L.nextLower
  increasing := L.increasing
  sharedRank := L.sharedRank
  nextRank := L.nextRank
  lowerGap := L.lowerGap
  upperBounds := L.upperBounds
  intersection := L.intersection
  lowerFresh := fun x hx ↦ ⟨hKH (L.lowerFresh x hx).1, hbc.trans_lt (L.lowerFresh x hx).2⟩
  upperFresh := fun x hx ↦ ⟨hKH (L.upperFresh x hx).1, hbc.trans_lt (L.upperFresh x hx).2⟩

def Reserve.rebase {H K : Set ℕ} {b c k l v : ℕ} {S : Stem} (Z : Reserve K c k l v S)
    (hKH : K ⊆ H) (hbc : b ≤ c) : Reserve H b k l v S where
  labels := Z.labels.rebase hKH hbc
  lower := Z.lower
  below := Z.below

def Reserve.move {H : Set ℕ} {b k l v : ℕ} {S : Stem} (Z : Reserve H b k l v S)
    (T : Stem) (hroot : T.root = S.root) (hlabel : T.rootLabel = S.rootLabel) :
    Reserve H b k l v T where
  labels := Z.labels
  lower := hlabel.trans Z.lower
  below := by rw [hroot]; exact Z.below

theorem root_reserved {H : Set ℕ} (hH : H.Infinite) (b k l v : ℕ)
    (hv : 0 < v) (hvk : v < k + 1) (hl : 0 < l) :
    ∃ A : RootResponses.Setup k, ∃ _Z : Reserve H b k l v A.stem,
      ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x := by
  obtain ⟨L⟩ := labels hH b k l v hv hvk hl
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
  obtain ⟨S, w, hr, hlabel, hcount, _, hdec, _, hw, p, hp⟩ :=
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
  let Z : Reserve H b k l v A.stem :=
    { labels := L, lower := hlabel
      below := by intro x hx; change x < S.root; rw [hr]; exact hDm x hx }
  refine ⟨A, Z, ?_⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  exact (List.mem_append.mp hx).elim (hE x) (hw x)

theorem Reserve.index_of_rank {H : Set ℕ} {b k l v : ℕ} (D : BodyDecision)
    (Z : Reserve H b k l v D.stem)
    (hrank : LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = v) :
    D.stem.done.length + 1 = Z.labels.shared := by
  have hshared : Z.labels.shared ∈ D.stem.rootLabel := Z.lower ▸ Z.labels.sharedLower
  have hv : LabelRanks.rank D.stem.rootLabel Z.labels.shared = v :=
    Z.lower ▸ Z.labels.sharedRank
  exact LabelRanks.rank_injective D.rootSelected hshared (hrank.trans hv.symm)

def Reserve.rootSetup {H : Set ℕ} {b k l v : ℕ} {S : Stem} (Z : Reserve H b k l v S)
    (hindex : S.done.length + 1 = Z.labels.shared) : RootResponses.Setup l :=
  LabelOverlays.rootSetup S Z.labels.upper Z.labels.upperIncreasing Z.below l Z.labels.upperCard
    (hindex.trans Z.labels.first.symm)

theorem Reserve.rootSetup_ordinary {H : Set ℕ} {b k l v : ℕ} {S : Stem}
    (Z : Reserve H b k l v S) (hindex : S.done.length + 1 = Z.labels.shared) :
    (Z.rootSetup hindex).stem.ordinary = S.ordinary :=
  LabelOverlays.plainStem_ordinary S Z.labels.upper Z.labels.upperIncreasing Z.below

theorem Reserve.rootSetup_supported {H : Set ℕ} {b k l v : ℕ} {S : Stem}
    (Z : Reserve H b k l v S) (hindex : S.done.length + 1 = Z.labels.shared)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (Z.rootSetup hindex).stem.decorated, x ∈ H ∧ b < x :=
  LabelOverlays.plainStem_supported S Z.labels.upper Z.labels.upperIncreasing Z.below
    Z.labels.upperFresh hf

end Erdos118.RankedRootReserve
