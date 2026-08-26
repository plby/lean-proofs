import ErdosProblems.Erdos118.RootResponses

/-!
Finite overlapping label windows and actual root/body response overlays.
The ordinary word is unchanged. No coloring certificate is transported by
relabeling without a separately proved conservative response.
-/

namespace Erdos118.LabelOverlays

open Negative Negative.Exact LabelledExtensions Erdos590.Larson

theorem shared_extreme_labels {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ C D : List ℕ, ∃ c : ℕ,
      C.length = k + 1 ∧ D.length = l + 1 ∧ C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧
      C.getLastD 0 = c ∧ D.headD 0 = c ∧ c ∈ C ∧ c ∈ D ∧
      (∀ x, x ∈ C ∧ x ∈ D ↔ x = c) ∧
      (∀ x ∈ C, x ∈ H ∧ b < x ∧ x ≤ c) ∧
      (∀ x ∈ D, x ∈ H ∧ b < x ∧ c ≤ x) := by
  obtain ⟨A, hAcard, hAinc, hA⟩ := InteriorWords.fresh_list hH b k
  obtain ⟨c, hcH, hc⟩ := hH.exists_gt (max b A.sum)
  have hbc : b < c := (le_max_left _ _).trans_lt hc
  have hAc : ∀ x ∈ A, x < c := fun x hx ↦
    (nat_le_sum_of_mem hx).trans_lt ((le_max_right _ _).trans_lt hc)
  obtain ⟨E, hEcard, hEinc, hE⟩ := InteriorWords.fresh_list hH c l
  refine ⟨A ++ [c], c :: E, c, by simp [hAcard], by simp [hEcard], ?_, ?_,
    by simp, rfl, List.mem_append_right _ (List.mem_singleton_self _),
    List.mem_cons_self .., ?_, ?_, ?_⟩
  · apply List.pairwise_append.mpr
    exact ⟨hAinc, by simp, fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hAc x hx⟩
  · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hE x hx).2, hEinc⟩
  · intro x
    constructor
    · rintro ⟨hxC, hxD⟩
      rcases List.mem_append.mp hxC with hxA | hxC
      · rcases List.mem_cons.mp hxD with rfl | hxE
        · rfl
        · have h1 := hAc x hxA
          have h2 := (hE x hxE).2
          omega
      · exact List.mem_singleton.mp hxC
    · rintro rfl
      exact ⟨List.mem_append_right _ (List.mem_singleton_self _), List.mem_cons_self ..⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hA x hx).1, (hA x hx).2, (hAc x hx).le⟩
    · have he := List.mem_singleton.mp hx
      subst x
      exact ⟨hcH, hbc, le_rfl⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hcH, hbc, le_rfl⟩
    · exact ⟨(hE x hx).1, hbc.trans (hE x hx).2, (hE x hx).2.le⟩

theorem labels_before_ordinary (S : Stem) (C : List ℕ)
    (hC : ∀ x ∈ C, x < S.root) : ∀ x ∈ C, ∀ y ∈ S.ordinary, x < y := by
  intro x hx y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hC x hx
  · have hinc := List.pairwise_cons.mp (S.increasing.sublist S.ordinary_sublist)
    exact (hC x hx).trans (hinc.1 y hy)

def plainStem (S : Stem) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root) : Stem where
  root := S.root
  rootLabel := C
  done := (S.done.map Body.values).map LabelledExtensions.plain
  count := by simpa only [List.length_map] using S.count
  increasing := by
    rw [plain_decorated, List.flatMap_map]
    exact List.pairwise_append.mpr
      ⟨hC, S.increasing.sublist S.ordinary_sublist, labels_before_ordinary S C hCr⟩

theorem plainStem_ordinary (S : Stem) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root) : (plainStem S C hC hCr).ordinary = S.ordinary := by
  change S.root :: ((S.done.map Body.values).map LabelledExtensions.plain).flatMap
    Body.ordinary = S.ordinary
  rw [plain_ordinary, List.flatMap_map]
  rfl

theorem plainStem_decorated (S : Stem) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root) :
    (plainStem S C hC hCr).decorated = C ++ S.ordinary := by
  change C ++ (S.root :: ((S.done.map Body.values).map LabelledExtensions.plain).flatMap
    Body.decorated) = C ++ S.ordinary
  rw [plain_decorated, List.flatMap_map]
  rfl

theorem plainStem_supported (S : Stem) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root) {H : Set ℕ} {b : ℕ}
    (hc : ∀ x ∈ C, x ∈ H ∧ b < x) (hS : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (plainStem S C hC hCr).decorated, x ∈ H ∧ b < x := by
  rw [plainStem_decorated]
  intro x hx
  exact (List.mem_append.mp hx).elim (hc x) (hS x)

def rootSetup (S : Stem) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root) (k : ℕ) (hcard : C.length = k + 1)
    (hfirst : S.done.length + 1 = C.headD 0) : RootResponses.Setup k where
  stem := plainStem S C hC hCr
  label_length := hcard
  first_body := by simpa only [plainStem, List.length_map] using hfirst
  plain := by
    intro a ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    rfl

theorem plainStem_before_marker (P : Position) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.stem.root) :
    ∀ x ∈ (plainStem P.stem C hC hCr).decorated, x < P.size := by
  have hprefix : ∀ x ∈ P.stem.decorated, x < P.size := by
    intro x hx
    exact (List.pairwise_append.mp P.increasing).2.2 x hx P.size
      (List.mem_append_right _ (List.mem_cons_self ..))
  rw [plainStem_decorated]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hCr x hx).trans (hprefix P.stem.root
      (List.mem_append_right _ (List.mem_cons_self ..)))
  · exact hprefix x (P.stem.ordinary_sublist.subset hx)

def position (P : Position) (C D : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.stem.root) (hD : D.Pairwise (· < ·))
    (hDn : ∀ x ∈ D, x < P.size)
    (hbefore : ∀ x ∈ (plainStem P.stem C hC hCr).decorated, ∀ y ∈ D, x < y) : Position where
  stem := plainStem P.stem C hC hCr
  size := P.size
  label := D
  entries := P.entries
  room := by simpa only [plainStem, List.length_map] using P.room
  started := P.started
  unfinished := P.unfinished
  increasing := by
    have hmarker := plainStem_before_marker P C hC hCr
    have htail : (P.size :: P.entries).Pairwise (· < ·) :=
      (List.pairwise_append.mp (List.pairwise_append.mp P.increasing).2.1).2.1
    have htailbound : ∀ x ∈ D, ∀ y ∈ P.size :: P.entries, x < y := by
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hDn x hx
      · exact (hDn x hx).trans ((List.pairwise_cons.mp htail).1 y hy)
    apply List.pairwise_append.mpr
    refine ⟨(plainStem P.stem C hC hCr).increasing,
      List.pairwise_append.mpr ⟨hD, htail, htailbound⟩, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hbefore x hx y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hmarker x hx
      · exact (hmarker x hx).trans ((List.pairwise_cons.mp htail).1 y hy)

theorem position_ordinary (P : Position) (C D : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.stem.root) (hD : D.Pairwise (· < ·))
    (hDn : ∀ x ∈ D, x < P.size)
    (hbefore : ∀ x ∈ (plainStem P.stem C hC hCr).decorated, ∀ y ∈ D, x < y) :
    (position P C D hC hCr hD hDn hbefore).ordinary = P.ordinary := by
  simp only [position, Position.ordinary, plainStem_ordinary]

def bodySetup (P : Position) (C D : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.stem.root) (hD : D.Pairwise (· < ·))
    (hDn : ∀ x ∈ D, x < P.size)
    (hbefore : ∀ x ∈ (plainStem P.stem C hC hCr).decorated, ∀ y ∈ D, x < y)
    (k : ℕ) (hcard : D.length = k + 1) (hfirst : P.entries.length = D.headD 0) :
    BodyResponses.Setup (plainStem P.stem C hC hCr) k where
  position := position P C D hC hCr hD hDn hbefore
  stem_eq := rfl
  label_length := hcard
  entries_length := hfirst

theorem bodySetup_newWord (P : Position) (C D : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.stem.root) (hD : D.Pairwise (· < ·))
    (hDn : ∀ x ∈ D, x < P.size)
    (hbefore : ∀ x ∈ (plainStem P.stem C hC hCr).decorated, ∀ y ∈ D, x < y)
    (k : ℕ) (hcard : D.length = k + 1) (hfirst : P.entries.length = D.headD 0) :
    BodyResponses.newWord (bodySetup P C D hC hCr hD hDn hbefore k hcard hfirst).position =
      D ++ P.size :: P.entries := rfl

end Erdos118.LabelOverlays
