import ErdosProblems.Erdos590

/-!
# A Ramsey dichotomy for well-founded countably branching games

This supplies a general uniformization theorem, not the missing height-two
game or the positive partition relation. Builder response families are thin
and meet every infinite set, so the conservative-play condition is not
vacuous. All recursion below is ordinary structural recursion.
-/

open Set

namespace Erdos118.RamseyGame

def AlmostSubset (H K : Set ℕ) : Prop := (H \ K).Finite

theorem almostSubset_of_subset {H K : Set ℕ} (h : H ⊆ K) : AlmostSubset H K := by
  rw [AlmostSubset, Set.sdiff_eq_empty.mpr h]
  exact Set.finite_empty

theorem almostSubset_tail {H K : Set ℕ} (h : AlmostSubset H K) :
    ∃ b : ℕ, ∀ n ∈ H, b < n → n ∈ K := by
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨b, ?_⟩
  intro n hn hbn
  by_contra hnK
  exact (not_le_of_gt hbn) (hb ⟨hn, hnK⟩)

noncomputable def diagonalPick (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Infinite) : ℕ → ℕ
  | 0 => Classical.choose ((hA 0).exists_gt 0)
  | n + 1 => Classical.choose ((hA (n + 1)).exists_gt (diagonalPick A hA n))

theorem diagonalPick_mem (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Infinite) (n : ℕ) :
    diagonalPick A hA n ∈ A n := by
  cases n with
  | zero => exact (Classical.choose_spec ((hA 0).exists_gt 0)).1
  | succ n => exact (Classical.choose_spec
      ((hA (n + 1)).exists_gt (diagonalPick A hA n))).1

theorem diagonalPick_strictMono (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Infinite) :
    StrictMono (diagonalPick A hA) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Classical.choose_spec
    ((hA (n + 1)).exists_gt (diagonalPick A hA n))).2

/-- A decreasing sequence of infinite sets has an infinite subset of its
first member which is almost contained in every member. -/
theorem infinite_pseudointersection (A : ℕ → Set ℕ)
    (hA : ∀ n, (A n).Infinite) (hanti : Antitone A) :
    ∃ H, H ⊆ A 0 ∧ H.Infinite ∧ ∀ n, AlmostSubset H (A n) := by
  let f := diagonalPick A hA
  refine ⟨Set.range f, ?_,
    Set.infinite_range_of_injective (diagonalPick_strictMono A hA).injective, ?_⟩
  · rintro x ⟨n, rfl⟩
    exact hanti (Nat.zero_le n) (diagonalPick_mem A hA n)
  · intro n
    apply ((Finset.range n).finite_toSet.image f).subset
    rintro x ⟨⟨j, rfl⟩, hj⟩
    have hjn : j < n := by
      by_contra h
      exact hj (hanti (Nat.le_of_not_gt h) (diagonalPick_mem A hA j))
    exact ⟨j, Finset.mem_range.mpr hjn, rfl⟩

def TailHereditary (P : Set ℕ → Prop) : Prop :=
  ∀ ⦃H K⦄, AlmostSubset H K → P K → P H

def Dense (P : Set ℕ → Prop) : Prop :=
  ∀ N : Set ℕ, N.Infinite → ∃ H, H ⊆ N ∧ H.Infinite ∧ P H

/-- Countably many tail-hereditary dense predicates can be satisfied together. -/
theorem simultaneous_nat (P : ℕ → Set ℕ → Prop)
    (hher : ∀ n, TailHereditary (P n)) (hdense : ∀ n, Dense (P n))
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∀ n, P n H := by
  classical
  let I := {A : Set ℕ // A.Infinite}
  let step (n : ℕ) (A : I) : I :=
    ⟨Classical.choose (hdense n A.1 A.2),
      (Classical.choose_spec (hdense n A.1 A.2)).2.1⟩
  let seq : ℕ → I := fun n ↦ Nat.rec (⟨N, hN⟩ : I) (fun n A ↦ step n A) n
  have hsucc (n : ℕ) : seq (n + 1) = step n (seq n) := rfl
  have hsub (n : ℕ) : (seq (n + 1)).1 ⊆ (seq n).1 := by
    rw [hsucc]
    exact (Classical.choose_spec (hdense n (seq n).1 (seq n).2)).1
  have hP (n : ℕ) : P n (seq (n + 1)).1 := by
    rw [hsucc]
    exact (Classical.choose_spec (hdense n (seq n).1 (seq n).2)).2.2
  obtain ⟨H, hHsub, hHinf, hHalmost⟩ :=
    infinite_pseudointersection (fun n ↦ (seq n).1) (fun n ↦ (seq n).2)
      (antitone_nat_of_succ_le hsub)
  exact ⟨H, hHsub, hHinf, fun n ↦ hher n (hHalmost (n + 1)) (hP n)⟩

theorem simultaneous_countable {I : Type} [Countable I] [Nonempty I]
    (P : I → Set ℕ → Prop)
    (hher : ∀ i, TailHereditary (P i)) (hdense : ∀ i, Dense (P i))
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∀ i, P i H := by
  obtain ⟨e, he⟩ := exists_surjective_nat I
  obtain ⟨H, hHN, hH, hP⟩ := simultaneous_nat (fun n ↦ P (e n))
    (fun n ↦ hher (e n)) (fun n ↦ hdense (e n)) hN
  refine ⟨H, hHN, hH, ?_⟩
  intro i
  obtain ⟨n, rfl⟩ := he i
  exact hP n

/-- Thinness supplies Nash--Williams; unavoidability supplies legal moves. -/
structure ResponseFamily where
  members : Set (Finset ℕ)
  thin : Erdos590.Larson.NashWilliams.FinThin members
  hits : ∀ H : Set ℕ, H.Infinite → ∃ s ∈ members, (↑s : Set ℕ) ⊆ H

theorem ResponseFamily.nonempty (F : ResponseFamily) : Nonempty F.members := by
  obtain ⟨s, hs, _⟩ := F.hits Set.univ Set.infinite_univ
  exact ⟨s, hs⟩

/-- Every infinite set permits a response above any finite bound. -/
theorem ResponseFamily.conservative_exists (F : ResponseFamily)
    {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ s : F.members, (↑s.1 : Set ℕ) ⊆ H ∧ ∀ n ∈ s.1, b < n := by
  have htail : (H \ Set.Iic b).Infinite := hH.sdiff (Set.finite_Iic b)
  obtain ⟨s, hsF, hs⟩ := F.hits _ htail
  exact ⟨⟨s, hsF⟩, fun _ hn ↦ (hs hn).1,
    fun n hn ↦ lt_of_not_ge (hs hn).2⟩

/-- All trees are well founded by construction, with countable branching. -/
inductive Game where
  | leaf (payoff : Bool)
  | choice (next : ℕ → Game)
  | response (family : ResponseFamily) (next : family.members → Game)

/-- One legal move descends to a child of the game tree. -/
inductive Child : Game → Game → Prop where
  | choice (next : ℕ → Game) (n : ℕ) : Child (next n) (.choice next)
  | response (F : ResponseFamily) (next : F.members → Game) (s : F.members) :
      Child (next s) (.response F next)

theorem child_wellFounded : WellFounded Child := by
  refine ⟨fun G ↦ ?_⟩
  induction G with
  | leaf value =>
    refine Acc.intro _ ?_
    intro _ h
    cases h
  | choice next ih =>
    refine Acc.intro _ ?_
    intro _ h
    cases h with
    | choice _ n => exact ih n
  | response F next ih =>
    refine Acc.intro _ ?_
    intro _ h
    cases h with
    | response _ _ s => exact ih s

/-- A certificate records the value preserved through conservative plays.
`true` permits an architect choice; `false` covers every architect choice. -/
inductive Outcome (H : Set ℕ) : Game → Bool → Prop where
  | leaf (b : Bool) : Outcome H (.leaf b) b
  | choiceTrue (next : ℕ → Game) (n : ℕ) (h : Outcome H (next n) true) :
      Outcome H (.choice next) true
  | choiceFalse (next : ℕ → Game) (h : ∀ n, Outcome H (next n) false) :
      Outcome H (.choice next) false
  | response (F : ResponseFamily) (next : F.members → Game) (b : ℕ) (value : Bool)
      (h : ∀ s : F.members, (↑s.1 : Set ℕ) ⊆ H →
        (∀ n ∈ s.1, b < n) → Outcome H (next s) value) :
      Outcome H (.response F next) value

/-- Certificate validity is preserved after discarding finitely many exceptions. -/
theorem Outcome.almost_mono {K H : Set ℕ} {G : Game} {value : Bool}
    (h : Outcome K G value) (hHK : AlmostSubset H K) : Outcome H G value := by
  induction h generalizing H with
  | leaf b => exact Outcome.leaf b
  | choiceTrue next n _ ih => exact Outcome.choiceTrue next n (ih hHK)
  | choiceFalse next _ ih => exact Outcome.choiceFalse next (fun n ↦ ih n hHK)
  | response F next b value h ih =>
    obtain ⟨d, hd⟩ := almostSubset_tail hHK
    refine Outcome.response F next (max b d) value ?_
    intro s hsH hsbound
    have hsK : (↑s.1 : Set ℕ) ⊆ K := by
      intro n hn
      exact hd n (hsH hn) ((le_max_right b d).trans_lt (hsbound n hn))
    have hsold : ∀ n ∈ s.1, b < n :=
      fun n hn ↦ (le_max_left b d).trans_lt (hsbound n hn)
    exact ih s hsK hsold hHK

/-- The full abstract Ramsey dichotomy, with no assumed winning valuation. -/
theorem dichotomy (G : Game) : Dense (fun H ↦ ∃ value, Outcome H G value) := by
  induction G with
  | leaf value =>
    intro N hN
    exact ⟨N, Subset.rfl, hN, value, Outcome.leaf value⟩
  | choice next ih =>
    intro N hN
    obtain ⟨H, hHN, hH, hcert⟩ := simultaneous_nat
      (fun n H ↦ ∃ value, Outcome H (next n) value)
      (fun _ _ _ hHK ⟨b, hb⟩ ↦ ⟨b, hb.almost_mono hHK⟩) ih hN
    classical
    by_cases hwin : ∃ n, Outcome H (next n) true
    · obtain ⟨n, hn⟩ := hwin
      exact ⟨H, hHN, hH, true, Outcome.choiceTrue next n hn⟩
    · refine ⟨H, hHN, hH, false, Outcome.choiceFalse next ?_⟩
      intro n
      obtain ⟨b, hb⟩ := hcert n
      cases b with
      | false => exact hb
      | true => exact (hwin ⟨n, hb⟩).elim
  | response F next ih =>
    intro N hN
    classical
    let : Nonempty F.members := F.nonempty
    obtain ⟨K, hKN, hK, hcert⟩ := simultaneous_countable
      (fun s H ↦ ∃ value, Outcome H (next s) value)
      (fun _ _ _ hHK ⟨b, hb⟩ ↦ ⟨b, hb.almost_mono hHK⟩) ih hN
    let c : Finset ℕ → Bool := fun s ↦
      if hs : s ∈ F.members then Classical.choose (hcert ⟨s, hs⟩) else false
    obtain ⟨H, hHK, hH, value, hmono⟩ :=
      Erdos590.Larson.NashWilliams.nashWilliams_two F.members F.thin c hK
    refine ⟨H, hHK.trans hKN, hH, value, Outcome.response F next 0 value ?_⟩
    intro s hsH _
    have hc : c s.1 = Classical.choose (hcert s) := by simp [c, s.2]
    have hout := (Classical.choose_spec (hcert s)).almost_mono
      (almostSubset_of_subset hHK)
    rw [← hc, hmono s.1 s.2 hsH] at hout
    exact hout

/-- The two certificates cannot coexist on an infinite set. This uses
unavoidability at response nodes, not merely thinness. -/
theorem Outcome.not_both {H : Set ℕ} (hH : H.Infinite) (G : Game)
    (hone : Outcome H G true) (hzero : Outcome H G false) : False := by
  induction G with
  | leaf value =>
    cases hone
    cases hzero
  | choice next ih =>
    cases hone with
    | choiceTrue _ n hn =>
      cases hzero with
      | choiceFalse _ hz => exact ih n hn (hz n)
  | response F next ih =>
    cases hone with
    | response _ _ b _ hb =>
      cases hzero with
      | response _ _ c _ hc =>
        obtain ⟨s, hsH, hsbound⟩ := F.conservative_exists hH (max b c)
        exact ih s
          (hb s hsH (fun n hn ↦ (le_max_left b c).trans_lt (hsbound n hn)))
          (hc s hsH (fun n hn ↦ (le_max_right b c).trans_lt (hsbound n hn)))

/-- The homogeneous game value is unique on the thinned infinite set. -/
theorem dichotomy_unique (G : Game) {N : Set ℕ} (hN : N.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃! value, Outcome H G value := by
  obtain ⟨H, hHN, hH, value, hval⟩ := dichotomy G N hN
  refine ⟨H, hHN, hH, value, hval, ?_⟩
  intro other hother
  cases value <;> cases other
  · rfl
  · exact (Outcome.not_both hH G hother hval).elim
  · exact (Outcome.not_both hH G hval hother).elim
  · rfl

/-- At a leaf a certificate must agree with the actual payoff. -/
theorem outcome_leaf_iff {H : Set ℕ} {payoff value : Bool} :
    Outcome H (.leaf payoff) value ↔ payoff = value := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Outcome.leaf payoff

/-- The game of choosing two complete objects, with graph adjacency as payoff. -/
noncomputable def pairGame (F : ResponseFamily) (G : SimpleGraph F.members) : Game := by
  classical
  exact .response F (fun s ↦ .response F (fun t ↦ .leaf (decide (G.Adj s t))))

/-- A uniform blue two-completion game always supplies a blue triangle. -/
theorem pairGame_triangle (F : ResponseFamily) (G : SimpleGraph F.members)
    {H : Set ℕ} (hH : H.Infinite) (hwin : Outcome H (pairGame F G) true) :
    ∃ s t u : F.members, G.Adj s t ∧ G.Adj s u ∧ G.Adj t u := by
  classical
  have edge {s t : F.members}
      (h : Outcome H (.leaf (decide (G.Adj s t))) true) : G.Adj s t :=
    of_decide_eq_true (outcome_leaf_iff.mp h)
  unfold pairGame at hwin
  cases hwin with
  | response _ _ b0 _ hfirst =>
    obtain ⟨s, hsH, hs0⟩ := F.conservative_exists hH b0
    have hs := hfirst s hsH hs0
    cases hs with
    | response _ _ bs _ hsecondS =>
      obtain ⟨t, htH, htbound⟩ := F.conservative_exists hH (max b0 bs)
      have ht0 : ∀ n ∈ t.1, b0 < n :=
        fun n hn ↦ (le_max_left b0 bs).trans_lt (htbound n hn)
      have hts : ∀ n ∈ t.1, bs < n :=
        fun n hn ↦ (le_max_right b0 bs).trans_lt (htbound n hn)
      have hst := edge (hsecondS t htH hts)
      have ht := hfirst t htH ht0
      cases ht with
      | response _ _ bt _ hsecondT =>
        obtain ⟨u, huH, hubound⟩ := F.conservative_exists hH (max bs bt)
        have hus : ∀ n ∈ u.1, bs < n :=
          fun n hn ↦ (le_max_left bs bt).trans_lt (hubound n hn)
        have hut : ∀ n ∈ u.1, bt < n :=
          fun n hn ↦ (le_max_right bs bt).trans_lt (hubound n hn)
        exact ⟨s, t, u, hst, edge (hsecondS u huH hus), edge (hsecondT u huH hut)⟩

/-- Triangle-freeness rules out the blue value in the two-completion game. -/
theorem pairGame_not_true (F : ResponseFamily) (G : SimpleGraph F.members)
    (htri : G.CliqueFree 3) {H : Set ℕ} (hH : H.Infinite) :
    ¬ Outcome H (pairGame F G) true := by
  intro hwin
  obtain ⟨s, t, u, hst, hsu, htu⟩ := pairGame_triangle F G hH hwin
  exact htri {s, t, u}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

/-- Uniform red tails for pairs of complete responses. No order-type claim
about the family of responses is inferred from this local conclusion. -/
theorem pairGame_red_thinning (F : ResponseFamily) (G : SimpleGraph F.members)
    (htri : G.CliqueFree 3) {N : Set ℕ} (hN : N.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ b0 : ℕ,
      ∀ s : F.members, (↑s.1 : Set ℕ) ⊆ H → (∀ n ∈ s.1, b0 < n) →
        ∃ bs : ℕ, ∀ t : F.members, (↑t.1 : Set ℕ) ⊆ H →
          (∀ n ∈ t.1, bs < n) → ¬ G.Adj s t := by
  classical
  obtain ⟨H, hHN, hH, value, hval⟩ := dichotomy (pairGame F G) N hN
  cases value with
  | true => exact (pairGame_not_true F G htri hH hval).elim
  | false =>
    unfold pairGame at hval
    cases hval with
    | response _ _ b0 _ hfirst =>
      refine ⟨H, hHN, hH, b0, ?_⟩
      intro s hsH hs0
      have hs := hfirst s hsH hs0
      cases hs with
      | response _ _ bs _ hsecond =>
        refine ⟨bs, ?_⟩
        intro t htH hts
        exact of_decide_eq_false (outcome_leaf_iff.mp (hsecond t htH hts))

end Erdos118.RamseyGame
