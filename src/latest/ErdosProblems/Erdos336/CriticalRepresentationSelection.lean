import ErdosProblems.Erdos336.KneserConsequences

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The new sums of `C`. -/
def criticalNewSums (C : Finset G) : Finset G := (C + C) \ C

/-- A choice of one ordered representation for every new sum. -/
structure CriticalSelector (C : Finset G) where
  left : G → G
  right : G → G
  left_mem : ∀ s ∈ criticalNewSums C, left s ∈ C
  right_mem : ∀ s ∈ criticalNewSums C, right s ∈ C
  add_eq : ∀ s ∈ criticalNewSums C, left s + right s = s

noncomputable def defaultCriticalSelector (C : Finset G) : CriticalSelector C := by
  classical
  let rep : G → G × G := fun s =>
    if hs : s ∈ criticalNewSums C then
      let w := Finset.mem_add.mp (Finset.mem_sdiff.mp hs).1
      (w.choose, w.choose_spec.2.choose)
    else (0, 0)
  refine ⟨fun s => (rep s).1, fun s => (rep s).2, ?_, ?_, ?_⟩
  · intro s hs
    dsimp [rep]
    split <;> rename_i h
    · exact (Finset.mem_add.mp (Finset.mem_sdiff.mp h).1).choose_spec.1
    · exact (h hs).elim
  · intro s hs
    dsimp [rep]
    split <;> rename_i h
    · exact (Finset.mem_add.mp (Finset.mem_sdiff.mp h).1).choose_spec.2.choose_spec.1
    · exact (h hs).elim
  · intro s hs
    dsimp [rep]
    split <;> rename_i h
    · exact (Finset.mem_add.mp (Finset.mem_sdiff.mp h).1).choose_spec.2.choose_spec.2
    · exact (h hs).elim

/-- Number of endpoint occurrences of `g` in a selector. -/
def selectorLoad {C : Finset G} (r : CriticalSelector C) (g : G) : ℕ :=
  ((criticalNewSums C).filter fun s => r.left s = g).card +
  ((criticalNewSums C).filter fun s => r.right s = g).card

/-- If a vertex occurs more often than the number of selected edges, every
selected edge is incident to it, and its load is exactly one more than the
number of edges. -/
theorem overloaded_selector_is_star
    {C : Finset G} (r : CriticalSelector C) (g : G)
    (hover : (criticalNewSums C).card < selectorLoad r g) :
    selectorLoad r g = (criticalNewSums C).card + 1 ∧
      ∀ s ∈ criticalNewSums C, r.left s = g ∨ r.right s = g := by
  classical
  let D := criticalNewSums C
  let L := D.filter fun s => r.left s = g
  let R := D.filter fun s => r.right s = g
  have hLsub : L ⊆ D := Finset.filter_subset _ _
  have hRsub : R ⊆ D := Finset.filter_subset _ _
  have hUsub : L ∪ R ⊆ D := Finset.union_subset hLsub hRsub
  have hIsub : L ∩ R ⊆ {g + g} := by
    intro s hs
    have hsL := (Finset.mem_filter.mp (Finset.mem_inter.mp hs).1)
    have hsR := (Finset.mem_filter.mp (Finset.mem_inter.mp hs).2)
    have hadd := r.add_eq s hsL.1
    simp only [hsL.2, hsR.2] at hadd
    simpa [hadd]
  have hUcard : (L ∪ R).card ≤ D.card := Finset.card_le_card hUsub
  have hIcard : (L ∩ R).card ≤ 1 := by
    exact le_trans (Finset.card_le_card hIsub) (by simp)
  have hcardId := Finset.card_union_add_card_inter L R
  have hload : selectorLoad r g = L.card + R.card := rfl
  have hover' : D.card < L.card + R.card := by
    simpa [hload] using hover
  have hloadEq : selectorLoad r g = D.card + 1 := by omega
  have hDU : D.card ≤ (L ∪ R).card := by omega
  have hUeq : L ∪ R = D :=
    Finset.eq_of_subset_of_card_le hUsub hDU
  refine ⟨by simpa [D] using hloadEq, ?_⟩
  intro s hs
  have : s ∈ L ∪ R := by rw [hUeq]; exact hs
  rcases Finset.mem_union.mp this with hsL | hsR
  · exact Or.inl (Finset.mem_filter.mp hsL).2
  · exact Or.inr (Finset.mem_filter.mp hsR).2

/-- Outside the centre of an overloaded star, every vertex has load at most
one. -/
theorem selector_load_le_one_away_from_star
    {C : Finset G} (r : CriticalSelector C) (g x : G) (hxg : x ≠ g)
    (hstar : ∀ s ∈ criticalNewSums C, r.left s = g ∨ r.right s = g) :
    selectorLoad r x ≤ 1 := by
  classical
  let D := criticalNewSums C
  let L := D.filter fun s => r.left s = x
  let R := D.filter fun s => r.right s = x
  have hLsub : L ⊆ {x + g} := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    rcases hstar s hs'.1 with hsg | hsg
    · exact (hxg (hs'.2.symm.trans hsg)).elim
    · have hadd := r.add_eq s hs'.1
      rw [hs'.2, hsg] at hadd
      simpa [hadd]
  have hRsub : R ⊆ {g + x} := by
    intro s hs
    have hs' := Finset.mem_filter.mp hs
    rcases hstar s hs'.1 with hsg | hsg
    · have hadd := r.add_eq s hs'.1
      rw [hsg, hs'.2] at hadd
      simpa [add_comm, hadd]
    · exact (hxg (hs'.2.symm.trans hsg)).elim
  have hRsub' : R ⊆ {x + g} := by
    simpa [add_comm] using hRsub
  have hUsub : L ∪ R ⊆ {x + g} := Finset.union_subset hLsub hRsub'
  have hUcard : (L ∪ R).card ≤ 1 :=
    le_trans (Finset.card_le_card hUsub) (by simp)
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro s hsL hsR
    have hl := Finset.mem_filter.mp hsL
    have hr := Finset.mem_filter.mp hsR
    rcases hstar s hl.1 with h | h
    · exact hxg (hl.2.symm.trans h)
    · exact hxg (hr.2.symm.trans h)
  change L.card + R.card ≤ 1
  rw [← Finset.card_union_of_disjoint hdisj]
  exact hUcard

/-- Replace the selected representation of one new sum. -/
noncomputable def CriticalSelector.replace
    {C : Finset G} (r : CriticalSelector C) (s₀ b c : G)
    (hs₀ : s₀ ∈ criticalNewSums C) (hb : b ∈ C) (hc : c ∈ C)
    (hbc : b + c = s₀) : CriticalSelector C where
  left s := if s = s₀ then b else r.left s
  right s := if s = s₀ then c else r.right s
  left_mem s hs := by
    split <;> rename_i h
    · exact hb
    · exact r.left_mem s hs
  right_mem s hs := by
    split <;> rename_i h
    · exact hc
    · exact r.right_mem s hs
  add_eq s hs := by
    split <;> rename_i h
    · simpa [h] using hbc
    · exact r.add_eq s hs

/-- Replacing one edge of an overloaded star by an edge avoiding the centre
produces a balanced selector as soon as there are at least three new sums. -/
theorem balanced_selector_of_offcenter_representation
    {C : Finset G} (r : CriticalSelector C) (g s₀ b c : G)
    (hN : 3 ≤ (criticalNewSums C).card)
    (hover : (criticalNewSums C).card < selectorLoad r g)
    (hs₀ : s₀ ∈ criticalNewSums C)
    (hb : b ∈ C) (hc : c ∈ C) (hbg : b ≠ g) (hcg : c ≠ g)
    (hbc : b + c = s₀) :
    ∃ r' : CriticalSelector C,
      ∀ x ∈ C, selectorLoad r' x ≤ (criticalNewSums C).card := by
  classical
  let r' := r.replace s₀ b c hs₀ hb hc hbc
  obtain ⟨hloadg, hstar⟩ := overloaded_selector_is_star r g hover
  refine ⟨r', ?_⟩
  intro x hxC
  let D := criticalNewSums C
  let L := D.filter fun s => r.left s = x
  let R := D.filter fun s => r.right s = x
  let L' := D.filter fun s => r'.left s = x
  let R' := D.filter fun s => r'.right s = x
  by_cases hxg : x = g
  · subst x
    have hLsub : L' ⊆ L.erase s₀ := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hsne : s ≠ s₀ := by
        intro h
        subst s
        have hval := hs'.2
        change (if s₀ = s₀ then b else r.left s₀) = g at hval
        simp only [if_pos rfl] at hval
        exact hbg hval
      apply Finset.mem_erase.mpr
      refine ⟨hsne, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨hs'.1, ?_⟩
      have hval := hs'.2
      change (if s = s₀ then b else r.left s) = g at hval
      rw [if_neg hsne] at hval
      exact hval
    have hRsub : R' ⊆ R.erase s₀ := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      have hsne : s ≠ s₀ := by
        intro h
        subst s
        have hval := hs'.2
        change (if s₀ = s₀ then c else r.right s₀) = g at hval
        simp only [if_pos rfl] at hval
        exact hcg hval
      apply Finset.mem_erase.mpr
      refine ⟨hsne, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨hs'.1, ?_⟩
      have hval := hs'.2
      change (if s = s₀ then c else r.right s) = g at hval
      rw [if_neg hsne] at hval
      exact hval
    have hLc := Finset.card_le_card hLsub
    have hRc := Finset.card_le_card hRsub
    have hincident := hstar s₀ hs₀
    have hdrop : (L.erase s₀).card + (R.erase s₀).card < L.card + R.card := by
      rcases hincident with hl | hr
      · have hsL : s₀ ∈ L := Finset.mem_filter.mpr ⟨hs₀, hl⟩
        have hLeq := Finset.card_erase_of_mem hsL
        have hLpos : 0 < L.card := Finset.card_pos.mpr ⟨s₀, hsL⟩
        have hRle : (R.erase s₀).card ≤ R.card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        omega
      · have hsR : s₀ ∈ R := Finset.mem_filter.mpr ⟨hs₀, hr⟩
        have hReq := Finset.card_erase_of_mem hsR
        have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨s₀, hsR⟩
        have hLle : (L.erase s₀).card ≤ L.card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        omega
    change L'.card + R'.card ≤ D.card
    have hloadg' : L.card + R.card = D.card + 1 := by
      simpa [D, L, R, selectorLoad] using hloadg
    omega
  · have hold : selectorLoad r x ≤ 1 :=
      selector_load_le_one_away_from_star r g x hxg hstar
    have hLsub : L' ⊆ insert s₀ L := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      by_cases hss : s = s₀
      · simp [hss]
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨hs'.1, ?_⟩
        have hval := hs'.2
        change (if s = s₀ then b else r.left s) = x at hval
        rw [if_neg hss] at hval
        exact hval
    have hRsub : R' ⊆ insert s₀ R := by
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      by_cases hss : s = s₀
      · simp [hss]
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨hs'.1, ?_⟩
        have hval := hs'.2
        change (if s = s₀ then c else r.right s) = x at hval
        rw [if_neg hss] at hval
        exact hval
    have hLc := Finset.card_le_card hLsub
    have hRc := Finset.card_le_card hRsub
    have hLi : (insert s₀ L).card ≤ L.card + 1 := Finset.card_insert_le _ _
    have hRi : (insert s₀ R).card ≤ R.card + 1 := Finset.card_insert_le _ _
    change L'.card + R'.card ≤ D.card
    have hold' : L.card + R.card ≤ 1 := by
      simpa [D, L, R, selectorLoad] using hold
    have hN' : 3 ≤ D.card := by simpa [D] using hN
    omega

/-- An overloaded selector has a loop at its centre. -/
theorem overloaded_selector_has_center_loop
    {C : Finset G} (r : CriticalSelector C) (g : G)
    (hover : (criticalNewSums C).card < selectorLoad r g) :
    g + g ∈ criticalNewSums C := by
  classical
  let D := criticalNewSums C
  let L := D.filter fun s => r.left s = g
  let R := D.filter fun s => r.right s = g
  have hUsub : L ∪ R ⊆ D := Finset.union_subset
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hUcard := Finset.card_le_card hUsub
  have hcardId := Finset.card_union_add_card_inter L R
  have hover' : D.card < L.card + R.card := by simpa [D, L, R, selectorLoad] using hover
  have hIne : (L ∩ R).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨s, hs⟩ := hIne
  have hsL := Finset.mem_filter.mp (Finset.mem_inter.mp hs).1
  have hsR := Finset.mem_filter.mp (Finset.mem_inter.mp hs).2
  have hadd := r.add_eq s hsL.1
  rw [hsL.2, hsR.2] at hadd
  rw [hadd]
  exact hsL.1

/-- Either the selected representations can be balanced, or an overloaded
centre remains after deleting which the set is closed under addition. -/
theorem balanced_selector_or_offcenter_closed
    {C : Finset G} (hzero : 0 ∈ C)
    (hN : 3 ≤ (criticalNewSums C).card) :
    (∃ r : CriticalSelector C,
      ∀ x ∈ C, selectorLoad r x ≤ (criticalNewSums C).card) ∨
    ∃ (r : CriticalSelector C) (g : G), g ∈ C ∧ g ≠ 0 ∧
      (criticalNewSums C).card < selectorLoad r g ∧
      ∀ b ∈ C, b ≠ g → ∀ c ∈ C, c ≠ g → b + c ∈ C := by
  classical
  by_cases hExists : ∃ r : CriticalSelector C,
      ∀ x ∈ C, selectorLoad r x ≤ (criticalNewSums C).card
  · exact Or.inl hExists
  · push_neg at hExists
    let r := defaultCriticalSelector C
    obtain ⟨g, hgC, hover⟩ := hExists r
    right
    refine ⟨r, g, hgC, ?_, hover, ?_⟩
    · intro hg0
      subst g
      have hloop := overloaded_selector_has_center_loop r 0 hover
      have hloop' : (0 : G) ∈ criticalNewSums C := by simpa using hloop
      exact (Finset.mem_sdiff.mp hloop').2 hzero
    · intro b hbC hbg c hcC hcg
      by_contra hout
      have hs₀ : b + c ∈ criticalNewSums C :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_add.mpr ⟨b, hbC, c, hcC, rfl⟩, hout⟩
      obtain ⟨r', hr'⟩ := balanced_selector_of_offcenter_representation
        r g (b + c) b c hN hover hs₀ hbC hcC hbg hcg rfl
      obtain ⟨x, hxC, hbad⟩ := hExists r'
      exact (Nat.not_lt_of_ge (hr' x hxC)) hbad

end Erdos336
