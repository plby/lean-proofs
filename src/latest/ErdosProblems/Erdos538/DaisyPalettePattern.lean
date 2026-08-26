import ErdosProblems.Erdos538.WeightedPalette

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

noncomputable section
open Erdos538.IsotropicKernel

/-- The multiset pattern induced by a finite uniform daisy palette. -/
def DaisyPalettePattern
    (k m : ℕ) (F : Finset (UniformChildren m (k - 1)))
    (s : Multiset (Fin m)) : Prop :=
  s.Nodup ∧ s.card = k ∧ ∃ E ∈ F, E.1 = s.toFinset

/-- On a duplicate-free parent, the deletion count of a daisy-palette pattern
is bounded by the palette's parent-facet count. -/
theorem daisyPalette_deletionCount_le_two_of_nodup
    (k m : ℕ) (hk : 0 < k)
    (F : Finset (UniformChildren m (k - 1)))
    (hcap : ∀ T : Finset (Fin m), ∀ hT : T.card = (k - 1) + 2,
      (Finset.univ.filter fun x : T => parentFacet T hT x ∈ F).card ≤ 2)
    (s : Multiset (Fin m)) (hs : s.Nodup) :
    patternDeletionCount (DaisyPalettePattern k m F) s ≤ 2 := by
  classical
  let good := s.filter fun a => DaisyPalettePattern k m F (s.erase a)
  by_cases hgood : good = 0
  · simp [patternDeletionCount, good, hgood]
  · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hgood
    have has : a ∈ s := (Multiset.mem_filter.mp ha).1
    have haPat := (Multiset.mem_filter.mp ha).2
    have heraseCard : (s.erase a).card = k := haPat.2.1
    have hsCard : s.card = k + 1 := by
      have h := Multiset.card_erase_add_one has
      omega
    let T := s.toFinset
    have hTcard : T.card = (k - 1) + 2 := by
      rw [Multiset.toFinset_card_of_nodup hs, hsCard]
      omega
    let omissions := Finset.univ.filter fun x : T =>
      parentFacet T hTcard x ∈ F
    have hgoodNodup : good.Nodup := by
      exact hs.filter _
    let emb : (↥good.toFinset) ↪ (↥T) :=
      { toFun := fun b => ⟨b.1, Multiset.mem_toFinset.mpr
          (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp b.2)).1⟩
        inj' := by
          intro b c hbc
          apply Subtype.ext
          exact congrArg (fun z : T => z.1) hbc }
    have himage : Finset.univ.map emb ⊆ omissions := by
      intro bx hbx
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hbx
      have hbgood : b.1 ∈ good := Multiset.mem_toFinset.mp b.2
      have hbs : b.1 ∈ s := (Multiset.mem_filter.mp hbgood).1
      have hbPat := (Multiset.mem_filter.mp hbgood).2
      rcases hbPat.2.2 with ⟨E, hEF, hE⟩
      let bx : T := ⟨b.1, Multiset.mem_toFinset.mpr hbs⟩
      have herase : T.erase b.1 = (s.erase b.1).toFinset := by
        ext y
        simp only [T, Multiset.mem_toFinset, Finset.mem_erase]
        constructor
        · rintro ⟨hyb, hys⟩
          exact hs.mem_erase_iff.mpr ⟨hyb, hys⟩
        · intro hy
          have hpair := hs.mem_erase_iff.mp hy
          exact ⟨hpair.1, hpair.2⟩
      have hfacet : parentFacet T hTcard bx = E := by
        apply Subtype.ext
        change T.erase b.1 = E.1
        rw [herase, hE.symm]
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hfacet ▸ hEF⟩
    have hcardle : good.toFinset.card ≤ omissions.card := by
      calc
        good.toFinset.card = (Finset.univ : Finset good.toFinset).card := by simp
        _ = (Finset.univ.map emb).card := by rw [Finset.card_map]
        _ ≤ omissions.card := Finset.card_le_card himage
    calc
      patternDeletionCount (DaisyPalettePattern k m F) s = good.card := rfl
      _ = good.toFinset.card := Multiset.toFinset_card_of_nodup hgoodNodup |>.symm
      _ ≤ omissions.card := hcardle
      _ ≤ 2 := hcap T hTcard

/-- Every finite palette with at most two facets per parent induces a full
multiplicity-aware cap-two multiset pattern. -/
theorem daisyPalette_patternCap_two
    (k m : ℕ) (hk : 0 < k)
    (F : Finset (UniformChildren m (k - 1)))
    (hcap : ∀ T : Finset (Fin m), ∀ hT : T.card = (k - 1) + 2,
      (Finset.univ.filter fun x : T => parentFacet T hT x ∈ F).card ≤ 2) :
    PatternCap 2 (DaisyPalettePattern k m F) := by
  classical
  intro s
  by_cases hs : s.Nodup
  · exact daisyPalette_deletionCount_le_two_of_nodup k m hk F hcap s hs
  · calc
      patternDeletionCount (DaisyPalettePattern k m F) s ≤
          (s.filter fun a => (s.erase a).Nodup).card := by
        unfold patternDeletionCount
        apply Multiset.card_le_card
        apply Multiset.monotone_filter_right s
        intro a ha
        exact ha.1
      _ ≤ 2 := card_filter_erase_nodup_le_two s hs

end

end Erdos538
