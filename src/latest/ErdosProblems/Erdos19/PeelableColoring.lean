import ErdosProblems.Erdos19.DenseCore

/-! # Extending a coloring from a dense core

Relative peelability permits extension from an arbitrary proper coloring of
the core. The list condition is imposed only outside that core.
-/

namespace Erdos19

open Finset

theorem IsPeelableOutside.exists_list_coloring_extension
    {V C : Type*} [DecidableEq V] [DecidableEq C]
    {G : SimpleGraph V} {A S : Finset V} {k : ℕ}
    (hpeel : IsPeelableOutside G A S k) (hSA : S ⊆ A)
    (L : V → Finset C) (hL : ∀ v ∈ A \ S, k ≤ (L v).card)
    (c₀ : V → C)
    (hc₀ : ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → c₀ v ≠ c₀ w) :
    ∃ c : V → C, (∀ v ∈ S, c v = c₀ v) ∧
      (∀ v ∈ A \ S, c v ∈ L v) ∧
      ∀ v ∈ A, ∀ w ∈ A, G.Adj v w → c v ≠ c w := by
  classical
  have extend : ∀ T : Finset V, T ⊆ A \ S →
      ∃ c : V → C, (∀ v ∈ S, c v = c₀ v) ∧
        (∀ v ∈ T, c v ∈ L v) ∧
        ∀ v ∈ S ∪ T, ∀ w ∈ S ∪ T, G.Adj v w → c v ≠ c w := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hT
      by_cases hempty : T = ∅
      · subst T
        exact ⟨c₀, by simp, by simp, by simpa using hc₀⟩
      obtain ⟨v, hvT, hvdeg⟩ := hpeel T hT (nonempty_iff_ne_empty.mpr hempty)
      obtain ⟨c, hcS, hcL, hc⟩ :=
        ih (T.erase v) (erase_ssubset hvT) (subset_trans (erase_subset v T) hT)
      let N := (S ∪ T.erase v).filter (G.Adj v)
      have hN : N.card < (L v).card := by
        calc
          N.card ≤ ((S ∪ T).filter (G.Adj v)).card := by
            apply card_le_card
            exact filter_subset_filter _ (union_subset_union_right (erase_subset v T))
          _ < k := hvdeg
          _ ≤ (L v).card := hL v (hT hvT)
      have himage : (N.image c).card < (L v).card := card_image_le.trans_lt hN
      obtain ⟨a, haL, ha⟩ := exists_mem_notMem_of_card_lt_card himage
      have hvc : ∀ w ∈ S ∪ T.erase v, G.Adj v w → a ≠ c w := by
        intro w hw hvw heq
        exact ha (mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, hvw⟩, heq.symm⟩)
      have hvS : v ∉ S := (mem_sdiff.mp (hT hvT)).2
      have hmem : ∀ w ∈ S ∪ T, w ≠ v → w ∈ S ∪ T.erase v := by
        intro w hw hwv
        rcases mem_union.mp hw with hwS | hwT
        · exact mem_union_left _ hwS
        · exact mem_union_right _ (mem_erase.mpr ⟨hwv, hwT⟩)
      refine ⟨Function.update c v a, ?_, ?_, ?_⟩
      · intro w hw
        have hwv : w ≠ v := fun h ↦ hvS (h ▸ hw)
        simpa [Function.update_of_ne hwv] using hcS w hw
      · intro w hw
        by_cases hwv : w = v
        · simpa [hwv] using haL
        · simpa [Function.update_of_ne hwv] using hcL w (mem_erase.mpr ⟨hwv, hw⟩)
      · intro w hw z hz hwz
        by_cases hwv : w = v
        · have hzv : z ≠ v := fun h ↦ hwz.ne (hwv.trans h.symm)
          simpa [hwv, Function.update_of_ne hzv] using
            hvc z (hmem z hz hzv) (hwv ▸ hwz)
        · by_cases hzv : z = v
          · simpa [hzv, Function.update_of_ne hwv] using
              (hvc w (hmem w hw hwv) (hzv ▸ hwz.symm)).symm
          · simpa [Function.update_of_ne hwv, Function.update_of_ne hzv] using
              hc w (hmem w hw hwv) z (hmem z hz hzv) hwz
  obtain ⟨c, hcS, hcL, hc⟩ := extend (A \ S) (Subset.refl _)
  refine ⟨c, hcS, hcL, ?_⟩
  simpa only [union_sdiff_of_subset hSA] using hc

#print axioms IsPeelableOutside.exists_list_coloring_extension

end Erdos19
