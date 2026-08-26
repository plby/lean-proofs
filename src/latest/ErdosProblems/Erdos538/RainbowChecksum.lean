import ErdosProblems.Erdos538.PatternTransfer

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rainbow checksum pattern families

This is the elementary `H_3^k`-free checksum construction.  A pattern is
selected when its labels are all distinct and its additive checksum lies in a
small residue set.
-/

namespace Erdos538

/-- Duplicate-free patterns of cardinality `k` whose additive checksum lies in
`R`. -/
def RainbowChecksum {G : Type*} [DecidableEq G] [AddCommMonoid G]
    (k : ℕ) (R : Finset G) (s : Multiset G) : Prop :=
  s.Nodup ∧ s.card = k ∧ s.sum ∈ R

/-- If deleting one label makes a non-duplicate-free target duplicate-free,
then at most two occurrences can have this property. -/
theorem card_filter_erase_nodup_le_two {α : Type*} [DecidableEq α]
    (s : Multiset α) (hs : ¬s.Nodup) :
    (s.filter fun a => (s.erase a).Nodup).card ≤ 2 := by
  classical
  let good := s.filter fun a => (s.erase a).Nodup
  change good.card ≤ 2
  by_cases hempty : good = 0
  · rw [hempty]
    simp
  · obtain ⟨c, hcgood⟩ := Multiset.exists_mem_of_ne_zero hempty
    have hcs : c ∈ s := (Multiset.mem_filter.mp hcgood).1
    have hcNodup : (s.erase c).Nodup := (Multiset.mem_filter.mp hcgood).2
    have hcountc : s.count c ≤ 2 := by
      have hle : (s.erase c).count c ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hcNodup c
      rw [Multiset.count_erase_self] at hle
      have hpos : 0 < s.count c := Multiset.count_pos.mpr hcs
      omega
    have hall : ∀ d ∈ good, c = d := by
      intro d hdgood
      have hds : d ∈ s := (Multiset.mem_filter.mp hdgood).1
      have hdNodup : (s.erase d).Nodup := (Multiset.mem_filter.mp hdgood).2
      by_contra hcd
      have hdc : d ≠ c := Ne.symm hcd
      have hcountc_le_one : s.count c ≤ 1 := by
        rw [← Multiset.count_erase_of_ne hcd s]
        exact Multiset.nodup_iff_count_le_one.mp hdNodup c
      have hdup : ∃ x, 1 < s.count x := by
        by_contra hnone
        apply hs
        rw [Multiset.nodup_iff_count_le_one]
        intro x
        have := not_lt.mp (not_exists.mp hnone x)
        omega
      obtain ⟨x, hx⟩ := hdup
      have hxc : x = c := by
        by_contra hne
        have hxle : s.count x ≤ 1 := by
          rw [← Multiset.count_erase_of_ne hne s]
          exact Multiset.nodup_iff_count_le_one.mp hcNodup x
        omega
      subst x
      omega
    have hcountEq : good.count c = good.card :=
      Multiset.count_eq_card.mpr hall
    have hleFilter : good.count c ≤ s.count c := by
      simp only [good, Multiset.count_filter]
      split <;> omega
    omega

/-- On a duplicate-free target, selected deletion checksums inject into the
allowed residue set. -/
theorem rainbowChecksum_deletionCount_le_residues
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    (k : ℕ) (R : Finset G) (s : Multiset G) (hs : s.Nodup) :
    patternDeletionCount (RainbowChecksum k R) s ≤ R.card := by
  classical
  let good := s.filter fun a => RainbowChecksum k R (s.erase a)
  have hgoodNodup : good.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    have hle : good.count a ≤ s.count a := by
      simp only [good, Multiset.count_filter]
      split <;> omega
    exact hle.trans (Multiset.nodup_iff_count_le_one.mp hs a)
  have hmaps : Set.MapsTo (fun a => s.sum - a) (good.toFinset : Set G) (R : Set G) := by
    intro a ha
    have hagood : a ∈ good := Multiset.mem_toFinset.mp ha
    rcases Multiset.mem_filter.mp hagood with ⟨has, haSelect⟩
    have hsum : (s.erase a).sum = s.sum - a := by
      have h := Multiset.sum_erase has
      rw [← h]
      simp
    change s.sum - a ∈ R
    rw [← hsum]
    exact haSelect.2.2
  have hinj : Set.InjOn (fun a => s.sum - a) (good.toFinset : Set G) := by
    intro a _ b _ hab
    exact sub_right_injective hab
  have hcard : good.toFinset.card ≤ R.card :=
    Finset.card_le_card_of_injOn (fun a => s.sum - a) hmaps hinj
  have hgoodCard : good.card = good.toFinset.card := by
    exact (Multiset.toFinset_card_of_nodup hgoodNodup).symm
  simpa [patternDeletionCount, good, hgoodCard] using hcard

/-- A rainbow checksum family with at most two allowed residues obeys the full
multiplicity-weighted cap two. -/
theorem rainbowChecksum_patternCap_two
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    (k : ℕ) (R : Finset G) (hR : R.card ≤ 2) :
    PatternCap 2 (RainbowChecksum k R) := by
  classical
  intro s
  by_cases hs : s.Nodup
  · exact (rainbowChecksum_deletionCount_le_residues k R s hs).trans hR
  · calc
      patternDeletionCount (RainbowChecksum k R) s
          ≤ (s.filter fun a => (s.erase a).Nodup).card := by
            unfold patternDeletionCount
            apply Multiset.card_le_card
            apply Multiset.monotone_filter_right s
            intro a ha
            exact ha.1
      _ ≤ 2 := card_filter_erase_nodup_le_two s hs

/-- Therefore every prime coloring by an additive group and every two-residue
checksum rule induces an admissible squarefree integer family. -/
theorem rainbowChecksum_integerFamily_admissible
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    {N : ℕ} (k : ℕ) (R : Finset G) (hR : R.card ≤ 2)
    (color : ℕ → G) :
    Admissible 2 N (patternIntegerFamily N color (RainbowChecksum k R)) :=
  patternIntegerFamily_admissible_of_patternCap (by omega) color
    (RainbowChecksum k R) (rainbowChecksum_patternCap_two k R hR)

end Erdos538
