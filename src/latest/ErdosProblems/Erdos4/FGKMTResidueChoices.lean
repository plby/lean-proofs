import ErdosProblems.Erdos4.FGKMTGrowingPrimeCovering

/-! Translate the initial shifted sieve and source laws into actual residue covers. -/

namespace Erdos4.FGKMT

open Classical RandomResidueSieve

variable (sieve sources targets : Finset ℕ) [∀ l : sieve, Fact (l.val).Prime]

noncomputable def remainingPrimeTargets (Y : ℕ)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val) : Finset ℕ :=
  (sourceSurvivors sources targets
    (initialSurvivors (fun l : sieve => l.val) Y targets a) b).image (fun q : targets => q.val)

theorem remainingPrimeTargets_subset (Y : ℕ)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val) :
    remainingPrimeTargets sieve sources targets Y a b ⊆ targets := by
  intro q hq
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hq
  exact ht ▸ t.property

theorem mem_remainingPrimeTargets (Y q : ℕ) (hq : q ∈ targets)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val) :
    q ∈ remainingPrimeTargets sieve sources targets Y a b ↔
      Survives (fun l : sieve => l.val) a {q + Y} ∧
        ∀ p : sources, (q : ZMod p.val) ≠ b p := by
  constructor
  · intro hh
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hh
    have hdata := Finset.mem_filter.mp ht
    have hs := (Finset.mem_filter.mp hdata.1).2
    simpa only [heq] using And.intro hs hdata.2
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.1⟩, hh.2⟩

noncomputable def fgkmtChosenResidue (Y : ℕ)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val) (p : ℕ) : ℕ :=
  if hp : p ∈ sieve then (a ⟨p, hp⟩ - (Y : ZMod p)).val
  else if hp : p ∈ sources then (b ⟨p, hp⟩).val else 0

theorem exists_cover_of_residue_choices (Y : ℕ)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val)
    (hsource : ∀ p ∈ sources, p.Prime) (hdisjoint : Disjoint sieve sources) :
    ∃ cover : Erdos4.PartialResidueCover
      (targets \ remainingPrimeTargets sieve sources targets Y a b),
      cover.primes = sieve ∪ sources := by
  refine ⟨⟨sieve ∪ sources, fgkmtChosenResidue sieve sources Y a b, ?_, ?_⟩, rfl⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Fact.out : ((⟨p, hp⟩ : sieve).val).Prime)
    · exact hsource p hp
  · intro q hq
    obtain ⟨hqt, hnot⟩ := Finset.mem_sdiff.mp hq
    by_cases hs : Survives (fun l : sieve => l.val) a {q + Y}
    · have hn : ¬∀ p : sources, (q : ZMod p.val) ≠ b p := by
        intro hh
        exact hnot ((mem_remainingPrimeTargets sieve sources targets Y q hqt a b).mpr ⟨hs, hh⟩)
      push Not at hn
      obtain ⟨p, hp⟩ := hn
      have hpnot : p.val ∉ sieve := fun hh => Finset.disjoint_left.mp hdisjoint hh p.property
      letI : Fact p.val.Prime := ⟨hsource p p.property⟩
      refine ⟨p, Finset.mem_union_right sieve p.property, ?_⟩
      simp only [fgkmtChosenResidue, dif_neg hpnot, dif_pos p.property]
      apply (ZMod.natCast_eq_natCast_iff q (b p).val p.val).mp
      simpa only [ZMod.natCast_zmod_val] using hp
    · have hn : ¬∀ l : sieve, a l ≠ ((q + Y : ℕ) : ZMod l.val) := by
        intro hh
        exact hs ((survives_singleton (fun l : sieve => l.val) a (q + Y)).mpr hh)
      push Not at hn
      obtain ⟨l, hl⟩ := hn
      refine ⟨l, Finset.mem_union_left sources l.property, ?_⟩
      simp only [fgkmtChosenResidue, dif_pos l.property]
      apply (ZMod.natCast_eq_natCast_iff q (a l - (Y : ZMod l.val)).val l.val).mp
      rw [ZMod.natCast_zmod_val, hl, Nat.cast_add]
      ring

theorem exists_cover_of_residue_choices_with_reserve (Y : ℕ)
    (a : ∀ l : sieve, ZMod l.val) (b : ∀ p : sources, ZMod p.val)
    (extra reserve : Finset ℕ)
    (hsource : ∀ p ∈ sources, p.Prime) (hreserve : ∀ p ∈ reserve, p.Prime)
    (hdisjoint : Disjoint sieve sources) (hfresh : Disjoint (sieve ∪ sources) reserve)
    (hcard : (remainingPrimeTargets sieve sources targets Y a b ∪ extra).card ≤ reserve.card) :
    ∃ cover : Erdos4.PartialResidueCover (targets ∪ extra),
      cover.primes = (sieve ∪ sources) ∪ reserve := by
  obtain ⟨left, hleft⟩ := exists_cover_of_residue_choices sieve sources targets Y a b hsource hdisjoint
  obtain ⟨right, hright⟩ := Erdos4.PartialResidueCover.exists_of_card_le hreserve hcard
  have hd : Disjoint left.primes right.primes := by simpa only [hleft, hright] using hfresh
  have hsub := remainingPrimeTargets_subset sieve sources targets Y a b
  have hset : (targets \ remainingPrimeTargets sieve sources targets Y a b) ∪
      (remainingPrimeTargets sieve sources targets Y a b ∪ extra) = targets ∪ extra := by
    rw [← Finset.union_assoc, Finset.sdiff_union_of_subset hsub]
  refine ⟨(left.union right hd).reindex hset, ?_⟩
  simp only [Erdos4.PartialResidueCover.reindex_primes, Erdos4.PartialResidueCover.union, hleft, hright]

end Erdos4.FGKMT
