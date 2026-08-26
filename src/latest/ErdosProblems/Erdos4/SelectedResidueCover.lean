import ErdosProblems.Erdos4.TwoStageSelection

/-!
# From selected tuples to an actual residue cover

Every selected tuple lies in the residue class of its center modulo its
source prime. The preliminary random residues cover every target that
failed their survival test. Fresh primes cover the remaining finite
exceptional set, giving an actual `PartialResidueCover` with explicit
prime support.
-/

open scoped BigOperators

namespace Erdos4.SelectedResidueCover

open AffineTuples TwoStageSelection

variable {k : ℕ} (sieve : Finset ℕ) [∀ l : sieve, Fact (l : ℕ).Prime]

noncomputable def chosenResidue (sources : Finset ℕ) (Y : ℕ)
    (a : ∀ l : sieve, ZMod (l : ℕ)) (choice : sources → ↥(Finset.Icc 1 Y)) (p : ℕ) : ℕ :=
  if hp : p ∈ sieve then (a ⟨p, hp⟩).val else
    if hp : p ∈ sources then (choice ⟨p, hp⟩ : ℕ) else 0

theorem chosenResidue_at_sieve (sources : Finset ℕ) (Y : ℕ)
    (a : ∀ l : sieve, ZMod (l : ℕ)) (choice : sources → ↥(Finset.Icc 1 Y)) (l : sieve) :
    chosenResidue sieve sources Y a choice l = (a l).val := by
  simp [chosenResidue, l.property]

theorem chosenResidue_at_source (sources : Finset ℕ) (Y : ℕ)
    (a : ∀ l : sieve, ZMod (l : ℕ)) (choice : sources → ↥(Finset.Icc 1 Y)) (p : sources)
    (hp : (p : ℕ) ∉ sieve) : chosenResidue sieve sources Y a choice p = (choice p : ℕ) := by
  simp [chosenResidue, hp, p.property]

theorem exists_cover_of_choices (h : Fin k → ℕ) (sources targets : Finset ℕ) (Y : ℕ)
    (hprime : ∀ p ∈ sources, p.Prime) (hdisjoint : Disjoint sieve sources)
    (a : ∀ l : sieve, ZMod (l : ℕ)) (choice : sources → ↥(Finset.Icc 1 Y)) :
    ∃ cover : Erdos4.PartialResidueCover
      (targets \ uncovered (fun l : sieve => (l : ℕ)) h sources targets Y (a, choice)),
        cover.primes = sieve ∪ sources := by
  classical
  refine ⟨⟨sieve ∪ sources, chosenResidue sieve sources Y a choice, ?_, ?_⟩, rfl⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Fact.out : ((⟨p, hp⟩ : sieve) : ℕ).Prime)
    · exact hprime p hp
  · intro q hq
    have hqt := (Finset.mem_sdiff.mp hq).1
    have hnot := (Finset.mem_sdiff.mp hq).2
    by_cases hs : RandomResidueSieve.Survives (fun l : sieve => (l : ℕ)) a {q}
    · have hex : ∃ p : sources, q ∈ tuple h p (choice p) := by
        by_contra hn
        push Not at hn
        exact hnot (Finset.mem_filter.mpr ⟨hqt, hs, hn⟩)
      obtain ⟨p, hp⟩ := hex
      have hpnot : (p : ℕ) ∉ sieve := fun hps => Finset.disjoint_left.mp hdisjoint hps p.property
      refine ⟨p, Finset.mem_union_right sieve p.property, ?_⟩
      rw [chosenResidue_at_source sieve sources Y a choice p hpnot]
      obtain ⟨i, hi⟩ := (mem_tuple h p (choice p) q).mp hp
      rw [← hi]
      simp [Nat.ModEq, Nat.add_mod]
    · have hn : ¬∀ l : sieve, a l ≠ (q : ZMod (l : ℕ)) := by
        intro ha
        exact hs ((RandomResidueSieve.survives_singleton (fun l : sieve => (l : ℕ)) a q).mpr ha)
      push Not at hn
      obtain ⟨l, hl⟩ := hn
      refine ⟨l, Finset.mem_union_left sources l.property, ?_⟩
      rw [chosenResidue_at_sieve sieve sources Y a choice l]
      apply (ZMod.natCast_eq_natCast_iff q (a l).val (l : ℕ)).mp
      simpa only [ZMod.natCast_zmod_val] using hl.symm

/-- Finite two-stage covering with a disjoint fresh-prime reserve. All
residues are constructed; the only numerical premise is the explicit
expected-uncovered budget. -/
theorem exists_cover_with_reserve (h : Fin k → ℕ) (sources targets reserve : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hprime : ∀ p ∈ sources, p.Prime) (hreserve : ∀ p ∈ reserve, p.Prime)
    (hdisjoint : Disjoint sieve sources) (hfresh : Disjoint (sieve ∪ sources) reserve)
    (hbudget : UnitFourier.unitDensity (fun l : sieve => (l : ℕ)) *
      (∑ q ∈ targets, ConditionalTupleMoments.mean (fun l : sieve => (l : ℕ)) q
        (ConditionalCovering.miss (fun l : sieve => (l : ℕ)) h sources Y μ q)) < reserve.card + 1) :
    ∃ cover : Erdos4.PartialResidueCover targets, cover.primes = (sieve ∪ sources) ∪ reserve := by
  classical
  obtain ⟨a, choice, hcount⟩ := exists_choices (fun l : sieve => (l : ℕ)) h sources targets Y μ hY hμ
  let missed := uncovered (fun l : sieve => (l : ℕ)) h sources targets Y (a, choice)
  have hcard : missed.card ≤ reserve.card := by
    have hh : (missed.card : ℝ) < (reserve.card : ℝ) + 1 := hcount.trans_lt hbudget
    have hn : missed.card < reserve.card + 1 := by exact_mod_cast hh
    omega
  obtain ⟨left, hleft⟩ := exists_cover_of_choices sieve h sources targets Y hprime hdisjoint a choice
  obtain ⟨right, hright⟩ := Erdos4.PartialResidueCover.exists_of_card_le hreserve hcard
  have hd : Disjoint left.primes right.primes := by simpa only [hleft, hright] using hfresh
  have hsub : missed ⊆ targets := Finset.filter_subset _ _
  have hset : (targets \ missed) ∪ missed = targets := Finset.sdiff_union_of_subset hsub
  refine ⟨(left.union right hd).reindex hset, ?_⟩
  simp only [Erdos4.PartialResidueCover.reindex_primes, Erdos4.PartialResidueCover.union, hleft, hright]

end Erdos4.SelectedResidueCover
