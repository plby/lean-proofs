import ErdosProblems.Erdos4.Base
import Mathlib.Data.Nat.Find

/-! The finite maxima in the manuscript: the longest prime-residue cover and the largest prime gap. -/

namespace Erdos4.Tilted

theorem residueCover_length_lt_modulus {y : ℕ} (cover : Erdos4.ResidueCover y) : y < cover.modulus := by
  classical
  let b : ℕ := Nat.chineseRemainderOfFinset cover.residue id cover.primes
    (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime
  have hb : b < cover.modulus := Nat.chineseRemainderOfFinset_lt_prod cover.residue id
    (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime
  by_contra h
  have hMy : cover.modulus ≤ y := le_of_not_gt h
  obtain ⟨p, hp, hcovered⟩ := cover.covers (b + 1) (by omega) (by omega)
  let instPrime : Fact p.Prime := ⟨cover.prime p hp⟩
  have hcrt : b ≡ cover.residue p [MOD p] :=
    (Nat.chineseRemainderOfFinset cover.residue id cover.primes
      (fun p hp => (cover.prime p hp).ne_zero) cover.pairwise_coprime).prop p hp
  have hbad : cover.residue p + 1 ≡ cover.residue p [MOD p] :=
    (hcrt.add_right 1).symm.trans hcovered
  have heq := (ZMod.natCast_eq_natCast_iff (cover.residue p + 1) (cover.residue p) p).mpr hbad
  have hzero : (1 : ZMod p) = 0 := add_left_cancel
    (show (cover.residue p : ZMod p) + 1 = (cover.residue p : ZMod p) + 0 by
      simpa only [Nat.cast_add, Nat.cast_one, add_zero] using heq)
  exact one_ne_zero hzero

def BoundedCover (z y : ℕ) : Prop :=
  ∃ cover : Erdos4.ResidueCover y, cover.primes ⊆ z.primesLE

theorem boundedCover_zero (z : ℕ) : BoundedCover z 0 := by
  refine ⟨⟨∅, fun _ => 0, ?_, ?_⟩, Finset.empty_subset _⟩
  · simp
  · intro i hi hiy
    omega

theorem boundedCover_lt_primorial {z y : ℕ} (h : BoundedCover z y) : y < primorial z := by
  obtain ⟨cover, hcover⟩ := h
  exact (residueCover_length_lt_modulus cover).trans_le (Erdos4.primeProduct_le_primorial hcover)

theorem boundedCover_iff_residues (z y : ℕ) : BoundedCover z y ↔
    ∃ a : ℕ → ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ y → ∃ p : ℕ,
      p.Prime ∧ p ≤ z ∧ i ≡ a p [MOD p] := by
  constructor
  · rintro ⟨cover, hcover⟩
    refine ⟨cover.residue, ?_⟩
    intro i hi hiy
    obtain ⟨p, hp, hmod⟩ := cover.covers i hi hiy
    exact ⟨p, cover.prime p hp, (Nat.mem_primesLE.mp (hcover hp)).1, hmod⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨z.primesLE, a, fun p hp => (Nat.mem_primesLE.mp hp).2, ?_⟩, Finset.Subset.refl _⟩
    intro i hi hiy
    obtain ⟨p, hp, hpz, hmod⟩ := ha i hi hiy
    exact ⟨p, Nat.mem_primesLE.mpr ⟨hpz, hp⟩, hmod⟩

theorem boundedCover_floor_iff {X : ℝ} (hX : 0 ≤ X) (y : ℕ) : BoundedCover ⌊X⌋₊ y ↔
    ∃ a : ℕ → ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ y → ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ X ∧ i ≡ a p [MOD p] := by
  rw [boundedCover_iff_residues]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro i hi hiy
    obtain ⟨p, hp, hpX, hmod⟩ := ha i hi hiy
    exact ⟨p, hp, (Nat.cast_le.mpr hpX).trans (Nat.floor_le hX), hmod⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro i hi hiy
    obtain ⟨p, hp, hpX, hmod⟩ := ha i hi hiy
    exact ⟨p, hp, Nat.le_floor hpX, hmod⟩

open Classical in
noncomputable def maximumCoverLength (X : ℝ) : ℕ :=
  Nat.findGreatest (BoundedCover ⌊X⌋₊) (primorial ⌊X⌋₊)

theorem maximumCoverLength_spec (X : ℝ) : BoundedCover ⌊X⌋₊ (maximumCoverLength X) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (boundedCover_zero ⌊X⌋₊)

theorem le_maximumCoverLength {X : ℝ} {y : ℕ} (h : BoundedCover ⌊X⌋₊ y) : y ≤ maximumCoverLength X := by
  classical
  exact Nat.le_findGreatest (boundedCover_lt_primorial h).le h

theorem maximumCoverLength_lt_primorial (X : ℝ) : maximumCoverLength X < primorial ⌊X⌋₊ :=
  boundedCover_lt_primorial (maximumCoverLength_spec X)

open Classical in
noncomputable def maximumPrimeGap (T : ℝ) : ℕ :=
  (Finset.range (⌊T⌋₊ + 1)).sup (fun n =>
    if (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ T then Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n else 0)

theorem prime_gap_le_maximum (T : ℝ) (n : ℕ) (hT : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ T) :
    (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ≤ (maximumPrimeGap T : ℝ) := by
  classical
  have hn : n + 1 ≤ Nat.nth Nat.Prime (n + 1) :=
    Nat.le_nth (fun hfinite => False.elim (Nat.infinite_setOfPred_prime hfinite))
  have hindex : n ∈ Finset.range (⌊T⌋₊ + 1) := by
    have hh := Nat.le_floor hT
    exact Finset.mem_range.mpr (by omega)
  have hh := Finset.le_sup (f := fun k =>
    if (Nat.nth Nat.Prime (k + 1) : ℝ) ≤ T then Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k else 0) hindex
  simp only [if_pos hT] at hh
  have hnat : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_monotone Nat.infinite_setOfPred_prime) (Nat.le_succ n)
  have hreal : ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ≤ maximumPrimeGap T :=
    Nat.cast_le.mpr hh
  simpa only [Nat.cast_sub hnat] using hreal

theorem maximumPrimeGap_le {T : ℝ} {B : ℕ}
    (hB : ∀ n, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ T →
      Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n ≤ B) : maximumPrimeGap T ≤ B := by
  classical
  apply Finset.sup_le
  intro n _
  split_ifs with hT
  · exact hB n hT
  · exact Nat.zero_le B

end Erdos4.Tilted
