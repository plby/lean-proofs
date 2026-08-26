import ErdosProblems.Erdos4.OuterPrimeSupply

/-!
# Complete interval covering from the numerical survivor budget

The fresh-prime reserve pays for both the uncovered prime targets and
the entire smooth exceptional set. Adding the zero-residue initial
sieve yields a genuine cover of every offset, with modulus bounded by
the primorial of the outer frontier.
-/

open scoped BigOperators

namespace Erdos4.CompleteCover

open AffineTuples ConditionalTupleMoments TwoStageSelection SelectedResidueCover
open SmoothParameters ChebyshevIntervals OuterRay OuterPrimeSupply ZeroSieveResidual

variable {k : ℕ}

theorem exists_cover_with_extra (sieve : Finset ℕ) [∀ l : sieve, Fact (l : ℕ).Prime]
    (h : Fin k → ℕ) (sources targets extra reserve : Finset ℕ) (Y : ℕ)
    (μ : ℕ → ℕ → ℝ) (hY : 1 ≤ Y)
    (hμ : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ p n)
    (hprime : ∀ p ∈ sources, p.Prime) (hreserve : ∀ p ∈ reserve, p.Prime)
    (hdisjoint : Disjoint sieve sources) (hfresh : Disjoint (sieve ∪ sources) reserve)
    (hbudget : UnitFourier.unitDensity (fun l : sieve => (l : ℕ)) *
      (∑ q ∈ targets, mean (fun l : sieve => (l : ℕ)) q
        (ConditionalCovering.miss (fun l : sieve => (l : ℕ)) h sources Y μ q)) + extra.card < reserve.card + 1) :
    ∃ cover : Erdos4.PartialResidueCover (targets ∪ extra),
      cover.primes = (sieve ∪ sources) ∪ reserve := by
  classical
  obtain ⟨a, choice, hcount⟩ := exists_choices (fun l : sieve => (l : ℕ)) h sources targets Y μ hY hμ
  let missed := uncovered (fun l : sieve => (l : ℕ)) h sources targets Y (a, choice)
  have hcard : (missed ∪ extra).card ≤ reserve.card := by
    have hsum : ((missed ∪ extra).card : ℝ) ≤ (missed.card : ℝ) + extra.card := by
      exact_mod_cast Finset.card_union_le missed extra
    have hh := hsum.trans (add_le_add hcount le_rfl) |>.trans_lt hbudget
    have hn : (missed ∪ extra).card < reserve.card + 1 := by exact_mod_cast hh
    omega
  obtain ⟨left, hleft⟩ := exists_cover_of_choices sieve h sources targets Y hprime hdisjoint a choice
  obtain ⟨right, hright⟩ := Erdos4.PartialResidueCover.exists_of_card_le hreserve hcard
  have hd : Disjoint left.primes right.primes := by simpa only [hleft, hright] using hfresh
  have hsub : missed ⊆ targets := Finset.filter_subset _ _
  have hset : (targets \ missed) ∪ (missed ∪ extra) = targets ∪ extra := by
    rw [← Finset.union_assoc, Finset.sdiff_union_of_subset hsub]
  refine ⟨(left.union right hd).reindex hset, ?_⟩
  simp only [Erdos4.PartialResidueCover.reindex_primes, Erdos4.PartialResidueCover.union, hleft, hright]

theorem zero_random_disjoint (w z x : ℕ) : Disjoint (zeroPrimes w z x) (primeInterval w z) := by
  apply Finset.disjoint_left.mpr
  intro p hp hrandom
  have hr := mem_primeInterval.mp hrandom
  rcases Finset.mem_union.mp hp with hp | hp
  · have hh := (Nat.mem_primesLE.mp hp).1
    omega
  · have hh := (mem_primeInterval.mp hp).2.1
    omega

theorem zero_bounded {w z x : ℕ} (hwx : w ≤ x) : ∀ p ∈ zeroPrimes w z x, p ≤ x := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact (Nat.mem_primesLE.mp hp).1.trans hwx
  · exact (mem_primeInterval.mp hp).2.2

/-- A full interval cover with a controlled CRT modulus, once the
explicit expected-uncovered-plus-smooth budget is satisfied. -/
theorem exists_ray_cover_of_budget (a D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hwz : smallCutoff a r ≤ smoothFrontier r)
    (hzero : length a D r ≤ smallCutoff a r * base a r)
    (h : Fin k → ℕ) (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ p ∈ sourcePrimes a r, ∀ n ∈ Finset.Icc 1 (length a D r), 0 ≤ μ p n)
    (hbudget : UnitFourier.unitDensity (fun l : randomPrimes a r => (l : ℕ)) *
      (∑ q ∈ primeInterval (base a r) (length a D r),
        mean (fun l : randomPrimes a r => (l : ℕ)) q
          (ConditionalCovering.miss (fun l : randomPrimes a r => (l : ℕ)) h
            (sourcePrimes a r) (length a D r) μ q)) +
        (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card <
          (reservePrimes a r).card + 1) :
    ∃ cover : Erdos4.ResidueCover (length a D r), cover.modulus ≤ primorial (frontier a r) := by
  classical
  have hY : 1 ≤ length a D r :=
    (frontier_pos a r).trans_le (frontier_le_length a hD hr)
  have hprime : ∀ p ∈ sourcePrimes a r, p.Prime := fun p hp => (source_range a r hp).1
  have hreserve : ∀ p ∈ reservePrimes a r, p.Prime := fun p hp => (reserve_range a r hp).1
  have hfresh : Disjoint (randomPrimes a r ∪ sourcePrimes a r) (reservePrimes a r) :=
    Finset.disjoint_union_left.mpr ⟨random_reserve_disjoint a r, source_reserve_disjoint a r⟩
  obtain ⟨other, hother⟩ := exists_cover_with_extra (randomPrimes a r) h (sourcePrimes a r)
    (primeInterval (base a r) (length a D r))
    (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)) (reservePrimes a r)
    (length a D r) μ hY hμ hprime hreserve (random_source_disjoint a r) hfresh hbudget
  let S := survivors (length a D r) (smallCutoff a r) (smoothFrontier r) (base a r)
  have hS : S ⊆ primeInterval (base a r) (length a D r) ∪
      Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1) := by
    simpa only [S, Finset.union_comm] using
      survivors_subset (z := smoothFrontier r) (base_pos a r) hzero
  let rest : Erdos4.PartialResidueCover S :=
    ⟨other.primes, other.residue, other.prime, fun n hn => other.covers n (hS hn)⟩
  obtain ⟨initial, hinitial⟩ := exists_zero_cover (length a D r) (smallCutoff a r)
    (smoothFrontier r) (base a r)
  have hwbase : smallCutoff a r ≤ base a r := hwz.trans (smooth_le_base a r)
  have hd : Disjoint initial.primes rest.primes := by
    change Disjoint initial.primes other.primes
    rw [hinitial, hother]
    apply Finset.disjoint_union_right.mpr
    constructor
    · apply Finset.disjoint_union_right.mpr
      constructor
      · exact zero_random_disjoint _ _ _
      · apply Finset.disjoint_left.mpr
        intro p hp hs
        have hb := zero_bounded hwbase p hp
        have hh := (source_range a r hs).2.1
        omega
    · apply Finset.disjoint_left.mpr
      intro p hp hs
      have hb := zero_bounded hwbase p hp
      have hh := (reserve_range a r hs).2.1
      omega
  have hsub : S ⊆ Finset.Icc 1 (length a D r) := Finset.filter_subset _ _
  let combined := (initial.union rest hd).reindex (Finset.sdiff_union_of_subset hsub)
  let cover := combined.toResidueCover
  have hsupport : cover.primes = zeroPrimes (smallCutoff a r) (smoothFrontier r) (base a r) ∪
      ((randomPrimes a r ∪ sourcePrimes a r) ∪ reservePrimes a r) := by
    change initial.primes ∪ other.primes = _
    rw [hinitial, hother]
  have hbound : cover.primes ⊆ (frontier a r).primesLE := by
    intro p hp
    have hpprime := cover.prime p hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, hpprime⟩
    rw [hsupport] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (zero_bounded hwbase p hp).trans (base_le_frontier a r)
    · rcases Finset.mem_union.mp hp with hp | hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact ((mem_primeInterval.mp hp).2.2.trans (smooth_le_base a r)).trans (base_le_frontier a r)
        · exact (source_range a r hp).2.2
      · have hh := (reserve_range a r hp).2.2
        change p ≤ 256 * base a r
        omega
  exact ⟨cover, Erdos4.primeProduct_le_primorial hbound⟩

end Erdos4.CompleteCover
