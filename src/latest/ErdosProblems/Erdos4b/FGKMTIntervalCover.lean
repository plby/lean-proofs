/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTInitialResidueSieve

/-! # Complete finite interval covers from an initial sieve and fresh primes -/

namespace Erdos4b.FGKMT

noncomputable section

theorem integerResidueIndex_modEq {p : ℕ} (hp : 0 < p) (n : ℤ) :
    (integerResidueIndex p n : ℤ) ≡ n [ZMOD (p : ℤ)] := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  change ((n % (p : ℤ)).toNat : ℤ) % (p : ℤ) = n % (p : ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg n hpZ), Int.emod_emod]

def initialSievePartialCover (x Y : ℕ) (r : ℕ → ℕ) :
    PartialResidueCover (Finset.Ioc x Y \ initialResidueSurvivors x Y r) where
  primes := Nat.primesLE x
  residue := r
  prime p hp := (Nat.mem_primesLE.mp hp).2
  covers n hn := by
    classical
    obtain ⟨hnI, hnE⟩ := Finset.mem_sdiff.mp hn
    by_contra h
    push Not at h
    apply hnE
    exact (mem_initialResidueSurvivors x Y r n).mpr
      ⟨(Finset.mem_Ioc.mp hnI).1, (Finset.mem_Ioc.mp hnI).2, h⟩

def translatedIntervalCover {x Y : ℕ} (cover : PartialResidueCover (Finset.Ioc x Y)) :
    ResidueCover (Y - x) where
  primes := cover.primes
  residue p := integerResidueIndex p ((cover.residue p : ℤ) - (x : ℤ))
  prime := cover.prime
  covers i hi hiy := by
    have hmem : x + i ∈ Finset.Ioc x Y := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
    obtain ⟨p, hp, hmod⟩ := cover.covers (x + i) hmem
    refine ⟨p, hp, Int.natCast_modEq_iff.mp ?_⟩
    have hmodZ : ((x + i : ℕ) : ℤ) ≡ (cover.residue p : ℤ) [ZMOD (p : ℤ)] :=
      Int.natCast_modEq_iff.mpr hmod
    have hsub := hmodZ.sub (Int.ModEq.refl (x : ℤ))
    have hiZ : (i : ℤ) ≡ (cover.residue p : ℤ) - (x : ℤ) [ZMOD (p : ℤ)] := by
      simpa only [Nat.cast_add, add_sub_cancel_left] using hsub
    exact hiZ.trans (integerResidueIndex_modEq (cover.prime p hp).pos _).symm

theorem exists_interval_cover_of_survivors {x Y : ℕ} (r : ℕ → ℕ) {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hfresh : ∀ p ∈ P, x < p)
    (hcard : (initialResidueSurvivors x Y r).card ≤ P.card) :
    ∃ cover : ResidueCover (Y - x), cover.primes = Nat.primesLE x ∪ P := by
  obtain ⟨cleanup, hcleanup⟩ := PartialResidueCover.exists_of_card_le hprime hcard
  let initial := initialSievePartialCover x Y r
  have hd : Disjoint initial.primes cleanup.primes := by
    rw [hcleanup]
    apply Finset.disjoint_left.mpr
    intro p hp hP
    have hpx := (Nat.mem_primesLE.mp hp).1
    exact (not_lt_of_ge hpx) (hfresh p hP)
  let joined := initial.union cleanup hd
  have hsets : (Finset.Ioc x Y \ initialResidueSurvivors x Y r) ∪
      initialResidueSurvivors x Y r = Finset.Ioc x Y :=
    Finset.sdiff_union_of_subset (initialResidueSurvivors_subset x Y r)
  refine ⟨translatedIntervalCover (joined.reindex hsets), ?_⟩
  change Nat.primesLE x ∪ cleanup.primes = _
  rw [hcleanup]

end

end Erdos4b.FGKMT
