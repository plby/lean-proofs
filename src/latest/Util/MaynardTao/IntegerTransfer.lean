/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.Basic
import Util.MaynardTao.Natural

/-!
# Translating integer shift tuples to natural shift tuples

The sieve infrastructure is stated for natural shifts.  Subtracting a common
lower bound from an integer tuple preserves its cardinality, admissibility,
and prime-shift counts after translating the base point back.
-/

namespace MaynardTao

open Nat Finset

/-- Subtract a common integer lower bound and view the resulting
nonnegative shifts as naturals. -/
def integerTupleToNat (B : Finset ℤ) (a : ℤ) : Finset ℕ :=
  B.image fun b => (b - a).toNat

theorem translated_toNat_mod
    {b a : ℤ} {p : ℕ} (hp : p.Prime) (hba : a ≤ b) :
    (b - a).toNat % p =
      (((b % (p : ℤ)) - a) % (p : ℤ)).toNat := by
  have hnonneg : 0 ≤ ((b % (p : ℤ)) - a) % (p : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg hnonneg,
    Int.toNat_of_nonneg (sub_nonneg.mpr hba)]
  simp only [Int.sub_emod, Int.emod_emod]

theorem integerTupleToNat_card
    (B : Finset ℤ) (a : ℤ) (ha : ∀ b ∈ B, a ≤ b) :
    (integerTupleToNat B a).card = B.card := by
  unfold integerTupleToNat
  apply Finset.card_image_iff.mpr
  intro b hb c hc h
  have hb0 : 0 ≤ b - a := sub_nonneg.mpr (ha b hb)
  have hc0 : 0 ≤ c - a := sub_nonneg.mpr (ha c hc)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
  rw [Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg hc0] at hcast
  omega

theorem integerTupleToNat_admissible
    (B : Finset ℤ) (a : ℤ) (ha : ∀ b ∈ B, a ≤ b)
    (hB : Admissible B) :
    BoundedGaps.IsAdmissible (integerTupleToNat B a) := by
  intro p hp
  let R : Finset ℤ := B.image (fun b => b % (p : ℤ))
  let f : ℤ → ℕ := fun r => ((r - a) % (p : ℤ)).toNat
  have hsub :
      (integerTupleToNat B a).image (fun h => h % p) ⊆ R.image f := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    apply Finset.mem_image.mpr
    refine ⟨b % (p : ℤ), Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    exact (translated_toNat_mod hp (ha b hb)).symm
  calc
    ((integerTupleToNat B a).image (fun h => h % p)).card ≤
        (R.image f).card := Finset.card_le_card hsub
    _ ≤ R.card := Finset.card_image_le
    _ < p := hB p hp

theorem translated_prime_iff
    {a b : ℤ} (hba : a ≤ b) (q : ℕ) :
    (((q : ℤ) - a + b).natAbs).Prime ↔
      (q + (b - a).toNat).Prime := by
  have hba0 : 0 ≤ b - a := sub_nonneg.mpr hba
  have hsum : (((q + (b - a).toNat : ℕ) : ℤ)) =
      (q : ℤ) - a + b := by
    rw [Nat.cast_add, Int.toNat_of_nonneg hba0]
    ring
  have hz : 0 ≤ (q : ℤ) - a + b := by
    rw [← hsum]
    positivity
  have habs : ((q : ℤ) - a + b).natAbs =
      q + (b - a).toNat := by
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hz]
    exact hsum.symm
  rw [habs]

theorem translated_prime_filter_card
    (B : Finset ℤ) (a : ℤ) (ha : ∀ b ∈ B, a ≤ b) (q : ℕ) :
    ((integerTupleToNat B a).filter fun h => (q + h).Prime).card =
      (B.filter fun b => (((q : ℤ) - a + b).natAbs).Prime).card := by
  symm
  apply Finset.card_bij (fun b _ => (b - a).toNat)
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩, ?_⟩
    exact (translated_prime_iff (ha b hb.1) q).mp hb.2
  · intro b hb c hc h
    have hb0 : 0 ≤ b - a :=
      sub_nonneg.mpr (ha b (Finset.mem_filter.mp hb).1)
    have hc0 : 0 ≤ c - a :=
      sub_nonneg.mpr (ha c (Finset.mem_filter.mp hc).1)
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    rw [Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg hc0] at hcast
    omega
  · intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh.1
    refine ⟨b, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨hb, (translated_prime_iff (ha b hb) q).mpr hh.2⟩

/-- Any natural-shift infinitude statement for the translated tuple gives
the exact integer-shift statement for the original tuple. -/
theorem integerPrimeShifts_of_naturalPrimeShifts
    {m : ℕ} (B : Finset ℤ) (a : ℤ)
    (ha : ∀ b ∈ B, a ≤ b)
    (hnat : ∀ T : ℕ, ∃ q : ℕ, T < q ∧
      m ≤ BoundedGaps.primeShiftCount (integerTupleToNat B a) q) :
    ∀ N : ℕ, ∃ n : ℤ, N < n ∧
      m ≤ (B.filter (fun b => (n + b).natAbs.Prime)).card := by
  intro N
  obtain ⟨q, hq, hcount⟩ := hnat (N + a.natAbs + 1)
  refine ⟨(q : ℤ) - a, ?_, ?_⟩
  · have hqZ : ((N + a.natAbs + 1 : ℕ) : ℤ) < q := by
      exact_mod_cast hq
    have haAbs : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
    omega
  · unfold BoundedGaps.primeShiftCount at hcount
    rw [translated_prime_filter_card B a ha q] at hcount
    simpa [sub_add_eq_add_sub] using hcount

end MaynardTao
