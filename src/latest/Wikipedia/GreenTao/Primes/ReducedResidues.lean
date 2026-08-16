import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Primorial

namespace Wikipedia.SzemeredisTheorem

open Finset

/-- The reduced residue system modulo `W`, represented by its standard
natural-number representatives in `[0, W)`. -/
def reducedResidues (W : ℕ) : Finset ℕ :=
  {b ∈ Finset.range W | W.Coprime b}

@[simp]
theorem mem_reducedResidues {W b : ℕ} :
    b ∈ reducedResidues W ↔ b < W ∧ W.Coprime b := by
  simp [reducedResidues]

/-- Euler's totient is exactly the number of standard reduced residues. -/
@[simp]
theorem card_reducedResidues (W : ℕ) :
    #(reducedResidues W) = W.totient :=
  rfl

/-- A positive modulus has at least one reduced residue. -/
theorem reducedResidues_nonempty {W : ℕ} (hW : 0 < W) :
    (reducedResidues W).Nonempty := by
  rw [← Finset.card_pos, card_reducedResidues, Nat.totient_pos]
  exact hW

/-- The elements of `S` lying in the standard residue class `b` modulo
`W`. -/
def residueFiber (S : Finset ℕ) (W b : ℕ) : Finset ℕ :=
  {n ∈ S | n % W = b}

@[simp]
theorem mem_residueFiber {S : Finset ℕ} {W b n : ℕ} :
    n ∈ residueFiber S W b ↔ n ∈ S ∧ n % W = b := by
  simp [residueFiber]

/-- For a standard representative, membership in a residue fiber is
equivalently membership in the corresponding congruence class. -/
theorem mem_residueFiber_iff_modEq {S : Finset ℕ} {W b n : ℕ}
    (hb : b < W) :
    n ∈ residueFiber S W b ↔ n ∈ S ∧ n ≡ b [MOD W] := by
  simp [residueFiber, Nat.ModEq, Nat.mod_eq_of_lt hb]

/-- Reduction modulo a positive modulus sends every number coprime to the
modulus into the reduced residue system. -/
theorem mod_mem_reducedResidues {W n : ℕ} (hW : 0 < W)
    (hn : n.Coprime W) :
    n % W ∈ reducedResidues W := by
  rw [mem_reducedResidues]
  refine ⟨Nat.mod_lt n hW, ?_⟩
  exact ((ZMod.coprime_mod_iff_coprime n W).2 hn).symm

/-- Finite pigeonhole principle for the `W`-trick, in a division-free
form.  If every element of `S` is coprime to `W`, one reduced residue
class contains enough of `S` that multiplying its size by `φ(W)` covers
all of `S`. -/
theorem exists_reducedResidue_card_le_totient_mul_card_fiber
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hcop : ∀ n ∈ S, n.Coprime W) :
    ∃ b ∈ reducedResidues W,
      #S ≤ W.totient * #(residueFiber S W b) := by
  let q := #S / W.totient
  have hmap : ∀ n ∈ S, n % W ∈ reducedResidues W :=
    fun n hn ↦ mod_mem_reducedResidues hW (hcop n hn)
  have hnonempty : (reducedResidues W).Nonempty :=
    reducedResidues_nonempty hW
  have hbase : #(reducedResidues W) * q ≤ #S := by
    rw [card_reducedResidues]
    exact Nat.mul_div_le _ _
  by_cases heq : #(reducedResidues W) * q = #S
  · obtain ⟨b, hb, hfiber⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := S) (t := reducedResidues W) (f := fun n ↦ n % W)
        hmap hnonempty hbase
    refine ⟨b, hb, ?_⟩
    calc
      #S = #(reducedResidues W) * q := heq.symm
      _ ≤ #(reducedResidues W) * #(residueFiber S W b) := by
        apply Nat.mul_le_mul_left
        simpa [residueFiber] using hfiber
      _ = W.totient * #(residueFiber S W b) := by
        rw [card_reducedResidues]
  · have hstrict : #(reducedResidues W) * q < #S :=
      lt_of_le_of_ne hbase heq
    obtain ⟨b, hb, hfiber⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := S) (t := reducedResidues W) (f := fun n ↦ n % W)
        hmap hstrict
    refine ⟨b, hb, ?_⟩
    have hceil :
        #S < #(reducedResidues W) * (q + 1) := by
      simpa [q, card_reducedResidues] using
        Nat.lt_mul_div_succ #S (Nat.totient_pos.mpr hW)
    calc
      #S ≤ #(reducedResidues W) * (q + 1) := hceil.le
      _ ≤ #(reducedResidues W) * #(residueFiber S W b) := by
        apply Nat.mul_le_mul_left
        exact Nat.succ_le_iff.mpr (by simpa [residueFiber] using hfiber)
      _ = W.totient * #(residueFiber S W b) := by
        rw [card_reducedResidues]

/-- The usual floor-of-the-average consequence of the multiplication
inequality. -/
theorem exists_reducedResidue_div_totient_le_card_fiber
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hcop : ∀ n ∈ S, n.Coprime W) :
    ∃ b ∈ reducedResidues W,
      #S / W.totient ≤ #(residueFiber S W b) := by
  obtain ⟨b, hb, hcard⟩ :=
    exists_reducedResidue_card_le_totient_mul_card_fiber hW S hcop
  exact ⟨b, hb, Nat.div_le_of_le_mul hcard⟩

/-- A prime larger than `w` shares no prime factor with the product of
all primes at most `w`. -/
theorem prime_coprime_primorial_of_lt {p w : ℕ} (hp : p.Prime)
    (hw : w < p) :
    p.Coprime (primorial w) := by
  apply hp.coprime_iff_not_dvd.mpr
  rw [hp.dvd_primorial_iff]
  exact not_le.mpr hw

/-- Consequently, a prime larger than `w` reduces to a reduced residue
modulo the primorial of `w`. -/
theorem prime_mod_primorial_mem_reducedResidues {p w : ℕ}
    (hp : p.Prime) (hw : w < p) :
    p % primorial w ∈ reducedResidues (primorial w) :=
  mod_mem_reducedResidues (primorial_pos w)
    (prime_coprime_primorial_of_lt hp hw)

/-- Pigeonhole specialization used in the prime `W`-trick: among any
finite collection of primes larger than `w`, one reduced residue modulo
`primorial w` captures the required proportion. -/
theorem exists_reducedResidue_for_primes_above
    {w : ℕ} (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (habove : ∀ p ∈ S, w < p) :
    ∃ b ∈ reducedResidues (primorial w),
      #S ≤ (primorial w).totient *
        #(residueFiber S (primorial w) b) :=
  exists_reducedResidue_card_le_totient_mul_card_fiber
    (primorial_pos w) S fun p hp ↦
      prime_coprime_primorial_of_lt (hprime p hp) (habove p hp)

end Wikipedia.SzemeredisTheorem
