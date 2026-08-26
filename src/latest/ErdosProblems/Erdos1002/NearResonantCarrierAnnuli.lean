import ErdosProblems.Erdos1002.NearResonantCarrierPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Signed carrier annuli for the near-resonant square function

For a dyadic denominator block `P < 2p`, `p ≤ P`, the carrier
`ell * N * p` lies in the core of a signed annulus whose radial range is
`[|ell|NP/4, 2|ell|NP]`.  This file proves both facts needed by the
Fourier leakage argument:

* the carrier is separated from the complement by `|ell|NP/4`;
* annuli with radii `P = 2^s` overlap at most fourfold.

All endpoints and signs are part of the definitions below.
-/

open Set Finset

namespace Erdos1002

noncomputable section

/-- Real orientation of a nonzero integer carrier. -/
def nearCarrierOrientation (ell : ℤ) : ℝ :=
  if 0 < ell then 1 else -1

theorem abs_nearCarrierOrientation (ell : ℤ) :
    |nearCarrierOrientation ell| = 1 := by
  unfold nearCarrierOrientation
  split <;> simp

theorem nearCarrierOrientation_mul_cast
    {ell : ℤ} (hell : ell ≠ 0) :
    nearCarrierOrientation ell * (ell : ℝ) = |(ell : ℝ)| := by
  unfold nearCarrierOrientation
  split_ifs with hpos
  · rw [one_mul, abs_of_pos (by exact_mod_cast hpos)]
  · have hneg : ell < 0 := lt_of_le_of_ne (not_lt.mp hpos) hell
    rw [neg_one_mul, abs_of_neg (by exact_mod_cast hneg)]

/-- Radial scale `|ell| N P` of one carrier annulus. -/
def nearCarrierScale (N : ℕ) (ell : ℤ) (P : ℕ) : ℝ :=
  |(ell : ℝ)| * (N : ℝ) * (P : ℝ)

theorem nearCarrierScale_pos
    {N P : ℕ} {ell : ℤ} (hN : 0 < N) (hP : 0 < P) (hell : ell ≠ 0) :
    0 < nearCarrierScale N ell P := by
  unfold nearCarrierScale
  positivity

/-- Signed annulus `[|ell|NP/4, 2|ell|NP]` in integer frequency space. -/
def nearCarrierAnnulus (N : ℕ) (ell : ℤ) (P : ℕ) : Set ℤ :=
  {n | nearCarrierScale N ell P / 4 ≤
      nearCarrierOrientation ell * (n : ℝ) ∧
    nearCarrierOrientation ell * (n : ℝ) ≤
      2 * nearCarrierScale N ell P}

/-- A carrier belonging to the half-open denominator block is separated
from the complement of its annulus by one quarter of the annular scale. -/
theorem nearCarrier_annulus_separation
    {N p P : ℕ} {ell : ℤ}
    (hN : 0 < N) (hP : 0 < P) (hell : ell ≠ 0)
    (hpLower : P < 2 * p) (hpUpper : p ≤ P) (k : ℤ)
    (hleak : nearBernoulliCarrierFrequency N p ell + k ∉
      nearCarrierAnnulus N ell P) :
    nearCarrierScale N ell P / 4 ≤ |(k : ℝ)| := by
  let sigma := nearCarrierOrientation ell
  let S := nearCarrierScale N ell P
  let m := nearBernoulliCarrierFrequency N p ell
  have hsigma : |sigma| = 1 := abs_nearCarrierOrientation ell
  have hS : 0 < S := nearCarrierScale_pos hN hP hell
  have hm : sigma * (m : ℝ) = |(ell : ℝ)| * (N : ℝ) * (p : ℝ) := by
    dsimp [sigma, m, nearBernoulliCarrierFrequency]
    push_cast
    calc
      nearCarrierOrientation ell * (ell * (N * p)) =
          (nearCarrierOrientation ell * ell) * (N * p) := by ring
      _ = |(ell : ℝ)| * ((N : ℝ) * (p : ℝ)) := by
        rw [nearCarrierOrientation_mul_cast hell]
      _ = |(ell : ℝ)| * (N : ℝ) * (p : ℝ) := by ring
  have hcoreLower : S / 2 < sigma * (m : ℝ) := by
    rw [hm]
    dsimp [S, nearCarrierScale]
    have hcast : (P : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hpLower
    have hc : 0 < |(ell : ℝ)| * (N : ℝ) := by positivity
    nlinarith
  have hcoreUpper : sigma * (m : ℝ) ≤ S := by
    rw [hm]
    dsimp [S, nearCarrierScale]
    have hcast : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hpUpper
    exact mul_le_mul_of_nonneg_left hcast (by positivity)
  have hout :
      sigma * ((m + k : ℤ) : ℝ) < S / 4 ∨
        2 * S < sigma * ((m + k : ℤ) : ℝ) := by
    change ¬ (S / 4 ≤ sigma * ((m + k : ℤ) : ℝ) ∧
      sigma * ((m + k : ℤ) : ℝ) ≤ 2 * S) at hleak
    by_cases hleft : S / 4 ≤ sigma * ((m + k : ℤ) : ℝ)
    · exact Or.inr (lt_of_not_ge fun hright ↦ hleak ⟨hleft, hright⟩)
    · exact Or.inl (lt_of_not_ge hleft)
  have hkdiff :
      sigma * (k : ℝ) =
        sigma * ((m + k : ℤ) : ℝ) - sigma * (m : ℝ) := by
    push_cast
    ring
  have hquarter : S / 4 ≤ |sigma * (k : ℝ)| := by
    rcases hout with hlow | hhigh
    · have hneg : S / 4 ≤ -(sigma * (k : ℝ)) := by
        rw [hkdiff]
        linarith
      exact hneg.trans (neg_le_abs _)
    · have hpos : S / 4 ≤ sigma * (k : ℝ) := by
        rw [hkdiff]
        nlinarith
      exact hpos.trans (le_abs_self _)
  rw [abs_mul, hsigma, one_mul] at hquarter
  exact hquarter

/-- If two power-of-two carrier annuli contain the same frequency, their
dyadic exponents differ by at most three. -/
theorem nearCarrierAnnulus_pow_two_indices_close
    {N : ℕ} {ell : ℤ} (hN : 0 < N) (hell : ell ≠ 0)
    {s t : ℕ} {n : ℤ}
    (hs : n ∈ nearCarrierAnnulus N ell (2 ^ s))
    (ht : n ∈ nearCarrierAnnulus N ell (2 ^ t)) :
    t ≤ s + 3 := by
  have hscale :
      nearCarrierScale N ell (2 ^ t) ≤
        8 * nearCarrierScale N ell (2 ^ s) := by
    have hlower := ht.1
    have hupper := hs.2
    linarith
  have hc : 0 < |(ell : ℝ)| * (N : ℝ) := by positivity
  have hpowsReal : ((2 ^ t : ℕ) : ℝ) ≤ 8 * ((2 ^ s : ℕ) : ℝ) := by
    dsimp [nearCarrierScale] at hscale
    nlinarith
  have hpowsNat : 2 ^ t ≤ 8 * 2 ^ s := by exact_mod_cast hpowsReal
  have hpows : 2 ^ t ≤ 2 ^ (s + 3) := by
    simpa [pow_add, mul_comm] using! hpowsNat
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpows

/-- Power-of-two carrier annuli have overlap multiplicity at most four,
uniformly in the carrier mode, main parameter, cutoff, and frequency. -/
theorem frequencyOverlapCount_nearCarrierAnnulus_pow_two_le_four
    (N : ℕ) (ell : ℤ) (M : ℕ)
    (hN : 0 < N) (hell : ell ≠ 0) (n : ℤ) :
    frequencyOverlapCount (Finset.range M)
      (fun s ↦ nearCarrierAnnulus N ell (2 ^ s)) n ≤ 4 := by
  classical
  let u := (Finset.range M).filter
    (fun s ↦ n ∈ nearCarrierAnnulus N ell (2 ^ s))
  change u.card ≤ 4
  by_cases hu : u.Nonempty
  · let r := u.min' hu
    have hrmem : r ∈ u := Finset.min'_mem u hu
    have hsubset : u ⊆ Finset.Icc r (r + 3) := by
      intro s hs
      have hrs : r ≤ s := Finset.min'_le u s hs
      have hsann : n ∈ nearCarrierAnnulus N ell (2 ^ s) :=
        (Finset.mem_filter.mp hs).2
      have hrann : n ∈ nearCarrierAnnulus N ell (2 ^ r) :=
        (Finset.mem_filter.mp hrmem).2
      have hsr : s ≤ r + 3 :=
        nearCarrierAnnulus_pow_two_indices_close hN hell hrann hsann
      exact Finset.mem_Icc.mpr ⟨hrs, hsr⟩
    calc
      u.card ≤ (Finset.Icc r (r + 3)).card := Finset.card_le_card hsubset
      _ = 4 := by rw [Nat.card_Icc]; omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hu]
    simp

end

end Erdos1002
