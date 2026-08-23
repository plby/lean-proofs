import ErdosProblems.Erdos245.Counting

open Filter Set
open scoped Pointwise Topology BigOperators

namespace Erdos245Scratch

open Erdos899
open Erdos587
open Erdos587.GeneralizedAP

/-- Under an eventual sumset ratio strictly below three, a positive
density-zero set has doubling gaps arbitrarily far out in its increasing
enumeration. -/
lemma exists_doubling_gap_of_eventually_three
    {S : Set ℕ} (hS : S.Infinite) (hpos : S ⊆ Ici 1)
    (hden : Tendsto (fun N ↦ (countIn S N : ℝ) / N) atTop (nhds 0))
    (hsum : ∀ᶠ N in atTop,
      countIn (S + S) N < 3 * countIn S N) :
    ∀ s : ℕ, ∃ i ≥ s,
      2 * enumerate S i < enumerate S (i + 1) := by
  intro s
  by_contra hgap
  push_neg at hgap
  have hnogap : ∀ i ≥ s,
      enumerate S (i + 1) ≤ 2 * enumerate S i := by
    intro i hi
    exact hgap i hi
  let R := freimanRank 12
  let C := freimanSizeFactor 12
  let D := (R + 1).factorial * (3 ^ R * C) * enumerate S s
  have hdenseD : ∀ᶠ M in atTop,
      (D + 1) * countIn S M < M :=
    density_eventually_mul_lt (countIn S) hden (by omega)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hdenseD
  have hlarge : ∀ᶠ N in atTop,
      countIn S L + s + 2 < countIn S N :=
    (countIn_tendsto_atTop hS hpos).eventually
      (eventually_gt_atTop (countIn S L + s + 2))
  obtain ⟨Lsum, hLsum⟩ := eventually_atTop.1 hsum
  have hsum2 : ∀ᶠ N in atTop,
      countIn (S + S) (2 * N) < 3 * countIn S (2 * N) :=
    eventually_atTop.2 ⟨Lsum, fun N hN ↦ hLsum (2 * N) (by omega)⟩
  obtain ⟨N, hstop, hsumN, hklarge⟩ :=
    ((frequently_countIn_two_mul_le_four hS hpos hden).and_eventually
      (hsum2.and hlarge)).exists
  let X := window S N
  let k := countIn S N
  have hsk : s < k := by
    dsimp [k]
    omega
  have hkpos : 0 < k := hsk.trans_le' (Nat.zero_le s)
  have hXcard : X.card = k := rfl
  have hXne : X.Nonempty := Finset.card_pos.mp (by simpa [hXcard] using hkpos)
  have hXsmall : (X + X).card ≤ 12 * X.card := by
    have hsub := Finset.card_le_card (window_add_subset S N)
    change (X + X).card ≤ countIn (S + S) (2 * N) at hsub
    change countIn S (2 * N) ≤ 4 * k at hstop
    change countIn (S + S) (2 * N) < 3 * countIn S (2 * N) at hsumN
    change X.card = k at hXcard
    omega
  let Xint := natToIntFinset X
  have hXintne : Xint.Nonempty := natToIntFinset_nonempty.mpr hXne
  have hXintsmall : (Xint + Xint).card ≤ 12 * Xint.card := by
    change (natToIntFinset X + natToIntFinset X).card ≤
      12 * (natToIntFinset X).card
    rw [← natToIntFinset_add, card_natToIntFinset,
      card_natToIntFinset]
    exact hXsmall
  obtain ⟨Q, hQrank, hQproper, hQsub, hQcard⟩ :=
    exists_proper_GAP_cover_of_small_doubling Xint hXintne 12
      (by omega) hXintsmall
  have hprefix (j : ℕ) (hj : j < k) : enumerate S j ∈ X := by
    apply mem_window.mpr
    exact ⟨hpos (enumerate_mem hS j),
      (enumerate_le_iff_lt_countIn hS hpos j N).mpr (by simpa [k] using hj),
      enumerate_mem hS j⟩
  have hparam (j : ℕ) (hj : j < k) :
      ∃ q : Q.Param, Q.eval q = (enumerate S j : ℤ) := by
    apply Q.mem_carrier_iff.mp
    apply hQsub
    exact natCast_mem_natToIntFinset.mpr (hprefix j hj)
  let x : ℕ → Q.Param := fun j ↦
    if hj : j < k then Classical.choose (hparam j hj) else default
  have hx (j : ℕ) (hj : j < k) :
      Q.eval (x j) = (enumerate S j : ℤ) := by
    simp only [x, dif_pos hj]
    exact Classical.choose_spec (hparam j hj)
  let n := k - 1 - s
  let y : ℕ → Q.Param := fun j ↦ x (s + j)
  have hsn : s + n = k - 1 := by
    dsimp [n]
    omega
  have hy (j : ℕ) (hj : j ≤ n) :
      Q.eval (y j) = (enumerate S (s + j) : ℤ) := by
    apply hx
    omega
  have hypos : ∀ j ≤ n, 0 ≤ Q.eval (y j) := by
    intro j hj
    rw [hy j hj]
    exact Int.ofNat_nonneg _
  have hynogap : ∀ j < n,
      Q.eval (y (j + 1)) ≤ 2 * Q.eval (y j) := by
    intro j hj
    rw [hy (j + 1) (by omega), hy j hj.le]
    exact_mod_cast hnogap (s + j) (by omega)
  have hdiam := gap_chain_diameter_bound Q y n hypos hynogap
  have hdiamNat :
      enumerate S (k - 1) ≤
        ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
          enumerate S s := by
    have hy0 : Q.eval (y 0) = (enumerate S s : ℤ) := by
      simpa using hy 0 (Nat.zero_le n)
    have hyn : Q.eval (y n) = (enumerate S (k - 1) : ℤ) := by
      simpa [hsn] using hy n le_rfl
    rw [hyn, hy0] at hdiam
    exact_mod_cast hdiam
  have hcoef :
      (Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard) ≤
        (R + 1).factorial * (3 ^ R * (C * k)) := by
    have hfac : (Q.rank + 1).factorial ≤ (R + 1).factorial := by
      apply Nat.factorial_le
      dsimp [R]
      omega
    have hpow : 3 ^ Q.rank ≤ 3 ^ R := by
      apply Nat.pow_le_pow_right (by omega)
      simpa [R] using hQrank
    have hcard : Q.boxCard ≤ C * k := by
      rw [card_natToIntFinset] at hQcard
      change Q.boxCard ≤ C * X.card at hQcard
      rwa [hXcard] at hQcard
    exact Nat.mul_le_mul hfac (Nat.mul_le_mul hpow hcard)
  have hlinear : enumerate S (k - 1) ≤ D * k := by
    calc
      enumerate S (k - 1) ≤
          ((Q.rank + 1).factorial * (3 ^ Q.rank * Q.boxCard)) *
            enumerate S s := hdiamNat
      _ ≤ ((R + 1).factorial * (3 ^ R * (C * k))) *
            enumerate S s := Nat.mul_le_mul_right _ hcoef
      _ = D * k := by simp only [D]; ring
  have hlastL : L < enumerate S (k - 1) := by
    have hcountL : countIn S L < k := by
      dsimp [k] at hklarge ⊢
      omega
    have hnot : ¬(k - 1 < countIn S L) := by omega
    exact Nat.lt_of_not_ge fun hle ↦
      hnot ((enumerate_le_iff_lt_countIn hS hpos (k - 1) L).mp hle)
  have hdenseLast := hL (enumerate S (k - 1)) hlastL.le
  rw [countIn_enumerate_eq hS hpos (k - 1)] at hdenseLast
  have hkpred : k - 1 + 1 = k := by omega
  rw [hkpred] at hdenseLast
  rw [add_mul, one_mul] at hdenseLast
  omega

end Erdos245Scratch

