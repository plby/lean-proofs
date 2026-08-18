/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.CFP.DilateVolume
import ErdosProblems.Erdos186.DiscreteJohn
import ErdosProblems.Erdos186.Numerical

/-!
# Exact size estimates for the Pham--Zakharov reduction

This file contains the finite counting part of Lemmas 6--8 in
Pham--Zakharov.  The estimates deliberately retain all powers and constants.
In particular, they do not use asymptotic notation and do not assume the
existence of a Conlon--Fox--Pham witness.

There are three ingredients.

* A GAP containing zero contains every subset sum of at most `m` of its
  points in its `m`-fold dilation.  Padding by copies of zero removes the
  otherwise unnecessary union over all possible subset cardinalities.
* A progression all of whose displayed widths are at least two satisfies
  `k ^ r * volume P <= 2 ^ r * volume (k P)`.  This is the exact version of
  the usual lower estimate `|kP| \gg_r k^r |P|`.
* Combining these facts with an `EnhancedCFPWitness`, or with a discrete John
  certificate, gives the cross-progression estimates used when the subset
  sum dimension rises or does not rise.
-/

namespace Erdos186.PZ.Reduction

open scoped BigOperators

noncomputable section

variable {d r q s D k loss : ℕ}

namespace GAP

/-- If a GAP contains zero, a sum of at most `m` points of its carrier lies
in its `m`-fold dilation.  The missing summands are represented by copies of
zero.  This is the finite, one-sided-coordinate form of the familiar fact
`Sigma(A) subset mP` for a homogeneous/symmetric progression. -/
theorem sum_mem_dilate_of_card_le_of_zero_mem (P : Erdos186.GAP d r)
    (hzero : 0 ∈ P.carrier) {S : Finset (LatticePoint d)}
    (hS : S ⊆ P.carrier) {m : ℕ} (hcard : S.card ≤ m) :
    (∑ x ∈ S, x) ∈ (P.dilate m).carrier := by
  classical
  obtain ⟨z, hz⟩ := Erdos186.GAP.mem_carrier_iff.mp hzero
  let repr : LatticePoint d → P.Coord := fun x ↦
    if hx : x ∈ S then
      Classical.choose (Erdos186.GAP.mem_carrier_iff.mp (hS hx))
    else z
  have repr_spec (x : LatticePoint d) (hx : x ∈ S) :
      P.coordPoint (repr x) = x := by
    rw [show repr x = Classical.choose
      (Erdos186.GAP.mem_carrier_iff.mp (hS hx)) by simp [repr, hx]]
    exact Classical.choose_spec (Erdos186.GAP.mem_carrier_iff.mp (hS hx))
  let total : Fin r → ℕ := fun i ↦
    (∑ x ∈ S, (repr x i : ℕ)) + (m - S.card) * (z i : ℕ)
  have total_lt (i : Fin r) :
      total i < m * (P.widths i - 1) + 1 := by
    have hrepr (x : LatticePoint d) (_hx : x ∈ S) :
        (repr x i : ℕ) ≤ P.widths i - 1 := by
      have hi := (repr x i).isLt
      omega
    have hzle : (z i : ℕ) ≤ P.widths i - 1 := by
      have hi := (z i).isLt
      omega
    have hsum :
        ∑ x ∈ S, (repr x i : ℕ) ≤
          S.card * (P.widths i - 1) := by
      calc
        ∑ x ∈ S, (repr x i : ℕ) ≤
            ∑ _x ∈ S, (P.widths i - 1) :=
          Finset.sum_le_sum fun x hx ↦ hrepr x hx
        _ = S.card * (P.widths i - 1) := by simp
    dsimp [total]
    have hpad :
        (m - S.card) * (z i : ℕ) ≤
          (m - S.card) * (P.widths i - 1) :=
      Nat.mul_le_mul_left _ hzle
    have hadd := Nat.add_le_add hsum hpad
    have hm : S.card + (m - S.card) = m := Nat.add_sub_of_le hcard
    calc
      ∑ x ∈ S, (repr x i : ℕ) + (m - S.card) * (z i : ℕ)
          ≤ S.card * (P.widths i - 1) +
              (m - S.card) * (P.widths i - 1) := hadd
      _ = m * (P.widths i - 1) := by rw [← Nat.add_mul, hm]
      _ < m * (P.widths i - 1) + 1 := Nat.lt_succ_self _
  let n : (P.dilate m).Coord := fun i ↦ ⟨total i, total_lt i⟩
  refine Erdos186.GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
  ext j
  have hzj := congrFun hz j
  have hreprsum :
      (∑ x ∈ S, P.coordPoint (repr x) j) = ∑ x ∈ S, x j := by
    apply Finset.sum_congr rfl
    intro x hx
    exact congrFun (repr_spec x hx) j
  have hdouble :
      (∑ i, (∑ x ∈ S, (repr x i : ℤ)) * P.steps i j) =
        ∑ x ∈ S, ∑ i, (repr x i : ℤ) * P.steps i j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [Erdos186.GAP.coordPoint, Erdos186.GAP.dilate, n, total,
    Finset.sum_apply]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [hdouble]
  rw [← add_assoc]
  have hzero_coord : P.offset j + ∑ i, (z i : ℤ) * P.steps i j = 0 := hzj
  have hreprcoord :
      ∑ x ∈ S, (P.offset j + ∑ i, (repr x i : ℤ) * P.steps i j) =
        ∑ x ∈ S, x j := hreprsum
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hreprcoord
  have hmcast : (S.card : ℤ) + (m - S.card : ℕ) = m := by
    exact_mod_cast Nat.add_sub_of_le hcard
  have hoffset :
      (m : ℤ) * P.offset j =
        (S.card : ℤ) * P.offset j +
          ((m - S.card : ℕ) : ℤ) * P.offset j := by
    rw [← add_mul, hmcast]
  have hpadzero :
      ((m - S.card : ℕ) : ℤ) * P.offset j +
          ∑ i, ((m - S.card : ℕ) : ℤ) *
            ((z i : ℤ) * P.steps i j) = 0 := by
    calc
      ((m - S.card : ℕ) : ℤ) * P.offset j +
            ∑ i, ((m - S.card : ℕ) : ℤ) *
              ((z i : ℤ) * P.steps i j)
          = ((m - S.card : ℕ) : ℤ) *
              (P.offset j + ∑ i, (z i : ℤ) * P.steps i j) := by
                rw [mul_add, Finset.mul_sum]
      _ = 0 := by rw [hzero_coord, mul_zero]
  calc
    (m : ℤ) * P.offset j +
          (∑ x ∈ S, ∑ i, (repr x i : ℤ) * P.steps i j) +
          ∑ i, ((m - S.card : ℕ) : ℤ) * (z i : ℤ) * P.steps i j
        = ((S.card : ℤ) * P.offset j +
            ∑ x ∈ S, ∑ i, (repr x i : ℤ) * P.steps i j) +
          (((m - S.card : ℕ) : ℤ) * P.offset j +
            ∑ i, ((m - S.card : ℕ) : ℤ) *
              ((z i : ℤ) * P.steps i j)) := by
                rw [hoffset]
                ring
    _ = ∑ x ∈ S, x j := by rw [hpadzero, add_zero, hreprcoord]

/-- All subset sums of a set in a zero-containing GAP lie in one fixed
dilation, rather than merely in a union of dilations. -/
theorem subsetSums_subset_dilate_of_zero_mem (P : Erdos186.GAP d r)
    (hzero : 0 ∈ P.carrier) {A : Finset (LatticePoint d)}
    (hA : A ⊆ P.carrier) {m : ℕ} (hcard : A.card ≤ m) :
    Erdos186.GAP.subsetSums A ⊆ (P.dilate m).carrier := by
  intro x hx
  obtain ⟨S, hS, rfl⟩ := Erdos186.GAP.mem_subsetSums_iff.mp hx
  exact sum_mem_dilate_of_card_le_of_zero_mem P hzero (hS.trans hA)
    ((Finset.card_le_card hS).trans hcard)

/-- Polynomial subset-sum cardinality bound inside a zero-containing GAP. -/
theorem card_subsetSums_le_succ_pow_mul_volume (P : Erdos186.GAP d r)
    (hzero : 0 ∈ P.carrier) {A : Finset (LatticePoint d)}
    (hA : A ⊆ P.carrier) {m : ℕ} (hcard : A.card ≤ m) :
    (Erdos186.GAP.subsetSums A).card ≤ (m + 1) ^ r * P.volume := by
  exact (Finset.card_le_card
    (subsetSums_subset_dilate_of_zero_mem P hzero hA hcard)).trans
      ((P.dilate m).card_carrier_le_volume.trans (P.volume_dilate_le m))

end GAP

namespace Estimates

/-- Cancel a common positive natural power from a dimension estimate. -/
theorem cancel_pow_of_rank_le {a b C k r q : ℕ} (hk : 0 < k) (hqr : q ≤ r)
    (h : k ^ r * a ≤ C * k ^ q * b) :
    k ^ (r - q) * a ≤ C * b := by
  have hkq : 0 < k ^ q := pow_pos hk q
  apply Nat.le_of_mul_le_mul_left (c := k ^ q) _ hkq
  calc
    k ^ q * (k ^ (r - q) * a) = k ^ r * a := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hqr]
    _ ≤ C * k ^ q * b := h
    _ = k ^ q * (C * b) := by ring

/-- The rational CFP scale comparison implies an integral comparison between
the padded subset-sum scale `s+1` and the dilation scale `k`.  The harmless
factor two is exactly the cost of padding after replacing `s+1` by `2s`. -/
theorem succ_reserve_le_two_mul_scaleDen_mul_scale
    {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    s + 1 ≤ (2 * W.scaleDen) * k := by
  have hspos := W.s_pos
  have hs : s + 1 ≤ 2 * s := by omega
  have hnum : 1 ≤ W.scaleNum := W.scaleNum_pos
  calc
    s + 1 ≤ W.scaleNum * (s + 1) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (s + 1) hnum
    _ ≤ W.scaleNum * (2 * s) := Nat.mul_le_mul_left _ hs
    _ = 2 * (W.scaleNum * s) := by ring
    _ ≤ 2 * (W.scaleDen * k) := Nat.mul_le_mul_left 2 W.scale_lower
    _ = (2 * W.scaleDen) * k := by ring

/-- The raw cross-progression estimate furnished by a CFP witness.

The hypothesis says that the witness core, together with zero, lies in a
comparison GAP `Q`.  Coverage of the dilated witness progression by subset
sums then bounds it by the `s`-fold dilation of `Q`. -/
theorem cfpWitness_dilatedVolume_le {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : Erdos186.GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier) :
    (W.progression.dilate k).volume ≤ (s + 1) ^ q * Q.volume := by
  calc
    (W.progression.dilate k).volume
        ≤ (Erdos186.GAP.subsetSums W.reserved).card :=
      W.dilated_volume_le_card_subsetSums
    _ ≤ (s + 1) ^ q * Q.volume := by
      apply GAP.card_subsetSums_le_succ_pow_mul_volume Q
      · exact hcore (Finset.mem_insert_self 0 W.core)
      · exact W.reserved_subset_core.trans
          ((Finset.subset_insert 0 W.core).trans hcore)
      · exact W.reserved_small

/-- Dimension-sensitive volume comparison for a CFP witness.  No division
or asymptotics are hidden in the statement. -/
theorem cfpWitness_crossVolume {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : Erdos186.GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier) :
    k ^ W.rank * W.progression.volume ≤
      2 ^ W.rank * ((s + 1) ^ q * Q.volume) := by
  have hwidth : ∀ i, 2 ≤ W.progression.widths i := fun i ↦
    (W.three_le_width i).trans' (by omega)
  exact (Erdos186.GAP.pow_mul_volume_le_pow_two_mul_volume_dilate
    W.progression hwidth k).trans
      (Nat.mul_le_mul_left _ (cfpWitness_dilatedVolume_le W Q hcore))

/-- Lemma 6 in cancellation form.  The enhanced witness's rational scale
comparison controls the padded scale `s+1`; the excess rank appears as a
power of `k` on the left. -/
theorem cfpWitness_dimensionIncrease {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : Erdos186.GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier)
    (hrank : q ≤ W.rank) :
    k ^ (W.rank - q) * W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ q * Q.volume := by
  apply cancel_pow_of_rank_le W.k_pos hrank
  refine (cfpWitness_crossVolume W Q hcore).trans ?_
  have hpow : (s + 1) ^ q ≤ ((2 * W.scaleDen) * k) ^ q :=
    Nat.pow_le_pow_left (succ_reserve_le_two_mul_scaleDen_mul_scale W) q
  calc
    2 ^ W.rank * ((s + 1) ^ q * Q.volume)
        ≤ 2 ^ W.rank * (((2 * W.scaleDen) * k) ^ q * Q.volume) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
    _ = (2 ^ W.rank * (2 * W.scaleDen) ^ q) * k ^ q * Q.volume := by
      rw [mul_pow]
      ring

/-- Exact no-dimension-increase consequence of the CFP cardinality chain.
This is source-faithful: it uses the witness coverage by subset sums, and
does not assume an unshifted inclusion between two dilated carriers. -/
theorem cfpWitness_noDimensionIncrease {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : Erdos186.GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier)
    (hrank : q ≤ W.rank) :
    W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ q * Q.volume := by
  have hdimension := cfpWitness_dimensionIncrease W Q hcore hrank
  have hkpow : 0 < k ^ (W.rank - q) := pow_pos W.k_pos _
  calc
    W.progression.volume ≤
        k ^ (W.rank - q) * W.progression.volume := by
      exact Nat.le_mul_of_pos_left W.progression.volume hkpow
    _ ≤ 2 ^ W.rank * (2 * W.scaleDen) ^ q * Q.volume := hdimension

/-- Discrete-John packaging of the source-faithful no-dimension-increase
estimate.  The core lies in the John outer progression, then witness
coverage and the John cardinality sandwich do all of the counting. -/
theorem cfpWitness_noDimensionIncrease_discreteJohn
    {A points : Finset (LatticePoint d)} {factor : ℕ}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (C : DiscreteJohn.Certificate points q factor)
    (hcore : insert 0 W.core ⊆ C.outer.carrier)
    (hrank : q ≤ W.rank) :
    W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ q *
        ((2 * factor + 1) ^ q * points.card) := by
  calc
    W.progression.volume ≤
        2 ^ W.rank * (2 * W.scaleDen) ^ q * C.outer.volume :=
      cfpWitness_noDimensionIncrease W C.outer hcore hrank
    _ = 2 ^ W.rank * (2 * W.scaleDen) ^ q * C.outer.carrier.card := by
      rw [Erdos186.GAP.card_carrier_eq_volume C.outer C.outer_proper]
    _ ≤ 2 ^ W.rank * (2 * W.scaleDen) ^ q *
        ((2 * factor + 1) ^ q * points.card) :=
      Nat.mul_le_mul_left _ C.card_outer_le

/-- Real-cast form of the exact CFP dimension-increase estimate. -/
theorem cfpWitness_dimensionIncrease_real {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : Erdos186.GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier)
    (hrank : q ≤ W.rank) :
    (k : ℝ) ^ (W.rank - q) * W.progression.volume ≤
      (2 : ℝ) ^ W.rank * (2 * W.scaleDen) ^ q * Q.volume := by
  exact_mod_cast cfpWitness_dimensionIncrease W Q hcore hrank

/-- Real-cast form of the discrete John no-dimension-increase estimate. -/
theorem cfpWitness_noDimensionIncrease_discreteJohn_real
    {A points : Finset (LatticePoint d)} {factor : ℕ}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (C : DiscreteJohn.Certificate points q factor)
    (hcore : insert 0 W.core ⊆ C.outer.carrier)
    (hrank : q ≤ W.rank) :
    (W.progression.volume : ℝ) ≤
      (2 : ℝ) ^ W.rank * (2 * W.scaleDen) ^ q *
        ((2 * factor + 1) ^ q * points.card) := by
  exact_mod_cast cfpWitness_noDimensionIncrease_discreteJohn
    W C hcore hrank

end Estimates

end

end Erdos186.PZ.Reduction
