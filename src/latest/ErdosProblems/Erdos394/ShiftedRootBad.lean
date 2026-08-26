import ErdosProblems.Erdos394.GeneralGlobalMediumSieve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shifted root boxes for denominator lower bounds
-/

open Nat Finset

namespace Erdos394

noncomputable local instance shiftedRootUnitsFintype (p : ℕ) [NeZero p] :
    Fintype (ZMod p)ˣ := Fintype.ofFinite _

/-- A local multiplier hits the block shifted so that label `a` is the term
absorbing a future large prime. -/
def localShiftedBlockHit (p K j a : ℕ) (h : (ZMod p)ˣ) : Prop :=
  ∃ b ∈ Finset.range K,
    ((h : ZMod p) * (j : ZMod p) + (b : ZMod p)) = (a : ZMod p)

noncomputable def localShiftedBlockHitSet
    (p K j a : ℕ) [NeZero p] : Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter (localShiftedBlockHit p K j a)

/-- If `p|j`, every shifted local hit set is at most the whole unit group. -/
theorem card_localShiftedBlockHitSet_of_dvd_le
    {p K j a : ℕ} [NeZero p] (hp : p.Prime) (hpj : p ∣ j) :
    (localShiftedBlockHitSet p K j a).card ≤ p - 1 := by
  classical
  calc
    (localShiftedBlockHitSet p K j a).card ≤
        (Finset.univ : Finset (ZMod p)ˣ).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = p - 1 := by
      rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- If `p∤j`, deleting the distinguished label `a` leaves at most `K-1`
possible unit multipliers. -/
theorem card_localShiftedBlockHitSet_of_not_dvd_le
    {p K j a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : a < K) (hKp : K < p) (hpj : ¬p ∣ j) :
    (localShiftedBlockHitSet p K j a).card ≤ K - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let s := localShiftedBlockHitSet p K j a
  let u := (Finset.range K).erase a
  have hjz : (j : ZMod p) ≠ 0 := by
    intro hz
    exact hpj ((ZMod.natCast_eq_zero_iff j p).mp hz)
  let label : (ZMod p)ˣ → ℕ := fun h ↦
    ((a : ZMod p) - (h : ZMod p) * (j : ZMod p)).val
  have hmaps : Set.MapsTo label (↑s) (↑u) := by
    intro h hh
    have hh' : h ∈ localShiftedBlockHitSet p K j a := by simpa [s] using hh
    obtain ⟨b, hbK, hbeq⟩ := (Finset.mem_filter.mp hh').2
    have hb_ltK : b < K := Finset.mem_range.mp hbK
    have hb_ltp : b < p := hb_ltK.trans hKp
    have hlabel : label h = b := by
      unfold label
      have hz : (a : ZMod p) - (h : ZMod p) * (j : ZMod p) =
          (b : ZMod p) := by
        rw [← hbeq]
        ring
      rw [hz, ZMod.val_natCast_of_lt hb_ltp]
    have hba : b ≠ a := by
      intro hba
      have hz : (h : ZMod p) * (j : ZMod p) = 0 := by
        calc
          (h : ZMod p) * (j : ZMod p) =
              ((h : ZMod p) * (j : ZMod p) + (b : ZMod p)) -
                (b : ZMod p) := by ring
          _ = (a : ZMod p) - (b : ZMod p) := by rw [hbeq]
          _ = 0 := by rw [hba]; ring
      exact (mul_ne_zero h.ne_zero hjz) hz
    rw [hlabel]
    exact Finset.mem_erase.mpr ⟨hba, hbK⟩
  have hinj : Set.InjOn label (↑s) := by
    intro h₁ hh₁ h₂ hh₂ heq
    have hz : (a : ZMod p) - (h₁ : ZMod p) * (j : ZMod p) =
        (a : ZMod p) - (h₂ : ZMod p) * (j : ZMod p) :=
      ZMod.val_injective p heq
    have hmul : (h₁ : ZMod p) * (j : ZMod p) =
        (h₂ : ZMod p) * (j : ZMod p) := by
      calc
        (h₁ : ZMod p) * (j : ZMod p) =
            (a : ZMod p) - ((a : ZMod p) -
              (h₁ : ZMod p) * (j : ZMod p)) := by ring
        _ = (a : ZMod p) - ((a : ZMod p) -
              (h₂ : ZMod p) * (j : ZMod p)) := by rw [hz]
        _ = (h₂ : ZMod p) * (j : ZMod p) := by ring
    apply Units.ext
    exact mul_right_cancel₀ hjz hmul
  have hcard := Finset.card_le_card_of_injOn label hmaps hinj
  have hau : a ∈ Finset.range K := Finset.mem_range.mpr ha
  have hcardu : u.card = K - 1 := by
    dsimp [u]
    rw [Finset.card_erase_of_mem hau, Finset.card_range]
  exact hcard.trans_eq hcardu

/-- Uniform shifted local count is bounded by the same arithmetic weight as
the unshifted root box. -/
theorem card_localShiftedBlockHitSet_le
    {p K j a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : a < K) (hKp : K < p) :
    (localShiftedBlockHitSet p K j a).card ≤
      if p ∣ j then p - 1 else K - 1 := by
  by_cases hpj : p ∣ j
  · rw [if_pos hpj]
    exact card_localShiftedBlockHitSet_of_dvd_le hp hpj
  · rw [if_neg hpj]
    exact card_localShiftedBlockHitSet_of_not_dvd_le hp ha hKp hpj

/-- Independent local tuples producing a shifted hit. -/
noncomputable def shiftedRootBoxHitTupleSet
    (P : Finset ℕ) (K j a : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  letI (p : ↥P) : NeZero p.1 := ⟨(hprime p.1 p.2).ne_zero⟩
  exact Fintype.piFinset
    (fun p : ↥P ↦ localShiftedBlockHitSet p.1 K j a)

/-- A shifted tuple set has at most the standard root-box local weight. -/
theorem card_shiftedRootBoxHitTupleSet_le
    (P : Finset ℕ) (K j a : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ha : a < K) (hlarge : ∀ p ∈ P, K < p) :
    (shiftedRootBoxHitTupleSet P K j a hprime).card ≤
      rootBoxLocalWeight P K j := by
  classical
  letI (p : ↥P) : NeZero p.1 := ⟨(hprime p.1 p.2).ne_zero⟩
  unfold shiftedRootBoxHitTupleSet rootBoxLocalWeight
  rw [Fintype.card_piFinset]
  calc
    (∏ p : ↥P, (localShiftedBlockHitSet p.1 K j a).card) ≤
      ∏ p : ↥P, (if p.1 ∣ j then p.1 - 1 else K - 1) := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        exact card_localShiftedBlockHitSet_le (hprime p.1 p.2) ha
          (hlarge p.1 p.2)
    _ = ∏ p ∈ P, (if p ∣ j then p - 1 else K - 1) := by
      rw [← Finset.attach_eq_univ]
      simpa using Finset.prod_attach P
        (fun p ↦ if p ∣ j then p - 1 else K - 1)

/-- Tuples with at least one shifted hit, over all absorbed labels and times
`1≤j≤Y`. -/
noncomputable def shiftedRootBadTupleSet
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  exact (Finset.range K).biUnion (fun a ↦
    (Finset.Icc 1 Y).biUnion (fun j ↦
      shiftedRootBoxHitTupleSet P K j a hprime))

/-- Union bound: all `K` shifts cost at most `K` copies of the ordinary first
moment. -/
theorem card_shiftedRootBadTupleSet_le
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, K < p) :
    (shiftedRootBadTupleSet P K Y hprime).card ≤
      K * rootBoxFirstMoment P K Y := by
  classical
  unfold shiftedRootBadTupleSet
  calc
    ((Finset.range K).biUnion (fun a ↦
      (Finset.Icc 1 Y).biUnion (fun j ↦
        shiftedRootBoxHitTupleSet P K j a hprime))).card ≤
      ∑ a ∈ Finset.range K,
        ((Finset.Icc 1 Y).biUnion (fun j ↦
          shiftedRootBoxHitTupleSet P K j a hprime)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.range K,
        ∑ j ∈ Finset.Icc 1 Y,
          (shiftedRootBoxHitTupleSet P K j a hprime).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Finset.range K,
        rootBoxFirstMoment P K Y := by
      apply Finset.sum_le_sum
      intro a ha
      unfold rootBoxFirstMoment
      apply Finset.sum_le_sum
      intro j hj
      exact card_shiftedRootBoxHitTupleSet_le P K j a hprime
        (Finset.mem_range.mp ha) hlarge
    _ = K * rootBoxFirstMoment P K Y := by simp

/-- Normalized shifted-bad proportion has the sharp first-moment scale
`K^(|P|+1)Y/q`. -/
theorem normalized_card_shiftedRootBadTupleSet_le
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hK : 1 ≤ K) (hlarge : ∀ p ∈ P, K < p) :
    ((shiftedRootBadTupleSet P K Y hprime).card : ℝ) /
        (rootBoxTupleUniverseCount P hprime : ℝ) ≤
      ((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
        (primeProduct P : ℝ) := by
  have hcard := card_shiftedRootBadTupleSet_le P K Y hprime hlarge
  have hfirst := (normalized_rootBoxTupleFirstMoment_bounds P K Y hprime
    hK hlarge).2
  rw [rootBoxTupleFirstMoment_eq P K Y hprime hK hlarge] at hfirst
  have hUposNat : 0 < rootBoxTupleUniverseCount P hprime := by
    rw [rootBoxTupleUniverseCount_eq_primeUnitCount P hprime]
    unfold primeUnitCount
    exact Finset.prod_pos fun p hp ↦ by
      have := (hprime p hp).two_le
      omega
  have hUpos : (0 : ℝ) < rootBoxTupleUniverseCount P hprime := by
    exact_mod_cast hUposNat
  have hdiv : ((shiftedRootBadTupleSet P K Y hprime).card : ℝ) /
      (rootBoxTupleUniverseCount P hprime : ℝ) ≤
      (K : ℝ) * ((rootBoxFirstMoment P K Y : ℝ) /
        (rootBoxTupleUniverseCount P hprime : ℝ)) := by
    rw [div_le_iff₀ hUpos]
    have hc : ((shiftedRootBadTupleSet P K Y hprime).card : ℝ) ≤
        (K : ℝ) * (rootBoxFirstMoment P K Y : ℝ) := by
      exact_mod_cast hcard
    calc
      ((shiftedRootBadTupleSet P K Y hprime).card : ℝ) ≤
          (K : ℝ) * (rootBoxFirstMoment P K Y : ℝ) := hc
      _ = (K : ℝ) * ((rootBoxFirstMoment P K Y : ℝ) /
          (rootBoxTupleUniverseCount P hprime : ℝ)) *
            (rootBoxTupleUniverseCount P hprime : ℝ) := by field_simp
  apply hdiv.trans
  calc
    (K : ℝ) * ((rootBoxFirstMoment P K Y : ℝ) /
        (rootBoxTupleUniverseCount P hprime : ℝ)) ≤
      (K : ℝ) * (((K ^ P.card : ℕ) : ℝ) * (Y : ℝ) /
        (primeProduct P : ℝ)) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_pow] using hfirst) (by positivity)
    _ = ((K ^ (P.card + 1) : ℕ) : ℝ) * (Y : ℝ) /
        (primeProduct P : ℝ) := by
      rw [pow_succ]
      push_cast
      ring

end Erdos394
