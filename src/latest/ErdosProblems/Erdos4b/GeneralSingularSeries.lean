/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralExceptionalPreSieve

/-!
# Local factors for the Maynard large-gap singular series

For a prime `p`, the normalization weight excludes the residue classes on
which one of the forms

`n + h*q`, `m*(n + h*q) - 1`

vanishes.  This file packages those classes as finite subsets of `ZMod p`,
proves the dimension bound for their cardinality, and records positivity of
the resulting finite Euler product.  The shift tuple is allowed to depend on
the pre-sieve cutoff; this is essential at primes between the dimension and
the cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4GeneralSingularSeriesDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A `K`-element admissible tuple all of whose shifts are multiples of the
full pre-sieve primorial. -/
def preSievedShifts (K w : ℕ) : Finset ℕ :=
  (Finset.range K).image fun i ↦ primorial w * i

theorem card_preSievedShifts (K w : ℕ) :
    (preSievedShifts K w).card = K := by
  rw [preSievedShifts, Finset.card_image_iff.mpr]
  · simp
  · intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left (primorial_pos w) hab

theorem primorial_dvd_shift_of_mem_preSievedShifts
    {K w h : ℕ} (hh : h ∈ preSievedShifts K w) :
    primorial w ∣ h := by
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hh
  exact dvd_mul_right _ _

theorem prime_dvd_shift_of_mem_preSievedShifts
    {K w h p : ℕ} (hh : h ∈ preSievedShifts K w)
    (hp : p.Prime) (hpw : p ≤ w) :
    p ∣ h := by
  exact (hp.dvd_primorial_iff.mpr hpw).trans
    (primorial_dvd_shift_of_mem_preSievedShifts hh)

/-- The standard residue-cardinality admissibility proof, now with the
larger cutoff-dependent primorial. -/
theorem preSievedShifts_admissible {K w : ℕ} (hKw : K ≤ w) :
    AdmissibleShifts (preSievedShifts K w) := by
  intro p hp
  by_cases hpw : p ≤ w
  · have hsubset :
        (preSievedShifts K w).image (fun h ↦ h % p) ⊆ {0} := by
      intro r hr
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hr
      simp only [Finset.mem_singleton]
      exact Nat.mod_eq_zero_of_dvd
        (prime_dvd_shift_of_mem_preSievedShifts hh hp hpw)
    calc
      ((preSievedShifts K w).image (fun h ↦ h % p)).card ≤
          ({0} : Finset ℕ).card := Finset.card_le_card hsubset
      _ = 1 := by simp
      _ < p := hp.one_lt
  · have hwp : w < p := by omega
    calc
      ((preSievedShifts K w).image (fun h ↦ h % p)).card ≤
          (preSievedShifts K w).card := Finset.card_image_le
      _ = K := card_preSievedShifts K w
      _ < p := hKw.trans_lt hwp

/-- Residues on which one of the first-family forms vanishes. -/
noncomputable def largeGapFirstLocalResidues
    (H : Finset ℕ) (q p : ℕ) : Finset (ZMod p) :=
  H.attach.image fun h ↦ -((h.1 * q : ℕ) : ZMod p)

/-- Residues on which one of the companion forms vanishes.  If `p ∣ m`
there is no such residue; otherwise multiplication by `m` is invertible in
`ZMod p`. -/
noncomputable def largeGapCompanionLocalResidues
    (H : Finset ℕ) (m q p : ℕ) : Finset (ZMod p) :=
  if (m : ZMod p) = 0 then ∅
  else H.attach.image fun h ↦ (m : ZMod p)⁻¹ - (h.1 * q : ℕ)

/-- All forbidden residues for the doubled large-gap system. -/
noncomputable def largeGapLocalForbiddenResidues
    (H : Finset ℕ) (m q p : ℕ) : Finset (ZMod p) :=
  largeGapFirstLocalResidues H q p ∪
    largeGapCompanionLocalResidues H m q p

/-- The local multiplicity `ω_{m,q}(p)`. -/
def largeGapLocalMultiplicity
    (H : Finset ℕ) (m q p : ℕ) : ℕ :=
  (largeGapLocalForbiddenResidues H m q p).card

/-- The first local residue set is exactly the set on which one of the
linear forms `a + h*q` vanishes. -/
theorem mem_largeGapFirstLocalResidues_iff
    {H : Finset ℕ} {q p : ℕ} {a : ZMod p} :
    a ∈ largeGapFirstLocalResidues H q p ↔
      ∃ h ∈ H, a + (h * q : ℕ) = 0 := by
  constructor
  · intro ha
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨h.1, h.2, by simp⟩
  · rintro ⟨h, hh, ha⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨h, hh⟩, Finset.mem_attach _ _, ?_⟩
    exact ((eq_neg_iff_add_eq_zero).2 ha).symm

/-- At a prime modulus, the companion local residue set is exactly the set
on which one of the affine forms `m*(a + h*q) - 1` vanishes. -/
theorem mem_largeGapCompanionLocalResidues_iff
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime) {a : ZMod p} :
    a ∈ largeGapCompanionLocalResidues H m q p ↔
      ∃ h ∈ H, (m : ZMod p) * (a + (h * q : ℕ)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hm : (m : ZMod p) = 0
  · simp [largeGapCompanionLocalResidues, hm]
  · constructor
    · intro ha
      rw [largeGapCompanionLocalResidues, if_neg hm] at ha
      obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp ha
      refine ⟨h.1, h.2, ?_⟩
      rw [sub_add_cancel]
      exact mul_inv_cancel₀ hm
    · rintro ⟨h, hh, ha⟩
      rw [largeGapCompanionLocalResidues, if_neg hm]
      apply Finset.mem_image.mpr
      refine ⟨⟨h, hh⟩, Finset.mem_attach _ _, ?_⟩
      have hcancel : (m : ZMod p) * (m : ZMod p)⁻¹ = 1 :=
        mul_inv_cancel₀ hm
      have hax : a + (h * q : ℕ) = (m : ZMod p)⁻¹ := by
        apply (mul_left_cancel₀ hm)
        rw [ha, hcancel]
      exact ((eq_sub_iff_add_eq).2 hax).symm

/-- Thus `largeGapLocalMultiplicity` is the cardinality of the union of
the two source congruence obstructions, rather than an auxiliary upper
bound for that cardinality. -/
theorem mem_largeGapLocalForbiddenResidues_iff
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime) {a : ZMod p} :
    a ∈ largeGapLocalForbiddenResidues H m q p ↔
      (∃ h ∈ H, a + (h * q : ℕ) = 0) ∨
        (∃ h ∈ H, (m : ZMod p) * (a + (h * q : ℕ)) = 1) := by
  rw [largeGapLocalForbiddenResidues, Finset.mem_union,
    mem_largeGapFirstLocalResidues_iff,
    mem_largeGapCompanionLocalResidues_iff hp]

/-- Above the pre-sieve cutoff, multiplication by a number not divisible
by `p` keeps the pre-sieved shifts distinct modulo `p`. -/
theorem preSievedFirstResidueMap_injOn
    {K w q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) :
    Set.InjOn
      (fun h : ↥(preSievedShifts K w) ↦ -((h.1 * q : ℕ) : ZMod p))
      Set.univ := by
  letI : Fact p.Prime := ⟨hp⟩
  have hP0 : ((primorial w : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff (primorial w) p).mp hzero
    exact (not_le_of_gt hwp) (hp.dvd_primorial_iff.mp hdiv)
  have hq0 : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro hzero
    exact hpq ((ZMod.natCast_eq_zero_iff q p).mp hzero)
  intro a _ha b _hb hab
  obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp a.2
  obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp b.2
  have habpos : ((a.1 * q : ℕ) : ZMod p) = (b.1 * q : ℕ) :=
    neg_injective hab
  have habcast : (a.1 : ZMod p) * (q : ZMod p) =
      (b.1 : ZMod p) * (q : ZMod p) := by
    simpa only [Nat.cast_mul] using habpos
  have habbase : (a.1 : ZMod p) = (b.1 : ZMod p) :=
    mul_right_cancel₀ hq0 habcast
  rw [← hai, ← hbj] at habbase
  have hijcast : (i : ZMod p) = (j : ZMod p) := by
    apply mul_left_cancel₀ hP0
    simpa only [Nat.cast_mul] using habbase
  have hijmod : i ≡ j [MOD p] :=
    (ZMod.natCast_eq_natCast_iff i j p).mp hijcast
  have hip : i < p :=
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hKw).trans hwp
  have hjp : j < p :=
    (lt_of_lt_of_le (Finset.mem_range.mp hj) hKw).trans hwp
  have hij : i = j := hijmod.eq_of_lt_of_lt hip hjp
  apply Subtype.ext
  rw [← hai, ← hbj, hij]

theorem card_largeGapFirstLocalResidues_preSievedShifts
    {K w q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) :
    (largeGapFirstLocalResidues (preSievedShifts K w) q p).card = K := by
  unfold largeGapFirstLocalResidues
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_attach.trans (card_preSievedShifts K w)
  · intro a _ha b _hb
    exact preSievedFirstResidueMap_injOn hp hKw hwp hpq
      (Set.mem_univ a) (Set.mem_univ b)

theorem card_largeGapCompanionLocalResidues_preSievedShifts
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m) :
    (largeGapCompanionLocalResidues (preSievedShifts K w) m q p).card = K := by
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro hm
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hm)
  unfold largeGapCompanionLocalResidues
  rw [if_neg hm0, Finset.card_image_iff.mpr]
  · exact Finset.card_attach.trans (card_preSievedShifts K w)
  · intro a _ha b _hb hab
    apply preSievedFirstResidueMap_injOn hp hKw hwp hpq
      (Set.mem_univ a) (Set.mem_univ b)
    exact congrArg Neg.neg (sub_right_inj.mp hab)

/-- Away from the exceptional primes `p = q` and `p ∣ m`, a drop below
the generic multiplicity `2K` forces a genuine first/companion collision.
The collision prime divides exactly one of Maynard's signed affine
differences. -/
theorem exists_crossAffineDifference_of_localMultiplicity_lt
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m)
    (homega : largeGapLocalMultiplicity (preSievedShifts K w) m q p <
      2 * K) :
    ∃ hb ha : ↥(preSievedShifts K w),
      (p : ℤ) ∣ crossAffineDifference m q (hb, ha) := by
  let F := largeGapFirstLocalResidues (preSievedShifts K w) q p
  let E := largeGapCompanionLocalResidues (preSievedShifts K w) m q p
  have hF : F.card = K :=
    card_largeGapFirstLocalResidues_preSievedShifts hp hKw hwp hpq
  have hE : E.card = K :=
    card_largeGapCompanionLocalResidues_preSievedShifts hp hKw hwp hpq hpm
  have hnot : ¬Disjoint F E := by
    intro hdisj
    have hcard := Finset.card_union_of_disjoint hdisj
    have heq : largeGapLocalMultiplicity (preSievedShifts K w) m q p =
        2 * K := by
      unfold largeGapLocalMultiplicity largeGapLocalForbiddenResidues
      change (F ∪ E).card = 2 * K
      rw [hcard, hF, hE]
      omega
    omega
  obtain ⟨a, haF, haE⟩ := Finset.not_disjoint_iff.mp hnot
  obtain ⟨ha, haH, hfirst⟩ :=
    mem_largeGapFirstLocalResidues_iff.mp haF
  obtain ⟨hb, hbH, hcomp⟩ :=
    (mem_largeGapCompanionLocalResidues_iff hp).mp haE
  let ha' : ↥(preSievedShifts K w) := ⟨ha, haH⟩
  let hb' : ↥(preSievedShifts K w) := ⟨hb, hbH⟩
  refine ⟨hb', ha', ?_⟩
  have haeq : a = -((ha * q : ℕ) : ZMod p) :=
    (eq_neg_iff_add_eq_zero).2 hfirst
  rw [haeq] at hcomp
  have hcast : ((m * (ha * q) + 1 : ℕ) : ZMod p) =
      (m * (hb * q) : ℕ) := by
    push_cast
    push_cast at hcomp
    rw [← hcomp]
    ring
  have hmod : m * (ha * q) + 1 ≡ m * (hb * q) [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hdiv := Nat.modEq_iff_dvd.mp hmod
  simpa [crossAffineDifference, hb', ha'] using hdiv

theorem prime_dvd_crossExceptionalModulus_of_localMultiplicity_lt
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m)
    (homega : largeGapLocalMultiplicity (preSievedShifts K w) m q p <
      2 * K) :
    p ∣ crossExceptionalModulus (preSievedShifts K w) m q := by
  obtain ⟨hb, ha, hdiv⟩ :=
    exists_crossAffineDifference_of_localMultiplicity_lt
      hp hKw hwp hpq hpm homega
  have hpAbs : p ∣ (crossAffineDifference m q (hb, ha)).natAbs :=
    Int.natCast_dvd.mp hdiv
  exact hpAbs.trans
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ (hb, ha)))

theorem card_largeGapFirstLocalResidues_le
    (H : Finset ℕ) (q p : ℕ) :
    (largeGapFirstLocalResidues H q p).card ≤ H.card := by
  unfold largeGapFirstLocalResidues
  exact Finset.card_image_le.trans_eq Finset.card_attach

theorem card_largeGapCompanionLocalResidues_le
    (H : Finset ℕ) (m q p : ℕ) :
    (largeGapCompanionLocalResidues H m q p).card ≤ H.card := by
  unfold largeGapCompanionLocalResidues
  split_ifs
  · simp
  · exact Finset.card_image_le.trans_eq Finset.card_attach

theorem largeGapLocalMultiplicity_le_two_mul_card
    (H : Finset ℕ) (m q p : ℕ) :
    largeGapLocalMultiplicity H m q p ≤ 2 * H.card := by
  unfold largeGapLocalMultiplicity largeGapLocalForbiddenResidues
  calc
    (largeGapFirstLocalResidues H q p ∪
        largeGapCompanionLocalResidues H m q p).card ≤
        (largeGapFirstLocalResidues H q p).card +
          (largeGapCompanionLocalResidues H m q p).card :=
      Finset.card_union_le _ _
    _ ≤ H.card + H.card := Nat.add_le_add
      (card_largeGapFirstLocalResidues_le H q p)
      (card_largeGapCompanionLocalResidues_le H m q p)
    _ = 2 * H.card := by omega

/-- Consequently every nonexceptional rough prime has the generic local
multiplicity `2K`.  This is the exact support statement needed before the
singular-series inverse is expanded. -/
theorem largeGapLocalMultiplicity_eq_generic_of_not_exceptional
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m)
    (hpex : ¬p ∣ crossExceptionalModulus (preSievedShifts K w) m q) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p = 2 * K := by
  have hle :
      largeGapLocalMultiplicity (preSievedShifts K w) m q p ≤ 2 * K := by
    simpa [card_preSievedShifts] using
      largeGapLocalMultiplicity_le_two_mul_card
        (preSievedShifts K w) m q p
  by_contra hne
  have hlt :
      largeGapLocalMultiplicity (preSievedShifts K w) m q p < 2 * K := by
    omega
  exact hpex (prime_dvd_crossExceptionalModulus_of_localMultiplicity_lt
    hp hKw hwp hpq hpm hlt)

theorem largeGapCompanionLocalResidues_eq_empty_of_dvd
    {H : Finset ℕ} {m q p : ℕ} (hpm : p ∣ m) :
    largeGapCompanionLocalResidues H m q p = ∅ := by
  unfold largeGapCompanionLocalResidues
  rw [if_pos]
  exact (ZMod.natCast_eq_zero_iff m p).mpr hpm

theorem largeGapFirstLocalResidues_subset_zero_of_shifts
    {H : Finset ℕ} {q p : ℕ} (hshift : ∀ h ∈ H, p ∣ h) :
    largeGapFirstLocalResidues H q p ⊆ {0} := by
  intro r hr
  obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hr
  have hph : p ∣ h.1 := hshift h.1 h.2
  have hpMul : p ∣ h.1 * q := dvd_mul_of_dvd_left hph q
  simp only [Finset.mem_singleton]
  rw [(ZMod.natCast_eq_zero_iff (h.1 * q) p).mpr hpMul, neg_zero]

theorem largeGapCompanionLocalResidues_subset_singleton_of_shifts
    {H : Finset ℕ} {m q p : ℕ} (hshift : ∀ h ∈ H, p ∣ h) :
    largeGapCompanionLocalResidues H m q p ⊆ {(m : ZMod p)⁻¹} := by
  unfold largeGapCompanionLocalResidues
  split_ifs with hm
  · simp
  · intro r hr
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hr
    have hph : p ∣ h.1 := hshift h.1 h.2
    have hpMul : p ∣ h.1 * q := dvd_mul_of_dvd_left hph q
    simp only [Finset.mem_singleton]
    rw [(ZMod.natCast_eq_zero_iff (h.1 * q) p).mpr hpMul, sub_zero]

theorem largeGapFirstLocalResidues_eq_singleton_of_shifts
    {H : Finset ℕ} {q p : ℕ} (hH : H.Nonempty)
    (hshift : ∀ h ∈ H, p ∣ h) :
    largeGapFirstLocalResidues H q p = {0} := by
  apply Finset.Subset.antisymm
  · exact largeGapFirstLocalResidues_subset_zero_of_shifts hshift
  · intro a ha
    simp only [Finset.mem_singleton] at ha
    subst a
    rw [mem_largeGapFirstLocalResidues_iff]
    obtain ⟨h, hh⟩ := hH
    refine ⟨h, hh, ?_⟩
    have hpMul : p ∣ h * q := dvd_mul_of_dvd_left (hshift h hh) q
    rw [(ZMod.natCast_eq_zero_iff (h * q) p).mpr hpMul]
    simp

theorem largeGapCompanionLocalResidues_eq_singleton_of_shifts
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime) (hH : H.Nonempty)
    (hshift : ∀ h ∈ H, p ∣ h) (hm : (m : ZMod p) ≠ 0) :
    largeGapCompanionLocalResidues H m q p = {(m : ZMod p)⁻¹} := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Finset.Subset.antisymm
  · exact largeGapCompanionLocalResidues_subset_singleton_of_shifts hshift
  · intro a ha
    simp only [Finset.mem_singleton] at ha
    subst a
    rw [mem_largeGapCompanionLocalResidues_iff hp]
    obtain ⟨h, hh⟩ := hH
    refine ⟨h, hh, ?_⟩
    have hpMul : p ∣ h * q := dvd_mul_of_dvd_left (hshift h hh) q
    rw [(ZMod.natCast_eq_zero_iff (h * q) p).mpr hpMul, add_zero]
    exact mul_inv_cancel₀ hm

/-- At a small prime dividing all shifts, the two-dimensional local
multiplicity is exactly one or two according as `p` divides `m`. -/
theorem largeGapLocalMultiplicity_eq_one_of_shifts_of_dvd
    {H : Finset ℕ} {m q p : ℕ} (hH : H.Nonempty)
    (hshift : ∀ h ∈ H, p ∣ h) (hpm : p ∣ m) :
    largeGapLocalMultiplicity H m q p = 1 := by
  rw [largeGapLocalMultiplicity, largeGapLocalForbiddenResidues,
    largeGapFirstLocalResidues_eq_singleton_of_shifts hH hshift,
    largeGapCompanionLocalResidues_eq_empty_of_dvd hpm]
  simp

theorem largeGapLocalMultiplicity_eq_two_of_shifts_of_not_dvd
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime) (hH : H.Nonempty)
    (hshift : ∀ h ∈ H, p ∣ h) (hpm : ¬p ∣ m) :
    largeGapLocalMultiplicity H m q p = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm : (m : ZMod p) ≠ 0 := by
    exact fun hm => hpm ((ZMod.natCast_eq_zero_iff m p).mp hm)
  rw [largeGapLocalMultiplicity, largeGapLocalForbiddenResidues,
    largeGapFirstLocalResidues_eq_singleton_of_shifts hH hshift,
    largeGapCompanionLocalResidues_eq_singleton_of_shifts hp hH hshift hm]
  have hminv : (m : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hm
  rw [Finset.singleton_union]
  exact Finset.card_pair hminv.symm

theorem preSievedShifts_nonempty {K w : ℕ} (hK : 0 < K) :
    (preSievedShifts K w).Nonempty := by
  refine ⟨0, ?_⟩
  unfold preSievedShifts
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr hK, by simp⟩

theorem largeGapLocalMultiplicity_preSievedShifts
    {K w m q p : ℕ} (hK : 0 < K) (hp : p.Prime) (hpw : p ≤ w) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p =
      if p ∣ m then 1 else 2 := by
  have hshift : ∀ h ∈ preSievedShifts K w, p ∣ h := by
    intro h hh
    exact prime_dvd_shift_of_mem_preSievedShifts hh hp hpw
  by_cases hpm : p ∣ m
  · rw [if_pos hpm]
    exact largeGapLocalMultiplicity_eq_one_of_shifts_of_dvd
      (preSievedShifts_nonempty hK) hshift hpm
  · rw [if_neg hpm]
    exact largeGapLocalMultiplicity_eq_two_of_shifts_of_not_dvd hp
      (preSievedShifts_nonempty hK) hshift hpm

theorem largeGapLocalMultiplicity_le_two_of_shifts
    {H : Finset ℕ} {m q p : ℕ} (hshift : ∀ h ∈ H, p ∣ h) :
    largeGapLocalMultiplicity H m q p ≤ 2 := by
  unfold largeGapLocalMultiplicity largeGapLocalForbiddenResidues
  have hsubset :
      largeGapFirstLocalResidues H q p ∪
          largeGapCompanionLocalResidues H m q p ⊆
        ({0} : Finset (ZMod p)) ∪ {(m : ZMod p)⁻¹} :=
    Finset.union_subset_union
      (largeGapFirstLocalResidues_subset_zero_of_shifts hshift)
      (largeGapCompanionLocalResidues_subset_singleton_of_shifts hshift)
  calc
    (largeGapFirstLocalResidues H q p ∪
        largeGapCompanionLocalResidues H m q p).card ≤
        (({0} : Finset (ZMod p)) ∪ {(m : ZMod p)⁻¹}).card :=
      Finset.card_le_card hsubset
    _ ≤ ({0} : Finset (ZMod p)).card +
        ({(m : ZMod p)⁻¹} : Finset (ZMod p)).card := Finset.card_union_le _ _
    _ = 2 := by simp

theorem largeGapLocalMultiplicity_le_one_of_shifts_of_dvd
    {H : Finset ℕ} {m q p : ℕ} (hshift : ∀ h ∈ H, p ∣ h)
    (hpm : p ∣ m) :
    largeGapLocalMultiplicity H m q p ≤ 1 := by
  rw [largeGapLocalMultiplicity, largeGapLocalForbiddenResidues,
    largeGapCompanionLocalResidues_eq_empty_of_dvd hpm, Finset.union_empty]
  exact (Finset.card_le_card
    (largeGapFirstLocalResidues_subset_zero_of_shifts hshift)).trans_eq (by simp)

/-- The normalized local Euler factor used by the large-gap singular
series. -/
noncomputable def largeGapLocalFactor
    (H : Finset ℕ) (m q p : ℕ) : ℝ :=
  (1 - (largeGapLocalMultiplicity H m q p : ℝ) / p) *
    (1 - (1 : ℝ) / p)⁻¹ ^ (2 * H.card)

/-- The local factor when all `2K` forbidden residues are distinct. -/
noncomputable def genericLargeGapLocalFactor (K p : ℕ) : ℝ :=
  (1 - (2 * K : ℕ) / (p : ℝ)) *
    (1 - (1 : ℝ) / p)⁻¹ ^ (2 * K)

/-- Multiplicative increase of the actual local factor over its generic
`2K`-distinct-residue value. -/
noncomputable def largeGapLocalAmplification
    (H : Finset ℕ) (m q p : ℕ) : ℝ :=
  ((p : ℝ) - largeGapLocalMultiplicity H m q p) /
    ((p : ℝ) - 2 * H.card)

/-- The loss in the inverse singular factor caused by a local collision.
It is zero at a generic prime and lies in `[0,1)` whenever `2 * |H| < p`.
Writing the inverse factor as `1 - loss` is the finite Euler-product
expansion used in the pinned prime average. -/
noncomputable def largeGapLocalPenalty
    (H : Finset ℕ) (m q p : ℕ) : ℝ :=
  ((2 * H.card : ℕ) - largeGapLocalMultiplicity H m q p) /
    ((p : ℝ) - largeGapLocalMultiplicity H m q p)

theorem largeGapLocalFactor_eq_generic_mul_amplification
    {H : Finset ℕ} {m q p : ℕ} (hp0 : 0 < p)
    (hcard : H.card = K) (hKp : 2 * K < p) :
    largeGapLocalFactor H m q p =
      genericLargeGapLocalFactor K p *
        largeGapLocalAmplification H m q p := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hden : (p : ℝ) - 2 * K ≠ 0 := by
    have : (2 * K : ℝ) < p := by exact_mod_cast hKp
    linarith
  unfold largeGapLocalFactor genericLargeGapLocalFactor
    largeGapLocalAmplification
  rw [hcard]
  have hbase :
      1 - (largeGapLocalMultiplicity H m q p : ℝ) / p =
        (1 - (2 * K : ℕ) / (p : ℝ)) *
          (((p : ℝ) - largeGapLocalMultiplicity H m q p) /
            ((p : ℝ) - 2 * K)) := by
    field_simp
    push_cast
    ring
  rw [hbase]
  ring

theorem one_le_largeGapLocalAmplification
    {H : Finset ℕ} {m q p : ℕ}
    (hKp : 2 * H.card < p) :
    1 ≤ largeGapLocalAmplification H m q p := by
  have hden : (0 : ℝ) < (p : ℝ) - 2 * H.card := by
    exact sub_pos.mpr (by exact_mod_cast hKp)
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have homegaR :
      (largeGapLocalMultiplicity H m q p : ℝ) ≤ 2 * H.card := by
    exact_mod_cast homega
  unfold largeGapLocalAmplification
  rw [le_div_iff₀ hden]
  linarith

theorem largeGapLocalAmplification_inv_eq_one_sub_penalty
    {H : Finset ℕ} {m q p : ℕ}
    (hKp : 2 * H.card < p) :
    (largeGapLocalAmplification H m q p)⁻¹ =
      1 - largeGapLocalPenalty H m q p := by
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have hnum :
      (p : ℝ) - largeGapLocalMultiplicity H m q p ≠ 0 := by
    have homegaP : largeGapLocalMultiplicity H m q p < p :=
      homega.trans_lt hKp
    have : (largeGapLocalMultiplicity H m q p : ℝ) < p := by
      exact_mod_cast homegaP
    linarith
  have hden : (p : ℝ) - 2 * H.card ≠ 0 := by
    have : (2 * H.card : ℝ) < p := by exact_mod_cast hKp
    linarith
  unfold largeGapLocalAmplification largeGapLocalPenalty
  field_simp
  push_cast
  ring

theorem largeGapLocalPenalty_nonneg
    (H : Finset ℕ) (m q p : ℕ) (hKp : 2 * H.card < p) :
    0 ≤ largeGapLocalPenalty H m q p := by
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have homegaP : largeGapLocalMultiplicity H m q p < p :=
    homega.trans_lt hKp
  have hden :
      (0 : ℝ) < (p : ℝ) - largeGapLocalMultiplicity H m q p := by
    exact sub_pos.mpr (by exact_mod_cast homegaP)
  unfold largeGapLocalPenalty
  exact div_nonneg
    (sub_nonneg.mpr (by exact_mod_cast homega)) hden.le

theorem largeGapLocalPenalty_lt_one
    (H : Finset ℕ) (m q p : ℕ) (hKp : 2 * H.card < p) :
    largeGapLocalPenalty H m q p < 1 := by
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have homegaP : largeGapLocalMultiplicity H m q p < p :=
    homega.trans_lt hKp
  have hden :
      (0 : ℝ) < (p : ℝ) - largeGapLocalMultiplicity H m q p := by
    exact sub_pos.mpr (by exact_mod_cast homegaP)
  unfold largeGapLocalPenalty
  rw [div_lt_one hden]
  have hKpR : ((2 * H.card : ℕ) : ℝ) < p := by exact_mod_cast hKp
  exact sub_lt_sub_right hKpR _

theorem largeGapLocalPenalty_eq_zero_iff
    (H : Finset ℕ) (m q p : ℕ) (hKp : 2 * H.card < p) :
    largeGapLocalPenalty H m q p = 0 ↔
      largeGapLocalMultiplicity H m q p = 2 * H.card := by
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have homegaP : largeGapLocalMultiplicity H m q p < p :=
    homega.trans_lt hKp
  have hden :
      (p : ℝ) - largeGapLocalMultiplicity H m q p ≠ 0 := by
    have : (largeGapLocalMultiplicity H m q p : ℝ) < p := by
      exact_mod_cast homegaP
    linarith
  unfold largeGapLocalPenalty
  rw [div_eq_zero_iff]
  simp only [hden, or_false, sub_eq_zero]
  constructor <;> intro h <;> exact_mod_cast h.symm

/-- First Bonferroni inequality for a finite product.  This elementary
form is convenient for lower-bounding a truncated inverse singular
series after the local inverse factors have been written as `1 - loss`. -/
theorem one_sub_sum_le_prod_one_sub
    {I : Type*} [DecidableEq I] (S : Finset I) (f : I → ℝ)
    (hf0 : ∀ i ∈ S, 0 ≤ f i) (hf1 : ∀ i ∈ S, f i ≤ 1) :
    1 - ∑ i ∈ S, f i ≤ ∏ i ∈ S, (1 - f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have ha0 := hf0 a (by simp)
      have ha1 := hf1 a (by simp)
      have hS0 : ∀ i ∈ S, 0 ≤ f i := by
        intro i hi
        exact hf0 i (by simp [hi])
      have hS1 : ∀ i ∈ S, f i ≤ 1 := by
        intro i hi
        exact hf1 i (by simp [hi])
      have hsum0 : 0 ≤ ∑ i ∈ S, f i :=
        Finset.sum_nonneg fun i hi ↦ hS0 i hi
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hmul :
          (1 - f a) * (1 - ∑ i ∈ S, f i) ≤
            (1 - f a) * ∏ i ∈ S, (1 - f i) := by
        apply mul_le_mul_of_nonneg_left (ih hS0 hS1)
        linarith
      calc
        1 - (f a + ∑ i ∈ S, f i) ≤
            (1 - f a) * (1 - ∑ i ∈ S, f i) := by
              nlinarith
        _ ≤ (1 - f a) * ∏ i ∈ S, (1 - f i) := hmul

theorem one_sub_sum_largeGapLocalPenalty_le_prod_amplification_inv
    {H : Finset ℕ} {m q : ℕ} (S : Finset ℕ)
    (hlarge : ∀ p ∈ S, 2 * H.card < p) :
    1 - ∑ p ∈ S, largeGapLocalPenalty H m q p ≤
      ∏ p ∈ S, (largeGapLocalAmplification H m q p)⁻¹ := by
  calc
    1 - ∑ p ∈ S, largeGapLocalPenalty H m q p ≤
        ∏ p ∈ S, (1 - largeGapLocalPenalty H m q p) := by
      exact one_sub_sum_le_prod_one_sub S
        (fun p ↦ largeGapLocalPenalty H m q p)
        (fun p hp ↦ largeGapLocalPenalty_nonneg H m q p (hlarge p hp))
        (fun p hp ↦ (largeGapLocalPenalty_lt_one H m q p
          (hlarge p hp)).le)
    _ = ∏ p ∈ S, (largeGapLocalAmplification H m q p)⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (largeGapLocalAmplification_inv_eq_one_sub_penalty
        (hlarge p hp)).symm

/-- Exact squarefree-subset expansion of the inverse local amplification
product.  The subset of primes is the scalar analogue of Maynard's family
of pairwise-coprime auxiliary `a_{i,j}` variables. -/
theorem prod_largeGapLocalAmplification_inv_eq_powerset_sum
    {H : Finset ℕ} {m q : ℕ} (S : Finset ℕ)
    (hlarge : ∀ p ∈ S, 2 * H.card < p) :
    ∏ p ∈ S, (largeGapLocalAmplification H m q p)⁻¹ =
      ∑ T ∈ S.powerset,
        (-1 : ℝ) ^ T.card *
          ∏ p ∈ T, largeGapLocalPenalty H m q p := by
  calc
    ∏ p ∈ S, (largeGapLocalAmplification H m q p)⁻¹ =
        ∏ p ∈ S, (1 - largeGapLocalPenalty H m q p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact largeGapLocalAmplification_inv_eq_one_sub_penalty (hlarge p hp)
    _ = ∑ T ∈ S.powerset,
        (-1 : ℝ) ^ T.card *
          ∏ p ∈ T, largeGapLocalPenalty H m q p := by
      simpa using
        (Finset.prod_sub (fun _p : ℕ ↦ (1 : ℝ))
          (fun p ↦ largeGapLocalPenalty H m q p) S)

/-- A nonzero inverse-factor loss at a rough prime is supported on one of
the three arithmetically exceptional loci: the auxiliary prime, the
residual cofactor, or an affine first/companion collision. -/
theorem prime_dvd_q_or_m_or_crossExceptional_of_localPenalty_ne_zero
    {K w m q p : ℕ} (hp : p.Prime) (hKw : 2 * K ≤ w) (hwp : w < p)
    (hloss : largeGapLocalPenalty (preSievedShifts K w) m q p ≠ 0) :
    p ∣ q ∨ p ∣ m ∨
      p ∣ crossExceptionalModulus (preSievedShifts K w) m q := by
  by_contra hnot
  push Not at hnot
  have hKle : K ≤ w := by omega
  have hKp : 2 * (preSievedShifts K w).card < p := by
    rw [card_preSievedShifts]
    omega
  apply hloss
  rw [largeGapLocalPenalty_eq_zero_iff
      (preSievedShifts K w) m q p hKp,
    card_preSievedShifts]
  exact largeGapLocalMultiplicity_eq_generic_of_not_exceptional
    hp hKle hwp hnot.1 hnot.2.1 hnot.2.2

theorem largeGapLocalFactor_eq_generic_of_not_exceptional
    {K w m q p : ℕ} (hp : p.Prime) (hKw : K ≤ w) (hwp : w < p)
    (hpq : ¬p ∣ q) (hpm : ¬p ∣ m)
    (hpex : ¬p ∣ crossExceptionalModulus (preSievedShifts K w) m q) :
    largeGapLocalFactor (preSievedShifts K w) m q p =
      genericLargeGapLocalFactor K p := by
  rw [largeGapLocalFactor, genericLargeGapLocalFactor,
    largeGapLocalMultiplicity_eq_generic_of_not_exceptional
      hp hKw hwp hpq hpm hpex,
    card_preSievedShifts]

theorem largeGapLocalFactor_pos
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime)
    (homega : largeGapLocalMultiplicity H m q p < p) :
    0 < largeGapLocalFactor H m q p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have homegaR : (largeGapLocalMultiplicity H m q p : ℝ) < p := by
    exact_mod_cast homega
  unfold largeGapLocalFactor
  have hfirst : 0 < 1 - (largeGapLocalMultiplicity H m q p : ℝ) / p := by
    rw [sub_pos, div_lt_one hpR]
    exact homegaR
  have hbase : 0 < 1 - (1 : ℝ) / p := by
    rw [sub_pos, div_lt_one hpR]
    exact hone
  positivity

/-- The truncated singular series. -/
noncomputable def largeGapSingularSeries
    (H : Finset ℕ) (m q y : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, largeGapLocalFactor H m q p

/-- At a prime within the pre-sieve cutoff, the local singular factor is
the exact doubled pre-sieve density times the usual dimension-`2K`
Mertens normalization. -/
theorem largeGapLocalFactor_preSievedShifts
    {K w m q p : ℕ} (hK : 0 < K) (hp : p.Prime) (hpw : p ≤ w) :
    largeGapLocalFactor (preSievedShifts K w) m q p =
      (if p ∣ m then ((p : ℝ) - 1) / p else ((p : ℝ) - 2) / p) *
        (1 - (1 : ℝ) / p)⁻¹ ^ (2 * K) := by
  rw [largeGapLocalFactor, largeGapLocalMultiplicity_preSievedShifts hK hp hpw,
    card_preSievedShifts]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hpm : p ∣ m
  · simp only [hpm, if_true, Nat.cast_one]
    congr 1
    field_simp
  · simp only [hpm, if_false, Nat.cast_ofNat]
    congr 1
    field_simp

/-- The small-prime portion of the singular series is therefore exactly
the finite pre-sieve density times the universal Mertens factor. -/
theorem largeGapSingularSeries_preSieveCutoff
    {K w m q : ℕ} (hK : 0 < K) :
    largeGapSingularSeries (preSievedShifts K w) m q w =
      preSieveDensity w m *
        ∏ p ∈ Nat.primesLE w,
          (1 - (1 : ℝ) / p)⁻¹ ^ (2 * K) := by
  unfold largeGapSingularSeries preSieveDensity
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpMem
  exact largeGapLocalFactor_preSievedShifts hK
    (Nat.mem_primesLE.mp hpMem).2 (Nat.mem_primesLE.mp hpMem).1

theorem largeGapSingularSeries_pos
    {H : Finset ℕ} {m q y : ℕ}
    (homega : ∀ p ∈ Nat.primesLE y,
      largeGapLocalMultiplicity H m q p < p) :
    0 < largeGapSingularSeries H m q y := by
  unfold largeGapSingularSeries
  apply Finset.prod_pos
  intro p hp
  exact largeGapLocalFactor_pos (Nat.mem_primesLE.mp hp).2 (homega p hp)

/-- For the cutoff-dependent shift tuple, the local obstruction never fills
all residue classes once the cutoff dominates twice the dimension and the
residual cofactor is even. -/
theorem largeGapLocalMultiplicity_lt_prime_preSievedShifts
    {K w m q p : ℕ} (hKw : 2 * K ≤ w) (hm : Even m)
    (hp : p.Prime) :
    largeGapLocalMultiplicity (preSievedShifts K w) m q p < p := by
  by_cases hpw : p ≤ w
  · have hshift : ∀ h ∈ preSievedShifts K w, p ∣ h := by
      intro h hh
      exact prime_dvd_shift_of_mem_preSievedShifts hh hp hpw
    rcases hp.eq_two_or_odd with rfl | hpOdd
    · exact (largeGapLocalMultiplicity_le_one_of_shifts_of_dvd hshift
        hm.two_dvd).trans_lt (by omega)
    · have hpTwo : 2 ≤ p := hp.two_le
      have hpNeTwo : p ≠ 2 := by
        intro hpEq
        subst p
        norm_num at hpOdd
      have hpThree : 3 ≤ p := by omega
      exact (largeGapLocalMultiplicity_le_two_of_shifts hshift).trans_lt
        (by omega)
  · have hwp : w < p := by omega
    calc
      largeGapLocalMultiplicity (preSievedShifts K w) m q p ≤
          2 * (preSievedShifts K w).card :=
        largeGapLocalMultiplicity_le_two_mul_card _ _ _ _
      _ = 2 * K := by rw [card_preSievedShifts]
      _ ≤ w := hKw
      _ < p := hwp

theorem largeGapSingularSeries_preSievedShifts_pos
    {K w m q y : ℕ} (hKw : 2 * K ≤ w) (hm : Even m) :
    0 < largeGapSingularSeries (preSievedShifts K w) m q y := by
  apply largeGapSingularSeries_pos
  intro p hp
  exact largeGapLocalMultiplicity_lt_prime_preSievedShifts hKw hm
    (Nat.mem_primesLE.mp hp).2

end

end Erdos4b
