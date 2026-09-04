import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# An allowed nonsquare for the local construction in Erdős Problem 29

For an odd prime `p` we search the canonical representatives `0, …, p - 1`.
The predicate used by the search is a genuinely finite computation: a residue is
declared square precisely when it occurs among the `p` explicitly enumerated
squares.  For `p ≥ 11`, four distinct square multiples of any nonsquare show
that at least one nonsquare avoids the three exceptional values needed below.
-/

namespace Erdos29

/-- The natural representatives of all squares modulo `p`. -/
def squareResidues (p : ℕ) : Finset ℕ :=
  (Finset.range p).image fun x ↦ x * x % p

/-- The finite collection searched for the distinguished nonsquare. -/
def allowedCandidates (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun n ↦
    n ∉ squareResidues p ∧
      (n : ZMod p) ≠ -1 ∧
      (n : ZMod p) ≠ -3 ∧
      (n : ZMod p) ≠ -((3 : ZMod p)⁻¹)

/-- A bounded, executable search for the first allowed nonsquare, with a harmless
default value in the parameter ranges where no candidate exists. -/
def allowedT (p : ℕ) : ℕ :=
  (allowedCandidates p).min.untopD 0

lemma mem_squareResidues_iff_isSquare {p n : ℕ} (hp : 0 < p) (hn : n < p) :
    n ∈ squareResidues p ↔ IsSquare (n : ZMod p) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  constructor
  · intro h
    rw [isSquare_iff_exists_mul_self]
    simp only [squareResidues, Finset.mem_image] at h
    obtain ⟨x, hx, hxn⟩ := h
    have hxp : x < p := Finset.mem_range.mp hx
    refine ⟨(x : ZMod p), ?_⟩
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt hn, ZMod.val_mul, ZMod.val_natCast_of_lt hxp]
    exact hxn.symm
  · intro h
    rw [isSquare_iff_exists_mul_self] at h
    obtain ⟨x, hx⟩ := h
    simp only [squareResidues, Finset.mem_image]
    refine ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
    have hv := congrArg ZMod.val hx
    rw [ZMod.val_natCast_of_lt hn, ZMod.val_mul] at hv
    exact hv.symm

private lemma exists_allowed_residue {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ∃ t : ZMod p,
      ¬ IsSquare t ∧ t ≠ -1 ∧ t ≠ -3 ∧ t ≠ -((3 : ZMod p)⁻¹) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by omega) hp11
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  obtain ⟨q, hq⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hq0 : q ≠ 0 := by
    intro h
    apply hq
    rw [h]
    exact IsSquare.zero
  have hqChar : quadraticChar (ZMod p) q = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hq
  let S : Finset (ZMod p) :=
    (Finset.Icc 1 4 : Finset ℕ).image fun r : ℕ ↦ (r : ZMod p) ^ 2 * q
  have hInjective : Set.InjOn (fun r : ℕ ↦ (r : ZMod p) ^ 2 * q)
      (Finset.Icc 1 4 : Finset ℕ) := by
    intro r hr s hs hrs
    simp only [Finset.coe_Icc, Set.mem_Icc] at hr hs
    have hrp : r < p := by omega
    have hsp : s < p := by omega
    have hsquares : (r : ZMod p) ^ 2 = (s : ZMod p) ^ 2 :=
      mul_right_cancel₀ hq0 hrs
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with heq | hneg
    · have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast_of_lt hrp, ZMod.val_natCast_of_lt hsp] using hv
    · exfalso
      have hzero : ((r + s : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, hneg]
        simp
      have hdvd : p ∣ r + s := (CharP.cast_eq_zero_iff (ZMod p) p (r + s)).mp hzero
      exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hcardS : S.card = 4 := by
    rw [show S = (Finset.Icc 1 4 : Finset ℕ).image
        (fun r : ℕ ↦ (r : ZMod p) ^ 2 * q) from rfl]
    rw [Finset.card_image_iff.mpr hInjective, Nat.card_Icc]
  have hS_nonsquare : ∀ x ∈ S, ¬ IsSquare x := by
    intro x hx
    simp only [S, Finset.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrBounds := Finset.mem_Icc.mp hr
    have hrp : r < p := by omega
    have hr0 : (r : ZMod p) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast_of_lt hrp, ZMod.val_zero] at hv
      omega
    apply quadraticChar_neg_one_iff_not_isSquare.mp
    rw [map_mul, quadraticChar_sq_one' hr0, hqChar, one_mul]
  let F : Finset (ZMod p) := {-1, -3, -((3 : ZMod p)⁻¹)}
  have hcardF : F.card ≤ 3 := by
    have h1 := Finset.card_insert_le (-1 : ZMod p) {-3, -((3 : ZMod p)⁻¹)}
    have h2 := Finset.card_insert_le (-3 : ZMod p) {-((3 : ZMod p)⁻¹)}
    simpa [F] using h1.trans (Nat.add_le_add_right h2 1)
  have hnsub : ¬ S ⊆ F := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨t, htS, htF⟩ := Finset.not_subset.mp hnsub
  have htAvoid : t ≠ -1 ∧ t ≠ -3 ∧ t ≠ -((3 : ZMod p)⁻¹) := by
    simpa [F] using htF
  exact ⟨t, hS_nonsquare t htS, htAvoid⟩

private lemma allowedCandidates_nonempty {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedCandidates p).Nonempty := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := lt_of_lt_of_le (by omega) hp11
  obtain ⟨t, htSquare, ht1, ht3, htInv3⟩ := exists_allowed_residue hp hp11
  refine ⟨t.val, ?_⟩
  simp only [allowedCandidates, Finset.mem_filter, Finset.mem_range]
  have htlt : t.val < p := ZMod.val_lt t
  refine ⟨htlt, ?_, ?_, ?_, ?_⟩
  · intro h
    apply htSquare
    simpa only [ZMod.natCast_zmod_val] using
      (mem_squareResidues_iff_isSquare hp0 htlt).mp h
  · simpa only [ZMod.natCast_zmod_val] using ht1
  · simpa only [ZMod.natCast_zmod_val] using ht3
  · simpa only [ZMod.natCast_zmod_val] using htInv3

lemma allowedT_mem_candidates {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    allowedT p ∈ allowedCandidates p := by
  have hne := allowedCandidates_nonempty hp hp11
  obtain ⟨a, ha⟩ := Finset.min_of_nonempty hne
  have hvalue : allowedT p = a := by
    simp only [allowedT, ha, WithTop.untopD_coe]
  rw [hvalue]
  exact Finset.mem_of_min ha

theorem allowedT_spec {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    allowedT p < p ∧
      ¬ IsSquare (allowedT p : ZMod p) ∧
      (allowedT p : ZMod p) ≠ -1 ∧
      (allowedT p : ZMod p) ≠ -3 ∧
      (allowedT p : ZMod p) ≠ -((3 : ZMod p)⁻¹) := by
  have hp0 : 0 < p := hp.pos
  have hm := allowedT_mem_candidates hp hp11
  simp only [allowedCandidates, Finset.mem_filter, Finset.mem_range] at hm
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
  exact fun hs ↦ hm.2.1 ((mem_squareResidues_iff_isSquare hp0 hm.1).mpr hs)

theorem allowedT_not_isSquare {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ IsSquare (allowedT p : ZMod p) :=
  (allowedT_spec hp hp11).2.1

theorem allowedT_ne_neg_one {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -1 :=
  (allowedT_spec hp hp11).2.2.1

theorem allowedT_ne_neg_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -3 :=
  (allowedT_spec hp hp11).2.2.2.1

theorem allowedT_ne_neg_inv_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ -((3 : ZMod p)⁻¹) :=
  (allowedT_spec hp hp11).2.2.2.2

/-- The three parabola coefficients attached to the allowed nonsquare. -/
def parabolaCoefficients (p : ℕ) : Finset (ZMod p) :=
  let t : ZMod p := allowedT p
  {2, 1 + t, 1 + t⁻¹}

private lemma allowedT_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p) ≠ 0 := by
  intro h
  apply allowedT_not_isSquare hp hp11
  rw [h]
  exact IsSquare.zero

private lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma four_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (4 : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  intro h
  have hdvd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

private lemma allowedT_inv_ne_neg_one {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p)⁻¹ ≠ -1 := by
  let : Fact p.Prime := ⟨hp⟩
  intro h
  apply allowedT_ne_neg_one hp hp11
  have hi := congrArg Inv.inv h
  simpa only [inv_inv, inv_neg, inv_one] using hi

private lemma allowedT_inv_ne_neg_three {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    (allowedT p : ZMod p)⁻¹ ≠ -3 := by
  let : Fact p.Prime := ⟨hp⟩
  intro h
  apply allowedT_ne_neg_inv_three hp hp11
  have hi := congrArg Inv.inv h
  simpa only [inv_inv, inv_neg] using hi

/-- Every ordered sum of two selected parabola coefficients is nonzero. -/
theorem parabolaCoefficients_add_ne_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {c d : ZMod p} (hc : c ∈ parabolaCoefficients p) (hd : d ∈ parabolaCoefficients p) :
    c + d ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let t : ZMod p := allowedT p
  have ht0 : t ≠ 0 := allowedT_ne_zero hp hp11
  have ht1 : t ≠ -1 := allowedT_ne_neg_one hp hp11
  have ht3 : t ≠ -3 := allowedT_ne_neg_three hp hp11
  have hti1 : t⁻¹ ≠ -1 := allowedT_inv_ne_neg_one hp hp11
  have hti3 : t⁻¹ ≠ -3 := allowedT_inv_ne_neg_three hp hp11
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero hp hp11
  have h4 : (4 : ZMod p) ≠ 0 := four_ne_zero hp hp11
  have hdouble (z : ZMod p) (hz : z ≠ -1) : (1 + z) + (1 + z) ≠ 0 := by
    intro h
    have hf : (2 : ZMod p) * (1 + z) = 0 := by
      calc
        (2 : ZMod p) * (1 + z) = (1 + z) + (1 + z) := by ring
        _ = 0 := h
    have := (mul_eq_zero.mp hf).resolve_left h2
    apply hz
    linear_combination this
  have hcross : (1 + t) + (1 + t⁻¹) ≠ 0 := by
    intro h
    have hsquare : (t + 1) ^ 2 = 0 := by
      calc
        (t + 1) ^ 2 = t * ((1 + t) + (1 + t⁻¹)) := by
          field_simp [ht0]
          <;> ring
        _ = 0 := by rw [h, mul_zero]
    have hz : t + 1 = 0 := (sq_eq_zero_iff).mp hsquare
    exact ht1 (eq_neg_of_add_eq_zero_left hz)
  simp only [parabolaCoefficients, Finset.mem_insert, Finset.mem_singleton] at hc hd
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl
  · convert h4 using 1 <;> ring
  · intro h; apply ht3; linear_combination h
  · intro h; apply hti3; linear_combination h
  · intro h; apply ht3; linear_combination h
  · exact hdouble t ht1
  · exact hcross
  · intro h; apply hti3; linear_combination h
  · simpa [add_comm] using hcross
  · exact hdouble t⁻¹ hti1

end Erdos29
