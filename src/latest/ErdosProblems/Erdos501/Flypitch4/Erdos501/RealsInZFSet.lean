/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The real numbers as a complete ordered field inside Mathlib's `ZFSet`, and the direction
"`Erdos501_f` holds in the standard structure ⇒ DeepMind's proposition" of the bridge.
-/
import ErdosProblems.Erdos501.Flypitch4.Erdos501.StdSemantics

set_option relaxedAutoImplicit true

/-!
# `ℝ` inside `ZFSet`, and `StdSem.erdos501 → erdos501_deepmind`

We code a real `r` by the `ZFSet` `cutZ r` of (the codes of) the rationals below `r` (an injection
`ℝ → ZFSet`, `cutZ_injective`), and transport the ordered field structure of `ℝ`:
`Rz = {cutZ r | r ∈ ℝ}`, `plusZ`, `timesZ` (sets of triples), `ltZ` (a set of pairs), `zeroZ`,
`oneZ`.  These form a complete ordered field in the sense of `StdSem.completeOrderedField`
(`completeOrderedField_Rz`).

Given a family `A : ℝ → Set ℝ` of bounded sets of Lebesgue outer measure `< 1`, its copy
`famZ A : Rz → 𝒫(Rz)` satisfies the internal hypotheses of the Erdős property
(`bounded_setZ`, `outerMeasureLtOne_setZ`; the latter uses the covering lemma
`exists_cover_of_volume_lt`, extracted from the definition of the Lebesgue outer measure), and an
internal infinite independent set pulls back to an infinite independent `X ⊆ ℝ`
(`erdos501_deepmind_of_std`).
-/

open Fol Set MeasureTheory
open scoped ENNReal

namespace Flypitch.Erdos501

namespace RealsInZFSet

open StdSem

/-! ### The coding of reals -/

/-- The code of the real `r`: the set of the (codes of the) rationals `q < r`. -/
noncomputable def cutZ (r : ℝ) : ZFSet.{0} :=
  ZFSet.range (fun q : {q : ℚ // (q : ℝ) < r} => natZ (Encodable.encode q.1))

theorem natZ_encode_mem_cutZ_iff {q : ℚ} {r : ℝ} :
    natZ (Encodable.encode q) ∈ cutZ r ↔ (q : ℝ) < r := by
  rw [cutZ, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨q', hq'⟩, h⟩
    have h' := Encodable.encode_injective (natZ_injective h)
    subst h'
    exact hq'
  · intro h
    exact ⟨⟨q, h⟩, rfl⟩

theorem cutZ_injective : Function.Injective cutZ := by
  intro r r' h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have h1 : natZ (Encodable.encode q) ∈ cutZ r' := natZ_encode_mem_cutZ_iff.2 hq2
    rw [← h] at h1
    exact lt_asymm hq1 (natZ_encode_mem_cutZ_iff.1 h1)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have h1 : natZ (Encodable.encode q) ∈ cutZ r := natZ_encode_mem_cutZ_iff.2 hq2
    rw [h] at h1
    exact lt_asymm hq1 (natZ_encode_mem_cutZ_iff.1 h1)

@[simp] theorem cutZ_inj {r r' : ℝ} : cutZ r = cutZ r' ↔ r = r' := cutZ_injective.eq_iff

/-! ### The complete ordered field `Rz` -/

/-- The set of all codes of reals. -/
noncomputable def Rz : ZFSet.{0} := ZFSet.range cutZ

/-- Addition, as a set of triples `((x, y), x + y)`. -/
noncomputable def plusZ : ZFSet.{0} :=
  ZFSet.range fun p : ℝ × ℝ => ZFSet.pair (ZFSet.pair (cutZ p.1) (cutZ p.2)) (cutZ (p.1 + p.2))

/-- Multiplication, as a set of triples `((x, y), x · y)`. -/
noncomputable def timesZ : ZFSet.{0} :=
  ZFSet.range fun p : ℝ × ℝ => ZFSet.pair (ZFSet.pair (cutZ p.1) (cutZ p.2)) (cutZ (p.1 * p.2))

/-- The order, as a set of pairs `(x, y)` with `x < y`. -/
noncomputable def ltZ : ZFSet.{0} :=
  ZFSet.range fun p : {p : ℝ × ℝ // p.1 < p.2} => ZFSet.pair (cutZ p.1.1) (cutZ p.1.2)

/-- The code of `0`. -/
noncomputable def zeroZ : ZFSet.{0} := cutZ 0

/-- The code of `1`. -/
noncomputable def oneZ : ZFSet.{0} := cutZ 1

theorem mem_Rz {x : ZFSet.{0}} : x ∈ Rz ↔ ∃ r : ℝ, x = cutZ r := by
  rw [Rz, ZFSet.mem_range]
  exact ⟨fun ⟨r, h⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm⟩⟩

theorem cutZ_mem_Rz (r : ℝ) : cutZ r ∈ Rz := mem_Rz.2 ⟨r, rfl⟩

theorem app2_plusZ_iff {a b : ℝ} {z : ZFSet.{0}} :
    app2 plusZ (cutZ a) (cutZ b) z ↔ z = cutZ (a + b) := by
  rw [app2, plusZ, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨a', b'⟩, h⟩
    rw [ZFSet.pair_inj, ZFSet.pair_inj, cutZ_inj, cutZ_inj] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · rintro rfl
    exact ⟨(a, b), rfl⟩

theorem app2_timesZ_iff {a b : ℝ} {z : ZFSet.{0}} :
    app2 timesZ (cutZ a) (cutZ b) z ↔ z = cutZ (a * b) := by
  rw [app2, timesZ, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨a', b'⟩, h⟩
    rw [ZFSet.pair_inj, ZFSet.pair_inj, cutZ_inj, cutZ_inj] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · rintro rfl
    exact ⟨(a, b), rfl⟩

theorem lt_ltZ_iff {a b : ℝ} : lt ltZ (cutZ a) (cutZ b) ↔ a < b := by
  rw [lt, ltZ, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨a', b'⟩, hab⟩, h⟩
    rw [ZFSet.pair_inj, cutZ_inj, cutZ_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hab
  · intro h
    exact ⟨⟨(a, b), h⟩, rfl⟩

theorem le_ltZ_iff {a b : ℝ} : le ltZ (cutZ a) (cutZ b) ↔ a ≤ b := by
  rw [le, lt_ltZ_iff, cutZ_inj]
  exact le_iff_lt_or_eq.symm

theorem isOp2_plusZ : isOp2 Rz plusZ := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  exact ⟨cutZ (a + b), cutZ_mem_Rz _, app2_plusZ_iff.2 rfl, fun z' hz' => app2_plusZ_iff.1 hz'⟩

theorem isOp2_timesZ : isOp2 Rz timesZ := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  exact ⟨cutZ (a * b), cutZ_mem_Rz _, app2_timesZ_iff.2 rfl, fun z' hz' => app2_timesZ_iff.1 hz'⟩

theorem assoc_plusZ : assoc Rz plusZ := by
  intro x hx y hy z hz u v w w' hu hv hw hw'
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  obtain ⟨c, rfl⟩ := mem_Rz.1 hz
  rw [app2_plusZ_iff] at hu hw
  subst hu hw
  rw [app2_plusZ_iff] at hv hw'
  subst hv hw'
  rw [add_assoc]

theorem comm_plusZ : comm Rz plusZ := by
  intro x hx y hy u hu
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  rw [app2_plusZ_iff] at hu ⊢
  rw [hu, add_comm]

theorem ident_plusZ : ident Rz plusZ zeroZ := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  exact app2_plusZ_iff.2 (by rw [add_zero])

theorem addInv_plusZ : addInv Rz plusZ zeroZ := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  exact ⟨cutZ (-a), cutZ_mem_Rz _, app2_plusZ_iff.2 (by rw [zeroZ, add_neg_cancel])⟩

theorem assoc_timesZ : assoc Rz timesZ := by
  intro x hx y hy z hz u v w w' hu hv hw hw'
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  obtain ⟨c, rfl⟩ := mem_Rz.1 hz
  rw [app2_timesZ_iff] at hu hw
  subst hu hw
  rw [app2_timesZ_iff] at hv hw'
  subst hv hw'
  rw [mul_assoc]

theorem comm_timesZ : comm Rz timesZ := by
  intro x hx y hy u hu
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  rw [app2_timesZ_iff] at hu ⊢
  rw [hu, mul_comm]

theorem ident_timesZ : ident Rz timesZ oneZ := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  exact app2_timesZ_iff.2 (by rw [mul_one])

theorem mulInv_timesZ : mulInv Rz timesZ zeroZ oneZ := by
  intro x hx hne
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  have ha : a ≠ 0 := fun h => hne (by rw [h]; rfl)
  exact ⟨cutZ a⁻¹, cutZ_mem_Rz _, app2_timesZ_iff.2 (by rw [oneZ, mul_inv_cancel₀ ha])⟩

theorem zeroZ_ne_oneZ : ¬ zeroZ = oneZ := by
  rw [zeroZ, oneZ, cutZ_inj]
  exact zero_ne_one

theorem distrib_Z : distrib Rz plusZ timesZ := by
  intro x hx y hy z hz u v w t t' hu hv hw ht ht'
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  obtain ⟨c, rfl⟩ := mem_Rz.1 hz
  rw [app2_plusZ_iff] at hu
  subst hu
  rw [app2_timesZ_iff] at hv hw ht
  subst hv hw ht
  rw [app2_plusZ_iff] at ht'
  subst ht'
  rw [mul_add]

theorem irrefl_ltZ : irrefl Rz ltZ := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  rw [lt_ltZ_iff]
  exact lt_irrefl a

theorem trans_ltZ : trans Rz ltZ := by
  intro x hx y hy z hz
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  obtain ⟨c, rfl⟩ := mem_Rz.1 hz
  rw [lt_ltZ_iff, lt_ltZ_iff, lt_ltZ_iff]
  exact lt_trans

theorem total_ltZ : total Rz ltZ := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  rw [lt_ltZ_iff, lt_ltZ_iff, cutZ_inj]
  exact lt_trichotomy a b

theorem addCompat_Z : addCompat Rz plusZ ltZ := by
  intro x hx y hy z hz u v hxy hu hv
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  obtain ⟨c, rfl⟩ := mem_Rz.1 hz
  rw [app2_plusZ_iff] at hu hv
  subst hu hv
  rw [lt_ltZ_iff] at hxy ⊢
  exact add_lt_add_left hxy c

theorem mulPos_Z : mulPos Rz timesZ ltZ zeroZ := by
  intro x hx y hy u h0x h0y hu
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  obtain ⟨b, rfl⟩ := mem_Rz.1 hy
  rw [app2_timesZ_iff] at hu
  subst hu
  rw [zeroZ, lt_ltZ_iff] at h0x h0y ⊢
  exact mul_pos h0x h0y

theorem complete_Z : complete Rz ltZ := by
  intro S hS hne hbdd
  rw [ZFSet.mem_powerset] at hS
  -- the set of reals coded in `S`
  set T : Set ℝ := {a | cutZ a ∈ S} with hT
  have hTne : T.Nonempty := by
    have hex : ∃ x, x ∈ S := by
      by_contra h
      exact hne ((ZFSet.eq_empty S).2 fun y hy => h ⟨y, hy⟩)
    obtain ⟨x, hx⟩ := hex
    obtain ⟨a, rfl⟩ := mem_Rz.1 (hS hx)
    exact ⟨a, hx⟩
  have hTbdd : BddAbove T := by
    obtain ⟨b, hb, hbS⟩ := hbdd
    obtain ⟨β, rfl⟩ := mem_Rz.1 hb
    refine ⟨β, fun a ha => ?_⟩
    exact le_ltZ_iff.1 (hbS _ ha)
  refine ⟨cutZ (sSup T), cutZ_mem_Rz _, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, rfl⟩ := mem_Rz.1 (hS hs)
    exact le_ltZ_iff.2 (le_csSup hTbdd hs)
  · intro v hv hvS
    obtain ⟨β, rfl⟩ := mem_Rz.1 hv
    refine le_ltZ_iff.2 (csSup_le hTne fun a ha => ?_)
    exact le_ltZ_iff.1 (hvS _ ha)

/-- **`(Rz, plusZ, timesZ, ltZ, zeroZ, oneZ)` is a complete ordered field** in the sense of the
sentence `CompleteOrderedFieldF`, read in the standard structure. -/
theorem completeOrderedField_Rz : completeOrderedField Rz plusZ timesZ ltZ zeroZ oneZ :=
  ⟨isOp2_plusZ, isOp2_timesZ, cutZ_mem_Rz 0, cutZ_mem_Rz 1, assoc_plusZ, comm_plusZ, ident_plusZ,
    addInv_plusZ, assoc_timesZ, comm_timesZ, ident_timesZ, mulInv_timesZ, zeroZ_ne_oneZ, distrib_Z,
    irrefl_ltZ, trans_ltZ, total_ltZ, addCompat_Z, mulPos_Z, complete_Z⟩


/-! ### Subsets, families and sequences of reals as `ZFSet`s -/

/-- The set of codes of the elements of `s`. -/
noncomputable def setZ (s : Set ℝ) : ZFSet.{0} := ZFSet.range (fun x : s => cutZ x.1)

theorem mem_setZ {s : Set ℝ} {x : ZFSet.{0}} : x ∈ setZ s ↔ ∃ a ∈ s, x = cutZ a := by
  rw [setZ, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, h.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem cutZ_mem_setZ_iff {s : Set ℝ} {a : ℝ} : cutZ a ∈ setZ s ↔ a ∈ s := by
  rw [mem_setZ]
  constructor
  · rintro ⟨a', ha', h⟩
    rw [cutZ_inj] at h
    exact h ▸ ha'
  · intro h
    exact ⟨a, h, rfl⟩

theorem setZ_subset_Rz (s : Set ℝ) : setZ s ⊆ Rz := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := mem_setZ.1 hx
  exact cutZ_mem_Rz a

theorem setZ_mem_powerset (s : Set ℝ) : setZ s ∈ ZFSet.powerset Rz :=
  ZFSet.mem_powerset.2 (setZ_subset_Rz s)

/-- The copy of a family `A : ℝ → Set ℝ` as a function `Rz → 𝒫(Rz)` (a set of pairs). -/
noncomputable def famZ (A : ℝ → Set ℝ) : ZFSet.{0} :=
  ZFSet.range (fun a : ℝ => ZFSet.pair (cutZ a) (setZ (A a)))

theorem app_famZ_iff {A : ℝ → Set ℝ} {a : ℝ} {y : ZFSet.{0}} :
    app (famZ A) (cutZ a) y ↔ y = setZ (A a) := by
  rw [app, famZ, ZFSet.mem_range]
  constructor
  · rintro ⟨a', h⟩
    rw [ZFSet.pair_inj, cutZ_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rintro rfl
    exact ⟨a, rfl⟩

theorem isFun_famZ (A : ℝ → Set ℝ) : isFun Rz (ZFSet.powerset Rz) (famZ A) := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Rz.1 hx
  exact ⟨setZ (A a), setZ_mem_powerset _, app_famZ_iff.2 rfl, fun y' hy' => app_famZ_iff.1 hy'⟩

/-- The copy of a sequence `f : ℕ → ℝ` as a function `ω → Rz` (a set of pairs). -/
noncomputable def seqZ (f : ℕ → ℝ) : ZFSet.{0} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natZ n) (cutZ (f n)))

theorem app_seqZ_iff {f : ℕ → ℝ} {n : ℕ} {y : ZFSet.{0}} :
    app (seqZ f) (natZ n) y ↔ y = cutZ (f n) := by
  rw [app, seqZ, ZFSet.mem_range]
  constructor
  · rintro ⟨n', h⟩
    rw [ZFSet.pair_inj] at h
    obtain ⟨h1, rfl⟩ := h
    rw [natZ_injective h1]
  · rintro rfl
    exact ⟨n, rfl⟩

theorem isFun_seqZ (f : ℕ → ℝ) : isFun ZFSet.omega Rz (seqZ f) := by
  intro x hx
  obtain ⟨n, rfl⟩ := mem_omega_iff.1 hx
  exact ⟨cutZ (f n), cutZ_mem_Rz _, app_seqZ_iff.2 rfl, fun y' hy' => app_seqZ_iff.1 hy'⟩

/-! ### The internal hypotheses of the Erdős property for the copy of a family -/

theorem bounded_setZ {s : Set ℝ} (hs : Bornology.IsBounded s) : bounded Rz ltZ (setZ s) := by
  obtain ⟨⟨m, hm⟩, ⟨M, hM⟩⟩ := isBounded_iff_bddBelow_bddAbove.1 hs
  refine ⟨cutZ (m - 1), cutZ_mem_Rz _, cutZ (M + 1), cutZ_mem_Rz _, ?_⟩
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_setZ.1 hy
  exact ⟨lt_ltZ_iff.2 (by linarith [hm ha]), lt_ltZ_iff.2 (by linarith [hM ha])⟩

/-- The Lebesgue measure of a set of reals is the Stieltjes outer measure of the identity. -/
theorem volume_eq_outer (s : Set ℝ) : volume s = StieltjesFunction.id.outer s := by
  rw [Real.volume_val, StieltjesFunction.measure]
  rfl

theorem botSet_real : (botSet : Set ℝ) = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx => not_isBot x hx

/-- A set of finite `length` (in the sense of `StieltjesFunction.length` for the identity) is
contained in an interval `Ioc a b` of almost the same length. -/
theorem exists_Ioc_of_length_lt {t : Set ℝ} {c : ℝ≥0∞} (h : StieltjesFunction.id.length t < c) :
    ∃ a b : ℝ, a ≤ b ∧ t ⊆ Ioc a b ∧ ENNReal.ofReal (b - a) < c := by
  rw [StieltjesFunction.length_eq, botSet_real, diff_empty] at h
  simp only [iInf_lt_iff, StieltjesFunction.id_apply, id] at h
  obtain ⟨a, b, hab, hlt⟩ := h
  rcases le_or_gt a b with hle | hlt'
  · exact ⟨a, b, hle, hab, hlt⟩
  · refine ⟨a, a, le_rfl, ?_, ?_⟩
    · intro x hx
      exact absurd ((hab hx).1.trans_le (hab hx).2) (not_lt.2 hlt'.le)
    · rw [sub_self, ENNReal.ofReal_zero]
      exact lt_of_le_of_lt zero_le hlt

/-- **The covering lemma.**  A set of reals of Lebesgue outer measure `< 1` is covered by a
sequence of nondegenerate open intervals `(aₙ, bₙ)` all of whose partial sums of lengths are
`≤ r` for some `r < 1`. -/
theorem exists_cover_of_volume_lt_one {s : Set ℝ} (hs : volume s < 1) :
    ∃ (a b : ℕ → ℝ) (r : ℝ), (∀ n, a n < b n) ∧ (∀ y ∈ s, ∃ n, a n < y ∧ y < b n) ∧
      (∀ n, ∑ i ∈ Finset.range n, (b i - a i) ≤ r) ∧ r < 1 := by
  -- a countable cover by sets `t n` with `∑' n, length (t n) < 1`
  rw [volume_eq_outer, StieltjesFunction.outer, OuterMeasure.ofFunction_apply] at hs
  simp only [iInf_lt_iff] at hs
  obtain ⟨t, hts, hsum⟩ := hs
  set L : ℕ → ℝ≥0∞ := fun n => StieltjesFunction.id.length (t n) with hL
  have hsumtop : ∑' n, L n ≠ ∞ := hsum.ne_top
  have hLtop : ∀ n, L n ≠ ∞ := fun n => ne_top_of_le_ne_top hsumtop (ENNReal.le_tsum n)
  -- the slack
  obtain ⟨ε₀, hε₀, hε₀sum⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hsum
  set ε : ℝ := (ε₀ : ℝ) / 2 with hε
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- almost optimal intervals `Ioc (a n) (b n) ⊇ t n`
  have hchoice : ∀ n, ∃ a b : ℝ, a ≤ b ∧ t n ⊆ Ioc a b ∧
      ENNReal.ofReal (b - a) < L n + ENNReal.ofReal (ε / 2 ^ (n + 2)) := fun n =>
    exists_Ioc_of_length_lt (ENNReal.lt_add_right (hLtop n)
      (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity))
  choose a b hab hts' hlen using hchoice
  have hδ : ∀ n : ℕ, (0 : ℝ) < ε / 2 ^ (n + 2) := fun n => by positivity
  have hreal : ∀ i, b i - a i ≤ (L i).toReal + ε / 2 ^ (i + 2) := by
    intro i
    have h1 := hlen i
    rw [ENNReal.ofReal_lt_iff_lt_toReal (sub_nonneg.2 (hab i))
        (ENNReal.add_ne_top.2 ⟨hLtop i, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add (hLtop i) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hδ i).le] at h1
    exact h1.le
  refine ⟨fun n => a n - ε / 2 ^ (n + 2), fun n => b n + ε / 2 ^ (n + 2),
    (∑' n, L n).toReal + 2 * ε, ?_, ?_, ?_, ?_⟩
  · intro n
    have := hab n
    have := hδ n
    linarith
  · intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hts hy)
    have h1 := hts' n hn
    have := hδ n
    exact ⟨n, by linarith [h1.1], by linarith [h1.2]⟩
  · intro n
    have hgeom : ∀ i : ℕ, 3 * (ε / 2 ^ (i + 2)) = (3 * ε / 4) * (1 / 2 : ℝ) ^ i := by
      intro i
      rw [one_div_pow, pow_add]
      field_simp
      norm_num
    calc ∑ i ∈ Finset.range n, ((b i + ε / 2 ^ (i + 2)) - (a i - ε / 2 ^ (i + 2)))
        = ∑ i ∈ Finset.range n, ((b i - a i) + 2 * (ε / 2 ^ (i + 2))) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range n, ((L i).toReal + 3 * (ε / 2 ^ (i + 2))) :=
          Finset.sum_le_sum fun i _ => by linarith [hreal i, hδ i]
      _ = ∑ i ∈ Finset.range n, (L i).toReal +
            (3 * ε / 4) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => hgeom i
      _ ≤ (∑' n, L n).toReal + (3 * ε / 4) * 2 := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left (sum_geometric_two_le n)
            (by positivity))
          rw [← ENNReal.toReal_sum (fun i _ => hLtop i)]
          exact ENNReal.toReal_mono hsumtop (ENNReal.sum_le_tsum _)
      _ ≤ (∑' n, L n).toReal + 2 * ε := by linarith
  · have h1 : (∑' n, L n + ε₀ : ℝ≥0∞).toReal < (1 : ℝ≥0∞).toReal :=
      ENNReal.toReal_strict_mono ENNReal.one_ne_top hε₀sum
    rw [ENNReal.toReal_add hsumtop ENNReal.coe_ne_top, ENNReal.toReal_one,
      ENNReal.coe_toReal] at h1
    rw [hε]
    linarith

theorem outerMeasureLtOne_setZ {s : Set ℝ} (hs : volume s < 1) :
    outerMeasureLtOne Rz plusZ ltZ zeroZ oneZ (setZ s) := by
  obtain ⟨a, b, r, hab, hcov, hsum, hr⟩ := exists_cover_of_volume_lt_one hs
  set p : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, (b i - a i) with hp
  refine ⟨seqZ a, seqZ b, seqZ p, isFun_seqZ a, isFun_seqZ b, isFun_seqZ p, ?_, ?_, ?_, ?_, ?_⟩
  · -- nondegenerate
    intro n hn u v hu hv
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    rw [app_seqZ_iff] at hu hv
    subst hu hv
    exact lt_ltZ_iff.2 (hab k)
  · -- covers
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_setZ.1 hy
    obtain ⟨k, hk1, hk2⟩ := hcov x hx
    exact ⟨natZ k, natZ_mem_omega k, cutZ (a k), cutZ (b k), app_seqZ_iff.2 rfl,
      app_seqZ_iff.2 rfl, lt_ltZ_iff.2 hk1, lt_ltZ_iff.2 hk2⟩
  · -- s 0 = 0
    show app (seqZ p) (natZ 0) zeroZ
    exact app_seqZ_iff.2 (by simp [hp, zeroZ])
  · -- the partial sums recursion
    intro n hn m hnm u v w w' t t' hu hv hw hw' ht ht'
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    have hm := natZ_eq_of_succ hnm
    subst hm
    rw [app_seqZ_iff] at hu hv hw hw'
    subst hu hv hw hw'
    rw [app2_plusZ_iff] at ht ht'
    subst ht ht'
    congr 1
    simp only [hp, Finset.sum_range_succ]
    ring
  · -- the partial sums are bounded by `r < 1`
    refine ⟨cutZ r, cutZ_mem_Rz _, lt_ltZ_iff.2 hr, ?_⟩
    intro n hn w hw
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    rw [app_seqZ_iff] at hw
    subst hw
    exact le_ltZ_iff.2 (hsum k)

/-! ### Pulling back an infinite independent set -/

theorem infinite_of_infinite_Z {X : ZFSet.{0}} (hX : X ⊆ Rz) (h : infinite X) :
    {a : ℝ | cutZ a ∈ X}.Infinite := by
  obtain ⟨f, hf, hinj⟩ := h
  have hval : ∀ n : ℕ, ∃ a : ℝ, fval f (natZ n) = cutZ a := fun n =>
    mem_Rz.1 (hX (fval_mem hf (natZ_mem_omega n)))
  choose g hg using hval
  apply Set.infinite_of_injective_forall_mem (f := g)
  · intro n m hnm
    have h1 : fval f (natZ n) = fval f (natZ m) := by rw [hg, hg, hnm]
    have h2 : app f (natZ n) (fval f (natZ n)) := app_fval hf (natZ_mem_omega n)
    have h3 : app f (natZ m) (fval f (natZ n)) := h1 ▸ app_fval hf (natZ_mem_omega m)
    exact natZ_injective (hinj _ (natZ_mem_omega n) _ (natZ_mem_omega m) _ h2 h3)
  · intro n
    show cutZ (g n) ∈ X
    rw [← hg]
    exact fval_mem hf (natZ_mem_omega n)

/-- **`Erdos501_f` in the standard structure implies DeepMind's proposition.** -/
theorem erdos501_deepmind_of_std (H : StdSem.erdos501) : erdos501_deepmind := by
  intro A hb hm
  have hE := H Rz plusZ timesZ ltZ zeroZ oneZ completeOrderedField_Rz
  obtain ⟨X, hXP, hXinf, hXind⟩ := hE (famZ A) (isFun_famZ A) (by
    intro x hx Ax hAx
    obtain ⟨a, rfl⟩ := mem_Rz.1 hx
    rw [app_famZ_iff] at hAx
    subst hAx
    exact ⟨bounded_setZ (hb a), outerMeasureLtOne_setZ (hm a)⟩)
  rw [ZFSet.mem_powerset] at hXP
  refine ⟨{a | cutZ a ∈ X}, infinite_of_infinite_Z hXP hXinf, ?_⟩
  intro x hx y hy hxy hxA
  have hne : ¬ cutZ x = cutZ y := fun h => hxy (cutZ_injective h)
  exact hXind _ hx _ hy hne _ (app_famZ_iff.2 rfl) (cutZ_mem_setZ_iff.2 hxA)

end RealsInZFSet

end Flypitch.Erdos501
