/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib
import ErdosProblems.Erdos1027.FiniteExpect

/-!
# A finite priority space for the DGK recolouring argument

The continuous presentation of the Duraj--Gutowski--Kozik argument gives every
vertex an independent fair initial colour and an independent uniform priority
in `[0,1]`.  This file replaces that space by a genuinely finite one.  A label
is a pair in `Bool × Fin N`, and an outcome assigns one label independently to
every vertex.

If an edge has size `j`, we require `j ∣ N`.  Its high interval consists of
the final `d * (N / j)` priority values.  It consequently has density exactly
`d / j`; the complementary low interval has density `1 - d / j`.  The main
count proves, on the common global sample space, the exact analogue

`Pr(edge is initially monochromatic and all its priorities are low)
  = 2^(1-j) * (1-d/j)^j`.

Priorities can tie in `Fin N`.  For algorithms which require a total order we
order the pair `(priority value, vertex)`, so the given linear order on the
vertices supplies a deterministic tie-break.
-/

open scoped BigOperators

namespace Erdos1027.DGKPriorities

open Finset
open Erdos1027.FiniteExpect

/-- One independent initial colour and finite priority for each vertex. -/
abbrev Outcome (V : Type*) (N : ℕ) := V → Bool × Fin N

/-- The initial Boolean colour of a vertex. -/
def colour {V : Type*} {N : ℕ} (w : Outcome V N) (v : V) : Bool :=
  (w v).1

/-- The finite priority of a vertex. -/
def priority {V : Type*} {N : ℕ} (w : Outcome V N) (v : V) : Fin N :=
  (w v).2

/-- Number of priority values in the high interval for parameters `d,j`. -/
def highCount (N d j : ℕ) : ℕ := d * (N / j)

/-- The first value in the final (high) priority interval. -/
def cutoff (N d j : ℕ) : ℕ := N - highCount N d j

/-- A priority is low when it lies strictly below the cutoff. -/
def IsLow (N d j : ℕ) (p : Fin N) : Prop :=
  p.val < cutoff N d j

/-- A priority is high when it lies in the final interval. -/
def IsHigh (N d j : ℕ) (p : Fin N) : Prop :=
  cutoff N d j ≤ p.val

instance (N d j : ℕ) (p : Fin N) : Decidable (IsLow N d j p) := by
  unfold IsLow
  infer_instance

instance (N d j : ℕ) (p : Fin N) : Decidable (IsHigh N d j p) := by
  unfold IsHigh
  infer_instance

/-- The low priority interval as a finset. -/
def lowValues (N d j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (IsLow N d j)

/-- The high priority interval as a finset. -/
def highValues (N d j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (IsHigh N d j)

lemma highCount_le (N d j : ℕ) (hdj : d ≤ j) : highCount N d j ≤ N := by
  unfold highCount
  by_cases hj : j = 0
  · subst j
    simp
  · calc
      d * (N / j) ≤ j * (N / j) := Nat.mul_le_mul_right _ hdj
      _ ≤ N := Nat.mul_div_le N j

lemma cutoff_le (N d j : ℕ) : cutoff N d j ≤ N := by
  simp [cutoff]

@[simp] lemma card_lowValues (N d j : ℕ) :
    (lowValues N d j).card = cutoff N d j := by
  change ((Finset.univ : Finset (Fin N)).filter
    (fun p ↦ p.val < cutoff N d j)).card = cutoff N d j
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (cutoff_le N d j)

@[simp] lemma card_highValues (N d j : ℕ) (hdj : d ≤ j) :
    (highValues N d j).card = highCount N d j := by
  have hcompl : highValues N d j = (lowValues N d j)ᶜ := by
    ext p
    simp [highValues, lowValues, IsHigh, IsLow]
  rw [hcompl, card_compl, card_lowValues]
  simpa [cutoff] using Nat.sub_sub_self (highCount_le N d j hdj)

lemma low_or_high {N d j : ℕ} (p : Fin N) : IsLow N d j p ∨ IsHigh N d j p := by
  exact lt_or_ge _ _

lemma not_low_iff_high {N d j : ℕ} (p : Fin N) : ¬ IsLow N d j p ↔ IsHigh N d j p := by
  simp [IsLow, IsHigh]

/-- Addition-only form matching the usual DGK definition of the final
`d/j` priority window. -/
lemma isHigh_iff_le_add {N d j : ℕ} (hdj : d ≤ j) (p : Fin N) :
    IsHigh N d j p ↔ N ≤ p.val + highCount N d j := by
  unfold IsHigh cutoff
  omega

/-! ## Deterministic tie-breaking -/

section TieBreak

variable {V : Type*} [LinearOrder V] {N : ℕ}

/-- Lexicographic key: finite priority first, vertex order second. -/
def priorityKey (w : Outcome V N) (v : V) : Fin N ×ₗ V :=
  (priority w v, v)

/-- `v` is processed before `u`, with the vertex order breaking ties. -/
def Earlier (w : Outcome V N) (v u : V) : Prop :=
  priorityKey w v < priorityKey w u

lemma priorityKey_injective (w : Outcome V N) : Function.Injective (priorityKey w) := by
  intro v u h
  exact congrArg (fun p : Fin N ×ₗ V ↦ p.2) h

lemma earlier_or_earlier (w : Outcome V N) {v u : V} (hvu : v ≠ u) :
    Earlier w v u ∨ Earlier w u v := by
  exact lt_or_gt_of_ne (fun h ↦ hvu (priorityKey_injective w h))

lemma earlier_asymm (w : Outcome V N) {v u : V} :
    Earlier w v u → ¬ Earlier w u v := by
  exact LT.lt.asymm

end TieBreak

/-! ## A reusable exact cylinder count -/

/-- A finite sum of rational indicators is the cardinality of the
corresponding filter.  Keeping the decidability instance as an explicit type
class parameter avoids any dependence on which proposition decider is in
scope at a use site. -/
lemma sum_indicator_eq_card_filter {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] :
    (∑ x : A, indicator (P x)) = ((Finset.univ.filter P).card : ℚ) := by
  classical
  change (∑ x ∈ (Finset.univ : Finset A), indicator (P x)) = _
  induction (Finset.univ : Finset A) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases h : P a
      · simp only [Finset.sum_insert ha, indicator_of_true h, ih]
        have hfilter : (insert a s).filter P = insert a (s.filter P) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hPx⟩
            · exact Or.inl hx
            · exact Or.inr ⟨hx, hPx⟩
          · rintro (hx | ⟨hxs, hPx⟩)
            · subst x
              exact ⟨Or.inl rfl, h⟩
            · exact ⟨Or.inr hxs, hPx⟩
        have hnot : a ∉ s.filter P := by
          exact fun ha' ↦ ha (Finset.mem_filter.1 ha').1
        rw [hfilter, Finset.card_insert_of_notMem hnot]
        rw [Nat.cast_add, Nat.cast_one]
        exact add_comm (1 : ℚ) _
      · simp only [Finset.sum_insert ha, indicator_of_false h, zero_add, ih]
        have hfilter : (insert a s).filter P = s.filter P := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hPx⟩
            · subst x
              exact False.elim (h hPx)
            · exact ⟨hx, hPx⟩
          · rintro ⟨hxs, hPx⟩
            exact ⟨Or.inr hxs, hPx⟩
        rw [hfilter]

/-- On a uniform product space, requiring the coordinates in `s` to lie in
`t` has probability `(card t / card A) ^ card s`.  The assertion is stated as
an exact rational expectation, and importantly `s` may be a proper subset of
the global vertex type `V`. -/
lemma expect_indicator_all_mem {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Nonempty A] (s : Finset V) (t : Finset A) :
    (𝔼 w : V → A, indicator (∀ v ∈ s, w v ∈ t)) =
      ((t.card : ℚ) / Fintype.card A) ^ s.card := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  have hfilter :
      (Finset.univ.filter fun w : V → A ↦ ∀ v ∈ s, w v ∈ t) =
        Fintype.piFinset (fun v ↦ if v ∈ s then t else Finset.univ) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hw v
      by_cases hv : v ∈ s
      · simp [hv, hw v hv]
      · simp [hv]
    · intro hw v hv
      simpa [hv] using hw v
  have hsum :
      (∑ w : V → A, indicator (∀ v ∈ s, w v ∈ t)) =
        ((Fintype.piFinset (fun v ↦ if v ∈ s then t else Finset.univ)).card : ℚ) := by
    rw [← hfilter]
    exact sum_indicator_eq_card_filter (fun w : V → A ↦ ∀ v ∈ s, w v ∈ t)
  rw [hsum, Fintype.card_piFinset]
  simp only [Nat.cast_prod, apply_ite Finset.card, card_univ, Fintype.card_fun]
  rw [show ((∏ v : V, (if v ∈ s then t.card else Fintype.card A : ℕ)) : ℚ) =
      ∏ v : V, (if v ∈ s then (t.card : ℚ) else Fintype.card A) by norm_cast]
  rw [show ((Fintype.card A ^ Fintype.card V : ℕ) : ℚ) =
      ∏ _v : V, (Fintype.card A : ℚ) by simp]
  rw [← Finset.prod_div_distrib]
  simp only [ite_div, div_self (by exact_mod_cast Fintype.card_ne_zero :
    (Fintype.card A : ℚ) ≠ 0)]
  rw [Fintype.prod_ite_mem]
  exact Finset.prod_const ((t.card : ℚ) / Fintype.card A)

/-! ## Exact high and low probabilities -/

/-- A single finite priority is high with probability exactly `d/j`. -/
theorem expect_indicator_isHigh {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j)
    (hdiv : j ∣ N) :
    (𝔼 p : Fin N, indicator (IsHigh N d j p)) = (d : ℚ) / j := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  rw [show (𝔼 p : Fin N, indicator (IsHigh N d j p)) =
      ((highValues N d j).card : ℚ) / N by
        rw [Fintype.expect_eq_sum_div_card]
        simp only [Fintype.card_fin]
        rw [sum_indicator_eq_card_filter]
        rfl]
  rw [card_highValues N d j hdj, highCount]
  have hj : 0 < j := Nat.pos_of_dvd_of_pos hdiv hN
  rw [Nat.cast_mul, Nat.cast_div_charZero hdiv]
  field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne',
    show (j : ℚ) ≠ 0 by exact_mod_cast hj.ne']

/-- A single finite priority is low with probability exactly `1-d/j`. -/
theorem expect_indicator_isLow {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j)
    (hdiv : j ∣ N) :
    (𝔼 p : Fin N, indicator (IsLow N d j p)) = 1 - (d : ℚ) / j := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  rw [show (𝔼 p : Fin N, indicator (IsLow N d j p)) =
      ((lowValues N d j).card : ℚ) / N by
        rw [Fintype.expect_eq_sum_div_card]
        simp only [Fintype.card_fin]
        rw [sum_indicator_eq_card_filter]
        rfl]
  rw [card_lowValues, cutoff]
  have hj : 0 < j := Nat.pos_of_dvd_of_pos hdiv hN
  have hhigh := highCount_le N d j hdj
  rw [Nat.cast_sub hhigh]
  rw [highCount, Nat.cast_mul, Nat.cast_div_charZero hdiv]
  field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne',
    show (j : ℚ) ≠ 0 by exact_mod_cast hj.ne']

/-- The high marginal remains exactly `d/j` when the priority is one
coordinate of the common global colour-priority product space. -/
theorem expect_indicator_vertex_isHigh {V : Type*} [Fintype V]
    [DecidableEq V] {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j)
    (hdiv : j ∣ N) (v : V) :
    (𝔼 w : Outcome V N, indicator (IsHigh N d j (priority w v))) =
      (d : ℚ) / j := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let labels : Finset (Bool × Fin N) :=
    (Finset.univ : Finset Bool) ×ˢ highValues N d j
  have hevent : ∀ w : Outcome V N,
      IsHigh N d j (priority w v) ↔ ∀ u ∈ ({v} : Finset V), w u ∈ labels := by
    intro w
    simp [labels, highValues, priority]
  rw [show (𝔼 w : Outcome V N, indicator (IsHigh N d j (priority w v))) =
      (𝔼 w : Outcome V N,
        indicator (∀ u ∈ ({v} : Finset V), w u ∈ labels)) by
      apply Finset.expect_congr rfl
      intro w _
      rw [propext (hevent w)]]
  rw [expect_indicator_all_mem]
  simp only [card_singleton, pow_one, labels, card_product, card_univ,
    Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
  rw [card_highValues N d j hdj]
  rw [show ((2 * highCount N d j : ℕ) : ℚ) =
      2 * (highCount N d j : ℚ) by norm_num]
  rw [show ((2 * N : ℕ) : ℚ) = 2 * (N : ℚ) by norm_num]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℚ) ≠ 0)]
  rw [highCount]
  have hj : 0 < j := Nat.pos_of_dvd_of_pos hdiv hN
  rw [Nat.cast_mul, Nat.cast_div_charZero hdiv]
  field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne',
    show (j : ℚ) ≠ 0 by exact_mod_cast hj.ne']

/-! ## Initially monochromatic low-priority edges -/

/-- A fixed edge is initially monochromatic in the colour `b`. -/
def Monochromatic {V : Type*} {N : ℕ} (w : Outcome V N)
    (e : Finset V) (b : Bool) : Prop :=
  ∀ v ∈ e, colour w v = b

/-- A fixed edge is initially monochromatic, in either colour. -/
def InitiallyMonochromatic {V : Type*} {N : ℕ} (w : Outcome V N)
    (e : Finset V) : Prop :=
  ∃ b : Bool, Monochromatic w e b

/-- Every priority on the edge lies below its `d/j` high interval. -/
def AllLow {V : Type*} {N : ℕ} (d j : ℕ) (w : Outcome V N)
    (e : Finset V) : Prop :=
  ∀ v ∈ e, IsLow N d j (priority w v)

/-- The allowed label set for one prescribed monochromatic colour. -/
def lowLabels (N d j : ℕ) (b : Bool) : Finset (Bool × Fin N) :=
  {b} ×ˢ lowValues N d j

@[simp] lemma card_lowLabels (N d j : ℕ) (b : Bool) :
    (lowLabels N d j b).card = cutoff N d j := by
  simp [lowLabels]

lemma monochromatic_and_allLow_iff_all_mem {V : Type*} {N d j : ℕ}
    (w : Outcome V N) (e : Finset V) (b : Bool) :
    Monochromatic w e b ∧ AllLow d j w e ↔
      ∀ v ∈ e, w v ∈ lowLabels N d j b := by
  constructor
  · rintro ⟨hmono, hlow⟩ v hv
    change w v ∈ ({b} : Finset Bool) ×ˢ lowValues N d j
    apply Finset.mem_product.2
    refine ⟨?_, ?_⟩
    · simpa [colour] using hmono v hv
    · apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [priority] using hlow v hv
  · intro hall
    constructor
    · intro v hv
      have hmem := hall v hv
      change w v ∈ ({b} : Finset Bool) ×ˢ lowValues N d j at hmem
      have h := Finset.mem_product.1 hmem
      simpa [colour] using h.1
    · intro v hv
      have hmem := hall v hv
      change w v ∈ ({b} : Finset Bool) ×ˢ lowValues N d j at hmem
      have h := Finset.mem_product.1 hmem
      have hp := (Finset.mem_filter.1 h.2).2
      simpa [priority] using hp

/-- Exact probability for one prescribed colour. -/
theorem expect_indicator_monochromatic_and_allLow {V : Type*} [Fintype V]
    [DecidableEq V] {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j) (hdiv : j ∣ N)
    (e : Finset V) (hecard : e.card = j) (b : Bool) :
    (𝔼 w : Outcome V N, indicator (Monochromatic w e b ∧ AllLow d j w e)) =
      ((1 : ℚ) / 2 * (1 - (d : ℚ) / j)) ^ j := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  rw [show (𝔼 w : Outcome V N, indicator (Monochromatic w e b ∧ AllLow d j w e)) =
      (𝔼 w : Outcome V N, indicator (∀ v ∈ e, w v ∈ lowLabels N d j b)) by
        apply Finset.expect_congr rfl
        intro w _
        rw [monochromatic_and_allLow_iff_all_mem]]
  rw [expect_indicator_all_mem, card_lowLabels, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, hecard]
  have hj : 0 < j := Nat.pos_of_dvd_of_pos hdiv hN
  have hhigh := highCount_le N d j hdj
  rw [cutoff, Nat.cast_sub hhigh, highCount, Nat.cast_mul, Nat.cast_div_charZero hdiv]
  congr 1
  field_simp [show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne',
    show (j : ℚ) ≠ 0 by exact_mod_cast hj.ne']
  push_cast
  ring

/-- Exact DGK edge probability on the common global finite sample space. -/
theorem expect_indicator_initiallyMonochromatic_and_allLow
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j) (hdiv : j ∣ N)
    (e : Finset V) (hecard : e.card = j) (he : e.Nonempty) :
    (𝔼 w : Outcome V N,
        indicator (InitiallyMonochromatic w e ∧ AllLow d j w e)) =
      (2 : ℚ) ^ (1 - (j : ℤ)) * (1 - (d : ℚ) / j) ^ j := by
  classical
  have hpoint : ∀ w : Outcome V N,
      indicator (InitiallyMonochromatic w e ∧ AllLow d j w e) =
        indicator (Monochromatic w e false ∧ AllLow d j w e) +
          indicator (Monochromatic w e true ∧ AllLow d j w e) := by
    intro w
    let P : Bool → Prop := fun b ↦ Monochromatic w e b ∧ AllLow d j w e
    have hdisjoint : ¬ (P false ∧ P true) := by
      rintro ⟨hfalse, htrue⟩
      obtain ⟨v, hv⟩ := he
      have h0 := hfalse.1 v hv
      have h1 := htrue.1 v hv
      simp_all
    have horiginal :
        InitiallyMonochromatic w e ∧ AllLow d j w e ↔ P false ∨ P true := by
      constructor
      · rintro ⟨⟨b, hb⟩, hlow⟩
        cases b
        · exact Or.inl ⟨hb, hlow⟩
        · exact Or.inr ⟨hb, hlow⟩
      · rintro (h | h)
        · exact ⟨⟨false, h.1⟩, h.2⟩
        · exact ⟨⟨true, h.1⟩, h.2⟩
    rw [show indicator (InitiallyMonochromatic w e ∧ AllLow d j w e) =
        indicator (P false ∨ P true) by rw [propext horiginal]]
    change indicator (P false ∨ P true) = indicator (P false) + indicator (P true)
    by_cases h0 : P false <;> by_cases h1 : P true <;>
      simp [indicator, h0, h1] at hdisjoint ⊢
  simp_rw [hpoint]
  rw [Finset.expect_add_distrib,
    expect_indicator_monochromatic_and_allLow hN hdj hdiv e hecard false,
    expect_indicator_monochromatic_and_allLow hN hdj hdiv e hecard true]
  let x : ℚ := 1 - (d : ℚ) / j
  change ((1 : ℚ) / 2 * x) ^ j + ((1 : ℚ) / 2 * x) ^ j =
    (2 : ℚ) ^ (1 - (j : ℤ)) * x ^ j
  rw [← two_mul]
  rw [mul_pow, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one, zpow_natCast]
  rw [div_pow, one_pow]
  ring

/-- The upper-bound form used by the DGK union bound. -/
theorem expect_indicator_initiallyMonochromatic_and_allLow_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j) (hdiv : j ∣ N)
    (e : Finset V) (hecard : e.card = j) (he : e.Nonempty) :
    (𝔼 w : Outcome V N,
        indicator (InitiallyMonochromatic w e ∧ AllLow d j w e)) ≤
      (2 : ℚ) ^ (1 - (j : ℤ)) * (1 - (d : ℚ) / j) ^ j := by
  exact (expect_indicator_initiallyMonochromatic_and_allLow hN hdj hdiv e hecard he).le

/-- The directly usable DGK form: an edge of size `j ≥ r > d` satisfies
the desired light-edge bound.  Nonemptiness follows from these inequalities. -/
theorem expect_indicator_initiallyMonochromatic_and_allLow_le_of_lt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d r j : ℕ} (hN : 0 < N) (hdiv : j ∣ N) (hdr : d < r) (hrj : r ≤ j)
    (e : Finset V) (hecard : e.card = j) :
    (𝔼 w : Outcome V N,
        indicator (InitiallyMonochromatic w e ∧ AllLow d j w e)) ≤
      (2 : ℚ) ^ (1 - (j : ℤ)) * (1 - (d : ℚ) / j) ^ j := by
  have hdj : d ≤ j := (Nat.le_of_lt hdr).trans hrj
  have hj : 0 < j := lt_of_lt_of_le (Nat.zero_lt_succ d) (hdr.trans_le hrj)
  have he : e.Nonempty := Finset.card_pos.mp (hecard.trans_gt hj)
  exact expect_indicator_initiallyMonochromatic_and_allLow_le
    hN hdj hdiv e hecard he

end Erdos1027.DGKPriorities
