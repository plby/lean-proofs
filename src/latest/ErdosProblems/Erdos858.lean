/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 858.
https://www.erdosproblems.com/forum/thread/858

Informal authors:
- Przemek Chojecki
- GPT-5.4 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos858.md
-/
import Mathlib
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 858

For a finite set `A ⊆ {1, …, N}`, call `A` admissible when it contains no
pair `a, b` with `b = a * t`, `1 < t`, and `a < t.minFac`.  This file proves
that the largest reciprocal mass of such a set, divided by `log N`, converges
to the explicit constant described by Chojecki's resolution of the problem.
-/

open scoped BigOperators Topology
open Filter Finset Set

namespace Erdos858

/-- The integer interval occurring in the original problem. -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The literal exclusion condition from Erdős Problem 858. -/
def Admissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ, 1 < t → b = a * t → t.minFac ≤ a

/-- Reciprocal (harmonic) mass of a finite set of positive integers. -/
noncomputable def harmonicMass (A : Finset ℕ) : ℝ := ∑ n ∈ A, (n : ℝ)⁻¹

/-- All admissible subsets of `{1, …, N}`. -/
noncomputable def candidateFamilies (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (interval N).powerset.filter Admissible

/-- The finite set of all reciprocal masses attained by admissible families. -/
noncomputable def candidateMasses (N : ℕ) : Finset ℝ := by
  classical
  exact (candidateFamilies N).image harmonicMass

lemma empty_mem_candidateFamilies (N : ℕ) : ∅ ∈ candidateFamilies N := by
  classical
  simp [candidateFamilies, Admissible]

lemma candidateMasses_nonempty (N : ℕ) : (candidateMasses N).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  exact Finset.mem_image.mpr ⟨∅, empty_mem_candidateFamilies N, by simp [harmonicMass]⟩

/-- The exact finite maximum asked for in the problem. -/
noncomputable def extremalMass (N : ℕ) : ℝ :=
  (candidateMasses N).max' (candidateMasses_nonempty N)

lemma extremalMass_mem (N : ℕ) : extremalMass N ∈ candidateMasses N :=
  Finset.max'_mem _ _

lemma harmonicMass_le_extremalMass {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ interval N) (hadm : Admissible A) :
    harmonicMass A ≤ extremalMass N := by
  classical
  apply Finset.le_max' (candidateMasses N) (harmonicMass A)
  refine Finset.mem_image.mpr ⟨A, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hadm⟩

lemma exists_extremizer (N : ℕ) :
    ∃ A ⊆ interval N, Admissible A ∧ harmonicMass A = extremalMass N := by
  classical
  obtain ⟨A, hA, hm⟩ := Finset.mem_image.mp (extremalMass_mem N)
  have hA' := Finset.mem_filter.mp hA
  exact ⟨A, Finset.mem_powerset.mp hA'.1, hA'.2, hm⟩

/-- The two-prime part of the limiting inflow profile. -/
noncomputable def twoPrimeProfile (u : ℝ) : ℝ :=
  if u < (1 : ℝ) / 3 then
    ∫ x in u..(1 - u) / 2, x⁻¹ * Real.log ((1 - u - x) / x)
  else 0

/-- The limiting inflow profile above the quarter-power layer. -/
noncomputable def profile (u : ℝ) : ℝ :=
  Real.log ((1 - u) / u) + twoPrimeProfile u

/-- The threshold exponent.  Later results identify this infimum with the
unique root of `profile u = 1` in `(1/4, 1/3)`. -/
noncomputable def alphaTwo : ℝ :=
  sInf {u : ℝ | u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) ∧ profile u ≤ 1}

/-- The explicit asymptotic constant in the resolution of the problem. -/
noncomputable def constant : ℝ :=
  (1 : ℝ) / 2 + ∫ u in alphaTwo..(1 : ℝ) / 2, 1 - profile u

/-- Rough divisibility: `a ≼ b` exactly when `a = b`, or `b/a` has every
prime factor strictly larger than `a`. -/
def RoughLE (a b : ℕ) : Prop :=
  a = b ∨ ∃ t : ℕ, 1 < t ∧ b = a * t ∧ a < t.minFac

lemma lt_minFac_mul {a t u : ℕ} (ht : 1 < t) (hu : 1 < u)
    (hat : a < t.minFac) (hau : a < u.minFac) :
    a < (t * u).minFac := by
  have htu : t * u ≠ 1 := by nlinarith
  have hp : Nat.Prime ((t * u).minFac) := Nat.minFac_prime htu
  rcases (Nat.Prime.dvd_mul hp).mp (Nat.minFac_dvd (t * u)) with hpt | hpu
  · exact hat.trans_le (Nat.minFac_le_of_dvd hp.two_le hpt)
  · exact hau.trans_le (Nat.minFac_le_of_dvd hp.two_le hpu)

lemma RoughLE.refl (a : ℕ) : RoughLE a a := Or.inl rfl

lemma RoughLE.trans {a b c : ℕ} (hab : RoughLE a b) (hbc : RoughLE b c) :
    RoughLE a c := by
  rcases hab with rfl | ⟨t, ht, hbt, hat⟩
  · exact hbc
  rcases hbc with rfl | ⟨u, hu, hcu, hbu⟩
  · exact Or.inr ⟨t, ht, hbt, hat⟩
  refine Or.inr ⟨t * u, by nlinarith, ?_, lt_minFac_mul ht hu hat ?_⟩
  · calc
      c = b * u := hcu
      _ = (a * t) * u := by rw [hbt]
      _ = a * (t * u) := by simp [mul_assoc]
  · have hab_le : a ≤ b := by
      rw [hbt]
      exact Nat.le_mul_of_pos_right a (by omega)
    exact hab_le.trans_lt hbu

lemma RoughLE.dvd {a b : ℕ} (hab : RoughLE a b) : a ∣ b := by
  rcases hab with rfl | ⟨t, -, rfl, -⟩
  · exact dvd_rfl
  · exact dvd_mul_right a t

lemma RoughLE.antisymm {a b : ℕ} (hab : RoughLE a b) (hba : RoughLE b a) : a = b :=
  Nat.dvd_antisymm hab.dvd hba.dvd

lemma RoughLE.lt_of_ne {a b : ℕ} (ha : 0 < a) (hab : RoughLE a b) (hne : a ≠ b) :
    a < b := by
  rcases hab with heq | ⟨t, ht, rfl, -⟩
  · exact (hne heq).elim
  · nlinarith

/-- A proper divisor that is an ancestor in the rough-divisibility order. -/
def Eligible (n d : ℕ) : Prop :=
  0 < d ∧ d < n ∧ d ∣ n ∧ d < (n / d).minFac

lemma eligible_of_rough {a n : ℕ} (ha : 0 < a) (han : RoughLE a n) (hne : a ≠ n) :
    Eligible n a := by
  rcases han with heq | ⟨t, ht, hnt, hmin⟩
  · exact (hne heq).elim
  have hadvd : a ∣ n := ⟨t, hnt⟩
  have hquot : n / a = t := by
    rw [hnt]
    exact Nat.mul_div_cancel_left t ha
  exact ⟨ha, by nlinarith [Nat.one_le_iff_ne_zero.mpr ha.ne'], hadvd, by simpa [hquot] using hmin⟩

/-- Eligible ancestors of one integer are linearly ordered by divisibility.
This is the arithmetic fact that makes rough divisibility a tree order. -/
lemma eligible_dvd_of_le {n a d : ℕ} (ha : Eligible n a) (hd : Eligible n d)
    (had : a ≤ d) : a ∣ d := by
  by_contra hnot
  let g := Nat.gcd a d
  let x := a / g
  let y := d / g
  let s := n / d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d ha.1
  have hga : g ∣ a := Nat.gcd_dvd_left a d
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  have hax : g * x = a := by simpa [g, x] using Nat.mul_div_cancel' hga
  have hdy : g * y = d := by simpa [g, y] using Nat.mul_div_cancel' hgd
  have hds : d * s = n := by simpa [s] using Nat.mul_div_cancel' hd.2.2.1
  have hxy : x.Coprime y := by
    simpa [g, x, y] using Nat.coprime_div_gcd_div_gcd hg
  have hx_dvd_ys : x ∣ y * s := by
    apply Nat.dvd_of_mul_dvd_mul_left hg
    have hgxy : g * x ∣ g * (y * s) := by
      rw [hax, ← mul_assoc, hdy, hds]
      exact ha.2.2.1
    exact hgxy
  have hx_dvd_s : x ∣ s := hxy.dvd_of_dvd_mul_left hx_dvd_ys
  have hx_ne_one : x ≠ 1 := by
    intro hx
    apply hnot
    rw [← hax, hx, mul_one]
    exact hgd
  let p := x.minFac
  have hpprime : p.Prime := Nat.minFac_prime hx_ne_one
  have hp_dvd_x : p ∣ x := Nat.minFac_dvd x
  have hp_dvd_a : p ∣ a := by
    rw [← hax]
    exact dvd_mul_of_dvd_right hp_dvd_x g
  have hp_le_a : p ≤ a := Nat.le_of_dvd ha.1 hp_dvd_a
  have hp_dvd_s : p ∣ s := dvd_trans hp_dvd_x hx_dvd_s
  have hs_min_le : s.minFac ≤ p := Nat.minFac_le_of_dvd hpprime.two_le hp_dvd_s
  have : d < p := hd.2.2.2.trans_le hs_min_le
  exact (not_lt_of_ge (hp_le_a.trans had)) this

/-- The finite collection from which the parent is selected. -/
noncomputable def eligibleDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 1 n).filter (Eligible n)

lemma mem_eligibleDivisors {n d : ℕ} :
    d ∈ eligibleDivisors n ↔ Eligible n d := by
  classical
  rw [eligibleDivisors, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h⟩

lemma eligibleDivisors_nonempty {n : ℕ} (hn : 1 < n) :
    (eligibleDivisors n).Nonempty := by
  refine ⟨1, mem_eligibleDivisors.mpr ?_⟩
  have hp : Nat.Prime n.minFac := Nat.minFac_prime hn.ne'
  simp [Eligible, hn, hp.one_lt]

/-- The largest proper rough ancestor of `n`; it is `0` at `0` and `1`. -/
noncomputable def parent (n : ℕ) : ℕ :=
  if h : 1 < n then (eligibleDivisors n).max' (eligibleDivisors_nonempty h) else 0

lemma parent_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : parent n = 0 := by
  rw [parent, dif_neg (Nat.not_lt.mpr hn)]

@[simp] lemma parent_zero : parent 0 = 0 := parent_eq_zero_of_le_one (by omega)

@[simp] lemma parent_one : parent 1 = 0 := parent_eq_zero_of_le_one (by omega)

lemma parent_mem_eligibleDivisors {n : ℕ} (hn : 1 < n) :
    parent n ∈ eligibleDivisors n := by
  rw [parent, dif_pos hn]
  exact Finset.max'_mem _ _

lemma parent_eligible {n : ℕ} (hn : 1 < n) : Eligible n (parent n) :=
  mem_eligibleDivisors.mp (parent_mem_eligibleDivisors hn)

lemma le_parent_of_eligible {n d : ℕ} (hn : 1 < n) (hd : Eligible n d) :
    d ≤ parent n := by
  rw [parent, dif_pos hn]
  exact Finset.le_max' _ _ (mem_eligibleDivisors.mpr hd)

lemma parent_pos {n : ℕ} (hn : 1 < n) : 0 < parent n := (parent_eligible hn).1

lemma parent_lt {n : ℕ} (hn : 1 < n) : parent n < n := (parent_eligible hn).2.1

lemma parent_dvd {n : ℕ} (hn : 1 < n) : parent n ∣ n := (parent_eligible hn).2.2.1

lemma parent_rough {n : ℕ} (hn : 1 < n) : RoughLE (parent n) n := by
  let d := parent n
  let t := n / d
  have hd := parent_eligible hn
  have heq : d * t = n := by simpa [d, t] using Nat.mul_div_cancel' hd.2.2.1
  have ht : 1 < t := by
    by_contra h
    have htle : t ≤ 1 := Nat.le_of_not_gt h
    have ht_cases : t = 0 ∨ t = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp htle
    rcases ht_cases with ht0 | ht1
    · rw [ht0] at heq
      simp at heq
      omega
    · rw [ht1] at heq
      rw [mul_one] at heq
      exact (ne_of_lt hd.2.1) heq
  exact Or.inr ⟨t, ht, heq.symm, by simpa [d, t] using hd.2.2.2⟩

/-- If two eligible ancestors are ordered and distinct, the smaller one is
itself eligible as an ancestor of the larger one. -/
lemma eligible_between {n a d : ℕ} (ha : Eligible n a) (hd : Eligible n d)
    (had : a ≤ d) (hne : a ≠ d) : Eligible d a := by
  have hadvd : a ∣ d := eligible_dvd_of_le ha hd had
  have hadlt : a < d := lt_of_le_of_ne had hne
  have hq_ne_one : d / a ≠ 1 := by
    intro hq
    apply hne
    calc
      a = a * (d / a) := by simp [hq]
      _ = d := Nat.mul_div_cancel' hadvd
  have hq_dvd : d / a ∣ n / a := by
    rw [Nat.dvd_div_iff_mul_dvd ha.2.2.1, Nat.mul_div_cancel' hadvd]
    exact hd.2.2.1
  have hp : Nat.Prime (d / a).minFac := Nat.minFac_prime hq_ne_one
  have hmin : (n / a).minFac ≤ (d / a).minFac :=
    Nat.minFac_le_of_dvd hp.two_le (dvd_trans (Nat.minFac_dvd _) hq_dvd)
  exact ⟨ha.1, hadlt, hadvd, ha.2.2.2.trans_le hmin⟩

lemma rough_of_eligible {n d : ℕ} (hd : Eligible n d) : RoughLE d n := by
  let t := n / d
  have heq : d * t = n := by
    simpa [t] using Nat.mul_div_cancel' hd.2.2.1
  have ht : 1 < t := by
    by_contra h
    have htle : t ≤ 1 := Nat.le_of_not_gt h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp htle with ht0 | ht1
    · have hzero : 0 = n := by simpa [ht0] using heq
      exact (Nat.ne_of_gt (hd.1.trans hd.2.1)) hzero.symm
    · have heq' : d = n := by simpa [ht1] using heq
      exact (ne_of_lt hd.2.1) heq'
  exact Or.inr ⟨t, ht, heq.symm, by simpa [t] using hd.2.2.2⟩

/-- A directed edge from a parent to one of its children. -/
def ParentStep (a b : ℕ) : Prop := 1 < b ∧ parent b = a

/-- The reflexive transitive closure of the parent relation. -/
def IsAncestor (a b : ℕ) : Prop := Relation.ReflTransGen ParentStep a b

lemma ancestor_rough {a b : ℕ} (h : IsAncestor a b) : RoughLE a b := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl a => exact RoughLE.refl a
  | single h =>
      rw [← h.2]
      exact parent_rough h.1
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Rough divisibility is exactly ancestry in the parent tree. -/
lemma rough_iff_ancestor {a b : ℕ} (ha : 0 < a) :
    RoughLE a b ↔ IsAncestor a b := by
  constructor
  · intro hab
    induction b using Nat.strong_induction_on with
    | h b ih =>
      by_cases heq : a = b
      · subst b
        exact Relation.ReflTransGen.refl
      have hablt : a < b := hab.lt_of_ne ha heq
      have hb : 1 < b := by omega
      have hea : Eligible b a := eligible_of_rough ha hab heq
      let d := parent b
      have hed : Eligible b d := by simpa [d] using parent_eligible hb
      have had : a ≤ d := by simpa [d] using le_parent_of_eligible hb hea
      by_cases hadeq : a = d
      · apply Relation.ReflTransGen.single
        exact ⟨hb, by simpa [d] using hadeq.symm⟩
      · have head : Eligible d a := eligible_between hea hed had hadeq
        have hi : IsAncestor a d := ih d (by simpa [d] using parent_lt hb)
          (rough_of_eligible head)
        exact hi.tail ⟨hb, by simp [d]⟩
  · exact ancestor_rough

lemma admissible_iff_pairwise_not_rough {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a) :
    Admissible A ↔ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ RoughLE a b := by
  constructor
  · intro h a ha b hb hab hr
    rcases hr with rfl | ⟨t, ht, hbat, hmin⟩
    · exact hab rfl
    · exact (not_le_of_gt hmin) (h a ha b hb t ht hbat)
  · intro h a ha b hb t ht hbat
    by_contra hmin
    have hab : a ≠ b := by
      intro hab
      rw [hab] at hbat
      have hbpos : 0 < b := hpos b hb
      nlinarith
    exact h a ha b hb hab (Or.inr ⟨t, ht, hbat, Nat.lt_of_not_ge hmin⟩)

/-- Reciprocal weight attached to a vertex of the parent tree. -/
noncomputable def weight (n : ℕ) : ℝ := (n : ℝ)⁻¹

/-- Total weight entering `n` from its children not exceeding `N`. -/
noncomputable def inflow (N n : ℕ) : ℝ :=
  ∑ m ∈ interval N, if parent m = n then weight m else 0

/-- Discrete divergence of reciprocal weight at `n`. -/
noncomputable def divergence (N n : ℕ) : ℝ := weight n - inflow N n

/-- A vertex set is closed under taking children inside the truncation. -/
def DescendantClosed (N : ℕ) (U : Finset ℕ) : Prop :=
  U ⊆ interval N ∧
    ∀ n ∈ U, ∀ m ∈ interval N, parent m = n → m ∈ U

/-- The top boundary of a descendant-closed set. -/
noncomputable def roots (U : Finset ℕ) : Finset ℕ := by
  classical
  exact U.filter fun n ↦ parent n ∉ U

lemma sum_inflow_eq_internal (N : ℕ) {U : Finset ℕ}
    (hU : DescendantClosed N U) :
    ∑ n ∈ U, inflow N n = ∑ m ∈ U.filter (fun m ↦ parent m ∈ U), weight m := by
  classical
  calc
    ∑ n ∈ U, inflow N n =
        ∑ m ∈ interval N, ∑ n ∈ U, if parent m = n then weight m else 0 := by
          simp only [inflow]
          rw [Finset.sum_comm]
    _ = ∑ m ∈ interval N, if parent m ∈ U then weight m else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          by_cases hp : parent m ∈ U
          · simp [hp]
          · simp [hp]
    _ = ∑ m ∈ (interval N).filter (fun m ↦ parent m ∈ U), weight m := by
          rw [Finset.sum_filter]
    _ = ∑ m ∈ U.filter (fun m ↦ parent m ∈ U), weight m := by
          congr 1
          ext m
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hmN, hp⟩
            exact ⟨hU.2 (parent m) hp m hmN rfl, hp⟩
          · rintro ⟨hmU, hp⟩
            exact ⟨hU.1 hmU, hp⟩

/-- Finite discrete divergence theorem for a descendant-closed set. -/
lemma sum_divergence_eq_roots (N : ℕ) {U : Finset ℕ}
    (hU : DescendantClosed N U) :
    ∑ n ∈ U, divergence N n = ∑ n ∈ roots U, weight n := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not U
    (fun n ↦ parent n ∈ U) weight
  calc
    ∑ n ∈ U, divergence N n =
        (∑ n ∈ U, weight n) - ∑ n ∈ U, inflow N n := by
          simp [divergence, Finset.sum_sub_distrib]
    _ = (∑ n ∈ U, weight n) -
        ∑ n ∈ U.filter (fun n ↦ parent n ∈ U), weight n := by
          rw [sum_inflow_eq_internal N hU]
    _ = ∑ n ∈ roots U, weight n := by
          rw [← hsplit]
          simp only [roots]
          ring

/-- Vertices below at least one member of `A`, truncated at `N`. -/
noncomputable def descendantClosure (N : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (interval N).filter fun n ↦ ∃ a ∈ A, IsAncestor a n

lemma mem_descendantClosure {N : ℕ} {A : Finset ℕ} {n : ℕ} :
    n ∈ descendantClosure N A ↔ n ∈ interval N ∧ ∃ a ∈ A, IsAncestor a n := by
  classical
  simp [descendantClosure]

lemma descendantClosure_closed (N : ℕ) (A : Finset ℕ) :
    DescendantClosed N (descendantClosure N A) := by
  classical
  constructor
  · intro n hn
    exact (mem_descendantClosure.mp hn).1
  · intro n hn m hm hparent
    obtain ⟨hnN, a, ha, han⟩ := mem_descendantClosure.mp hn
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hnN).1
      omega
    have hmgt : 1 < m := by
      by_contra h
      have hmle : m ≤ 1 := Nat.le_of_not_gt h
      have hpzero := parent_eq_zero_of_le_one hmle
      rw [hparent] at hpzero
      omega
    exact mem_descendantClosure.mpr
      ⟨hm, ⟨a, ha, han.tail ⟨hmgt, hparent⟩⟩⟩

lemma ancestor_parent_of_ne {a n : ℕ} (ha : 0 < a) (han : IsAncestor a n)
    (hne : a ≠ n) : IsAncestor a (parent n) := by
  have hran : RoughLE a n := ancestor_rough han
  have hanlt : a < n := hran.lt_of_ne ha hne
  have hn : 1 < n := by omega
  have hea : Eligible n a := eligible_of_rough ha hran hne
  have hep : Eligible n (parent n) := parent_eligible hn
  have hap : a ≤ parent n := le_parent_of_eligible hn hea
  by_cases heq : a = parent n
  · rw [← heq]
    exact Relation.ReflTransGen.refl
  · exact (rough_iff_ancestor ha).mp (rough_of_eligible
      (eligible_between hea hep hap heq))

/-- For an antichain, the top boundary of its descendant closure is exactly
the antichain itself. -/
lemma roots_descendantClosure_eq {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ interval N) (hadm : Admissible A) :
    roots (descendantClosure N A) = A := by
  classical
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha
    have := (Finset.mem_Icc.mp (hA ha)).1
    omega
  have hanti := (admissible_iff_pairwise_not_rough hpos).mp hadm
  ext n
  simp only [roots, Finset.mem_filter]
  constructor
  · rintro ⟨hnU, hpnU⟩
    obtain ⟨hnN, a, ha, han⟩ := mem_descendantClosure.mp hnU
    by_cases heq : a = n
    · simpa [heq] using ha
    · exfalso
      apply hpnU
      have hanlt : a < n := (ancestor_rough han).lt_of_ne (hpos a ha) heq
      have hapos : 0 < a := hpos a ha
      have hn : 1 < n := by omega
      have hparentN : parent n ∈ interval N := Finset.mem_Icc.mpr
        ⟨parent_pos hn, (parent_lt hn).le.trans (Finset.mem_Icc.mp hnN).2⟩
      exact mem_descendantClosure.mpr
        ⟨hparentN, ⟨a, ha, ancestor_parent_of_ne (hpos a ha) han heq⟩⟩
  · intro hnA
    have hnU : n ∈ descendantClosure N A := mem_descendantClosure.mpr
      ⟨hA hnA, ⟨n, hnA, Relation.ReflTransGen.refl⟩⟩
    refine ⟨hnU, ?_⟩
    intro hpnU
    obtain ⟨hpnN, a, ha, hap⟩ := mem_descendantClosure.mp hpnU
    have hn : 1 < n := by
      by_contra h
      have hnle : n ≤ 1 := Nat.le_of_not_gt h
      have hpzero := parent_eq_zero_of_le_one hnle
      rw [hpzero] at hpnN
      simp [interval] at hpnN
    have han : IsAncestor a n := hap.tail ⟨hn, rfl⟩
    by_cases heq : a = n
    · subst a
      have heq' := RoughLE.antisymm (ancestor_rough hap) (parent_rough hn)
      exact (ne_of_lt (parent_lt hn)) heq'.symm
    · exact (hanti a ha n hnA heq) (ancestor_rough han)

lemma harmonicMass_eq_sum_divergence {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ interval N) (hadm : Admissible A) :
    harmonicMass A = ∑ n ∈ descendantClosure N A, divergence N n := by
  rw [sum_divergence_eq_roots N (descendantClosure_closed N A),
    roots_descendantClosure_eq hA hadm]
  rfl

/-- The universal positive-divergence upper bound for the finite extremum. -/
noncomputable def positiveDivergenceMass (N : ℕ) : ℝ :=
  ∑ n ∈ interval N, max (divergence N n) 0

lemma harmonicMass_le_positiveDivergenceMass {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ interval N) (hadm : Admissible A) :
    harmonicMass A ≤ positiveDivergenceMass N := by
  rw [harmonicMass_eq_sum_divergence hA hadm]
  calc
    ∑ n ∈ descendantClosure N A, divergence N n ≤
        ∑ n ∈ descendantClosure N A, max (divergence N n) 0 := by
          exact Finset.sum_le_sum fun n hn ↦ le_max_left _ _
    _ ≤ positiveDivergenceMass N := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (descendantClosure_closed N A).1
            (fun n hn hnU ↦ le_max_right _ _)

lemma extremalMass_le_positiveDivergenceMass (N : ℕ) :
    extremalMass N ≤ positiveDivergenceMass N := by
  obtain ⟨A, hA, hadm, hmass⟩ := exists_extremizer N
  rw [← hmass]
  exact harmonicMass_le_positiveDivergenceMass hA hadm

lemma mem_of_mem_of_ancestor {N : ℕ} {U : Finset ℕ}
    (hU : DescendantClosed N U) {a b : ℕ} (haU : a ∈ U)
    (hbN : b ∈ interval N) (hab : IsAncestor a b) : b ∈ U := by
  have hapos : 0 < a := by
    have := (Finset.mem_Icc.mp (hU.1 haU)).1
    omega
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases heq : a = b
    · simpa [heq] using haU
    · have hablt : a < b := (ancestor_rough hab).lt_of_ne hapos heq
      have hb : 1 < b := by omega
      have hpN : parent b ∈ interval N := Finset.mem_Icc.mpr
        ⟨parent_pos hb, (parent_lt hb).le.trans (Finset.mem_Icc.mp hbN).2⟩
      have hpU : parent b ∈ U := ih (parent b) (parent_lt hb)
        hpN (ancestor_parent_of_ne hapos hab heq)
      exact hU.2 (parent b) hpU b hbN rfl

/-- The top boundary of every descendant-closed set is admissible. -/
lemma roots_admissible {N : ℕ} {U : Finset ℕ} (hU : DescendantClosed N U) :
    Admissible (roots U) := by
  classical
  have hpos : ∀ a ∈ roots U, 0 < a := by
    intro a ha
    have haU := (Finset.mem_filter.mp ha).1
    have := (Finset.mem_Icc.mp (hU.1 haU)).1
    omega
  apply (admissible_iff_pairwise_not_rough hpos).mpr
  intro a ha b hb hne hab
  have haU := (Finset.mem_filter.mp ha).1
  have hpbU := (Finset.mem_filter.mp hb).2
  have hbU := (Finset.mem_filter.mp hb).1
  have hapos : 0 < a := hpos a ha
  have hablt : a < b := hab.lt_of_ne hapos hne
  have hbgt : 1 < b := by omega
  have hpN : parent b ∈ interval N := Finset.mem_Icc.mpr
    ⟨parent_pos hbgt, (parent_lt hbgt).le.trans
      (Finset.mem_Icc.mp (hU.1 hbU)).2⟩
  apply hpbU
  exact mem_of_mem_of_ancestor hU haU hpN
    (ancestor_parent_of_ne hapos ((rough_iff_ancestor hapos).mp hab) hne)

lemma harmonicMass_roots_eq_sum_divergence {N : ℕ} {U : Finset ℕ}
    (hU : DescendantClosed N U) :
    harmonicMass (roots U) = ∑ n ∈ U, divergence N n := by
  rw [sum_divergence_eq_roots N hU]
  rfl

/-- The descendant-closed set cut out by an integer threshold. -/
def thresholdSet (N K : ℕ) : Finset ℕ :=
  (interval N).filter fun n ↦ K < n

lemma thresholdSet_closed (N K : ℕ) : DescendantClosed N (thresholdSet N K) := by
  classical
  constructor
  · intro n hn
    exact (Finset.mem_filter.mp hn).1
  · intro n hn m hm hparent
    have hnN := (Finset.mem_filter.mp hn).1
    have hKn := (Finset.mem_filter.mp hn).2
    have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hnN).1
      omega
    have hmgt : 1 < m := by
      by_contra h
      have hmle : m ≤ 1 := Nat.le_of_not_gt h
      have hpzero := parent_eq_zero_of_le_one hmle
      rw [hparent] at hpzero
      omega
    have hnm : n < m := by simpa [hparent] using parent_lt hmgt
    exact Finset.mem_filter.mpr ⟨hm, hKn.trans hnm⟩

/-- Divergence above the integer threshold `K`. -/
noncomputable def thresholdDivergenceMass (N K : ℕ) : ℝ :=
  ∑ n ∈ thresholdSet N K, divergence N n

lemma thresholdDivergenceMass_le_extremalMass (N K : ℕ) :
    thresholdDivergenceMass N K ≤ extremalMass N := by
  let U := thresholdSet N K
  have hU : DescendantClosed N U := thresholdSet_closed N K
  have hroots : roots U ⊆ interval N := fun n hn ↦
    hU.1 (Finset.mem_filter.mp hn).1
  have hle := harmonicMass_le_extremalMass hroots (roots_admissible hU)
  rw [harmonicMass_roots_eq_sum_divergence hU] at hle
  exact hle

/-! ### The reciprocal-prime Mertens bridge -/

/-- Error term in the reciprocal-prime Mertens formula. -/
noncomputable def primeReciprocalError (x : ℝ) : ℝ :=
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
    (Real.log (Real.log x) + meissel_mertens)

lemma primeReciprocalError_tendsto :
    Tendsto primeReciprocalError atTop (nhds 0) := by
  have hsmall :
      Asymptotics.IsLittleO atTop primeReciprocalError (fun _ : ℝ ↦ (1 : ℝ)) := by
    exact prime_reciprocal.trans_isLittleO (is_o_log_inv_one one_ne_zero)
  have hdiv := hsmall.tendsto_div_nhds_zero
  simpa only [div_one] using hdiv

/-- Epsilon form of Mertens, uniform for every argument above one common
real threshold. -/
lemma primeReciprocalError_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε := by
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp primeReciprocalError_tendsto ε hε
  refine ⟨X, fun x hx ↦ ?_⟩
  simpa [Real.dist_eq] using hX x hx

/-! ### Child classification above the quarter-power scale -/

lemma rough_multiplier_has_at_most_two_factors {N n t : ℕ}
    (hn : 0 < n) (ht : 1 < t) (hmin : n < t.minFac)
    (hnt : n * t ≤ N) (hscale : N < n ^ 4) :
    t.primeFactorsList.length ≤ 2 := by
  by_contra hlen
  have hthree : 3 ≤ t.primeFactorsList.length := by omega
  generalize hl : t.primeFactorsList = l at hthree
  rcases l with _ | ⟨p, l⟩
  · simp at hthree
  rcases l with _ | ⟨q, l⟩
  · simp at hthree
  rcases l with _ | ⟨r, l⟩
  · simp at hthree
  have hp_mem : p ∈ t.primeFactorsList := by simp [hl]
  have hq_mem : q ∈ t.primeFactorsList := by simp [hl]
  have hr_mem : r ∈ t.primeFactorsList := by simp [hl]
  have hpprime := Nat.prime_of_mem_primeFactorsList hp_mem
  have hqprime := Nat.prime_of_mem_primeFactorsList hq_mem
  have hrprime := Nat.prime_of_mem_primeFactorsList hr_mem
  have hp : n < p := hmin.trans_le
    (Nat.minFac_le_of_dvd hpprime.two_le (Nat.dvd_of_mem_primeFactorsList hp_mem))
  have hq : n < q := hmin.trans_le
    (Nat.minFac_le_of_dvd hqprime.two_le (Nat.dvd_of_mem_primeFactorsList hq_mem))
  have hr : n < r := hmin.trans_le
    (Nat.minFac_le_of_dvd hrprime.two_le (Nat.dvd_of_mem_primeFactorsList hr_mem))
  have hrest : 1 ≤ l.prod := List.one_le_prod fun s hs ↦ by
    have hs_mem : s ∈ t.primeFactorsList := by simp [hl, hs]
    exact (Nat.prime_of_mem_primeFactorsList hs_mem).one_lt.le
  have hprod : p * (q * (r * l.prod)) = t := by
    have ht0 : t ≠ 0 := by omega
    simpa [hl] using Nat.prod_primeFactorsList ht0
  have hpq : n * n ≤ p * q := Nat.mul_le_mul hp.le hq.le
  have hnnpos : 0 < n * n := Nat.mul_pos hn hn
  have hcube₁ : (n * n) * n < (n * n) * r :=
    Nat.mul_lt_mul_of_pos_left hr hnnpos
  have hcube₂ : (n * n) * r ≤ (p * q) * r :=
    Nat.mul_le_mul_right r hpq
  have hcube_pqr : n ^ 3 < p * q * r := by
    simpa [pow_succ, mul_assoc] using hcube₁.trans_le hcube₂
  have hpqr_le : p * q * r ≤ p * (q * (r * l.prod)) := by
    have := Nat.mul_le_mul_left (p * q * r) hrest
    simpa [mul_assoc] using this
  have htbig : n ^ 3 < t := by
    rw [← hprod]
    exact hcube_pqr.trans_le hpqr_le
  have hn4 : n ^ 4 < n * t := by
    have := Nat.mul_lt_mul_of_pos_left htbig hn
    simpa [pow_succ, mul_assoc] using this
  omega

lemma parent_eq_of_maximal_eligible {m n : ℕ} (hm : 1 < m)
    (hn : Eligible m n) (hmax : ∀ d, Eligible m d → d ≤ n) :
    parent m = n := by
  apply Nat.le_antisymm
  · exact hmax _ (parent_eligible hm)
  · exact le_parent_of_eligible hm hn

lemma child_factorization {N n m : ℕ} (hmN : m ≤ N)
    (hscale : N < n ^ 4) (hchild : ParentStep n m) :
    (∃ p : ℕ, p.Prime ∧ n < p ∧ m = n * p) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p ≤ q ∧ m = n * p * q := by
  have hnm : n < m := by
    simpa [hchild.2] using parent_lt hchild.1
  have hn : 0 < n := by
    rw [← hchild.2]
    exact parent_pos hchild.1
  have hrough : RoughLE n m := by
    rw [← hchild.2]
    exact parent_rough hchild.1
  rcases hrough with heq | ⟨t, ht, hmt, hmin⟩
  · exact (ne_of_lt hnm heq).elim
  have hlen : t.primeFactorsList.length ≤ 2 :=
    rough_multiplier_has_at_most_two_factors hn ht hmin (by simpa [hmt] using hmN) hscale
  generalize hl : t.primeFactorsList = l at hlen
  rcases l with _ | ⟨p, l⟩
  · have htprod := Nat.prod_primeFactorsList (by omega : t ≠ 0)
    simp [hl] at htprod
    omega
  rcases l with _ | ⟨q, l⟩
  · left
    have hp_mem : p ∈ t.primeFactorsList := by simp [hl]
    have hpprime := Nat.prime_of_mem_primeFactorsList hp_mem
    have htprod := Nat.prod_primeFactorsList (by omega : t ≠ 0)
    have hpt : p = t := by simpa [hl] using htprod
    refine ⟨p, hpprime, ?_, ?_⟩
    · exact hmin.trans_le (Nat.minFac_le_of_dvd hpprime.two_le
        (Nat.dvd_of_mem_primeFactorsList hp_mem))
    · simpa [hpt, mul_assoc] using hmt
  rcases l with _ | ⟨r, l⟩
  · right
    have hp_mem : p ∈ t.primeFactorsList := by simp [hl]
    have hq_mem : q ∈ t.primeFactorsList := by simp [hl]
    have hpprime := Nat.prime_of_mem_primeFactorsList hp_mem
    have hqprime := Nat.prime_of_mem_primeFactorsList hq_mem
    have htprod := Nat.prod_primeFactorsList (by omega : t ≠ 0)
    have hpqt : p * q = t := by simpa [hl] using htprod
    have hsorted := Nat.primeFactorsList_sorted t
    rw [hl] at hsorted
    have hpq : p ≤ q := by
      change Monotone [p, q].get at hsorted
      let i : Fin [p, q].length := ⟨0, by simp⟩
      let j : Fin [p, q].length := ⟨1, by simp⟩
      have hij : i ≤ j := by simp [i, j]
      simpa [i, j] using hsorted hij
    refine ⟨p, q, hpprime, hqprime, ?_, hpq, ?_⟩
    · exact hmin.trans_le (Nat.minFac_le_of_dvd hpprime.two_le
        (Nat.dvd_of_mem_primeFactorsList hp_mem))
    · simpa [hpqt, mul_assoc] using hmt
  · simp at hlen

lemma prime_extension_is_child {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hnp : n < p) : parent (n * p) = n := by
  have hpgt : 1 < p := hp.one_lt
  have hm : 1 < n * p := by nlinarith
  have hquot : n * p / n = p := Nat.mul_div_cancel_left p hn
  have hel : Eligible (n * p) n :=
    ⟨hn, by nlinarith, dvd_mul_right n p, by simpa [hquot, hp.minFac_eq]⟩
  apply parent_eq_of_maximal_eligible hm hel
  intro d hd
  by_contra hdn
  have hnd : n < d := Nat.lt_of_not_ge hdn
  have hndvd : n ∣ d := eligible_dvd_of_le hel hd hnd.le
  let k := d / n
  have hnk : n * k = d := by simpa [k] using Nat.mul_div_cancel' hndvd
  have hkdvd : k ∣ p := by
    apply Nat.dvd_of_mul_dvd_mul_left hn
    simpa [hnk, mul_assoc] using hd.2.2.1
  rcases hp.eq_one_or_self_of_dvd k hkdvd with hk | hk
  · rw [hk] at hnk
    rw [mul_one] at hnk
    exact (ne_of_lt hnd) hnk
  · rw [hk] at hnk
    exact (ne_of_lt hd.2.1) hnk.symm

lemma two_prime_extension_is_child {n p q : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hq : q.Prime) (hnp : n < p) (hpq : p ≤ q)
    (hbound : n * p * q < n ^ 4) : parent (n * p * q) = n := by
  have hp_le_np : p ≤ n * p := Nat.le_mul_of_pos_left p hn
  have hnp_le_npq : n * p ≤ n * p * q :=
    Nat.le_mul_of_pos_right (n * p) hq.pos
  have hm : 1 < n * p * q := hp.one_lt.trans_le (hp_le_np.trans hnp_le_npq)
  have hquot : n * p * q / n = p * q := by
    simpa [mul_assoc] using Nat.mul_div_cancel_left (p * q) hn
  have hel : Eligible (n * p * q) n := by
    refine ⟨hn, hnp.trans_le (hp_le_np.trans hnp_le_npq),
      ⟨p * q, by simp [mul_assoc]⟩, ?_⟩
    rw [hquot]
    exact lt_minFac_mul hp.one_lt hq.one_lt (by simpa [hp.minFac_eq])
      (hnp.trans_le hpq |>.trans_eq hq.minFac_eq.symm)
  apply parent_eq_of_maximal_eligible hm hel
  intro d hd
  by_contra hdn
  have hnd : n < d := Nat.lt_of_not_ge hdn
  have hndvd : n ∣ d := eligible_dvd_of_le hel hd hnd.le
  let k := d / n
  let s := (n * p * q) / d
  have hnk : n * k = d := by simpa [k] using Nat.mul_div_cancel' hndvd
  have hds : d * s = n * p * q := by
    simpa [s] using Nat.mul_div_cancel' hd.2.2.1
  have hks : k * s = p * q := by
    apply Nat.mul_left_cancel hn
    calc
      n * (k * s) = (n * k) * s := by simp [mul_assoc]
      _ = d * s := by rw [hnk]
      _ = n * p * q := hds
      _ = n * (p * q) := by simp [mul_assoc]
  have hkgt : 1 < k := by
    by_contra h
    have hkle : k ≤ 1 := Nat.le_of_not_gt h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkle with hk0 | hk1
    · rw [hk0] at hnk
      simp at hnk
      omega
    · rw [hk1] at hnk
      rw [mul_one] at hnk
      exact (ne_of_lt hnd) hnk
  let r := k.minFac
  have hrprime : r.Prime := Nat.minFac_prime hkgt.ne'
  have hrdvd : r ∣ p * q := by
    rw [← hks]
    exact dvd_mul_of_dvd_left (Nat.minFac_dvd k) s
  have hpr : p ≤ r := by
    rcases (Nat.Prime.dvd_mul hrprime).mp hrdvd with hrp | hrq
    · rcases hp.eq_one_or_self_of_dvd r hrp with hr1 | hrp'
      · exact (hrprime.ne_one hr1).elim
      · exact hrp'.symm.le
    · rcases hq.eq_one_or_self_of_dvd r hrq with hr1 | hrq'
      · exact (hrprime.ne_one hr1).elim
      · exact hpq.trans hrq'.symm.le
  have hrk : r ≤ k := Nat.minFac_le (by omega)
  have hpk : p ≤ k := hpr.trans hrk
  have hpq_lt_cube : p * q < n ^ 3 := by
    apply (Nat.mul_lt_mul_left hn).mp
    simpa [pow_succ, mul_assoc] using hbound
  have hnq_lt : n * q < p * q := Nat.mul_lt_mul_of_pos_right hnp hq.pos
  have hq_lt_nsq : q < n ^ 2 := by
    apply (Nat.mul_lt_mul_left hn).mp
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      hnq_lt.trans hpq_lt_cube
  have hnsq_lt_np : n ^ 2 < n * p := by
    simpa [pow_two] using (Nat.mul_lt_mul_left hn).mpr hnp
  have hq_lt_d : q < d := by
    rw [← hnk]
    exact hq_lt_nsq.trans hnsq_lt_np |>.trans_le (Nat.mul_le_mul_left n hpk)
  have hs_le_q : s ≤ q := by
    apply Nat.le_of_mul_le_mul_left _ hp.pos
    calc
      p * s ≤ k * s := Nat.mul_le_mul_right s hpk
      _ = p * q := hks
  have hspos : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    rw [hs0] at hds
    simp at hds
    nlinarith [hp.pos, hq.pos]
  have hmin_le : s.minFac ≤ s := Nat.minFac_le hspos
  have hmin_lt_d : s.minFac < d := hmin_le.trans hs_le_q |>.trans_lt hq_lt_d
  have hdmin : d < s.minFac := by simpa [s] using hd.2.2.2
  exact (not_lt_of_ge hmin_lt_d.le) hdmin

lemma child_iff_prime_or_two_prime {N n m : ℕ} (hn : 0 < n)
    (hmN : m ≤ N) (hscale : N < n ^ 4) :
    ParentStep n m ↔
      (∃ p : ℕ, p.Prime ∧ n < p ∧ m = n * p) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p ≤ q ∧ m = n * p * q := by
  constructor
  · exact child_factorization hmN hscale
  · rintro (⟨p, hp, hnp, rfl⟩ | ⟨p, q, hp, hq, hnp, hpq, rfl⟩)
    · refine ⟨?_, prime_extension_is_child hn hp hnp⟩
      have hp_le : p ≤ n * p := Nat.le_mul_of_pos_left p hn
      exact hp.one_lt.trans_le hp_le
    · refine ⟨?_, two_prime_extension_is_child hn hp hq hnp hpq ?_⟩
      · have hp_le_np : p ≤ n * p := Nat.le_mul_of_pos_left p hn
        have hnp_le : n * p ≤ n * p * q := Nat.le_mul_of_pos_right (n * p) hq.pos
        exact hp.one_lt.trans_le (hp_le_np.trans hnp_le)
      · exact hmN.trans_lt hscale

lemma inflow_eq_zero_of_sq_gt {N n : ℕ} (hn : 0 < n) (hscale : N < n * n) :
    inflow N n = 0 := by
  classical
  rw [inflow]
  apply Finset.sum_eq_zero
  intro m hm
  split_ifs with hparent
  · exfalso
    have hmgt : 1 < m := by
      by_contra h
      have hmle : m ≤ 1 := Nat.le_of_not_gt h
      have hpzero := parent_eq_zero_of_le_one hmle
      rw [hparent] at hpzero
      omega
    have hrough : RoughLE n m := by
      rw [← hparent]
      exact parent_rough hmgt
    have hnm : n < m := by simpa [hparent] using parent_lt hmgt
    rcases hrough with heq | ⟨t, ht, hmt, hmin⟩
    · exact (ne_of_lt hnm heq).elim
    have hnt : n < t := hmin.trans_le (Nat.minFac_le (by omega))
    have hsq : n * n < n * t := (Nat.mul_lt_mul_left hn).mpr hnt
    have hmleN := (Finset.mem_Icc.mp hm).2
    omega
  · rfl

lemma divergence_eq_weight_of_sq_gt {N n : ℕ} (hn : 0 < n)
    (hscale : N < n * n) : divergence N n = weight n := by
  simp [divergence, inflow_eq_zero_of_sq_gt hn hscale]

/-- Prime parameters producing one-prime children inside `[1,N]`. -/
def primeIndices (N n : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun p ↦ p.Prime ∧ n < p ∧ n * p ≤ N

/-- Ordered prime pairs producing two-prime children inside `[1,N]`. -/
def primePairIndices (N n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter fun pq ↦
    pq.1.Prime ∧ pq.2.Prime ∧ n < pq.1 ∧ pq.1 ≤ pq.2 ∧ n * pq.1 * pq.2 ≤ N

/-- Children represented by a single prime extension. -/
def primeChildSet (N n : ℕ) : Finset ℕ :=
  (primeIndices N n).image fun p ↦ n * p

/-- Children represented by an ordered pair of prime extensions. -/
def twoPrimeChildSet (N n : ℕ) : Finset ℕ :=
  (primePairIndices N n).image fun pq ↦ n * pq.1 * pq.2

/-- The actual children of `n` in the finite truncation. -/
noncomputable def children (N n : ℕ) : Finset ℕ := by
  classical
  exact (interval N).filter fun m ↦ parent m = n

lemma inflow_eq_sum_children (N n : ℕ) :
    inflow N n = ∑ m ∈ children N n, weight m := by
  classical
  simp [inflow, children, Finset.sum_filter]

lemma ordered_prime_product_injective {p q r s : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≤ q) (hrs : r ≤ s) (hprod : p * q = r * s) :
    p = r ∧ q = s := by
  have hpdvd : p ∣ r * s := by rw [← hprod]; exact dvd_mul_right p q
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with hpr | hps
  · rcases hr.eq_one_or_self_of_dvd p hpr with hp1 | hpr'
    · exact (hp.ne_one hp1).elim
    · subst r
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos hprod⟩
  · rcases hs.eq_one_or_self_of_dvd p hps with hp1 | hps'
    · exact (hp.ne_one hp1).elim
    · have hqs : q = r := by
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        calc
          q * p = p * q := by simp [mul_comm]
          _ = r * s := hprod
          _ = r * p := by rw [hps']
      have hall : p = q := le_antisymm hpq (by simpa [hps', hqs] using hrs)
      exact ⟨by simpa [hqs] using hall, by simpa [hps', hqs] using hall.symm⟩

lemma children_eq_prime_union_twoPrime {N n : ℕ} (hn : 0 < n)
    (hscale : N < n ^ 4) :
    children N n = primeChildSet N n ∪ twoPrimeChildSet N n := by
  classical
  ext m
  simp only [children, Finset.mem_filter, primeChildSet, twoPrimeChildSet,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hmN, hparent⟩
    have hmle : m ≤ N := (Finset.mem_Icc.mp hmN).2
    have hmgt : 1 < m := by
      by_contra h
      have hpzero := parent_eq_zero_of_le_one (Nat.le_of_not_gt h)
      rw [hparent] at hpzero
      omega
    have hchild : ParentStep n m := ⟨hmgt, hparent⟩
    rcases (child_iff_prime_or_two_prime hn hmle hscale).mp hchild with
      ⟨p, hp, hnp, hmp⟩ | ⟨p, q, hp, hq, hnp, hpq, hmpq⟩
    · left
      refine ⟨p, ?_, hmp.symm⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, hp, hnp, ?_⟩
      · have hplem : p ≤ m := Nat.le_of_dvd (by omega) (by rw [hmp]; exact dvd_mul_left p n)
        omega
      · simpa [hmp] using hmle
    · right
      refine ⟨(p, q), ?_, hmpq.symm⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩,
        hp, hq, hnp, hpq, ?_⟩
      · have hpdiv : p ∣ m := by
          rw [hmpq]
          exact ⟨n * q, by ac_rfl⟩
        exact Nat.lt_succ_iff.mpr (Nat.le_of_dvd (by omega) hpdiv |>.trans hmle)
      · have hqdiv : q ∣ m := by
          rw [hmpq]
          exact ⟨n * p, by ac_rfl⟩
        exact Nat.lt_succ_iff.mpr (Nat.le_of_dvd (by omega) hqdiv |>.trans hmle)
      · simpa [hmpq] using hmle
  · rintro (⟨p, hpI, rfl⟩ | ⟨pq, hpqI, rfl⟩)
    · obtain ⟨hpN, hp, hnp, hnpN⟩ := Finset.mem_filter.mp hpI
      refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith [hp.one_lt], hnpN⟩, ?_⟩
      exact prime_extension_is_child hn hp hnp
    · obtain ⟨hpqN, hp, hq, hnp, hpq, hnpqN⟩ := Finset.mem_filter.mp hpqI
      have hp_le_np : pq.1 ≤ n * pq.1 := Nat.le_mul_of_pos_left _ hn
      have hnp_le : n * pq.1 ≤ n * pq.1 * pq.2 :=
        Nat.le_mul_of_pos_right _ hq.pos
      refine ⟨Finset.mem_Icc.mpr
        ⟨(hp.one_lt.trans_le (hp_le_np.trans hnp_le)).le, hnpqN⟩, ?_⟩
      exact two_prime_extension_is_child hn hp hq hnp hpq (hnpqN.trans_lt hscale)

lemma primeChildSet_disjoint_twoPrimeChildSet {N n : ℕ} (hn : 0 < n) :
    Disjoint (primeChildSet N n) (twoPrimeChildSet N n) := by
  classical
  rw [Finset.disjoint_left]
  intro m hm₁ hm₂
  obtain ⟨p, hpI, hpm⟩ := Finset.mem_image.mp hm₁
  obtain ⟨qr, hqrI, hqrm⟩ := Finset.mem_image.mp hm₂
  obtain ⟨hpN, hp, hnp, hnpN⟩ := Finset.mem_filter.mp hpI
  obtain ⟨hqrN, hq, hr, hnq, hqr, hnqrN⟩ := Finset.mem_filter.mp hqrI
  have heq : p = qr.1 * qr.2 := by
    apply Nat.mul_left_cancel hn
    calc
      n * p = m := hpm
      _ = n * qr.1 * qr.2 := hqrm.symm
      _ = n * (qr.1 * qr.2) := by simp [mul_assoc]
  have hqdiv : qr.1 ∣ p := by rw [heq]; exact dvd_mul_right _ _
  rcases hp.eq_one_or_self_of_dvd qr.1 hqdiv with hq1 | hqp
  · exact hq.ne_one hq1
  · have hr1 : qr.2 = 1 := by
      rw [hqp] at heq
      exact (Nat.mul_left_cancel hp.pos (by simpa using heq)).symm
    exact hr.ne_one hr1

/-- Reciprocal-prime mass of the one-prime child parameters. -/
noncomputable def primeChildMass (N n : ℕ) : ℝ :=
  ∑ p ∈ primeIndices N n, (p : ℝ)⁻¹

/-- Reciprocal mass of the ordered two-prime child parameters. -/
noncomputable def twoPrimeChildMass (N n : ℕ) : ℝ :=
  ∑ pq ∈ primePairIndices N n, ((pq.1 : ℝ) * (pq.2 : ℝ))⁻¹

lemma sum_primeChildSet {N n : ℕ} (hn : 0 < n) :
    ∑ m ∈ primeChildSet N n, weight m = weight n * primeChildMass N n := by
  classical
  rw [primeChildSet, Finset.sum_image]
  · rw [primeChildMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [weight, Nat.cast_mul, mul_inv]
  · intro p hp q hq heq
    exact Nat.mul_left_cancel hn heq

lemma sum_twoPrimeChildSet {N n : ℕ} (hn : 0 < n) :
    ∑ m ∈ twoPrimeChildSet N n, weight m = weight n * twoPrimeChildMass N n := by
  classical
  rw [twoPrimeChildSet, Finset.sum_image]
  · rw [twoPrimeChildMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [weight, Nat.cast_mul, mul_inv]
    ring
  · intro pq hpq rs hrs heq
    have hprod : pq.1 * pq.2 = rs.1 * rs.2 := by
      apply Nat.mul_left_cancel hn
      simpa [mul_assoc] using heq
    have hpq_data := (Finset.mem_filter.mp hpq).2
    have hrs_data := (Finset.mem_filter.mp hrs).2
    obtain ⟨hp, hq, hnp, hpqle, hboundpq⟩ := hpq_data
    obtain ⟨hr, hs, hnr, hrsle, hboundrs⟩ := hrs_data
    obtain ⟨hpr, hqs⟩ := ordered_prime_product_injective hp hr hs hpqle hrsle hprod
    exact Prod.ext hpr hqs

lemma inflow_eq_local_formula {N n : ℕ} (hn : 0 < n) (hscale : N < n ^ 4) :
    inflow N n = weight n * (primeChildMass N n + twoPrimeChildMass N n) := by
  rw [inflow_eq_sum_children, children_eq_prime_union_twoPrime hn hscale,
    Finset.sum_union (primeChildSet_disjoint_twoPrimeChildSet hn),
    sum_primeChildSet hn, sum_twoPrimeChildSet hn]
  ring

lemma divergence_eq_local_formula {N n : ℕ} (hn : 0 < n) (hscale : N < n ^ 4) :
    divergence N n =
      weight n * (1 - primeChildMass N n - twoPrimeChildMass N n) := by
  rw [divergence, inflow_eq_local_formula hn hscale]
  ring

/-- Reciprocal-prime summatory function at a natural endpoint. -/
noncomputable def primeReciprocalNat (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, (p : ℝ)⁻¹

lemma primeReciprocalNat_eq_summatory (x : ℕ) :
    primeReciprocalNat x = prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (x : ℝ) := by
  simp [primeReciprocalNat, prime_summatory]

lemma primeIndices_eq_Ioc {N n : ℕ} (hn : 0 < n) :
    primeIndices N n = (Finset.Ioc n (N / n)).filter Nat.Prime := by
  classical
  ext p
  simp only [primeIndices, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpN, hp, hnp, hmul⟩
    refine ⟨⟨hnp, (Nat.le_div_iff_mul_le hn).mpr ?_⟩, hp⟩
    simpa [mul_comm] using hmul
  · rintro ⟨⟨hnp, hpdiv⟩, hp⟩
    have hmul : n * p ≤ N := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hn).mp hpdiv
    have hp_le_N : p ≤ N := by
      exact (Nat.le_of_dvd (Nat.mul_pos hn hp.pos) (dvd_mul_left p n)).trans hmul
    exact ⟨by omega, hp, hnp, hmul⟩

lemma primeReciprocal_Ioc_eq_sub {x y : ℕ} (hxy : x ≤ y) :
    (∑ p ∈ (Finset.Ioc x y).filter Nat.Prime, (p : ℝ)⁻¹) =
      primeReciprocalNat y - primeReciprocalNat x := by
  classical
  let sx : Finset ℕ := (Finset.Icc 1 x).filter Nat.Prime
  let sy : Finset ℕ := (Finset.Icc 1 y).filter Nat.Prime
  have hsub : sx ⊆ sy := by
    intro p hp
    simp only [sx, sy, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hxy⟩, hp.2⟩
  have hdiff : sy \ sx = (Finset.Ioc x y).filter Nat.Prime := by
    ext p
    simp only [sx, sy, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hp1, hpy⟩, hp⟩, hnot⟩
      refine ⟨⟨?_, hpy⟩, hp⟩
      by_contra hpx
      apply hnot
      exact ⟨⟨hp1, Nat.le_of_not_gt hpx⟩, hp⟩
    · rintro ⟨⟨hxp, hpy⟩, hp⟩
      refine ⟨⟨⟨by omega, hpy⟩, hp⟩, ?_⟩
      intro hpsx
      exact (not_le_of_gt hxp) hpsx.1.2
  have hsum := Finset.sum_sdiff (s₁ := sx) (s₂ := sy) hsub
    (f := fun p ↦ (p : ℝ)⁻¹)
  rw [hdiff] at hsum
  simp only [sx, sy] at hsum
  rw [primeReciprocalNat, primeReciprocalNat]
  linarith

lemma primeChildMass_eq_sub {N n : ℕ} (hn : 0 < n) (hsq : n * n ≤ N) :
    primeChildMass N n = primeReciprocalNat (N / n) - primeReciprocalNat n := by
  rw [primeChildMass, primeIndices_eq_Ioc hn]
  apply primeReciprocal_Ioc_eq_sub
  exact (Nat.le_div_iff_mul_le hn).mpr (by simpa [mul_comm] using hsq)

lemma primeReciprocalNat_eq_main_add_error (x : ℕ) :
    primeReciprocalNat x = Real.log (Real.log (x : ℝ)) + meissel_mertens +
      primeReciprocalError (x : ℝ) := by
  rw [primeReciprocalNat_eq_summatory]
  simp only [primeReciprocalError]
  ring

lemma primeReciprocalNat_uniform_error (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ x : ℕ, K ≤ x →
      |primeReciprocalNat x -
        (Real.log (Real.log (x : ℝ)) + meissel_mertens)| < ε := by
  obtain ⟨X, hX⟩ := primeReciprocalError_uniform ε hε
  obtain ⟨K, hK⟩ := exists_nat_ge X
  refine ⟨K, fun x hx ↦ ?_⟩
  rw [primeReciprocalNat_eq_main_add_error]
  ring_nf
  exact hX x (hK.trans (by exact_mod_cast hx))

lemma primeChildMass_loglog_error {N n K : ℕ} (hn : 0 < n)
    (hsq : n * n ≤ N) (hKn : K ≤ n) (hKq : K ≤ N / n)
    {ε : ℝ} (hM : ∀ x : ℕ, K ≤ x →
      |primeReciprocalNat x -
        (Real.log (Real.log (x : ℝ)) + meissel_mertens)| < ε) :
    |primeChildMass N n -
      (Real.log (Real.log (N / n : ℕ)) - Real.log (Real.log (n : ℝ)))| < 2 * ε := by
  rw [primeChildMass_eq_sub hn hsq]
  have h₁ := hM (N / n) hKq
  have h₂ := hM n hKn
  rw [abs_lt] at h₁ h₂ ⊢
  constructor <;> linarith

/-- A natural quotient is exactly the floor of the corresponding real
quotient, so the real-endpoint form of Mertens applies without a rounding
error. -/
lemma primeReciprocalNat_div_eq_summatory (N n : ℕ) :
    primeReciprocalNat (N / n) =
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 ((N : ℝ) / (n : ℝ)) := by
  simp [primeReciprocalNat, prime_summatory, Nat.floor_div_eq_div]

lemma primeChildMass_eq_real_interval {N n : ℕ} (hn : 0 < n)
    (hsq : n * n ≤ N) :
    primeChildMass N n =
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 ((N : ℝ) / (n : ℝ)) -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (n : ℝ) := by
  rw [primeChildMass_eq_sub hn hsq, primeReciprocalNat_div_eq_summatory,
    primeReciprocalNat_eq_summatory]

/-- Uniform Mertens estimate for the one-prime inflow, stated at the exact
real endpoints. -/
lemma primeChildMass_real_loglog_error {N n : ℕ} (hn : 0 < n)
    (hsq : n * n ≤ N) {X ε : ℝ}
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) (hXq : X ≤ (N : ℝ) / (n : ℝ)) :
    |primeChildMass N n -
      (Real.log (Real.log ((N : ℝ) / (n : ℝ))) -
        Real.log (Real.log (n : ℝ)))| < 2 * ε := by
  rw [primeChildMass_eq_real_interval hn hsq]
  have h₁ := hM ((N : ℝ) / (n : ℝ)) hXq
  have h₂ := hM (n : ℝ) hXn
  simp only [primeReciprocalError] at h₁ h₂
  rw [abs_lt] at h₁ h₂ ⊢
  constructor <;> linarith

lemma real_loglog_div_identity {X x : ℝ} (hx : 1 < x) (hX : x < X) :
    Real.log (Real.log (X / x)) - Real.log (Real.log x) =
      Real.log ((1 - Real.log x / Real.log X) /
        (Real.log x / Real.log X)) := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hX0 : X ≠ 0 := ne_of_gt (zero_lt_one.trans (hx.trans hX))
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogX : 0 < Real.log X := Real.log_pos (hx.trans hX)
  have hdiff : 0 < Real.log X - Real.log x := by
    exact sub_pos.mpr (Real.strictMonoOn_log
      (show x ∈ Set.Ioi 0 by exact zero_lt_one.trans hx)
      (show X ∈ Set.Ioi 0 by exact zero_lt_one.trans (hx.trans hX)) hX)
  rw [Real.log_div hX0 hx0]
  have hratio :
      (1 - Real.log x / Real.log X) / (Real.log x / Real.log X) =
        (Real.log X - Real.log x) / Real.log x := by
    field_simp [ne_of_gt hlogX, ne_of_gt hlogx]
  rw [hratio, Real.log_div (ne_of_gt hdiff) (ne_of_gt hlogx)]

lemma real_double_loglog_identity {X n p : ℝ} (hn : 1 < n) (hp : 1 < p)
    (hprod : n * p < X) :
    Real.log (Real.log (X / (n * p))) - Real.log (Real.log p) =
      Real.log ((1 - Real.log n / Real.log X - Real.log p / Real.log X) /
        (Real.log p / Real.log X)) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans hn)
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp)
  have hnp0 : n * p ≠ 0 := mul_ne_zero hn0 hp0
  have honeprod : 1 < n * p := by nlinarith [zero_lt_one.trans hn, hp]
  have hXone : 1 < X := honeprod.trans hprod
  have hX0 : X ≠ 0 := ne_of_gt (zero_lt_one.trans hXone)
  have hlogp : 0 < Real.log p := Real.log_pos hp
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hlogprod : Real.log (n * p) < Real.log X :=
    Real.strictMonoOn_log
      (show n * p ∈ Set.Ioi 0 by exact mul_pos (zero_lt_one.trans hn) (zero_lt_one.trans hp))
      (show X ∈ Set.Ioi 0 by exact zero_lt_one.trans hXone) hprod
  have hdiff : 0 < Real.log X - Real.log n - Real.log p := by
    have hlogmul := Real.log_mul hn0 hp0
    linarith
  rw [Real.log_div hX0 hnp0, Real.log_mul hn0 hp0]
  rw [show Real.log X - (Real.log n + Real.log p) =
      Real.log X - Real.log n - Real.log p by ring]
  have hratio :
      (1 - Real.log n / Real.log X - Real.log p / Real.log X) /
          (Real.log p / Real.log X) =
        (Real.log X - Real.log n - Real.log p) / Real.log p := by
    field_simp [ne_of_gt hlogX, ne_of_gt hlogp]
  rw [hratio, Real.log_div (ne_of_gt hdiff) (ne_of_gt hlogp)]

/-- Outer prime candidates for the ordered two-prime mass. -/
def outerPrimeIndices (N n : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun p ↦ p.Prime ∧ n < p

/-- Inner reciprocal-prime interval corresponding to a fixed outer prime. -/
noncomputable def innerPrimeMass (N n p : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (N + 1)).filter
    (fun q ↦ q.Prime ∧ p ≤ q ∧ n * p * q ≤ N), (q : ℝ)⁻¹

lemma twoPrimeChildMass_eq_iterated (N n : ℕ) :
    twoPrimeChildMass N n =
      ∑ p ∈ outerPrimeIndices N n, (p : ℝ)⁻¹ * innerPrimeMass N n p := by
  classical
  rw [twoPrimeChildMass, primePairIndices, Finset.sum_filter, Finset.sum_product]
  simp only [outerPrimeIndices, innerPrimeMass, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hpN
  by_cases hp : p.Prime ∧ n < p
  · simp only [hp, and_self, if_true]
    apply Finset.sum_congr rfl
    intro q hqN
    by_cases hq : q.Prime ∧ p ≤ q ∧ n * p * q ≤ N
    · simp only [hq, and_self, if_true, mul_inv]
    · have hfalse : ¬(p.Prime ∧ q.Prime ∧ n < p ∧ p ≤ q ∧ n * p * q ≤ N) := by
        tauto
      simp [hq]
  · have hfalse (q : ℕ) :
        ¬(p.Prime ∧ q.Prime ∧ n < p ∧ p ≤ q ∧ n * p * q ≤ N) := by
        tauto
    simp [hp, hfalse]

lemma innerPrimeIndices_eq_Icc {N n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    (Finset.range (N + 1)).filter
      (fun q ↦ q.Prime ∧ p ≤ q ∧ n * p * q ≤ N) =
      (Finset.Icc p (N / (n * p))).filter Nat.Prime := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  have hnp : 0 < n * p := Nat.mul_pos hn hp.pos
  constructor
  · rintro ⟨hqN, hq, hpq, hmul⟩
    refine ⟨⟨hpq, (Nat.le_div_iff_mul_le hnp).mpr ?_⟩, hq⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · rintro ⟨⟨hpq, hqdiv⟩, hq⟩
    have hmul : n * p * q ≤ N := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Nat.le_div_iff_mul_le hnp).mp hqdiv
    have hq_le_N : q ≤ N := by
      have hqdivprod : q ∣ n * p * q := dvd_mul_left q (n * p)
      exact (Nat.le_of_dvd (Nat.mul_pos hnp hq.pos) hqdivprod).trans hmul
    exact ⟨by omega, hq, hpq, hmul⟩

lemma innerPrimeMass_eq_sub {N n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpp : n * p * p ≤ N) :
    innerPrimeMass N n p =
      primeReciprocalNat (N / (n * p)) - primeReciprocalNat (p - 1) := by
  rw [innerPrimeMass, innerPrimeIndices_eq_Icc hn hp]
  have hp_le : p ≤ N / (n * p) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hn hp.pos)).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpp
  have hfin : Finset.Icc p (N / (n * p)) = Finset.Ioc (p - 1) (N / (n * p)) := by
    have hppos : 0 < p := hp.pos
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hfin]
  exact primeReciprocal_Ioc_eq_sub (by omega)

lemma primeReciprocalNat_pred_prime {p : ℕ} (hp : p.Prime) :
    primeReciprocalNat (p - 1) = primeReciprocalNat p - (p : ℝ)⁻¹ := by
  have h := primeReciprocal_Ioc_eq_sub (x := p - 1) (y := p) (by omega)
  have hsum :
      (∑ q ∈ (Finset.Ioc (p - 1) p).filter Nat.Prime, (q : ℝ)⁻¹) =
        (p : ℝ)⁻¹ := by
    apply Finset.sum_eq_single p
    · intro q hq hne
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hq
      have : q = p := by omega
      exact (hne this).elim
    · intro hpnot
      exfalso
      apply hpnot
      simp [hp, hp.pos]
  rw [hsum] at h
  linarith

lemma innerPrimeMass_eq_real_interval {N n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hpp : n * p * p ≤ N) :
    innerPrimeMass N n p =
      prime_summatory (fun q ↦ (q : ℝ)⁻¹) 1
          ((N : ℝ) / ((n : ℝ) * (p : ℝ))) -
        prime_summatory (fun q ↦ (q : ℝ)⁻¹) 1 (p : ℝ) + (p : ℝ)⁻¹ := by
  rw [innerPrimeMass_eq_sub hn hp hpp, primeReciprocalNat_pred_prime hp]
  have hnp : (n : ℝ) * (p : ℝ) = (n * p : ℕ) := by norm_num
  rw [show primeReciprocalNat (N / (n * p)) =
      prime_summatory (fun q ↦ (q : ℝ)⁻¹) 1
        ((N : ℝ) / ((n : ℝ) * (p : ℝ))) by
    rw [hnp]
    exact primeReciprocalNat_div_eq_summatory N (n * p)]
  rw [primeReciprocalNat_eq_summatory]
  ring

lemma innerPrimeMass_real_loglog_error {N n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hpp : n * p * p ≤ N) {X ε : ℝ}
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXp : X ≤ (p : ℝ))
    (hXq : X ≤ (N : ℝ) / ((n : ℝ) * (p : ℝ))) :
    |innerPrimeMass N n p -
      (Real.log (Real.log ((N : ℝ) / ((n : ℝ) * (p : ℝ)))) -
        Real.log (Real.log (p : ℝ)) + (p : ℝ)⁻¹)| < 2 * ε := by
  rw [innerPrimeMass_eq_real_interval hn hp hpp]
  have h₁ := hM ((N : ℝ) / ((n : ℝ) * (p : ℝ))) hXq
  have h₂ := hM (p : ℝ) hXp
  simp only [primeReciprocalError] at h₁ h₂
  rw [abs_lt] at h₁ h₂ ⊢
  constructor <;> linarith

/-- Outer primes for which the inner interval is nonempty. -/
def effectiveOuterPrimeIndices (N n : ℕ) : Finset ℕ :=
  (outerPrimeIndices N n).filter fun p ↦ n * p * p ≤ N

lemma effectiveOuterPrimeIndices_eq_Ioc {N n : ℕ} (hn : 0 < n) :
    effectiveOuterPrimeIndices N n =
      (Finset.Ioc n (Nat.sqrt (N / n))).filter Nat.Prime := by
  classical
  ext p
  simp only [effectiveOuterPrimeIndices, outerPrimeIndices, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Ioc]
  have hmul : n * p * p ≤ N ↔ p ^ 2 ≤ N / n := by
    constructor
    · intro h
      apply (Nat.le_div_iff_mul_le hn).mpr
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
    · intro h
      have := (Nat.le_div_iff_mul_le hn).mp h
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using this
  rw [hmul, Nat.le_sqrt']
  constructor
  · rintro ⟨⟨hpN, hp, hnp⟩, hbound⟩
    exact ⟨⟨hnp, hbound⟩, hp⟩
  · rintro ⟨⟨hnp, hbound⟩, hp⟩
    have hpN : p < N + 1 := by
      have hp_le_Ndiv : p ≤ N / n := by
        exact (show p ≤ p ^ 2 by nlinarith [hp.two_le]).trans hbound
      have hp_le_N : p ≤ N := hp_le_Ndiv.trans (Nat.div_le_self N n)
      omega
    exact ⟨⟨hpN, hp, hnp⟩, hbound⟩

lemma innerPrimeMass_eq_zero_of_lt {N n p : ℕ} (hN : N < n * p * p) :
    innerPrimeMass N n p = 0 := by
  classical
  rw [innerPrimeMass]
  apply Finset.sum_eq_zero
  intro q hq
  simp only [Finset.mem_filter] at hq
  obtain ⟨-, -, hpq, hnpq⟩ := hq
  have hppq : n * p * p ≤ n * p * q := by
    exact Nat.mul_le_mul_left (n * p) hpq
  omega

lemma twoPrimeChildMass_eq_effective_iterated (N n : ℕ) :
    twoPrimeChildMass N n =
      ∑ p ∈ effectiveOuterPrimeIndices N n,
        (p : ℝ)⁻¹ * innerPrimeMass N n p := by
  rw [twoPrimeChildMass_eq_iterated N n]
  classical
  rw [effectiveOuterPrimeIndices, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpp : n * p * p ≤ N
  · simp [hpp]
  · simp [hpp, innerPrimeMass_eq_zero_of_lt (Nat.lt_of_not_ge hpp)]

/-! ### Prime sums on logarithmic bands -/

/-- Reciprocal-prime mass in the real logarithmic band `(N^a,N^b]`. -/
noncomputable def primeBandMass (N : ℕ) (a b : ℝ) : ℝ :=
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 ((N : ℝ) ^ b) -
    prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 ((N : ℝ) ^ a)

lemma primeBandMass_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ ↦ primeBandMass N a b) atTop
      (nhds (Real.log b - Real.log a)) := by
  have hNa : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hNb : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hEa : Tendsto (fun N : ℕ ↦ primeReciprocalError ((N : ℝ) ^ a))
      atTop (nhds 0) := primeReciprocalError_tendsto.comp hNa
  have hEb : Tendsto (fun N : ℕ ↦ primeReciprocalError ((N : ℝ) ^ b))
      atTop (nhds 0) := primeReciprocalError_tendsto.comp hNb
  have hlim : Tendsto
      (fun N : ℕ ↦ (Real.log b - Real.log a) +
        (primeReciprocalError ((N : ℝ) ^ b) -
          primeReciprocalError ((N : ℝ) ^ a))) atTop
      (nhds (Real.log b - Real.log a)) := by
    simpa using
      (tendsto_const_nhds.add (hEb.sub hEa) : Tendsto
        (fun N : ℕ ↦ (Real.log b - Real.log a) +
          (primeReciprocalError ((N : ℝ) ^ b) -
            primeReciprocalError ((N : ℝ) ^ a))) atTop
        (nhds ((Real.log b - Real.log a) + (0 - 0))))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  simp only [primeBandMass, primeReciprocalError]
  rw [Real.log_rpow (zero_lt_one.trans hNR),
    Real.log_rpow (zero_lt_one.trans hNR)]
  rw [Real.log_mul (ne_of_gt hb) (ne_of_gt hlogN),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hlogN)]
  ring

/-- A quantitative Abel-summation lemma.  If a summatory function is
uniformly within `η` of a differentiable model `A`, then testing it against
a nonnegative decreasing function costs at most `η * f k`. -/
lemma partial_summation_uniform_error (a : ℕ → ℝ)
    (f f' A A' : ℝ → ℝ) {k : ℕ} {x η : ℝ}
    (hk : k ≠ 0) (hkx : (k : ℝ) ≤ x)
    (hf : ∀ t ∈ Set.Icc (k : ℝ) x, HasDerivAt f (f' t) t)
    (hA : ∀ t ∈ Set.Icc (k : ℝ) x, HasDerivAt A (A' t) t)
    (hf' : ContinuousOn f' (Set.Icc (k : ℝ) x))
    (hA' : ContinuousOn A' (Set.Icc (k : ℝ) x))
    (hfx : f x = 0)
    (hfnonpos : ∀ t ∈ Set.Icc (k : ℝ) x, f' t ≤ 0)
    (herr : ∀ t ∈ Set.Icc (k : ℝ) x,
      |summatory a k t - A t| ≤ η) :
    |summatory (fun n ↦ a n * f n) k x -
      ((∫ t in (k : ℝ)..x, A' t * f t) + A k * f k)| ≤ η * f k := by
  have hIf' : IntervalIntegrable f' MeasureTheory.volume (k : ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hkx] using hf'
  have hIA' : IntervalIntegrable A' MeasureTheory.volume (k : ℝ) x := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hkx] using hA'
  have hIf : ContinuousOn f (Set.Icc (k : ℝ) x) :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hIA : ContinuousOn A (Set.Icc (k : ℝ) x) :=
    fun t ht ↦ (hA t ht).continuousAt.continuousWithinAt
  have hIAf' : IntervalIntegrable (fun t ↦ A t * f' t)
      MeasureTheory.volume (k : ℝ) x := by
    change IntervalIntegrable (A * f') MeasureTheory.volume (k : ℝ) x
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hkx] using hIA.mul hf'
  have hISf' : IntervalIntegrable (fun t ↦ summatory a k t * f' t)
      MeasureTheory.volume (k : ℝ) x := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hkx).2
    exact partial_summation_integrable (a := a) (x := (k : ℝ)) (y := x)
      (k := k) hf'.integrableOn_Icc
  have hIEf' : IntervalIntegrable
      (fun t ↦ (summatory a k t - A t) * f' t)
      MeasureTheory.volume (k : ℝ) x := by
    have := hISf'.sub hIAf'
    apply this.congr
    intro t ht
    ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (k : ℝ)) (b := x) (u := A) (u' := A') (v := f) (v' := f')
    (fun t ht ↦ hA t (by simpa [Set.uIcc_of_le hkx] using ht))
    (fun t ht ↦ hf t (by simpa [Set.uIcc_of_le hkx] using ht)) hIA' hIf'
  have hsplit :
      (∫ t in (k : ℝ)..x, summatory a k t * f' t) =
        (∫ t in (k : ℝ)..x, A t * f' t) +
          ∫ t in (k : ℝ)..x, (summatory a k t - A t) * f' t := by
    rw [← intervalIntegral.integral_add hIAf' hIEf']
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hps := partial_summation a f f' hk hf hf'.integrableOn_Icc
  have hint_eq :
      (∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t) =
        ∫ t in (k : ℝ)..x, summatory a k t * f' t := by
    rw [intervalIntegral.integral_of_le hkx,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hps' : summatory (fun n ↦ a n * f n) k x =
      summatory a k x * f x -
        ∫ t in (k : ℝ)..x, summatory a k t * f' t := by
    rw [hps, hint_eq]
  have hmain :
      summatory (fun n ↦ a n * f n) k x -
          ((∫ t in (k : ℝ)..x, A' t * f t) + A k * f k) =
        -(∫ t in (k : ℝ)..x, (summatory a k t - A t) * f' t) := by
    rw [hps', hfx, mul_zero, zero_sub, hsplit, hparts, hfx, mul_zero]
    ring
  rw [hmain, abs_neg, ← Real.norm_eq_abs]
  calc
    ‖∫ t in (k : ℝ)..x, (summatory a k t - A t) * f' t‖ ≤
        ∫ t in (k : ℝ)..x, η * (-f' t) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hkx
      · exact Filter.Eventually.of_forall fun t ht ↦ by
          have ht' : t ∈ Set.Icc (k : ℝ) x := ⟨ht.1.le, ht.2⟩
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (hfnonpos t ht')]
          exact mul_le_mul_of_nonneg_right (herr t ht')
            (neg_nonneg.mpr (hfnonpos t ht'))
      · apply ContinuousOn.intervalIntegrable
        change ContinuousOn ((fun _ : ℝ ↦ η) * (-f')) (Set.uIcc (k : ℝ) x)
        simpa [Set.uIcc_of_le hkx] using continuousOn_const.mul hf'.neg
    _ = η * f k := by
      rw [intervalIntegral.integral_const_mul]
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (k : ℝ)) (b := x) (f := f) (f' := f')
        (fun t ht ↦ hf t (by simpa [Set.uIcc_of_le hkx] using ht)) hIf'
      rw [intervalIntegral.integral_neg, hFTC, hfx]
      ring

/-- Smooth form of the logarithmic kernel used in Abel summation. -/
noncomputable def outerKernel (X n t : ℝ) : ℝ :=
  Real.log (Real.log X - Real.log n - Real.log t) - Real.log (Real.log t)

noncomputable def outerKernelDeriv (X n t : ℝ) : ℝ :=
  -(t⁻¹ / (Real.log X - Real.log n - Real.log t)) -
    t⁻¹ / Real.log t

noncomputable def logLogIncrement (n t : ℝ) : ℝ :=
  Real.log (Real.log t) - Real.log (Real.log n)

noncomputable def logLogIncrementDeriv (t : ℝ) : ℝ :=
  t⁻¹ / Real.log t

/-- Logarithmic coordinate with base `X`. -/
noncomputable def logCoord (X t : ℝ) : ℝ := Real.log t / Real.log X

noncomputable def logCoordDeriv (X t : ℝ) : ℝ := t⁻¹ / Real.log X

noncomputable def limitIntegrand (u v : ℝ) : ℝ :=
  v⁻¹ * Real.log ((1 - u - v) / v)

lemma limitLog_bounds {u v : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hv : v ∈ Set.Icc u ((1 - u) / 2)) :
    0 ≤ Real.log ((1 - u - v) / v) ∧
      Real.log ((1 - u - v) / v) ≤ 1 := by
  have hvpos : 0 < v := by linarith [hv.1, hu.1]
  have hratio1 : 1 ≤ (1 - u - v) / v := by
    apply (le_div_iff₀ hvpos).2
    linarith [hv.2]
  have hratio2 : (1 - u - v) / v ≤ 2 := by
    apply (div_le_iff₀ hvpos).2
    linarith [hv.1, hu.1]
  constructor
  · exact Real.log_nonneg hratio1
  · have hmono := Real.strictMonoOn_log.monotoneOn
      (show (1 - u - v) / v ∈ Set.Ioi 0 by
        exact lt_of_lt_of_le zero_lt_one hratio1)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) hratio2
    exact hmono.trans ((Real.log_two_lt_d9).le.trans (by norm_num))

lemma limitIntegrand_bounds {u v : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hv : v ∈ Set.Icc u ((1 - u) / 2)) :
    0 ≤ limitIntegrand u v ∧ limitIntegrand u v ≤ 4 := by
  have hvpos : 0 < v := by linarith [hv.1, hu.1]
  have hlog := limitLog_bounds hu hv
  have hinv : 0 ≤ v⁻¹ ∧ v⁻¹ ≤ 4 := by
    constructor
    · exact inv_nonneg.mpr hvpos.le
    · apply (inv_le_iff_one_le_mul₀ hvpos).2
      linarith [hv.1, hu.1]
  simp only [limitIntegrand]
  exact ⟨mul_nonneg hinv.1 hlog.1,
    (mul_le_mul hinv.2 hlog.2 hlog.1 (by norm_num)).trans_eq (by norm_num)⟩

lemma outerKernel_eq_innerLog {X n t : ℝ} (hX : X ≠ 0)
    (hn : n ≠ 0) (ht : t ≠ 0) :
    outerKernel X n t =
      Real.log (Real.log (X / (n * t))) - Real.log (Real.log t) := by
  rw [outerKernel, Real.log_div hX (mul_ne_zero hn ht), Real.log_mul hn ht]
  congr 2; ring

lemma hasDerivAt_outerKernel {X n t : ℝ} (ht : 1 < t)
    (hinner : 0 < Real.log X - Real.log n - Real.log t) :
    HasDerivAt (outerKernel X n) (outerKernelDeriv X n t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlog := Real.hasDerivAt_log ht0
  have hinside : HasDerivAt
      (fun s : ℝ ↦ Real.log X - Real.log n - Real.log s) (-t⁻¹) t := by
    change HasDerivAt ((fun _ : ℝ ↦ Real.log X - Real.log n) - Real.log) (-t⁻¹) t
    simpa only [zero_sub] using
      (hasDerivAt_const t (Real.log X - Real.log n)).sub hlog
  have hfirst := hinside.log hinner.ne'
  have hsecond := hlog.log hlogt.ne'
  change HasDerivAt
    ((fun y : ℝ ↦ Real.log (Real.log X - Real.log n - Real.log y)) -
      fun y : ℝ ↦ Real.log (Real.log y)) (outerKernelDeriv X n t) t
  simpa only [outerKernelDeriv, neg_div] using hfirst.sub hsecond

lemma hasDerivAt_logLogIncrement {n t : ℝ} (ht : 1 < t) :
    HasDerivAt (logLogIncrement n) (logLogIncrementDeriv t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have hlogt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (Real.hasDerivAt_log ht0).log hlogt
  change HasDerivAt (fun s : ℝ ↦ Real.log (Real.log s) - Real.log (Real.log n))
    (logLogIncrementDeriv t) t
  simpa only [logLogIncrementDeriv] using h.sub_const (Real.log (Real.log n))

lemma hasDerivAt_logCoord {X t : ℝ} (hX : 1 < X) (ht : 1 < t) :
    HasDerivAt (logCoord X) (logCoordDeriv X t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  change HasDerivAt (fun s : ℝ ↦ Real.log s / Real.log X)
    (logCoordDeriv X t) t
  simpa only [logCoordDeriv] using
    (Real.hasDerivAt_log ht0).div_const (Real.log X)

lemma outerKernel_eq_limitLog {X n t : ℝ}
    (hX : 1 < X) (hn : 1 < n) (ht : 1 < t) (hnt : n * t < X) :
    outerKernel X n t =
      Real.log ((1 - logCoord X n - logCoord X t) / logCoord X t) := by
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans hn)
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlognt : Real.log (n * t) < Real.log X :=
    Real.strictMonoOn_log
      (show n * t ∈ Set.Ioi 0 by
        exact mul_pos (zero_lt_one.trans hn) (zero_lt_one.trans ht))
      (show X ∈ Set.Ioi 0 by exact zero_lt_one.trans hX) hnt
  have hinner : 0 < Real.log X - Real.log n - Real.log t := by
    rw [Real.log_mul hn0 ht0] at hlognt
    linarith
  have hratio :
      (Real.log X - Real.log n - Real.log t) / Real.log t =
        (1 - logCoord X n - logCoord X t) / logCoord X t := by
    simp only [logCoord]
    field_simp [ne_of_gt hlogX, ne_of_gt hlogt]
  rw [outerKernel, ← Real.log_div hinner.ne' hlogt.ne', hratio]

lemma outerKernel_eq_limitIntegrand_logCoord {X n t : ℝ}
    (hX : 1 < X) (hn : 1 < n) (ht : 1 < t) (hnt : n * t < X) :
    logLogIncrementDeriv t * outerKernel X n t =
      limitIntegrand (logCoord X n) (logCoord X t) * logCoordDeriv X t := by
  have hX0 : X ≠ 0 := ne_of_gt (zero_lt_one.trans hX)
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogt : 0 < Real.log t := Real.log_pos ht
  rw [outerKernel_eq_limitLog hX hn ht hnt]
  simp only [logLogIncrementDeriv, limitIntegrand, logCoordDeriv, logCoord]
  field_simp [ne_of_gt hlogX, ne_of_gt hlogt]

lemma outerKernel_integral_change_variables {X n a b : ℝ}
    (hX : 1 < X) (hn : 1 < n) (ha : 1 < a) (hab : a ≤ b)
    (hnb : n * b < X) :
    (∫ t in a..b, logLogIncrementDeriv t * outerKernel X n t) =
      ∫ v in logCoord X a..logCoord X b,
        limitIntegrand (logCoord X n) v := by
  have hder : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (logCoord X) (logCoordDeriv X t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    exact hasDerivAt_logCoord hX (ha.trans_le ht'.1)
  have hcontDer : ContinuousOn (logCoordDeriv X) (Set.uIcc a b) := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans (ha.trans_le ht'.1))
    have hlogX : Real.log X ≠ 0 := (Real.log_pos hX).ne'
    unfold logCoordDeriv
    fun_prop
  have hg : ContinuousOn (limitIntegrand (logCoord X n))
      (logCoord X '' Set.uIcc a b) := by
    rintro v ⟨t, ht, rfl⟩
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
    have ht1 : 1 < t := ha.trans_le ht'.1
    have hnt : n * t < X :=
      (mul_le_mul_of_nonneg_left ht'.2 (by positivity)).trans_lt hnb
    have hv : 0 < logCoord X t := div_pos (Real.log_pos ht1) (Real.log_pos hX)
    have hnum : 0 < 1 - logCoord X n - logCoord X t := by
      have hlognt : Real.log (n * t) < Real.log X :=
        Real.strictMonoOn_log
          (show n * t ∈ Set.Ioi 0 by
            exact mul_pos (zero_lt_one.trans hn) (zero_lt_one.trans ht1))
          (show X ∈ Set.Ioi 0 by exact zero_lt_one.trans hX) hnt
      rw [Real.log_mul (by positivity : n ≠ 0) (by positivity : t ≠ 0)] at hlognt
      simp only [logCoord]
      have hlogX := Real.log_pos hX
      rw [show 1 - Real.log n / Real.log X - Real.log t / Real.log X =
          (Real.log X - Real.log n - Real.log t) / Real.log X by
        field_simp [hlogX.ne']]
      exact div_pos (by linarith) hlogX
    unfold limitIntegrand
    apply ContinuousAt.continuousWithinAt
    have hid : ContinuousAt (fun v : ℝ ↦ v) (logCoord X t) := continuousAt_id
    have hinv := hid.inv₀ hv.ne'
    have hnumCont : ContinuousAt
        (fun v : ℝ ↦ 1 - logCoord X n - v) (logCoord X t) := by fun_prop
    have hratio := hnumCont.div hid hv.ne'
    have hlog := hratio.log (div_ne_zero hnum.ne' hv.ne')
    exact hinv.mul hlog
  have hchange := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := logCoord X) (f' := logCoordDeriv X)
    (g := limitIntegrand (logCoord X n)) hder hcontDer hg
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using ht
  have ht1 : 1 < t := ha.trans_le ht'.1
  have hnt : n * t < X :=
    (mul_le_mul_of_nonneg_left ht'.2 (by positivity)).trans_lt hnb
  exact outerKernel_eq_limitIntegrand_logCoord hX hn ht1 hnt

lemma outerKernelDeriv_nonpos {X n t : ℝ} (ht : 1 < t)
    (hinner : 0 < Real.log X - Real.log n - Real.log t) :
    outerKernelDeriv X n t ≤ 0 := by
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr (zero_lt_one.trans ht).le
  have hlog : 0 ≤ Real.log t := (Real.log_pos ht).le
  simp only [outerKernelDeriv]
  exact add_nonpos (neg_nonpos.mpr (div_nonneg htinv hinner.le))
    (neg_nonpos.mpr (div_nonneg htinv hlog))

lemma summatory_prime_from_succ {n : ℕ} {x : ℝ}
    (hx : (n + 1 : ℕ) ≤ ⌊x⌋₊) :
    summatory (fun m : ℕ ↦ if m.Prime then (m : ℝ)⁻¹ else 0) (n + 1) x =
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (n : ℝ) := by
  classical
  rw [summatory, ← Finset.sum_filter, prime_summatory, prime_summatory]
  have hfin : Finset.Icc (n + 1) ⌊x⌋₊ = Finset.Ioc n ⌊x⌋₊ := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hfin]
  have hsub : n ≤ ⌊x⌋₊ := by omega
  have h := primeReciprocal_Ioc_eq_sub hsub
  simpa [primeReciprocalNat, prime_summatory] using h

/-- Real upper endpoint for the outer prime in a two-prime child. -/
noncomputable def outerEndpoint (N n : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) / (n : ℝ))

lemma nat_mul_sq_le_iff_le_outerEndpoint {N n p : ℕ} (hn : 0 < n) :
    n * p * p ≤ N ↔ (p : ℝ) ≤ outerEndpoint N n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq0 : 0 ≤ (N : ℝ) / (n : ℝ) := div_nonneg (by positivity) hnR.le
  constructor
  · intro h
    rw [outerEndpoint, Real.le_sqrt (by positivity) hq0]
    apply (le_div_iff₀ hnR).2
    norm_num only [sq, Nat.cast_mul]
    exact_mod_cast (by simpa [mul_assoc, mul_comm, mul_left_comm] using h)
  · intro h
    have hsquare : (p : ℝ) ^ 2 ≤ (N : ℝ) / (n : ℝ) := by
      calc
        (p : ℝ) ^ 2 ≤ (outerEndpoint N n) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by
            exact Real.sqrt_nonneg _)).2 h
        _ = (N : ℝ) / (n : ℝ) := by
          rw [outerEndpoint, Real.sq_sqrt hq0]
    have hmulR : (n : ℝ) * ((p : ℝ) ^ 2) ≤ (N : ℝ) := by
      simpa [mul_comm] using (le_div_iff₀ hnR).1 hsquare
    have hcast : ((n * p * p : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa [pow_two, mul_assoc] using hmulR
    exact_mod_cast hcast

lemma effectiveOuterPrimeIndices_eq_floorEndpoint {N n : ℕ} (hn : 0 < n) :
    effectiveOuterPrimeIndices N n =
      (Finset.Icc (n + 1) ⌊outerEndpoint N n⌋₊).filter Nat.Prime := by
  classical
  ext p
  simp only [effectiveOuterPrimeIndices, outerPrimeIndices, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  rw [nat_mul_sq_le_iff_le_outerEndpoint hn]
  have hfloor : (p : ℝ) ≤ outerEndpoint N n ↔ p ≤ ⌊outerEndpoint N n⌋₊ := by
    exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).symm
  rw [hfloor]
  constructor
  · rintro ⟨⟨hpN, hp, hnp⟩, hpB⟩
    exact ⟨⟨by omega, hpB⟩, hp⟩
  · rintro ⟨⟨hpn, hpB⟩, hp⟩
    have hp_le_N : p ≤ N := by
      have hmul : n * p * p ≤ N :=
        (nat_mul_sq_le_iff_le_outerEndpoint hn).2 (hfloor.mpr hpB)
      have hp_le_np : p ≤ n * p := Nat.le_mul_of_pos_left p hn
      have hnp_le_npp : n * p ≤ n * p * p :=
        Nat.le_mul_of_pos_right (n * p) hp.pos
      exact hp_le_np.trans hnp_le_npp |>.trans hmul
    exact ⟨⟨by omega, hp, by omega⟩, hpB⟩

lemma effectiveOuter_sum_eq_summatory {N n : ℕ} (hn : 0 < n) :
    (∑ p ∈ effectiveOuterPrimeIndices N n,
        (p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p) =
      summatory
        (fun p : ℕ ↦ (if p.Prime then (p : ℝ)⁻¹ else 0) *
          outerKernel (N : ℝ) (n : ℝ) p)
        (n + 1) (outerEndpoint N n) := by
  classical
  rw [effectiveOuterPrimeIndices_eq_floorEndpoint hn, summatory]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> simp [hprime]

lemma effectiveOuter_reciprocal_sum_eq_summatory {N n : ℕ} (hn : 0 < n) :
    (∑ p ∈ effectiveOuterPrimeIndices N n, (p : ℝ)⁻¹) =
      summatory (fun p : ℕ ↦ if p.Prime then (p : ℝ)⁻¹ else 0)
        (n + 1) (outerEndpoint N n) := by
  classical
  rw [effectiveOuterPrimeIndices_eq_floorEndpoint hn, summatory]
  rw [Finset.sum_filter]

lemma effectiveOuter_square_sum_le {N n : ℕ} (hn : 0 < n) :
    (∑ p ∈ effectiveOuterPrimeIndices N n, ((p : ℝ) ^ 2)⁻¹) ≤ (n : ℝ)⁻¹ := by
  classical
  let M := max n (Nat.sqrt (N / n))
  calc
    (∑ p ∈ effectiveOuterPrimeIndices N n, ((p : ℝ) ^ 2)⁻¹) ≤
        ∑ p ∈ Finset.Ioc n M, ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · rw [effectiveOuterPrimeIndices_eq_Ioc hn]
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).1
        have hpI := Finset.mem_Ioc.mp hp'
        exact Finset.mem_Ioc.mpr ⟨hpI.1, hpI.2.trans (le_max_right _ _)⟩
      · intro p hp hnot
        positivity
    _ ≤ (n : ℝ)⁻¹ - (M : ℝ)⁻¹ :=
      sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
    _ ≤ (n : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (by positivity))

lemma outerEndpoint_geometry {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n) :
    1 < (N : ℝ) ∧
      (n : ℝ) * outerEndpoint N n < (N : ℝ) ∧
      logCoord (N : ℝ) (outerEndpoint N n) =
        (1 - logCoord (N : ℝ) (n : ℝ)) / 2 := by
  let B := outerEndpoint N n
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnB : (n : ℝ) < B := by
    exact (show (n : ℝ) < ((n + 1 : ℕ) : ℝ) by norm_num).trans_le hendpoint
  have hBpos : 0 < B := (zero_lt_one.trans hnR).trans hnB
  have hqpos : 0 < (N : ℝ) / (n : ℝ) := by
    have hsqrt : Real.sqrt ((N : ℝ) / (n : ℝ)) = B := by rfl
    have hq0 : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
    have hsquare := Real.sq_sqrt hq0
    rw [hsqrt] at hsquare
    nlinarith
  have hNR : 0 < (N : ℝ) := by
    rcases div_pos_iff.mp hqpos with h | h
    · exact h.1
    · have : 0 ≤ (n : ℝ) := by positivity
      linarith [h.2]
  have hBsq : B ^ 2 = (N : ℝ) / (n : ℝ) := by
    change (Real.sqrt ((N : ℝ) / (n : ℝ))) ^ 2 = _
    exact Real.sq_sqrt hqpos.le
  have hqgt : 1 < (N : ℝ) / (n : ℝ) := by
    rw [← hBsq]
    nlinarith
  have hnN : (n : ℝ) < (N : ℝ) := by
    simpa using (lt_div_iff₀ (by positivity : (0 : ℝ) < n)).1 hqgt
  have hNone : 1 < (N : ℝ) := hnR.trans hnN
  have hnB_lt : (n : ℝ) * B < (N : ℝ) := by
    have hBltq : B < (N : ℝ) / (n : ℝ) := by
      rw [← hBsq]
      nlinarith
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < n)).1 hBltq
    simpa [mul_comm] using this
  have hlogeq : Real.log (N : ℝ) - Real.log (n : ℝ) = 2 * Real.log B := by
    have hdiv := Real.log_div (ne_of_gt hNR) (by positivity : (n : ℝ) ≠ 0)
    have hpow := Real.log_pow B 2
    rw [← hBsq] at hdiv
    calc
      Real.log (N : ℝ) - Real.log (n : ℝ) = Real.log (B ^ 2) := hdiv.symm
      _ = 2 * Real.log B := by simp [Real.log_pow]
  refine ⟨hNone, hnB_lt, ?_⟩
  simp only [logCoord]
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNone).ne'
  field_simp [hlogN]
  linarith

lemma effectiveOuter_reciprocal_sum_le_three {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    (hu : logCoord (N : ℝ) (n : ℝ) ∈
      Set.Icc ((1 : ℝ) / 4) (1 / 3))
    {X ε : ℝ} (hε1 : ε ≤ 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ ε)
    (hXn : X ≤ (n : ℝ)) :
    (∑ p ∈ effectiveOuterPrimeIndices N n, (p : ℝ)⁻¹) ≤ 3 := by
  have hg := outerEndpoint_geometry hn hendpoint
  have hN := hg.1
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hB1 : 1 < outerEndpoint N n := hnR.trans
    ((show (n : ℝ) < (n + 1 : ℕ) by norm_num).trans_le hendpoint)
  have hfloor : n + 1 ≤ ⌊outerEndpoint N n⌋₊ := by
    exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).2 hendpoint
  rw [effectiveOuter_reciprocal_sum_eq_summatory (by omega),
    summatory_prime_from_succ hfloor]
  have hXB : X ≤ outerEndpoint N n := hXn.trans
    ((show (n : ℝ) < (n + 1 : ℕ) by norm_num).le.trans hendpoint)
  have hEB := hM (outerEndpoint N n) hXB
  have hEn := hM (n : ℝ) hXn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN
  have hcoord : logCoord (N : ℝ) (outerEndpoint N n) ≤
      2 * logCoord (N : ℝ) (n : ℝ) := by
    rw [hg.2.2]
    linarith [hu.1]
  have hlogcomp : Real.log (outerEndpoint N n) ≤ 2 * Real.log (n : ℝ) := by
    apply (div_le_div_iff_of_pos_right hlogN).mp
    calc
      Real.log (outerEndpoint N n) / Real.log (N : ℝ) ≤
          2 * (Real.log (n : ℝ) / Real.log (N : ℝ)) := by
        simpa only [logCoord] using hcoord
      _ = (2 * Real.log (n : ℝ)) / Real.log (N : ℝ) := by ring
  have hratio : Real.log (outerEndpoint N n) / Real.log (n : ℝ) ≤ 2 := by
    exact (div_le_iff₀ (Real.log_pos hnR)).2 hlogcomp
  have hmain : logLogIncrement (n : ℝ) (outerEndpoint N n) ≤ 1 := by
    rw [logLogIncrement, ← Real.log_div (Real.log_pos hB1).ne'
      (Real.log_pos hnR).ne']
    have hratioPos : 0 < Real.log (outerEndpoint N n) / Real.log (n : ℝ) :=
      div_pos (Real.log_pos hB1) (Real.log_pos hnR)
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show Real.log (outerEndpoint N n) / Real.log (n : ℝ) ∈ Set.Ioi 0 by
        exact hratioPos)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) hratio
    exact hmono.trans ((Real.log_two_lt_d9).le.trans (by norm_num))
  have hdecomp :
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (outerEndpoint N n) -
          prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (n : ℝ) =
        logLogIncrement (n : ℝ) (outerEndpoint N n) +
          primeReciprocalError (outerEndpoint N n) -
          primeReciprocalError (n : ℝ) := by
    simp only [primeReciprocalError, logLogIncrement]
    ring
  rw [hdecomp]
  rw [abs_le] at hEB hEn
  linarith

lemma outerKernel_integral_eq_profile_tail {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n) :
    (∫ t in ((n + 1 : ℕ) : ℝ)..outerEndpoint N n,
        logLogIncrementDeriv t * outerKernel (N : ℝ) (n : ℝ) t) =
      ∫ v in logCoord (N : ℝ) (n + 1 : ℕ)..
          (1 - logCoord (N : ℝ) (n : ℝ)) / 2,
        limitIntegrand (logCoord (N : ℝ) (n : ℝ)) v := by
  have hg := outerEndpoint_geometry hn hendpoint
  rw [← hg.2.2]
  exact outerKernel_integral_change_variables hg.1
    (by exact_mod_cast hn) (by exact_mod_cast hn.trans (Nat.lt_add_one n))
    hendpoint hg.2.1

lemma logCoord_succ_sub_bounds {X : ℝ} {n : ℕ} (hX : 1 ≤ Real.log X)
    (hn : 0 < n) :
    0 ≤ logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ) ∧
      logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ) ≤ (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsuccR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlogX : 0 < Real.log X := zero_lt_one.trans_le hX
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) :=
    Real.strictMonoOn_log.monotoneOn (show (n : ℝ) ∈ Set.Ioi 0 by exact hnR)
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by exact hsuccR) (by norm_num)
  have hlogdiff : Real.log (n + 1 : ℕ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
    have hqpos : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := div_pos hsuccR hnR
    have hbound := Real.log_le_sub_one_of_pos hqpos
    rw [Real.log_div hsuccR.ne' hnR.ne'] at hbound
    have hquot : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = (n : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    linarith
  simp only [logCoord]
  constructor
  · rw [show Real.log (n + 1 : ℕ) / Real.log X -
        Real.log (n : ℝ) / Real.log X =
        (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log X by ring]
    exact div_nonneg (sub_nonneg.mpr hlogmono) hlogX.le
  · calc
      (Real.log (n + 1 : ℕ) / Real.log X -
          Real.log (n : ℝ) / Real.log X) =
          (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log X := by ring
      _ ≤ (n : ℝ)⁻¹ / Real.log X :=
        div_le_div_of_nonneg_right hlogdiff hlogX.le
      _ ≤ (n : ℝ)⁻¹ := by
        exact (div_le_iff₀ hlogX).2 (by
          have hinv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
          nlinarith)

lemma logLogIncrement_succ_bounds {n : ℕ} (hn : 0 < n)
    (hlogn : 1 ≤ Real.log (n : ℝ)) :
    0 ≤ logLogIncrement (n : ℝ) (n + 1 : ℕ) ∧
      logLogIncrement (n : ℝ) (n + 1 : ℕ) ≤ (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hkR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlogn0 : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlogn
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) :=
    Real.strictMonoOn_log.monotoneOn (show (n : ℝ) ∈ Set.Ioi 0 by exact hnR)
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by exact hkR) (by norm_num)
  have houter : Real.log (Real.log (n + 1 : ℕ)) -
      Real.log (Real.log (n : ℝ)) ≤
      (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    have hratio : 0 < Real.log (n + 1 : ℕ) / Real.log (n : ℝ) :=
      div_pos (hlogn0.trans_le hlogmono) hlogn0
    have h := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (hlogn0.trans_le hlogmono |>.ne') hlogn0.ne'] at h
    have heq : Real.log (n + 1 : ℕ) / Real.log (n : ℝ) - 1 =
        (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ) := by
      field_simp [hlogn0.ne']
    linarith
  have hinner : Real.log (n + 1 : ℕ) - Real.log (n : ℝ) ≤ (n : ℝ)⁻¹ := by
    have hqpos : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := div_pos hkR hnR
    have h := Real.log_le_sub_one_of_pos hqpos
    rw [Real.log_div hkR.ne' hnR.ne'] at h
    have hquot : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = (n : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    linarith
  simp only [logLogIncrement]
  constructor
  · exact sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn
      (show Real.log (n : ℝ) ∈ Set.Ioi 0 by exact hlogn0)
      (show Real.log (n + 1 : ℕ) ∈ Set.Ioi 0 by exact hlogn0.trans_le hlogmono)
      hlogmono)
  · calc
      _ ≤ (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) /
          Real.log (n : ℝ) := houter
      _ ≤ (n : ℝ)⁻¹ / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hinner hlogn0.le
      _ ≤ (n : ℝ)⁻¹ := (div_le_iff₀ hlogn0).2 (by
        have hinv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnR.le
        nlinarith)

lemma logCoord_succ_sub_lower {X : ℝ} {n : ℕ}
    (hX : 0 < Real.log X) (hn : 0 < n) :
    (((n + 1 : ℕ) : ℝ)⁻¹ / Real.log X) ≤
      logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hratio : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := div_pos hsR hnR
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  rw [Real.log_div hsR.ne' hnR.ne'] at hlog
  have halg :
      1 - ((((n + 1 : ℕ) : ℝ) / (n : ℝ))⁻¹) =
        ((n + 1 : ℕ) : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [halg] at hlog
  simp only [logCoord]
  rw [show Real.log (n + 1 : ℕ) / Real.log X -
      Real.log (n : ℝ) / Real.log X =
        (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log X by ring]
  exact div_le_div_of_nonneg_right hlog hX.le

lemma logCoord_succ_sub_upper_exact {X : ℝ} {n : ℕ}
    (hX : 0 < Real.log X) (hn : 0 < n) :
    logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ) ≤
      (n : ℝ)⁻¹ / Real.log X := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsR : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hratio : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := div_pos hsR hnR
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hsR.ne' hnR.ne'] at hlog
  have halg : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = (n : ℝ)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [halg] at hlog
  simp only [logCoord]
  rw [show Real.log (n + 1 : ℕ) / Real.log X -
      Real.log (n : ℝ) / Real.log X =
        (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log X by ring]
  exact div_le_div_of_nonneg_right hlog hX.le

lemma harmonicCoeff_sub_logCell_bounds {X : ℝ} {n : ℕ}
    (hX : 1 ≤ Real.log X) (hn : 0 < n) :
    0 ≤ (n : ℝ)⁻¹ / Real.log X -
        (logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ)) ∧
      (n : ℝ)⁻¹ / Real.log X -
          (logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ)) ≤
        ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) / Real.log X := by
  have hXpos : 0 < Real.log X := zero_lt_one.trans_le hX
  have hu := logCoord_succ_sub_upper_exact hXpos hn
  have hl := logCoord_succ_sub_lower hXpos hn
  constructor
  · apply sub_nonneg.mpr
    exact hu
  · calc
      (n : ℝ)⁻¹ / Real.log X -
          (logCoord X (n + 1 : ℕ) - logCoord X (n : ℝ)) ≤
          (n : ℝ)⁻¹ / Real.log X -
            ((n + 1 : ℕ) : ℝ)⁻¹ / Real.log X := sub_le_sub_left hl _
      _ = ((n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹) / Real.log X := by ring

noncomputable def logHarmonicRiemannSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    f (logCoord (N : ℝ) ((k + 1 : ℕ) : ℝ)) *
      (((k + 1 : ℕ) : ℝ)⁻¹ / Real.log (N : ℝ))

lemma logCoord_cells_in_unit_two {N k : ℕ} (hN : 3 ≤ N) (hk : k < N) :
    logCoord (N : ℝ) ((k + 1 : ℕ) : ℝ) ∈ Set.Icc 0 2 ∧
      logCoord (N : ℝ) ((k + 2 : ℕ) : ℝ) ∈ Set.Icc 0 2 := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have bound (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ N + 1) :
      logCoord (N : ℝ) (m : ℝ) ∈ Set.Icc 0 2 := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
    have hN1sq : N + 1 ≤ N ^ 2 := by nlinarith
    have hmN2 : (m : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hm.trans hN1sq
    have hlogle := Real.strictMonoOn_log.monotoneOn
      (show (m : ℝ) ∈ Set.Ioi 0 by exact hmpos)
      (show (N : ℝ) ^ 2 ∈ Set.Ioi 0 by
        change 0 < (N : ℝ) ^ 2
        positivity) hmN2
    rw [Real.log_pow] at hlogle
    have hlogle' : Real.log (m : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      simpa using hlogle
    exact ⟨div_nonneg hlogm0 hlogN.le,
      (div_le_iff₀ hlogN).2 hlogle'⟩
  exact ⟨bound (k + 1) (by omega) (by omega),
    bound (k + 2) (by omega) (by omega)⟩

theorem harmonic_log_riemann {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (logHarmonicRiemannSum f) atTop
      (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfOn : ContinuousOn f (Set.Icc (0 : ℝ) 2) := hf.continuousOn
  have huc : UniformContinuousOn f (Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hfOn
  rcases (Metric.uniformContinuousOn_iff.mp huc) (ε / 8) (by positivity) with
    ⟨δ, hδ, hδf⟩
  have hfabs : ContinuousOn (fun x : ℝ ↦ |f x|) (Set.Icc (0 : ℝ) 2) :=
    hfOn.abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hfabs)
  have hCbound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 2) : |f x| ≤ C :=
    hC _ (Set.mem_image_of_mem _ hx)
  have hC0 : 0 ≤ C := (abs_nonneg (f 0)).trans (hCbound 0 (by norm_num))
  let R : ℝ := max 1 (max (δ⁻¹ + 1) (8 * C / ε + 1))
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := (tendsto_atTop_atTop.mp hlogTop) R
  refine ⟨max 3 N₀, fun N hN ↦ ?_⟩
  have hN3 : 3 ≤ N := (le_max_left 3 N₀).trans hN
  have hlogR : R ≤ Real.log (N : ℝ) := hN₀ N ((le_max_right 3 N₀).trans hN)
  have hlog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hlogR
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog1
  have hinvδ : (Real.log (N : ℝ))⁻¹ < δ := by
    have hRδ : δ⁻¹ + 1 ≤ Real.log (N : ℝ) :=
      (le_max_left (δ⁻¹ + 1) (8 * C / ε + 1)).trans
        ((le_max_right 1 _).trans hlogR)
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hlogpos).2
    have hmul := mul_le_mul_of_nonneg_left hRδ hδ.le
    have hcancel := inv_mul_cancel₀ hδ.ne'
    nlinarith
  have hClog : C / Real.log (N : ℝ) < ε / 8 := by
    have hRε : 8 * C / ε + 1 ≤ Real.log (N : ℝ) :=
      (le_max_right (δ⁻¹ + 1) (8 * C / ε + 1)).trans
        ((le_max_right 1 _).trans hlogR)
    apply (div_lt_iff₀ hlogpos).2
    have hεpos : 0 < ε := hε
    have hstrict : 8 * C / ε < Real.log (N : ℝ) :=
      (lt_add_one (8 * C / ε)).trans_le hRε
    have hmain : 8 * C < ε * Real.log (N : ℝ) := by
      have := (div_lt_iff₀ hεpos).mp hstrict
      nlinarith
    nlinarith
  let a : ℕ → ℝ := fun k ↦ logCoord (N : ℝ) ((k + 1 : ℕ) : ℝ)
  have hcell (k : ℕ) (hk : k < N) :
      ‖(∫ x in a k..a (k + 1), f (a k) - f x)‖ ≤
        (ε / 8) * (a (k + 1) - a k) := by
    have hcells := logCoord_cells_in_unit_two hN3 hk
    have horder : a k ≤ a (k + 1) := by
      exact (logCoord_succ_sub_bounds hlog1 (by omega : 0 < k + 1)).1 |> sub_nonneg.mp
    calc
      ‖(∫ x in a k..a (k + 1), f (a k) - f x)‖ ≤
          (ε / 8) * |a (k + 1) - a k| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        simp only [Set.uIoc_of_le horder] at hx
        have hxI : x ∈ Set.Icc (0 : ℝ) 2 :=
          ⟨hcells.1.1.trans hx.1.le, hx.2.trans hcells.2.2⟩
        rw [Real.norm_eq_abs]
        exact le_of_lt (hδf (a k) hcells.1 x hxI (by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
          simp only [neg_sub]
          calc
            x - a k ≤ a (k + 1) - a k := sub_le_sub_right hx.2 _
            _ ≤ ((k + 1 : ℕ) : ℝ)⁻¹ / Real.log (N : ℝ) :=
              logCoord_succ_sub_upper_exact hlogpos (by omega)
            _ ≤ (Real.log (N : ℝ))⁻¹ := by
              rw [div_eq_mul_inv]
              exact mul_le_of_le_one_left (by
                exact inv_nonneg.mpr hlogpos.le) (by
                apply (inv_le_one₀ (by
                  exact_mod_cast (show 0 < k + 1 by omega) :
                    (0 : ℝ) < ((k + 1 : ℕ) : ℝ))).2
                exact_mod_cast (show 1 ≤ k + 1 by omega))
            _ < δ := hinvδ))
      _ = (ε / 8) * (a (k + 1) - a k) := by
        rw [abs_of_nonneg (sub_nonneg.mpr horder)]
  have ha0 : a 0 = 0 := by simp [a, logCoord]
  have hNpos : 0 < N := by omega
  have haNmem : a N ∈ Set.Icc (0 : ℝ) 2 := by
    have hc := (logCoord_cells_in_unit_two hN3 (k := N - 1) (by omega)).2
    convert hc using 1; simp only [a]; congr 2; norm_num; omega
  have hsumint :
      ∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), f x =
        ∫ x in a 0..a N, f x := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (f := f) (n := N) (fun k hk ↦ hf.intervalIntegrable _ _)
  let Q := ∑ k ∈ Finset.range N,
    f (a k) * (a (k + 1) - a k)
  have hQ : |Q - ∫ x in (0 : ℝ)..a N, f x| ≤ ε / 4 := by
    have hrewrite : Q - ∫ x in (0 : ℝ)..a N, f x =
        ∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), f (a k) - f x := by
      rw [← ha0, ← hsumint]
      dsimp only [Q]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [hrewrite, ← Real.norm_eq_abs]
    calc
      ‖∑ k ∈ Finset.range N, ∫ x in a k..a (k + 1), f (a k) - f x‖ ≤
          ∑ k ∈ Finset.range N,
            ‖∫ x in a k..a (k + 1), f (a k) - f x‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (ε / 8) * (a (k + 1) - a k) := by
        exact Finset.sum_le_sum fun k hk ↦ hcell k (Finset.mem_range.mp hk)
      _ = (ε / 8) * (a N - a 0) := by
        rw [← Finset.mul_sum]
        congr 1
        simpa using Finset.sum_Ico_sub a (Nat.zero_le N)
      _ ≤ (ε / 8) * 2 := by
        gcongr
        linarith [haNmem.2, ha0]
      _ = ε / 4 := by ring
  have htel :
      (∑ k ∈ Finset.range N,
        (((k + 1 : ℕ) : ℝ)⁻¹ - ((k + 2 : ℕ) : ℝ)⁻¹)) =
        1 - (((N + 1 : ℕ) : ℝ)⁻¹) := by
    have hs := Finset.sum_Ico_sub (fun m : ℕ ↦ (m : ℝ)⁻¹)
      (show 1 ≤ N + 1 by omega)
    rw [Finset.sum_Ico_eq_sum_range] at hs
    norm_num at hs
    rw [Finset.sum_sub_distrib]
    have hs' :
        (∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ)⁻¹) -
          ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹ =
            (((N + 1 : ℕ) : ℝ)⁻¹) - 1 := by
      calc
        (∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ)⁻¹) -
            ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹ =
            (∑ k ∈ Finset.range N, (1 + (k : ℝ) + 1)⁻¹) -
              ∑ k ∈ Finset.range N, (1 + (k : ℝ))⁻¹ := by
                congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;>
                  congr 1 <;> push_cast <;> ring
        _ = (((N + 1 : ℕ) : ℝ)⁻¹) - 1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using hs
    linarith
  have hHQ : |logHarmonicRiemannSum f N - Q| ≤ C / Real.log (N : ℝ) := by
    have heq : logHarmonicRiemannSum f N - Q =
        ∑ k ∈ Finset.range N, f (a k) *
          ((((k + 1 : ℕ) : ℝ)⁻¹ / Real.log (N : ℝ)) -
            (a (k + 1) - a k)) := by
      rw [logHarmonicRiemannSum]
      dsimp only [Q, a]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [heq]
    calc
      |∑ k ∈ Finset.range N, f (a k) *
          ((((k + 1 : ℕ) : ℝ)⁻¹ / Real.log (N : ℝ)) -
            (a (k + 1) - a k))| ≤
          ∑ k ∈ Finset.range N, |f (a k) *
            ((((k + 1 : ℕ) : ℝ)⁻¹ / Real.log (N : ℝ)) -
              (a (k + 1) - a k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, C *
          (((k + 1 : ℕ) : ℝ)⁻¹ - ((k + 2 : ℕ) : ℝ)⁻¹) /
            Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hcells := logCoord_cells_in_unit_two hN3 (Finset.mem_range.mp hk)
        have hb := harmonicCoeff_sub_logCell_bounds hlog1 (by omega : 0 < k + 1)
        rw [abs_mul, abs_of_nonneg hb.1]
        calc
          |f (a k)| *
              ((↑(k + 1))⁻¹ / Real.log (N : ℝ) - (a (k + 1) - a k)) ≤
              C * ((↑(k + 1))⁻¹ / Real.log (N : ℝ) -
                (a (k + 1) - a k)) :=
            mul_le_mul_of_nonneg_right (hCbound (a k) hcells.1) hb.1
          _ ≤ C * (((↑(k + 1))⁻¹ - (↑(k + 2))⁻¹) /
                Real.log (N : ℝ)) := mul_le_mul_of_nonneg_left hb.2 hC0
          _ = C * ((↑(k + 1))⁻¹ - (↑(k + 2))⁻¹) /
                Real.log (N : ℝ) := by ring
      _ = C * (1 - (((N + 1 : ℕ) : ℝ)⁻¹)) / Real.log (N : ℝ) := by
        rw [← Finset.sum_div, ← Finset.mul_sum, htel]
      _ ≤ C / Real.log (N : ℝ) := by
        apply (div_le_div_iff_of_pos_right hlogpos).2
        nlinarith [show 0 ≤ (((N + 1 : ℕ) : ℝ)⁻¹) by positivity]
  have haN1 : 1 ≤ a N := by
    simp only [a, logCoord]
    apply (le_div_iff₀ hlogpos).2
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show (N : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < N
        exact_mod_cast hNpos)
      (show ((N + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < (N + 1 : ℕ)
        positivity)
      (by norm_num : (N : ℝ) ≤ (N + 1 : ℕ))
    simpa using hmono
  have hEnd : |(∫ x in (0 : ℝ)..a N, f x) - ∫ x in (0 : ℝ)..1, f x| ≤
      C / Real.log (N : ℝ) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) 1 :
        IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1)
      (hf.intervalIntegrable 1 (a N) :
        IntervalIntegrable f MeasureTheory.volume 1 (a N))
    have heq : (∫ x in (0 : ℝ)..a N, f x) - ∫ x in (0 : ℝ)..1, f x =
        ∫ x in (1 : ℝ)..a N, f x := by linarith
    rw [heq, ← Real.norm_eq_abs]
    calc
      ‖∫ x in (1 : ℝ)..a N, f x‖ ≤ C * |a N - 1| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        simp only [Set.uIoc_of_le haN1] at hx
        exact hCbound x ⟨zero_le_one.trans hx.1.le, hx.2.trans haNmem.2⟩
      _ = C * (a N - 1) := by rw [abs_of_nonneg (sub_nonneg.mpr haN1)]
      _ ≤ C * ((N : ℝ)⁻¹ / Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        have hu := logCoord_succ_sub_upper_exact hlogpos hNpos
        simpa [a, logCoord, hlogpos.ne'] using hu
      _ ≤ C / Real.log (N : ℝ) := by
        rw [show C * ((N : ℝ)⁻¹ / Real.log (N : ℝ)) =
          (C * (N : ℝ)⁻¹) / Real.log (N : ℝ) by ring]
        apply (div_le_div_iff_of_pos_right hlogpos).2
        have hNinv : (N : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)]
          exact_mod_cast (show 1 ≤ N by omega)
        have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
        nlinarith
  rw [Real.dist_eq]
  calc
    |logHarmonicRiemannSum f N - ∫ x in (0 : ℝ)..1, f x| ≤
        |logHarmonicRiemannSum f N - Q| +
          |Q - ∫ x in (0 : ℝ)..1, f x| :=
      abs_sub_le _ _ _
    _ ≤ |logHarmonicRiemannSum f N - Q| +
        (|Q - ∫ x in (0 : ℝ)..a N, f x| +
          |(∫ x in (0 : ℝ)..a N, f x) - ∫ x in (0 : ℝ)..1, f x|) := by
      exact add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ C / Real.log (N : ℝ) +
        (ε / 4 + C / Real.log (N : ℝ)) :=
      add_le_add hHQ (add_le_add hQ hEnd)
    _ = C / Real.log (N : ℝ) + ε / 4 + C / Real.log (N : ℝ) := by ring
    _ < ε := by linarith [hClog]


lemma outerKernel_succ_bounds {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    (hu : logCoord (N : ℝ) (n : ℝ) ∈
      Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    0 ≤ outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ) ∧
      outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ) ≤ 1 := by
  have hg := outerEndpoint_geometry hn hendpoint
  have hN := hg.1
  let u := logCoord (N : ℝ) (n : ℝ)
  let v := logCoord (N : ℝ) (n + 1 : ℕ)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN
  have huv : u ≤ v := by
    apply div_le_div_of_nonneg_right _ hlogN.le
    exact Real.strictMonoOn_log.monotoneOn
      (show (n : ℝ) ∈ Set.Ioi 0 by
        exact zero_lt_one.trans (show (1 : ℝ) < n by exact_mod_cast hn))
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change 0 < ((n + 1 : ℕ) : ℝ)
        positivity) (by norm_num)
  have hvb : v ≤ (1 - u) / 2 := by
    rw [← hg.2.2]
    apply div_le_div_of_nonneg_right _ hlogN.le
    exact Real.strictMonoOn_log.monotoneOn
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change 0 < ((n + 1 : ℕ) : ℝ)
        positivity)
      (show outerEndpoint N n ∈ Set.Ioi 0 by
        exact (zero_lt_one.trans (show (1 : ℝ) < n by exact_mod_cast hn)).trans
          ((show (n : ℝ) < (n + 1 : ℕ) by norm_num).trans_le hendpoint)) hendpoint
  have hnt : (n : ℝ) * (n + 1 : ℕ) < (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hendpoint (by positivity)).trans_lt hg.2.1
  rw [outerKernel_eq_limitLog hN (by exact_mod_cast hn)
    (by exact_mod_cast hn.trans (Nat.lt_add_one n)) hnt]
  exact limitLog_bounds hu ⟨huv, hvb⟩

/-- Abel summation for the outer prime, with the error controlled solely by
the uniform Mertens remainder. -/
lemma outerPrime_abel_error {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    {X ε : ℝ}
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ ε)
    (hXn : X ≤ (n : ℝ)) :
    |(∑ p ∈ effectiveOuterPrimeIndices N n,
        (p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p) -
      ((∫ t in ((n + 1 : ℕ) : ℝ)..outerEndpoint N n,
          logLogIncrementDeriv t * outerKernel (N : ℝ) (n : ℝ) t) +
        logLogIncrement (n : ℝ) (n + 1 : ℕ) *
          outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ))| ≤
      (2 * ε) * outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ) := by
  let B := outerEndpoint N n
  let k := n + 1
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnk : (n : ℝ) < (k : ℝ) := by simp [k]
  have hnB : (n : ℝ) < B := hnk.trans_le hendpoint
  have hBpos : 0 < B := (zero_lt_one.trans hnR).trans hnB
  have hqpos : 0 < (N : ℝ) / (n : ℝ) := by
    simpa [B, outerEndpoint] using Real.sq_sqrt (show 0 ≤ (N : ℝ) / (n : ℝ) by positivity) ▸
      sq_pos_of_pos hBpos
  have hNR : 0 < (N : ℝ) := by
    rcases div_pos_iff.mp hqpos with h | h
    · exact h.1
    · have : 0 ≤ (n : ℝ) := by positivity
      linarith [h.2]
  have hBsq : B ^ 2 = (N : ℝ) / (n : ℝ) := by
    change (Real.sqrt ((N : ℝ) / (n : ℝ))) ^ 2 = _
    exact Real.sq_sqrt hqpos.le
  have hntX : ∀ t ∈ Set.Icc (k : ℝ) B, (n : ℝ) * t < (N : ℝ) := by
    intro t ht
    have hntB : (n : ℝ) * t < B ^ 2 := by
      calc
        (n : ℝ) * t ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        _ < B * B := mul_lt_mul_of_pos_right hnB hBpos
        _ = B ^ 2 := by ring
    have hq_lt_N : (N : ℝ) / (n : ℝ) < (N : ℝ) :=
      div_lt_self hNR hnR
    linarith [hBsq]
  have hinner : ∀ t ∈ Set.Icc (k : ℝ) B,
      0 < Real.log (N : ℝ) - Real.log (n : ℝ) - Real.log t := by
    intro t ht
    have ht1 : 1 < t := hnR.trans hnk |>.trans_le ht.1
    have hloglt := Real.strictMonoOn_log
      (show (n : ℝ) * t ∈ Set.Ioi 0 by
        exact mul_pos (zero_lt_one.trans hnR) (zero_lt_one.trans ht1))
      (show (N : ℝ) ∈ Set.Ioi 0 by exact hNR) (hntX t ht)
    rw [Real.log_mul (by positivity : (n : ℝ) ≠ 0) (by positivity : t ≠ 0)] at hloglt
    linarith
  have hkernelB : outerKernel (N : ℝ) (n : ℝ) B = 0 := by
    have hlogB : Real.log B ≠ 0 := (Real.log_pos (hnR.trans hnB)).ne'
    have hlogeq : Real.log (N : ℝ) - Real.log (n : ℝ) = 2 * Real.log B := by
      have hdiv := Real.log_div (ne_of_gt hNR) (by positivity : (n : ℝ) ≠ 0)
      have hpow := Real.log_pow B 2
      rw [← hBsq] at hdiv
      calc
        Real.log (N : ℝ) - Real.log (n : ℝ) = Real.log (B ^ 2) := hdiv.symm
        _ = 2 * Real.log B := by simp [Real.log_pow]
    simp only [outerKernel]
    rw [show Real.log (N : ℝ) - Real.log (n : ℝ) - Real.log B =
        Real.log B by linarith]
    ring
  have hcontF' : ContinuousOn (outerKernelDeriv (N : ℝ) (n : ℝ))
      (Set.Icc (k : ℝ) B) := by
    intro t ht
    have ht1 : 1 < t := hnR.trans hnk |>.trans_le ht.1
    have ht0 : t ≠ 0 := by positivity
    have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hin := (hinner t ht).ne'
    unfold outerKernelDeriv
    fun_prop
  have hcontA' : ContinuousOn logLogIncrementDeriv (Set.Icc (k : ℝ) B) := by
    intro t ht
    have ht1 : 1 < t := hnR.trans hnk |>.trans_le ht.1
    have ht0 : t ≠ 0 := by positivity
    have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    unfold logLogIncrementDeriv
    fun_prop
  have herr : ∀ t ∈ Set.Icc (k : ℝ) B,
      |summatory (fun m : ℕ ↦ if m.Prime then (m : ℝ)⁻¹ else 0) k t -
        logLogIncrement (n : ℝ) t| ≤ 2 * ε := by
    intro t ht
    have hfloor : k ≤ ⌊t⌋₊ := by
      apply (Nat.le_floor_iff (by linarith [hnR, hnk, ht.1] : 0 ≤ t)).2
      exact ht.1
    rw [summatory_prime_from_succ hfloor]
    have hXt : X ≤ t := hXn.trans (hnk.le.trans ht.1)
    have hEt := hM t hXt
    have hEn := hM (n : ℝ) hXn
    simp only [primeReciprocalError, logLogIncrement] at hEt hEn ⊢
    rw [abs_le] at hEt hEn ⊢
    constructor <;> linarith
  have hab := partial_summation_uniform_error
    (a := fun m : ℕ ↦ if m.Prime then (m : ℝ)⁻¹ else 0)
    (f := outerKernel (N : ℝ) (n : ℝ))
    (f' := outerKernelDeriv (N : ℝ) (n : ℝ))
    (A := logLogIncrement (n : ℝ)) (A' := logLogIncrementDeriv)
    (k := k) (x := B) (η := 2 * ε)
    (by simp [k]) hendpoint
    (fun t ht ↦ hasDerivAt_outerKernel
      (hnR.trans hnk |>.trans_le ht.1) (hinner t ht))
    (fun t ht ↦ hasDerivAt_logLogIncrement
      (hnR.trans hnk |>.trans_le ht.1))
    hcontF' hcontA' hkernelB
    (fun t ht ↦ outerKernelDeriv_nonpos
      (hnR.trans hnk |>.trans_le ht.1) (hinner t ht)) herr
  rw [effectiveOuter_sum_eq_summatory (N := N) (n := n) (by omega)]
  simpa [B, k] using hab

/-! ### Elementary properties of the limiting profile -/

lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.strictMonoOn_log (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show Real.exp 1 ∈ Set.Ioi 0 by exact Real.exp_pos 1) Real.exp_one_gt_two
  simpa using h

lemma one_lt_log_three : 1 < Real.log 3 := by
  have h := Real.strictMonoOn_log
    (show Real.exp 1 ∈ Set.Ioi 0 by exact Real.exp_pos 1)
    (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num) Real.exp_one_lt_three
  simpa using h

lemma profile_one_third : profile ((1 : ℝ) / 3) = Real.log 2 := by
  norm_num [profile, twoPrimeProfile]

lemma twoPrimeProfile_one_fourth_nonneg :
    0 ≤ twoPrimeProfile ((1 : ℝ) / 4) := by
  rw [twoPrimeProfile, if_pos (by norm_num)]
  norm_num only [one_div]
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  have hxpos : 0 < x := by linarith [hx.1]
  have hratio : 1 ≤ ((3 : ℝ) / 4 - x) / x := by
    apply (le_div_iff₀ hxpos).mpr
    linarith [hx.2]
  exact mul_nonneg (inv_nonneg.mpr hxpos.le) (Real.log_nonneg hratio)

lemma one_lt_profile_one_fourth : 1 < profile ((1 : ℝ) / 4) := by
  rw [profile]
  have hlog : Real.log (((1 : ℝ) - (1 : ℝ) / 4) / ((1 : ℝ) / 4)) =
      Real.log 3 := by norm_num
  rw [hlog]
  exact one_lt_log_three.trans_le
    (le_add_of_nonneg_right twoPrimeProfile_one_fourth_nonneg)

lemma profile_one_third_lt_one : profile ((1 : ℝ) / 3) < 1 := by
  rw [profile_one_third]
  exact log_two_lt_one

lemma profileIntegrand_continuousOn {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    ContinuousOn (fun x : ℝ ↦ x⁻¹ * Real.log ((1 - u - x) / x))
      (Set.Icc u ((1 - u) / 2)) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.inv₀ continuousOn_id
    intro x hx hzero
    change x = 0 at hzero
    linarith [hx.1, hu.1]
  · apply ContinuousOn.log
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx hzero
        change x = 0 at hzero
        linarith [hx.1, hu.1]
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1, hu.1]
      have hnum : 0 < 1 - u - x := by linarith [hx.2, hu.2]
      exact div_ne_zero hnum.ne' hxpos.ne'

lemma profileIntegrand_nonneg {u x : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hx : x ∈ Set.Icc u ((1 - u) / 2)) :
    0 ≤ x⁻¹ * Real.log ((1 - u - x) / x) := by
  have hxpos : 0 < x := by linarith [hx.1, hu.1]
  have hratio : 1 ≤ (1 - u - x) / x := by
    apply (le_div_iff₀ hxpos).mpr
    linarith [hx.2]
  exact mul_nonneg (inv_nonneg.mpr hxpos.le) (Real.log_nonneg hratio)

lemma profileIntegral_tail_error {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hu : logCoord (N : ℝ) (n : ℝ) ∈
      Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    |(∫ v in logCoord (N : ℝ) (n + 1 : ℕ)..
          (1 - logCoord (N : ℝ) (n : ℝ)) / 2,
          limitIntegrand (logCoord (N : ℝ) (n : ℝ)) v) -
      ∫ v in logCoord (N : ℝ) (n : ℝ)..
          (1 - logCoord (N : ℝ) (n : ℝ)) / 2,
          limitIntegrand (logCoord (N : ℝ) (n : ℝ)) v| ≤
      4 * (n : ℝ)⁻¹ := by
  let u := logCoord (N : ℝ) (n : ℝ)
  let v := logCoord (N : ℝ) (n + 1 : ℕ)
  let b := (1 - u) / 2
  have hg := outerEndpoint_geometry hn hendpoint
  have hlogNpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have huv : u ≤ v := by
    apply div_le_div_of_nonneg_right _ hlogNpos.le
    exact Real.strictMonoOn_log.monotoneOn
      (show (n : ℝ) ∈ Set.Ioi 0 by
        change (0 : ℝ) < n
        exact_mod_cast (show 0 < n by omega))
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change 0 < ((n + 1 : ℕ) : ℝ)
        positivity) (by norm_num)
  have hvb : v ≤ b := by
    have hcoord := hg.2.2
    change v ≤ (1 - u) / 2
    rw [← hcoord]
    apply div_le_div_of_nonneg_right _ hlogNpos.le
    exact Real.strictMonoOn_log.monotoneOn
      (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        change 0 < ((n + 1 : ℕ) : ℝ)
        positivity)
      (show outerEndpoint N n ∈ Set.Ioi 0 by
        exact (zero_lt_one.trans (show (1 : ℝ) < n by exact_mod_cast hn)).trans
          ((show (n : ℝ) < (n + 1 : ℕ) by norm_num).trans_le hendpoint)) hendpoint
  have hcont : ContinuousOn (limitIntegrand u) (Set.Icc u b) := by
    change ContinuousOn
      (fun x : ℝ ↦ x⁻¹ * Real.log ((1 - u - x) / x)) (Set.Icc u b)
    simpa [u, b] using profileIntegrand_continuousOn hu
  have hIntUV : IntervalIntegrable (limitIntegrand u) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro x hx
    have hx' : x ∈ Set.Icc u v := by simpa [Set.uIcc_of_le huv] using hx
    exact ⟨hx'.1, hx'.2.trans hvb⟩
  have hIntVB : IntervalIntegrable (limitIntegrand u) MeasureTheory.volume v b := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro x hx
    have hx' : x ∈ Set.Icc v b := by simpa [Set.uIcc_of_le hvb] using hx
    exact ⟨huv.trans hx'.1, hx'.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIntUV hIntVB
  have heq :
      (∫ x in v..b, limitIntegrand u x) - ∫ x in u..b, limitIntegrand u x =
        -(∫ x in u..v, limitIntegrand u x) := by
    linarith
  rw [show logCoord (N : ℝ) (n + 1 : ℕ) = v by rfl,
    show logCoord (N : ℝ) (n : ℝ) = u by rfl,
    show (1 - u) / 2 = b by rfl, heq, abs_neg, ← Real.norm_eq_abs]
  calc
    ‖∫ x in u..v, limitIntegrand u x‖ ≤ 4 * |v - u| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · have hx' : x ∈ Set.Icc u v := by
          simpa [Set.uIcc_of_le huv] using (Set.uIoc_subset_uIcc hx)
        exact (limitIntegrand_bounds hu ⟨hx'.1, hx'.2.trans hvb⟩).2
      · have hx' : x ∈ Set.Icc u v := by
          simpa [Set.uIcc_of_le huv] using (Set.uIoc_subset_uIcc hx)
        exact (limitIntegrand_bounds hu ⟨hx'.1, hx'.2.trans hvb⟩).1
    _ = 4 * (v - u) := by rw [abs_of_nonneg (sub_nonneg.mpr huv)]
    _ ≤ 4 * (n : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (logCoord_succ_sub_bounds hlogN (by omega)).2 (by norm_num)

/-- Quantitative local limit for the ordered two-prime inflow.  The first
term is the uniform Mertens error; the second records the discrete endpoint
and diagonal-prime corrections. -/
lemma twoPrimeChildMass_profile_error {N n : ℕ} (hn : 1 < n)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hlogn : 1 ≤ Real.log (n : ℝ))
    (hu : logCoord (N : ℝ) (n : ℝ) ∈
      Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hult : logCoord (N : ℝ) (n : ℝ) < (1 : ℝ) / 3)
    {X ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) :
    |twoPrimeChildMass N n -
      twoPrimeProfile (logCoord (N : ℝ) (n : ℝ))| ≤
      8 * ε + 6 * (n : ℝ)⁻¹ := by
  classical
  let u := logCoord (N : ℝ) (n : ℝ)
  let E := effectiveOuterPrimeIndices N n
  let S := ∑ p ∈ E, (p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p
  let D := ∑ p ∈ E, ((p : ℝ) ^ 2)⁻¹
  let I := ∫ t in ((n + 1 : ℕ) : ℝ)..outerEndpoint N n,
    logLogIncrementDeriv t * outerKernel (N : ℝ) (n : ℝ) t
  let B := logLogIncrement (n : ℝ) (n + 1 : ℕ) *
    outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ)
  have hg := outerEndpoint_geometry hn hendpoint
  have hNR : 0 < (N : ℝ) := zero_lt_one.trans hg.1
  have hnR : 0 < (n : ℝ) := by positivity
  have hMle : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ ε :=
    fun x hx ↦ (hM x hx).le
  have hsumrec : (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 3 := by
    exact effectiveOuter_reciprocal_sum_le_three hn hendpoint hu hε1 hMle hXn
  have hlocal : ∀ p ∈ E,
      |(p : ℝ)⁻¹ * innerPrimeMass N n p -
        ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p + ((p : ℝ) ^ 2)⁻¹)| ≤
        (p : ℝ)⁻¹ * (2 * ε) := by
    intro p hpE
    have hpData := Finset.mem_filter.mp hpE
    have hpOuter := Finset.mem_filter.mp hpData.1
    have hp : p.Prime := hpOuter.2.1
    have hnp : n < p := hpOuter.2.2
    have hpp : n * p * p ≤ N := hpData.2
    have hXp : X ≤ (p : ℝ) := hXn.trans (by exact_mod_cast hnp.le)
    have hpq : (p : ℝ) ≤ (N : ℝ) / ((n : ℝ) * (p : ℝ)) := by
      apply (le_div_iff₀ (mul_pos hnR (by exact_mod_cast hp.pos))).2
      have hppR : ((n * p * p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hppR
    have hXq : X ≤ (N : ℝ) / ((n : ℝ) * (p : ℝ)) := hXp.trans hpq
    have hi := innerPrimeMass_real_loglog_error (N := N) (n := n) (p := p)
      (by omega) hp hpp hM hXp hXq
    have hk := outerKernel_eq_innerLog hNR.ne' (by positivity : (n : ℝ) ≠ 0)
      (by exact_mod_cast hp.ne_zero : (p : ℝ) ≠ 0)
    rw [← hk] at hi
    have hpinv : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have halg :
        (p : ℝ)⁻¹ * innerPrimeMass N n p -
            ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p + ((p : ℝ) ^ 2)⁻¹) =
          (p : ℝ)⁻¹ * (innerPrimeMass N n p -
            (outerKernel (N : ℝ) (n : ℝ) p + (p : ℝ)⁻¹)) := by
      rw [pow_two, mul_inv]
      ring
    calc
      |(p : ℝ)⁻¹ * innerPrimeMass N n p -
          ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p + ((p : ℝ) ^ 2)⁻¹)| =
          (p : ℝ)⁻¹ * |innerPrimeMass N n p -
            (outerKernel (N : ℝ) (n : ℝ) p + (p : ℝ)⁻¹)| := by
            rw [halg, abs_mul, abs_of_nonneg hpinv]
      _ ≤ (p : ℝ)⁻¹ * (2 * ε) :=
        mul_le_mul_of_nonneg_left hi.le hpinv
  have hmass : |twoPrimeChildMass N n - (S + D)| ≤ 6 * ε := by
    rw [twoPrimeChildMass_eq_effective_iterated N n]
    change |(∑ p ∈ E, (p : ℝ)⁻¹ * innerPrimeMass N n p) - (S + D)| ≤ _
    have heq :
        (∑ p ∈ E, (p : ℝ)⁻¹ * innerPrimeMass N n p) - (S + D) =
          ∑ p ∈ E, ((p : ℝ)⁻¹ * innerPrimeMass N n p -
            ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p +
              ((p : ℝ) ^ 2)⁻¹)) := by
      simp only [S, D, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [heq]
    calc
      |∑ p ∈ E, ((p : ℝ)⁻¹ * innerPrimeMass N n p -
          ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p +
            ((p : ℝ) ^ 2)⁻¹))| ≤
          ∑ p ∈ E, |(p : ℝ)⁻¹ * innerPrimeMass N n p -
            ((p : ℝ)⁻¹ * outerKernel (N : ℝ) (n : ℝ) p +
              ((p : ℝ) ^ 2)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ E, (p : ℝ)⁻¹ * (2 * ε) := by
        exact Finset.sum_le_sum fun p hp ↦ hlocal p hp
      _ = (2 * ε) * ∑ p ∈ E, (p : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ (2 * ε) * 3 :=
        mul_le_mul_of_nonneg_left hsumrec (mul_nonneg (by norm_num) hε0)
      _ = 6 * ε := by ring
  have hD0 : 0 ≤ D := by
    exact Finset.sum_nonneg fun p hp ↦ by positivity
  have hD : D ≤ (n : ℝ)⁻¹ := effectiveOuter_square_sum_le (N := N) (n := n) (by omega)
  have habel : |S - (I + B)| ≤ 2 * ε := by
    have h := outerPrime_abel_error hn hendpoint hMle hXn
    have hk := (outerKernel_succ_bounds hn hendpoint hu).2
    calc
      |S - (I + B)| ≤ (2 * ε) * outerKernel (N : ℝ) (n : ℝ) (n + 1 : ℕ) := h
      _ ≤ (2 * ε) * 1 :=
        mul_le_mul_of_nonneg_left hk (mul_nonneg (by norm_num) hε0)
      _ = 2 * ε := by ring
  have hB0 : 0 ≤ B := mul_nonneg (logLogIncrement_succ_bounds (by omega) hlogn).1
    (outerKernel_succ_bounds hn hendpoint hu).1
  have hB : B ≤ (n : ℝ)⁻¹ := by
    exact (mul_le_mul (logLogIncrement_succ_bounds (by omega) hlogn).2
      (outerKernel_succ_bounds hn hendpoint hu).2
      (outerKernel_succ_bounds hn hendpoint hu).1 (by positivity)).trans_eq (by ring)
  have htail : |I - twoPrimeProfile u| ≤ 4 * (n : ℝ)⁻¹ := by
    rw [twoPrimeProfile, if_pos hult]
    dsimp only [I]
    change |(∫ t in ((n + 1 : ℕ) : ℝ)..outerEndpoint N n,
      logLogIncrementDeriv t * outerKernel (N : ℝ) (n : ℝ) t) -
      (∫ v in u..(1 - u) / 2, limitIntegrand u v)| ≤ _
    rw [outerKernel_integral_eq_profile_tail hn hendpoint]
    exact profileIntegral_tail_error hn hendpoint hlogN hu
  have htri := abs_sub_le (twoPrimeChildMass N n) (S + D) (twoPrimeProfile u)
  have htri2 := abs_sub_le S (I + B) (twoPrimeProfile u - D)
  have hIB : |(I + B) - (twoPrimeProfile u - D)| ≤
      4 * (n : ℝ)⁻¹ + (n : ℝ)⁻¹ + (n : ℝ)⁻¹ := by
    calc
      |(I + B) - (twoPrimeProfile u - D)| =
          |(I - twoPrimeProfile u) + B + D| := by ring_nf
      _ ≤ |I - twoPrimeProfile u| + |B| + |D| := by
        calc
          |(I - twoPrimeProfile u) + B + D| ≤
              |(I - twoPrimeProfile u) + B| + |D| := abs_add_le _ _
          _ ≤ (|I - twoPrimeProfile u| + |B|) + |D| :=
            add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 4 * (n : ℝ)⁻¹ + (n : ℝ)⁻¹ + (n : ℝ)⁻¹ := by
        exact add_le_add (add_le_add htail (by simpa [abs_of_nonneg hB0] using hB))
          (by simpa [abs_of_nonneg hD0] using hD)
  calc
    |twoPrimeChildMass N n - twoPrimeProfile u| ≤
        |twoPrimeChildMass N n - (S + D)| + |(S + D) - twoPrimeProfile u| := htri
    _ ≤ 6 * ε + (|S - (I + B)| + |(I + B) - (twoPrimeProfile u - D)|) := by
      apply add_le_add hmass
      convert htri2 using 1; ring
    _ ≤ 6 * ε + (2 * ε +
        (4 * (n : ℝ)⁻¹ + (n : ℝ)⁻¹ + (n : ℝ)⁻¹)) := by
      gcongr
    _ = 8 * ε + 6 * (n : ℝ)⁻¹ := by ring

/-- Quantitative local limit for the one-prime inflow. -/
lemma primeChildMass_profile_error {N n : ℕ} (hn : 1 < n)
    (hsq : n * n ≤ N) {X ε : ℝ}
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) :
    |primeChildMass N n -
      Real.log ((1 - logCoord (N : ℝ) (n : ℝ)) /
        logCoord (N : ℝ) (n : ℝ))| < 2 * ε := by
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnn : n < n * n := by nlinarith
  have hnNnat : n < N := hnn.trans_le hsq
  have hnN : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnNnat
  have hnpos : 0 < n := by omega
  have hXq : X ≤ (N : ℝ) / (n : ℝ) := by
    refine hXn.trans ?_
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n)).2
    exact_mod_cast hsq
  have h := primeChildMass_real_loglog_error hnpos hsq hM hXn hXq
  rw [real_loglog_div_identity hnR hnN] at h
  simpa only [logCoord] using h

lemma twoPrimeProfile_nonneg {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    0 ≤ twoPrimeProfile u := by
  rw [twoPrimeProfile]
  split_ifs with hlt
  · apply intervalIntegral.integral_nonneg (by linarith [hu.2])
    exact fun x hx ↦ profileIntegrand_nonneg hu hx
  · exact le_rfl

lemma profileIntegrand_anti_param {u v x : ℝ}
    (hv : v ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) (huv : u ≤ v)
    (hx : x ∈ Set.Icc v ((1 - v) / 2)) :
    x⁻¹ * Real.log ((1 - v - x) / x) ≤
      x⁻¹ * Real.log ((1 - u - x) / x) := by
  have hxpos : 0 < x := by linarith [hx.1, hv.1]
  have hvnum : 0 < 1 - v - x := by linarith [hx.2, hv.2]
  have hunum : 0 < 1 - u - x := by linarith
  have hratio : (1 - v - x) / x ≤ (1 - u - x) / x := by
    exact div_le_div_of_nonneg_right (by linarith) hxpos.le
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show (1 - v - x) / x ∈ Set.Ioi 0 by exact div_pos hvnum hxpos)
    (show (1 - u - x) / x ∈ Set.Ioi 0 by exact div_pos hunum hxpos) hratio
  exact mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hxpos.le)

lemma twoPrimeProfile_antitoneOn :
    AntitoneOn twoPrimeProfile (Set.Icc ((1 : ℝ) / 4) (1 / 3)) := by
  intro u hu v hv huv
  by_cases hvlt : v < (1 : ℝ) / 3
  · have hult : u < (1 : ℝ) / 3 := huv.trans_lt hvlt
    simp only [twoPrimeProfile, if_pos hult, if_pos hvlt]
    have hvb : v ≤ (1 - v) / 2 := by linarith [hv.2]
    have hub : u ≤ (1 - u) / 2 := by linarith [hu.2]
    have hbvu : (1 - v) / 2 ≤ (1 - u) / 2 := by linarith
    have hcontV := profileIntegrand_continuousOn hv
    have hcontU := profileIntegrand_continuousOn hu
    have hcontUsub :
        ContinuousOn (fun x : ℝ ↦ x⁻¹ * Real.log ((1 - u - x) / x))
          (Set.Icc v ((1 - v) / 2)) := by
      apply hcontU.mono
      intro x hx
      exact ⟨huv.trans hx.1, hx.2.trans hbvu⟩
    have h₁ :
        (∫ x in v..(1 - v) / 2, x⁻¹ * Real.log ((1 - v - x) / x)) ≤
          ∫ x in v..(1 - v) / 2, x⁻¹ * Real.log ((1 - u - x) / x) := by
      have hIntV : IntervalIntegrable
          (fun x : ℝ ↦ x⁻¹ * Real.log ((1 - v - x) / x)) MeasureTheory.volume
          v ((1 - v) / 2) := by
        apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le hvb] using hcontV
      have hIntUsub : IntervalIntegrable
          (fun x : ℝ ↦ x⁻¹ * Real.log ((1 - u - x) / x)) MeasureTheory.volume
          v ((1 - v) / 2) := by
        apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le hvb] using hcontUsub
      exact intervalIntegral.integral_mono_on hvb hIntV hIntUsub (fun x hx ↦
          profileIntegrand_anti_param hv huv hx)
    have h₂ :
        (∫ x in v..(1 - v) / 2, x⁻¹ * Real.log ((1 - u - x) / x)) ≤
          ∫ x in u..(1 - u) / 2, x⁻¹ * Real.log ((1 - u - x) / x) := by
      apply intervalIntegral.integral_mono_interval huv hvb hbvu
      · change ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioc u ((1 - u) / 2)),
          0 ≤ x⁻¹ * Real.log ((1 - u - x) / x)
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall fun x hx ↦
          profileIntegrand_nonneg hu ⟨hx.1.le, hx.2⟩
      · apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le hub] using hcontU
    exact h₁.trans h₂
  · have hveq : v = (1 : ℝ) / 3 := le_antisymm hv.2 (le_of_not_gt hvlt)
    rw [hveq, twoPrimeProfile, if_neg (by norm_num)]
    exact twoPrimeProfile_nonneg hu

lemma baseProfile_strictAntiOn :
    StrictAntiOn (fun u : ℝ ↦ Real.log ((1 - u) / u))
      (Set.Icc ((1 : ℝ) / 4) (1 / 2)) := by
  intro u hu v hv huv
  have hupos : 0 < u := by linarith [hu.1]
  have hvpos : 0 < v := by linarith [hv.1]
  have hunum : 0 < 1 - u := by linarith [hu.2]
  have hvnum : 0 < 1 - v := by linarith [hv.2]
  have hratio : (1 - v) / v < (1 - u) / u := by
    apply (div_lt_div_iff₀ hvpos hupos).mpr
    nlinarith
  exact Real.strictMonoOn_log
    (show (1 - v) / v ∈ Set.Ioi 0 by exact div_pos hvnum hvpos)
    (show (1 - u) / u ∈ Set.Ioi 0 by exact div_pos hunum hupos) hratio

lemma profile_strictAntiOn :
    StrictAntiOn profile (Set.Icc ((1 : ℝ) / 4) (1 / 2)) := by
  intro u hu v hv huv
  have hbase := baseProfile_strictAntiOn hu hv huv
  by_cases hvsmall : v ≤ (1 : ℝ) / 3
  · have husmall : u ≤ (1 : ℝ) / 3 := huv.le.trans hvsmall
    have hu' : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := ⟨hu.1, husmall⟩
    have hv' : v ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := ⟨hu.1.trans huv.le, hvsmall⟩
    have htwo := twoPrimeProfile_antitoneOn hu' hv' huv.le
    rw [profile, profile]
    exact add_lt_add_of_lt_of_le hbase htwo
  · have hvnot : ¬v < (1 : ℝ) / 3 := not_lt_of_ge (le_of_not_ge hvsmall)
    have hvzero : twoPrimeProfile v = 0 := by
      rw [twoPrimeProfile, if_neg hvnot]
    by_cases husmall : u < (1 : ℝ) / 3
    · have hu' : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := ⟨hu.1, husmall.le⟩
      rw [profile, profile, hvzero, add_zero]
      exact hbase.trans_le (le_add_of_nonneg_right (twoPrimeProfile_nonneg hu'))
    · have huzero : twoPrimeProfile u = 0 := by
        rw [twoPrimeProfile, if_neg husmall]
      rw [profile, profile, hvzero, huzero, add_zero, add_zero]
      exact hbase

/-- Length of the two-prime integration interval after normalization. -/
noncomputable def profileLength (u : ℝ) : ℝ := (1 - 3 * u) / 2

/-- Affine parametrization of the two-prime integration interval. -/
noncomputable def profilePoint (u y : ℝ) : ℝ := u + profileLength u * y

/-- Fixed-interval version of the two-prime profile integrand. -/
noncomputable def profileKernel (u y : ℝ) : ℝ :=
  profileLength u * ((profilePoint u y)⁻¹ *
    Real.log ((1 - u - profilePoint u y) / profilePoint u y))

lemma profileLength_bounds {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    0 ≤ profileLength u ∧ profileLength u ≤ 1 := by
  constructor <;> simp only [profileLength] <;> linarith [hu.1, hu.2]

lemma profilePoint_bounds {u y : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    u ≤ profilePoint u y ∧ profilePoint u y ≤ (1 - u) / 2 := by
  have hL := profileLength_bounds hu
  constructor
  · simp only [profilePoint]
    exact le_add_of_nonneg_right (mul_nonneg hL.1 hy.1)
  · have hLy : profileLength u * y ≤ profileLength u :=
      mul_le_of_le_one_right hL.1 hy.2
    simp only [profilePoint]
    have hident : u + profileLength u = (1 - u) / 2 := by
      simp [profileLength]
      ring
    linarith

lemma profileKernel_bounds {u y : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ profileKernel u y ∧ |profileKernel u y| ≤ 4 := by
  have hL := profileLength_bounds hu
  have hx := profilePoint_bounds hu hy
  have hxpos : 0 < profilePoint u y := by linarith [hx.1, hu.1]
  have hratio_one : 1 ≤
      (1 - u - profilePoint u y) / profilePoint u y := by
    apply (le_div_iff₀ hxpos).mpr
    linarith [hx.2]
  have hratio_two :
      (1 - u - profilePoint u y) / profilePoint u y ≤ 2 := by
    apply (div_le_iff₀ hxpos).mpr
    linarith [hx.1, hu.1]
  have hlog0 : 0 ≤ Real.log
      ((1 - u - profilePoint u y) / profilePoint u y) :=
    Real.log_nonneg hratio_one
  have hlog4 : Real.log
      ((1 - u - profilePoint u y) / profilePoint u y) ≤ 1 := by
    have hratioPos : 0 <
        (1 - u - profilePoint u y) / profilePoint u y := lt_of_lt_of_le zero_lt_one hratio_one
    have hlog_le := Real.strictMonoOn_log.monotoneOn
      (show (1 - u - profilePoint u y) / profilePoint u y ∈ Set.Ioi 0 by
        exact hratioPos)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num) hratio_two
    exact hlog_le.trans log_two_lt_one.le
  have hinv0 : 0 ≤ (profilePoint u y)⁻¹ := inv_nonneg.mpr hxpos.le
  have hinv4 : (profilePoint u y)⁻¹ ≤ 4 := by
    apply (inv_le_iff_one_le_mul₀ hxpos).mpr
    linarith [hx.1, hu.1]
  have hinner0 : 0 ≤ (profilePoint u y)⁻¹ *
      Real.log ((1 - u - profilePoint u y) / profilePoint u y) :=
    mul_nonneg hinv0 hlog0
  have hinner4 : (profilePoint u y)⁻¹ *
      Real.log ((1 - u - profilePoint u y) / profilePoint u y) ≤ 4 := by
    calc
      _ ≤ 4 * 1 := mul_le_mul hinv4 hlog4 hlog0 (by norm_num)
      _ = 4 := by norm_num
  have hkernel0 : 0 ≤ profileKernel u y := by
    exact mul_nonneg hL.1 hinner0
  refine ⟨hkernel0, ?_⟩
  rw [abs_of_nonneg hkernel0]
  exact (mul_le_mul hL.2 hinner4 hinner0 (by norm_num)).trans_eq (by norm_num)

lemma profileKernel_continuousOn_y {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    ContinuousOn (profileKernel u) (Set.Icc (0 : ℝ) 1) := by
  have hpoint : ContinuousOn (profilePoint u) (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun y : ℝ ↦ u + ((1 - 3 * u) / 2) * y) _
    fun_prop
  have hpoint_ne : ∀ y ∈ Set.Icc (0 : ℝ) 1, profilePoint u y ≠ 0 := by
    intro y hy
    exact (by linarith [profilePoint_bounds hu hy |>.1, hu.1])
  have hinv := hpoint.inv₀ hpoint_ne
  have hnum : ContinuousOn (fun y ↦ 1 - u - profilePoint u y) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hratio := hnum.div hpoint hpoint_ne
  have hratio_ne : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (1 - u - profilePoint u y) / profilePoint u y ≠ 0 := by
    intro y hy
    have hx := profilePoint_bounds hu hy
    have hxpos : 0 < profilePoint u y := by linarith [hx.1, hu.1]
    have hnumpos : 0 < 1 - u - profilePoint u y := by linarith [hx.2, hu.2]
    exact div_ne_zero hnumpos.ne' hxpos.ne'
  exact continuousOn_const.mul (hinv.mul (hratio.log hratio_ne))

lemma profileKernel_continuousWithinAt_u {u y : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3))
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousWithinAt (fun v ↦ profileKernel v y)
      (Set.Icc ((1 : ℝ) / 4) (1 / 3)) u := by
  have hpoint : ContinuousWithinAt (fun v ↦ profilePoint v y)
      (Set.Icc ((1 : ℝ) / 4) (1 / 3)) u := by
    simp only [profilePoint, profileLength]
    fun_prop
  have hx := profilePoint_bounds hu hy
  have hxpos : 0 < profilePoint u y := by linarith [hx.1, hu.1]
  have hinv := hpoint.inv₀ hxpos.ne'
  have hnum : ContinuousWithinAt (fun v ↦ 1 - v - profilePoint v y)
      (Set.Icc ((1 : ℝ) / 4) (1 / 3)) u := by
    fun_prop
  have hratio := hnum.div hpoint hxpos.ne'
  have hnumpos : 0 < 1 - u - profilePoint u y := by linarith [hx.2, hu.2]
  have hlog := hratio.log (div_ne_zero hnumpos.ne' hxpos.ne')
  have hlength : ContinuousWithinAt profileLength
      (Set.Icc ((1 : ℝ) / 4) (1 / 3)) u := by
    change ContinuousWithinAt (fun v : ℝ ↦ (1 - 3 * v) / 2) _ u
    fun_prop
  exact hlength.mul (hinv.mul hlog)

lemma kernelIntegral_eq_twoPrimeIntegral {u : ℝ} :
    (∫ y in (0 : ℝ)..1, profileKernel u y) =
      ∫ x in u..(1 - u) / 2, x⁻¹ * Real.log ((1 - u - x) / x) := by
  let f : ℝ → ℝ := fun x ↦ x⁻¹ * Real.log ((1 - u - x) / x)
  let L : ℝ := profileLength u
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1) f L u
  calc
    (∫ y in (0 : ℝ)..1, profileKernel u y) =
        L * ∫ y in (0 : ℝ)..1, f (u + L * y) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro y hy
          simp [profileKernel, profilePoint, f, L]
    _ = ∫ x in u + L * 0..u + L * 1, f x := by
          simpa only [smul_eq_mul] using hchange
    _ = ∫ x in u..(1 - u) / 2, x⁻¹ * Real.log ((1 - u - x) / x) := by
          congr 1
          · simp
          · simp [L, profileLength]
            ring

lemma twoPrimeProfile_eq_kernelIntegral {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) :
    twoPrimeProfile u = ∫ y in (0 : ℝ)..1, profileKernel u y := by
  by_cases hlt : u < (1 : ℝ) / 3
  · rw [twoPrimeProfile, if_pos hlt, kernelIntegral_eq_twoPrimeIntegral]
  · have hueq : u = (1 : ℝ) / 3 := le_antisymm hu.2 (le_of_not_gt hlt)
    subst u
    rw [twoPrimeProfile, if_neg (by norm_num)]
    simp [profileKernel, profileLength]

lemma kernelIntegral_continuousOn :
    ContinuousOn (fun u : ℝ ↦ ∫ y in (0 : ℝ)..1, profileKernel u y)
      (Set.Icc ((1 : ℝ) / 4) (1 / 3)) := by
  intro u hu
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (μ := MeasureTheory.volume) (bound := fun _ : ℝ ↦ (4 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    have hc : ContinuousOn (profileKernel v) (Set.uIoc (0 : ℝ) 1) := by
      apply (profileKernel_continuousOn_y hv).mono
      intro y hy
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (Set.uIoc_subset_uIcc hy)
    exact hc.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [Real.norm_eq_abs]
      have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          (Set.uIoc_subset_uIcc hy)
      exact (profileKernel_bounds hv hy').2
  · apply ContinuousOn.intervalIntegrable
    fun_prop
  · exact Filter.Eventually.of_forall fun y hy ↦ by
      have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          (Set.uIoc_subset_uIcc hy)
      exact profileKernel_continuousWithinAt_u hu hy'

lemma twoPrimeProfile_continuousOn :
    ContinuousOn twoPrimeProfile (Set.Icc ((1 : ℝ) / 4) (1 / 3)) := by
  apply kernelIntegral_continuousOn.congr
  intro u hu
  exact twoPrimeProfile_eq_kernelIntegral hu

lemma profile_continuousOn_quarter_third :
    ContinuousOn profile (Set.Icc ((1 : ℝ) / 4) (1 / 3)) := by
  apply ContinuousOn.add
  · apply ContinuousOn.log
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu hzero
        change u = 0 at hzero
        linarith [hu.1]
    · intro u hu
      have hupos : 0 < u := by linarith [hu.1]
      have hnum : 0 < 1 - u := by linarith [hu.2]
      exact div_ne_zero hnum.ne' hupos.ne'
  · exact twoPrimeProfile_continuousOn

/-- The cutoff in `twoPrimeProfile` is continuous because its integration
interval collapses to a point at `u = 1 / 3`. -/
lemma twoPrimeProfile_continuousOn_quarter_half :
    ContinuousOn twoPrimeProfile (Set.Icc ((1 : ℝ) / 4) (1 / 2)) := by
  let F : ℝ → ℝ := fun u ↦ ∫ y in (0 : ℝ)..1, profileKernel u y
  let S : Set ℝ := Set.Icc ((1 : ℝ) / 4) (1 / 2)
  let T : Set ℝ := Set.Iic ((1 : ℝ) / 3)
  have hpiece : ContinuousOn (Set.piecewise T F 0) S := by
    apply ContinuousOn.piecewise
    · intro u hu
      have hueq : u = (1 : ℝ) / 3 := by
        have hu' : u ∈ ({(1 : ℝ) / 3} : Set ℝ) := by
          simpa [T, frontier_Iic] using hu.2
        simpa using hu'
      subst u
      simp [F, profileKernel, profileLength]
    · apply kernelIntegral_continuousOn.mono
      intro u hu
      have huT : u ≤ (1 : ℝ) / 3 := by
        simpa [T, closure_Iic] using hu.2
      exact ⟨hu.1.1, huT⟩
    · exact continuousOn_const
  apply hpiece.congr
  intro u hu
  by_cases hlt : u < (1 : ℝ) / 3
  · have hu' : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := ⟨hu.1, hlt.le⟩
    rw [twoPrimeProfile_eq_kernelIntegral hu']
    rw [T.piecewise_eq_of_mem F 0 (show u ∈ T by simpa [T] using hlt.le)]
  · have hge : (1 : ℝ) / 3 ≤ u := le_of_not_gt hlt
    rw [twoPrimeProfile, if_neg hlt]
    by_cases heq : u = (1 : ℝ) / 3
    · subst u
      simp [Set.piecewise, T, F, profileKernel, profileLength]
    · have hnotT : u ∉ T := by
        simp only [T, Set.mem_Iic]
        exact not_le_of_gt (lt_of_le_of_ne hge (Ne.symm heq))
      simp [Set.piecewise, hnotT]

lemma profile_continuousOn :
    ContinuousOn profile (Set.Icc ((1 : ℝ) / 4) (1 / 2)) := by
  apply ContinuousOn.add
  · apply ContinuousOn.log
    · apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro u hu hzero
        change u = 0 at hzero
        linarith [hu.1]
    · intro u hu
      have hupos : 0 < u := by linarith [hu.1]
      have hnum : 0 < 1 - u := by linarith [hu.2]
      exact div_ne_zero hnum.ne' hupos.ne'
  · exact twoPrimeProfile_continuousOn_quarter_half

lemma exists_unique_profile_root :
    ∃! u : ℝ, u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) ∧ profile u = 1 := by
  have hvalue : (1 : ℝ) ∈ Set.Icc (profile ((1 : ℝ) / 3))
      (profile ((1 : ℝ) / 4)) :=
    ⟨profile_one_third_lt_one.le, one_lt_profile_one_fourth.le⟩
  obtain ⟨u, hu, hprofile⟩ :=
    (intermediate_value_Icc' (by norm_num : (1 : ℝ) / 4 ≤ 1 / 3)
      profile_continuousOn_quarter_third) hvalue
  refine ⟨u, ⟨hu, hprofile⟩, ?_⟩
  intro v hv
  by_contra hne
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have hstrict := profile_strictAntiOn
      ⟨hv.1.1, hv.1.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩
      ⟨hu.1, hu.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩ huv
    rw [hprofile, hv.2] at hstrict
    exact (lt_irrefl 1 hstrict)
  · have hstrict := profile_strictAntiOn
      ⟨hu.1, hu.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩
      ⟨hv.1.1, hv.1.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩ hvu
    rw [hprofile, hv.2] at hstrict
    exact (lt_irrefl 1 hstrict)

lemma alphaTwo_eq_profile_root : alphaTwo = (exists_unique_profile_root.choose) := by
  let r := exists_unique_profile_root.choose
  have hr := exists_unique_profile_root.choose_spec.1
  let S : Set ℝ := {u : ℝ | u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) ∧ profile u ≤ 1}
  have hrS : r ∈ S := ⟨hr.1, hr.2.le⟩
  have hSne : S.Nonempty := ⟨r, hrS⟩
  have hSbelow : BddBelow S := ⟨(1 : ℝ) / 4, fun u hu ↦ hu.1.1⟩
  have hrlower : ∀ u ∈ S, r ≤ u := by
    intro u huS
    by_contra hru
    have hur : u < r := lt_of_not_ge hru
    have hstrict := profile_strictAntiOn
      ⟨huS.1.1, huS.1.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩
      ⟨hr.1.1, hr.1.2.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)⟩ hur
    rw [hr.2] at hstrict
    exact (not_lt_of_ge huS.2) hstrict
  apply le_antisymm
  · rw [alphaTwo]
    exact csInf_le hSbelow hrS
  · rw [alphaTwo]
    exact le_csInf hSne hrlower

lemma alphaTwo_mem : alphaTwo ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := by
  rw [alphaTwo_eq_profile_root]
  exact exists_unique_profile_root.choose_spec.1.1

lemma profile_alphaTwo : profile alphaTwo = 1 := by
  rw [alphaTwo_eq_profile_root]
  exact exists_unique_profile_root.choose_spec.1.2

lemma alphaTwo_unique {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3)) (hprofile : profile u = 1) :
    u = alphaTwo := by
  rw [alphaTwo_eq_profile_root]
  exact exists_unique_profile_root.choose_spec.2 u ⟨hu, hprofile⟩

lemma alphaTwo_gt_quarter : (1 : ℝ) / 4 < alphaTwo := by
  have hle := alphaTwo_mem.1
  exact lt_of_le_of_ne hle fun heq ↦ by
    have hpa := profile_alphaTwo
    rw [← heq] at hpa
    linarith [one_lt_profile_one_fourth]

lemma alphaTwo_lt_third : alphaTwo < (1 : ℝ) / 3 := by
  have hle := alphaTwo_mem.2
  exact lt_of_le_of_ne hle fun heq ↦ by
    have hpa := profile_alphaTwo
    rw [heq] at hpa
    linarith [profile_one_third_lt_one]

noncomputable def clampedExponent (u : ℝ) : ℝ :=
  max ((1 : ℝ) / 4) (min u ((1 : ℝ) / 2))

noncomputable def frontierDensity (u : ℝ) : ℝ :=
  max (1 - profile (clampedExponent u)) 0

lemma clampedExponent_mem (u : ℝ) :
    clampedExponent u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) := by
  simp only [clampedExponent, Set.mem_Icc]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

lemma continuous_clampedExponent : Continuous clampedExponent := by
  unfold clampedExponent
  fun_prop

lemma continuous_frontierDensity : Continuous frontierDensity := by
  have hp : Continuous (profile ∘ clampedExponent) :=
    profile_continuousOn.comp_continuous continuous_clampedExponent clampedExponent_mem
  unfold frontierDensity
  exact (continuous_const.sub hp).max continuous_const

lemma profile_ge_one_of_le_alpha {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) (hua : u ≤ alphaTwo) :
    1 ≤ profile u := by
  rcases hua.eq_or_lt with h | h
  · rw [h, profile_alphaTwo]
  · have hs := profile_strictAntiOn hu
      ⟨alphaTwo_mem.1, alphaTwo_mem.2.trans (by norm_num)⟩ h
    rw [profile_alphaTwo] at hs
    exact hs.le

lemma profile_le_one_of_alpha_le {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) (hau : alphaTwo ≤ u) :
    profile u ≤ 1 := by
  rcases hau.eq_or_lt with h | h
  · rw [← h, profile_alphaTwo]
  · have hs := profile_strictAntiOn
      ⟨alphaTwo_mem.1, alphaTwo_mem.2.trans (by norm_num)⟩ hu h
    rw [profile_alphaTwo] at hs
    exact hs.le

lemma clampedExponent_le_alpha {u : ℝ} (hu : u ≤ alphaTwo) :
    clampedExponent u ≤ alphaTwo := by
  simp only [clampedExponent]
  apply max_le alphaTwo_mem.1
  exact (min_le_left _ _).trans hu

lemma frontierDensity_eq_zero {u : ℝ} (hu : u ≤ alphaTwo) :
    frontierDensity u = 0 := by
  rw [frontierDensity, max_eq_right]
  linarith [profile_ge_one_of_le_alpha (clampedExponent_mem u)
    (clampedExponent_le_alpha hu)]

lemma clampedExponent_eq_of_mem {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) :
    clampedExponent u = u := by
  rw [clampedExponent, min_eq_left hu.2, max_eq_right hu.1]

lemma frontierDensity_eq_one_sub_profile {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) (hau : alphaTwo ≤ u) :
    frontierDensity u = 1 - profile u := by
  rw [frontierDensity, clampedExponent_eq_of_mem hu, max_eq_left]
  linarith [profile_le_one_of_alpha_le hu hau]

lemma profile_half : profile ((1 : ℝ) / 2) = 0 := by
  norm_num [profile, twoPrimeProfile]

lemma frontierDensity_eq_one {u : ℝ} (hu : (1 : ℝ) / 2 ≤ u) :
    frontierDensity u = 1 := by
  have hc : clampedExponent u = (1 : ℝ) / 2 := by
    rw [clampedExponent, min_eq_right hu, max_eq_right (by norm_num)]
  rw [frontierDensity, hc, profile_half]
  norm_num

lemma frontierDensity_integral_eq_constant :
    (∫ u in (0 : ℝ)..1, frontierDensity u) = constant := by
  have hInt (a b : ℝ) :
      IntervalIntegrable frontierDensity MeasureTheory.volume a b :=
    continuous_frontierDensity.intervalIntegrable a b
  have hzero : (∫ u in (0 : ℝ)..alphaTwo, frontierDensity u) = 0 := by
    calc
      (∫ u in (0 : ℝ)..alphaTwo, frontierDensity u) =
          ∫ _u in (0 : ℝ)..alphaTwo, 0 := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact frontierDensity_eq_zero (by
          have hq0 : (0 : ℝ) ≤ (1 : ℝ) / 4 := by norm_num
          have ha0 : 0 ≤ alphaTwo := hq0.trans alphaTwo_mem.1
          have hu' : u ∈ Set.Icc (0 : ℝ) alphaTwo := by
            rw [Set.uIcc_of_le ha0] at hu
            exact hu
          exact hu'.2)
      _ = 0 := by simp
  have hmid :
      (∫ u in alphaTwo..(1 : ℝ) / 2, frontierDensity u) =
        ∫ u in alphaTwo..(1 : ℝ) / 2, 1 - profile u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have horder : alphaTwo ≤ (1 : ℝ) / 2 :=
      alphaTwo_mem.2.trans (by norm_num)
    have hua : u ∈ Set.Icc alphaTwo ((1 : ℝ) / 2) := by
      rw [Set.uIcc_of_le horder] at hu
      exact hu
    exact frontierDensity_eq_one_sub_profile
      ⟨alphaTwo_mem.1.trans hua.1, hua.2⟩ hua.1
  have hone : (∫ u in (1 : ℝ) / 2..1, frontierDensity u) = (1 : ℝ) / 2 := by
    calc
      (∫ u in (1 : ℝ) / 2..1, frontierDensity u) =
          ∫ _u in (1 : ℝ) / 2..1, 1 := by
        apply intervalIntegral.integral_congr
        intro u hu
        apply frontierDensity_eq_one
        have hu' : u ∈ Set.Icc ((1 : ℝ) / 2) 1 := by
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hu
          exact hu
        exact hu'.1
      _ = (1 : ℝ) / 2 := by norm_num
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 alphaTwo) (hInt alphaTwo ((1 : ℝ) / 2))
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 ((1 : ℝ) / 2)) (hInt ((1 : ℝ) / 2) 1)
  rw [← hadd2, ← hadd1, hzero, hmid, hone, constant]
  ring

lemma sq_le_of_logCoord_le_half {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (hu : logCoord (N : ℝ) (n : ℝ) ≤ (1 : ℝ) / 2) :
    n ^ 2 ≤ N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogs : 2 * Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    simp only [logCoord] at hu
    have := (div_le_iff₀ hlogN).mp hu
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogs
  have hpow : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    simp [Real.log_pow]
  rw [← hpow, Real.exp_log (by positivity : 0 < (n : ℝ) ^ 2),
    Real.exp_log hNR] at hexp
  exact_mod_cast hexp

lemma lt_fourth_of_quarter_lt_logCoord {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (hu : (1 : ℝ) / 4 < logCoord (N : ℝ) (n : ℝ)) :
    N < n ^ 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogs : Real.log (N : ℝ) < 4 * Real.log (n : ℝ) := by
    simp only [logCoord] at hu
    have := (lt_div_iff₀ hlogN).mp hu
    nlinarith
  have hexp := Real.exp_lt_exp.mpr hlogs
  have hpow : Real.log ((n : ℝ) ^ 4) = 4 * Real.log (n : ℝ) := by
    simp [Real.log_pow]
  rw [← hpow, Real.exp_log hNR,
    Real.exp_log (by positivity : 0 < (n : ℝ) ^ 4)] at hexp
  exact_mod_cast hexp

lemma le_cube_of_third_le_logCoord {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (hu : (1 : ℝ) / 3 ≤ logCoord (N : ℝ) (n : ℝ)) :
    N ≤ n ^ 3 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogs : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    simp only [logCoord] at hu
    have := (le_div_iff₀ hlogN).mp hu
    nlinarith
  have hexp := Real.exp_le_exp.mpr hlogs
  have hpow : Real.log ((n : ℝ) ^ 3) = 3 * Real.log (n : ℝ) := by
    simp [Real.log_pow]
  rw [← hpow, Real.exp_log hNR,
    Real.exp_log (by positivity : 0 < (n : ℝ) ^ 3)] at hexp
  exact_mod_cast hexp

lemma twoPrimeChildMass_eq_zero_of_third_le {N n : ℕ} (hN : 1 < N)
    (hn : 0 < n) (hu : (1 : ℝ) / 3 ≤ logCoord (N : ℝ) (n : ℝ)) :
    twoPrimeChildMass N n = 0 := by
  classical
  have hcube := le_cube_of_third_le_logCoord hN hn hu
  rw [twoPrimeChildMass]
  apply Finset.sum_eq_zero
  intro pq hpq
  have hd := (Finset.mem_filter.mp hpq).2
  obtain ⟨hp, hq, hnp, hpqle, hbound⟩ := hd
  exfalso
  have hnp' : n < pq.2 := hnp.trans_le hpqle
  have : n ^ 3 < n * pq.1 * pq.2 := by
    have hnn_pn : n * n < pq.1 * n := Nat.mul_lt_mul_of_pos_right hnp hn
    have hpn_pp : pq.1 * n < pq.1 * pq.2 :=
      Nat.mul_lt_mul_of_pos_left hnp' hp.pos
    have hsq : n * n < pq.1 * pq.2 := hnn_pn.trans hpn_pp
    have := Nat.mul_lt_mul_of_pos_left hsq hn
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
  omega

lemma inflow_eq_zero_of_half_lt_logCoord {N n : ℕ} (hN : 1 < N)
    (hn : 0 < n) (hu : (1 : ℝ) / 2 < logCoord (N : ℝ) (n : ℝ)) :
    inflow N n = 0 := by
  apply inflow_eq_zero_of_sq_gt hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogs : Real.log (N : ℝ) < 2 * Real.log (n : ℝ) := by
    simp only [logCoord] at hu
    have := (lt_div_iff₀ hlogN).mp hu
    nlinarith
  have hexp := Real.exp_lt_exp.mpr hlogs
  have hpow : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
    simp [Real.log_pow]
  rw [← hpow, Real.exp_log hNR,
    Real.exp_log (by positivity : 0 < (n : ℝ) ^ 2)] at hexp
  have hnat : N < n ^ 2 := by exact_mod_cast hexp
  simpa [pow_two] using hnat

lemma outerEndpoint_ge_succ_of_logCoord_gap {N n : ℕ} {ρ : ℝ}
    (hN : 1 < N) (hn : 0 < n)
    (hu : logCoord (N : ℝ) (n : ℝ) ≤ (1 : ℝ) / 3 - ρ)
    (hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ)) :
    ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hcoord : 3 * Real.log (n : ℝ) ≤
      (1 - 3 * ρ) * Real.log (N : ℝ) := by
    simp only [logCoord] at hu
    have := (div_le_iff₀ hlogN).mp hu
    nlinarith
  have hlogs : Real.log 4 + 3 * Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    nlinarith
  have hpow : Real.log ((n : ℝ) ^ 3) = 3 * Real.log (n : ℝ) := by
    simp [Real.log_pow]
  have hprod : Real.log (4 * (n : ℝ) ^ 3) =
      Real.log 4 + 3 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity), hpow]
  rw [← hprod] at hlogs
  have hexp := Real.exp_le_exp.mpr hlogs
  rw [Real.exp_log (by positivity : 0 < (4 : ℝ) * (n : ℝ) ^ 3),
    Real.exp_log hNR] at hexp
  have hnat : 4 * n ^ 3 ≤ N := by exact_mod_cast hexp
  have hmul : n * (2 * n) * (2 * n) ≤ N := by
    calc
      n * (2 * n) * (2 * n) = 4 * n ^ 3 := by ring
      _ ≤ N := hnat
  have hep := (nat_mul_sq_le_iff_le_outerEndpoint (N := N) hn).1 hmul
  have hs : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  exact hs.trans hep

noncomputable def outerPrimeMass (N n : ℕ) : ℝ :=
  ∑ p ∈ outerPrimeIndices N n, (p : ℝ)⁻¹

lemma outerPrimeIndices_eq_Ioc {N n : ℕ} :
    outerPrimeIndices N n = (Finset.Ioc n N).filter Nat.Prime := by
  classical
  ext p
  simp only [outerPrimeIndices, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpN, hp, hnp⟩
    exact ⟨⟨hnp, by omega⟩, hp⟩
  · rintro ⟨⟨hnp, hpN⟩, hp⟩
    exact ⟨by omega, hp, hnp⟩

lemma outerPrimeMass_eq_sub {N n : ℕ} (hnN : n ≤ N) :
    outerPrimeMass N n = primeReciprocalNat N - primeReciprocalNat n := by
  rw [outerPrimeMass, outerPrimeIndices_eq_Ioc]
  exact primeReciprocal_Ioc_eq_sub hnN

lemma primeChildMass_le_outerPrimeMass {N n : ℕ} :
    primeChildMass N n ≤ outerPrimeMass N n := by
  classical
  rw [primeChildMass, outerPrimeMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hd := (Finset.mem_filter.mp hp)
    exact Finset.mem_filter.mpr ⟨hd.1, hd.2.1, hd.2.2.1⟩
  · intro p hp hnot
    positivity

lemma innerPrimeMass_le_outerPrimeMass {N n p : ℕ}
    (hpOuter : p ∈ outerPrimeIndices N n) :
    innerPrimeMass N n p ≤ outerPrimeMass N n := by
  classical
  rw [innerPrimeMass, outerPrimeMass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have hd := Finset.mem_filter.mp hq
    have hnp := (Finset.mem_filter.mp hpOuter).2.2
    exact Finset.mem_filter.mpr ⟨hd.1, hd.2.1, by omega⟩
  · intro q hq hnot
    positivity

lemma twoPrimeChildMass_le_outerPrimeMass_sq {N n : ℕ} :
    twoPrimeChildMass N n ≤ (outerPrimeMass N n) ^ 2 := by
  rw [twoPrimeChildMass_eq_iterated N n]
  have hmass0 : 0 ≤ outerPrimeMass N n := by
    exact Finset.sum_nonneg fun p hp ↦ by positivity
  calc
    (∑ p ∈ outerPrimeIndices N n, (p : ℝ)⁻¹ * innerPrimeMass N n p) ≤
        ∑ p ∈ outerPrimeIndices N n, (p : ℝ)⁻¹ * outerPrimeMass N n := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (innerPrimeMass_le_outerPrimeMass hp) (by positivity)
    _ = (outerPrimeMass N n) ^ 2 := by
      rw [← Finset.sum_mul, outerPrimeMass]
      ring

lemma outerPrimeMass_le_four {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hnN : n ≤ N)
    (hu : (1 : ℝ) / 4 ≤ logCoord (N : ℝ) (n : ℝ))
    {X : ℝ} (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ 1)
    (hXn : X ≤ (n : ℝ)) :
    outerPrimeMass N n ≤ 4 := by
  have hXN : X ≤ (N : ℝ) := hXn.trans (by exact_mod_cast hnN)
  have hEn := hM (n : ℝ) hXn
  have hEN := hM (N : ℝ) hXN
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hratio : Real.log (N : ℝ) / Real.log (n : ℝ) ≤ 4 := by
    simp only [logCoord] at hu
    apply (div_le_iff₀ hlogn).2
    have := (le_div_iff₀ hlogN).mp hu
    nlinarith
  have hratio0 : 0 < Real.log (N : ℝ) / Real.log (n : ℝ) :=
    div_pos hlogN hlogn
  have hlogratio : Real.log (Real.log (N : ℝ) / Real.log (n : ℝ)) < 2 := by
    have hm := Real.strictMonoOn_log.monotoneOn
      (show Real.log (N : ℝ) / Real.log (n : ℝ) ∈ Set.Ioi 0 by exact hratio0)
      (show (4 : ℝ) ∈ Set.Ioi 0 by norm_num) hratio
    have hlog4 : Real.log 4 < 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [log_two_lt_one]
    exact hm.trans_lt hlog4
  rw [outerPrimeMass_eq_sub hnN, primeReciprocalNat_eq_summatory,
    primeReciprocalNat_eq_summatory]
  have hmain : Real.log (Real.log (N : ℝ)) - Real.log (Real.log (n : ℝ)) =
      Real.log (Real.log (N : ℝ) / Real.log (n : ℝ)) := by
    rw [Real.log_div hlogN.ne' hlogn.ne']
  simp only [primeReciprocalError] at hEn hEN
  rw [abs_le] at hEn hEN
  linarith

lemma local_divergence_abs_le_twenty_one {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hnN : n ≤ N)
    (huq : (1 : ℝ) / 4 < logCoord (N : ℝ) (n : ℝ))
    {X : ℝ} (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ 1)
    (hXn : X ≤ (n : ℝ)) :
    |divergence N n| ≤ 21 * weight n := by
  have hscale := lt_fourth_of_quarter_lt_logCoord hN (by omega) huq
  have hP := primeChildMass_le_outerPrimeMass (N := N) (n := n)
  have hO := outerPrimeMass_le_four hN hn hnN huq.le hM hXn
  have hQ := twoPrimeChildMass_le_outerPrimeMass_sq (N := N) (n := n)
  have hP0 : 0 ≤ primeChildMass N n := Finset.sum_nonneg fun p hp ↦ by positivity
  have hQ0 : 0 ≤ twoPrimeChildMass N n := Finset.sum_nonneg fun p hp ↦ by positivity
  have hO0 : 0 ≤ outerPrimeMass N n := Finset.sum_nonneg fun p hp ↦ by positivity
  rw [divergence_eq_local_formula (by omega) hscale, abs_mul,
    abs_of_nonneg (by unfold weight; positivity)]
  have hfactor : |1 - primeChildMass N n - twoPrimeChildMass N n| ≤ 21 := by
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (outerPrimeMass N n - 2)]
  have hw : 0 ≤ weight n := by unfold weight; positivity
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hfactor hw

noncomputable def beta : ℝ := (13 : ℝ) / 50

lemma beta_bounds : (1 : ℝ) / 4 < beta ∧ beta < (1 : ℝ) / 3 := by
  norm_num [beta]

lemma one_lt_base_beta :
    1 < Real.log ((1 - beta) / beta) := by
  have hexp : Real.exp 1 < (1 - beta) / beta := by
    exact Real.exp_one_lt_d9.trans (by norm_num [beta])
  have h := Real.strictMonoOn_log
    (show Real.exp 1 ∈ Set.Ioi 0 by exact Real.exp_pos 1)
    (show (1 - beta) / beta ∈ Set.Ioi 0 by norm_num [beta]) hexp
  simpa using h

lemma beta_lt_alphaTwo : beta < alphaTwo := by
  have hbmem : beta ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) :=
    ⟨beta_bounds.1.le, beta_bounds.2.le.trans (by norm_num)⟩
  by_contra h
  have hle : alphaTwo ≤ beta := le_of_not_gt h
  have hp := profile_le_one_of_alpha_le hbmem hle
  have htwo : 0 ≤ twoPrimeProfile beta :=
    twoPrimeProfile_nonneg ⟨beta_bounds.1.le, beta_bounds.2.le⟩
  rw [profile] at hp
  linarith [one_lt_base_beta]

lemma primeChildSet_subset_children {N n : ℕ} (hn : 0 < n) :
    primeChildSet N n ⊆ children N n := by
  intro m hm
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
  have hd := (Finset.mem_filter.mp hp)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨?_, hd.2.2.2⟩, ?_⟩
  · exact Nat.mul_pos hn hd.2.1.pos
  · exact prime_extension_is_child hn hd.2.1 hd.2.2.1

lemma weight_mul_primeChildMass_le_inflow {N n : ℕ} (hn : 0 < n) :
    weight n * primeChildMass N n ≤ inflow N n := by
  rw [← sum_primeChildSet hn, inflow_eq_sum_children]
  exact Finset.sum_le_sum_of_subset_of_nonneg (primeChildSet_subset_children hn)
    (fun m hm hnot ↦ by unfold weight; positivity)

lemma divergence_nonpos_of_primeChildMass_one_le {N n : ℕ} (hn : 0 < n)
    (hP : 1 ≤ primeChildMass N n) :
    divergence N n ≤ 0 := by
  have hw : 0 ≤ weight n := by unfold weight; positivity
  have hin := weight_mul_primeChildMass_le_inflow (N := N) hn
  rw [divergence]
  nlinarith [mul_le_mul_of_nonneg_left hP hw]

lemma base_beta_le_of_logCoord_le_beta {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hu : logCoord (N : ℝ) (n : ℝ) ≤ beta) :
    Real.log ((1 - beta) / beta) ≤
      Real.log ((1 - logCoord (N : ℝ) (n : ℝ)) /
        logCoord (N : ℝ) (n : ℝ)) := by
  let u := logCoord (N : ℝ) (n : ℝ)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hu0 : 0 < u := div_pos hlogn hlogN
  have hb0 : 0 < beta := by norm_num [beta]
  have hb1 : beta < 1 := by norm_num [beta]
  have hratio : (1 - beta) / beta ≤ (1 - u) / u := by
    apply (div_le_div_iff₀ hb0 hu0).2
    linarith
  exact Real.strictMonoOn_log.monotoneOn
    (show (1 - beta) / beta ∈ Set.Ioi 0 by exact div_pos (sub_pos.mpr hb1) hb0)
    (show (1 - u) / u ∈ Set.Ioi 0 by
      exact div_pos (sub_pos.mpr (hu.trans_lt hb1)) hu0) hratio

lemma low_divergence_nonpos {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hu : logCoord (N : ℝ) (n : ℝ) ≤ beta)
    {X ε : ℝ}
    (hmargin : 2 * ε < Real.log ((1 - beta) / beta) - 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) :
    divergence N n ≤ 0 := by
  have hsq : n * n ≤ N := by
    have hs := sq_le_of_logCoord_le_half (n := n) hN (by omega)
      (hu.trans (beta_bounds.2.le.trans (by norm_num)))
    simpa [pow_two] using hs
  have herr := primeChildMass_profile_error hn hsq hM hXn
  have hbase := base_beta_le_of_logCoord_le_beta hN hn hu
  have hP : 1 ≤ primeChildMass N n := by
    rw [abs_lt] at herr
    linarith
  exact divergence_nonpos_of_primeChildMass_one_le (by omega) hP

lemma local_divergence_profile_error_lower {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hlogN : 1 ≤ Real.log (N : ℝ)) (hlogn : 1 ≤ Real.log (n : ℝ))
    (huq : (1 : ℝ) / 4 < logCoord (N : ℝ) (n : ℝ))
    (hut : logCoord (N : ℝ) (n : ℝ) < (1 : ℝ) / 3)
    (hendpoint : ((n + 1 : ℕ) : ℝ) ≤ outerEndpoint N n)
    {X ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) :
    |divergence N n - weight n *
        (1 - profile (logCoord (N : ℝ) (n : ℝ)))| ≤
      weight n * (10 * ε + 6 * (n : ℝ)⁻¹) := by
  let u := logCoord (N : ℝ) (n : ℝ)
  have hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 3) := ⟨huq.le, hut.le⟩
  have hsqNat := sq_le_of_logCoord_le_half hN (by omega)
    (hut.le.trans (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2))
  have hsq : n * n ≤ N := by simpa [pow_two] using hsqNat
  have hP := primeChildMass_profile_error hn hsq hM hXn
  have hQ := twoPrimeChildMass_profile_error hn hendpoint hlogN hlogn hu hut
    hε0 hε1 hM hXn
  change |primeChildMass N n - Real.log ((1 - u) / u)| < 2 * ε at hP
  change |twoPrimeChildMass N n - twoPrimeProfile u| ≤
    8 * ε + 6 * (n : ℝ)⁻¹ at hQ
  have hscale := lt_fourth_of_quarter_lt_logCoord hN (by omega) huq
  have hw : 0 ≤ weight n := by unfold weight; positivity
  rw [divergence_eq_local_formula (by omega) hscale, profile]
  have hfactor :
      |(1 - primeChildMass N n - twoPrimeChildMass N n) -
        (1 - (Real.log ((1 - u) / u) + twoPrimeProfile u))| ≤
          10 * ε + 6 * (n : ℝ)⁻¹ := by
    have hP' : |Real.log ((1 - u) / u) - primeChildMass N n| ≤ 2 * ε := by
      simpa [abs_sub_comm] using hP.le
    have hQ' : |twoPrimeProfile u - twoPrimeChildMass N n| ≤
        8 * ε + 6 * (n : ℝ)⁻¹ := by
      simpa [abs_sub_comm] using hQ
    calc
      |(1 - primeChildMass N n - twoPrimeChildMass N n) -
          (1 - (Real.log ((1 - u) / u) + twoPrimeProfile u))| =
          |(Real.log ((1 - u) / u) - primeChildMass N n) +
            (twoPrimeProfile u - twoPrimeChildMass N n)| := by ring_nf
      _ ≤ |Real.log ((1 - u) / u) - primeChildMass N n| +
          |twoPrimeProfile u - twoPrimeChildMass N n| := abs_add_le _ _
      _ ≤ 2 * ε + (8 * ε + 6 * (n : ℝ)⁻¹) :=
        add_le_add hP' hQ'
      _ = 10 * ε + 6 * (n : ℝ)⁻¹ := by ring
  have halg :
      weight n * (1 - primeChildMass N n - twoPrimeChildMass N n) -
          weight n * (1 - (Real.log ((1 - u) / u) + twoPrimeProfile u)) =
        weight n * ((1 - primeChildMass N n - twoPrimeChildMass N n) -
          (1 - (Real.log ((1 - u) / u) + twoPrimeProfile u))) := by ring
  rw [halg, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left hfactor hw

lemma local_divergence_profile_error_upper {N n : ℕ} (hN : 1 < N) (hn : 1 < n)
    (hut : (1 : ℝ) / 3 ≤ logCoord (N : ℝ) (n : ℝ))
    (huh : logCoord (N : ℝ) (n : ℝ) ≤ (1 : ℝ) / 2)
    {X ε : ℝ}
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < ε)
    (hXn : X ≤ (n : ℝ)) :
    |divergence N n - weight n *
        (1 - profile (logCoord (N : ℝ) (n : ℝ)))| <
      weight n * (2 * ε) := by
  let u := logCoord (N : ℝ) (n : ℝ)
  have hsqNat := sq_le_of_logCoord_le_half hN (by omega) huh
  have hsq : n * n ≤ N := by simpa [pow_two] using hsqNat
  have hP := primeChildMass_profile_error hn hsq hM hXn
  have hQ := twoPrimeChildMass_eq_zero_of_third_le hN (by omega) hut
  have hscale := lt_fourth_of_quarter_lt_logCoord hN (by omega)
    ((by norm_num : (1 : ℝ) / 4 < 1 / 3).trans_le hut)
  have htwo : twoPrimeProfile u = 0 := by
    rw [twoPrimeProfile, if_neg]
    exact not_lt_of_ge hut
  have hw : 0 < weight n := by unfold weight; positivity
  rw [divergence_eq_local_formula (by omega) hscale, profile, hQ, htwo]
  simp only [sub_zero, add_zero]
  change |weight n * (1 - primeChildMass N n) -
    weight n * (1 - Real.log ((1 - u) / u))| < weight n * (2 * ε)
  have hfactor :
      |(1 - primeChildMass N n) - (1 - Real.log ((1 - u) / u))| < 2 * ε := by
    simpa [abs_sub_comm] using hP
  have halg :
      weight n * (1 - primeChildMass N n) -
          weight n * (1 - Real.log ((1 - u) / u)) =
        weight n * ((1 - primeChildMass N n) -
          (1 - Real.log ((1 - u) / u))) := by ring
  rw [halg, abs_mul, abs_of_pos hw]
  exact mul_lt_mul_of_pos_left hfactor hw

lemma le_sq_of_half_le_logCoord {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (hu : (1 : ℝ) / 2 ≤ logCoord (N : ℝ) (n : ℝ)) :
    N ≤ n ^ 2 := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hmul : Real.log (N : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    simp only [logCoord] at hu
    have := (le_div_iff₀ hlogN).mp hu
    linarith
  have hlogpow : Real.log ((N : ℝ)) ≤ Real.log ((n : ℝ) ^ 2) := by
    rw [Real.log_pow]
    norm_num
    exact hmul
  have hreal : (N : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hexp := Real.exp_le_exp.mpr hlogpow
    rw [Real.exp_log (by positivity : (0 : ℝ) < N),
      Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)] at hexp
    exact hexp
  exact_mod_cast hreal

lemma primeChildMass_eq_zero_of_half_le {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    (hu : (1 : ℝ) / 2 ≤ logCoord (N : ℝ) (n : ℝ)) :
    primeChildMass N n = 0 := by
  classical
  have hsq := le_sq_of_half_le_logCoord hN hn hu
  rw [primeChildMass]
  apply Finset.sum_eq_zero
  intro p hp
  have hd := (Finset.mem_filter.mp hp).2
  exfalso
  have hlt : n * n < n * p := Nat.mul_lt_mul_of_pos_left hd.2.1 hn
  have hbound : n * p ≤ N := hd.2.2
  have hsq' : N ≤ n * n := by simpa [pow_two] using hsq
  omega

lemma divergence_eq_weight_of_half_le_logCoord {N n : ℕ} (hN : 1 < N)
    (hn : 0 < n) (hu : (1 : ℝ) / 2 ≤ logCoord (N : ℝ) (n : ℝ)) :
    divergence N n = weight n := by
  by_cases heq : logCoord (N : ℝ) (n : ℝ) = (1 : ℝ) / 2
  · have hscale := lt_fourth_of_quarter_lt_logCoord hN hn
      ((by norm_num : (1 : ℝ) / 4 < 1 / 2).trans_eq heq.symm)
    rw [divergence_eq_local_formula hn hscale,
      primeChildMass_eq_zero_of_half_le hN hn hu,
      twoPrimeChildMass_eq_zero_of_third_le hN hn
        ((by norm_num : (1 : ℝ) / 3 ≤ 1 / 2).trans_eq heq.symm)]
    ring
  · have hz := inflow_eq_zero_of_half_lt_logCoord hN hn
      (lt_of_le_of_ne hu (Ne.symm heq))
    simp [divergence, hz]

lemma profile_nonneg_on_quarter_half {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) : 0 ≤ profile u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num) hu.1
  have hratio : 1 ≤ (1 - u) / u := by
    apply (le_div_iff₀ hu0).2
    linarith [hu.2]
  have hbase : 0 ≤ Real.log ((1 - u) / u) := Real.log_nonneg hratio
  have htwo : 0 ≤ twoPrimeProfile u := by
    by_cases hut : u ≤ (1 : ℝ) / 3
    · exact twoPrimeProfile_nonneg ⟨hu.1, hut⟩
    · rw [twoPrimeProfile, if_neg (not_lt_of_ge (le_of_not_ge hut))]
  exact add_nonneg hbase htwo

lemma frontierDensity_nonneg (u : ℝ) : 0 ≤ frontierDensity u := by
  exact le_max_right _ _

lemma frontierDensity_le_one (u : ℝ) : frontierDensity u ≤ 1 := by
  rw [frontierDensity]
  exact max_le (by linarith [profile_nonneg_on_quarter_half (clampedExponent_mem u)])
    (by norm_num)

lemma inflow_nonneg (N n : ℕ) : 0 ≤ inflow N n := by
  unfold inflow
  exact Finset.sum_nonneg fun m hm ↦ by unfold weight; positivity

lemma divergence_le_weight (N n : ℕ) : divergence N n ≤ weight n := by
  unfold divergence
  linarith [inflow_nonneg N n]

lemma max_divergence_nonneg (N n : ℕ) :
    0 ≤ max (divergence N n) 0 := le_max_right _ _

lemma max_divergence_le_weight {N n : ℕ} (hn : 0 < n) :
    max (divergence N n) 0 ≤ weight n := by
  exact max_le (divergence_le_weight N n) (by unfold weight; positivity)

lemma interval_eq_Ico (N : ℕ) : interval N = Finset.Ico 1 (N + 1) := by
  ext n
  simp [interval]

lemma sum_interval_eq_sum_range_succ {M : Type*} [AddCommMonoid M]
    (g : ℕ → M) (N : ℕ) :
    ∑ n ∈ interval N, g n = ∑ k ∈ Finset.range N, g (k + 1) := by
  rw [interval_eq_Ico, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

lemma normalized_interval_sum_eq_logHarmonicRiemannSum (f : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ interval N,
      weight n * f (logCoord (N : ℝ) (n : ℝ)) / Real.log (N : ℝ)) =
      logHarmonicRiemannSum f N := by
  rw [sum_interval_eq_sum_range_succ]
  unfold logHarmonicRiemannSum
  apply Finset.sum_congr rfl
  intro k hk
  unfold weight
  ring

lemma max_zero_sub_max_zero_abs_le {a b : ℝ} :
    |max a 0 - max b 0| ≤ |a - b| := by
  exact abs_max_sub_max_le_abs a b 0

noncomputable def junctionBump (ρ u : ℝ) : ℝ :=
  max (1 - max (|u - (1 : ℝ) / 3| - ρ) 0 / ρ) 0

lemma continuous_junctionBump (ρ : ℝ) : Continuous (junctionBump ρ) := by
  unfold junctionBump
  fun_prop

lemma junctionBump_nonneg (ρ u : ℝ) : 0 ≤ junctionBump ρ u := by
  exact le_max_right _ _

lemma junctionBump_le_one {ρ u : ℝ} (hρ : 0 < ρ) : junctionBump ρ u ≤ 1 := by
  unfold junctionBump
  apply max_le
  · have hi : 0 ≤ max (|u - (1 : ℝ) / 3| - ρ) 0 / ρ :=
      div_nonneg (le_max_right _ _) hρ.le
    linarith
  · norm_num

lemma junctionBump_eq_one {ρ u : ℝ}
    (hu : |u - (1 : ℝ) / 3| ≤ ρ) : junctionBump ρ u = 1 := by
  have hz : max (|u - (1 : ℝ) / 3| - ρ) 0 = 0 := by
    rw [max_eq_right]
    linarith
  unfold junctionBump
  change max (1 - max (|u - (1 : ℝ) / 3| - ρ) 0 / ρ) 0 = 1
  rw [hz]
  norm_num

lemma junctionBump_eq_zero {ρ u : ℝ} (hρ : 0 < ρ)
    (hu : 2 * ρ ≤ |u - (1 : ℝ) / 3|) : junctionBump ρ u = 0 := by
  have hinner : ρ ≤ max (|u - (1 : ℝ) / 3| - ρ) 0 := by
    exact (show ρ ≤ |u - (1 : ℝ) / 3| - ρ by linarith).trans (le_max_left _ _)
  have hquot : 1 ≤ max (|u - (1 : ℝ) / 3| - ρ) 0 / ρ := by
    exact (le_div_iff₀ hρ).2 (by simpa using hinner)
  rw [junctionBump, max_eq_right]
  linarith

lemma junctionBump_integral_le {ρ : ℝ} (hρ : 0 < ρ)
    (hρsmall : ρ ≤ (1 : ℝ) / 12) :
    (∫ u in (0 : ℝ)..1, junctionBump ρ u) ≤ 4 * ρ := by
  let a : ℝ := (1 : ℝ) / 3 - 2 * ρ
  let b : ℝ := (1 : ℝ) / 3 + 2 * ρ
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hInt (x y : ℝ) :
      IntervalIntegrable (junctionBump ρ) MeasureTheory.volume x y :=
    (continuous_junctionBump ρ).intervalIntegrable x y
  have hleft : (∫ u in (0 : ℝ)..a, junctionBump ρ u) = 0 := by
    calc
      (∫ u in (0 : ℝ)..a, junctionBump ρ u) = ∫ _u in (0 : ℝ)..a, 0 := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hua : u ∈ Set.Icc (0 : ℝ) a := by
          rw [Set.uIcc_of_le ha0] at hu
          exact hu
        apply junctionBump_eq_zero hρ
        rw [abs_of_nonpos]
        · dsimp [a] at hua
          linarith [hua.2]
        · dsimp [a] at hua
          linarith [hua.2]
      _ = 0 := by simp
  have hright : (∫ u in b..(1 : ℝ), junctionBump ρ u) = 0 := by
    calc
      (∫ u in b..(1 : ℝ), junctionBump ρ u) = ∫ _u in b..(1 : ℝ), 0 := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hub : u ∈ Set.Icc b (1 : ℝ) := by
          rw [Set.uIcc_of_le hb1] at hu
          exact hu
        apply junctionBump_eq_zero hρ
        rw [abs_of_nonneg]
        · dsimp [b] at hub
          linarith [hub.1]
        · dsimp [b] at hub
          linarith [hub.1]
      _ = 0 := by simp
  have hmid : (∫ u in a..b, junctionBump ρ u) ≤ 4 * ρ := by
    calc
      (∫ u in a..b, junctionBump ρ u) ≤ ∫ _u in a..b, 1 := by
        exact intervalIntegral.integral_mono_on hab (hInt a b) (by simp)
          (fun u hu ↦ junctionBump_le_one hρ)
      _ = 4 * ρ := by simp [a, b]; ring
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals (hInt 0 a) (hInt a b)
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (hInt 0 b) (hInt b 1)
  rw [← hadd2, ← hadd1, hleft, hright]
  simpa using hmid

lemma logCoord_mem_unit {N n : ℕ} (hN : 1 < N) (hn : n ∈ interval N) :
    logCoord (N : ℝ) (n : ℝ) ∈ Set.Icc 0 1 := by
  have hd := Finset.mem_Icc.mp hn
  have hnpos : 0 < n := by omega
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd.1)
  have hlogle : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show 0 < (n : ℝ) by exact_mod_cast hnpos)
      (show 0 < (N : ℝ) by positivity)
      (by exact_mod_cast hd.2)
  exact ⟨div_nonneg hlogn0 hlogN.le, (div_le_one hlogN).2 hlogle⟩

lemma weighted_frontierDensity_eq_max {n : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2)) :
    weight n * frontierDensity u = max (weight n * (1 - profile u)) 0 := by
  have hw : 0 ≤ weight n := by unfold weight; positivity
  rw [frontierDensity, clampedExponent_eq_of_mem hu, mul_max_of_nonneg _ _ hw]
  simp

lemma cutoff_log_lower {J n : ℕ} (hJ : 0 < J) (hJn : J ≤ n)
    (hlogJ : 1 ≤ Real.log (J : ℝ)) : 1 ≤ Real.log (n : ℝ) := by
  exact hlogJ.trans (Real.strictMonoOn_log.monotoneOn
    (show 0 < (J : ℝ) by exact_mod_cast hJ)
    (show 0 < (n : ℝ) by exact_mod_cast hJ.trans_le hJn)
    (by exact_mod_cast hJn))

lemma cutoff_inv_upper {J n : ℕ} (hJ : 0 < J) (hJn : J ≤ n) :
    (n : ℝ)⁻¹ ≤ (J : ℝ)⁻¹ := by
  exact inv_anti₀ (by exact_mod_cast hJ : (0 : ℝ) < J) (by exact_mod_cast hJn)

lemma positive_pointwise_comparison {N n J : ℕ} {X η ρ : ℝ}
    (hN : 1 < N) (hnN : n ∈ interval N) (hJn : J ≤ n)
    (hJ : 1 < J) (hlogJ : 1 ≤ Real.log (J : ℝ))
    (hXJ : X ≤ (J : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hJinv : (J : ℝ)⁻¹ ≤ η) (hρ : 0 < ρ)
    (hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ))
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hmargin : 2 * η < Real.log ((1 - beta) / beta) - 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < η) :
    |max (divergence N n) 0 -
        weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ))| ≤
      weight n * (16 * η + 22 * junctionBump ρ (logCoord (N : ℝ) (n : ℝ))) := by
  let u := logCoord (N : ℝ) (n : ℝ)
  have hnpos : 0 < n := by
    have := (Finset.mem_Icc.mp hnN).1
    omega
  have hn : 1 < n := hJ.trans_le hJn
  have hJnR : (J : ℝ) ≤ n := by exact_mod_cast hJn
  have hXn : X ≤ (n : ℝ) := hXJ.trans hJnR
  have hlogn : 1 ≤ Real.log (n : ℝ) := cutoff_log_lower (by omega) hJn hlogJ
  have hninv : (n : ℝ)⁻¹ ≤ η := (cutoff_inv_upper (by omega) hJn).trans hJinv
  have hu01 : u ∈ Set.Icc 0 1 := logCoord_mem_unit hN hnN
  have hw : 0 ≤ weight n := by unfold weight; positivity
  have hb0 : 0 ≤ junctionBump ρ u := junctionBump_nonneg ρ u
  by_cases hub : u ≤ beta
  · have hd := low_divergence_nonpos hN hn hub hmargin hM hXn
    have hf : frontierDensity u = 0 := frontierDensity_eq_zero (hub.trans beta_lt_alphaTwo.le)
    rw [max_eq_right hd, hf, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hw (by positivity)
  · have hbu : beta < u := lt_of_not_ge hub
    have huq : (1 : ℝ) / 4 < u := beta_bounds.1.trans hbu
    by_cases hleft : u < (1 : ℝ) / 3 - ρ
    · have hut : u < (1 : ℝ) / 3 := by linarith
      have hep := outerEndpoint_ge_succ_of_logCoord_gap hN hnpos hleft.le hlarge
      have herr := local_divergence_profile_error_lower hN hn hlogN hlogn huq hut hep
        hη.le hη1 hM hXn
      have htarget := weighted_frontierDensity_eq_max (n := n)
        (show u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) by
          exact ⟨huq.le, hut.le.trans (by norm_num)⟩)
      rw [htarget]
      calc
        |max (divergence N n) 0 - max (weight n * (1 - profile u)) 0| ≤
            |divergence N n - weight n * (1 - profile u)| :=
          max_zero_sub_max_zero_abs_le
        _ ≤ weight n * (10 * η + 6 * (n : ℝ)⁻¹) := herr
        _ ≤ weight n * (16 * η + 22 * junctionBump ρ u) := by
          apply mul_le_mul_of_nonneg_left _ hw
          nlinarith
    · by_cases hut : (1 : ℝ) / 3 ≤ u
      · by_cases huh : u ≤ (1 : ℝ) / 2
        · have herr := local_divergence_profile_error_upper hN hn hut huh hM hXn
          have htarget := weighted_frontierDensity_eq_max (n := n)
            (show u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) by
              exact ⟨huq.le, huh⟩)
          rw [htarget]
          calc
            |max (divergence N n) 0 - max (weight n * (1 - profile u)) 0| ≤
                |divergence N n - weight n * (1 - profile u)| :=
              max_zero_sub_max_zero_abs_le
            _ ≤ weight n * (2 * η) := herr.le
            _ ≤ weight n * (16 * η + 22 * junctionBump ρ u) := by
              apply mul_le_mul_of_nonneg_left _ hw
              nlinarith
        · have huh' : (1 : ℝ) / 2 ≤ u := le_of_not_ge huh
          rw [divergence_eq_weight_of_half_le_logCoord hN hnpos huh',
            frontierDensity_eq_one huh']
          rw [max_eq_left hw]
          simp only [mul_one, sub_self, abs_zero, ge_iff_le]
          exact mul_nonneg hw (add_nonneg (by positivity) (mul_nonneg (by norm_num) hb0))
      · have hut' : u < (1 : ℝ) / 3 := lt_of_not_ge hut
        have hbandlo : (1 : ℝ) / 3 - ρ ≤ u := le_of_not_gt hleft
        have hbump : junctionBump ρ u = 1 := by
          apply junctionBump_eq_one
          rw [abs_of_nonpos (sub_nonpos.mpr hut'.le)]
          linarith
        have hmd0 := max_divergence_nonneg N n
        have hmdw := max_divergence_le_weight (N := N) hnpos
        have ht0 : 0 ≤ weight n * frontierDensity u :=
          mul_nonneg hw (frontierDensity_nonneg u)
        have htw : weight n * frontierDensity u ≤ weight n := by
          simpa using mul_le_mul_of_nonneg_left (frontierDensity_le_one u) hw
        rw [hbump]
        rw [abs_le]
        constructor <;> nlinarith

lemma raw_pointwise_comparison {N n J : ℕ} {X η ρ : ℝ}
    (hN : 1 < N) (hnN : n ∈ interval N) (hJn : J ≤ n)
    (hJ : 1 < J) (hlogJ : 1 ≤ Real.log (J : ℝ))
    (hXJ : X ≤ (J : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hJinv : (J : ℝ)⁻¹ ≤ η) (hρ : 0 < ρ)
    (hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ))
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hau : alphaTwo < logCoord (N : ℝ) (n : ℝ))
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < η) :
    |divergence N n -
        weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ))| ≤
      weight n * (16 * η + 22 * junctionBump ρ (logCoord (N : ℝ) (n : ℝ))) := by
  let u := logCoord (N : ℝ) (n : ℝ)
  have hnpos : 0 < n := by
    have := (Finset.mem_Icc.mp hnN).1
    omega
  have hn : 1 < n := hJ.trans_le hJn
  have hXn : X ≤ (n : ℝ) := hXJ.trans (by exact_mod_cast hJn)
  have hlogn : 1 ≤ Real.log (n : ℝ) := cutoff_log_lower (by omega) hJn hlogJ
  have hninv : (n : ℝ)⁻¹ ≤ η := (cutoff_inv_upper (by omega) hJn).trans hJinv
  have hu01 : u ∈ Set.Icc 0 1 := logCoord_mem_unit hN hnN
  have hbu : beta < u := beta_lt_alphaTwo.trans hau
  have huq : (1 : ℝ) / 4 < u := beta_bounds.1.trans hbu
  have hw : 0 ≤ weight n := by unfold weight; positivity
  have hb0 : 0 ≤ junctionBump ρ u := junctionBump_nonneg ρ u
  by_cases hleft : u < (1 : ℝ) / 3 - ρ
  · have hut : u < (1 : ℝ) / 3 := by linarith
    have hep := outerEndpoint_ge_succ_of_logCoord_gap hN hnpos hleft.le hlarge
    have herr := local_divergence_profile_error_lower hN hn hlogN hlogn huq hut hep
      hη.le hη1 hM hXn
    have htarget := weighted_frontierDensity_eq_max (n := n)
      (show u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) by
        exact ⟨huq.le, hut.le.trans (by norm_num)⟩)
    have hnonneg : 0 ≤ weight n * (1 - profile u) := by
      exact mul_nonneg hw (sub_nonneg.mpr (profile_le_one_of_alpha_le
        ⟨huq.le, hut.le.trans (by norm_num)⟩ hau.le))
    rw [htarget, max_eq_left hnonneg]
    calc
      |divergence N n - weight n * (1 - profile u)| ≤
          weight n * (10 * η + 6 * (n : ℝ)⁻¹) := herr
      _ ≤ weight n * (16 * η + 22 * junctionBump ρ u) := by
        apply mul_le_mul_of_nonneg_left _ hw
        nlinarith
  · by_cases hut : (1 : ℝ) / 3 ≤ u
    · by_cases huh : u ≤ (1 : ℝ) / 2
      · have herr := local_divergence_profile_error_upper hN hn hut huh hM hXn
        have htarget := weighted_frontierDensity_eq_max (n := n)
          (show u ∈ Set.Icc ((1 : ℝ) / 4) (1 / 2) by exact ⟨huq.le, huh⟩)
        have hnonneg : 0 ≤ weight n * (1 - profile u) := by
          exact mul_nonneg hw (sub_nonneg.mpr (profile_le_one_of_alpha_le
            ⟨huq.le, huh⟩ hau.le))
        rw [htarget, max_eq_left hnonneg]
        exact herr.le.trans (mul_le_mul_of_nonneg_left (by nlinarith) hw)
      · have huh' : (1 : ℝ) / 2 ≤ u := le_of_not_ge huh
        rw [divergence_eq_weight_of_half_le_logCoord hN hnpos huh',
          frontierDensity_eq_one huh']
        simp only [mul_one, sub_self, abs_zero, ge_iff_le]
        exact mul_nonneg hw (by positivity)
    · have hut' : u < (1 : ℝ) / 3 := lt_of_not_ge hut
      have hbandlo : (1 : ℝ) / 3 - ρ ≤ u := le_of_not_gt hleft
      have hbump : junctionBump ρ u = 1 := by
        apply junctionBump_eq_one
        rw [abs_of_nonpos (sub_nonpos.mpr hut'.le)]
        linarith
      have hM1 : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| ≤ 1 := by
        intro x hx
        exact (hM x hx).le.trans hη1
      have hdabs := local_divergence_abs_le_twenty_one hN hn
        (Finset.mem_Icc.mp hnN).2 huq hM1 hXn
      have ht0 : 0 ≤ weight n * frontierDensity u :=
        mul_nonneg hw (frontierDensity_nonneg u)
      have htw : weight n * frontierDensity u ≤ weight n := by
        simpa using mul_le_mul_of_nonneg_left (frontierDensity_le_one u) hw
      rw [hbump]
      calc
        |divergence N n - weight n * frontierDensity u| ≤
            |divergence N n| + |weight n * frontierDensity u| := abs_sub _ _
        _ ≤ 21 * weight n + weight n := by
          rw [abs_of_nonneg ht0]
          exact add_le_add hdabs htw
        _ ≤ weight n * (16 * η + 22 * 1) := by nlinarith

noncomputable def modelMass (N : ℕ) : ℝ :=
  ∑ n ∈ interval N, weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ))

noncomputable def harmonicIntervalMass (N : ℕ) : ℝ :=
  ∑ n ∈ interval N, weight n

noncomputable def bumpMass (ρ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ interval N, weight n * junctionBump ρ (logCoord (N : ℝ) (n : ℝ))

lemma modelMass_div_log (N : ℕ) :
    modelMass N / Real.log (N : ℝ) =
      logHarmonicRiemannSum frontierDensity N := by
  rw [modelMass, ← normalized_interval_sum_eq_logHarmonicRiemannSum]
  rw [Finset.sum_div]

lemma harmonicIntervalMass_div_log (N : ℕ) :
    harmonicIntervalMass N / Real.log (N : ℝ) =
      logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N := by
  rw [harmonicIntervalMass, ← normalized_interval_sum_eq_logHarmonicRiemannSum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

lemma bumpMass_div_log (ρ : ℝ) (N : ℕ) :
    bumpMass ρ N / Real.log (N : ℝ) =
      logHarmonicRiemannSum (junctionBump ρ) N := by
  rw [bumpMass, ← normalized_interval_sum_eq_logHarmonicRiemannSum]
  rw [Finset.sum_div]

lemma small_weight_sum_le (N J : ℕ) :
    (∑ n ∈ interval N, if n < J then weight n else 0) ≤ J := by
  let S := (interval N).filter fun n ↦ n < J
  have hsum : (∑ n ∈ interval N, if n < J then weight n else 0) =
      ∑ n ∈ S, weight n := by
    dsimp [S]
    rw [Finset.sum_filter]
  rw [hsum]
  calc
    (∑ n ∈ S, weight n) ≤ ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnI := (Finset.mem_filter.mp hn).1
      have hn1 := (Finset.mem_Icc.mp hnI).1
      unfold weight
      rw [inv_le_one₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)]
      exact_mod_cast hn1
    _ = S.card := by simp
    _ ≤ J := by
      have hc : S.card ≤ J := by
        simpa using Finset.card_le_card (show S ⊆ Finset.range J by
          intro n hn
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2)
      exact_mod_cast hc

lemma positive_normalized_error_bound {N J : ℕ} {X η ρ : ℝ}
    (hN : 1 < N) (hJ : 1 < J) (hlogJ : 1 ≤ Real.log (J : ℝ))
    (hXJ : X ≤ (J : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hJinv : (J : ℝ)⁻¹ ≤ η) (hρ : 0 < ρ)
    (hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ))
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hmargin : 2 * η < Real.log ((1 - beta) / beta) - 1)
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < η) :
    |positiveDivergenceMass N / Real.log (N : ℝ) -
        logHarmonicRiemannSum frontierDensity N| ≤
      (J : ℝ) / Real.log (N : ℝ) +
        16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
        22 * logHarmonicRiemannSum (junctionBump ρ) N := by
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  let L : ℕ → ℝ := fun n ↦
    weight n * (16 * η + 22 * junctionBump ρ (logCoord (N : ℝ) (n : ℝ)))
  have hnum : |positiveDivergenceMass N - modelMass N| ≤
      (J : ℝ) + 16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N := by
    rw [positiveDivergenceMass, modelMass, ← Finset.sum_sub_distrib]
    calc
      |∑ n ∈ interval N,
          (max (divergence N n) 0 -
            weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ)))| ≤
          ∑ n ∈ interval N,
            |max (divergence N n) 0 -
              weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ interval N, if n < J then weight n else L n := by
        apply Finset.sum_le_sum
        intro n hn
        split_ifs with hnj
        · have hnpos : 0 < n := by
            have := (Finset.mem_Icc.mp hn).1
            omega
          have hmd0 := max_divergence_nonneg N n
          have hmdw := max_divergence_le_weight (N := N) hnpos
          have hw : 0 ≤ weight n := by unfold weight; positivity
          have ht0 : 0 ≤ weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ)) :=
            mul_nonneg hw (frontierDensity_nonneg _)
          have htw : weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ)) ≤
              weight n := by
            simpa using mul_le_mul_of_nonneg_left
              (frontierDensity_le_one (logCoord (N : ℝ) (n : ℝ))) hw
          rw [abs_le]
          constructor <;> linarith
        · exact positive_pointwise_comparison hN hn (le_of_not_gt hnj) hJ hlogJ
            hXJ hη hη1 hJinv hρ hlarge hlogN hmargin hM
      _ ≤ (∑ n ∈ interval N, if n < J then weight n else 0) +
          ∑ n ∈ interval N, L n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro n hn
        by_cases hnj : n < J
        · simp only [hnj, if_true]
          exact le_add_of_nonneg_right (by
            dsimp [L]
            exact mul_nonneg (by unfold weight; positivity)
              (add_nonneg (by positivity)
                (mul_nonneg (by norm_num) (junctionBump_nonneg _ _))))
        · simp [hnj]
      _ ≤ (J : ℝ) + ∑ n ∈ interval N, L n := by
        exact add_le_add (small_weight_sum_le N J) le_rfl
      _ = (J : ℝ) + 16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N := by
        have hLsum : (∑ n ∈ interval N, L n) =
            16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N := by
          simp only [L, harmonicIntervalMass, bumpMass]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1 <;> rw [Finset.mul_sum] <;>
            apply Finset.sum_congr rfl <;> intro n hn <;> ring
        rw [hLsum]
        ring
  have hdiv := div_le_div_of_nonneg_right hnum hlogpos.le
  rw [← modelMass_div_log, ← sub_div, abs_div, abs_of_pos hlogpos]
  calc
    |positiveDivergenceMass N - modelMass N| / Real.log (N : ℝ) ≤
        ((J : ℝ) + 16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N) /
          Real.log (N : ℝ) := hdiv
    _ = (J : ℝ) / Real.log (N : ℝ) +
        16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
        22 * logHarmonicRiemannSum (junctionBump ρ) N := by
      rw [← harmonicIntervalMass_div_log, ← bumpMass_div_log]
      ring

noncomputable def powerThreshold (N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ alphaTwo⌋₊

lemma powerThreshold_lt_iff {N n : ℕ} :
    powerThreshold N < n ↔ (N : ℝ) ^ alphaTwo < (n : ℝ) := by
  rw [powerThreshold, Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) alphaTwo)]

lemma alphaTwo_lt_logCoord_of_powerThreshold_lt {N n : ℕ} (hN : 1 < N)
    (hn : powerThreshold N < n) :
    alphaTwo < logCoord (N : ℝ) (n : ℝ) := by
  have hp := powerThreshold_lt_iff.mp hn
  have hNpos : (0 : ℝ) < N := by positivity
  have hnpos : (0 : ℝ) < n := (Real.rpow_pos_of_pos hNpos alphaTwo).trans hp
  have hlog := Real.strictMonoOn_log
    (show (N : ℝ) ^ alphaTwo ∈ Set.Ioi 0 by exact Real.rpow_pos_of_pos hNpos _)
    (show (n : ℝ) ∈ Set.Ioi 0 by exact hnpos) hp
  rw [Real.log_rpow hNpos] at hlog
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [logCoord]
  exact (lt_div_iff₀ hlogN).2 (by simpa [mul_comm] using hlog)

lemma logCoord_le_alphaTwo_of_le_powerThreshold {N n : ℕ} (hN : 1 < N)
    (hnpos : 0 < n) (hn : n ≤ powerThreshold N) :
    logCoord (N : ℝ) (n : ℝ) ≤ alphaTwo := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hfloor : ((powerThreshold N : ℕ) : ℝ) ≤ (N : ℝ) ^ alphaTwo := by
    exact Nat.floor_le (Real.rpow_nonneg hNpos.le alphaTwo)
  have hncast : (n : ℝ) ≤ (powerThreshold N : ℕ) := by exact_mod_cast hn
  have hnrpow : (n : ℝ) ≤ (N : ℝ) ^ alphaTwo := hncast.trans hfloor
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show 0 < (n : ℝ) by exact_mod_cast hnpos)
    (show (N : ℝ) ^ alphaTwo ∈ Set.Ioi 0 by exact Real.rpow_pos_of_pos hNpos _)
    hnrpow
  rw [Real.log_rpow hNpos] at hlog
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [logCoord]
  exact (div_le_iff₀ hlogN).2 (by simpa [mul_comm] using hlog)

lemma modelMass_eq_threshold_modelMass {N : ℕ} (hN : 1 < N) :
    modelMass N = ∑ n ∈ thresholdSet N (powerThreshold N),
      weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ)) := by
  rw [modelMass, thresholdSet]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hkn
  · rfl
  · have hnpos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [frontierDensity_eq_zero
      (logCoord_le_alphaTwo_of_le_powerThreshold hN hnpos (le_of_not_gt hkn)), mul_zero]

lemma threshold_normalized_error_bound {N J : ℕ} {X η ρ : ℝ}
    (hN : 1 < N) (hJK : J ≤ powerThreshold N)
    (hJ : 1 < J) (hlogJ : 1 ≤ Real.log (J : ℝ))
    (hXJ : X ≤ (J : ℝ)) (hη : 0 < η) (hη1 : η ≤ 1)
    (hJinv : (J : ℝ)⁻¹ ≤ η) (hρ : 0 < ρ)
    (hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ))
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hM : ∀ x : ℝ, X ≤ x → |primeReciprocalError x| < η) :
    |thresholdDivergenceMass N (powerThreshold N) / Real.log (N : ℝ) -
        logHarmonicRiemannSum frontierDensity N| ≤
      16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
        22 * logHarmonicRiemannSum (junctionBump ρ) N := by
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  let L : ℕ → ℝ := fun n ↦
    weight n * (16 * η + 22 * junctionBump ρ (logCoord (N : ℝ) (n : ℝ)))
  have hL0 (n : ℕ) : 0 ≤ L n := by
    dsimp [L]
    exact mul_nonneg (by unfold weight; positivity)
      (add_nonneg (by positivity)
        (mul_nonneg (by norm_num) (junctionBump_nonneg _ _)))
  have hnum : |thresholdDivergenceMass N (powerThreshold N) - modelMass N| ≤
      16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N := by
    rw [thresholdDivergenceMass, modelMass_eq_threshold_modelMass hN,
      ← Finset.sum_sub_distrib]
    calc
      |∑ n ∈ thresholdSet N (powerThreshold N),
          (divergence N n -
            weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ)))| ≤
          ∑ n ∈ thresholdSet N (powerThreshold N),
            |divergence N n -
              weight n * frontierDensity (logCoord (N : ℝ) (n : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ thresholdSet N (powerThreshold N), L n := by
        apply Finset.sum_le_sum
        intro n hn
        have hd := Finset.mem_filter.mp hn
        exact raw_pointwise_comparison hN hd.1 (hJK.trans hd.2.le) hJ hlogJ
          hXJ hη hη1 hJinv hρ hlarge hlogN
          (alphaTwo_lt_logCoord_of_powerThreshold_lt hN hd.2) hM
      _ ≤ ∑ n ∈ interval N, L n := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn ↦ (Finset.mem_filter.mp hn).1)
          (fun n hn hnot ↦ hL0 n)
      _ = 16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N := by
        simp only [L, harmonicIntervalMass, bumpMass]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1 <;> rw [Finset.mul_sum] <;>
          apply Finset.sum_congr rfl <;> intro n hn <;> ring
  have hdiv := div_le_div_of_nonneg_right hnum hlogpos.le
  rw [← modelMass_div_log, ← sub_div, abs_div, abs_of_pos hlogpos]
  calc
    |thresholdDivergenceMass N (powerThreshold N) - modelMass N| /
        Real.log (N : ℝ) ≤
      (16 * η * harmonicIntervalMass N + 22 * bumpMass ρ N) /
        Real.log (N : ℝ) := hdiv
    _ = 16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
        22 * logHarmonicRiemannSum (junctionBump ρ) N := by
      rw [← harmonicIntervalMass_div_log, ← bumpMass_div_log]
      ring

theorem positiveDivergenceMass_tendsto :
    Tendsto (fun N : ℕ ↦ positiveDivergenceMass N / Real.log (N : ℝ))
      atTop (nhds constant) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm : 0 < Real.log ((1 - beta) / beta) - 1 :=
    sub_pos.mpr one_lt_base_beta
  let η : ℝ := min ((1 : ℝ) / 2) (min ((Real.log ((1 - beta) / beta) - 1) / 4)
    (ε / 10000))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hηm : η ≤ (Real.log ((1 - beta) / beta) - 1) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / 10000 := (min_le_right _ _).trans (min_le_right _ _)
  have hmargin : 2 * η < Real.log ((1 - beta) / beta) - 1 := by
    linarith
  let ρ : ℝ := min ((1 : ℝ) / 12) (ε / 10000)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsmall : ρ ≤ (1 : ℝ) / 12 := min_le_left _ _
  have hρε : ρ ≤ ε / 10000 := min_le_right _ _
  obtain ⟨X, hM⟩ := primeReciprocalError_uniform η hη
  let R : ℝ := max X (max (Real.exp 1) η⁻¹)
  obtain ⟨J, hJR⟩ := exists_nat_gt R
  have hXJ : X ≤ (J : ℝ) := (le_max_left _ _).trans hJR.le
  have hexpJ : Real.exp 1 < (J : ℝ) :=
    (le_max_left (Real.exp 1) η⁻¹).trans_lt
      ((le_max_right X _).trans_lt hJR)
  have hJ : 1 < J := by
    have h2J : 2 < J := by exact_mod_cast Real.exp_one_gt_two.trans hexpJ
    omega
  have hlogJ : 1 ≤ Real.log (J : ℝ) := by
    have hl := Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.exp 1 by positivity)
      (show 0 < (J : ℝ) by positivity) hexpJ.le
    rw [Real.log_exp] at hl
    simpa using hl
  have hηinvJ : η⁻¹ < (J : ℝ) :=
    (le_max_right (Real.exp 1) η⁻¹).trans_lt
      ((le_max_right X _).trans_lt hJR)
  have hJinv : (J : ℝ)⁻¹ ≤ η := by
    have hi : (J : ℝ)⁻¹ < (η⁻¹)⁻¹ :=
      (inv_lt_inv₀ (by positivity : (0 : ℝ) < J) (inv_pos.mpr hη)).2 hηinvJ
    simpa using hi.le
  have hmodelT : Tendsto (logHarmonicRiemannSum frontierDensity) atTop
      (nhds constant) := by
    simpa [frontierDensity_integral_eq_constant] using
      (harmonic_log_riemann continuous_frontierDensity)
  obtain ⟨Nm, hNm⟩ := (Metric.tendsto_atTop.mp hmodelT) (ε / 4) (by positivity)
  have hHT : Tendsto (logHarmonicRiemannSum (fun _ : ℝ ↦ 1)) atTop (nhds 1) := by
    convert harmonic_log_riemann (f := fun _ : ℝ ↦ 1) continuous_const using 1
    norm_num
  obtain ⟨Nh, hNh⟩ := (Metric.tendsto_atTop.mp hHT) 1 (by norm_num)
  let Iρ : ℝ := ∫ u in (0 : ℝ)..1, junctionBump ρ u
  have hBT : Tendsto (logHarmonicRiemannSum (junctionBump ρ)) atTop (nhds Iρ) := by
    exact harmonic_log_riemann (continuous_junctionBump ρ)
  obtain ⟨Nb, hNb⟩ := (Metric.tendsto_atTop.mp hBT) ρ hρ
  have hIρ : Iρ ≤ 4 * ρ := junctionBump_integral_le hρ hρsmall
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let Rlog : ℝ := max 1
    (max (Real.log 4 / (3 * ρ)) (4 * (J : ℝ) / ε + 1))
  obtain ⟨Nl, hNl⟩ := (tendsto_atTop_atTop.mp hlogTop) Rlog
  refine ⟨max Nm (max Nh (max Nb Nl)), fun N hN0 ↦ ?_⟩
  have hNmN : Nm ≤ N := (le_max_left Nm _).trans hN0
  have hNhN : Nh ≤ N := (le_max_left Nh _).trans
    ((le_max_right Nm _).trans hN0)
  have hNbN : Nb ≤ N := (le_max_left Nb Nl).trans
    ((le_max_right Nh _).trans ((le_max_right Nm _).trans hN0))
  have hNlN : Nl ≤ N := (le_max_right Nb Nl).trans
    ((le_max_right Nh _).trans ((le_max_right Nm _).trans hN0))
  have hlogR : Rlog ≤ Real.log (N : ℝ) := hNl N hNlN
  have hlog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left 1 _).trans hlogR
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog1
  have hN : 1 < N := by
    exact_mod_cast (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp hlogpos
  have hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ) := by
    have hq : Real.log 4 / (3 * ρ) ≤ Real.log (N : ℝ) :=
      (le_max_left _ _).trans ((le_max_right 1 _).trans hlogR)
    have := (div_le_iff₀ (by positivity : 0 < 3 * ρ)).mp hq
    nlinarith
  have hJfrac : (J : ℝ) / Real.log (N : ℝ) < ε / 4 := by
    have hq : 4 * (J : ℝ) / ε + 1 ≤ Real.log (N : ℝ) :=
      (le_max_right _ _).trans ((le_max_right 1 _).trans hlogR)
    have hq' : 4 * (J : ℝ) / ε < Real.log (N : ℝ) := by linarith
    have hmult := (div_lt_iff₀ hε).mp hq'
    apply (div_lt_iff₀ hlogpos).2
    nlinarith
  have hH : logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N < 2 := by
    have hh := hNh N hNhN
    rw [Real.dist_eq] at hh
    linarith [le_abs_self (logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N - 1)]
  have hB : logHarmonicRiemannSum (junctionBump ρ) N < 5 * ρ := by
    have hb := hNb N hNbN
    rw [Real.dist_eq] at hb
    linarith [le_abs_self (logHarmonicRiemannSum (junctionBump ρ) N - Iρ)]
  have hE : (J : ℝ) / Real.log (N : ℝ) +
      16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
      22 * logHarmonicRiemannSum (junctionBump ρ) N < ε / 2 := by
    have hhprod : 16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N <
        32 * η := by
      nlinarith [mul_pos (show 0 < 16 * η by positivity) (sub_pos.mpr hH)]
    have hbprod : 22 * logHarmonicRiemannSum (junctionBump ρ) N < 110 * ρ := by
      linarith
    linarith
  have hdisc := positive_normalized_error_bound hN hJ hlogJ hXJ hη hη1
    hJinv hρ hlarge hlog1 hmargin hM
  have hmclose := hNm N hNmN
  rw [Real.dist_eq] at hmclose ⊢
  calc
    |positiveDivergenceMass N / Real.log (N : ℝ) - constant| ≤
        |positiveDivergenceMass N / Real.log (N : ℝ) -
          logHarmonicRiemannSum frontierDensity N| +
        |logHarmonicRiemannSum frontierDensity N - constant| := abs_sub_le _ _ _
    _ < ε := by linarith


theorem thresholdDivergenceMass_tendsto :
    Tendsto (fun N : ℕ ↦
      thresholdDivergenceMass N (powerThreshold N) / Real.log (N : ℝ))
      atTop (nhds constant) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hm : 0 < Real.log ((1 - beta) / beta) - 1 :=
    sub_pos.mpr one_lt_base_beta
  let η : ℝ := min ((1 : ℝ) / 2) (min ((Real.log ((1 - beta) / beta) - 1) / 4)
    (ε / 10000))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hηm : η ≤ (Real.log ((1 - beta) / beta) - 1) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / 10000 := (min_le_right _ _).trans (min_le_right _ _)
  have hmargin : 2 * η < Real.log ((1 - beta) / beta) - 1 := by
    linarith
  let ρ : ℝ := min ((1 : ℝ) / 12) (ε / 10000)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsmall : ρ ≤ (1 : ℝ) / 12 := min_le_left _ _
  have hρε : ρ ≤ ε / 10000 := min_le_right _ _
  obtain ⟨X, hM⟩ := primeReciprocalError_uniform η hη
  let R : ℝ := max X (max (Real.exp 1) η⁻¹)
  obtain ⟨J, hJR⟩ := exists_nat_gt R
  have hXJ : X ≤ (J : ℝ) := (le_max_left _ _).trans hJR.le
  have hexpJ : Real.exp 1 < (J : ℝ) :=
    (le_max_left (Real.exp 1) η⁻¹).trans_lt
      ((le_max_right X _).trans_lt hJR)
  have hJ : 1 < J := by
    have h2J : 2 < J := by exact_mod_cast Real.exp_one_gt_two.trans hexpJ
    omega
  have hlogJ : 1 ≤ Real.log (J : ℝ) := by
    have hl := Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.exp 1 by positivity)
      (show 0 < (J : ℝ) by positivity) hexpJ.le
    rw [Real.log_exp] at hl
    simpa using hl
  have hηinvJ : η⁻¹ < (J : ℝ) :=
    (le_max_right (Real.exp 1) η⁻¹).trans_lt
      ((le_max_right X _).trans_lt hJR)
  have hJinv : (J : ℝ)⁻¹ ≤ η := by
    have hi : (J : ℝ)⁻¹ < (η⁻¹)⁻¹ :=
      (inv_lt_inv₀ (by positivity : (0 : ℝ) < J) (inv_pos.mpr hη)).2 hηinvJ
    simpa using hi.le
  have hmodelT : Tendsto (logHarmonicRiemannSum frontierDensity) atTop
      (nhds constant) := by
    simpa [frontierDensity_integral_eq_constant] using
      (harmonic_log_riemann continuous_frontierDensity)
  obtain ⟨Nm, hNm⟩ := (Metric.tendsto_atTop.mp hmodelT) (ε / 4) (by positivity)
  have hHT : Tendsto (logHarmonicRiemannSum (fun _ : ℝ ↦ 1)) atTop (nhds 1) := by
    convert harmonic_log_riemann (f := fun _ : ℝ ↦ 1) continuous_const using 1
    norm_num
  obtain ⟨Nh, hNh⟩ := (Metric.tendsto_atTop.mp hHT) 1 (by norm_num)
  let Iρ : ℝ := ∫ u in (0 : ℝ)..1, junctionBump ρ u
  have hBT : Tendsto (logHarmonicRiemannSum (junctionBump ρ)) atTop (nhds Iρ) := by
    exact harmonic_log_riemann (continuous_junctionBump ρ)
  obtain ⟨Nb, hNb⟩ := (Metric.tendsto_atTop.mp hBT) ρ hρ
  have hIρ : Iρ ≤ 4 * ρ := junctionBump_integral_le hρ hρsmall
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let Rlog : ℝ := max 1
    (max (Real.log 4 / (3 * ρ)) (4 * (J : ℝ) / ε + 1))
  obtain ⟨Nl, hNl⟩ := (tendsto_atTop_atTop.mp hlogTop) Rlog
  have hpowerT : Tendsto powerThreshold atTop atTop := by
    unfold powerThreshold
    exact tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by linarith [alphaTwo_gt_quarter])).comp
        tendsto_natCast_atTop_atTop)
  obtain ⟨Np, hNp⟩ := (tendsto_atTop_atTop.mp hpowerT) J
  let Nbase := max Nm (max Nh (max Nb Nl))
  refine ⟨max Nbase Np, fun N hN0 ↦ ?_⟩
  have hbase : Nbase ≤ N := (le_max_left Nbase Np).trans hN0
  have hNpN : Np ≤ N := (le_max_right Nbase Np).trans hN0
  have hNmN : Nm ≤ N := (le_max_left Nm _).trans hbase
  have hNhN : Nh ≤ N := (le_max_left Nh _).trans
    ((le_max_right Nm _).trans hbase)
  have hNbN : Nb ≤ N := (le_max_left Nb Nl).trans
    ((le_max_right Nh _).trans ((le_max_right Nm _).trans hbase))
  have hNlN : Nl ≤ N := (le_max_right Nb Nl).trans
    ((le_max_right Nh _).trans ((le_max_right Nm _).trans hbase))
  have hlogR : Rlog ≤ Real.log (N : ℝ) := hNl N hNlN
  have hlog1 : 1 ≤ Real.log (N : ℝ) := (le_max_left 1 _).trans hlogR
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog1
  have hN : 1 < N := by
    exact_mod_cast (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ N)).mp hlogpos
  have hlarge : Real.log 4 ≤ 3 * ρ * Real.log (N : ℝ) := by
    have hq : Real.log 4 / (3 * ρ) ≤ Real.log (N : ℝ) :=
      (le_max_left _ _).trans ((le_max_right 1 _).trans hlogR)
    have := (div_le_iff₀ (by positivity : 0 < 3 * ρ)).mp hq
    nlinarith
  have hJfrac : (J : ℝ) / Real.log (N : ℝ) < ε / 4 := by
    have hq : 4 * (J : ℝ) / ε + 1 ≤ Real.log (N : ℝ) :=
      (le_max_right _ _).trans ((le_max_right 1 _).trans hlogR)
    have hq' : 4 * (J : ℝ) / ε < Real.log (N : ℝ) := by linarith
    have hmult := (div_lt_iff₀ hε).mp hq'
    apply (div_lt_iff₀ hlogpos).2
    nlinarith
  have hJfrac0 : 0 ≤ (J : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg J) hlogpos.le
  have hH : logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N < 2 := by
    have hh := hNh N hNhN
    rw [Real.dist_eq] at hh
    linarith [le_abs_self (logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N - 1)]
  have hB : logHarmonicRiemannSum (junctionBump ρ) N < 5 * ρ := by
    have hb := hNb N hNbN
    rw [Real.dist_eq] at hb
    linarith [le_abs_self (logHarmonicRiemannSum (junctionBump ρ) N - Iρ)]
  have hE : (J : ℝ) / Real.log (N : ℝ) +
      16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N +
      22 * logHarmonicRiemannSum (junctionBump ρ) N < ε / 2 := by
    have hhprod : 16 * η * logHarmonicRiemannSum (fun _ : ℝ ↦ 1) N <
        32 * η := by
      nlinarith [mul_pos (show 0 < 16 * η by positivity) (sub_pos.mpr hH)]
    have hbprod : 22 * logHarmonicRiemannSum (junctionBump ρ) N < 110 * ρ := by
      linarith
    linarith
  have hdisc := threshold_normalized_error_bound hN (hNp N hNpN) hJ hlogJ
    hXJ hη hη1 hJinv hρ hlarge hlog1 hM
  have hmclose := hNm N hNmN
  rw [Real.dist_eq] at hmclose ⊢
  calc
    |thresholdDivergenceMass N (powerThreshold N) / Real.log (N : ℝ) - constant| ≤
        |thresholdDivergenceMass N (powerThreshold N) / Real.log (N : ℝ) -
          logHarmonicRiemannSum frontierDensity N| +
        |logHarmonicRiemannSum frontierDensity N - constant| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- Resolution of Erdős Problem 858: the exact finite maximum of the reciprocal
mass, divided by `log N`, converges to the explicit constant `constant`. -/
theorem erdos_858 :
    Tendsto (fun N : ℕ ↦ extremalMass N / Real.log (N : ℝ))
      atTop (nhds constant) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    thresholdDivergenceMass_tendsto positiveDivergenceMass_tendsto ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact (div_le_div_iff_of_pos_right hlog).2
      (thresholdDivergenceMass_le_extremalMass N (powerThreshold N))
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact (div_le_div_iff_of_pos_right hlog).2
      (extremalMass_le_positiveDivergenceMass N)

end Erdos858
