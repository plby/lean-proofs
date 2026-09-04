/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos847.LineCounting
import ErdosProblems.Erdos847.BlockCandidates
import ErdosProblems.Erdos847.LineExclusions
import ErdosProblems.Erdos847.SparseSelection

/-!
# Sparse Hales--Jewett line systems for Erdős Problem 847

This scratch module isolates the finite line-system input in the
Reiher--Rödl--Sales construction.  It provides:

* precise finitary definitions of the Ramsey, tripod, and triangle properties;
* rigidity of combinatorial lines (two distinct common points determine a line);
* the ordinary Hales--Jewett theorem packaged as a finite Ramsey line family;
* support-size strata for the later sparse-selection counting argument.

The final sparse-selection argument is stated only after all its constituent
predicates have been made explicit.  Every declaration in this file is proved;
there are no proof placeholders.
-/

namespace Erdos847SparseLines

open Function Set
open Combinatorics

attribute [local instance] Classical.propDecidable

universe u v w

variable {A : Type u} {I : Type v} {K : Type w}

/-- The set of cube vertices lying on a combinatorial line. -/
def linePoints (l : Line A I) : Set (I → A) := Set.range l

@[simp]
lemma mem_linePoints (l : Line A I) (x : I → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Evaluation on a combinatorial line is injective as soon as the alphabet is nontrivial. -/
lemma line_apply_injective [Nontrivial A] (l : Line A I) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have h := congrFun hab i
  simpa [Line.coe_apply, hi] using h

/-- Two parameter values determine the line as a function. -/
lemma line_eq_of_apply_eq_apply [Nontrivial A] {l m : Line A I} {a b : A}
    (hab : a ≠ b) (ha : l a = m a) (hb : l b = m b) : l = m := by
  ext i
  have hai := congrFun ha i
  have hbi := congrFun hb i
  cases hl : l.idxFun i <;> cases hm : m.idxFun i <;>
    simp_all [Line.coe_apply]

/-- Two distinct common cube vertices determine a combinatorial line uniquely. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {l m : Line A I} {x y : I → A}
    (hxy : x ≠ y) (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  have hab : a ≠ b := by
    intro hab
    apply hxy
    simpa [hab] using hby
  obtain ⟨i, hi⟩ := l.proper
  have hc : c = a := by
    have h := congrFun hca i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun (hdy.trans hby.symm) i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h.symm.trans h')).elim
  have hd : d = b := by
    have h := congrFun (hdy.trans hby.symm) i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun hca i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h'.symm.trans h)).elim
  apply line_eq_of_apply_eq_apply hab
  · simpa [hc] using hca.symm
  · simpa [hd] using (hdy.trans hby.symm).symm

/-- Distinct combinatorial lines meet in at most one cube vertex. -/
lemma common_point_unique [Nontrivial A] {l m : Line A I} (hlm : l ≠ m)
    {x y : I → A} (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : x = y := by
  by_contra hxy
  exact hlm (line_eq_of_two_mem_points hxy hxl hxm hyl hym)

/-- Injectivity of the data field of a combinatorial line. -/
lemma line_idxFun_injective :
    Function.Injective (Line.idxFun : Line A I → I → Option A) := by
  intro l m h
  cases l with
  | mk lf lp =>
      cases m with
      | mk mf mp =>
          simp only at h
          subst mf
          rfl

/-- The moving-coordinate support of a line. -/
def movingSet [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

@[simp]
lemma mem_movingSet [Fintype I] (l : Line A I) (i : I) :
    i ∈ movingSet l ↔ l.idxFun i = none := by
  simp [movingSet]

lemma movingSet_nonempty [Fintype I] (l : Line A I) : (movingSet l).Nonempty := by
  obtain ⟨i, hi⟩ := l.proper
  exact ⟨i, (mem_movingSet l i).2 hi⟩

lemma movingSet_card_pos [Fintype I] (l : Line A I) : 0 < (movingSet l).card :=
  Finset.card_pos.mpr (movingSet_nonempty l)

/-- A line through a fixed vertex is determined already by its moving support. -/
lemma line_eq_of_movingSet_eq_of_mem [Fintype I] {l m : Line A I}
    (hmove : movingSet l = movingSet m) {x : I → A}
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, ha⟩
  rcases hxm with ⟨b, hb⟩
  apply line_idxFun_injective
  funext i
  by_cases hi : i ∈ movingSet l
  · have hil : l.idxFun i = none := (mem_movingSet l i).mp hi
    have him : m.idxFun i = none := (mem_movingSet m i).mp (hmove ▸ hi)
    simp [hil, him]
  · have hil : l.idxFun i ≠ none := fun h ↦ hi ((mem_movingSet l i).mpr h)
    have him : m.idxFun i ≠ none := by
      intro h
      exact hi (hmove.symm ▸ (mem_movingSet m i).mpr h)
    cases hl : l.idxFun i with
    | none => exact (hil hl).elim
    | some c =>
        cases hm : m.idxFun i with
        | none => exact (him hm).elim
        | some d =>
            have h := congrFun (ha.trans hb.symm) i
            simp only [Line.coe_apply, hl, hm, Option.getD_some] at h
            exact congrArg some h

/-- The vertices of a line, as a finset for incidence counting. -/
noncomputable def linePointFinset [Fintype A] (l : Line A I) : Finset (I → A) :=
  Finset.univ.image l

@[simp]
lemma mem_linePointFinset [Fintype A] {l : Line A I} {x : I → A} :
    x ∈ linePointFinset l ↔ x ∈ linePoints l := by
  simp [linePointFinset, linePoints]

lemma card_linePointFinset [Fintype A] [Nontrivial A] (l : Line A I) :
    (linePointFinset l).card = Fintype.card A := by
  rw [linePointFinset, Finset.card_image_of_injective _ (line_apply_injective l)]
  exact Finset.card_univ

/-- A concrete `Fintype` structure on combinatorial lines. -/
noncomputable def lineFintype [Fintype A] [Fintype I] : Fintype (Line A I) :=
  Fintype.ofInjective Line.idxFun line_idxFun_injective

/-- The full finite line family in a finite cube. -/
noncomputable def allLines [Fintype A] [Fintype I] : Finset (Line A I) := by
  letI := lineFintype (A := A) (I := I)
  exact Finset.univ

@[simp]
lemma mem_allLines [Fintype A] [Fintype I] (l : Line A I) : l ∈ allLines := by
  classical
  let := lineFintype (A := A) (I := I)
  simp [allLines]

/-- A line in `S` is monochromatic for every coloring of its cube vertices. -/
def IsRamseyFamily (S : Finset (Line A I)) (K : Type w) : Prop :=
  ∀ color : (I → A) → K, ∃ l ∈ S, l.IsMono color

/-- Lines of `S` incident with a fixed cube vertex. -/
noncomputable def incidentLines (S : Finset (Line A I)) (x : I → A) : Finset (Line A I) :=
  S.filter fun l ↦ x ∈ linePoints l

@[simp]
lemma mem_incidentLines {S : Finset (Line A I)} {x : I → A} {l : Line A I} :
    l ∈ incidentLines S x ↔ l ∈ S ∧ x ∈ linePoints l := by
  simp [incidentLines]

/-- The degree of a cube vertex in a selected line family. -/
noncomputable def lineDegree (S : Finset (Line A I)) (x : I → A) : ℕ :=
  (incidentLines S x).card

/-- Double-counting incidences: every selected line contains exactly `|A|` vertices. -/
lemma sum_lineDegree [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) :
    ∑ x : I → A, lineDegree S x = Fintype.card A * S.card := by
  classical
  let r : Line A I → (I → A) → Prop := fun l x ↦ x ∈ linePoints l
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (Finset.univ : Finset (I → A))) r
  have habove : ∀ l : Line A I,
      Finset.bipartiteAbove r Finset.univ l = linePointFinset l := by
    intro l
    ext x
    simp [r]
  have hbelow : ∀ x : I → A,
      Finset.bipartiteBelow r S x = incidentLines S x := by
    intro x
    ext l
    simp [r]
  simpa only [habove, hbelow, lineDegree, card_linePointFinset, Finset.sum_const_nat,
    Finset.card_univ, Nat.nsmul_eq_mul, Nat.mul_comm] using hdouble.symm

/-- Vertices whose selected-line degree has reached the cap `d`. -/
noncomputable def saturatedPoints [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (d : ℕ) : Finset (I → A) :=
  Finset.univ.filter fun x ↦ d ≤ lineDegree S x

@[simp]
lemma mem_saturatedPoints [Fintype A] [Fintype I]
    {S : Finset (Line A I)} {d : ℕ} {x : I → A} :
    x ∈ saturatedPoints S d ↔ d ≤ lineDegree S x := by
  simp [saturatedPoints]

/-- First RRS exclusion estimate in abstract incidence form: the number of saturated vertices,
times the degree cap, is at most the total number of line--vertex incidences. -/
lemma card_saturatedPoints_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) (d : ℕ) :
    (saturatedPoints S d).card * d ≤ Fintype.card A * S.card := by
  classical
  calc
    (saturatedPoints S d).card * d ≤
        ∑ x ∈ saturatedPoints S d, lineDegree S x := by
      simpa [Nat.nsmul_eq_mul] using
        Finset.card_nsmul_le_sum (saturatedPoints S d) (lineDegree S) d
          (fun x hx ↦ mem_saturatedPoints.mp hx)
    _ ≤ ∑ x : I → A, lineDegree S x := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card A * S.card := sum_lineDegree S

/-- Lines from `T` that meet at least one vertex of `P`. -/
noncomputable def linesMeetingPoints (T : Finset (Line A I)) (P : Finset (I → A)) :
    Finset (Line A I) :=
  P.biUnion (incidentLines T)

@[simp]
lemma mem_linesMeetingPoints {T : Finset (Line A I)} {P : Finset (I → A)}
    {l : Line A I} :
    l ∈ linesMeetingPoints T P ↔
      ∃ x ∈ P, l ∈ T ∧ x ∈ linePoints l := by
  simp [linesMeetingPoints]

/-- Union bound for lines excluded because they meet a forbidden set of vertices. -/
lemma card_linesMeetingPoints_le_sum_degree (T : Finset (Line A I)) (P : Finset (I → A)) :
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x := by
  classical
  simpa [linesMeetingPoints, lineDegree] using
    (Finset.card_biUnion_le (s := P) (t := incidentLines T))

/-- If every forbidden vertex belongs to at most `M` candidate lines, at most `|P| M`
candidates are excluded by the degree condition. -/
lemma card_linesMeetingPoints_le (T : Finset (Line A I)) (P : Finset (I → A)) (M : ℕ)
    (hM : ∀ x ∈ P, lineDegree T x ≤ M) :
    (linesMeetingPoints T P).card ≤ P.card * M := by
  calc
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x :=
      card_linesMeetingPoints_le_sum_degree T P
    _ ≤ P.card * M := by
      simpa [Nat.nsmul_eq_mul] using Finset.sum_le_card_nsmul P (lineDegree T) M hM

/-- The exact RRS tripod pattern: three pairwise distinct selected lines pass through one
cube vertex and, after the existential relabeling displayed here, the moving support of the first
line is the disjoint union of the moving supports of the other two. -/
def HasTripod [Fintype I] (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (∃ x, x ∈ linePoints l₁ ∧ x ∈ linePoints l₂ ∧ x ∈ linePoints l₃) ∧
      movingSet l₁ = movingSet l₂ ∪ movingSet l₃ ∧
      Disjoint (movingSet l₂) (movingSet l₃)

/-- Three pairwise distinct selected lines meet pairwise, but have no common point. -/
def HasTriangle (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (linePoints l₁ ∩ linePoints l₂).Nonempty ∧
      (linePoints l₂ ∩ linePoints l₃).Nonempty ∧
      (linePoints l₃ ∩ linePoints l₁).Nonempty ∧
      linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ = ∅

/-- The two forbidden intersection patterns required by the RRS partite construction. -/
def IsSparse [Fintype I] (S : Finset (Line A I)) : Prop :=
  ¬ HasTripod S ∧ ¬ HasTriangle S

lemma IsSparse.subset [Fintype I] {S T : Finset (Line A I)} (hS : IsSparse S) (hTS : T ⊆ S) :
    IsSparse T := by
  constructor
  · intro hT
    apply hS.1
    rcases hT with ⟨l₁, h₁, l₂, h₂, l₃, h₃, hrest⟩
    exact ⟨l₁, hTS h₁, l₂, hTS h₂, l₃, hTS h₃, hrest⟩
  · intro hT
    apply hS.2
    rcases hT with ⟨l₁, h₁, l₂, h₂, l₃, h₃, hrest⟩
    exact ⟨l₁, hTS h₁, l₂, hTS h₂, l₃, hTS h₃, hrest⟩

lemma isSparse_empty [Fintype I] : IsSparse (∅ : Finset (Line A I)) := by
  constructor <;> simp [HasTripod, HasTriangle]

/-- A support-size stratum of an explicitly finite family of lines. -/
def supportStratum [Fintype I] (S : Finset (Line A I)) (s : ℕ) : Finset (Line A I) :=
  S.filter fun l ↦ (movingSet l).card = s

@[simp]
lemma mem_supportStratum [Fintype I] {S : Finset (Line A I)} {s : ℕ} {l : Line A I} :
    l ∈ supportStratum S s ↔ l ∈ S ∧ (movingSet l).card = s := by
  simp [supportStratum]

lemma supportStratum_zero [Fintype I] (S : Finset (Line A I)) :
    supportStratum S 0 = ∅ := by
  ext l
  simp only [mem_supportStratum, Finset.notMem_empty, iff_false, not_and]
  intro _ hl
  exact (movingSet_card_pos l).ne' hl

/-- At a fixed vertex there are at most `choose |I| s` lines with moving support of size `s`.
This is the incidence bound used in the saturated-point estimate (RRS equation (5.5)). -/
lemma lineDegree_supportStratum_le_choose [Fintype I]
    (S : Finset (Line A I)) (s : ℕ) (x : I → A) :
    lineDegree (supportStratum S s) x ≤ Nat.choose (Fintype.card I) s := by
  classical
  let source := incidentLines (supportStratum S s) x
  let target := Finset.powersetCard s (Finset.univ : Finset I)
  have hmap : Set.MapsTo movingSet (source : Set (Line A I)) (target : Set (Finset I)) := by
    intro l hl
    have hinc := mem_incidentLines.mp hl
    have hstratum := mem_supportStratum.mp hinc.1
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hstratum.2⟩
  have hinj : (source : Set (Line A I)).InjOn movingSet := by
    intro l hl m hm heq
    exact line_eq_of_movingSet_eq_of_mem heq
      (mem_incidentLines.mp hl).2 (mem_incidentLines.mp hm).2
  have hcard := Finset.card_le_card_of_injOn movingSet hmap hinj
  simpa [source, target, lineDegree] using hcard

/-- The ordinary Hales--Jewett theorem, packaged as a finite Ramsey family.

The family here is the full finite family of lines.  The sparse-selection
argument starts from support-size strata of this family and deletes lines.
-/
theorem exists_finite_ramsey_family (A : Type u) [Finite A] [Nontrivial A]
    (K : Type w) [Finite K] :
    ∃ (I : Type) (_ : Fintype I) (S : Finset (Line A I)), IsRamseyFamily S K := by
  rcases Line.exists_mono_in_high_dimension A K with ⟨I, hI, hHJ⟩
  let : Fintype I := hI
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (Line A I) :=
    Fintype.ofInjective Line.idxFun (by
      intro l m h
      cases l with
      | mk lf lp =>
          cases m with
          | mk mf mp =>
              simp only at h
              subst mf
              rfl)
  refine ⟨I, inferInstance, Finset.univ, ?_⟩
  intro color
  rcases hHJ color with ⟨l, hl⟩
  exact ⟨l, Finset.mem_univ l, hl⟩

/-! ## Generic one-stratum greedy selection -/

open Erdos847SparseSelection in
/-- One-stratum specialization of the finite averaging lemma. -/
theorem exists_addable_hits_many_one {Candidate Colour : Type*}
    (X : Finset Candidate) (colours : Finset Colour)
    (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)
    {A q : ℕ} (hA : 0 < A) (hX : 0 < X.card)
    (hdense : ∀ c ∈ colours, X.card ≤ A * (X.filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      2 * A * (X.filter fun x ↦ ¬ Suitable (insert x S)).card < X.card)
    {S : Finset Candidate} (hS : Suitable S) (hSq : S.card < q)
    (hbad : (badColourings colours Hit S).Nonempty) :
    ∃ x ∈ X, Suitable (insert x S) ∧
      (badColourings colours Hit S).card ≤
        (2 * A) * ((badColourings colours Hit S).filter fun c ↦ Hit x c).card := by
  classical
  let strata : Fin 1 → Finset Candidate := fun _ ↦ X
  have hcard : ∀ j : Fin 1, 1 * (strata j).card = X.card := by simp [strata]
  have hdense' : ∀ c ∈ colours, ∃ j : Fin 1,
      (strata j).card ≤ A * ((strata j).filter fun x ↦ Hit x c).card := by
    intro c hc
    exact ⟨0, by simpa [strata] using hdense c hc⟩
  have hnonadd' : ∀ (S : Finset Candidate), Suitable S → S.card < q → ∀ j : Fin 1,
      2 * A * ((strata j).filter fun x ↦ ¬ Suitable (insert x S)).card <
        (strata j).card := by
    intro S hS hSq j
    simpa [strata] using hnonadd S hS hSq
  obtain ⟨j, x, hx, hsx, hhit⟩ :=
    exists_addable_hits_many strata colours Hit Suitable (fun _ ↦ 1)
      hA hX hcard hdense' hnonadd' hS hSq hbad
  exact ⟨x, by simpa [strata] using hx, hsx, by simpa using hhit⟩

/-- The first two binomial terms, in a form sufficient for the integer decay estimate. -/
lemma pow_add_one_linear_lower (x n : ℕ) :
    x ^ (n + 1) + (n + 1) * x ^ n ≤ (x + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmul := Nat.mul_le_mul_right (x + 1) ih
      calc
        x ^ (n + 2) + (n + 2) * x ^ (n + 1)
            ≤ x ^ (n + 2) + (n + 2) * x ^ (n + 1) + (n + 1) * x ^ n :=
              Nat.le_add_right _ _
        _ = (x ^ (n + 1) + (n + 1) * x ^ n) * (x + 1) := by
              simp only [pow_succ]
              ring
        _ ≤ (x + 1) ^ (n + 1) * (x + 1) := hmul
        _ = (x + 1) ^ (n + 2) := by
          exact (pow_succ (x + 1) (n + 1)).symm

/-- `D` successive losses by the ratio `(D-1)/D` reduce an integer count by at least half. -/
lemma two_mul_pred_pow_le_pow {D : ℕ} (hD : 2 ≤ D) :
    2 * (D - 1) ^ D ≤ D ^ D := by
  have hlin := pow_add_one_linear_lower (D - 1) (D - 1)
  have hD1 : D - 1 + 1 = D := Nat.sub_add_cancel (by omega : 1 ≤ D)
  have hlin' : (D - 1) ^ D + D * (D - 1) ^ (D - 1) ≤ D ^ D := by
    simpa [hD1] using hlin
  have hterm : (D - 1) ^ D ≤ D * (D - 1) ^ (D - 1) := by
    calc
      (D - 1) ^ D = (D - 1) ^ ((D - 1) + 1) := by rw [hD1]
      _ = (D - 1) ^ (D - 1) * (D - 1) := pow_succ _ _
      _ ≤ (D - 1) ^ (D - 1) * D :=
        Nat.mul_le_mul_left _ (Nat.sub_le D 1)
      _ = D * (D - 1) ^ (D - 1) := Nat.mul_comm _ _
  omega

lemma decay_power_blocks {D s : ℕ} (hD : 2 ≤ D) :
    2 ^ s * (D - 1) ^ (D * s) ≤ D ^ (D * s) := by
  have h := Nat.pow_le_pow_left (two_mul_pred_pow_le_pow hD) s
  simpa [mul_pow, pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

open Erdos847SparseSelection in
/-- Complete one-stratum greedy selection, with the iteration and vanishing estimate kept over
natural numbers. -/
theorem exists_suitable_hitting_family {Candidate Colour : Type*}
    (X : Finset Candidate) (colours : Finset Colour)
    (Hit : Candidate → Colour → Prop) (Suitable : Finset Candidate → Prop)
    {A s : ℕ} (hA : 0 < A) (hempty : Suitable ∅)
    (hdense : ∀ c ∈ colours, X.card ≤ A * (X.filter fun x ↦ Hit x c).card)
    (hnonadd : ∀ (S : Finset Candidate), Suitable S → S.card < (2 * A) * s →
      2 * A * (X.filter fun x ↦ ¬ Suitable (insert x S)).card < X.card)
    (hcolours : colours.card < 2 ^ s) :
    ∃ S : Finset Candidate, Suitable S ∧
      badColourings colours Hit S = ∅ := by
  classical
  by_cases hcol : colours = ∅
  · exact ⟨∅, hempty, by simp [hcol]⟩
  have hcolne : colours.Nonempty := Finset.nonempty_iff_ne_empty.mpr hcol
  have hcpos : 0 < colours.card := Finset.card_pos.mpr hcolne
  obtain ⟨c, hc⟩ := hcolne
  have hX : 0 < X.card := by
    have hd := hdense c hc
    by_contra hzero
    have hX0 : X.card = 0 := Nat.eq_zero_of_not_pos hzero
    have hfilter0 : (X.filter fun x ↦ Hit x c).card = 0 := by
      have : X = ∅ := Finset.card_eq_zero.mp hX0
      simp [this]
    have hspos : 0 < s := by
      by_contra hs
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
      subst s
      have hlt : colours.card < 1 := by simpa using hcolours
      exact (Nat.not_lt_of_ge hcpos) hlt
    have hqpos : 0 < (2 * A) * s := by positivity
    have := hnonadd ∅ hempty (by simpa using hqpos)
    simp [hX0] at this
  let D := 2 * A
  let q := D * s
  have hD : 2 ≤ D := by
    dsimp [D]
    omega
  have hstep : ∀ (S : Finset Candidate), Suitable S → S.card < q →
      (badColourings colours Hit S).Nonempty →
      ∃ x, Suitable (insert x S) ∧
        D * (badColourings colours Hit (insert x S)).card ≤
          (D - 1) * (badColourings colours Hit S).card := by
    intro S hS hSq hbad
    obtain ⟨x, hxX, hxSuit, hxhit⟩ :=
      exists_addable_hits_many_one X colours Hit Suitable hA hX hdense
        (by simpa [q, D] using hnonadd) hS (by simpa [q, D] using hSq) hbad
    refine ⟨x, hxSuit, ?_⟩
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := badColourings colours Hit S) (fun c ↦ Hit x c)
    have hnext : badColourings colours Hit (insert x S) =
        (badColourings colours Hit S).filter fun c ↦ ¬ Hit x c :=
      badColourings_insert colours Hit x S
    rw [hnext]
    let B := (badColourings colours Hit S).card
    let H := ((badColourings colours Hit S).filter fun c ↦ Hit x c).card
    let R := ((badColourings colours Hit S).filter fun c ↦ ¬ Hit x c).card
    have hBH : B = H + R := by
      dsimp [B, H, R]
      omega
    have hxhit' : B ≤ D * H := by simpa [B, H, D] using hxhit
    have hDRB : D * R + B ≤ D * B := by
      calc
        D * R + B ≤ D * R + D * H := Nat.add_le_add_left hxhit' _
        _ = D * (H + R) := by ring
        _ = D * B := by rw [← hBH]
    have hDB : D * B = (D - 1) * B + B := by
      calc
        D * B = ((D - 1) + 1) * B := by congr 1 <;> omega
        _ = (D - 1) * B + B := by rw [Nat.add_mul, one_mul]
    have hcancel : D * R + B ≤ (D - 1) * B + B := hDRB.trans_eq hDB
    exact Nat.le_of_add_le_add_right hcancel
  obtain ⟨S, hS, hScard, hdec⟩ :=
    iterate_decay colours Hit Suitable (D := D) (q := q)
      (by omega : 0 < D) hempty hstep q (le_rfl)
  have hblock : 2 ^ s * (D - 1) ^ q ≤ D ^ q := by
    simpa [q] using decay_power_blocks hD (s := s)
  have hsmall : (D - 1) ^ q * colours.card < D ^ q := by
    have hpred : 0 < D - 1 := by omega
    have hpredpos : 0 < (D - 1) ^ q := pow_pos hpred q
    calc
      (D - 1) ^ q * colours.card < (D - 1) ^ q * 2 ^ s :=
        (Nat.mul_lt_mul_left hpredpos).2 hcolours
      _ = 2 ^ s * (D - 1) ^ q := Nat.mul_comm _ _
      _ ≤ D ^ q := hblock
  have hzero : (badColourings colours Hit S).card = 0 := by
    by_contra hb
    have hbone : 1 ≤ (badColourings colours Hit S).card := Nat.one_le_iff_ne_zero.mpr hb
    have hlower : D ^ q ≤ D ^ q * (badColourings colours Hit S).card := by
      simpa using Nat.mul_le_mul_left (D ^ q) hbone
    exact (not_lt_of_ge (hlower.trans hdec)) hsmall
  exact ⟨S, hS, Finset.card_eq_zero.mp hzero⟩

/-! ## Disjoint-block candidates and geometric suitability -/

/-- Coordinates in one block of `Fin t × J`. -/
def coordinateBlock {J : Type*} [Fintype J] (t : ℕ) (j : Fin t) :
    Finset (Fin t × J) :=
  Finset.univ.filter fun iq ↦ iq.1 = j

lemma card_coordinateBlock {J : Type*} [Fintype J] (t : ℕ) (j : Fin t) :
    (coordinateBlock (J := J) t j).card = Fintype.card J := by
  classical
  let f : J → Fin t × J := fun q ↦ (j, q)
  have himage : Finset.univ.image f = coordinateBlock (J := J) t j := by
    ext iq
    simp [coordinateBlock, f, Prod.ext_iff, eq_comm]
  rw [← himage, Finset.card_image_of_injective]
  · simp
  · intro q r h
    exact congrArg Prod.snd h

lemma candidateLines_supported {A J : Type*} [Fintype A] [Fintype J]
    (t : ℕ) (S : Finset (Line A J)) :
    Erdos847LineExclusions.SupportedInBlocks
      (Erdos847BlockCandidates.candidateLines t S)
      (coordinateBlock (J := J) t) := by
  classical
  intro l hl
  rcases Erdos847BlockCandidates.mem_candidateLines.mp hl with ⟨c, rfl⟩
  refine ⟨c.1, ?_⟩
  intro iq hi
  have hnone :=
    (Erdos847LineExclusions.mem_movingSet
      (Erdos847BlockCandidates.encodedLine c) iq).mp hi
  have hblock : iq.1 = c.1 := by
    by_contra hne
    simp [Erdos847BlockCandidates.encodedLine, hne] at hnone
  simp [coordinateBlock, hblock]

lemma cleared_fraction_bound {E d U k L : ℕ}
    (hE : E * d ≤ U) (hcross : k * U < d * L) : k * E < L := by
  have hmul : (k * E) * d < L * d := by
    calc
      (k * E) * d = k * (E * d) := by ring
      _ ≤ k * U := Nat.mul_le_mul_left k hE
      _ < d * L := hcross
      _ = L * d := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right hmul

lemma pow_lt_two_pow_mul_add_one (r N : ℕ) :
    r ^ N < 2 ^ (r * N + 1) := by
  have hr : r ≤ 2 ^ r := r.lt_two_pow_self.le
  have hp : r ^ N ≤ (2 ^ r) ^ N := Nat.pow_le_pow_left hr N
  have heq : (2 ^ r) ^ N = 2 ^ (r * N) := by rw [pow_mul]
  have hlt : 2 ^ (r * N) < 2 ^ (r * N + 1) :=
    Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  exact hp.trans_eq heq |>.trans_lt hlt

/-! ## Natural-number parameter hierarchy for sparse selection

The paper writes `n ≫ d ≫ α⁻¹ ≫ m`.  The following explicit integer parameters implement
the denominator-cleared scheme used by the finite greedy proof.  Keeping these quantities in `ℕ`
avoids logarithms and real-valued probability estimates.
-/

/-- A common denominator for the monochromatic-line density supplied by Hales--Jewett
double counting. -/
def densityDenom (a m : ℕ) : ℕ := a ^ m * m ^ (m + 1)

/-- If `D = deletionDenom a m`, one admissible line eliminates at least a `1/D` fraction
of the currently bad colorings. -/
def deletionDenom (a m : ℕ) : ℕ := 2 * densityDenom a m * m

/-- Constant used to dominate the length of the greedy construction. -/
def growthConst (a m r : ℕ) : ℕ := deletionDenom a m * (r + 1)

/-- Explicit selected-line degree cap. -/
def degreeCap (a m r : ℕ) : ℕ :=
  4 * densityDenom a m * growthConst a m r * a ^ (m + 1)

/-- Explicit ambient dimension large enough for both the Hales--Jewett embedding and the
tripod/triangle completion estimate. -/
def sparseDimension (a m r : ℕ) : ℕ :=
  max (m + 1)
    (8 * densityDenom a m * (degreeCap a m r) ^ 2 * a ^ (m + 2))

lemma lt_sparseDimension (a m r : ℕ) : m < sparseDimension a m r := by
  exact (Nat.lt_succ_self m).trans_le (Nat.le_max_left _ _)

lemma completion_bound_le_sparseDimension (a m r : ℕ) :
    8 * densityDenom a m * (degreeCap a m r) ^ 2 * a ^ (m + 2) ≤
      sparseDimension a m r :=
  Nat.le_max_right _ _

lemma degreeCap_meets_bound (a m r : ℕ) :
    4 * densityDenom a m * growthConst a m r * a ^ (m + 1) ≤
      degreeCap a m r := by
  rfl

lemma deletionDenom_two_le {a m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    2 ≤ deletionDenom a m := by
  have hden : 0 < densityDenom a m := by
    unfold densityDenom
    positivity
  have hprod : 0 < densityDenom a m * m := Nat.mul_pos hden hm
  simpa [deletionDenom, Nat.mul_assoc] using
    Nat.mul_le_mul_left 2 (show 1 ≤ densityDenom a m * m by omega)

/-- The advertised greedy step budget `D (r a^n + 1)` is bounded by `C a^n`. -/
lemma greedyBudget_le {a m r n : ℕ} (ha : 0 < a) :
    deletionDenom a m * (r * a ^ n + 1) ≤ growthConst a m r * a ^ n := by
  have hp : 1 ≤ a ^ n := one_le_pow₀ (by omega : 1 ≤ a)
  unfold growthConst
  nlinarith

/-! The following denominator-cleared calculation is the numerical core of the
disjoint-block construction.  It is deliberately stated independently of the
geometry: the first summand is the saturated-point exclusion and the second is
the combined tripod/triangle certificate bound. -/

lemma block_parameter_bound
    {a m r A₀ C d t V P F s N M : ℕ}
    (ha : 0 < a) (hA₀ : 0 < A₀) (hP : 0 < P)
    (hC : C = 2 * A₀ * (r + 1))
    (hd : d = 4 * A₀ * a * C * a ^ m * 2 ^ m + 1)
    (ht : t = 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1)
    (hV : V = P * a ^ m) (hF : F = t * P) (hs : s = r * V + 1)
    (hN : N < 2 * A₀ * s) (hFM : F ≤ M) :
    (2 * A₀) *
        ((a * N) * (t * 2 ^ m) +
          (d ^ 2 * V + (a * d) ^ 2 * V) * d) < d * M := by
  have hVpos : 0 < V := by rw [hV]; positivity
  have hVone : 1 ≤ V := by omega
  have hCpos : 0 < C := by rw [hC]; positivity
  have hdpos : 0 < d := by rw [hd]; positivity
  have htpos : 0 < t := by rw [ht]; positivity
  have hFpos : 0 < F := by rw [hF]; positivity
  have hNs : N < C * V := by
    calc
      N < 2 * A₀ * s := hN
      _ ≤ 2 * A₀ * ((r + 1) * V) := by
        apply Nat.mul_le_mul_left
        rw [hs]
        calc
          r * V + 1 ≤ r * V + V := Nat.add_le_add_left hVone _
          _ = (r + 1) * V := by ring
      _ = C * V := by rw [hC]; ring
  let U₁ := (a * N) * (t * 2 ^ m)
  let U₂ := (d ^ 2 * V + (a * d) ^ 2 * V) * d
  have hU₁raw : U₁ < (a * (C * V)) * (t * 2 ^ m) := by
    dsimp [U₁]
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_left hNs ha) (by positivity)
  have hU₁ : (4 * A₀) * U₁ < d * F := by
    calc
      (4 * A₀) * U₁ < (4 * A₀) * ((a * (C * V)) * (t * 2 ^ m)) :=
        Nat.mul_lt_mul_of_pos_left hU₁raw (by positivity)
      _ = (4 * A₀ * a * C * a ^ m * 2 ^ m) * F := by
        rw [hV, hF]
        ring
      _ < d * F := by
        apply Nat.mul_lt_mul_of_pos_right _ hFpos
        rw [hd]
        omega
  have had : d ≤ a * d := by
    calc
      d = 1 * d := by simp
      _ ≤ a * d := Nat.mul_le_mul_right d (by omega)
  have hU₂raw : U₂ ≤ 2 * a ^ 2 * d ^ 3 * V := by
    dsimp [U₂]
    calc
      (d ^ 2 * V + (a * d) ^ 2 * V) * d
          ≤ ((a * d) ^ 2 * V + (a * d) ^ 2 * V) * d := by
            apply Nat.mul_le_mul_right
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right V (Nat.pow_le_pow_left had 2)) _
      _ = 2 * a ^ 2 * d ^ 3 * V := by ring
  have hU₂ : (4 * A₀) * U₂ < d * F := by
    calc
      (4 * A₀) * U₂ ≤ (4 * A₀) * (2 * a ^ 2 * d ^ 3 * V) :=
        Nat.mul_le_mul_left _ hU₂raw
      _ = (8 * A₀ * a ^ 2 * d ^ 2 * a ^ m) * (d * P) := by
        rw [hV]
        ring
      _ < t * (d * P) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
        rw [ht]
        omega
      _ = d * F := by rw [hF]; ring
  have hsum : (4 * A₀) * (U₁ + U₂) < d * F + d * F := by
    rw [Nat.mul_add]
    exact Nat.add_lt_add hU₁ hU₂
  have hdouble : 2 * ((2 * A₀) * (U₁ + U₂)) < 2 * (d * F) := by
    convert hsum using 1 <;> ring
  have hhalf : (2 * A₀) * (U₁ + U₂) < d * F :=
    (Nat.mul_lt_mul_left (by omega : 0 < 2)).mp hdouble
  exact hhalf.trans_le (Nat.mul_le_mul_left d hFM)

/-- The numerical estimate above, combined with the geometric exclusion
lemmas, says that fewer than a `1/(2A₀)` fraction of the disjoint-block
candidates are forbidden at every greedy stage.  Factoring this out keeps the
final Ramsey construction inexpensive to elaborate. -/
theorem block_candidates_nonaddable
    (A : Type u) [Fintype A] [Nontrivial A]
    {J : Type v} [Fintype J] (S : Finset (Line A J)) (hSne : S.Nonempty)
    {a m r A₀ C d t P V F s : ℕ}
    (ha : 0 < a) (hA₀ : 0 < A₀) (hP : 0 < P)
    (haeq : a = Fintype.card A) (hmeq : m = Fintype.card J)
    (hC : C = 2 * A₀ * (r + 1))
    (hd : d = 4 * A₀ * a * C * a ^ m * 2 ^ m + 1)
    (ht : t = 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1)
    (hPdef : P = a ^ (m * (t - 1)))
    (hV : V = P * a ^ m) (hF : F = t * P) (hs : s = r * V + 1)
    (R : Finset (Line A (Fin t × J)))
    (hR : Erdos847LineExclusions.Suitable R d)
    (hRcard : R.card < (2 * A₀) * s) :
    (2 * A₀) *
        (Erdos847LineExclusions.nonaddable
          (Erdos847BlockCandidates.candidateLines t S) R d).card <
      (Erdos847BlockCandidates.candidateLines t S).card := by
  let : DecidableEq (Fin t × J) := Classical.decEq _
  have htpos : 0 < t := by rw [ht]; positivity
  have htone : 1 ≤ t := by omega
  have htm : t * m = m * (t - 1) + m := by
    calc
      t * m = ((t - 1) + 1) * m := by rw [Nat.sub_add_cancel htone]
      _ = m * (t - 1) + m := by ring
  have hcube : Fintype.card (Fin t × J → A) = V := by
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    rw [← haeq, ← hmeq]
    rw [htm, pow_add, ← hPdef, hV]
  have hFlower : F ≤
      (Erdos847BlockCandidates.candidateLines t S).card := by
    rw [hF, hPdef, haeq, hmeq]
    exact Erdos847BlockCandidates.candidateLines_card_lower hSne
  have hparam : (2 * A₀) *
      ((Fintype.card A * R.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (Fin t × J → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (Fin t × J → A)) * d) <
      d * (Erdos847BlockCandidates.candidateLines t S).card := by
    rw [← haeq, hcube]
    exact block_parameter_bound ha hA₀ hP hC hd ht hV hF hs hRcard hFlower
  exact Erdos847LineExclusions.nonaddable_fraction
    (t := t) (m := m) (d := d) (A₀ := A₀)
    (Erdos847BlockCandidates.candidateLines t S) R
    (coordinateBlock (J := J) t)
    (candidateLines_supported t S)
    (by intro j; simpa [hmeq] using card_coordinateBlock (J := J) t j)
    hR hparam

/-- Exact target of the sparse Hales--Jewett selection step. -/
def SparseHalesJewett (A : Type u) (K : Type w) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (S : Finset (Line A I)),
    IsSparse S ∧ IsRamseyFamily S K

/-- Sparse Hales--Jewett, in the exact tripod/triangle-free form used by
Reiher--Rödl--Sales.  The ambient cube consists of many disjoint copies of an
ordinary Hales--Jewett cube. -/
theorem sparse_hales_jewett (A : Type u) [Fintype A] [Nontrivial A]
    (K : Type w) [Fintype K] : SparseHalesJewett A K := by
  classical
  cases isEmpty_or_nonempty K with
  | inl hK =>
      let : IsEmpty K := hK
      refine ⟨PEmpty, inferInstance, ∅, isSparse_empty, ?_⟩
      intro color
      exact isEmptyElim (color fun i ↦ nomatch i)
  | inr hK =>
      let : Nonempty K := hK
      let : Inhabited K := Classical.inhabited_of_nonempty hK
      obtain ⟨J, hJ, S, hHJ⟩ := exists_finite_ramsey_family A K
      let : Fintype J := hJ
      have hSne : S.Nonempty := by
        obtain ⟨l, hl, -⟩ := hHJ (fun _ ↦ default)
        exact ⟨l, hl⟩
      let a := Fintype.card A
      let m := Fintype.card J
      let r := Fintype.card K
      let A₀ := (a + 1) ^ m
      let C := 2 * A₀ * (r + 1)
      let d := 4 * A₀ * a * C * a ^ m * 2 ^ m + 1
      let t := 8 * A₀ * a ^ 2 * d ^ 2 * a ^ m + 1
      let P := a ^ (m * (t - 1))
      let V := P * a ^ m
      let F := t * P
      let s := r * V + 1
      let X : Finset (Line A (Fin t × J)) :=
        Erdos847BlockCandidates.candidateLines t S
      let colours : Finset (((Fin t × J → A) → K)) := Finset.univ
      let Hit : Line A (Fin t × J) → ((Fin t × J → A) → K) → Prop :=
        fun l color ↦ l.IsMono color
      let Good : Finset (Line A (Fin t × J)) → Prop :=
        fun R ↦ Erdos847LineExclusions.Suitable R d
      have ha : 0 < a := by
        dsimp [a]
        exact Fintype.card_pos
      have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
      have hd : 0 < d := by dsimp [d]; positivity
      have ht : 0 < t := by dsimp [t]; positivity
      have htone : 1 ≤ t := by omega
      have hP : 0 < P := by dsimp [P]; positivity
      have hF : 0 < F := by dsimp [F]; positivity
      have htm : t * m = m * (t - 1) + m := by
        calc
          t * m = ((t - 1) + 1) * m := by rw [Nat.sub_add_cancel htone]
          _ = m * (t - 1) + m := by ring
      have hcube : Fintype.card (Fin t × J → A) = V := by
        rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
        change a ^ (t * m) = V
        rw [htm, pow_add]
      have hFlower : F ≤ X.card := by
        simpa [F, P, X, a, m] using
          (Erdos847BlockCandidates.candidateLines_card_lower
            (t := t) (S := S) hSne)
      have hX : 0 < X.card := hF.trans_le hFlower
      have hdense : ∀ c ∈ colours,
          X.card ≤ A₀ * (X.filter fun l ↦ Hit l c).card := by
        intro c _hc
        have hupper := Erdos847BlockCandidates.candidateLines_card_upper t S
        have hlower := Erdos847BlockCandidates.monoCandidateLines_card_lower hHJ c
        calc
          X.card ≤ F * A₀ := by
            simpa [X, F, P, A₀, a, m] using hupper
          _ = A₀ * F := by ring
          _ ≤ A₀ * (X.filter fun l ↦ Hit l c).card := by
            apply Nat.mul_le_mul_left
            simpa [X, Hit, F, P, a, m,
              Erdos847BlockCandidates.monoCandidateLines] using hlower
      have hempty : Good ∅ := by
        dsimp [Good]
        constructor
        · intro x
          simp [Erdos847LineExclusions.DegreeBound,
            Erdos847LineExclusions.lineDegree,
            Erdos847LineExclusions.incidentLines]
        · constructor
          · simp [Erdos847LineExclusions.HasTripod]
          · simp [Erdos847LineExclusions.HasTriangle]
      have hnonadd : ∀ (R : Finset (Line A (Fin t × J))), Good R →
          R.card < (2 * A₀) * s →
          2 * A₀ * (X.filter fun l ↦ ¬ Good (insert l R)).card < X.card := by
        intro R hR hRcard
        change Erdos847LineExclusions.Suitable R d at hR
        change (2 * A₀) *
          (Erdos847LineExclusions.nonaddable X R d).card < X.card
        change (2 * A₀) *
          (Erdos847LineExclusions.nonaddable
            (Erdos847BlockCandidates.candidateLines t S) R d).card <
          (Erdos847BlockCandidates.candidateLines t S).card
        exact block_candidates_nonaddable A S hSne ha hA₀ hP
          rfl rfl rfl rfl rfl rfl rfl rfl rfl R hR hRcard
      have hcolourCard : colours.card = r ^ V := by
        rw [show colours.card = Fintype.card ((Fin t × J → A) → K) by
          simp [colours]]
        rw [Fintype.card_fun]
        change r ^ Fintype.card (Fin t × J → A) = r ^ V
        rw [hcube]
      have hcolours : colours.card < 2 ^ s := by
        rw [hcolourCard]
        simpa [s] using pow_lt_two_pow_mul_add_one r V
      obtain ⟨R, hR, hbad⟩ := exists_suitable_hitting_family
        X colours Hit Good hA₀ hempty hdense hnonadd hcolours
      refine ⟨Fin t × J, inferInstance, R, ?_, ?_⟩
      · constructor
        · change ¬ Erdos847LineExclusions.HasTripod R
          exact hR.2.1
        · change ¬ Erdos847LineExclusions.HasTriangle R
          exact hR.2.2
      · intro color
        by_contra hnone
        have hall : ∀ l ∈ R, ¬ Hit l color := by
          intro l hl hmono
          exact hnone ⟨l, hl, hmono⟩
        have hmem : color ∈ Erdos847SparseSelection.badColourings colours Hit R :=
          Erdos847SparseSelection.mem_badColourings.mpr ⟨Finset.mem_univ _, hall⟩
        rw [hbad] at hmem
        simp at hmem

end Erdos847SparseLines
