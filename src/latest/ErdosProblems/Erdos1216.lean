/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1216.
https://www.erdosproblems.com/forum/thread/1216

Informal authors:
- K. B. Reid
- E. T. Parker

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1216.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1216.Certificates
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.IntervalCases

/-!
# Erdős Problem 1216

Reid and Parker proved that every tournament on fourteen vertices contains
a transitive tournament on five vertices.  This gives a negative answer to
the proposed formula at n = 14.  The finite exhaustion is stored in
ErdosProblems.Erdos1216.Certificates and checked by definitional reduction.

A detailed mathematical proof and Leanization plan are in tex/1216.tex.
-/

open Function
open Erdos1216.Certificates

namespace Erdos1216

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A labeled tournament on n vertices.  Only upper-triangle bits are read;
the lower triangle and diagonal are determined by tournament symmetry. -/
abbrev Tournament (n : Nat) := BitVec (n * n)

/-- The directed edge relation encoded by a tournament bit-vector. -/
def Tournament.arc {n : Nat} (T : Tournament n) (i j : Fin n) : Bool :=
  if i = j then false
  else if i < j then T.getLsbD (i.1 * n + j.1)
  else !T.getLsbD (j.1 * n + i.1)

lemma Tournament.arc_self {n : Nat} (T : Tournament n) (i : Fin n) :
    T.arc i i = false := by
  simp [Tournament.arc]

lemma Tournament.arc_reverse {n : Nat} (T : Tournament n) {i j : Fin n}
    (hij : i ≠ j) : T.arc i j = !T.arc j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [Tournament.arc, hij, hij.symm, h, not_lt_of_ge h.le]
  · exact (hij h).elim
  · simp [Tournament.arc, hij, hij.symm, h, not_lt_of_ge h.le]

/-- An ordered injective transitive subtournament. -/
def HasTransitiveTournament {n : Nat} (T : Tournament n) (k : Nat) : Prop :=
  ∃ v : Fin k → Fin n, Injective v ∧
    ∀ i j : Fin k, i < j → T.arc (v i) (v j) = true

/-- The property that every n-vertex tournament contains a transitive k-set. -/
def Guaranteed (n k : Nat) : Prop :=
  k ≤ n ∧ ∀ T : Tournament n, HasTransitiveTournament T k

/-- The exact extremal function from Problem 1216. -/
def f (n : Nat) : Nat :=
  Nat.findGreatest (Guaranteed n) n

/-- The formula proposed in Problem 1216. -/
def ProposedFormula : Prop :=
  ∀ n, 1 ≤ n → f n = Nat.log2 n + 1

def compactArc {w : Nat} (code : BitVec w) (n : Nat) (i j : Nat) : Bool :=
  if i = j then false
  else if i < j then code.getLsbD (Certificates.pairIndex n i j)
  else !code.getLsbD (Certificates.pairIndex n j i)

lemma lit_arc {w n i j : Nat} {code : BitVec w} (hij : i ≠ j)
    (h : Certificates.litSatisfied code (Certificates.arcLit n i j) = true) :
    compactArc code n i j = true := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · simp [Certificates.arcLit, compactArc, Certificates.litSatisfied, hlt,
      ne_of_lt hlt] at h ⊢
    exact h
  · exact (hij heq).elim
  · simp [Certificates.arcLit, compactArc, Certificates.litSatisfied, hgt,
      ne_of_gt hgt, not_lt_of_ge hgt.le] at h ⊢
    exact h

lemma order4_data (o : Certificates.Order4) {n : Nat}
    (h : o.data n = true) :
    o.a < n ∧ o.b < n ∧ o.c < n ∧ o.d < n ∧
    o.a ≠ o.b ∧ o.a ≠ o.c ∧ o.a ≠ o.d ∧
    o.b ≠ o.c ∧ o.b ≠ o.d ∧ o.c ≠ o.d := by
  simp [Certificates.Order4.data, Bool.and_eq_true] at h
  aesop

lemma order4_compact {w n : Nat} {code : BitVec w}
    (o : Certificates.Order4) (h : o.holds code n = true) :
    ∃ a b c d : Fin n,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      compactArc code n a b = true ∧ compactArc code n a c = true ∧
      compactArc code n a d = true ∧ compactArc code n b c = true ∧
      compactArc code n b d = true ∧ compactArc code n c d = true := by
  rw [Certificates.Order4.holds, Bool.and_eq_true] at h
  obtain ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    order4_data o h.1
  let a : Fin n := ⟨o.a, ha⟩
  let b : Fin n := ⟨o.b, hb⟩
  let c : Fin n := ⟨o.c, hc⟩
  let d : Fin n := ⟨o.d, hd⟩
  have hall := h.2
  simp only [Certificates.Order4.lits, List.all_cons, List.all_nil,
    Bool.and_eq_true, Bool.true_eq] at hall
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hab (Fin.ext_iff.mp h)
  · exact fun h => hac (Fin.ext_iff.mp h)
  · exact fun h => had (Fin.ext_iff.mp h)
  · exact fun h => hbc (Fin.ext_iff.mp h)
  · exact fun h => hbd (Fin.ext_iff.mp h)
  · exact fun h => hcd (Fin.ext_iff.mp h)
  · exact lit_arc hab hall.1
  · exact lit_arc hac hall.2.1
  · exact lit_arc had hall.2.2.1
  · exact lit_arc hbc hall.2.2.2.1
  · exact lit_arc hbd hall.2.2.2.2.1
  · exact lit_arc hcd hall.2.2.2.2.2.1

lemma compactArc_pack {m w n : Nat} {code : BitVec w} {T : Tournament n}
    {e : Fin m → Fin n} (he : Injective e)
    (hget : ∀ i j : Fin m, i < j →
      code.getLsbD (Certificates.pairIndex m i.1 j.1) = T.arc (e i) (e j))
    {i j : Fin m} (hij : i ≠ j) :
    compactArc code m i.1 j.1 = T.arc (e i) (e j) := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hval : i.1 ≠ j.1 := by omega
    simp [compactArc, hval, hlt, hget i j hlt]
  · exact (hij heq).elim
  · have hval : i.1 ≠ j.1 := by omega
    have hnlt : ¬ i.1 < j.1 := by omega
    have hne : e i ≠ e j := fun h => (ne_of_gt hgt) (he h)
    rw [compactArc]
    simp only [hval, hnlt, if_false]
    rw [hget j i hgt]
    exact (T.arc_reverse hne).symm

lemma order4_to_transitive {m w n : Nat} {code : BitVec w} {T : Tournament n}
    {e : Fin m → Fin n} (he : Injective e)
    (hget : ∀ i j : Fin m, i < j →
      code.getLsbD (Certificates.pairIndex m i.1 j.1) = T.arc (e i) (e j))
    {o : Certificates.Order4} (ho : o.holds code m = true) :
    HasTransitiveTournament T 4 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    eab, eac, ead, ebc, ebd, ecd⟩ := order4_compact o ho
  let v : Fin 4 → Fin n := ![e a, e b, e c, e d]
  have heab : e a ≠ e b := fun h => hab (he h)
  have heac : e a ≠ e c := fun h => hac (he h)
  have head : e a ≠ e d := fun h => had (he h)
  have hebc : e b ≠ e c := fun h => hbc (he h)
  have hebd : e b ≠ e d := fun h => hbd (he h)
  have hecd : e c ≠ e d := fun h => hcd (he h)
  refine ⟨v, ?_, ?_⟩
  · intro i j hij'
    fin_cases i <;> fin_cases j <;> simp_all [v]
  · intro i j hij'
    fin_cases i <;> fin_cases j <;>
      simp_all [v, compactArc_pack he hget]

def pack6 {n : Nat} (T : Tournament n) (e : Fin 6 → Fin n) : BitVec 15 :=
  BitVec.ofBoolListLE [
    T.arc (e 0) (e 1),
    T.arc (e 0) (e 2),
    T.arc (e 0) (e 3),
    T.arc (e 0) (e 4),
    T.arc (e 0) (e 5),
    T.arc (e 1) (e 2),
    T.arc (e 1) (e 3),
    T.arc (e 1) (e 4),
    T.arc (e 1) (e 5),
    T.arc (e 2) (e 3),
    T.arc (e 2) (e 4),
    T.arc (e 2) (e 5),
    T.arc (e 3) (e 4),
    T.arc (e 3) (e 5),
    T.arc (e 4) (e 5)]

lemma pack6_get {n : Nat} (T : Tournament n) (e : Fin 6 → Fin n)
    (i j : Fin 6) (hij : i < j) :
    (pack6 T e).getLsbD (Certificates.pairIndex 6 i.1 j.1) =
      T.arc (e i) (e j) := by
  fin_cases i <;> fin_cases j <;>
    simp at hij <;>
    rw [pack6, BitVec.getLsbD_ofBoolListLE] <;>
    rfl

def pack7 {n : Nat} (T : Tournament n) (e : Fin 7 → Fin n) : BitVec 21 :=
  BitVec.ofBoolListLE [
    T.arc (e 0) (e 1),
    T.arc (e 0) (e 2),
    T.arc (e 0) (e 3),
    T.arc (e 0) (e 4),
    T.arc (e 0) (e 5),
    T.arc (e 0) (e 6),
    T.arc (e 1) (e 2),
    T.arc (e 1) (e 3),
    T.arc (e 1) (e 4),
    T.arc (e 1) (e 5),
    T.arc (e 1) (e 6),
    T.arc (e 2) (e 3),
    T.arc (e 2) (e 4),
    T.arc (e 2) (e 5),
    T.arc (e 2) (e 6),
    T.arc (e 3) (e 4),
    T.arc (e 3) (e 5),
    T.arc (e 3) (e 6),
    T.arc (e 4) (e 5),
    T.arc (e 4) (e 6),
    T.arc (e 5) (e 6)]

lemma pack7_get {n : Nat} (T : Tournament n) (e : Fin 7 → Fin n)
    (i j : Fin 7) (hij : i < j) :
    (pack7 T e).getLsbD (Certificates.pairIndex 7 i.1 j.1) =
      T.arc (e i) (e j) := by
  fin_cases i <;> fin_cases j <;>
    simp at hij <;>
    rw [pack7, BitVec.getLsbD_ofBoolListLE] <;>
    rfl

def pack8 {n : Nat} (T : Tournament n) (e : Fin 8 → Fin n) : BitVec 28 :=
  BitVec.ofBoolListLE [
    T.arc (e 0) (e 1),
    T.arc (e 0) (e 2),
    T.arc (e 0) (e 3),
    T.arc (e 0) (e 4),
    T.arc (e 0) (e 5),
    T.arc (e 0) (e 6),
    T.arc (e 0) (e 7),
    T.arc (e 1) (e 2),
    T.arc (e 1) (e 3),
    T.arc (e 1) (e 4),
    T.arc (e 1) (e 5),
    T.arc (e 1) (e 6),
    T.arc (e 1) (e 7),
    T.arc (e 2) (e 3),
    T.arc (e 2) (e 4),
    T.arc (e 2) (e 5),
    T.arc (e 2) (e 6),
    T.arc (e 2) (e 7),
    T.arc (e 3) (e 4),
    T.arc (e 3) (e 5),
    T.arc (e 3) (e 6),
    T.arc (e 3) (e 7),
    T.arc (e 4) (e 5),
    T.arc (e 4) (e 6),
    T.arc (e 4) (e 7),
    T.arc (e 5) (e 6),
    T.arc (e 5) (e 7),
    T.arc (e 6) (e 7)]

lemma pack8_get {n : Nat} (T : Tournament n) (e : Fin 8 → Fin n)
    (i j : Fin 8) (hij : i < j) :
    (pack8 T e).getLsbD (Certificates.pairIndex 8 i.1 j.1) =
      T.arc (e i) (e j) := by
  fin_cases i <;> fin_cases j <;>
    simp at hij <;>
    rw [pack8, BitVec.getLsbD_ofBoolListLE] <;>
    rfl

lemma order4_prepend {m w n : Nat} {code : BitVec w} {T : Tournament n}
    {e : Fin m → Fin n} (he : Injective e)
    (hget : ∀ i j : Fin m, i < j →
      code.getLsbD (Certificates.pairIndex m i.1 j.1) = T.arc (e i) (e j))
    {o : Certificates.Order4} (ho : o.holds code m = true)
    (v : Fin n) (hv : ∀ i, T.arc v (e i) = true)
    (hvne : ∀ i, v ≠ e i) : HasTransitiveTournament T 5 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    eab, eac, ead, ebc, ebd, ecd⟩ := order4_compact o ho
  let u : Fin 5 → Fin n := ![v, e a, e b, e c, e d]
  have heab : e a ≠ e b := fun h => hab (he h)
  have heac : e a ≠ e c := fun h => hac (he h)
  have head : e a ≠ e d := fun h => had (he h)
  have hebc : e b ≠ e c := fun h => hbc (he h)
  have hebd : e b ≠ e d := fun h => hbd (he h)
  have hecd : e c ≠ e d := fun h => hcd (he h)
  have hva : v ≠ e a := hvne a
  have hvb : v ≠ e b := hvne b
  have hvc : v ≠ e c := hvne c
  have hvd : v ≠ e d := hvne d
  have hav : e a ≠ v := hva.symm
  have hbv : e b ≠ v := hvb.symm
  have hcv : e c ≠ v := hvc.symm
  have hdv : e d ≠ v := hvd.symm
  refine ⟨u, ?_, ?_⟩
  · intro i j hij'
    fin_cases i <;> fin_cases j <;> simp_all [u]
  · intro i j hij'
    fin_cases i <;> fin_cases j <;>
      simp_all [u, compactArc_pack he hget]

lemma order4_append {m w n : Nat} {code : BitVec w} {T : Tournament n}
    {e : Fin m → Fin n} (he : Injective e)
    (hget : ∀ i j : Fin m, i < j →
      code.getLsbD (Certificates.pairIndex m i.1 j.1) = T.arc (e i) (e j))
    {o : Certificates.Order4} (ho : o.holds code m = true)
    (v : Fin n) (hv : ∀ i, T.arc (e i) v = true)
    (hvne : ∀ i, e i ≠ v) : HasTransitiveTournament T 5 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
    eab, eac, ead, ebc, ebd, ecd⟩ := order4_compact o ho
  let u : Fin 5 → Fin n := ![e a, e b, e c, e d, v]
  have heab : e a ≠ e b := fun h => hab (he h)
  have heac : e a ≠ e c := fun h => hac (he h)
  have head : e a ≠ e d := fun h => had (he h)
  have hebc : e b ≠ e c := fun h => hbc (he h)
  have hebd : e b ≠ e d := fun h => hbd (he h)
  have hecd : e c ≠ e d := fun h => hcd (he h)
  have hva : e a ≠ v := hvne a
  have hvb : e b ≠ v := hvne b
  have hvc : e c ≠ v := hvne c
  have hvd : e d ≠ v := hvne d
  have hav : v ≠ e a := hva.symm
  have hbv : v ≠ e b := hvb.symm
  have hcv : v ≠ e c := hvc.symm
  have hdv : v ≠ e d := hvd.symm
  refine ⟨u, ?_, ?_⟩
  · intro i j hij'
    fin_cases i <;> fin_cases j <;> simp_all [u]
  · intro i j hij'
    fin_cases i <;> fin_cases j <;>
      simp_all [u, compactArc_pack he hget]

lemma eight_prepend {n : Nat} (T : Tournament n) (e : Fin 8 → Fin n)
    (he : Injective e) (v : Fin n)
    (hv : ∀ i, T.arc v (e i) = true) (hvne : ∀ i, v ≠ e i) :
    HasTransitiveTournament T 5 := by
  obtain ⟨o, ho⟩ := Certificates.R4.four_exists (pack8 T e)
  exact order4_prepend he (pack8_get T e) ho v hv hvne

lemma eight_append {n : Nat} (T : Tournament n) (e : Fin 8 → Fin n)
    (he : Injective e) (v : Fin n)
    (hv : ∀ i, T.arc (e i) v = true) (hvne : ∀ i, e i ≠ v) :
    HasTransitiveTournament T 5 := by
  obtain ⟨o, ho⟩ := Certificates.R4.four_exists (pack8 T e)
  exact order4_append he (pack8_get T e) ho v hv hvne

def outSet {n : Nat} (T : Tournament n) (v : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase v).filter fun x => T.arc v x = true

def inSet {n : Nat} (T : Tournament n) (v : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase v).filter fun x => T.arc v x ≠ true

lemma outSet_card_add_inSet_card {n : Nat} (T : Tournament n) (v : Fin n) :
    (outSet T v).card + (inSet T v).card = n - 1 := by
  rw [outSet, inSet, Finset.card_filter_add_card_filter_not]
  simp

lemma outSet_mem {n : Nat} {T : Tournament n} {v x : Fin n}
    (h : x ∈ outSet T v) : T.arc v x = true ∧ v ≠ x := by
  simp only [outSet, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at h
  exact ⟨h.2, h.1.symm⟩

lemma inSet_mem {n : Nat} {T : Tournament n} {v x : Fin n}
    (h : x ∈ inSet T v) : T.arc x v = true ∧ x ≠ v := by
  simp only [inSet, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at h
  have hfalse : T.arc v x = false := Bool.eq_false_of_not_eq_true h.2
  have hrev := T.arc_reverse h.1
  simp [hfalse] at hrev
  exact ⟨hrev, h.1⟩

lemma outSet_card_le_seven (T : Tournament 14)
    (hfree : ¬ HasTransitiveTournament T 5) (v : Fin 14) :
    (outSet T v).card ≤ 7 := by
  by_contra h
  have hcard : 8 ≤ (outSet T v).card := by omega
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hcard
  let E := Finset.orderIsoOfFin s hscard
  let e : Fin 8 → Fin 14 := fun i => (E i).1
  have he : Injective e := by
    intro i j hij
    apply E.injective
    exact Subtype.ext hij
  have hemem : ∀ i, e i ∈ s := fun i => (E i).2
  have hout : ∀ i, T.arc v (e i) = true := by
    intro i
    exact (outSet_mem (hs (hemem i))).1
  have hne : ∀ i, v ≠ e i := by
    intro i
    exact (outSet_mem (hs (hemem i))).2
  exact hfree (eight_prepend T e he v hout hne)

lemma inSet_card_le_seven (T : Tournament 14)
    (hfree : ¬ HasTransitiveTournament T 5) (v : Fin 14) :
    (inSet T v).card ≤ 7 := by
  by_contra h
  have hcard : 8 ≤ (inSet T v).card := by omega
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hcard
  let E := Finset.orderIsoOfFin s hscard
  let e : Fin 8 → Fin 14 := fun i => (E i).1
  have he : Injective e := by
    intro i j hij
    apply E.injective
    exact Subtype.ext hij
  have hemem : ∀ i, e i ∈ s := fun i => (E i).2
  have hin : ∀ i, T.arc (e i) v = true := by
    intro i
    exact (inSet_mem (hs (hemem i))).1
  have hne : ∀ i, e i ≠ v := by
    intro i
    exact (inSet_mem (hs (hemem i))).2
  exact hfree (eight_append T e he v hin hne)

lemma q6_arc_reverse {i j : Fin 6} (hij : i ≠ j) :
    Certificates.Q6.qArc i j = !Certificates.Q6.qArc j i := by
  fin_cases i <;> fin_cases j <;> simp at hij <;> rfl

lemma q7_arc_reverse {i j : Fin 7} (hij : i ≠ j) :
    Certificates.Q7.qArc i j = !Certificates.Q7.qArc j i := by
  fin_cases i <;> fin_cases j <;> simp at hij <;> rfl

lemma q6_injective_of_bool {p : Fin 6 → Fin 6}
    (h : Certificates.Q6.injectiveBool p = true) : Injective p := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Certificates.Q6.injectiveBool]

lemma q7_injective_of_bool {p : Fin 7 → Fin 7}
    (h : Certificates.Q7.injectiveBool p = true) : Injective p := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [Certificates.Q7.injectiveBool]

lemma q6_orbit_bit {code : BitVec 15} {p : Fin 6 → Fin 6}
    (h : Certificates.Q6.orbitHolds code p = true)
    {i j : Fin 6} (hij : i < j) :
    code.getLsbD (Certificates.pairIndex 6 i.1 j.1) =
      Certificates.Q6.qArc (p i) (p j) := by
  rw [Certificates.Q6.orbitHolds, Bool.and_eq_true] at h
  have hmem :
      ⟨Certificates.pairIndex 6 i.1 j.1,
        Certificates.Q6.qArc (p i) (p j)⟩ ∈ Certificates.Q6.orbitLits p := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [Certificates.Q6.orbitLits, Certificates.pairIndex]
  have hs := (List.all_eq_true.mp h.2) _ hmem
  simpa [Certificates.litSatisfied] using hs

lemma q7_orbit_bit {code : BitVec 21} {p : Fin 7 → Fin 7}
    (h : Certificates.Q7.orbitHolds code p = true)
    {i j : Fin 7} (hij : i < j) :
    code.getLsbD (Certificates.pairIndex 7 i.1 j.1) =
      Certificates.Q7.qArc (p i) (p j) := by
  rw [Certificates.Q7.orbitHolds, Bool.and_eq_true] at h
  have hmem :
      ⟨Certificates.pairIndex 7 i.1 j.1,
        Certificates.Q7.qArc (p i) (p j)⟩ ∈ Certificates.Q7.orbitLits p := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [Certificates.Q7.orbitLits, Certificates.pairIndex]
  have hs := (List.all_eq_true.mp h.2) _ hmem
  simpa [Certificates.litSatisfied] using hs

lemma q6_orbit_compact {code : BitVec 15} {p : Fin 6 → Fin 6}
    (h : Certificates.Q6.orbitHolds code p = true)
    {i j : Fin 6} (hij : i ≠ j) :
    compactArc code 6 i.1 j.1 = Certificates.Q6.qArc (p i) (p j) := by
  have hparts := h
  rw [Certificates.Q6.orbitHolds, Bool.and_eq_true] at hparts
  have hp : Injective p := q6_injective_of_bool hparts.1
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hval : i.1 ≠ j.1 := by omega
    have hltv : i.1 < j.1 := hlt
    rw [compactArc]
    simp only [hval, hltv, if_false, if_true]
    exact q6_orbit_bit h hlt
  · exact (hij heq).elim
  · have hval : i.1 ≠ j.1 := by omega
    have hnlt : ¬ i.1 < j.1 := by omega
    rw [compactArc]
    simp only [hval, hnlt, if_false, q6_orbit_bit h hgt]
    have hpne : p i ≠ p j := fun hpij => hij (hp hpij)
    exact (q6_arc_reverse hpne).symm

lemma q7_orbit_compact {code : BitVec 21} {p : Fin 7 → Fin 7}
    (h : Certificates.Q7.orbitHolds code p = true)
    {i j : Fin 7} (hij : i ≠ j) :
    compactArc code 7 i.1 j.1 = Certificates.Q7.qArc (p i) (p j) := by
  have hparts := h
  rw [Certificates.Q7.orbitHolds, Bool.and_eq_true] at hparts
  have hp : Injective p := q7_injective_of_bool hparts.1
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hval : i.1 ≠ j.1 := by omega
    have hltv : i.1 < j.1 := hlt
    rw [compactArc]
    simp only [hval, hltv, if_false, if_true]
    exact q7_orbit_bit h hlt
  · exact (hij heq).elim
  · have hval : i.1 ≠ j.1 := by omega
    have hnlt : ¬ i.1 < j.1 := by omega
    rw [compactArc]
    simp only [hval, hnlt, if_false, q7_orbit_bit h hgt]
    have hpne : p i ≠ p j := fun hpij => hij (hp hpij)
    exact (q7_arc_reverse hpne).symm

def packCross (T : Tournament 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) : BitVec 42 :=
  BitVec.ofBoolListLE [
    T.arc (a 0) (b 0), T.arc (a 0) (b 1), T.arc (a 0) (b 2),
    T.arc (a 0) (b 3), T.arc (a 0) (b 4), T.arc (a 0) (b 5),
    T.arc (a 1) (b 0), T.arc (a 1) (b 1), T.arc (a 1) (b 2),
    T.arc (a 1) (b 3), T.arc (a 1) (b 4), T.arc (a 1) (b 5),
    T.arc (a 2) (b 0), T.arc (a 2) (b 1), T.arc (a 2) (b 2),
    T.arc (a 2) (b 3), T.arc (a 2) (b 4), T.arc (a 2) (b 5),
    T.arc (a 3) (b 0), T.arc (a 3) (b 1), T.arc (a 3) (b 2),
    T.arc (a 3) (b 3), T.arc (a 3) (b 4), T.arc (a 3) (b 5),
    T.arc (a 4) (b 0), T.arc (a 4) (b 1), T.arc (a 4) (b 2),
    T.arc (a 4) (b 3), T.arc (a 4) (b 4), T.arc (a 4) (b 5),
    T.arc (a 5) (b 0), T.arc (a 5) (b 1), T.arc (a 5) (b 2),
    T.arc (a 5) (b 3), T.arc (a 5) (b 4), T.arc (a 5) (b 5),
    T.arc (a 6) (b 0), T.arc (a 6) (b 1), T.arc (a 6) (b 2),
    T.arc (a 6) (b 3), T.arc (a 6) (b 4), T.arc (a 6) (b 5)]

lemma packCross_get (T : Tournament 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) (i : Fin 7) (j : Fin 6) :
    (packCross T a b).getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j) := by
  fin_cases i <;> fin_cases j <;>
    rw [packCross, BitVec.getLsbD_ofBoolListLE] <;>
    rfl

lemma order5_data (o : Certificates.Normalized.Order5)
    (h : o.data = true) :
    o.a < 14 ∧ o.b < 14 ∧ o.c < 14 ∧ o.d < 14 ∧ o.e < 14 ∧
    o.a ≠ o.b ∧ o.a ≠ o.c ∧ o.a ≠ o.d ∧ o.a ≠ o.e ∧
    o.b ≠ o.c ∧ o.b ≠ o.d ∧ o.b ≠ o.e ∧
    o.c ≠ o.d ∧ o.c ≠ o.e ∧ o.d ≠ o.e := by
  simp [Certificates.Normalized.Order5.data, Bool.and_eq_true] at h
  aesop

lemma order5_to_transitive (T : Tournament 14) (cross : BitVec 42)
    (g : Fin 14 → Fin 14) (hg : Injective g)
    (hpair : ∀ i j : Fin 14, i ≠ j →
      Certificates.Normalized.holdsPair cross (i.1, j.1) = true →
      T.arc (g i) (g j) = true)
    (o : Certificates.Normalized.Order5) (ho : o.holds cross = true) :
    HasTransitiveTournament T 5 := by
  rw [Certificates.Normalized.Order5.holds, Bool.and_eq_true] at ho
  obtain ⟨ha, hb, hc, hd, he, hab, hac, had, hae, hbc, hbd, hbe,
    hcd, hce, hde⟩ := order5_data o ho.1
  let a : Fin 14 := ⟨o.a, ha⟩
  let b : Fin 14 := ⟨o.b, hb⟩
  let c : Fin 14 := ⟨o.c, hc⟩
  let d : Fin 14 := ⟨o.d, hd⟩
  let e : Fin 14 := ⟨o.e, he⟩
  have hall := ho.2
  simp only [Certificates.Normalized.Order5.pairs, List.all_cons,
    List.all_nil, Bool.and_eq_true] at hall
  let u : Fin 5 → Fin 14 := ![g a, g b, g c, g d, g e]
  have gab : g a ≠ g b := fun h => hab (Fin.ext_iff.mp (hg h))
  have gac : g a ≠ g c := fun h => hac (Fin.ext_iff.mp (hg h))
  have gad : g a ≠ g d := fun h => had (Fin.ext_iff.mp (hg h))
  have gae : g a ≠ g e := fun h => hae (Fin.ext_iff.mp (hg h))
  have gbc : g b ≠ g c := fun h => hbc (Fin.ext_iff.mp (hg h))
  have gbd : g b ≠ g d := fun h => hbd (Fin.ext_iff.mp (hg h))
  have gbe : g b ≠ g e := fun h => hbe (Fin.ext_iff.mp (hg h))
  have gcd : g c ≠ g d := fun h => hcd (Fin.ext_iff.mp (hg h))
  have gce : g c ≠ g e := fun h => hce (Fin.ext_iff.mp (hg h))
  have gde : g d ≠ g e := fun h => hde (Fin.ext_iff.mp (hg h))
  have eab : T.arc (g a) (g b) = true := hpair a b (by exact fun h => hab (Fin.ext_iff.mp h)) hall.1
  have eac : T.arc (g a) (g c) = true := hpair a c (by exact fun h => hac (Fin.ext_iff.mp h)) hall.2.1
  have ead : T.arc (g a) (g d) = true := hpair a d (by exact fun h => had (Fin.ext_iff.mp h)) hall.2.2.1
  have eae : T.arc (g a) (g e) = true := hpair a e (by exact fun h => hae (Fin.ext_iff.mp h)) hall.2.2.2.1
  have ebc : T.arc (g b) (g c) = true := hpair b c (by exact fun h => hbc (Fin.ext_iff.mp h)) hall.2.2.2.2.1
  have ebd : T.arc (g b) (g d) = true := hpair b d (by exact fun h => hbd (Fin.ext_iff.mp h)) hall.2.2.2.2.2.1
  have ebe : T.arc (g b) (g e) = true := hpair b e (by exact fun h => hbe (Fin.ext_iff.mp h)) hall.2.2.2.2.2.2.1
  have ecd : T.arc (g c) (g d) = true := hpair c d (by exact fun h => hcd (Fin.ext_iff.mp h)) hall.2.2.2.2.2.2.2.1
  have ece : T.arc (g c) (g e) = true := hpair c e (by exact fun h => hce (Fin.ext_iff.mp h)) hall.2.2.2.2.2.2.2.2.1
  have ede : T.arc (g d) (g e) = true := hpair d e (by exact fun h => hde (Fin.ext_iff.mp h)) hall.2.2.2.2.2.2.2.2.2.1
  refine ⟨u, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [u]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [u]

def normalizedMap (v : Fin 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) : Fin 14 → Fin 14 := ![
  v, a 0, a 1, a 2, a 3, a 4, a 5, a 6,
  b 0, b 1, b 2, b 3, b 4, b 5]

def indexA (i : Fin 7) : Fin 14 := ⟨i.1 + 1, by omega⟩

def indexB (i : Fin 6) : Fin 14 := ⟨i.1 + 8, by omega⟩

lemma normalizedMap_zero (v : Fin 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) : normalizedMap v a b 0 = v := by
  rfl

lemma normalizedMap_indexA (v : Fin 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) (i : Fin 7) : normalizedMap v a b (indexA i) = a i := by
  fin_cases i <;> rfl

lemma normalizedMap_indexB (v : Fin 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) (i : Fin 6) : normalizedMap v a b (indexB i) = b i := by
  fin_cases i <;> rfl

lemma index_zero_or_A_or_B (i : Fin 14) :
    i = 0 ∨ (∃ r : Fin 7, i = indexA r) ∨ ∃ r : Fin 6, i = indexB r := by
  by_cases h0 : i.1 = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h7 : i.1 ≤ 7
  · right; left
    let r : Fin 7 := ⟨i.1 - 1, by omega⟩
    exact ⟨r, Fin.ext (by simp [indexA, r]; omega)⟩
  · right; right
    let r : Fin 6 := ⟨i.1 - 8, by omega⟩
    exact ⟨r, Fin.ext (by simp [indexB, r]; omega)⟩

lemma normalizedMap_injective (v : Fin 14) (a : Fin 7 → Fin 14)
    (b : Fin 6 → Fin 14) (ha : Injective a) (hb : Injective b)
    (hvane : ∀ i, v ≠ a i) (hbvne : ∀ i, b i ≠ v)
    (hab : ∀ i j, a i ≠ b j) : Injective (normalizedMap v a b) := by
  intro i j hij
  rcases index_zero_or_A_or_B i with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
    rcases index_zero_or_A_or_B j with rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rfl
  · have hij' := hij
    rw [normalizedMap_zero, normalizedMap_indexA] at hij'
    exact (hvane s hij').elim
  · have hij' := hij
    rw [normalizedMap_zero, normalizedMap_indexB] at hij'
    exact ((hbvne s).symm hij').elim
  · have hij' := hij
    rw [normalizedMap_indexA, normalizedMap_zero] at hij'
    exact ((hvane r) hij'.symm).elim
  · have hij' := hij
    rw [normalizedMap_indexA, normalizedMap_indexA] at hij'
    exact congrArg indexA (ha hij')
  · have hij' := hij
    rw [normalizedMap_indexA, normalizedMap_indexB] at hij'
    exact ((hab r s) hij').elim
  · have hij' := hij
    rw [normalizedMap_indexB, normalizedMap_zero] at hij'
    exact (hbvne r hij').elim
  · have hij' := hij
    rw [normalizedMap_indexB, normalizedMap_indexA] at hij'
    exact ((hab s r) hij'.symm).elim
  · have hij' := hij
    rw [normalizedMap_indexB, normalizedMap_indexB] at hij'
    exact congrArg indexB (hb hij')

lemma indexA_injective : Injective indexA := by
  intro i j h
  apply Fin.ext
  have := Fin.ext_iff.mp h
  simp [indexA] at this
  omega

lemma indexB_injective : Injective indexB := by
  intro i j h
  apply Fin.ext
  have := Fin.ext_iff.mp h
  simp [indexB] at this
  omega

lemma holdsPair_A_zero (cross : BitVec 42) (i : Fin 7) :
    Certificates.Normalized.holdsPair cross ((indexA i).1, 0) = false := by
  fin_cases i <;> rfl

lemma holdsPair_B_zero (cross : BitVec 42) (i : Fin 6) :
    Certificates.Normalized.holdsPair cross ((indexB i).1, 0) = true := by
  fin_cases i <;> rfl

lemma holdsPair_A_A (cross : BitVec 42) (i j : Fin 7) :
    Certificates.Normalized.holdsPair cross ((indexA i).1, (indexA j).1) =
      Certificates.Q7.qArc i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma holdsPair_B_B (cross : BitVec 42) (i j : Fin 6) :
    Certificates.Normalized.holdsPair cross ((indexB i).1, (indexB j).1) =
      Certificates.Q6.qArc i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma holdsPair_A_B (cross : BitVec 42) (i : Fin 7) (j : Fin 6) :
    Certificates.Normalized.holdsPair cross ((indexA i).1, (indexB j).1) =
      (cross.getLsbD (i.1 * 6 + j.1) == true) := by
  fin_cases i <;> fin_cases j <;> rfl

lemma holdsPair_B_A (cross : BitVec 42) (i : Fin 6) (j : Fin 7) :
    Certificates.Normalized.holdsPair cross ((indexB i).1, (indexA j).1) =
      (cross.getLsbD (j.1 * 6 + i.1) == false) := by
  fin_cases i <;> fin_cases j <;> rfl

lemma normalized_pair_zero (T : Tournament 14) (v : Fin 14)
    (a : Fin 7 → Fin 14) (b : Fin 6 → Fin 14)
    (cross : BitVec 42)
    (hva : ∀ i, T.arc v (a i) = true)
    (hbv : ∀ i, T.arc (b i) v = true)
    (harcA : ∀ i j : Fin 7, i ≠ j →
      T.arc (a i) (a j) = Certificates.Q7.qArc i j)
    (harcB : ∀ i j : Fin 6, i ≠ j →
      T.arc (b i) (b j) = Certificates.Q6.qArc i j)
    (hab : ∀ i j, a i ≠ b j)
    (hcross : ∀ i j,
      cross.getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j)) :
    ∀ j : Fin 14, (0 : Fin 14) ≠ j →
      Certificates.Normalized.holdsPair cross (0, j.1) = true →
      T.arc (normalizedMap v a b 0) (normalizedMap v a b j) = true := by
  have hba : ∀ i j, T.arc (b j) (a i) = !T.arc (a i) (b j) := by
    intro i j
    exact T.arc_reverse (hab i j).symm
  intro j hij hh
  fin_cases j <;> simp at hij
  all_goals
    simp_all [normalizedMap, Certificates.Normalized.holdsPair,
      Certificates.Normalized.crossLit?, Certificates.Normalized.fixedArc,
      Certificates.Normalized.inA, Certificates.Normalized.inB,
      Certificates.litSatisfied, Certificates.Q7.qArc, Certificates.Q6.qArc]

lemma normalized_pair_A (T : Tournament 14) (v : Fin 14)
    (a : Fin 7 → Fin 14) (b : Fin 6 → Fin 14)
    (cross : BitVec 42)
    (hva : ∀ i, T.arc v (a i) = true)
    (hbv : ∀ i, T.arc (b i) v = true)
    (harcA : ∀ i j : Fin 7, i ≠ j →
      T.arc (a i) (a j) = Certificates.Q7.qArc i j)
    (harcB : ∀ i j : Fin 6, i ≠ j →
      T.arc (b i) (b j) = Certificates.Q6.qArc i j)
    (hab : ∀ i j, a i ≠ b j)
    (hcross : ∀ i j,
      cross.getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j)) :
    ∀ i : Fin 7, ∀ j : Fin 14, indexA i ≠ j →
      Certificates.Normalized.holdsPair cross ((indexA i).1, j.1) = true →
      T.arc (normalizedMap v a b (indexA i)) (normalizedMap v a b j) = true := by
  intro i j hij hh
  rcases index_zero_or_A_or_B j with rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · change Certificates.Normalized.holdsPair cross ((indexA i).1, 0) = true at hh
    rw [holdsPair_A_zero] at hh
    contradiction
  · have his : i ≠ s := fun h => hij (congrArg indexA h)
    rw [normalizedMap_indexA, normalizedMap_indexA, harcA i s his]
    simpa [holdsPair_A_A] using hh
  · rw [normalizedMap_indexA, normalizedMap_indexB]
    have hbit : cross.getLsbD (i.1 * 6 + s.1) = true := by
      simpa [holdsPair_A_B] using hh
    exact (hcross i s) ▸ hbit

lemma normalized_pair_B (T : Tournament 14) (v : Fin 14)
    (a : Fin 7 → Fin 14) (b : Fin 6 → Fin 14)
    (cross : BitVec 42)
    (hva : ∀ i, T.arc v (a i) = true)
    (hbv : ∀ i, T.arc (b i) v = true)
    (harcA : ∀ i j : Fin 7, i ≠ j →
      T.arc (a i) (a j) = Certificates.Q7.qArc i j)
    (harcB : ∀ i j : Fin 6, i ≠ j →
      T.arc (b i) (b j) = Certificates.Q6.qArc i j)
    (hab : ∀ i j, a i ≠ b j)
    (hcross : ∀ i j,
      cross.getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j)) :
    ∀ i : Fin 6, ∀ j : Fin 14, indexB i ≠ j →
      Certificates.Normalized.holdsPair cross ((indexB i).1, j.1) = true →
      T.arc (normalizedMap v a b (indexB i)) (normalizedMap v a b j) = true := by
  intro i j hij hh
  rcases index_zero_or_A_or_B j with rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [normalizedMap_indexB, normalizedMap_zero]
    exact hbv i
  · rw [normalizedMap_indexB, normalizedMap_indexA]
    have hbit : cross.getLsbD (s.1 * 6 + i.1) = false := by
      simpa [holdsPair_B_A] using hh
    have hrev := T.arc_reverse (hab s i).symm
    rw [hrev, ← hcross s i, hbit]
    rfl
  · have his : i ≠ s := fun h => hij (congrArg indexB h)
    rw [normalizedMap_indexB, normalizedMap_indexB, harcB i s his]
    simpa [holdsPair_B_B] using hh

lemma normalized_pair_sound (T : Tournament 14) (v : Fin 14)
    (a : Fin 7 → Fin 14) (b : Fin 6 → Fin 14)
    (cross : BitVec 42)
    (hva : ∀ i, T.arc v (a i) = true)
    (hbv : ∀ i, T.arc (b i) v = true)
    (harcA : ∀ i j : Fin 7, i ≠ j →
      T.arc (a i) (a j) = Certificates.Q7.qArc i j)
    (harcB : ∀ i j : Fin 6, i ≠ j →
      T.arc (b i) (b j) = Certificates.Q6.qArc i j)
    (hab : ∀ i j, a i ≠ b j)
    (hcross : ∀ i j,
      cross.getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j)) :
    ∀ i j : Fin 14, i ≠ j →
      Certificates.Normalized.holdsPair cross (i.1, j.1) = true →
      T.arc (normalizedMap v a b i) (normalizedMap v a b j) = true := by
  intro i j hij hh
  rcases index_zero_or_A_or_B i with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact normalized_pair_zero T v a b cross hva hbv harcA harcB hab hcross j hij hh
  · exact normalized_pair_A T v a b cross hva hbv harcA harcB hab hcross r j hij hh
  · exact normalized_pair_B T v a b cross hva hbv harcA harcB hab hcross r j hij hh

lemma outSet_seven_impossible (T : Tournament 14)
    (hfree : ¬ HasTransitiveTournament T 5) (v : Fin 14)
    (houtcard : (outSet T v).card = 7) : False := by
  have hincard : (inSet T v).card = 6 := by
    have hsum := outSet_card_add_inSet_card T v
    omega
  let EA := Finset.orderIsoOfFin (outSet T v) houtcard
  let EB := Finset.orderIsoOfFin (inSet T v) hincard
  let a0 : Fin 7 → Fin 14 := fun i => (EA i).1
  let b0 : Fin 6 → Fin 14 := fun i => (EB i).1
  have ha0 : Injective a0 := by
    intro i j hij
    apply EA.injective
    exact Subtype.ext hij
  have hb0 : Injective b0 := by
    intro i j hij
    apply EB.injective
    exact Subtype.ext hij
  have ha0mem : ∀ i, a0 i ∈ outSet T v := fun i => (EA i).2
  have hb0mem : ∀ i, b0 i ∈ inSet T v := fun i => (EB i).2
  have hva0 : ∀ i, T.arc v (a0 i) = true := fun i => (outSet_mem (ha0mem i)).1
  have hva0ne : ∀ i, v ≠ a0 i := fun i => (outSet_mem (ha0mem i)).2
  have hb0v : ∀ i, T.arc (b0 i) v = true := fun i => (inSet_mem (hb0mem i)).1
  have hb0vne : ∀ i, b0 i ≠ v := fun i => (inSet_mem (hb0mem i)).2
  have hfreeA : ∀ o : Certificates.Order4,
      o.holds (pack7 T a0) 7 ≠ true := by
    intro o ho
    exact hfree (order4_prepend ha0 (pack7_get T a0) ho v hva0 hva0ne)
  have hfreeB : ∀ o : Certificates.Order4,
      o.holds (pack6 T b0) 6 ≠ true := by
    intro o ho
    exact hfree (order4_append hb0 (pack6_get T b0) ho v hb0v hb0vne)
  obtain ⟨pA, hpA⟩ := Certificates.Q7.classification (pack7 T a0) hfreeA
  obtain ⟨pB, hpB⟩ := Certificates.Q6.classification (pack6 T b0) hfreeB
  have hpAparts := hpA
  rw [Certificates.Q7.orbitHolds, Bool.and_eq_true] at hpAparts
  have hpBparts := hpB
  rw [Certificates.Q6.orbitHolds, Bool.and_eq_true] at hpBparts
  have hpAinj : Injective pA := q7_injective_of_bool hpAparts.1
  have hpBinj : Injective pB := q6_injective_of_bool hpBparts.1
  let PA : Fin 7 ≃ Fin 7 := Equiv.ofBijective pA hpAinj.bijective_of_finite
  let PB : Fin 6 ≃ Fin 6 := Equiv.ofBijective pB hpBinj.bijective_of_finite
  let a : Fin 7 → Fin 14 := fun i => a0 (PA.symm i)
  let b : Fin 6 → Fin 14 := fun i => b0 (PB.symm i)
  have ha : Injective a := ha0.comp PA.symm.injective
  have hb : Injective b := hb0.comp PB.symm.injective
  have hamem : ∀ i, a i ∈ outSet T v := fun i => ha0mem (PA.symm i)
  have hbmem : ∀ i, b i ∈ inSet T v := fun i => hb0mem (PB.symm i)
  have hva : ∀ i, T.arc v (a i) = true := fun i => (outSet_mem (hamem i)).1
  have hvane : ∀ i, v ≠ a i := fun i => (outSet_mem (hamem i)).2
  have hbv : ∀ i, T.arc (b i) v = true := fun i => (inSet_mem (hbmem i)).1
  have hbvne : ∀ i, b i ≠ v := fun i => (inSet_mem (hbmem i)).2
  have hab : ∀ i j, a i ≠ b j := by
    intro i j hij
    have haout := (outSet_mem (hamem i)).1
    have hbin := (Finset.mem_filter.mp (hbmem j)).2
    exact hbin (hij ▸ haout)
  have harcA : ∀ i j : Fin 7, i ≠ j →
      T.arc (a i) (a j) = Certificates.Q7.qArc i j := by
    intro i j hij
    have hpre : PA.symm i ≠ PA.symm j := fun h => hij (PA.symm.injective h)
    calc
      T.arc (a i) (a j) = compactArc (pack7 T a0) 7
          (PA.symm i).1 (PA.symm j).1 :=
        (compactArc_pack ha0 (pack7_get T a0) hpre).symm
      _ = Certificates.Q7.qArc (pA (PA.symm i)) (pA (PA.symm j)) :=
        q7_orbit_compact hpA hpre
      _ = Certificates.Q7.qArc i j := by
        change Certificates.Q7.qArc (PA (PA.symm i)) (PA (PA.symm j)) = _
        rw [PA.apply_symm_apply, PA.apply_symm_apply]
  have harcB : ∀ i j : Fin 6, i ≠ j →
      T.arc (b i) (b j) = Certificates.Q6.qArc i j := by
    intro i j hij
    have hpre : PB.symm i ≠ PB.symm j := fun h => hij (PB.symm.injective h)
    calc
      T.arc (b i) (b j) = compactArc (pack6 T b0) 6
          (PB.symm i).1 (PB.symm j).1 :=
        (compactArc_pack hb0 (pack6_get T b0) hpre).symm
      _ = Certificates.Q6.qArc (pB (PB.symm i)) (pB (PB.symm j)) :=
        q6_orbit_compact hpB hpre
      _ = Certificates.Q6.qArc i j := by
        change Certificates.Q6.qArc (PB (PB.symm i)) (PB (PB.symm j)) = _
        rw [PB.apply_symm_apply, PB.apply_symm_apply]
  let cross := packCross T a b
  have hcross : ∀ i j, cross.getLsbD (i.1 * 6 + j.1) = T.arc (a i) (b j) :=
    fun i j => packCross_get T a b i j
  let g := normalizedMap v a b
  have hg : Injective g := normalizedMap_injective v a b ha hb hvane hbvne hab
  have hpair : ∀ i j : Fin 14, i ≠ j →
      Certificates.Normalized.holdsPair cross (i.1, j.1) = true →
      T.arc (g i) (g j) = true :=
    normalized_pair_sound T v a b cross hva hbv harcA harcB hab hcross
  obtain ⟨o, ho⟩ := Certificates.Normalized.five_exists cross
  exact hfree (order5_to_transitive T cross g hg hpair o ho)

def st13 : Tournament 13 :=
  BitVec.ofNat 169 45680290137101156136957078565513855030502589038

def cyclicArc13 (i j : Fin 13) : Bool :=
  decide ((j.1 + 13 - i.1) % 13 = 1 ∨ (j.1 + 13 - i.1) % 13 = 2 ∨
    (j.1 + 13 - i.1) % 13 = 3 ∨ (j.1 + 13 - i.1) % 13 = 5 ∨
    (j.1 + 13 - i.1) % 13 = 6 ∨ (j.1 + 13 - i.1) % 13 = 9)

lemma st13_arc {i j : Fin 13} (hij : i ≠ j) :
    st13.arc i j = cyclicArc13 i j := by
  fin_cases i <;> fin_cases j <;> simp at hij <;> rfl

def neighborOffset (i : Fin 6) : Nat := ![1, 3, 6, 9, 2, 5] i

def st13Neighbor (v : Fin 13) (i : Fin 6) : Fin 13 :=
  ⟨(v.1 + neighborOffset i) % 13, Nat.mod_lt _ (by omega)⟩

def neighborIndex (v x : Fin 13) : Fin 6 :=
  let d := (x.1 + 13 - v.1) % 13
  if d = 1 then 0 else if d = 3 then 1 else if d = 6 then 2
  else if d = 9 then 3 else if d = 2 then 4 else 5

lemma st13_neighbor_index {v x : Fin 13} (h : st13.arc v x = true) :
    st13Neighbor v (neighborIndex v x) = x := by
  have hvx : v ≠ x := by
    intro hvx
    subst x
    simp [Tournament.arc_self] at h
  have hrot := st13_arc hvx
  rw [hrot] at h
  fin_cases v <;> fin_cases x <;>
    simp [cyclicArc13, neighborIndex, st13Neighbor, neighborOffset] at h ⊢

lemma st13Neighbor_injective (v : Fin 13) : Injective (st13Neighbor v) := by
  intro i j h
  fin_cases v <;> fin_cases i <;> fin_cases j <;>
    simp [st13Neighbor, neighborOffset] at h ⊢

lemma st13_neighbor_arc (v : Fin 13) (i j : Fin 6) :
    st13.arc (st13Neighbor v i) (st13Neighbor v j) = Certificates.Q6.qArc i j := by
  by_cases hij : i = j
  · subst j
    simp [Tournament.arc_self, Certificates.Q6.qArc]
  · rw [st13_arc (fun h => hij (st13Neighbor_injective v h))]
    fin_cases v <;> fin_cases i <;> fin_cases j <;>
      simp [cyclicArc13, st13Neighbor, neighborOffset, Certificates.Q6.qArc]

lemma q6_has_no_transitive_four :
    ¬ ∃ a b c d : Fin 6,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      Certificates.Q6.qArc a b = true ∧ Certificates.Q6.qArc a c = true ∧
      Certificates.Q6.qArc a d = true ∧ Certificates.Q6.qArc b c = true ∧
      Certificates.Q6.qArc b d = true ∧ Certificates.Q6.qArc c d = true := by
  decide

lemma st13_has_no_transitive_five : ¬ HasTransitiveTournament st13 5 := by
  rintro ⟨u, hu, harc⟩
  let a := neighborIndex (u 0) (u 1)
  let b := neighborIndex (u 0) (u 2)
  let c := neighborIndex (u 0) (u 3)
  let d := neighborIndex (u 0) (u 4)
  have ha : st13Neighbor (u 0) a = u 1 := st13_neighbor_index (harc 0 1 (by decide))
  have hb : st13Neighbor (u 0) b = u 2 := st13_neighbor_index (harc 0 2 (by decide))
  have hc : st13Neighbor (u 0) c = u 3 := st13_neighbor_index (harc 0 3 (by decide))
  have hd : st13Neighbor (u 0) d = u 4 := st13_neighbor_index (harc 0 4 (by decide))
  apply q6_has_no_transitive_four
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact (by decide : (1 : Fin 5) ≠ 2) (hu (ha ▸ hb ▸ congrArg (st13Neighbor (u 0)) h))
  · intro h; exact (by decide : (1 : Fin 5) ≠ 3) (hu (ha ▸ hc ▸ congrArg (st13Neighbor (u 0)) h))
  · intro h; exact (by decide : (1 : Fin 5) ≠ 4) (hu (ha ▸ hd ▸ congrArg (st13Neighbor (u 0)) h))
  · intro h; exact (by decide : (2 : Fin 5) ≠ 3) (hu (hb ▸ hc ▸ congrArg (st13Neighbor (u 0)) h))
  · intro h; exact (by decide : (2 : Fin 5) ≠ 4) (hu (hb ▸ hd ▸ congrArg (st13Neighbor (u 0)) h))
  · intro h; exact (by decide : (3 : Fin 5) ≠ 4) (hu (hc ▸ hd ▸ congrArg (st13Neighbor (u 0)) h))
  · rw [← st13_neighbor_arc (u 0) a b, ha, hb]
    exact harc 1 2 (by decide)
  · rw [← st13_neighbor_arc (u 0) a c, ha, hc]
    exact harc 1 3 (by decide)
  · rw [← st13_neighbor_arc (u 0) a d, ha, hd]
    exact harc 1 4 (by decide)
  · rw [← st13_neighbor_arc (u 0) b c, hb, hc]
    exact harc 2 3 (by decide)
  · rw [← st13_neighbor_arc (u 0) b d, hb, hd]
    exact harc 2 4 (by decide)
  · rw [← st13_neighbor_arc (u 0) c d, hc, hd]
    exact harc 3 4 (by decide)

def extremal14 : Tournament 14 :=
  BitVec.ofNat 196 3065271710028222795110899890727524075270911729065213950

def lift13 (i : Fin 13) : Fin 14 := ⟨i.1 + 1, by omega⟩

def drop14 (i : Fin 14) : Fin 13 := ⟨i.1 - 1, by omega⟩

lemma lift13_drop14 {i : Fin 14} (hi : i ≠ 0) : lift13 (drop14 i) = i := by
  apply Fin.ext
  simp [lift13, drop14]
  have : i.1 ≠ 0 := by
    intro h
    exact hi (Fin.ext h)
  omega

lemma extremal14_arc_lift13 (i j : Fin 13) :
    extremal14.arc (lift13 i) (lift13 j) = st13.arc i j := by
  fin_cases i <;> fin_cases j <;> rfl

lemma extremal14_source (i : Fin 13) :
    extremal14.arc 0 (lift13 i) = true := by
  fin_cases i <;> rfl

lemma extremal14_to_source {i : Fin 14} (hi : i ≠ 0) :
    extremal14.arc i 0 = false := by
  have hsource := extremal14_source (drop14 i)
  rw [lift13_drop14 hi] at hsource
  have hrev := extremal14.arc_reverse hi.symm
  rw [hsource] at hrev
  cases hbit : extremal14.arc i 0 with
  | false => rfl
  | true => simpa only [hbit, Bool.not_true] using hrev

lemma st13_transitive_of_extremal_nonzero
    (u : Fin 5 → Fin 14) (hu : Injective u)
    (harc : ∀ i j : Fin 5, i < j → extremal14.arc (u i) (u j) = true)
    (hnz : ∀ i, u i ≠ 0) : HasTransitiveTournament st13 5 := by
  let w : Fin 5 → Fin 13 := fun i => drop14 (u i)
  have hw : Injective w := by
    intro i j hij
    apply hu
    rw [← lift13_drop14 (hnz i), ← lift13_drop14 (hnz j)]
    exact congrArg lift13 hij
  refine ⟨w, hw, ?_⟩
  intro i j hij
  rw [← extremal14_arc_lift13 (w i) (w j)]
  simpa [w, lift13_drop14 (hnz i), lift13_drop14 (hnz j)] using harc i j hij

lemma extremal14_has_no_transitive_six :
    ¬ HasTransitiveTournament extremal14 6 := by
  rintro ⟨u, hu, harc⟩
  apply st13_has_no_transitive_five
  by_cases hzero : u 0 = 0
  · let next : Fin 5 → Fin 6 := fun i => ⟨i.1 + 1, by omega⟩
    let w : Fin 5 → Fin 14 := fun i => u (next i)
    have hw : Injective w := hu.comp (by
      intro i j h
      apply Fin.ext
      have := Fin.ext_iff.mp h
      simp [next] at this
      omega)
    have hnz : ∀ i, w i ≠ 0 := by
      intro i hi
      have hnext : (0 : Fin 6) ≠ next i := by
        intro h
        have := Fin.ext_iff.mp h
        simp [next] at this
      exact hnext (hu (hzero.trans hi.symm))
    apply st13_transitive_of_extremal_nonzero w hw
    · intro i j hij
      exact harc (next i) (next j) (by simp [next]; omega)
    · exact hnz
  · let first : Fin 5 → Fin 6 := fun i => ⟨i.1, by omega⟩
    let w : Fin 5 → Fin 14 := fun i => u (first i)
    have hw : Injective w := hu.comp (by
      intro i j h
      apply Fin.ext
      simpa [first] using Fin.ext_iff.mp h)
    have hnz6 : ∀ i : Fin 6, u i ≠ 0 := by
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        exact hzero hi
      · have hlt : (0 : Fin 6) < i := by omega
        have hedge := harc 0 i hlt
        rw [hi, extremal14_to_source hzero] at hedge
        contradiction
    apply st13_transitive_of_extremal_nonzero w hw
    · intro i j hij
      exact harc (first i) (first j) (by simpa [first] using hij)
    · exact fun i => hnz6 (first i)

def reverseTournament (T : Tournament 14) : Tournament 14 := ~~~T

lemma reverseTournament_arc (T : Tournament 14) {i j : Fin 14} (hij : i ≠ j) :
    (reverseTournament T).arc i j = T.arc j i := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hidx : i.1 * 14 + j.1 < 14 * 14 := by omega
    have hnrev : ¬ j < i := not_lt_of_ge hlt.le
    simp [reverseTournament, Tournament.arc, hij, hij.symm, hlt, hnrev,
      BitVec.getLsbD_not, hidx]
  · exact (hij heq).elim
  · have hidx : j.1 * 14 + i.1 < 14 * 14 := by omega
    have hnlt : ¬ i < j := not_lt_of_ge hgt.le
    simp [reverseTournament, Tournament.arc, hij, hij.symm, hgt, hnlt,
      BitVec.getLsbD_not, hidx]

lemma transitive_of_reverse_transitive (T : Tournament 14) :
    HasTransitiveTournament (reverseTournament T) 5 →
      HasTransitiveTournament T 5 := by
  rintro ⟨v, hv, harc⟩
  let w : Fin 5 → Fin 14 := fun i => v i.rev
  refine ⟨w, hv.comp Fin.rev_injective, ?_⟩
  intro i j hij
  have hrev : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
  have h := harc j.rev i.rev hrev
  have hvne : v j.rev ≠ v i.rev := fun hvji => (ne_of_lt hrev) (hv hvji)
  rw [reverseTournament_arc T hvne] at h
  simpa [w] using h

lemma reverse_outSet_eq_inSet (T : Tournament 14) (v : Fin 14) :
    outSet (reverseTournament T) v = inSet T v := by
  ext x
  by_cases hx : x = v
  · subst x
    simp [outSet, inSet]
  · have hrev := reverseTournament_arc T (Ne.symm hx)
    have hswap := T.arc_reverse (Ne.symm hx)
    simp only [outSet, inSet, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true]
    rw [hrev, hswap]
    cases hbit : T.arc v x <;> simp [hbit, hx]

/-- Reid--Parker's directed Ramsey theorem R_T(5) = 14, in its upper-bound form. -/
theorem directed_ramsey_five_fourteen : Guaranteed 14 5 := by
  refine ⟨by omega, ?_⟩
  intro T
  by_contra hfree
  let v : Fin 14 := 0
  have hout := outSet_card_le_seven T hfree v
  have hin := inSet_card_le_seven T hfree v
  have hsum := outSet_card_add_inSet_card T v
  have hcases : (outSet T v).card = 7 ∨ (inSet T v).card = 7 := by omega
  rcases hcases with houtcard | hincard
  · exact outSet_seven_impossible T hfree v houtcard
  · let R := reverseTournament T
    have hfreeR : ¬ HasTransitiveTournament R 5 := by
      intro hR
      exact hfree (transitive_of_reverse_transitive T hR)
    have houtR : (outSet R v).card = 7 := by
      rw [show R = reverseTournament T from rfl, reverse_outSet_eq_inSet]
      exact hincard
    exact outSet_seven_impossible R hfreeR v houtR

lemma hasTransitiveTournament_mono {n k l : Nat} {T : Tournament n}
    (hlk : l ≤ k) (h : HasTransitiveTournament T k) :
    HasTransitiveTournament T l := by
  obtain ⟨v, hv, harc⟩ := h
  let e : Fin l → Fin k := Fin.castLE hlk
  refine ⟨v ∘ e, hv.comp (Fin.castLE_injective hlk), ?_⟩
  intro i j hij
  apply harc (e i) (e j)
  simpa [e] using hij

lemma guaranteed_mono {n k l : Nat} (hlk : l ≤ k) (h : Guaranteed n k) :
    Guaranteed n l := by
  refine ⟨hlk.trans h.1, ?_⟩
  intro T
  exact hasTransitiveTournament_mono hlk (h.2 T)

lemma five_le_f_fourteen : 5 ≤ f 14 := by
  exact Nat.le_findGreatest (by omega) directed_ramsey_five_fourteen

/-- The exact Reid--Parker value at the first counterexample. -/
theorem f_fourteen_eq_five : f 14 = 5 := by
  apply Nat.le_antisymm
  · by_contra h
    have hsix : 6 ≤ f 14 := by omega
    have hgreatest : Guaranteed 14 (f 14) :=
      Nat.findGreatest_spec (by omega) directed_ramsey_five_fourteen
    have hguaranteed6 := guaranteed_mono hsix hgreatest
    exact extremal14_has_no_transitive_six (hguaranteed6.2 extremal14)
  · exact five_le_f_fourteen

/-- Erdős Problem 1216 has a negative answer (already at n = 14). -/
theorem not_erdos_1216 :
    ¬ (∀ n, 1 ≤ n → f n = Nat.log2 n + 1) := by
  intro hformula
  have heq := hformula 14 (by omega)
  have hlog : Nat.log2 14 + 1 = 4 := by decide
  rw [f_fourteen_eq_five, hlog] at heq
  contradiction


end

end Erdos1216

alias _root_.Erdos1216.erdos_1216 := _root_.Erdos1216.not_erdos_1216
