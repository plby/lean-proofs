/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Greedy bounded generators

Section 6.2 of the short design-existence proof chooses modular generators
greedily.  A candidate is added only if its vector is not already generated
and none of its lower faces is saturated.  The argument is independent of
the ambient group: it uses only monotonicity of the span predicate.

This file proves that finite greedy lemma once, in an abstract form.  The
later absorber specialization takes candidates to be `q`-cliques, counters
to be `(r-1)`-faces, and `Span` to be additive subgroup membership for the
modular clique-boundary vectors.
-/

namespace Erdos722.Generators

open Finset

noncomputable section

variable {Q C X : Type*} [DecidableEq Q]

/-- Number of selected candidates incident with one counter. -/
def counterLoad (inc : C → Q → Prop) [DecidableRel inc]
    (selected : Finset Q) (c : C) : ℕ :=
  (selected.filter (inc c)).card

/-- A candidate is saturated when it uses a counter already at its cap. -/
def IsSaturated (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (q : Q) : Prop :=
  ∃ c, inc c q ∧ cap ≤ counterLoad inc selected c

theorem counterLoad_mono
    (inc : C → Q → Prop) [DecidableRel inc]
    {A B : Finset Q} (hAB : A ⊆ B) (c : C) :
    counterLoad inc A c ≤ counterLoad inc B c := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

theorem IsSaturated.mono
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) {A B : Finset Q} (hAB : A ⊆ B) {q : Q}
    (h : IsSaturated inc cap A q) : IsSaturated inc cap B q := by
  obtain ⟨c, hcq, hc⟩ := h
  exact ⟨c, hcq, hc.trans (counterLoad_mono inc hAB c)⟩

/-- Double-counting selected-candidate/counter incidences bounds the number
of saturated counters. -/
theorem card_saturatedCounters_mul_le
    {C : Type*} [DecidableEq C]
    (inc : C → Q → Prop) [DecidableRel inc]
    (counters : Finset C) (selected : Finset Q) (cap M : ℕ)
    (hincident : ∀ q ∈ selected,
      (counters.filter fun c ↦ inc c q).card ≤ M) :
    cap * (counters.filter fun c ↦
      cap ≤ counterLoad inc selected c).card ≤ selected.card * M := by
  classical
  let saturated := counters.filter fun c ↦
    cap ≤ counterLoad inc selected c
  have hsatSub : saturated ⊆ counters := Finset.filter_subset _ _
  calc
    cap * saturated.card = ∑ c ∈ saturated, cap := by
      simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ saturated, counterLoad inc selected c := by
      apply Finset.sum_le_sum
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c ∈ counters, counterLoad inc selected c :=
      Finset.sum_le_sum_of_subset hsatSub
    _ = ∑ q ∈ selected, (counters.filter fun c ↦ inc c q).card := by
      simp only [counterLoad, Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _q ∈ selected, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact hincident q hq
    _ = selected.card * M := by simp

/-- One step of the bounded-generator algorithm.  The vector map and span
predicate are parameters, so this definition is usable for additive spans,
module spans, or any other monotone closure operation. -/
noncomputable def greedyStep (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (q : Q) : Finset Q := by
  classical
  exact if Span selected (vec q) ∨ IsSaturated inc cap selected q then
      selected
    else
      insert q selected

/-- Process a list of candidates from left to right. -/
def greedyRunFrom (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) : Finset Q → List Q → Finset Q
  | selected, [] => selected
  | selected, q :: qs =>
      greedyRunFrom vec Span inc cap
        (greedyStep vec Span inc cap selected q) qs

theorem subset_greedyStep
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (q : Q) :
    selected ⊆ greedyStep vec Span inc cap selected q := by
  classical
  unfold greedyStep
  split <;> simp

theorem subset_greedyRunFrom
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (qs : List Q) :
    selected ⊆ greedyRunFrom vec Span inc cap selected qs := by
  classical
  induction qs generalizing selected with
  | nil => exact Finset.Subset.rfl
  | cons q qs ih =>
      exact (subset_greedyStep vec Span inc cap selected q).trans
        (ih (greedyStep vec Span inc cap selected q))

theorem greedyStep_subset_insert
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (q : Q) :
    greedyStep vec Span inc cap selected q ⊆ insert q selected := by
  classical
  unfold greedyStep
  split <;> simp

theorem greedyRunFrom_subset_append
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (qs : List Q) :
    greedyRunFrom vec Span inc cap selected qs ⊆
      selected ∪ qs.toFinset := by
  classical
  induction qs generalizing selected with
  | nil => simp [greedyRunFrom]
  | cons q qs ih =>
      rw [greedyRunFrom]
      intro x hx
      have hx' := ih (greedyStep vec Span inc cap selected q) hx
      have hstep := greedyStep_subset_insert vec Span inc cap selected q
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at hx' ⊢
      rcases hx' with hxStep | hxTail
      · have := hstep hxStep
        simp only [Finset.mem_insert] at this
        exact this.elim (fun h ↦ Or.inr (Or.inl h)) (fun h ↦ Or.inl h)
      · exact Or.inr (Or.inr hxTail)

private theorem counterLoad_insert_le
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) {selected : Finset Q} {q : Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap)
    (hnotSat : ¬ IsSaturated inc cap selected q) :
    ∀ c, counterLoad inc (insert q selected) c ≤ cap := by
  classical
  intro c
  by_cases hcq : inc c q
  · have hlt : counterLoad inc selected c < cap := by
      by_contra hnot
      have hcap : cap ≤ counterLoad inc selected c := Nat.le_of_not_gt hnot
      exact hnotSat ⟨c, hcq, hcap⟩
    by_cases hqsel : q ∈ selected
    · rw [Finset.insert_eq_of_mem hqsel]
      exact hloads c
    · rw [counterLoad, Finset.filter_insert, if_pos hcq,
        Finset.card_insert_of_notMem]
      · simpa [counterLoad] using hlt
      · simpa [Finset.mem_filter, hqsel]
  · have : insert q selected = selected ∪ {q} := by ext; simp [or_comm]
    rw [counterLoad, Finset.filter_insert, if_neg hcq]
    exact hloads c

theorem greedyStep_load_le
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) {selected : Finset Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap) (q : Q) :
    ∀ c, counterLoad inc (greedyStep vec Span inc cap selected q) c ≤ cap := by
  classical
  unfold greedyStep
  split
  · exact hloads
  · rename_i h
    push_neg at h
    exact counterLoad_insert_le inc cap hloads h.2

theorem greedyRunFrom_load_le
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) {selected : Finset Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap)
    (qs : List Q) :
    ∀ c, counterLoad inc (greedyRunFrom vec Span inc cap selected qs) c ≤ cap := by
  classical
  induction qs generalizing selected with
  | nil => simpa [greedyRunFrom] using hloads
  | cons q qs ih =>
      rw [greedyRunFrom]
      exact ih (greedyStep_load_le vec Span inc cap hloads q)

theorem greedyStep_resolves
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ)
    (hself : ∀ (selected : Finset Q) (q : Q), q ∈ selected →
      Span selected (vec q))
    (selected : Finset Q) (q : Q) :
    Span (greedyStep vec Span inc cap selected q) (vec q) ∨
      IsSaturated inc cap (greedyStep vec Span inc cap selected q) q := by
  classical
  unfold greedyStep
  split
  · assumption
  · left
    apply hself
    simp

/-- Abstract bounded-generator lemma.  Every processed candidate is either
in the final span or saturated, while every counter remains below the cap.
No algebraic fact beyond span monotonicity and membership of generators is
used. -/
theorem exists_bounded_generators_list
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ)
    (hspanMono : ∀ {A B : Finset Q} {x : X}, A ⊆ B →
      Span A x → Span B x)
    (hself : ∀ (selected : Finset Q) (q : Q), q ∈ selected →
      Span selected (vec q))
    (initial : Finset Q) (hloads : ∀ c, counterLoad inc initial c ≤ cap)
    (qs : List Q) :
    let selected := greedyRunFrom vec Span inc cap initial qs
    (∀ c, counterLoad inc selected c ≤ cap) ∧
      ∀ q ∈ qs,
        Span selected (vec q) ∨ IsSaturated inc cap selected q := by
  classical
  dsimp only
  constructor
  · exact greedyRunFrom_load_le vec Span inc cap hloads qs
  · induction qs generalizing initial with
    | nil => simp
    | cons q qs ih =>
        let next := greedyStep vec Span inc cap initial q
        let final := greedyRunFrom vec Span inc cap next qs
        have hnextFinal : next ⊆ final :=
          subset_greedyRunFrom vec Span inc cap next qs
        have hqNext := greedyStep_resolves vec Span inc cap hself initial q
        have hqFinal : Span final (vec q) ∨ IsSaturated inc cap final q := by
          rcases hqNext with hspan | hsat
          · exact Or.inl (hspanMono hnextFinal hspan)
          · exact Or.inr (hsat.mono inc cap hnextFinal)
        have hnextLoads := greedyStep_load_le vec Span inc cap hloads q
        have htail := ih next hnextLoads
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa [next, final, greedyRunFrom] using hqFinal
        · simpa [next, final, greedyRunFrom] using htail x hx

/-- Finset form used by the absorber. -/
theorem exists_bounded_generators
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ)
    (hspanMono : ∀ {A B : Finset Q} {x : X}, A ⊆ B →
      Span A x → Span B x)
    (hself : ∀ (selected : Finset Q) (q : Q), q ∈ selected →
      Span selected (vec q))
    (candidates : Finset Q) :
    ∃ selected : Finset Q,
      selected ⊆ candidates ∧
      (∀ c, counterLoad inc selected c ≤ cap) ∧
      ∀ q ∈ candidates,
        Span selected (vec q) ∨ IsSaturated inc cap selected q := by
  classical
  let selected := greedyRunFrom vec Span inc cap ∅ candidates.toList
  refine ⟨selected, ?_, ?_, ?_⟩
  · have h := greedyRunFrom_subset_append vec Span inc cap
      (∅ : Finset Q) candidates.toList
    simpa [selected] using h
  · exact (exists_bounded_generators_list vec Span inc cap hspanMono hself
      ∅ (by simp [counterLoad]) candidates.toList).1
  · intro q hq
    have hmem : q ∈ candidates.toList := by simpa using hq
    exact (exists_bounded_generators_list vec Span inc cap hspanMono hself
      ∅ (by simp [counterLoad]) candidates.toList).2 q hmem

/-! ## Length of a strictly growing finite additive span -/

variable {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]

def InAdditiveSpan (vec : Q → A) (selected : Finset Q) (x : A) : Prop :=
  x ∈ AddSubgroup.closure (vec '' (↑selected : Set Q))

theorem InAdditiveSpan.mono (vec : Q → A)
    {S T : Finset Q} (hST : S ⊆ T) {x : A}
    (hx : InAdditiveSpan vec S x) : InAdditiveSpan vec T x := by
  apply AddSubgroup.closure_mono _ hx
  rintro y ⟨q, hq, rfl⟩
  exact ⟨q, hST hq, rfl⟩

theorem vec_mem_additiveSpan (vec : Q → A) (selected : Finset Q)
    {q : Q} (hq : q ∈ selected) : InAdditiveSpan vec selected (vec q) := by
  exact AddSubgroup.subset_closure ⟨q, hq, rfl⟩

private theorem double_card_le_of_addSubgroup_lt
    (H K : AddSubgroup A) (hHK : H ≤ K) {x : A}
    (hxK : x ∈ K) (hxH : x ∉ H) :
    2 * Nat.card H ≤ Nat.card K := by
  classical
  let f : H ⊕ H ↪ K :=
    { toFun := fun z ↦ match z with
        | Sum.inl h => ⟨h.1, hHK h.2⟩
        | Sum.inr h => ⟨x + h.1, K.add_mem hxK (hHK h.2)⟩
      inj' := by
        intro a b hab
        rcases a with a | a <;> rcases b with b | b
        · simp only [Sum.inl.injEq]
          dsimp at hab
          apply Subtype.ext
          exact congrArg (fun z : K ↦ (z.1 : A)) hab
        · exfalso
          dsimp at hab
          apply hxH
          have heq : x = a.1 - b.1 := by
            apply (eq_sub_iff_add_eq).2
            exact (congrArg Subtype.val hab).symm
          rw [heq]
          exact H.sub_mem a.2 b.2
        · exfalso
          dsimp at hab
          apply hxH
          have heq : x = b.1 - a.1 := by
            apply (eq_sub_iff_add_eq).2
            exact congrArg Subtype.val hab
          rw [heq]
          exact H.sub_mem b.2 a.2
        · simp only [Sum.inr.injEq]
          dsimp at hab
          apply Subtype.ext
          exact add_left_cancel (congrArg Subtype.val hab) }
  have hcard := Nat.card_le_card_of_injective f f.injective
  rw [Nat.card_sum] at hcard
  omega

private theorem double_spanCard_le_insert
    (vec : Q → A) (selected : Finset Q) (q : Q)
    (hnot : ¬ InAdditiveSpan vec selected (vec q)) :
    2 * Nat.card
        (AddSubgroup.closure (vec '' (↑selected : Set Q))) ≤
      Nat.card
        (AddSubgroup.closure (vec '' (↑(insert q selected) : Set Q))) := by
  let H := AddSubgroup.closure (vec '' (↑selected : Set Q))
  let K := AddSubgroup.closure (vec '' (↑(insert q selected) : Set Q))
  apply double_card_le_of_addSubgroup_lt H K
  · apply AddSubgroup.closure_mono
    rintro y ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_insert_of_mem hj, rfl⟩
  · apply AddSubgroup.subset_closure
    exact ⟨q, by simp, rfl⟩
  · exact hnot

/-- Along the greedy run, every genuinely added generator at least doubles
the cardinality of the generated subgroup. -/
theorem two_pow_card_greedyRunFrom_le_spanCard
    (vec : Q → A) (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (selected : Finset Q) (qs : List Q)
    (hstart : 2 ^ selected.card ≤
      Nat.card (AddSubgroup.closure
        (vec '' (↑selected : Set Q)))) :
    2 ^ (greedyRunFrom vec (InAdditiveSpan vec) inc cap selected qs).card ≤
      Nat.card (AddSubgroup.closure
        (vec '' (↑(greedyRunFrom vec (InAdditiveSpan vec) inc cap
          selected qs) : Set Q))) := by
  classical
  induction qs generalizing selected with
  | nil => simpa [greedyRunFrom] using hstart
  | cons q qs ih =>
      let next := greedyStep vec (InAdditiveSpan vec) inc cap selected q
      have hnext : 2 ^ next.card ≤
          Nat.card (AddSubgroup.closure
            (vec '' (↑next : Set Q))) := by
        unfold next greedyStep
        split
        · exact hstart
        · rename_i h
          push Not at h
          have hqnot : q ∉ selected := by
            intro hq
            exact h.1 (vec_mem_additiveSpan vec selected hq)
          rw [Finset.card_insert_of_notMem hqnot, pow_succ]
          simpa [Nat.mul_comm] using
            ((Nat.mul_le_mul_left 2 hstart).trans
              (double_spanCard_le_insert vec selected q h.1))
      simpa [greedyRunFrom, next] using ih next hnext

theorem two_pow_card_greedyRun_le_groupCard
    (vec : Q → A) (inc : C → Q → Prop) [DecidableRel inc]
    (cap : ℕ) (qs : List Q) :
    2 ^ (greedyRunFrom vec (InAdditiveSpan vec) inc cap ∅ qs).card ≤
      Nat.card A := by
  classical
  have hstart : 2 ^ (∅ : Finset Q).card ≤
      Nat.card (AddSubgroup.closure
        (vec '' (↑(∅ : Finset Q) : Set Q))) := by
    simp
  have hspan := two_pow_card_greedyRunFrom_le_spanCard
    vec inc cap ∅ qs hstart
  exact hspan.trans
    (Nat.card_le_card_of_injective
      (fun x : AddSubgroup.closure
        (vec '' (↑(greedyRunFrom vec (InAdditiveSpan vec) inc cap ∅ qs) :
          Set Q)) ↦ (x.1 : A))
      (fun _ _ h ↦ Subtype.ext h))

private theorem nat_le_two_pow (m : ℕ) : m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      by_cases hm : m = 0
      · subst m
        norm_num
      · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        omega

private theorem card_le_mul_of_two_pow_le_pow
    {s N m : ℕ} (hN : 0 < N) (h : 2 ^ s ≤ N ^ m) :
    s ≤ N * m := by
  have hbase : N ≤ 2 ^ N := nat_le_two_pow N
  have hupper : N ^ m ≤ 2 ^ (N * m) := by
    calc
      N ^ m ≤ (2 ^ N) ^ m := Nat.pow_le_pow_left hbase m
      _ = 2 ^ (N * m) := by rw [← pow_mul]
  by_contra hnot
  have hlt : N * m < s := Nat.lt_of_not_ge hnot
  have hp : 2 ^ (N * m) < 2 ^ s := Nat.pow_lt_pow_right (by omega) hlt
  omega

/-! ## Modular clique-boundary specialization -/

/-- The incidence vector of the complete `r`-graph on `Q`, reduced modulo
`N`.  Coordinates range over all finite vertex sets; off the `r`-uniform
layer the value is zero. -/
def modCliqueBoundary (N n r : ℕ) (Q : Finset (Fin n)) :
    Finset (Fin n) → ZMod N :=
  fun e ↦ if e.card = r ∧ e ⊆ Q then 1 else 0

/-- The same modular boundary restricted to a prescribed sparse edge set.
This restriction is what makes the subgroup-chain bound proportional to the
number of edges of the sparse host rather than to all subsets of `[n]`. -/
def modCliqueBoundaryOn (N r : ℕ) {n : ℕ}
    (K : Finset (Finset (Fin n))) (Q : Finset (Fin n)) :
    ↑K → ZMod N :=
  fun e ↦ if e.1.card = r ∧ e.1 ⊆ Q then 1 else 0

def InRestrictedModularSpan (N r : ℕ) {n : ℕ}
    (K : Finset (Finset (Fin n)))
    (selected : Finset (Finset (Fin n))) (x : ↑K → ZMod N) : Prop :=
  InAdditiveSpan (modCliqueBoundaryOn N r K) selected x

/-- Membership in the additive subgroup generated by the modular boundary
vectors of a selected clique family. -/
def InModularSpan (N n r : ℕ) (selected : Finset (Finset (Fin n)))
    (x : Finset (Fin n) → ZMod N) : Prop :=
  x ∈ AddSubgroup.closure
    (modCliqueBoundary N n r '' (↑selected : Set (Finset (Fin n))))

theorem InModularSpan.mono
    {N n r : ℕ} {A B : Finset (Finset (Fin n))}
    (hAB : A ⊆ B) {x : Finset (Fin n) → ZMod N}
    (hx : InModularSpan N n r A x) : InModularSpan N n r B x := by
  apply AddSubgroup.closure_mono _ hx
  rintro y ⟨Q, hQA, rfl⟩
  exact ⟨Q, hAB hQA, rfl⟩

theorem modCliqueBoundary_mem_span
    (N n r : ℕ) (selected : Finset (Finset (Fin n)))
    {Q : Finset (Fin n)} (hQ : Q ∈ selected) :
    InModularSpan N n r selected (modCliqueBoundary N n r Q) := by
  apply AddSubgroup.subset_closure
  exact ⟨Q, hQ, rfl⟩

/-- The exact greedy-generator output used in the integral absorber.  Each
lower face is used by at most `cap` selected cliques.  Every candidate not
generated by their modular boundaries contains a saturated lower face. -/
theorem exists_bounded_modular_clique_generators
    (N n r cap : ℕ) (candidates : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ candidates ∧
      (∀ f : Finset (Fin n),
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ cap) ∧
      ∀ Q ∈ candidates,
        InModularSpan N n r selected (modCliqueBoundary N n r Q) ∨
          ∃ f : Finset (Fin n), f ⊆ Q ∧
            cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  classical
  simpa only [IsSaturated] using
    (exists_bounded_generators
      (modCliqueBoundary N n r)
      (InModularSpan N n r)
      (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
      cap
      (fun hAB hx ↦ hx.mono hAB)
      (fun selected Q hQ ↦
        modCliqueBoundary_mem_span N n r selected hQ)
      candidates)

/-- Quantitative form of the modular greedy construction.  Since every
actual insertion strictly enlarges a subgroup of `(K → ZMod N)`, there
are at most `N * |K|` selected generators.  This is the finite chain-length
estimate used in Lemma 6.2 of the short proof. -/
theorem exists_bounded_restricted_modular_generators
    {N n r cap : ℕ} (hN : 0 < N)
    (K candidates : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ candidates ∧
      selected.card ≤ N * K.card ∧
      (∀ f : Finset (Fin n),
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ cap) ∧
      ∀ Q ∈ candidates,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) ∨
          ∃ f : Finset (Fin n), f ⊆ Q ∧
            cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let vec := modCliqueBoundaryOn N r K
  let inc : Finset (Fin n) → Finset (Fin n) → Prop := fun f Q ↦ f ⊆ Q
  let selected := greedyRunFrom vec (InAdditiveSpan vec) inc cap ∅
    candidates.toList
  have hsubset : selected ⊆ candidates := by
    have h := greedyRunFrom_subset_append vec (InAdditiveSpan vec) inc cap
      (∅ : Finset (Finset (Fin n))) candidates.toList
    simpa [selected] using h
  have hgeneric := exists_bounded_generators_list
    vec (InAdditiveSpan vec) inc cap
    (fun hAB hx ↦ hx.mono vec hAB)
    (fun chosen Q hQ ↦ vec_mem_additiveSpan vec chosen hQ)
    ∅ (by simp [counterLoad]) candidates.toList
  have hpow : 2 ^ selected.card ≤ N ^ K.card := by
    have h := two_pow_card_greedyRun_le_groupCard vec inc cap
      candidates.toList
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_coe] at h
    simpa [selected] using h
  have hcard : selected.card ≤ N * K.card :=
    card_le_mul_of_two_pow_le_pow hN hpow
  refine ⟨selected, hsubset, hcard, hgeneric.1, ?_⟩
  intro Q hQ
  have hmem : Q ∈ candidates.toList := by simpa using hQ
  simpa only [selected, vec, inc, InRestrictedModularSpan,
    IsSaturated] using hgeneric.2 Q hmem

/-- Source-faithful specialization in which the load counters are exactly
the `(r-1)`-faces.  The more permissive abstract theorem above is useful in
other applications, but the integral absorber must not allow a face of a
different cardinality (in particular the empty face) to cause saturation. -/
theorem exists_bounded_restricted_modular_generators_lowerFaces
    {N n r cap : ℕ} (hN : 0 < N)
    (K candidates : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ candidates ∧
      selected.card ≤ N * K.card ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ cap) ∧
      ∀ Q ∈ candidates,
        InRestrictedModularSpan N r K selected
          (modCliqueBoundaryOn N r K Q) ∨
          ∃ f : Finset (Fin n), f.card = r - 1 ∧ f ⊆ Q ∧
            cap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let vec := modCliqueBoundaryOn N r K
  let inc : Finset (Fin n) → Finset (Fin n) → Prop := fun f Q ↦
    f.card = r - 1 ∧ f ⊆ Q
  let selected := greedyRunFrom vec (InAdditiveSpan vec) inc cap ∅
    candidates.toList
  have hsubset : selected ⊆ candidates := by
    have h := greedyRunFrom_subset_append vec (InAdditiveSpan vec) inc cap
      (∅ : Finset (Finset (Fin n))) candidates.toList
    simpa [selected] using h
  have hgeneric := exists_bounded_generators_list
    vec (InAdditiveSpan vec) inc cap
    (fun hAB hx ↦ hx.mono vec hAB)
    (fun chosen Q hQ ↦ vec_mem_additiveSpan vec chosen hQ)
    ∅ (by simp [counterLoad]) candidates.toList
  have hpow : 2 ^ selected.card ≤ N ^ K.card := by
    have h := two_pow_card_greedyRun_le_groupCard vec inc cap
      candidates.toList
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_coe] at h
    simpa [selected] using h
  have hcard : selected.card ≤ N * K.card :=
    card_le_mul_of_two_pow_le_pow hN hpow
  refine ⟨selected, hsubset, hcard, ?_, ?_⟩
  · intro f hf
    have hload := hgeneric.1 f
    simpa [inc, counterLoad, hf] using hload
  · intro Q hQ
    have hmem : Q ∈ candidates.toList := by simpa using hQ
    rcases hgeneric.2 Q hmem with hspan | hsat
    · exact Or.inl hspan
    · obtain ⟨f, ⟨hf, hfQ⟩, hload⟩ := hsat
      refine Or.inr ⟨f, hf, hfQ, ?_⟩
      simpa [inc, counterLoad, hf] using hload

/-! ## Greedy generation with counter-dependent caps

The flattening stage also needs a much smaller cap on the number of
selected cliques through an `r`-edge.  A single scalar cap cannot express
that requirement together with the source's larger `(r-1)`-face cap.  The
following is the same finite greedy algorithm with a cap depending on the
counter. -/

def IsSaturatedAt (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (q : Q) : Prop :=
  ∃ c, inc c q ∧ cap c ≤ counterLoad inc selected c

theorem IsSaturatedAt.mono
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) {A B : Finset Q} (hAB : A ⊆ B) {q : Q}
    (h : IsSaturatedAt inc cap A q) : IsSaturatedAt inc cap B q := by
  obtain ⟨c, hcq, hc⟩ := h
  exact ⟨c, hcq, hc.trans (counterLoad_mono inc hAB c)⟩

noncomputable def variableCapGreedyStep
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (q : Q) : Finset Q := by
  classical
  exact if Span selected (vec q) ∨ IsSaturatedAt inc cap selected q then
    selected else insert q selected

def variableCapGreedyRunFrom
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) : Finset Q → List Q → Finset Q
  | selected, [] => selected
  | selected, q :: qs =>
      variableCapGreedyRunFrom vec Span inc cap
        (variableCapGreedyStep vec Span inc cap selected q) qs

lemma subset_variableCapGreedyStep
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (q : Q) :
    selected ⊆ variableCapGreedyStep vec Span inc cap selected q := by
  classical
  unfold variableCapGreedyStep
  split <;> simp

lemma subset_variableCapGreedyRunFrom
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (qs : List Q) :
    selected ⊆ variableCapGreedyRunFrom vec Span inc cap selected qs := by
  induction qs generalizing selected with
  | nil => exact Finset.Subset.rfl
  | cons q qs ih =>
      exact (subset_variableCapGreedyStep vec Span inc cap selected q).trans
        (ih (variableCapGreedyStep vec Span inc cap selected q))

lemma variableCapGreedyStep_subset_insert
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (q : Q) :
    variableCapGreedyStep vec Span inc cap selected q ⊆ insert q selected := by
  classical
  unfold variableCapGreedyStep
  split <;> simp

lemma variableCapGreedyRunFrom_subset_append
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (qs : List Q) :
    variableCapGreedyRunFrom vec Span inc cap selected qs ⊆
      selected ∪ qs.toFinset := by
  classical
  induction qs generalizing selected with
  | nil => simp [variableCapGreedyRunFrom]
  | cons q qs ih =>
      rw [variableCapGreedyRunFrom]
      intro x hx
      have hx' := ih
        (variableCapGreedyStep vec Span inc cap selected q) hx
      have hstep := variableCapGreedyStep_subset_insert
        vec Span inc cap selected q
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
        at hx' ⊢
      rcases hx' with hxStep | hxTail
      · have hxInsert := hstep hxStep
        simp only [Finset.mem_insert] at hxInsert
        exact hxInsert.elim (fun h ↦ Or.inr (Or.inl h)) (fun h ↦ Or.inl h)
      · exact Or.inr (Or.inr hxTail)

private lemma counterLoad_insert_le_cap
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) {selected : Finset Q} {q : Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap c)
    (hnotSat : ¬ IsSaturatedAt inc cap selected q) :
    ∀ c, counterLoad inc (insert q selected) c ≤ cap c := by
  classical
  intro c
  by_cases hcq : inc c q
  · have hlt : counterLoad inc selected c < cap c := by
      by_contra hnot
      exact hnotSat ⟨c, hcq, Nat.le_of_not_gt hnot⟩
    by_cases hqsel : q ∈ selected
    · rw [Finset.insert_eq_of_mem hqsel]
      exact hloads c
    · rw [counterLoad, Finset.filter_insert, if_pos hcq,
          Finset.card_insert_of_notMem]
      · simpa [counterLoad] using hlt
      · simpa [Finset.mem_filter, hqsel]
  · rw [counterLoad, Finset.filter_insert, if_neg hcq]
    exact hloads c

lemma variableCapGreedyStep_load_le
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) {selected : Finset Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap c) (q : Q) :
    ∀ c, counterLoad inc
      (variableCapGreedyStep vec Span inc cap selected q) c ≤ cap c := by
  classical
  unfold variableCapGreedyStep
  split
  · exact hloads
  · rename_i h
    push Not at h
    exact counterLoad_insert_le_cap inc cap hloads h.2

lemma variableCapGreedyRunFrom_load_le
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) {selected : Finset Q}
    (hloads : ∀ c, counterLoad inc selected c ≤ cap c)
    (qs : List Q) :
    ∀ c, counterLoad inc
      (variableCapGreedyRunFrom vec Span inc cap selected qs) c ≤ cap c := by
  induction qs generalizing selected with
  | nil => simpa [variableCapGreedyRunFrom] using hloads
  | cons q qs ih =>
      rw [variableCapGreedyRunFrom]
      exact ih (variableCapGreedyStep_load_le vec Span inc cap hloads q)

lemma variableCapGreedyStep_resolves
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ)
    (hself : ∀ (selected : Finset Q) (q : Q), q ∈ selected →
      Span selected (vec q))
    (selected : Finset Q) (q : Q) :
    Span (variableCapGreedyStep vec Span inc cap selected q) (vec q) ∨
      IsSaturatedAt inc cap
        (variableCapGreedyStep vec Span inc cap selected q) q := by
  classical
  unfold variableCapGreedyStep
  split
  · assumption
  · left
    apply hself
    simp

lemma variableCapGreedyRunFrom_resolves
    (vec : Q → X) (Span : Finset Q → X → Prop)
    (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ)
    (hspanMono : ∀ {A B : Finset Q} {x : X}, A ⊆ B →
      Span A x → Span B x)
    (hself : ∀ (selected : Finset Q) (q : Q), q ∈ selected →
      Span selected (vec q))
    (initial : Finset Q) (qs : List Q) :
    ∀ q ∈ qs, Span (variableCapGreedyRunFrom vec Span inc cap initial qs)
      (vec q) ∨ IsSaturatedAt inc cap
        (variableCapGreedyRunFrom vec Span inc cap initial qs) q := by
  classical
  induction qs generalizing initial with
  | nil => simp
  | cons q qs ih =>
      let next := variableCapGreedyStep vec Span inc cap initial q
      let final := variableCapGreedyRunFrom vec Span inc cap next qs
      have hnextFinal : next ⊆ final :=
        subset_variableCapGreedyRunFrom vec Span inc cap next qs
      have hqNext := variableCapGreedyStep_resolves
        vec Span inc cap hself initial q
      have hqFinal : Span final (vec q) ∨ IsSaturatedAt inc cap final q := by
        rcases hqNext with hspan | hsat
        · exact Or.inl (hspanMono hnextFinal hspan)
        · exact Or.inr (hsat.mono inc cap hnextFinal)
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa [next, final, variableCapGreedyRunFrom] using hqFinal
      · simpa [next, final, variableCapGreedyRunFrom] using ih next x hx

lemma two_pow_card_variableCapGreedyRunFrom_le_spanCard
    (vec : Q → A) (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (selected : Finset Q) (qs : List Q)
    (hstart : 2 ^ selected.card ≤
      Nat.card (AddSubgroup.closure (vec '' (↑selected : Set Q)))) :
    2 ^ (variableCapGreedyRunFrom vec (InAdditiveSpan vec) inc cap
        selected qs).card ≤
      Nat.card (AddSubgroup.closure
        (vec '' (↑(variableCapGreedyRunFrom vec (InAdditiveSpan vec)
          inc cap selected qs) : Set Q))) := by
  classical
  induction qs generalizing selected with
  | nil => simpa [variableCapGreedyRunFrom] using hstart
  | cons q qs ih =>
      let next := variableCapGreedyStep vec (InAdditiveSpan vec)
        inc cap selected q
      have hnext : 2 ^ next.card ≤
          Nat.card (AddSubgroup.closure (vec '' (↑next : Set Q))) := by
        unfold next variableCapGreedyStep
        split
        · exact hstart
        · rename_i h
          push Not at h
          have hqnot : q ∉ selected := by
            intro hq
            exact h.1 (vec_mem_additiveSpan vec selected hq)
          rw [Finset.card_insert_of_notMem hqnot, pow_succ]
          simpa [Nat.mul_comm] using
            ((Nat.mul_le_mul_left 2 hstart).trans
              (double_spanCard_le_insert vec selected q h.1))
      simpa [variableCapGreedyRunFrom, next] using ih next hnext

lemma two_pow_card_variableCapGreedyRun_le_groupCard
    (vec : Q → A) (inc : C → Q → Prop) [DecidableRel inc]
    (cap : C → ℕ) (qs : List Q) :
    2 ^ (variableCapGreedyRunFrom vec (InAdditiveSpan vec) inc cap ∅ qs).card ≤
      Nat.card A := by
  classical
  have hstart : 2 ^ (∅ : Finset Q).card ≤
      Nat.card (AddSubgroup.closure
        (vec '' (↑(∅ : Finset Q) : Set Q))) := by simp
  have hspan := two_pow_card_variableCapGreedyRunFrom_le_spanCard
    vec inc cap ∅ qs hstart
  exact hspan.trans (Nat.card_le_card_of_injective
    (fun x : AddSubgroup.closure
      (vec '' (↑(variableCapGreedyRunFrom vec (InAdditiveSpan vec)
        inc cap ∅ qs) : Set Q)) ↦ (x.1 : A))
    (fun _ _ h ↦ Subtype.ext h))

/-- Restricted modular generators with independent caps on lower-face and
edge multiplicities.  A non-generated clique is certified saturated in at
least one of these two senses. -/
theorem exists_twoCap_restricted_modular_generators
    {N n r faceCap edgeCap : ℕ} (hN : 0 < N)
    (K candidates : Finset (Finset (Fin n))) :
    ∃ selected : Finset (Finset (Fin n)),
      selected ⊆ candidates ∧
      selected.card ≤ N * K.card ∧
      (∀ f : Finset (Fin n), f.card = r - 1 →
        counterLoad (fun f Q ↦ f ⊆ Q) selected f ≤ faceCap) ∧
      (∀ e : Finset (Fin n), e.card = r →
        counterLoad (fun e Q ↦ e ⊆ Q) selected e ≤ edgeCap) ∧
      ∀ Q ∈ candidates,
        InRestrictedModularSpan N r K selected
            (modCliqueBoundaryOn N r K Q) ∨
          (∃ f : Finset (Fin n), f.card = r - 1 ∧ f ⊆ Q ∧
            faceCap ≤ counterLoad (fun f Q ↦ f ⊆ Q) selected f) ∨
          ∃ e : Finset (Fin n), e.card = r ∧ e ⊆ Q ∧
            edgeCap ≤ counterLoad (fun e Q ↦ e ⊆ Q) selected e := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let Counter := Sum (Finset (Fin n)) (Finset (Fin n))
  let vec := modCliqueBoundaryOn N r K
  let inc : Counter → Finset (Fin n) → Prop
    | Sum.inl f, Q => f.card = r - 1 ∧ f ⊆ Q
    | Sum.inr e, Q => e.card = r ∧ e ⊆ Q
  let cap : Counter → ℕ
    | Sum.inl _ => faceCap
    | Sum.inr _ => edgeCap
  let selected := variableCapGreedyRunFrom vec (InAdditiveSpan vec)
    inc cap ∅ candidates.toList
  have hsubset : selected ⊆ candidates := by
    have h := variableCapGreedyRunFrom_subset_append
      vec (InAdditiveSpan vec) inc cap
        (∅ : Finset (Finset (Fin n))) candidates.toList
    simpa [selected] using h
  have hloads : ∀ c, counterLoad inc selected c ≤ cap c := by
    exact variableCapGreedyRunFrom_load_le vec (InAdditiveSpan vec)
      inc cap (by simp [counterLoad]) candidates.toList
  have hresolve := variableCapGreedyRunFrom_resolves
    vec (InAdditiveSpan vec) inc cap
    (fun hAB hx ↦ hx.mono vec hAB)
    (fun chosen Q hQ ↦ vec_mem_additiveSpan vec chosen hQ)
    (∅ : Finset (Finset (Fin n))) candidates.toList
  have hpow : 2 ^ selected.card ≤ N ^ K.card := by
    have h := two_pow_card_variableCapGreedyRun_le_groupCard
      vec inc cap candidates.toList
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_coe] at h
    simpa [selected] using h
  have hcard : selected.card ≤ N * K.card :=
    card_le_mul_of_two_pow_le_pow hN hpow
  refine ⟨selected, hsubset, hcard, ?_, ?_, ?_⟩
  · intro f hf
    have h := hloads (Sum.inl f)
    simpa [inc, cap, counterLoad, hf] using h
  · intro e he
    have h := hloads (Sum.inr e)
    simpa [inc, cap, counterLoad, he] using h
  · intro Q hQ
    have hmem : Q ∈ candidates.toList := by simpa using hQ
    rcases hresolve Q hmem with hspan | hsat
    · exact Or.inl hspan
    · obtain ⟨c, hcQ, hload⟩ := hsat
      rcases c with f | e
      · exact Or.inr (Or.inl ⟨f, hcQ.1, hcQ.2, by
          simpa [inc, cap, counterLoad, hcQ.1] using hload⟩)
      · exact Or.inr (Or.inr ⟨e, hcQ.1, hcQ.2, by
          simpa [inc, cap, counterLoad, hcQ.1] using hload⟩)

end

end Erdos722.Generators
