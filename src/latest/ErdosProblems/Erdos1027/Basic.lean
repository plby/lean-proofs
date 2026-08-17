/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
The finite decision-tree/counting argument in the solution of Erdős problem 1027.

The non-uniform property-B theorem is deliberately exposed as the hypothesis
`beckFixedBudget`.  Everything after that input is finite combinatorics.
-/

namespace Erdos1027.Tree

open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Hypergraph (α : Type*) := Finset (Finset α)

/-- A set which meets, but does not contain, every edge. -/
def GoodSet {α : Type*} [DecidableEq α] (F : Hypergraph α) (B : Finset α) : Prop :=
  ∀ A ∈ F, (A ∩ B).Nonempty ∧ ¬ A ⊆ B

/-- Equivalently, a Boolean colouring with no monochromatic edge. -/
def ProperColoring {α : Type*} [DecidableEq α]
    (F : Hypergraph α) (red : Finset α) : Prop :=
  ∀ A ∈ F, (A ∩ red).Nonempty ∧ (A \ red).Nonempty

lemma goodSet_iff_properColoring {α : Type*} [DecidableEq α]
    (F : Hypergraph α) (B : Finset α) :
    GoodSet F B ↔ ProperColoring F B := by
  simp only [GoodSet, ProperColoring]
  constructor
  · intro h A hA
    obtain ⟨hmeet, hnot⟩ := h A hA
    refine ⟨hmeet, ?_⟩
    simpa [Finset.nonempty_iff_ne_empty, Finset.sdiff_eq_empty_iff_subset] using hnot
  · intro h A hA
    obtain ⟨hmeet, hmiss⟩ := h A hA
    refine ⟨hmeet, ?_⟩
    simpa [Finset.nonempty_iff_ne_empty, Finset.sdiff_eq_empty_iff_subset] using hmiss

/-- A partial red/blue colouring.  Validity relative to an ambient set is separate. -/
structure Partial (α : Type*) [DecidableEq α] where
  red : Finset α
  blue : Finset α

namespace Partial

variable {α : Type*} [DecidableEq α]

def Valid (X : Finset α) (p : Partial α) : Prop :=
  Disjoint p.red p.blue ∧ p.red ∪ p.blue ⊆ X

def colored (p : Partial α) : Finset α := p.red ∪ p.blue

def uncolored (X : Finset α) (p : Partial α) : Finset α := X \ p.colored

def child (p : Partial α) (v : α) (b : Bool) : Partial α :=
  if b then ⟨insert v p.red, p.blue⟩ else ⟨p.red, insert v p.blue⟩

@[simp] lemma child_red_true (p : Partial α) (v : α) : (p.child v true).red = insert v p.red := rfl
@[simp] lemma child_blue_true (p : Partial α) (v : α) : (p.child v true).blue = p.blue := rfl
@[simp] lemma child_red_false (p : Partial α) (v : α) : (p.child v false).red = p.red := rfl
@[simp] lemma child_blue_false (p : Partial α) (v : α) : (p.child v false).blue = insert v p.blue := rfl

lemma valid_child {X : Finset α} {p : Partial α} {v : α} (hp : p.Valid X)
    (hv : v ∈ p.uncolored X) (b : Bool) : (p.child v b).Valid X := by
  rcases hp with ⟨hdis, hsub⟩
  have hvX : v ∈ X := (Finset.mem_sdiff.mp hv).1
  have hvred : v ∉ p.red := by
    intro h
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ h)
  have hvblue : v ∉ p.blue := by
    intro h
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ h)
  cases b
  · constructor
    · change Disjoint p.red (insert v p.blue)
      rw [Finset.disjoint_insert_right]
      exact ⟨hvred, hdis⟩
    · change p.red ∪ insert v p.blue ⊆ X
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hsub (Finset.mem_union_left _ hx)
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hvX
        · exact hsub (Finset.mem_union_right _ hx)
  · constructor
    · change Disjoint (insert v p.red) p.blue
      rw [Finset.disjoint_insert_left]
      exact ⟨hvblue, hdis⟩
    · change insert v p.red ∪ p.blue ⊆ X
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hvX
        · exact hsub (Finset.mem_union_left _ hx)
      · exact hsub (Finset.mem_union_right _ hx)

lemma uncolored_child {X : Finset α} {p : Partial α} {v : α}
    (hv : v ∈ p.uncolored X) (b : Bool) :
    (p.child v b).uncolored X = p.uncolored X \ {v} := by
  ext x
  cases b <;> simp [uncolored, colored, child, and_assoc, and_left_comm, and_comm]

lemma card_uncolored_child {X : Finset α} {p : Partial α} {v : α}
    (hv : v ∈ p.uncolored X) (b : Bool) :
    ((p.child v b).uncolored X).card + 1 = (p.uncolored X).card := by
  rw [uncolored_child hv]
  have hsub : {v} ⊆ p.uncolored X := by simpa using hv
  simpa using Finset.card_sdiff_add_card_eq_card hsub

end Partial

variable {α : Type*} [DecidableEq α]

/-- An edge is live when it has not yet received both colours. -/
def Live (p : Partial α) (A : Finset α) : Prop :=
  Disjoint A p.red ∨ Disjoint A p.blue

/-- Contribution of completions which make an edge entirely the chosen colour. -/
def monoScore (forbidden chosen A : Finset α) : ℕ :=
  if Disjoint A forbidden then 2 ^ (A ∩ chosen).card else 0

/-- Twice the scaled weight from the writeup.  This normalization is integral.
Initially every edge has score `2`; a nonempty live coloured edge with `k`
coloured vertices has score `2^k`; a dead edge has score zero. -/
def edgeScore (p : Partial α) (A : Finset α) : ℕ :=
  monoScore p.blue p.red A + monoScore p.red p.blue A

def totalScore (F : Hypergraph α) (p : Partial α) : ℕ :=
  ∑ A ∈ F, edgeScore p A

def vertexLoad (F : Hypergraph α) (p : Partial α) (v : α) : ℕ :=
  (F.filter fun A => v ∈ A).sup (edgeScore p)

@[simp] lemma edgeScore_empty (A : Finset α) :
    edgeScore (Partial.mk ∅ ∅) A = 2 := by
  simp [edgeScore, monoScore]

@[simp] lemma totalScore_empty (F : Hypergraph α) :
    totalScore F (Partial.mk ∅ ∅) = 2 * F.card := by
  simp [totalScore, Nat.mul_comm]

lemma edgeScore_eq_zero_of_not_live {p : Partial α} {A : Finset α}
    (h : ¬ Live p A) : edgeScore p A = 0 := by
  simp only [Live, not_or] at h
  simp [edgeScore, monoScore, h.1, h.2]

lemma monoScore_branch (forbidden chosen A : Finset α) {v : α}
    (_hvf : v ∉ forbidden) (hvc : v ∉ chosen) :
    monoScore forbidden (insert v chosen) A + monoScore (insert v forbidden) chosen A =
      2 * monoScore forbidden chosen A := by
  by_cases hvA : v ∈ A
  · by_cases hd : Disjoint A forbidden
    · have hinter : A ∩ insert v chosen = insert v (A ∩ chosen) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        aesop
      have hnot : v ∉ A ∩ chosen := by simp [hvc]
      have hd' : ¬ Disjoint A (insert v forbidden) := by
        intro h
        exact (Finset.disjoint_left.mp h) hvA (Finset.mem_insert_self v forbidden)
      simp only [monoScore]
      rw [if_pos hd, if_neg hd', if_pos hd, Nat.add_zero]
      rw [hinter, Finset.card_insert_of_notMem hnot, pow_succ]
      omega
    · have hd' : ¬ Disjoint A (insert v forbidden) := by
        exact fun h => hd (h.mono_right (Finset.subset_insert v forbidden))
      simp [monoScore, hd, hd']
  · have hinter : A ∩ insert v chosen = A ∩ chosen := by ext x; simp; aesop
    have hdis : Disjoint A (insert v forbidden) ↔ Disjoint A forbidden := by simp [hvA]
    simp only [monoScore, hinter, hdis]
    split <;> omega

/-- Exact one-step averaging, in integral form. -/
lemma edgeScore_branch {p : Partial α} {A : Finset α} {v : α}
    (hv : v ∉ p.colored) :
    edgeScore (p.child v false) A + edgeScore (p.child v true) A =
      2 * edgeScore p A := by
  have hvr : v ∉ p.red := fun h => hv (Finset.mem_union_left _ h)
  have hvb : v ∉ p.blue := fun h => hv (Finset.mem_union_right _ h)
  have hblue := monoScore_branch p.blue p.red A hvb hvr
  have hred := monoScore_branch p.red p.blue A hvr hvb
  rw [edgeScore, edgeScore, edgeScore]
  simp only [Partial.child_red_false, Partial.child_blue_false,
    Partial.child_red_true, Partial.child_blue_true]
  omega

lemma totalScore_branch {F : Hypergraph α} {p : Partial α} {v : α}
    (hv : v ∉ p.colored) :
    totalScore F (p.child v false) + totalScore F (p.child v true) =
      2 * totalScore F p := by
  simp only [totalScore, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun A hA => edgeScore_branch hv

section DecisionTree

variable [LinearOrder α]

/-- A deterministic minimizer of a natural-valued load over a finite set. -/
noncomputable def selectMin (U : Finset α) (load : α → ℕ) : Option α :=
  if hU : U.Nonempty then some (Classical.choose (Finset.exists_min_image U load hU)) else none

lemma selectMin_eq_none_iff (U : Finset α) (load : α → ℕ) :
    selectMin U load = none ↔ U = ∅ := by
  simp [selectMin, Finset.not_nonempty_iff_eq_empty]

lemma selectMin_mem {U : Finset α} {load : α → ℕ} {v : α}
    (hv : selectMin U load = some v) : v ∈ U := by
  simp only [selectMin] at hv
  split at hv
  · have heq : Classical.choose (Finset.exists_min_image U load ‹U.Nonempty›) = v :=
      Option.some.inj hv
    simpa only [heq] using
      (Classical.choose_spec (Finset.exists_min_image U load ‹U.Nonempty›)).1
  · simp at hv

lemma selectMin_minimal {U : Finset α} {load : α → ℕ} {v : α}
    (hv : selectMin U load = some v) : ∀ x ∈ U, load v ≤ load x := by
  simp only [selectMin] at hv
  split at hv
  · have heq : Classical.choose (Finset.exists_min_image U load ‹U.Nonempty›) = v :=
      Option.some.inj hv
    intro x hx
    simpa only [heq] using
      (Classical.choose_spec (Finset.exists_min_image U load ‹U.Nonempty›)).2 x hx
  · simp at hv

def Failed (threshold : ℕ) (F : Hypergraph α) (p : Partial α) : Prop :=
  threshold < totalScore F p

def Repairable (r : ℕ) (X : Finset α) (F : Hypergraph α) (p : Partial α) : Prop :=
  ∃ A ∈ F, Live p A ∧ (A ∩ p.uncolored X).card ≤ r

inductive DTree (α : Type*) [DecidableEq α] where
  | leaf (p : Partial α)
  | node (p : Partial α) (v : α) (zero one : DTree α)

namespace DTree

def leaves : DTree α → List (Partial α)
  | leaf p => [p]
  | node _ _ t₀ t₁ => t₀.leaves ++ t₁.leaves

def leafSum (g : Partial α → ℕ) : DTree α → ℕ
  | leaf p => g p
  | node _ _ t₀ t₁ => t₀.leafSum g + t₁.leafSum g

lemma leafSum_eq_sum_leaves (t : DTree α) (g : Partial α → ℕ) :
    t.leafSum g = (t.leaves.map g).sum := by
  induction t <;> simp_all [leaves, leafSum]

lemma mem_leaves_leaf (p q : Partial α) : q ∈ (leaf p : DTree α).leaves ↔ q = p := by simp [leaves]

lemma mem_leaves_node (p : Partial α) (v : α) (t₀ t₁ : DTree α) (q : Partial α) :
    q ∈ (node p v t₀ t₁).leaves ↔ q ∈ t₀.leaves ∨ q ∈ t₁.leaves := by simp [leaves]

end DTree

/-- The adaptive tree, with the tests in the order failure, repairability,
completion.  The fuel is only a structurally recursive presentation; at the
root it is the number of uncoloured vertices. -/
noncomputable def build (threshold r : ℕ) (X : Finset α) (F : Hypergraph α) :
    ℕ → Partial α → DTree α
  | 0, p => .leaf p
  | fuel + 1, p =>
      if Failed threshold F p then .leaf p
      else if Repairable r X F p then .leaf p
      else
        match selectMin (p.uncolored X) (vertexLoad F p) with
        | none => .leaf p
        | some v => .node p v
            (build threshold r X F fuel (p.child v false))
            (build threshold r X F fuel (p.child v true))

def weightedScore (X : Finset α) (F : Hypergraph α) (t : DTree α) : ℕ :=
  t.leafSum fun p => 2 ^ (p.uncolored X).card * totalScore F p

def leafMass (X : Finset α) (P : Partial α → Prop) [DecidablePred P]
    (t : DTree α) : ℕ :=
  t.leafSum fun p => if P p then 2 ^ (p.uncolored X).card else 0

def allMass (X : Finset α) (t : DTree α) : ℕ :=
  t.leafSum fun p => 2 ^ (p.uncolored X).card

def Refines (p q : Partial α) : Prop := p.red ⊆ q.red ∧ p.blue ⊆ q.blue

def Extends (p : Partial α) (B : Finset α) : Prop := p.red ⊆ B ∧ Disjoint p.blue B

@[refl] lemma Refines.refl (p : Partial α) : Refines p p := ⟨fun _ => id, fun _ => id⟩

lemma Refines.trans {p q s : Partial α} (hpq : Refines p q) (hqs : Refines q s) :
    Refines p s := ⟨hpq.1.trans hqs.1, hpq.2.trans hqs.2⟩

lemma refines_child (p : Partial α) (v : α) (b : Bool) : Refines p (p.child v b) := by
  cases b <;> simp [Refines, Partial.child]

lemma leaf_refines_root (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p q : Partial α)
    (hq : q ∈ (build threshold r X F fuel p).leaves) : Refines p q := by
  induction fuel generalizing p with
  | zero =>
      have hqp : q = p := by simpa [build, DTree.leaves] using hq
      rw [hqp]
  | succ fuel ih =>
      rw [build] at hq
      split at hq
      · have hqp : q = p := by simpa [DTree.leaves] using hq
        rw [hqp]
      · split at hq
        · have hqp : q = p := by simpa [DTree.leaves] using hq
          rw [hqp]
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o at hq
          cases o with
          | none =>
              have hqp : q = p := by simpa [DTree.leaves] using hq
              rw [hqp]
          | some v =>
              simp only [DTree.mem_leaves_node] at hq
              rcases hq with hq | hq
              · exact (refines_child p v false).trans (ih _ hq)
              · exact (refines_child p v true).trans (ih _ hq)

lemma leaf_valid (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p q : Partial α) (hp : p.Valid X)
    (hq : q ∈ (build threshold r X F fuel p).leaves) : q.Valid X := by
  induction fuel generalizing p with
  | zero =>
      have hqp : q = p := by simpa [build, DTree.leaves] using hq
      simpa [hqp] using hp
  | succ fuel ih =>
      rw [build] at hq
      split at hq
      · have hqp : q = p := by simpa [DTree.leaves] using hq
        simpa [hqp] using hp
      · split at hq
        · have hqp : q = p := by simpa [DTree.leaves] using hq
          simpa [hqp] using hp
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o at hq
          cases o with
          | none =>
              have hqp : q = p := by simpa [DTree.leaves] using hq
              simpa [hqp] using hp
          | some v =>
              have hvU : v ∈ p.uncolored X := selectMin_mem hs
              simp only [DTree.mem_leaves_node] at hq
              rcases hq with hq | hq
              · exact ih _ (p.valid_child hp hvU false) hq
              · exact ih _ (p.valid_child hp hvU true) hq

lemma extends_of_refines {p q : Partial α} {B : Finset α}
    (hpq : Refines p q) (hq : Extends q B) : Extends p B := by
  refine ⟨hpq.1.trans hq.1, ?_⟩
  exact hq.2.mono_left hpq.2

/-- Two distinct leaves describe incompatible cylinder sets of total colourings. -/
lemma compatible_leaves_eq (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p q₀ q₁ : Partial α) (B : Finset α)
    (hq₀ : q₀ ∈ (build threshold r X F fuel p).leaves)
    (hq₁ : q₁ ∈ (build threshold r X F fuel p).leaves)
    (hB₀ : Extends q₀ B) (hB₁ : Extends q₁ B) : q₀ = q₁ := by
  induction fuel generalizing p with
  | zero =>
      simp only [build, DTree.mem_leaves_leaf] at hq₀ hq₁
      exact hq₀.trans hq₁.symm
  | succ fuel ih =>
      rw [build] at hq₀ hq₁
      split at hq₀
      · rw [if_pos ‹Failed threshold F p›] at hq₁
        simp only [DTree.mem_leaves_leaf] at hq₀ hq₁
        exact hq₀.trans hq₁.symm
      · rw [if_neg ‹¬ Failed threshold F p›] at hq₁
        split at hq₀
        · rw [if_pos ‹Repairable r X F p›] at hq₁
          simp only [DTree.mem_leaves_leaf] at hq₀ hq₁
          exact hq₀.trans hq₁.symm
        · rw [if_neg ‹¬ Repairable r X F p›] at hq₁
          generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o at hq₀ hq₁
          cases o with
          | none =>
              simp only [DTree.mem_leaves_leaf] at hq₀ hq₁
              exact hq₀.trans hq₁.symm
          | some v =>
              simp only [DTree.mem_leaves_node] at hq₀ hq₁
              rcases hq₀ with hq₀ | hq₀ <;> rcases hq₁ with hq₁ | hq₁
              · exact ih _ hq₀ hq₁
              · have href₀ := leaf_refines_root threshold r X F fuel
                    (p.child v false) q₀ hq₀
                have href₁ := leaf_refines_root threshold r X F fuel
                    (p.child v true) q₁ hq₁
                have hb0 := (extends_of_refines href₀ hB₀).2
                have hb1 := (extends_of_refines href₁ hB₁).1
                have hvnot : v ∉ B := by
                  exact fun hv => Finset.disjoint_left.mp hb0
                    (by simp [Partial.child]) hv
                exact False.elim (hvnot (hb1 (by simp [Partial.child])))
              · have href₀ := leaf_refines_root threshold r X F fuel
                    (p.child v true) q₀ hq₀
                have href₁ := leaf_refines_root threshold r X F fuel
                    (p.child v false) q₁ hq₁
                have hb0 := (extends_of_refines href₀ hB₀).1
                have hb1 := (extends_of_refines href₁ hB₁).2
                have hvnot : v ∉ B := by
                  exact fun hv => Finset.disjoint_left.mp hb1
                    (by simp [Partial.child]) hv
                exact False.elim (hvnot (hb0 (by simp [Partial.child])))
              · exact ih _ hq₀ hq₁

lemma terminal_leaf (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (p q : Partial α) (hp : p.Valid X)
    (hq : q ∈ (build threshold r X F (p.uncolored X).card p).leaves) :
    Failed threshold F q ∨ Repairable r X F q ∨ q.uncolored X = ∅ := by
  generalize hu : (p.uncolored X).card = fuel at hq
  induction fuel generalizing p with
  | zero =>
      have hU : p.uncolored X = ∅ := Finset.card_eq_zero.mp hu
      have hqp : q = p := by simpa [build, DTree.leaves] using hq
      rw [hqp]
      exact Or.inr (Or.inr hU)
  | succ fuel ih =>
      rw [build] at hq
      split at hq
      · have hqp : q = p := by simpa [DTree.leaves] using hq
        rw [hqp]
        exact Or.inl ‹Failed threshold F p›
      · split at hq
        · have hqp : q = p := by simpa [DTree.leaves] using hq
          rw [hqp]
          exact Or.inr (Or.inl ‹Repairable r X F p›)
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o at hq
          cases o with
          | none =>
              have hqp : q = p := by simpa [DTree.leaves] using hq
              rw [hqp]
              exact Or.inr (Or.inr
                ((selectMin_eq_none_iff (p.uncolored X) (vertexLoad F p)).mp hs))
          | some v =>
              have hvU : v ∈ p.uncolored X := selectMin_mem hs
              have hc0 := p.card_uncolored_child hvU false
              have hc1 := p.card_uncolored_child hvU true
              simp only [DTree.mem_leaves_node] at hq
              rcases hq with hq | hq
              · apply ih (p := p.child v false) (p.valid_child hp hvU false) ?_ hq
                omega
              · apply ih (p := p.child v true) (p.valid_child hp hvU true) ?_ hq
                omega

/-- Every non-root leaf remembers an actual minimum-load branch at its parent. -/
lemma leaf_eq_root_or_has_parent (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p q : Partial α)
    (hq : q ∈ (build threshold r X F fuel p).leaves) :
    q = p ∨ ∃ parent v b,
      selectMin (parent.uncolored X) (vertexLoad F parent) = some v ∧
      ¬ Failed threshold F parent ∧ ¬ Repairable r X F parent ∧
      q = parent.child v b := by
  induction fuel generalizing p with
  | zero => left; simpa [build, DTree.leaves] using hq
  | succ fuel ih =>
      rw [build] at hq
      split at hq
      · left; simpa [DTree.leaves] using hq
      · split at hq
        · left; simpa [DTree.leaves] using hq
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o at hq
          cases o with
          | none => left; simpa [DTree.leaves] using hq
          | some v =>
              simp only [DTree.mem_leaves_node] at hq
              rcases hq with hq | hq
              · rcases ih (p := p.child v false) hq with heq | hparent
                · right; exact ⟨p, v, false, hs, ‹¬ Failed threshold F p›,
                    ‹¬ Repairable r X F p›, heq⟩
                · exact Or.inr hparent
              · rcases ih (p := p.child v true) hq with heq | hparent
                · right; exact ⟨p, v, true, hs, ‹¬ Failed threshold F p›,
                    ‹¬ Repairable r X F p›, heq⟩
                · exact Or.inr hparent

lemma weightedScore_build (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p : Partial α) (hp : p.Valid X) :
    weightedScore X F (build threshold r X F fuel p) =
      2 ^ (p.uncolored X).card * totalScore F p := by
  induction fuel generalizing p with
  | zero => simp [build, weightedScore, DTree.leafSum]
  | succ fuel ih =>
      rw [build]
      split
      · simp [weightedScore, DTree.leafSum]
      · split
        · simp [weightedScore, DTree.leafSum]
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o
          cases o with
          | none => simp [weightedScore, DTree.leafSum]
          | some v =>
              have hvU : v ∈ p.uncolored X := selectMin_mem hs
              have hvcol : v ∉ p.colored := (Finset.mem_sdiff.mp hvU).2
              have hvalid0 := p.valid_child hp hvU false
              have hvalid1 := p.valid_child hp hvU true
              change weightedScore X F
                    (build threshold r X F fuel (p.child v false)) +
                  weightedScore X F
                    (build threshold r X F fuel (p.child v true)) = _
              rw [ih _ hvalid0, ih _ hvalid1]
              have hu0 := p.card_uncolored_child hvU false
              have hu1 := p.card_uncolored_child hvU true
              have hscores := totalScore_branch (F := F) (p := p) hvcol
              rw [show ((p.child v false).uncolored X).card =
                (p.uncolored X).card - 1 by omega]
              rw [show ((p.child v true).uncolored X).card =
                (p.uncolored X).card - 1 by omega]
              have hu : 0 < (p.uncolored X).card := Finset.card_pos.mpr ⟨v, hvU⟩
              have hpow : 2 ^ (p.uncolored X).card =
                  2 * 2 ^ ((p.uncolored X).card - 1) := by
                calc
                  2 ^ (p.uncolored X).card =
                      2 ^ (((p.uncolored X).card - 1) + 1) := by
                        congr 1 <;> omega
                  _ = 2 ^ ((p.uncolored X).card - 1) * 2 := by rw [pow_succ]
                  _ = 2 * 2 ^ ((p.uncolored X).card - 1) := by ring
              calc
                2 ^ ((p.uncolored X).card - 1) * totalScore F (p.child v false) +
                    2 ^ ((p.uncolored X).card - 1) * totalScore F (p.child v true) =
                    2 ^ ((p.uncolored X).card - 1) *
                      (totalScore F (p.child v false) +
                        totalScore F (p.child v true)) := by ring
                _ = 2 ^ ((p.uncolored X).card - 1) * (2 * totalScore F p) := by
                  rw [hscores]
                _ = 2 ^ (p.uncolored X).card * totalScore F p := by
                  rw [hpow]
                  ring

lemma allMass_build (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p : Partial α) (hp : p.Valid X) :
    allMass X (build threshold r X F fuel p) = 2 ^ (p.uncolored X).card := by
  induction fuel generalizing p with
  | zero => simp [build, allMass, DTree.leafSum]
  | succ fuel ih =>
      rw [build]
      split
      · simp [allMass, DTree.leafSum]
      · split
        · simp [allMass, DTree.leafSum]
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o
          cases o with
          | none => simp [allMass, DTree.leafSum]
          | some v =>
              have hvU : v ∈ p.uncolored X := selectMin_mem hs
              have hvalid0 := p.valid_child hp hvU false
              have hvalid1 := p.valid_child hp hvU true
              change allMass X (build threshold r X F fuel (p.child v false)) +
                  allMass X (build threshold r X F fuel (p.child v true)) = _
              rw [ih _ hvalid0, ih _ hvalid1]
              have hu0 := p.card_uncolored_child hvU false
              have hu1 := p.card_uncolored_child hvU true
              have hu : 0 < (p.uncolored X).card := Finset.card_pos.mpr ⟨v, hvU⟩
              rw [show ((p.child v false).uncolored X).card =
                (p.uncolored X).card - 1 by omega]
              rw [show ((p.child v true).uncolored X).card =
                (p.uncolored X).card - 1 by omega]
              have hpow : 2 ^ (p.uncolored X).card =
                  2 * 2 ^ ((p.uncolored X).card - 1) := by
                calc
                  2 ^ (p.uncolored X).card =
                      2 ^ (((p.uncolored X).card - 1) + 1) := by
                        congr 1 <;> omega
                  _ = 2 ^ ((p.uncolored X).card - 1) * 2 := by rw [pow_succ]
                  _ = 2 * 2 ^ ((p.uncolored X).card - 1) := by ring
              rw [hpow]
              ring

lemma leafMass_add_compl (X : Finset α) (P : Partial α → Prop) [DecidablePred P]
    (t : DTree α) : leafMass X P t + leafMass X (fun p => ¬ P p) t = allMass X t := by
  induction t with
  | leaf p =>
      by_cases hP : P p <;> simp [leafMass, allMass, DTree.leafSum, hP]
  | node p v t₀ t₁ ih₀ ih₁ =>
      change (leafMass X P t₀ + leafMass X P t₁) +
          (leafMass X (fun p => ¬ P p) t₀ + leafMass X (fun p => ¬ P p) t₁) =
        allMass X t₀ + allMass X t₁
      omega

lemma threshold_mul_leafMass_failed_le (threshold : ℕ) (X : Finset α)
    (F : Hypergraph α) (t : DTree α) :
    threshold * leafMass X (Failed threshold F) t ≤ weightedScore X F t := by
  induction t with
  | leaf p =>
      change threshold * (if Failed threshold F p then
          2 ^ (p.uncolored X).card else 0) ≤
        2 ^ (p.uncolored X).card * totalScore F p
      by_cases hfail : Failed threshold F p
      · rw [if_pos hfail]
        simpa [Nat.mul_comm] using
          Nat.mul_le_mul_left (2 ^ (p.uncolored X).card)
            (Nat.le_of_lt (show threshold < totalScore F p from hfail))
      · rw [if_neg hfail]
        simp
  | node p v t₀ t₁ ih₀ ih₁ =>
      change threshold * (leafMass X (Failed threshold F) t₀ +
          leafMass X (Failed threshold F) t₁) ≤
        weightedScore X F t₀ + weightedScore X F t₁
      rw [Nat.mul_add]
      exact Nat.add_le_add ih₀ ih₁

/-- The failed leaves account for at most half of all full extensions. -/
lemma failed_mass_at_most_half (C n r : ℕ) (hC : 0 < C) (X : Finset α)
    (F : Hypergraph α) (hcard : F.card ≤ C * 2 ^ n) :
    2 * leafMass X (Failed (4 * C * 2 ^ n) F)
        (build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)) ≤ 2 ^ X.card := by
  let t := build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)
  have hvalid : (Partial.mk (α := α) ∅ ∅).Valid X := by simp [Partial.Valid]
  have hw := threshold_mul_leafMass_failed_le (4 * C * 2 ^ n) X F t
  rw [weightedScore_build _ _ _ _ _ _ hvalid, totalScore_empty] at hw
  simp only [Partial.uncolored, Partial.colored, Finset.empty_union,
    Finset.sdiff_empty] at hw
  have hroot : 2 * F.card ≤ 2 * (C * 2 ^ n) := Nat.mul_le_mul_left 2 hcard
  have hmul : (2 * (C * 2 ^ n)) *
      (2 * leafMass X (Failed (4 * C * 2 ^ n) F) t) ≤
      (2 * (C * 2 ^ n)) * 2 ^ X.card := by
    calc
      _ = (4 * C * 2 ^ n) * leafMass X (Failed (4 * C * 2 ^ n) F) t := by ring
      _ ≤ 2 ^ X.card * (2 * F.card) := hw
      _ ≤ 2 ^ X.card * (2 * (C * 2 ^ n)) := Nat.mul_le_mul_left _ hroot
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

lemma leaves_build_nodup (threshold r : ℕ) (X : Finset α) (F : Hypergraph α)
    (fuel : ℕ) (p : Partial α) (hp : p.Valid X) :
    (build threshold r X F fuel p).leaves.Nodup := by
  induction fuel generalizing p with
  | zero => simp [build, DTree.leaves]
  | succ fuel ih =>
      rw [build]
      split
      · simp [DTree.leaves]
      · split
        · simp [DTree.leaves]
        · generalize hs : selectMin (p.uncolored X) (vertexLoad F p) = o
          cases o with
          | none => simp [DTree.leaves]
          | some v =>
              have hvU : v ∈ p.uncolored X := selectMin_mem hs
              rw [DTree.leaves, List.nodup_append]
              refine ⟨ih _ (p.valid_child hp hvU false),
                ih _ (p.valid_child hp hvU true), ?_⟩
              intro q hq0 q' hq1 heq
              subst q'
              have href0 := leaf_refines_root threshold r X F fuel
                (p.child v false) q hq0
              have href1 := leaf_refines_root threshold r X F fuel
                (p.child v true) q hq1
              have hqvalid := leaf_valid threshold r X F fuel (p.child v false) q
                (p.valid_child hp hvU false) hq0
              have hvred : v ∈ q.red := href1.1 (by simp [Partial.child])
              have hvblue : v ∈ q.blue := href0.2 (by simp [Partial.child])
              exact Finset.disjoint_left.mp hqvalid.1 hvred hvblue

def leafCount (P : Partial α → Prop) [DecidablePred P] (t : DTree α) : ℕ :=
  (t.leaves.filter P).length

lemma leafMass_le_pow_mul_leafCount (X : Finset α) (P : Partial α → Prop)
    [DecidablePred P] (K : ℕ) (t : DTree α)
    (hbound : ∀ p ∈ t.leaves, P p → (p.uncolored X).card ≤ K) :
    leafMass X P t ≤ 2 ^ K * leafCount P t := by
  induction t with
  | leaf p =>
      by_cases hP : P p
      · simpa [leafMass, leafCount, DTree.leafSum, DTree.leaves, hP] using
          Nat.pow_le_pow_right (by omega : 0 < 2) (hbound p (by simp [DTree.leaves]) hP)
      · simp [leafMass, leafCount, DTree.leafSum, DTree.leaves, hP]
  | node p v t₀ t₁ ih₀ ih₁ =>
      have h₀ := ih₀ fun q hq hP =>
        hbound q (List.mem_append_left t₁.leaves hq) hP
      have h₁ := ih₁ fun q hq hP =>
        hbound q (List.mem_append_right t₀.leaves hq) hP
      simpa [leafMass, leafCount, DTree.leafSum, DTree.leaves, Nat.mul_add] using
        Nat.add_le_add h₀ h₁

end DecisionTree

section Residual

noncomputable def residual (X : Finset α) (F : Hypergraph α) (p : Partial α) : Hypergraph α :=
  (F.filter (Live p)).image fun A => A ∩ p.uncolored X

def scaledWeight (n : ℕ) (H : Hypergraph α) : ℕ :=
  ∑ E ∈ H, 2 ^ (n - E.card)

lemma card_colored_add_uncolored {X A : Finset α} {p : Partial α}
    (hA : A ⊆ X) :
    (A ∩ p.colored).card + (A ∩ p.uncolored X).card = A.card := by
  have heq : A ∩ p.uncolored X = A \ (A ∩ p.colored) := by
    ext x
    simp [Partial.uncolored, and_assoc]
    aesop
  rw [heq, add_comm]
  exact Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left)

lemma edgeScore_lower_of_live {X A : Finset α} {p : Partial α}
    (hA : A ⊆ X) (hlive : Live p A) :
    2 ^ (A ∩ p.colored).card ≤ edgeScore p A := by
  rcases hlive with hred | hblue
  · have heq : A ∩ p.colored = A ∩ p.blue := by
      ext x
      simp [Partial.colored]
      exact fun hxA hxred => False.elim (Finset.disjoint_left.mp hred hxA hxred)
    rw [heq]
    simp [edgeScore, monoScore, hred]
  · have heq : A ∩ p.colored = A ∩ p.red := by
      ext x
      simp [Partial.colored]
      exact fun hxA hxblue => False.elim (Finset.disjoint_left.mp hblue hxA hxblue)
    rw [heq]
    simp [edgeScore, monoScore, hblue]

lemma residual_term_le_edgeScore {n : ℕ} {X A : Finset α} {p : Partial α}
    (hA : A ⊆ X) (hcard : A.card = n) (hlive : Live p A) :
    2 ^ (n - (A ∩ p.uncolored X).card) ≤ edgeScore p A := by
  have hpartition := card_colored_add_uncolored (p := p) hA
  have hexp : n - (A ∩ p.uncolored X).card = (A ∩ p.colored).card := by omega
  rw [hexp]
  exact edgeScore_lower_of_live hA hlive

lemma monoScore_le_colored (p : Partial α) (A : Finset α) :
    monoScore p.blue p.red A ≤ 2 ^ (A ∩ p.colored).card := by
  simp only [monoScore]
  split
  · exact Nat.pow_le_pow_right (by omega : 0 < 2) (Finset.card_le_card <| by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1, Finset.mem_union_left _ hx.2⟩)
  · simp

lemma edgeScore_upper (p : Partial α) (A : Finset α) :
    edgeScore p A ≤ 2 * 2 ^ (A ∩ p.colored).card := by
  have hred := monoScore_le_colored p A
  have hblue : monoScore p.red p.blue A ≤ 2 ^ (A ∩ p.colored).card := by
    simp only [monoScore]
    split
    · exact Nat.pow_le_pow_right (by omega : 0 < 2) (Finset.card_le_card <| by
        intro x hx
        rw [Finset.mem_inter] at hx ⊢
        exact ⟨hx.1, Finset.mem_union_right _ hx.2⟩)
    · simp
  simp only [edgeScore]
  omega

lemma heavy_edge_residual_card_le {n r : ℕ} (hn : r + 2 ≤ n)
    {X A : Finset α} {p : Partial α} (hA : A ⊆ X) (hcard : A.card = n)
    (hheavy : 2 ^ (n - r - 1) ≤ edgeScore p A) :
    (A ∩ p.uncolored X).card ≤ r + 2 := by
  have hu := edgeScore_upper p A
  have hpows : 2 ^ (n - r - 1) ≤ 2 ^ ((A ∩ p.colored).card + 1) := by
    calc
      _ ≤ edgeScore p A := hheavy
      _ ≤ 2 * 2 ^ (A ∩ p.colored).card := hu
      _ = _ := by rw [pow_succ]; omega
  have hexp : n - r - 1 ≤ (A ∩ p.colored).card + 1 := by
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpows
  have hpartition := card_colored_add_uncolored (p := p) hA
  omega

lemma sum_image_le_sum_of_nonneg {β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (g : β → ℕ) (h : α → ℕ)
    (hle : ∀ a ∈ s, g (f a) ≤ h a) :
    ∑ b ∈ s.image f, g b ≤ ∑ a ∈ s, h a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa, Finset.sum_insert ha]
        exact (ih fun x hx => hle x (Finset.mem_insert_of_mem hx)).trans
          (Nat.le_add_left _ _)
      · rw [Finset.sum_insert hfa, Finset.sum_insert ha]
        exact Nat.add_le_add (hle a (by simp)) (ih fun x hx => hle x (by simp [hx]))

lemma scaledWeight_residual_le_totalScore {n : ℕ} {X : Finset α} {F : Hypergraph α}
    {p : Partial α} (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n) :
    scaledWeight n (residual X F p) ≤ totalScore F p := by
  let liveF := F.filter (Live p)
  have himage :
      (∑ E ∈ liveF.image (fun A => A ∩ p.uncolored X), 2 ^ (n - E.card)) ≤
      ∑ A ∈ liveF, edgeScore p A := by
    exact sum_image_le_sum_of_nonneg (α := Finset α) (β := Finset α)
      liveF (fun A => A ∩ p.uncolored X)
      (fun E => 2 ^ (n - E.card)) (edgeScore p) fun A hA => by
        have hm := Finset.mem_filter.mp hA
        exact residual_term_le_edgeScore (hedges A hm.1).1 (hedges A hm.1).2 hm.2
  exact himage.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (Live p) F) (fun _ _ _ => Nat.zero_le _))

/-- The fixed-budget non-uniform property-B input, in the scaled integral form
used by the tree proof. -/
def BeckFixedBudget (C n r : ℕ) : Prop :=
  ∀ (H : Hypergraph α),
    (∀ E ∈ H, r ≤ E.card) →
    scaledWeight n H ≤ 4 * C * 2 ^ n →
    ∃ R : Finset α, ProperColoring H R

lemma live_parent_of_live_child (p : Partial α) (A : Finset α) (v : α) (b : Bool)
    (h : Live (p.child v b) A) : Live p A := by
  cases b <;> rcases h with h | h
  · left; exact h
  · right; exact h.mono_right (Finset.subset_insert v p.blue)
  · left; exact h.mono_right (Finset.subset_insert v p.red)
  · right; exact h

lemma child_edge_uncolored_le_parent (X A : Finset α) (p : Partial α) (v : α) (b : Bool) :
    (A ∩ (p.child v b).uncolored X).card ≤ (A ∩ p.uncolored X).card := by
  cases b <;> simp [Partial.uncolored, Partial.colored, Partial.child]
  · exact Finset.card_le_card (by intro x hx; simp_all)
  · exact Finset.card_le_card (by intro x hx; simp_all)

lemma parent_edge_uncolored_le_child_add_one {X A : Finset α} {p : Partial α} {v : α}
    (hv : v ∈ p.uncolored X) (b : Bool) :
    (A ∩ p.uncolored X).card ≤ (A ∩ (p.child v b).uncolored X).card + 1 := by
  rw [p.uncolored_child hv]
  rw [← Finset.inter_sdiff_assoc, Finset.sdiff_singleton_eq_erase]
  by_cases hvA : v ∈ A ∩ p.uncolored X
  · exact (Finset.card_erase_add_one hvA).symm.le
  · simp [Finset.erase_eq_of_notMem hvA]

end Residual

end Erdos1027.Tree
