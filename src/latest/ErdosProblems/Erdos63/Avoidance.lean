/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.ExpanderDefs

/-!
# Erdős Problem 63: finite avoidance and ball-growth lemmas

This file isolates the elementary finite-graph bookkeeping used in the
avoidance arguments of Liu--Montgomery.  The quantitative analytic estimates
and the Komlós--Szemerédi expansion hypothesis live in later files.  Here all
cardinality losses are exact: at one growth step the only lost external
neighbors are precisely the neighbors in the forbidden set.

The main definitions are `ballAvoidingFrom`, for balls with a finite set of
initial vertices, `availableExternalNeighborhood`, and `HasLimitedContact`.
The two main outputs are the one-step growth inequality
`card_ballAvoidingFrom_add_card_available_le` and the short-path lemma
`exists_avoiding_path_between_of_large_balls`.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} {I : Type v}
variable {G G' : SimpleGraph V}

/-! ## Balls with a finite initial set -/

/-- The union of the avoiding balls of the vertices of `A`.  A path starting
at `a ∈ A` is allowed to meet the forbidden set at `a`, but nowhere else. -/
noncomputable def ballAvoidingFrom [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (A : Finset V) (r : ℕ) : Finset V := by
  classical
  exact A.biUnion fun a ↦ ballAvoiding G forbidden a r

@[simp] theorem mem_ballAvoidingFrom [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (A : Finset V) (r : ℕ) (y : V) :
    y ∈ ballAvoidingFrom G forbidden A r ↔
      ∃ a ∈ A, ReachWithin G forbidden a r y := by
  classical
  simp [ballAvoidingFrom]

theorem subset_ballAvoidingFrom [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (A : Finset V) (r : ℕ) :
    A ⊆ ballAvoidingFrom G forbidden A r := by
  classical
  intro a ha
  exact (mem_ballAvoidingFrom G forbidden A r a).2
    ⟨a, ha, reachWithin_refl G forbidden a r⟩

@[simp] theorem ballAvoidingFrom_zero [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (A : Finset V) :
    ballAvoidingFrom G forbidden A 0 = A := by
  classical
  ext y
  simp

theorem ballAvoidingFrom_radius_mono [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (A : Finset V) {r s : ℕ} (hrs : r ≤ s) :
    ballAvoidingFrom G forbidden A r ⊆ ballAvoidingFrom G forbidden A s := by
  classical
  intro y hy
  obtain ⟨a, ha, hay⟩ := (mem_ballAvoidingFrom G forbidden A r y).1 hy
  exact (mem_ballAvoidingFrom G forbidden A s y).2
    ⟨a, ha, hay.radius_mono hrs⟩

theorem ballAvoidingFrom_forbidden_anti [Fintype V] (G : SimpleGraph V)
    {X Y : Set V} (hYX : Y ⊆ X) (A : Finset V) (r : ℕ) :
    ballAvoidingFrom G X A r ⊆ ballAvoidingFrom G Y A r := by
  classical
  intro y hy
  obtain ⟨a, ha, hay⟩ := (mem_ballAvoidingFrom G X A r y).1 hy
  exact (mem_ballAvoidingFrom G Y A r y).2
    ⟨a, ha, hay.forbidden_anti hYX⟩

theorem ballAvoidingFrom_mono_graph [Fintype V] (hGG' : G ≤ G')
    (X : Set V) (A : Finset V) (r : ℕ) :
    ballAvoidingFrom G X A r ⊆ ballAvoidingFrom G' X A r := by
  classical
  intro y hy
  obtain ⟨a, ha, hay⟩ := (mem_ballAvoidingFrom G X A r y).1 hy
  exact (mem_ballAvoidingFrom G' X A r y).2
    ⟨a, ha, hay.mono_graph hGG'⟩

/-- Every vertex on a witnessing path is in the same avoiding ball. -/
theorem support_subset_ballAvoiding [Fintype V]
    {X : Set V} {root y : V} {r : ℕ} {p : G.Walk root y}
    (hp : p.IsAvoidingPath X ({root} : Set V)) (hlen : p.length ≤ r) :
    ∀ z ∈ p.support, z ∈ ballAvoiding G X root r := by
  classical
  intro z hz
  rw [mem_ballAvoiding]
  refine ⟨p.takeUntil z hz, ⟨hp.1.takeUntil hz, ?_⟩, ?_⟩
  · intro w hw hwX
    exact hp.2 w (p.support_takeUntil_subset_support hz hw) hwX
  · exact (p.length_takeUntil_le_length hz).trans hlen

/-- Adding a forbidden set which is disjoint from the old ball does not
change that ball.  This is the exact deletion identity used for condition
(A2) in Liu--Montgomery Lemma 3.2. -/
theorem ballAvoidingFrom_union_eq_of_disjoint [Fintype V]
    (G : SimpleGraph V) (X Y : Set V) (A : Finset V) (r : ℕ)
    (hY : ∀ y ∈ ballAvoidingFrom G X A r, y ∉ Y) :
    ballAvoidingFrom G (X ∪ Y) A r = ballAvoidingFrom G X A r := by
  classical
  apply Finset.Subset.antisymm
  · exact ballAvoidingFrom_forbidden_anti G Set.subset_union_left A r
  · intro y hy
    obtain ⟨a, ha, p, hp, hlen⟩ :=
      (mem_ballAvoidingFrom G X A r y).1 hy
    rw [mem_ballAvoidingFrom]
    refine ⟨a, ha, p, ⟨hp.1, ?_⟩, hlen⟩
    intro z hz hzXY
    rcases hzXY with hzX | hzY
    · exact hp.2 z hz hzX
    · have hzball : z ∈ ballAvoidingFrom G X A r :=
        (mem_ballAvoidingFrom G X A r z).2
          ⟨a, ha, (mem_ballAvoiding G X a r z).1
            (support_subset_ballAvoiding hp hlen z hz)⟩
      exact (hY z hzball hzY).elim

/-- Every vertex on a witnessing path from `A` lies in the corresponding
set-ball.  This is the fact that makes adding a new external neighbor preserve
simplicity of the path. -/
theorem support_subset_ballAvoidingFrom [Fintype V]
    {X : Set V} {A : Finset V} {a y : V} {r : ℕ}
    (ha : a ∈ A) {p : G.Walk a y}
    (hp : p.IsAvoidingPath X ({a} : Set V)) (hlen : p.length ≤ r) :
    ∀ z ∈ p.support, z ∈ ballAvoidingFrom G X A r := by
  classical
  intro z hz
  rw [mem_ballAvoidingFrom]
  refine ⟨a, ha, p.takeUntil z hz, ⟨hp.1.takeUntil hz, ?_⟩, ?_⟩
  · intro w hw hwX
    exact hp.2 w (p.support_takeUntil_subset_support hz hw) hwX
  · exact (p.length_takeUntil_le_length hz).trans hlen

/-! ## Available and blocked external neighborhoods -/

/-- External neighbors which do not belong to `forbidden`. -/
noncomputable def availableExternalNeighborhood [Fintype V]
    (G : SimpleGraph V) (forbidden : Set V) (S : Finset V) : Finset V := by
  classical
  exact (externalNeighborhood G S).filter fun x ↦ x ∉ forbidden

/-- External neighbors which are lost because they belong to `forbidden`. -/
noncomputable def blockedExternalNeighborhood [Fintype V]
    (G : SimpleGraph V) (forbidden : Set V) (S : Finset V) : Finset V := by
  classical
  exact (externalNeighborhood G S).filter fun x ↦ x ∈ forbidden

@[simp] theorem mem_availableExternalNeighborhood [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) (x : V) :
    x ∈ availableExternalNeighborhood G X S ↔
      x ∈ externalNeighborhood G S ∧ x ∉ X := by
  classical
  simp [availableExternalNeighborhood]

@[simp] theorem mem_blockedExternalNeighborhood [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) (x : V) :
    x ∈ blockedExternalNeighborhood G X S ↔
      x ∈ externalNeighborhood G S ∧ x ∈ X := by
  classical
  simp [blockedExternalNeighborhood]

@[simp] theorem availableExternalNeighborhood_finset [Fintype V]
    (G : SimpleGraph V) (X S : Finset V) :
    availableExternalNeighborhood G (X : Set V) S =
      externalNeighborhood G S \ X := by
  classical
  ext x
  simp

@[simp] theorem blockedExternalNeighborhood_finset [Fintype V]
    (G : SimpleGraph V) (X S : Finset V) :
    blockedExternalNeighborhood G (X : Set V) S =
      externalNeighborhood G S ∩ X := by
  classical
  ext x
  simp

theorem availableExternalNeighborhood_subset_external [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) :
    availableExternalNeighborhood G X S ⊆ externalNeighborhood G S := by
  classical
  intro x hx
  exact (mem_availableExternalNeighborhood G X S x).1 hx |>.1

theorem blockedExternalNeighborhood_subset_external [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) :
    blockedExternalNeighborhood G X S ⊆ externalNeighborhood G S := by
  classical
  intro x hx
  exact (mem_blockedExternalNeighborhood G X S x).1 hx |>.1

theorem availableExternalNeighborhood_disjoint_blocked [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) :
    Disjoint (availableExternalNeighborhood G X S)
      (blockedExternalNeighborhood G X S) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (mem_availableExternalNeighborhood G X S x).1 hx |>.2
    ((mem_blockedExternalNeighborhood G X S x).1 hy |>.2)

theorem available_union_blocked [Fintype V] (G : SimpleGraph V)
    (X : Set V) (S : Finset V) :
    availableExternalNeighborhood G X S ∪ blockedExternalNeighborhood G X S =
      externalNeighborhood G S := by
  classical
  ext x
  by_cases hx : x ∈ X <;> simp [hx]

theorem card_available_add_card_blocked [Fintype V] (G : SimpleGraph V)
    (X : Set V) (S : Finset V) :
    (availableExternalNeighborhood G X S).card +
        (blockedExternalNeighborhood G X S).card =
      (externalNeighborhood G S).card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (availableExternalNeighborhood_disjoint_blocked G X S),
    available_union_blocked]

/-- If three finite sets are deleted, the blocked external neighbors consist
of vertices in the first two sets and the actually contacted vertices of the
third set. -/
theorem blockedExternalNeighborhood_union_three_subset [Fintype V]
    (G : SimpleGraph V) (X Y Z S : Finset V) :
    blockedExternalNeighborhood G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) S ⊆
      (X ∪ Y) ∪ blockedExternalNeighborhood G (Z : Set V) S := by
  classical
  intro x hx
  obtain ⟨hxN, hxXYZ⟩ :=
    (mem_blockedExternalNeighborhood G
      ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) S x).1 hx
  rcases hxXYZ with (hxX | hxY) | hxZ
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxX)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hxY)
  · exact Finset.mem_union_right _
      ((mem_blockedExternalNeighborhood G (Z : Set V) S x).2 ⟨hxN, hxZ⟩)

theorem card_blockedExternalNeighborhood_union_three_le [Fintype V]
    (G : SimpleGraph V) (X Y Z S : Finset V) :
    (blockedExternalNeighborhood G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) S).card ≤
      X.card + Y.card +
        (blockedExternalNeighborhood G (Z : Set V) S).card := by
  classical
  have hsub := Finset.card_le_card
    (blockedExternalNeighborhood_union_three_subset G X Y Z S)
  have h₁ := Finset.card_union_le X Y
  have h₂ := Finset.card_union_le (X ∪ Y)
    (blockedExternalNeighborhood G (Z : Set V) S)
  omega

theorem availableExternalNeighborhood_disjoint [Fintype V]
    (G : SimpleGraph V) (X : Set V) (S : Finset V) :
    Disjoint (availableExternalNeighborhood G X S) S := by
  classical
  exact (Finset.disjoint_of_subset_left
    (availableExternalNeighborhood_subset_external G X S)
    (externalNeighborhood_disjoint G S))

/-! ## Exact one-step growth -/

/-- An available external neighbor of an avoiding ball is reached in one more
step. -/
theorem availableExternalNeighborhood_subset_ballAvoidingFrom_succ
    [Fintype V] (G : SimpleGraph V) (X : Set V) (A : Finset V) (r : ℕ) :
    availableExternalNeighborhood G X (ballAvoidingFrom G X A r) ⊆
      ballAvoidingFrom G X A (r + 1) := by
  classical
  intro y hy
  obtain ⟨hyN, hyX⟩ := (mem_availableExternalNeighborhood G X _ y).1 hy
  obtain ⟨hyS, x, hxS, hxy⟩ :=
    (mem_externalNeighborhood G (ballAvoidingFrom G X A r) y).1 hyN
  obtain ⟨a, ha, p, hp, hlen⟩ :=
    (mem_ballAvoidingFrom G X A r x).1 hxS
  have hynp : y ∉ p.support := by
    intro hyp
    exact hyS (support_subset_ballAvoidingFrom ha hp hlen y hyp)
  rw [mem_ballAvoidingFrom]
  refine ⟨a, ha, p.concat hxy, ⟨hp.1.concat hynp hxy, ?_⟩, ?_⟩
  · intro z hz hzX
    rw [p.support_concat] at hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hp.2 z hz hzX
    · have hzy : z = y := by simpa using hz
      exact (hyX (hzy ▸ hzX)).elim
  · simpa only [p.length_concat] using Nat.add_le_add_right hlen 1

/-- Exact cardinal bookkeeping for one growth step. -/
theorem card_ballAvoidingFrom_add_card_available_le [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A : Finset V) (r : ℕ) :
    (ballAvoidingFrom G X A r).card +
        (availableExternalNeighborhood G X (ballAvoidingFrom G X A r)).card ≤
      (ballAvoidingFrom G X A (r + 1)).card := by
  classical
  let S := ballAvoidingFrom G X A r
  let T := availableExternalNeighborhood G X S
  have hST : S ∪ T ⊆ ballAvoidingFrom G X A (r + 1) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ballAvoidingFrom_radius_mono G X A (Nat.le_add_right r 1) hy
    · exact availableExternalNeighborhood_subset_ballAvoidingFrom_succ G X A r hy
  have hdisj : Disjoint S T :=
    (availableExternalNeighborhood_disjoint G X S).symm
  simpa [S, T, Finset.card_union_of_disjoint hdisj] using
    Finset.card_le_card hST

/-- If at least `q` external neighbors remain after accounting for the
blocked neighbors, then the next ball gains at least `q` vertices. -/
theorem card_ballAvoidingFrom_add_le_succ_of_external
    [Fintype V] (G : SimpleGraph V) (X : Set V) (A : Finset V)
    (r q : ℕ)
    (h_external : q +
        (blockedExternalNeighborhood G X (ballAvoidingFrom G X A r)).card ≤
      (externalNeighborhood G (ballAvoidingFrom G X A r)).card) :
    (ballAvoidingFrom G X A r).card + q ≤
      (ballAvoidingFrom G X A (r + 1)).card := by
  have hpartition := card_available_add_card_blocked G X
    (ballAvoidingFrom G X A r)
  have hq : q ≤
      (availableExternalNeighborhood G X (ballAvoidingFrom G X A r)).card := by
    omega
  exact (Nat.add_le_add_left hq _).trans
    (card_ballAvoidingFrom_add_card_available_le G X A r)

/-- Limited contact is the exact discrete hypothesis used in an avoidance
growth argument: at radius `r`, at most `k * (r+1)` external neighbors are
blocked. -/
def HasLimitedContact [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (X : Set V) (k : ℕ) : Prop :=
  ∀ r : ℕ,
    (blockedExternalNeighborhood G X (ballAvoidingFrom G X A r)).card ≤
      k * (r + 1)

theorem ballAvoidingFrom_avoids_forbidden [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A : Finset V) (r : ℕ)
    (hAX : ∀ a ∈ A, a ∉ X) :
    ∀ y ∈ ballAvoidingFrom G X A r, y ∉ X := by
  intro y hy
  obtain ⟨a, ha, hay⟩ := (mem_ballAvoidingFrom G X A r y).1 hy
  rcases hay.eq_root_or_not_mem with hya | hyX
  · simpa [hya] using hAX a ha
  · exact hyX

/-- Avoiding balls satisfy the expected semigroup inclusion.  Loop erasure
is needed because concatenating the two witnessing simple paths need not
itself be simple. -/
theorem ballAvoidingFrom_ballAvoidingFrom_subset [Fintype V]
    (G : SimpleGraph V) (W : Set V) (A : Finset V) (r s : ℕ)
    (hAW : ∀ a ∈ A, a ∉ W) :
    ballAvoidingFrom G W (ballAvoidingFrom G W A r) s ⊆
      ballAvoidingFrom G W A (r + s) := by
  classical
  intro y hy
  obtain ⟨z, hzball, q, hq, hqlen⟩ :=
    (mem_ballAvoidingFrom G W (ballAvoidingFrom G W A r) s y).1 hy
  obtain ⟨a, ha, p, hp, hplen⟩ :=
    (mem_ballAvoidingFrom G W A r z).1 hzball
  have hzW : z ∉ W := ballAvoidingFrom_avoids_forbidden G W A r hAW z hzball
  have hpempty : p.Avoids W (∅ : Set V) := by
    intro v hv hvW
    have hva : v = a := Set.mem_singleton_iff.1 (hp.2 v hv hvW)
    exact (hAW a ha (hva ▸ hvW)).elim
  have hqempty : q.Avoids W (∅ : Set V) := by
    intro v hv hvW
    have hvz : v = z := Set.mem_singleton_iff.1 (hq.2 v hv hvW)
    exact (hzW (hvz ▸ hvW)).elim
  let w : G.Walk a y := p.append q
  have hwempty : w.Avoids W (∅ : Set V) := by
    intro v hv hvW
    have hv' : v ∈ p.support ∨ v ∈ q.support := by
      simpa only [w, Walk.mem_support_append_iff] using hv
    rcases hv' with hvp | hvq
    · exact hpempty v hvp hvW
    · exact hqempty v hvq hvW
  rw [mem_ballAvoidingFrom]
  refine ⟨a, ha, w.bypass, ⟨w.bypass_isPath, ?_⟩, ?_⟩
  · exact (hwempty.of_support_subset w.support_bypass_subset_support).mono_permitted
      (by intro z hz; exact hz.elim)
  · calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = p.length + q.length := by simp [w]
      _ ≤ r + s := Nat.add_le_add hplen hqlen

/-- Blocked external neighbors are monotone with the explored set provided
the larger explored set still avoids the blocking set. -/
theorem blockedExternalNeighborhood_subset_of_subset_of_avoids [Fintype V]
    (G : SimpleGraph V) (X : Set V) {S T : Finset V}
    (hST : S ⊆ T) (hTX : ∀ x ∈ T, x ∉ X) :
    blockedExternalNeighborhood G X S ⊆
      blockedExternalNeighborhood G X T := by
  classical
  intro x hx
  obtain ⟨hxN, hxX⟩ := (mem_blockedExternalNeighborhood G X S x).1 hx
  obtain ⟨hxS, y, hyS, hyx⟩ := (mem_externalNeighborhood G S x).1 hxN
  rw [mem_blockedExternalNeighborhood, mem_externalNeighborhood]
  exact ⟨⟨fun hxT ↦ hTX x hxT hxX, y, hST hyS, hyx⟩, hxX⟩

/-- Limited contact defined using the larger `G-Z` balls controls the contact
of balls which additionally avoid `X` and `Y`.  This is the source's passage
from condition (A3) to the loss term in its growth estimate. -/
theorem HasLimitedContact.card_blocked_union_three_le [Fintype V]
    (G : SimpleGraph V) (A X Y Z : Finset V) {contact : ℕ}
    (hAZ : ∀ a ∈ A, a ∉ Z)
    (hcontact : HasLimitedContact G A (Z : Set V) contact) (r : ℕ) :
    (blockedExternalNeighborhood G (Z : Set V)
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r)).card ≤
      contact * (r + 1) := by
  let F : Set V := (X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)
  have hZF : (Z : Set V) ⊆ F := by
    intro z hz
    exact Or.inr hz
  have hballs : ballAvoidingFrom G F A r ⊆
      ballAvoidingFrom G (Z : Set V) A r :=
    ballAvoidingFrom_forbidden_anti G hZF A r
  have hblocked := blockedExternalNeighborhood_subset_of_subset_of_avoids
    G (Z : Set V) hballs
      (ballAvoidingFrom_avoids_forbidden G (Z : Set V) A r hAZ)
  exact (Finset.card_le_card hblocked).trans (hcontact r)

theorem HasLimitedContact.card_add_le_succ [Fintype V]
    {A : Finset V} {X : Set V} {k r q : ℕ}
    (hcontact : HasLimitedContact G A X k)
    (h_external : q + k * (r + 1) ≤
      (externalNeighborhood G (ballAvoidingFrom G X A r)).card) :
    (ballAvoidingFrom G X A r).card + q ≤
      (ballAvoidingFrom G X A (r + 1)).card := by
  apply card_ballAvoidingFrom_add_le_succ_of_external G X A r q
  exact (Nat.add_le_add_left (hcontact r) q).trans h_external

/-- Direct one-step avoidance growth from the exact Liu--Montgomery expander
property.  The real inequality `hbudget` is the numerical bookkeeping: after
paying for every blocked external neighbor, it leaves `q` new vertices. -/
theorem IsLMExpander.card_ballAvoidingFrom_add_le_succ [Fintype V]
    {epsilon₁ k : ℝ} (hexp : IsLMExpander G epsilon₁ k)
    (X : Set V) (A : Finset V) (r q : ℕ)
    (hlower : k / 2 ≤ (ballAvoidingFrom G X A r).card)
    (hupper : ((ballAvoidingFrom G X A r).card : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hbudget : ((q +
        (blockedExternalNeighborhood G X (ballAvoidingFrom G X A r)).card : ℕ) : ℝ) ≤
      expansionEpsilon epsilon₁ k (ballAvoidingFrom G X A r).card *
        (ballAvoidingFrom G X A r).card) :
    (ballAvoidingFrom G X A r).card + q ≤
      (ballAvoidingFrom G X A (r + 1)).card := by
  have hN := hexp.expands hlower hupper
  change expansionEpsilon epsilon₁ k (ballAvoidingFrom G X A r).card *
      ((ballAvoidingFrom G X A r).card : ℝ) ≤
        ((externalNeighborhood G (ballAvoidingFrom G X A r)).card : ℝ) at hN
  apply card_ballAvoidingFrom_add_le_succ_of_external G X A r q
  exact_mod_cast hbudget.trans hN

/-- Limited contact plus the exact expander field reduces a growth step to a
single explicit real cardinal inequality. -/
theorem IsLMExpander.card_ballAvoidingFrom_add_le_succ_of_limitedContact
    [Fintype V] {epsilon₁ k : ℝ} (hexp : IsLMExpander G epsilon₁ k)
    {X : Set V} {A : Finset V} {contact r q : ℕ}
    (hcontact : HasLimitedContact G A X contact)
    (hlower : k / 2 ≤ (ballAvoidingFrom G X A r).card)
    (hupper : ((ballAvoidingFrom G X A r).card : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hbudget : ((q + contact * (r + 1) : ℕ) : ℝ) ≤
      expansionEpsilon epsilon₁ k (ballAvoidingFrom G X A r).card *
        (ballAvoidingFrom G X A r).card) :
    (ballAvoidingFrom G X A r).card + q ≤
      (ballAvoidingFrom G X A (r + 1)).card := by
  apply hexp.card_ballAvoidingFrom_add_le_succ X A r q hlower hupper
  have hnat : q +
      (blockedExternalNeighborhood G X (ballAvoidingFrom G X A r)).card ≤
        q + contact * (r + 1) := Nat.add_le_add_left (hcontact r) q
  have hreal : ((q +
      (blockedExternalNeighborhood G X (ballAvoidingFrom G X A r)).card : ℕ) : ℝ) ≤
        ((q + contact * (r + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hbudget

/-- Source-shaped one-step form of the loss estimate in Liu--Montgomery
Lemma 3.2.  `X` and `Y` are paid for globally, while only the external
neighbors actually contacting `Z` are paid for. -/
theorem IsLMExpander.card_ballAvoidingFrom_union_three_add_le_succ
    [Fintype V] {epsilon₁ k : ℝ} (hexp : IsLMExpander G epsilon₁ k)
    (A X Y Z : Finset V) (r q contact : ℕ)
    (hlower : k / 2 ≤
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card)
    (hupper : ((ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hcontact : (blockedExternalNeighborhood G (Z : Set V)
        (ballAvoidingFrom G
          ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r)).card ≤ contact)
    (hbudget : ((q + X.card + Y.card + contact : ℕ) : ℝ) ≤
      expansionEpsilon epsilon₁ k
          (ballAvoidingFrom G
            ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card *
        (ballAvoidingFrom G
          ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card) :
    (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card + q ≤
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A (r + 1)).card := by
  let F : Set V := (X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)
  apply hexp.card_ballAvoidingFrom_add_le_succ F A r q hlower hupper
  have hblocked :
      (blockedExternalNeighborhood G F (ballAvoidingFrom G F A r)).card ≤
        X.card + Y.card + contact := by
    dsimp [F]
    exact (card_blockedExternalNeighborhood_union_three_le G X Y Z
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r)).trans
      (Nat.add_le_add_left hcontact (X.card + Y.card))
  have hnat : q +
      (blockedExternalNeighborhood G F (ballAvoidingFrom G F A r)).card ≤
        q + X.card + Y.card + contact := by omega
  have hreal : ((q +
      (blockedExternalNeighborhood G F (ballAvoidingFrom G F A r)).card : ℕ) : ℝ) ≤
        ((q + X.card + Y.card + contact : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hbudget

/-- Fully limited-contact form of the preceding three-deletion growth step. -/
theorem IsLMExpander.card_ballAvoidingFrom_union_three_add_le_succ_of_limitedContact
    [Fintype V] {epsilon₁ k : ℝ} (hexp : IsLMExpander G epsilon₁ k)
    (A X Y Z : Finset V) (r q contact : ℕ)
    (hAZ : ∀ a ∈ A, a ∉ Z)
    (hcontact : HasLimitedContact G A (Z : Set V) contact)
    (hlower : k / 2 ≤
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card)
    (hupper : ((ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card : ℝ) ≤
      (Fintype.card V : ℝ) / 2)
    (hbudget : ((q + X.card + Y.card + contact * (r + 1) : ℕ) : ℝ) ≤
      expansionEpsilon epsilon₁ k
          (ballAvoidingFrom G
            ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card *
        (ballAvoidingFrom G
          ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card) :
    (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A r).card + q ≤
      (ballAvoidingFrom G
        ((X : Set V) ∪ (Y : Set V) ∪ (Z : Set V)) A (r + 1)).card := by
  exact hexp.card_ballAvoidingFrom_union_three_add_le_succ A X Y Z r q
    (contact * (r + 1)) hlower hupper
      (HasLimitedContact.card_blocked_union_three_le G A X Y Z hAZ hcontact r) hbudget

/-- Iteration of an additive lower bound on successive balls. -/
theorem card_ballAvoidingFrom_add_mul_le [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A : Finset V) (q : ℕ)
    {r s : ℕ} (hrs : r ≤ s)
    (hgrow : ∀ i : ℕ, r ≤ i →
      (ballAvoidingFrom G X A i).card + q ≤
        (ballAvoidingFrom G X A (i + 1)).card) :
    (ballAvoidingFrom G X A r).card + (s - r) * q ≤
      (ballAvoidingFrom G X A s).card := by
  induction s, hrs using Nat.le_induction with
  | base => simp
  | succ s hrs ih =>
      have hs : r ≤ s := hrs
      have hstep := hgrow s hs
      rw [Nat.succ_sub hs, Nat.succ_mul, ← Nat.add_assoc]
      exact (Nat.add_le_add_right ih q).trans hstep

/-- Iteration of a multiplicative lower bound on successive balls. -/
theorem pow_mul_card_ballAvoidingFrom_le [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A : Finset V) (c : ℕ)
    {r s : ℕ} (hrs : r ≤ s)
    (hgrow : ∀ i : ℕ, r ≤ i →
      c * (ballAvoidingFrom G X A i).card ≤
        (ballAvoidingFrom G X A (i + 1)).card) :
    c ^ (s - r) * (ballAvoidingFrom G X A r).card ≤
      (ballAvoidingFrom G X A s).card := by
  induction s, hrs using Nat.le_induction with
  | base => simp
  | succ s hrs ih =>
      have hs : r ≤ s := hrs
      have hstep := hgrow s hs
      rw [Nat.succ_sub hs, pow_succ]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Nat.mul_le_mul_left c ih).trans hstep

/-! ## Connecting two large avoiding balls -/

/-- Extend an avoiding connector by one edge at each end.  Since the middle
path avoids both roots, the result remains simple; since the roots themselves
avoid `W`, the result avoids `W` everywhere.  In particular, the roots occur
only as the two endpoints of the resulting simple path. -/
theorem extend_avoiding_path_to_roots (G : SimpleGraph V) (W : Set V)
    {x y a b : V} (hxy : x ≠ y) (hxW : x ∉ W) (hyW : y ∉ W)
    (hxa : G.Adj x a) (hby : G.Adj b y) {p : G.Walk a b}
    (hp : p.IsAvoidingPath (W ∪ ({x, y} : Set V)) (∅ : Set V)) :
    ∃ q : G.Walk x y,
      q.IsAvoidingPath W (∅ : Set V) ∧ q.length = p.length + 2 := by
  have hx_forbidden : x ∈ W ∪ ({x, y} : Set V) := by simp
  have hy_forbidden : y ∈ W ∪ ({x, y} : Set V) := by simp
  have hx_support : x ∉ p.support := by
    intro hxp
    exact hp.2 x hxp hx_forbidden
  have hy_support : y ∉ p.support := by
    intro hyp
    exact hp.2 y hyp hy_forbidden
  let q₀ : G.Walk x b := Walk.cons hxa p
  have hq₀_path : q₀.IsPath := hp.1.cons hx_support
  have hyq₀ : y ∉ q₀.support := by
    intro hy
    have hy' : y = x ∨ y ∈ p.support := by simpa only [q₀, Walk.support_cons,
      List.mem_cons] using hy
    rcases hy' with hyx | hyp
    · exact hxy hyx.symm
    · exact hy_support hyp
  let q : G.Walk x y := q₀.concat hby
  refine ⟨q, ⟨hq₀_path.concat hyq₀ hby, ?_⟩, ?_⟩
  · intro z hz hzW
    have hz' : (z = x ∨ z ∈ p.support) ∨ z = y := by
      simpa only [q, q₀, Walk.support_concat, Walk.support_cons, List.mem_append,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hz
    rcases hz' with (hzx | hzp) | hzy
    · exact (hxW (hzx ▸ hzW)).elim
    · exact hp.2 z hzp (Or.inl hzW)
    · exact (hyW (hzy ▸ hzW)).elim
  · simp [q, q₀, Nat.add_assoc]

private theorem exists_common_of_card_add_gt [Fintype V]
    (S T : Finset V) (hcard : Fintype.card V < S.card + T.card) :
    ∃ z ∈ S, z ∈ T := by
  classical
  by_contra h
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    exact h ⟨z, hzS, hzT⟩
  have hu := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ] at hu
  omega

/-- If two set-balls meet, their witnessing paths concatenate to a short
walk, and erasing loops gives a short simple path.  Forbidden vertices can
only be the two selected initial vertices. -/
theorem exists_avoiding_path_between_of_common_ball [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A B : Finset V) (r s : ℕ)
    {z : V} (hzA : z ∈ ballAvoidingFrom G X A r)
    (hzB : z ∈ ballAvoidingFrom G X B s) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath X ({a, b} : Set V) ∧ p.length ≤ r + s := by
  classical
  obtain ⟨a, ha, p, hp, hplen⟩ :=
    (mem_ballAvoidingFrom G X A r z).1 hzA
  obtain ⟨b, hb, q, hq, hqlen⟩ :=
    (mem_ballAvoidingFrom G X B s z).1 hzB
  let w : G.Walk a b := p.append q.reverse
  have hwavoids : w.Avoids X ({a, b} : Set V) := by
    intro x hx hxX
    have hx' : x ∈ p.support ∨ x ∈ q.reverse.support := by
      simpa only [w, Walk.mem_support_append_iff] using hx
    rcases hx' with hx | hx
    · have hxa := hp.2 x hx hxX
      have hxa' : x = a := Set.mem_singleton_iff.1 hxa
      simp [hxa']
    · have hxq : x ∈ q.support := by
        simpa [q.support_reverse] using hx
      have hxb := hq.2 x hxq hxX
      have hxb' : x = b := Set.mem_singleton_iff.1 hxb
      simp [hxb']
  refine ⟨a, ha, b, hb, w.bypass, ⟨w.bypass_isPath, ?_⟩, ?_⟩
  · exact hwavoids.of_support_subset w.support_bypass_subset_support
  · calc
      w.bypass.length ≤ w.length := w.length_bypass_le_length
      _ = p.length + q.length := by simp [w]
      _ ≤ r + s := Nat.add_le_add hplen hqlen

/-- Pigeonhole form of the connection lemma: balls whose cardinalities sum
to more than the whole vertex set must meet. -/
theorem exists_avoiding_path_between_of_large_balls [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A B : Finset V) (r s : ℕ)
    (hcard : Fintype.card V <
      (ballAvoidingFrom G X A r).card +
        (ballAvoidingFrom G X B s).card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath X ({a, b} : Set V) ∧ p.length ≤ r + s := by
  obtain ⟨z, hzA, hzB⟩ := exists_common_of_card_add_gt
    (ballAvoidingFrom G X A r) (ballAvoidingFrom G X B s) hcard
  exact exists_avoiding_path_between_of_common_ball G X A B r s hzA hzB

/-- When the two initial sets themselves avoid `X`, the connecting path has
no vertex at all in `X`. -/
theorem exists_path_between_avoiding_of_large_balls [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A B : Finset V) (r s : ℕ)
    (hAX : ∀ a ∈ A, a ∉ X) (hBX : ∀ b ∈ B, b ∉ X)
    (hcard : Fintype.card V <
      (ballAvoidingFrom G X A r).card +
        (ballAvoidingFrom G X B s).card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath X (∅ : Set V) ∧ p.length ≤ r + s := by
  obtain ⟨a, ha, b, hb, p, hp, hlen⟩ :=
    exists_avoiding_path_between_of_large_balls G X A B r s hcard
  refine ⟨a, ha, b, hb, p, ⟨hp.1, ?_⟩, hlen⟩
  intro z hz hzX
  have hzab : z = a ∨ z = b := by simpa using hp.2 z hz hzX
  rcases hzab with hza | hzb
  · exact (hAX a ha (hza ▸ hzX)).elim
  · exact (hBX b hb (hzb ▸ hzX)).elim

/-- The usual more-than-half formulation of the avoiding connection lemma. -/
theorem exists_path_between_avoiding_of_balls_more_than_half [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A B : Finset V) (r s : ℕ)
    (hAX : ∀ a ∈ A, a ∉ X) (hBX : ∀ b ∈ B, b ∉ X)
    (hA : Fintype.card V < 2 * (ballAvoidingFrom G X A r).card)
    (hB : Fintype.card V < 2 * (ballAvoidingFrom G X B s).card) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath X (∅ : Set V) ∧ p.length ≤ r + s := by
  apply exists_path_between_avoiding_of_large_balls G X A B r s hAX hBX
  omega

/-- A lower bound on the length of every avoiding path forces the two balls
to be disjoint.  This is the elementary disjoint-ball step used in the
many-simultaneous-expansions argument. -/
theorem disjoint_ballAvoidingFrom_of_no_short_path [Fintype V]
    (G : SimpleGraph V) (X : Set V) (A B : Finset V) (r s : ℕ)
    (hfar : ∀ a ∈ A, ∀ b ∈ B, ∀ p : G.Walk a b,
      p.IsAvoidingPath X ({a, b} : Set V) → r + s < p.length) :
    Disjoint (ballAvoidingFrom G X A r) (ballAvoidingFrom G X B s) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzA hzB
  obtain ⟨a, ha, b, hb, p, hp, hlen⟩ :=
    exists_avoiding_path_between_of_common_ball G X A B r s hzA hzB
  exact (Nat.not_lt_of_ge hlen) (hfar a ha b hb p hp)

/-! ## Neighborhood unions and deletion losses -/

theorem externalNeighborhood_biUnion_subset [Fintype V]
    (G : SimpleGraph V) (J : Finset I) (S : I → Finset V) :
    externalNeighborhood G (J.biUnion S) ⊆
      J.biUnion fun i ↦ externalNeighborhood G (S i) := by
  classical
  intro y hy
  obtain ⟨hyJ, x, hxJ, hxy⟩ :=
    (mem_externalNeighborhood G (J.biUnion S) y).1 hy
  obtain ⟨i, hiJ, hxi⟩ := Finset.mem_biUnion.1 hxJ
  rw [Finset.mem_biUnion]
  refine ⟨i, hiJ, (mem_externalNeighborhood G (S i) y).2 ⟨?_, x, hxi, hxy⟩⟩
  intro hyi
  exact hyJ (Finset.mem_biUnion.2 ⟨i, hiJ, hyi⟩)

theorem availableExternalNeighborhood_biUnion_subset [Fintype V]
    (G : SimpleGraph V) (X : Set V)
    (J : Finset I) (S : I → Finset V) :
    availableExternalNeighborhood G X (J.biUnion S) ⊆
      J.biUnion fun i ↦ availableExternalNeighborhood G X (S i) := by
  classical
  intro y hy
  obtain ⟨hyN, hyX⟩ :=
    (mem_availableExternalNeighborhood G X (J.biUnion S) y).1 hy
  obtain ⟨i, hiJ, hyi⟩ := Finset.mem_biUnion.1
    (externalNeighborhood_biUnion_subset G J S hyN)
  exact Finset.mem_biUnion.2
    ⟨i, hiJ, (mem_availableExternalNeighborhood G X (S i) y).2 ⟨hyi, hyX⟩⟩

theorem card_availableExternalNeighborhood_biUnion_le [Fintype V]
    (G : SimpleGraph V) (X : Set V)
    (J : Finset I) (S : I → Finset V) :
    (availableExternalNeighborhood G X (J.biUnion S)).card ≤
      ∑ i ∈ J, (availableExternalNeighborhood G X (S i)).card := by
  classical
  exact (Finset.card_le_card
    (availableExternalNeighborhood_biUnion_subset G X J S)).trans
      Finset.card_biUnion_le

theorem card_biUnion_eq_sum_card {J : Finset I} {S : I → Finset V}
    (hdisj : (J : Set I).PairwiseDisjoint S) :
    (J.biUnion S).card = ∑ i ∈ J, (S i).card := by
  classical
  exact Finset.card_biUnion hdisj

/-- Restoring two deleted finite sets costs at most their total cardinality in
the available external neighborhood.  This is the precise set-theoretic
decomposition behind the neighborhood estimate in Liu--Montgomery Claim 3.8.
-/
theorem availableExternalNeighborhood_subset_of_restore [Fintype V]
    (G : SimpleGraph V) (X : Set V) (B C S : Finset V) :
    availableExternalNeighborhood G X S ⊆
      (availableExternalNeighborhood G
        (X ∪ (B : Set V) ∪ (C : Set V)) S ∪ B) ∪ C := by
  classical
  intro y hy
  obtain ⟨hyN, hyX⟩ := (mem_availableExternalNeighborhood G X S y).1 hy
  by_cases hyC : y ∈ C
  · exact Finset.mem_union_right _ hyC
  by_cases hyB : y ∈ B
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hyB)
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [mem_availableExternalNeighborhood]
    exact ⟨hyN, by simp [hyX, hyB, hyC]⟩

theorem card_availableExternalNeighborhood_restore_le [Fintype V]
    (G : SimpleGraph V) (X : Set V) (B C S : Finset V) :
    (availableExternalNeighborhood G X S).card ≤
      (availableExternalNeighborhood G
        (X ∪ (B : Set V) ∪ (C : Set V)) S).card + B.card + C.card := by
  classical
  have hsub := Finset.card_le_card
    (availableExternalNeighborhood_subset_of_restore G X B C S)
  have h₁ := Finset.card_union_le
    (availableExternalNeighborhood G (X ∪ (B : Set V) ∪ (C : Set V)) S) B
  have h₂ := Finset.card_union_le
    (availableExternalNeighborhood G (X ∪ (B : Set V) ∪ (C : Set V)) S ∪ B) C
  omega

end Erdos63
