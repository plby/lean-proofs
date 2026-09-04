/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Adjusters
import ErdosProblems.Erdos63.AvoidanceDeep

/-!
# Erdős Problem 63: concretely joining length adjusters

This file supplies the graph-theoretic join in Liu--Montgomery Lemma 4.7.
Avoiding balls are grown from the union of both ends of each adjuster while
only the small cores are deleted.  A minimum connector determines which end
was hit on each side; swapping the adjusters makes those hit ends the
discarded left ends.  Paths inside the selected expansions extend the
connection to the left roots, and the resulting path is spliced between an
adjustable route in each input adjuster.

The public results take the actual avoiding-ball inequality and construct the
joining path and the `AdjusterJoinRoutes` certificate.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

universe u

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V}

namespace Adjuster

variable {D m m' k : ℕ}

/-- Increase the radius allowed at both ends without changing any vertices
or any of the adjustable routes. -/
noncomputable def widenRadius (A : Adjuster G D m k) (hmm' : m ≤ m') :
    Adjuster G D m' k :=
  A.radiusMono hmm'

@[simp] theorem widenRadius_leftRoot (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').leftRoot = A.leftRoot := rfl

@[simp] theorem widenRadius_rightRoot (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').rightRoot = A.rightRoot := rfl

@[simp] theorem widenRadius_core (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').core = A.core := rfl

@[simp] theorem widenRadius_verts (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').verts = A.verts := by
  simpa [widenRadius] using A.radiusMono_verts hmm'

@[simp] theorem widenRadius_leftEnd_verts
    (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').leftEnd.verts = A.leftEnd.verts := rfl

@[simp] theorem widenRadius_rightEnd_verts
    (A : Adjuster G D m k) (hmm' : m ≤ m') :
    (A.widenRadius hmm').rightEnd.verts = A.rightEnd.verts := rfl

/-- Shrink both end expansions to a common positive order while leaving the
roots, core, and all adjustable routes unchanged.  In particular, every
vertex of the shrunk adjuster was already a vertex of the original one.

This is the final bookkeeping operation in the protected-set form of
Lemma 4.7: connections are made at an inflated end order, and only the two
surviving ends are reduced to the order appearing in the conclusion. -/
theorem exists_shrinkEnds_subset
    {largeOrder target radius length : ℕ}
    (A : Adjuster G largeOrder radius length)
    (htarget : 0 < target) (hle : target ≤ largeOrder) :
    ∃ A' : Adjuster G target radius length,
      A'.core = A.core ∧ A'.leftRoot = A.leftRoot ∧
        A'.rightRoot = A.rightRoot ∧ A'.verts ⊆ A.verts := by
  let originalDecEq : DecidableEq V := inferInstance
  classical
  let : DecidableEq V := originalDecEq
  obtain ⟨left, hleft⟩ := A.leftEnd.proposition3_10 htarget hle
  obtain ⟨right, hright⟩ := A.rightEnd.proposition3_10 htarget hle
  let A' : Adjuster G target radius length :=
    A.replaceEnds left right
      (A.core_disjoint_left.mono_right hleft)
      (A.core_disjoint_right.mono_right hright)
      (A.ends_disjoint.mono hleft hright)
      le_rfl
  refine ⟨A', rfl, rfl, rfl, ?_⟩
  intro v hv
  change v ∈ left.verts ∪ right.verts ∪ A.core at hv
  change v ∈ A.leftEnd.verts ∪ A.rightEnd.verts ∪ A.core
  simp only [Finset.mem_union] at hv ⊢
  rcases hv with (hvLeft | hvRight) | hvCore
  · exact Or.inl (Or.inl (hleft hvLeft))
  · exact Or.inl (Or.inr (hright hvRight))
  · exact Or.inr hvCore

end Adjuster

/-! ## A root connector obtained from the two discarded expansions -/

/-- A walk supported inside a set disjoint from `X` avoids `X` altogether. -/
private theorem avoids_of_supportsIn_disjoint {x y : V} {p : G.Walk x y}
    {S : Finset V} {X : Set V} (hp : ∀ z ∈ p.support, z ∈ S)
    (hSX : Disjoint (S : Set V) X) : p.Avoids X ∅ := by
  intro z hz hzX
  have hzS : z ∈ (S : Set V) := hp z hz
  exact (Set.disjoint_left.1 hSX hzS hzX).elim

/-- The path returned by the avoiding-ball connector avoids the forbidden
set altogether when its two selected endvertices do not belong to that set. -/
private theorem connector_avoids_empty {a b : V} {p : G.Walk a b}
    {X : Set V} (hp : p.Avoids X ({a, b} : Set V))
    (ha : a ∉ X) (hb : b ∉ X) : p.Avoids X ∅ := by
  intro z hz hzX
  have hzab := hp z hz hzX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzab
  rcases hzab with rfl | rfl
  · exact (ha hzX).elim
  · exact (hb hzX).elim

/-- Connect the roots of two vertex expansions using an avoiding path between
their vertex sets.  Loop erasure is used only after concatenation, so the
result is a genuine path and retains the required avoidance and length bound. -/
theorem exists_root_connector_of_avoiding_path
    {x y a b : V} {D₁ D₂ m₁ m₂ t : ℕ} {X : Set V}
    (E : VertexExpansion G x D₁ m₁) (F : VertexExpansion G y D₂ m₂)
    (ha : a ∈ E.verts) (hb : b ∈ F.verts)
    (hEX : Disjoint (E.verts : Set V) X)
    (hFX : Disjoint (F.verts : Set V) X)
    (p : G.Walk a b) (hp : p.IsAvoidingPath X ({a, b} : Set V))
    (hplen : p.length ≤ t) :
    ∃ q : G.Walk x y,
      q.IsPath ∧ q.Avoids X ∅ ∧ q.length ≤ m₁ + t + m₂ := by
  classical
  obtain ⟨px, hpx, hpxlen, hpxsupport⟩ := E.exists_path ha
  obtain ⟨py, hpy, hpylen, hpysupport⟩ := F.exists_path hb
  have haX : a ∉ X := fun ha' ↦
    Set.disjoint_left.1 hEX (by exact ha) ha'
  have hbX : b ∉ X := fun hb' ↦
    Set.disjoint_left.1 hFX (by exact hb) hb'
  have hpxavoid : px.Avoids X ∅ :=
    avoids_of_supportsIn_disjoint hpxsupport hEX
  have hpyavoid : py.Avoids X ∅ :=
    avoids_of_supportsIn_disjoint hpysupport hFX
  have hpavoid : p.Avoids X ∅ := connector_avoids_empty hp.2 haX hbX
  let w : G.Walk x y := (px.append p).append py.reverse
  have hwavoid : w.Avoids X ∅ := by
    intro z hz hzX
    simp only [w, Walk.mem_support_append_iff] at hz
    rcases hz with (hz | hz) | hz
    · exact hpxavoid z hz hzX
    · exact hpavoid z hz hzX
    · exact hpyavoid.reverse z hz hzX
  refine ⟨w.bypass, w.bypass_isPath,
    hwavoid.of_support_subset w.support_bypass_subset_support, ?_⟩
  calc
    w.bypass.length ≤ w.length := w.length_bypass_le_length
    _ = px.length + p.length + py.length := by simp [w, Walk.length_append]
    _ ≤ m₁ + t + m₂ := by omega

/-- Avoiding balls whose sizes sum to more than the order of the graph yield
a short path between the two expansion roots. -/
theorem exists_root_connector_of_large_balls [Fintype V]
    {x y : V} {D₁ D₂ m₁ m₂ r s : ℕ} {X : Set V}
    (E : VertexExpansion G x D₁ m₁) (F : VertexExpansion G y D₂ m₂)
    (hEX : Disjoint (E.verts : Set V) X)
    (hFX : Disjoint (F.verts : Set V) X)
    (hlarge : Fintype.card V <
      (ballAvoidingFrom G X E.verts r).card +
        (ballAvoidingFrom G X F.verts s).card) :
    ∃ q : G.Walk x y,
      q.IsPath ∧ q.Avoids X ∅ ∧ q.length ≤ m₁ + (r + s) + m₂ := by
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_large_balls G X E.verts F.verts r s hlarge
  exact exists_root_connector_of_avoiding_path E F ha hb hEX hFX p hp hplen

/-! ## Variable-rate multiplicative growth schedules -/

/-- A finite numerical certificate that the LM expansion profile grows a
`D`-vertex set past half of an `N`-vertex graph despite deletion of at most
`workspace` vertices.  The increments may vary with the round.  This is the
Lean form of the multiplicative calculation in Lemma 3.4; in particular it
does not demand a fixed additive increment large enough to cross half the
graph in logarithmically many rounds. -/
structure LMConnectorSchedule (epsilon kappa : ℝ) (N D workspace : ℕ) where
  rounds : ℕ
  lower : ℕ → ℕ
  increment : ℕ → ℕ
  lower_zero : lower 0 ≤ D
  lower_mono : Monotone lower
  seed : kappa / 2 ≤ (lower 0 : ℝ)
  step_target : ∀ i : ℕ, i < rounds →
    lower (i + 1) ≤ lower i + increment i
  rate : ∀ i : ℕ, i < rounds → ∀ s : ℕ,
    lower i ≤ s → s ≤ N / 2 →
      (((workspace + increment i : ℕ) : ℝ) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ))
  reaches_half : N / 2 + 1 ≤ lower rounds

namespace LMConnectorSchedule

/-- A schedule is realized by every avoiding ball whose initial set has the
certified order and whose deleted set is within the workspace budget. -/
theorem half_le_ball [Fintype V]
    {epsilon kappa : ℝ} {N D workspace : ℕ}
    (S : LMConnectorSchedule epsilon kappa N D workspace)
    (hexp : IsLMExpander G epsilon kappa)
    (hN : Fintype.card V = N) (W A : Finset V)
    (hAcard : A.card = D) (hW : W.card ≤ workspace) :
    N / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) A S.rounds).card := by
  let cap := N / 2 + 1
  have hind : ∀ i : ℕ, i ≤ S.rounds →
      min (S.lower i) cap ≤
        (ballAvoidingFrom G (W : Set V) A i).card := by
    intro i hi
    induction i with
    | zero =>
        have hAin := Finset.card_le_card
          (subset_ballAvoidingFrom G (W : Set V) A 0)
        calc
          min (S.lower 0) cap ≤ S.lower 0 := min_le_left _ _
          _ ≤ D := S.lower_zero
          _ = A.card := hAcard.symm
          _ ≤ (ballAvoidingFrom G (W : Set V) A 0).card := hAin
    | succ i ih =>
        have hi' : i < S.rounds := by omega
        let current := ballAvoidingFrom G (W : Set V) A i
        let next := ballAvoidingFrom G (W : Set V) A (i + 1)
        by_cases hcap : cap ≤ current.card
        · have hmono : current.card ≤ next.card := by
            exact Finset.card_le_card <|
              ballAvoidingFrom_radius_mono G (W : Set V) A (Nat.le_succ i)
          exact (min_le_right _ cap).trans (hcap.trans hmono)
        · have hcurrentUpper : current.card ≤ N / 2 := by
            dsimp [cap] at hcap
            omega
          have hlowCurrent : S.lower i ≤ current.card := by
            have hih := ih (by omega)
            dsimp [current]
            by_cases hlowCap : S.lower i ≤ cap
            · simpa [min_eq_left hlowCap] using hih
            · have hcapLow : cap ≤ S.lower i := Nat.le_of_not_ge hlowCap
              have : cap ≤ current.card := by
                simpa [min_eq_right hcapLow, current] using hih
              exact (hcap this).elim
          have hseed : kappa / 2 ≤ (current.card : ℝ) := by
            have hzeroi : S.lower 0 ≤ S.lower i := S.lower_mono (Nat.zero_le i)
            exact S.seed.trans (by exact_mod_cast hzeroi.trans hlowCurrent)
          have hupper : (current.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
            have hcast : (current.card : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
              exact_mod_cast hcurrentUpper
            rw [hN]
            exact hcast.trans Nat.cast_div_le
          have hblocked :
              (blockedExternalNeighborhood G (W : Set V) current).card ≤ W.card :=
            Finset.card_le_card (blockedExternalNeighborhood_subset_deleted G W current)
          have hnat : S.increment i +
              (blockedExternalNeighborhood G (W : Set V) current).card ≤
                workspace + S.increment i := by omega
          have hreal : ((S.increment i +
              (blockedExternalNeighborhood G (W : Set V) current).card : ℕ) : ℝ) ≤
                ((workspace + S.increment i : ℕ) : ℝ) := by
            exact_mod_cast hnat
          have hbudget := hreal.trans <|
            S.rate i hi' current.card hlowCurrent hcurrentUpper
          have hstep : current.card + S.increment i ≤ next.card := by
            dsimp [current, next]
            exact hexp.card_ballAvoidingFrom_add_le_succ
              (W : Set V) A i (S.increment i) hseed hupper hbudget
          have htarget : S.lower (i + 1) ≤ next.card :=
            (S.step_target i hi').trans
              ((Nat.add_le_add_right hlowCurrent (S.increment i)).trans hstep)
          exact (min_le_left _ cap).trans htarget
  have hlast := hind S.rounds le_rfl
  simpa [cap, min_eq_right S.reaches_half] using hlast

end LMConnectorSchedule

/-- Two copies of the same multiplicative schedule give a short avoiding
connector.  This is the source-faithful numerical form of Lemma 3.4 used by
the final Lemma 4.7 wrapper. -/
theorem exists_avoiding_path_between_of_lmConnectorSchedule [Fintype V]
    {epsilon kappa : ℝ} {N D workspace : ℕ}
    (S : LMConnectorSchedule epsilon kappa N D workspace)
    (hexp : IsLMExpander G epsilon kappa)
    (hN : Fintype.card V = N) (W A B : Finset V)
    (hAcard : A.card = D) (hBcard : B.card = D)
    (hW : W.card ≤ workspace) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * S.rounds := by
  have hA := S.half_le_ball hexp hN W A hAcard hW
  have hB := S.half_le_ball hexp hN W B hBcard hW
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_large_balls
      G (W : Set V) A B S.rounds S.rounds (by rw [hN]; omega)
  exact ⟨a, ha, b, hb, p, hp, by omega⟩

/-- Among all avoiding paths joining two finite sets, choose one of minimum
length.  Minimality makes the chosen endpoints the only vertices of the path
in either end set.  This is the elementary trimming step which permits the
two ends of an adjuster to be relabelled *after* the connector has been
found. -/
theorem exists_endpoint_clean_avoiding_path
    (X : Set V) (A B : Finset V) (t : ℕ)
    (hAX : Disjoint (A : Set V) X) (hBX : Disjoint (B : Set V) X)
    (hex : ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath X ({a, b} : Set V) ∧ p.length ≤ t) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath
        (X ∪ (A : Set V) ∪ (B : Set V)) ({a, b} : Set V) ∧
        p.length ≤ t := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.Avoids X (∅ : Set V) ∧ p.length = n
  have hP : ∃ n : ℕ, P n := by
    obtain ⟨a, ha, b, hb, p, hp, hlen⟩ := hex
    have haX : a ∉ X := fun ha' ↦ Set.disjoint_left.1 hAX ha ha'
    have hbX : b ∉ X := fun hb' ↦ Set.disjoint_left.1 hBX hb hb'
    exact ⟨p.length, a, ha, b, hb, p, hp.1,
      connector_avoids_empty hp.2 haX hbX, rfl⟩
  let n := Nat.find hP
  obtain ⟨a, ha, b, hb, p, hp, hpX, hplen⟩ := Nat.find_spec hP
  have honlyA : ∀ z ∈ p.support, z ∈ A → z = a := by
    intro z hzp hzA
    by_contra hza
    let q : G.Walk z b := p.dropUntil z hzp
    have hqpath : q.IsPath := by
      apply Walk.IsPath.mk'
      exact (p.support_dropUntil_suffix_support hzp).nodup hp.support_nodup
    have hqX : q.Avoids X (∅ : Set V) :=
      hpX.of_support_subset (p.support_dropUntil_subset_support hzp)
    have hqP : P q.length := ⟨z, hzA, b, hb, q, hqpath, hqX, rfl⟩
    have hmin : n ≤ q.length := Nat.find_min' hP hqP
    have hlt : q.length < p.length := p.length_dropUntil_lt_length hzp hza
    omega
  have honlyB : ∀ z ∈ p.support, z ∈ B → z = b := by
    intro z hzp hzB
    by_contra hzb
    let q : G.Walk a z := p.takeUntil z hzp
    have hqpath : q.IsPath := by
      apply Walk.IsPath.mk'
      exact (p.support_takeUntil_prefix_support hzp).nodup hp.support_nodup
    have hqX : q.Avoids X (∅ : Set V) :=
      hpX.of_support_subset (p.support_takeUntil_subset_support hzp)
    have hqP : P q.length := ⟨a, ha, z, hzB, q, hqpath, hqX, rfl⟩
    have hmin : n ≤ q.length := Nat.find_min' hP hqP
    have hlt : q.length < p.length := p.length_takeUntil_lt_length hzp hzb
    omega
  refine ⟨a, ha, b, hb, p, ⟨hp, ?_⟩, ?_⟩
  · intro z hzp hz
    rcases hz with (hzX | hzA) | hzB
    · exact (hpX z hzp hzX).elim
    · simp [honlyA z hzp hzA]
    · simp [honlyB z hzp hzB]
  · rw [hplen]
    obtain ⟨a₀, ha₀, b₀, hb₀, p₀, hp₀, hp₀len⟩ := hex
    have ha₀X : a₀ ∉ X := fun ha' ↦ Set.disjoint_left.1 hAX ha₀ ha'
    have hb₀X : b₀ ∉ X := fun hb' ↦ Set.disjoint_left.1 hBX hb₀ hb'
    have hp₀P : P p₀.length := ⟨a₀, ha₀, b₀, hb₀, p₀, hp₀.1,
      connector_avoids_empty hp₀.2 ha₀X hb₀X, rfl⟩
    exact (Nat.find_min' hP hp₀P).trans hp₀len

/-! ## Splicing a concrete connector between two adjusters -/

/-- Three pairwise compatible paths concatenate to a path. -/
private theorem isPath_append_append {v₁ v₂ v₃ v₄ : V}
    {p : G.Walk v₁ v₂} {q : G.Walk v₂ v₃} {r : G.Walk v₃ v₄}
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath)
    (hpq : p.support.Disjoint q.support.tail)
    (hpqr : (p.support ++ q.support.tail).Disjoint r.support.tail) :
    ((p.append q).append r).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, Walk.support_append, List.nodup_append']
  refine ⟨?_, hr.support_nodup.tail, hpqr⟩
  exact List.nodup_append'.2 ⟨hp.support_nodup, hq.support_nodup.tail, hpq⟩

/-- The vertices forbidden to the connector in the join construction: the
old cores, the two retained right ends, and an ambient deletion set. -/
noncomputable def adjusterJoinBarrier {D m₁ m₂ k₁ k₂ : ℕ}
    (forbidden : Finset V) (A : Adjuster G D m₁ k₁)
    (B : Adjuster G D m₂ k₂) : Finset V :=
  forbidden ∪ A.core ∪ A.rightEnd.verts ∪ B.core ∪ B.rightEnd.verts

/-- Both ends of an adjuster, before the connector determines which one is
discarded. -/
noncomputable def adjusterEnds {D m k : ℕ}
    (A : Adjuster G D m k) : Finset V :=
  A.leftEnd.verts ∪ A.rightEnd.verts

@[simp] theorem adjusterEnds_card {D m k : ℕ} (A : Adjuster G D m k) :
    (adjusterEnds A).card = 2 * D := by
  classical
  rw [adjusterEnds, Finset.card_union_of_disjoint A.ends_disjoint,
    A.leftEnd.card_verts, A.rightEnd.card_verts]
  omega

theorem adjusterEnds_subset_verts {D m k : ℕ} (A : Adjuster G D m k) :
    adjusterEnds A ⊆ A.verts := by
  intro z hz
  simp only [adjusterEnds, Finset.mem_union] at hz
  rcases hz with hz | hz
  · exact A.leftEnd_verts_subset hz
  · exact A.rightEnd_verts_subset hz

@[simp] theorem adjusterEnds_swap {D m k : ℕ} (A : Adjuster G D m k) :
    adjusterEnds A.swap = adjusterEnds A := by
  classical
  simp only [adjusterEnds, Adjuster.swap]
  rw [Finset.union_comm]

/-- The deletion genuinely paid for in the paper's joining argument.  The
large end expansions are seeds, not deleted workspace. -/
noncomputable def adjusterJoinSmallBarrier {D m₁ m₂ k₁ k₂ : ℕ}
    (forbidden : Finset V) (A : Adjuster G D m₁ k₁)
    (B : Adjuster G D m₂ k₂) : Finset V :=
  forbidden ∪ A.core ∪ B.core

theorem adjusterJoinSmallBarrier_card_le
    {D m₁ m₂ k₁ k₂ : ℕ} (forbidden : Finset V)
    (A : Adjuster G D m₁ k₁) (B : Adjuster G D m₂ k₂) :
    (adjusterJoinSmallBarrier forbidden A B).card ≤
      forbidden.card + A.core.card + B.core.card := by
  have h₁ := Finset.card_union_le forbidden A.core
  have h₂ := Finset.card_union_le (forbidden ∪ A.core) B.core
  dsimp [adjusterJoinSmallBarrier]
  omega

@[simp] theorem adjusterJoinSmallBarrier_swap_left
    {D m₁ m₂ k₁ k₂ : ℕ} (forbidden : Finset V)
    (A : Adjuster G D m₁ k₁) (B : Adjuster G D m₂ k₂) :
    adjusterJoinSmallBarrier forbidden A.swap B =
      adjusterJoinSmallBarrier forbidden A B := rfl

@[simp] theorem adjusterJoinSmallBarrier_swap_right
    {D m₁ m₂ k₁ k₂ : ℕ} (forbidden : Finset V)
    (A : Adjuster G D m₁ k₁) (B : Adjuster G D m₂ k₂) :
    adjusterJoinSmallBarrier forbidden A B.swap =
      adjusterJoinSmallBarrier forbidden A B := rfl

namespace AdjusterJoin

variable {D m mB k : ℕ}
variable (A : Adjuster G D m k) (B₀ : Adjuster G D mB 1)
variable (hmB : mB ≤ m)

private noncomputable def B : Adjuster G D m 1 := B₀.widenRadius hmB

private noncomputable def core (q : G.Walk A.leftRoot B₀.leftRoot) : Finset V :=
  A.core ∪ B₀.core ∪ q.support.toFinset

private theorem routeA_supports (i : ℕ) (hi : i ≤ k) :
    ∃ p : G.Walk A.rightRoot A.leftRoot,
      p.IsPath ∧ p.length = A.length + 2 * i ∧
        ∀ z ∈ p.support, z = A.rightRoot ∨ z = A.leftRoot ∨ z ∈ A.core := by
  obtain ⟨p, hp, hsupp, hlen⟩ := A.pathLength i hi
  refine ⟨p.reverse, hp.reverse, by simpa using hlen, ?_⟩
  intro z hz
  have hz' : z ∈ p.support := by simpa using hz
  have := hsupp z hz'
  simp only [Finset.mem_insert] at this
  rcases this with rfl | rfl | hzcore
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr hzcore)

private theorem routeB_supports (j : ℕ) (hj : j ≤ 1) :
    ∃ p : G.Walk B₀.leftRoot B₀.rightRoot,
      p.IsPath ∧ p.length = B₀.length + 2 * j ∧
        ∀ z ∈ p.support, z = B₀.leftRoot ∨ z = B₀.rightRoot ∨ z ∈ B₀.core := by
  obtain ⟨p, hp, hsupp, hlen⟩ := B₀.pathLength j hj
  refine ⟨p, hp, hlen, ?_⟩
  intro z hz
  have := hsupp z hz
  simp only [Finset.mem_insert] at this
  exact this

/-- A concrete short path between the discarded left roots constructs the
full route certificate used by Lemma 4.7. -/
theorem routesOfConnector
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (q : G.Walk A.leftRoot B₀.leftRoot) (hq : q.IsPath)
    (hqavoid : q.Avoids
      (adjusterJoinBarrier forbidden A B₀ : Set V) ∅)
    (hcard : A.core.card + B₀.core.card + q.length + 1 ≤
      10 * m * (k + 1)) :
    ∃ J : AdjusterJoinRoutes A (B₀.widenRadius hmB),
      Disjoint forbidden (A.ofJoinRoutes (B₀.widenRadius hmB) J).verts := by
  classical
  let B := B₀.widenRadius hmB
  let C := A.core ∪ B₀.core ∪ q.support.toFinset
  have hq_not_barrier {z : V} (hzq : z ∈ q.support)
      (hzX : z ∈ adjusterJoinBarrier forbidden A B₀) : False := by
    exact (hqavoid z hzq hzX).elim
  have hAB_left : ∀ {z : V}, z ∈ A.verts → z ∈ B₀.verts → False := by
    intro z hzA hzB
    exact Finset.disjoint_left.1 hAB hzA hzB
  have hcore_left : Disjoint C A.rightEnd.verts := by
    rw [Finset.disjoint_left]
    intro z hzC hzright
    simp only [C, Finset.mem_union, List.mem_toFinset] at hzC
    rcases hzC with (hzA | hzB) | hzq
    · exact Finset.disjoint_left.1 A.core_disjoint_right hzA hzright
    · exact hAB_left (A.rightEnd_verts_subset hzright)
        (B₀.core_subset_verts hzB)
    · apply hq_not_barrier hzq
      simp [adjusterJoinBarrier, hzright]
  have hcore_right : Disjoint C B.rightEnd.verts := by
    rw [Finset.disjoint_left]
    intro z hzC hzright
    have hzright₀ : z ∈ B₀.rightEnd.verts := by
      simpa only [B, Adjuster.widenRadius_rightEnd_verts] using hzright
    simp only [C, Finset.mem_union, List.mem_toFinset] at hzC
    rcases hzC with (hzA | hzB) | hzq
    · exact hAB_left (A.core_subset_verts hzA)
        (B₀.rightEnd_verts_subset hzright₀)
    · exact Finset.disjoint_left.1 B₀.core_disjoint_right hzB hzright₀
    · apply hq_not_barrier hzq
      simp [adjusterJoinBarrier, hzright₀]
  have hends : Disjoint A.rightEnd.verts B.rightEnd.verts := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    apply hAB_left (A.rightEnd_verts_subset hzA)
    apply B₀.rightEnd_verts_subset
    simpa only [B, Adjuster.widenRadius_rightEnd_verts] using hzB
  have hCcard : C.card ≤ 10 * m * (k + 1) := by
    have h₁ := Finset.card_union_le A.core B₀.core
    have h₂ := Finset.card_union_le (A.core ∪ B₀.core) q.support.toFinset
    have hsupport : q.support.toFinset.card = q.length + 1 := by
      rw [List.toFinset_card_of_nodup hq.support_nodup, q.length_support]
    calc
      C.card ≤ A.core.card + B₀.core.card + q.support.toFinset.card := by
        dsimp [C]
        omega
      _ = A.core.card + B₀.core.card + q.length + 1 := by omega
      _ ≤ 10 * m * (k + 1) := hcard
  have hforbidden : Disjoint forbidden C := by
    rw [Finset.disjoint_left]
    intro z hzforbidden hzC
    simp only [C, Finset.mem_union, List.mem_toFinset] at hzC
    rcases hzC with (hzA | hzB) | hzq
    · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
        (A.core_subset_verts hzA)
    · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
        (B₀.core_subset_verts hzB)
    · exact hq_not_barrier hzq (by simp [adjusterJoinBarrier, hzforbidden])
  let base := A.length + q.length + B₀.length
  have hroutes : ∀ i j : ℕ, i ≤ k → j ≤ 1 →
      HasSupportedPathLength G
        (insert A.rightRoot (insert B.rightRoot C))
        A.rightRoot B.rightRoot (base + 2 * (i + j)) := by
    intro i j hi hj
    obtain ⟨pA, hpA, hpAlen, hpAsupport⟩ := routeA_supports A i hi
    obtain ⟨pB, hpB, hpBlen, hpBsupport⟩ := routeB_supports B₀ j hj
    have hAq : pA.support.Disjoint q.support.tail := by
      rw [List.disjoint_left]
      intro z hzpA hzqtail
      have hzq : z ∈ q.support := by
        rw [← q.cons_tail_support]
        exact List.mem_cons_of_mem _ hzqtail
      rcases hpAsupport z hzpA with rfl | rfl | hzcore
      · exact hq_not_barrier hzq (by
          simp [adjusterJoinBarrier, A.rightEnd.root_mem])
      · have hn := hq.support_nodup
        rw [← q.cons_tail_support, List.nodup_cons] at hn
        exact hn.1 hzqtail
      · exact hq_not_barrier hzq (by simp [adjusterJoinBarrier, hzcore])
    have hABroute : pA.support.Disjoint pB.support.tail := by
      rw [List.disjoint_left]
      intro z hzpA hzpB
      have hzA : z ∈ A.verts := by
        rcases hpAsupport z hzpA with rfl | rfl | hzcore
        · exact A.rightRoot_mem_verts
        · exact A.leftRoot_mem_verts
        · exact A.core_subset_verts hzcore
      have hzB : z ∈ B₀.verts := by
        have hzpB' : z ∈ pB.support := by
          rw [← pB.cons_tail_support]
          exact List.mem_cons_of_mem _ hzpB
        rcases hpBsupport z hzpB' with rfl | rfl | hzcore
        · exact B₀.leftRoot_mem_verts
        · exact B₀.rightRoot_mem_verts
        · exact B₀.core_subset_verts hzcore
      exact hAB_left hzA hzB
    have hqB : q.support.Disjoint pB.support.tail := by
      rw [List.disjoint_left]
      intro z hzq hzpB
      have hzpB' : z ∈ pB.support := by
        rw [← pB.cons_tail_support]
        exact List.mem_cons_of_mem _ hzpB
      rcases hpBsupport z hzpB' with rfl | rfl | hzcore
      · have hn := hpB.support_nodup
        rw [← pB.cons_tail_support, List.nodup_cons] at hn
        exact hn.1 hzpB
      · exact hq_not_barrier hzq (by
          simp [adjusterJoinBarrier, B₀.rightEnd.root_mem])
      · exact hq_not_barrier hzq (by simp [adjusterJoinBarrier, hzcore])
    have htotal : (pA.support ++ q.support.tail).Disjoint pB.support.tail := by
      rw [List.disjoint_left]
      intro z hz hzpB
      rw [List.mem_append] at hz
      rcases hz with hz | hz
      · exact (List.disjoint_left.1 hABroute) hz hzpB
      · exact (List.disjoint_left.1 hqB)
          (by rw [← q.cons_tail_support]; exact List.mem_cons_of_mem _ hz) hzpB
    let w : G.Walk A.rightRoot B₀.rightRoot := (pA.append q).append pB
    have hwpath : w.IsPath := isPath_append_append hpA hq hpB hAq htotal
    have hBr : B₀.rightRoot = B.rightRoot := by simp [B]
    let wc : G.Walk A.rightRoot B.rightRoot := w.copy rfl hBr
    have hwcpath : wc.IsPath := by simpa [wc] using hwpath
    refine ⟨wc, hwcpath, ?_, ?_⟩
    · intro z hzw
      have hzw' : z ∈ w.support := by
        simpa only [wc, Walk.support_copy] using hzw
      simp only [w, Walk.mem_support_append_iff] at hzw'
      rcases hzw' with (hzA | hzq) | hzB
      · rcases hpAsupport z hzA with rfl | rfl | hzcore
        · simp
        · simp [C, q.start_mem_support]
        · simp [C, hzcore]
      · simp [C, hzq]
      · rcases hpBsupport z hzB with rfl | rfl | hzcore
        · simp [C, q.end_mem_support]
        · simp [B]
        · simp [C, hzcore]
    · have hwclen : wc.length = w.length := by simp [wc]
      rw [hwclen]
      dsimp [w, base]
      simp only [Walk.length_append, hpAlen, hpBlen]
      omega
  let J : AdjusterJoinRoutes A B :=
    { core := C
      core_disjoint_left := hcore_left
      core_disjoint_right := hcore_right
      ends_disjoint := hends
      core_card_le := hCcard
      baseLength := base
      routes := hroutes }
  have hforbiddenAll :
      Disjoint forbidden (A.rightEnd.verts ∪ B.rightEnd.verts ∪ C) := by
    rw [Finset.disjoint_left]
    intro z hzforbidden hz
    simp only [Finset.mem_union] at hz
    rcases hz with (hzA | hzB) | hzC
    · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
        (A.rightEnd_verts_subset hzA)
    · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
        (by
          apply B₀.rightEnd_verts_subset
          simpa only [B, Adjuster.widenRadius_rightEnd_verts] using hzB)
    · exact Finset.disjoint_left.1 hforbidden hzforbidden hzC
  refine ⟨J, ?_⟩
  simpa [Adjuster.ofJoinRoutes, Adjuster.verts, J, B] using hforbiddenAll

/-- The discarded left end of the first adjuster is disjoint from the exact
deletion set used to find the connector. -/
private theorem leftEnd_disjoint_barrier_A
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts) :
    Disjoint (A.leftEnd.verts : Set V)
      (adjusterJoinBarrier forbidden A B₀ : Set V) := by
  rw [Set.disjoint_left]
  intro z hzleft hzbarrier
  simp only [adjusterJoinBarrier, Finset.coe_union, Set.mem_union] at hzbarrier
  rcases hzbarrier with (((hzforbidden | hzAcore) | hzAright) | hzBcore) | hzBright
  · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
      (A.leftEnd_verts_subset hzleft)
  · exact Finset.disjoint_left.1 A.core_disjoint_left hzAcore hzleft
  · exact Finset.disjoint_left.1 A.ends_disjoint hzleft hzAright
  · exact Finset.disjoint_left.1 hAB (A.leftEnd_verts_subset hzleft)
      (B₀.core_subset_verts hzBcore)
  · exact Finset.disjoint_left.1 hAB (A.leftEnd_verts_subset hzleft)
      (B₀.rightEnd_verts_subset hzBright)

/-- The discarded left end of the second adjuster is disjoint from the exact
deletion set used to find the connector. -/
private theorem leftEnd_disjoint_barrier_B
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts) :
    Disjoint (B₀.leftEnd.verts : Set V)
      (adjusterJoinBarrier forbidden A B₀ : Set V) := by
  rw [Set.disjoint_left]
  intro z hzleft hzbarrier
  simp only [adjusterJoinBarrier, Finset.coe_union, Set.mem_union] at hzbarrier
  rcases hzbarrier with (((hzforbidden | hzAcore) | hzAright) | hzBcore) | hzBright
  · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
      (B₀.leftEnd_verts_subset hzleft)
  · exact Finset.disjoint_left.1 hAB (A.core_subset_verts hzAcore)
      (B₀.leftEnd_verts_subset hzleft)
  · exact Finset.disjoint_left.1 hAB (A.rightEnd_verts_subset hzAright)
      (B₀.leftEnd_verts_subset hzleft)
  · exact Finset.disjoint_left.1 B₀.core_disjoint_left hzBcore hzleft
  · exact Finset.disjoint_left.1 B₀.ends_disjoint hzleft hzBright

/-- Before an end is selected, the union of both ends of the first adjuster
is disjoint from the small deletion set. -/
private theorem ends_disjoint_smallBarrier_A
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts) :
    Disjoint (adjusterEnds A : Set V)
      (adjusterJoinSmallBarrier forbidden A B₀ : Set V) := by
  rw [Set.disjoint_left]
  intro z hzends hzbarrier
  simp only [adjusterEnds, Finset.coe_union, Set.mem_union] at hzends
  simp only [adjusterJoinSmallBarrier, Finset.coe_union, Set.mem_union] at hzbarrier
  rcases hzends with hzleft | hzright
  · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
    · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
        (A.leftEnd_verts_subset hzleft)
    · exact Finset.disjoint_left.1 A.core_disjoint_left hzAcore hzleft
    · exact Finset.disjoint_left.1 hAB (A.leftEnd_verts_subset hzleft)
        (B₀.core_subset_verts hzBcore)
  · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
    · exact Finset.disjoint_left.1 hforbiddenA hzforbidden
        (A.rightEnd_verts_subset hzright)
    · exact Finset.disjoint_left.1 A.core_disjoint_right hzAcore hzright
    · exact Finset.disjoint_left.1 hAB (A.rightEnd_verts_subset hzright)
        (B₀.core_subset_verts hzBcore)

/-- The corresponding disjointness for the second adjuster's two ends. -/
private theorem ends_disjoint_smallBarrier_B
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts) :
    Disjoint (adjusterEnds B₀ : Set V)
      (adjusterJoinSmallBarrier forbidden A B₀ : Set V) := by
  rw [Set.disjoint_left]
  intro z hzends hzbarrier
  simp only [adjusterEnds, Finset.coe_union, Set.mem_union] at hzends
  simp only [adjusterJoinSmallBarrier, Finset.coe_union, Set.mem_union] at hzbarrier
  rcases hzends with hzleft | hzright
  · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
    · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
        (B₀.leftEnd_verts_subset hzleft)
    · exact Finset.disjoint_left.1 hAB (A.core_subset_verts hzAcore)
        (B₀.leftEnd_verts_subset hzleft)
    · exact Finset.disjoint_left.1 B₀.core_disjoint_left hzBcore hzleft
  · rcases hzbarrier with (hzforbidden | hzAcore) | hzBcore
    · exact Finset.disjoint_left.1 hforbiddenB hzforbidden
        (B₀.rightEnd_verts_subset hzright)
    · exact Finset.disjoint_left.1 hAB (A.core_subset_verts hzAcore)
        (B₀.rightEnd_verts_subset hzright)
    · exact Finset.disjoint_left.1 B₀.core_disjoint_right hzBcore hzright

/-- If the connector has selected the left end of each adjuster and is clean
with respect to all four ends, the exact splice gives the successor
adjuster. -/
private theorem stepOfSelectedLeftConnector
    (hmB : mB ≤ m)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    {a b : V} (ha : a ∈ A.leftEnd.verts) (hb : b ∈ B₀.leftEnd.verts)
    {t : ℕ} (p : G.Walk a b)
    (hp : p.IsAvoidingPath
      ((adjusterJoinSmallBarrier forbidden A B₀ : Set V) ∪
        (adjusterEnds A : Set V) ∪ (adjusterEnds B₀ : Set V))
      ({a, b} : Set V))
    (hplen : p.length ≤ t)
    (hcard : A.core.card + B₀.core.card + (m + t + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  have hfull :
      (adjusterJoinBarrier forbidden A B₀ : Set V) ⊆
        (adjusterJoinSmallBarrier forbidden A B₀ : Set V) ∪
          (adjusterEnds A : Set V) ∪ (adjusterEnds B₀ : Set V) := by
    intro z hz
    simp only [adjusterJoinBarrier, adjusterJoinSmallBarrier, adjusterEnds,
      Finset.coe_union, Set.mem_union] at hz ⊢
    tauto
  have hpfull : p.IsAvoidingPath
      (adjusterJoinBarrier forbidden A B₀ : Set V) ({a, b} : Set V) :=
    hp.mono_forbidden hfull
  obtain ⟨q, hq, hqavoid, hqlen⟩ :=
    exists_root_connector_of_avoiding_path A.leftEnd B₀.leftEnd ha hb
      (leftEnd_disjoint_barrier_A A B₀ forbidden hAB hforbiddenA)
      (leftEnd_disjoint_barrier_B A B₀ forbidden hAB hforbiddenB)
      p hpfull hplen
  obtain ⟨J, hJ⟩ := routesOfConnector A B₀ hmB forbidden hAB
    hforbiddenA hforbiddenB q hq hqavoid (by omega)
  exact ⟨A.ofJoinRoutes (B₀.widenRadius hmB) J, hJ⟩

/-- A connector between the unions of both ends may hit any one end on each
side.  Swap the corresponding adjusters, making the hit ends the discarded
left ends, and retain the two untouched ends. -/
theorem stepOfEndpointCleanConnector
    (hmB : mB ≤ m)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    {a b : V} (ha : a ∈ adjusterEnds A) (hb : b ∈ adjusterEnds B₀)
    {t : ℕ} (p : G.Walk a b)
    (hp : p.IsAvoidingPath
      ((adjusterJoinSmallBarrier forbidden A B₀ : Set V) ∪
        (adjusterEnds A : Set V) ∪ (adjusterEnds B₀ : Set V))
      ({a, b} : Set V))
    (hplen : p.length ≤ t)
    (hcard : A.core.card + B₀.core.card + (m + t + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  classical
  simp only [adjusterEnds, Finset.mem_union] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact stepOfSelectedLeftConnector A B₀ hmB forbidden hAB hforbiddenA
      hforbiddenB ha hb p hp hplen hcard
  · have hp' : p.IsAvoidingPath
        ((adjusterJoinSmallBarrier forbidden A B₀.swap : Set V) ∪
          (adjusterEnds A : Set V) ∪ (adjusterEnds B₀.swap : Set V))
        ({a, b} : Set V) := by simpa using hp
    exact stepOfSelectedLeftConnector A B₀.swap hmB forbidden
      (by simpa using hAB) hforbiddenA (by simpa using hforbiddenB)
      ha hb p hp' hplen (by simpa using hcard)
  · have hp' : p.IsAvoidingPath
        ((adjusterJoinSmallBarrier forbidden A.swap B₀ : Set V) ∪
          (adjusterEnds A.swap : Set V) ∪ (adjusterEnds B₀ : Set V))
        ({a, b} : Set V) := by simpa using hp
    exact stepOfSelectedLeftConnector A.swap B₀ hmB forbidden
      (by simpa using hAB) (by simpa using hforbiddenA) hforbiddenB
      ha hb p hp' hplen (by simpa using hcard)
  · have hp' : p.IsAvoidingPath
        ((adjusterJoinSmallBarrier forbidden A.swap B₀.swap : Set V) ∪
          (adjusterEnds A.swap : Set V) ∪ (adjusterEnds B₀.swap : Set V))
        ({a, b} : Set V) := by simpa using hp
    exact stepOfSelectedLeftConnector A.swap B₀.swap hmB forbidden
      (by simpa using hAB) (by simpa using hforbiddenA)
      (by simpa using hforbiddenB) ha hb p hp' hplen (by simpa using hcard)

/-- Public raw-connector interface for the concrete growth-profile file.
The supplied path only avoids the small paid deletion.  This theorem
minimizes it, relabels the hit ends, and performs the complete splice. -/
theorem stepOfEndpointUnionRawConnector
    (hmB : mB ≤ m)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    {a b : V} (ha : a ∈ adjusterEnds A) (hb : b ∈ adjusterEnds B₀)
    {t : ℕ} (p : G.Walk a b)
    (hp : p.IsAvoidingPath
      (adjusterJoinSmallBarrier forbidden A B₀ : Set V) ({a, b} : Set V))
    (hplen : p.length ≤ t)
    (hcard : A.core.card + B₀.core.card + (m + t + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  let W := adjusterJoinSmallBarrier forbidden A B₀
  let EA := adjusterEnds A
  let EB := adjusterEnds B₀
  have hraw : ∃ a ∈ EA, ∃ b ∈ EB, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧ p.length ≤ t :=
    ⟨a, ha, b, hb, p, by simpa [W] using hp, hplen⟩
  have hEAW : Disjoint (EA : Set V) (W : Set V) := by
    simpa [EA, W] using
      ends_disjoint_smallBarrier_A A B₀ forbidden hAB hforbiddenA
  have hEBW : Disjoint (EB : Set V) (W : Set V) := by
    simpa [EB, W] using
      ends_disjoint_smallBarrier_B A B₀ forbidden hAB hforbiddenB
  obtain ⟨a', ha', b', hb', p', hp', hplen'⟩ :=
    exists_endpoint_clean_avoiding_path (G := G) (W : Set V) EA EB t
      hEAW hEBW hraw
  apply stepOfEndpointCleanConnector A B₀ hmB forbidden hAB hforbiddenA
    hforbiddenB ha' hb' p'
  · simpa [W, EA, EB] using hp'
  · exact hplen'
  · exact hcard

/-- Concrete ball-intersection form of the join step in Lemma 4.7.  The only
growth premise is the literal cardinal inequality for the two avoiding
balls; the root connector and all route-disjointness facts are constructed
inside the proof. -/
theorem routesOfLargeBalls [Fintype V]
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (r s : ℕ)
    (hlarge : Fintype.card V <
      (ballAvoidingFrom G
        (adjusterJoinBarrier forbidden A B₀ : Set V) A.leftEnd.verts r).card +
      (ballAvoidingFrom G
        (adjusterJoinBarrier forbidden A B₀ : Set V) B₀.leftEnd.verts s).card)
    (hcard : A.core.card + B₀.core.card + (m + (r + s) + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ J : AdjusterJoinRoutes A (B₀.widenRadius hmB),
      Disjoint forbidden (A.ofJoinRoutes (B₀.widenRadius hmB) J).verts := by
  obtain ⟨q, hq, hqavoid, hqlen⟩ :=
    exists_root_connector_of_large_balls A.leftEnd B₀.leftEnd
      (leftEnd_disjoint_barrier_A A B₀ forbidden hAB hforbiddenA)
      (leftEnd_disjoint_barrier_B A B₀ forbidden hAB hforbiddenB) hlarge
  apply routesOfConnector A B₀ hmB forbidden hAB hforbiddenA hforbiddenB q hq hqavoid
  omega

/-- The Komlós--Szemerédi-expander form of the join.  The hypotheses are
the exact finite growth inequalities needed by Liu--Montgomery Lemma 3.4;
that lemma constructs the connector between the two discarded expansions,
after which `routesOfConnector` performs the complete adjuster splice. -/
theorem routesOfLMExpanderGrowth [Fintype V]
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (growthStep radius : ℕ)
    (hAlower : expanderK / 2 ≤ (A.leftEnd.verts.card : ℝ))
    (hBlower : expanderK / 2 ≤ (B₀.leftEnd.verts.card : ℝ))
    (hArate : ∀ t : ℕ, A.leftEnd.verts.card ≤ t →
      t ≤ Fintype.card V / 2 →
      ((((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
        expansionEpsilon epsilon expanderK t * (t : ℝ)))
    (hBrate : ∀ t : ℕ, B₀.leftEnd.verts.card ≤ t →
      t ≤ Fintype.card V / 2 →
      ((((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
        expansionEpsilon epsilon expanderK t * (t : ℝ)))
    (hAsteps : Fintype.card V / 2 + 1 ≤
      A.leftEnd.verts.card + radius * growthStep)
    (hBsteps : Fintype.card V / 2 + 1 ≤
      B₀.leftEnd.verts.card + radius * growthStep)
    (hcard : A.core.card + B₀.core.card + (m + 2 * radius + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ J : AdjusterJoinRoutes A (B₀.widenRadius hmB),
      Disjoint forbidden (A.ofJoinRoutes (B₀.widenRadius hmB) J).verts := by
  let W := adjusterJoinBarrier forbidden A B₀
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmExpander_growth G epsilon expanderK hexp
      W A.leftEnd.verts B₀.leftEnd.verts growthStep radius
      hAlower hBlower hArate hBrate hAsteps hBsteps
  obtain ⟨q, hq, hqavoid, hqlen⟩ :=
    exists_root_connector_of_avoiding_path A.leftEnd B₀.leftEnd ha hb
      (leftEnd_disjoint_barrier_A A B₀ forbidden hAB hforbiddenA)
      (leftEnd_disjoint_barrier_B A B₀ forbidden hAB hforbiddenB)
      p hp hplen
  apply routesOfConnector A B₀ hmB forbidden hAB hforbiddenA hforbiddenB q hq hqavoid
  omega

/-- Correct paper-form scheduled join.  Both ends on each side are grown as
one seed set while only the ambient forbidden set and the two small cores are
deleted.  A minimum connector determines which end is discarded, and the
two adjusters are swapped accordingly.  In particular, the growth rate never
pays for either retained `D`-vertex expansion. -/
theorem stepOfEndpointUnionSchedule [Fintype V]
    (hmB : mB ≤ m)
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (workspace : ℕ)
    (S : LMConnectorSchedule epsilon expanderK (Fintype.card V) (2 * D) workspace)
    (hsmall : (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace)
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * S.rounds + mB) + 1 ≤ 10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  let W := adjusterJoinSmallBarrier forbidden A B₀
  let EA := adjusterEnds A
  let EB := adjusterEnds B₀
  have hraw : ∃ a ∈ EA, ∃ b ∈ EB, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * S.rounds := by
    apply exists_avoiding_path_between_of_lmConnectorSchedule S hexp rfl
      W EA EB
    · simp [EA]
    · simp [EB]
    · exact hsmall
  have hEAW : Disjoint (EA : Set V) (W : Set V) := by
    simpa [EA, W] using
      ends_disjoint_smallBarrier_A A B₀ forbidden hAB hforbiddenA
  have hEBW : Disjoint (EB : Set V) (W : Set V) := by
    simpa [EB, W] using
      ends_disjoint_smallBarrier_B A B₀ forbidden hAB hforbiddenB
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_endpoint_clean_avoiding_path (G := G) (W : Set V) EA EB
      (2 * S.rounds) hEAW hEBW hraw
  apply stepOfEndpointCleanConnector A B₀ hmB forbidden hAB hforbiddenA
    hforbiddenB ha hb p
  · simpa [W, EA, EB] using hp
  · exact hplen
  · exact hcard

/-- Strong-deletion specialization using a variable-increment growth
schedule.  This remains useful when the entire retained-end barrier is
genuinely affordable.  The paper-form Lemma 4.7 uses
`stepOfEndpointUnionSchedule` above instead. -/
theorem routesOfLMExpanderSchedule [Fintype V]
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (workspace : ℕ)
    (S : LMConnectorSchedule epsilon expanderK (Fintype.card V) D workspace)
    (hbarrier : (adjusterJoinBarrier forbidden A B₀).card ≤ workspace)
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * S.rounds + mB) + 1 ≤ 10 * m * (k + 1)) :
    ∃ J : AdjusterJoinRoutes A (B₀.widenRadius hmB),
      Disjoint forbidden (A.ofJoinRoutes (B₀.widenRadius hmB) J).verts := by
  let W := adjusterJoinBarrier forbidden A B₀
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_lmConnectorSchedule S hexp rfl W
      A.leftEnd.verts B₀.leftEnd.verts A.leftEnd.card_verts
      B₀.leftEnd.card_verts hbarrier
  obtain ⟨q, hq, hqavoid, hqlen⟩ :=
    exists_root_connector_of_avoiding_path A.leftEnd B₀.leftEnd ha hb
      (leftEnd_disjoint_barrier_A A B₀ forbidden hAB hforbiddenA)
      (leftEnd_disjoint_barrier_B A B₀ forbidden hAB hforbiddenB)
      p hp hplen
  apply routesOfConnector A B₀ hmB forbidden hAB hforbiddenA hforbiddenB q hq hqavoid
  omega

/-- One complete scheduled-growth successor step of Lemma 4.7. -/
theorem stepOfLMExpanderSchedule [Fintype V]
    (hmB : mB ≤ m)
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (workspace : ℕ)
    (S : LMConnectorSchedule epsilon expanderK (Fintype.card V) D workspace)
    (hbarrier : (adjusterJoinBarrier forbidden A B₀).card ≤ workspace)
    (hcard : A.core.card + B₀.core.card +
        (m + 2 * S.rounds + mB) + 1 ≤ 10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  obtain ⟨J, hJ⟩ := routesOfLMExpanderSchedule A B₀ hmB epsilon expanderK hexp
    forbidden hAB hforbiddenA hforbiddenB workspace S hbarrier hcard
  exact ⟨A.ofJoinRoutes (B₀.widenRadius hmB) J, hJ⟩

/-- One complete inductive step of Liu--Montgomery Lemma 4.7, stated as the
new adjuster rather than its intermediate route certificate. -/
theorem stepOfLMExpanderGrowth [Fintype V]
    (hmB : mB ≤ m)
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V)
    (hAB : Disjoint A.verts B₀.verts)
    (hforbiddenA : Disjoint forbidden A.verts)
    (hforbiddenB : Disjoint forbidden B₀.verts)
    (growthStep radius : ℕ)
    (hAlower : expanderK / 2 ≤ (A.leftEnd.verts.card : ℝ))
    (hBlower : expanderK / 2 ≤ (B₀.leftEnd.verts.card : ℝ))
    (hArate : ∀ t : ℕ, A.leftEnd.verts.card ≤ t →
      t ≤ Fintype.card V / 2 →
      ((((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
        expansionEpsilon epsilon expanderK t * (t : ℝ)))
    (hBrate : ∀ t : ℕ, B₀.leftEnd.verts.card ≤ t →
      t ≤ Fintype.card V / 2 →
      ((((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
        expansionEpsilon epsilon expanderK t * (t : ℝ)))
    (hAsteps : Fintype.card V / 2 + 1 ≤
      A.leftEnd.verts.card + radius * growthStep)
    (hBsteps : Fintype.card V / 2 + 1 ≤
      B₀.leftEnd.verts.card + radius * growthStep)
    (hcard : A.core.card + B₀.core.card + (m + 2 * radius + mB) + 1 ≤
      10 * m * (k + 1)) :
    ∃ C : Adjuster G D m (k + 1), Disjoint forbidden C.verts := by
  obtain ⟨J, hJ⟩ := routesOfLMExpanderGrowth A B₀ hmB epsilon expanderK hexp
    forbidden hAB hforbiddenA hforbiddenB growthStep radius hAlower hBlower
    hArate hBrate hAsteps hBsteps hcard
  exact ⟨A.ofJoinRoutes (B₀.widenRadius hmB) J, hJ⟩

/-! ## Iterating the concrete join -/

/-- Internal-order Lemma 4.7 induction with a variable-increment connector
schedule.  The protected set is included in every connector barrier.  Thus a
caller using a large protected set must run this theorem at an end order for
which the workspace rate is affordable; the public protected-set wrapper
below does so at an inflated order and then shrinks the surviving ends. -/
theorem lemma4_7_of_simple_supply_and_schedule [Fintype V]
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V) (r simpleBudget workspace : ℕ)
    (S : LMConnectorSchedule epsilon expanderK (Fintype.card V) (2 * D) workspace)
    (hrpos : 0 < r)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G D mB 1, Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hsupplyCap : forbidden.card + 2 * D + 10 * m * r ≤ simpleBudget)
    (hworkspaceCap :
      forbidden.card + 10 * m * r + 10 * mB ≤ workspace)
    (hjoinCapacity :
      10 * mB + (m + 2 * S.rounds + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G D m r, Disjoint forbidden A.verts := by
  induction r with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        have hforbiddenBudget : forbidden.card ≤ simpleBudget := by omega
        obtain ⟨B₀, hB⟩ := hsupply forbidden hforbiddenBudget
        exact ⟨B₀.widenRadius hmB, by simpa using hB⟩
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hsupplyCapJ :
            forbidden.card + 2 * D + 10 * m * j ≤ simpleBudget := by
          exact hsupplyCap.trans' <| by
            gcongr
            omega
        have hworkspaceCapJ :
            forbidden.card + 10 * m * j + 10 * mB ≤ workspace := by
          exact hworkspaceCap.trans' <| by
            gcongr
            omega
        obtain ⟨A, hforbiddenA⟩ := ih hjpos hsupplyCapJ hworkspaceCapJ
        let U := forbidden ∪ A.verts
        have hUcard : U.card ≤ simpleBudget := by
          calc
            U.card ≤ forbidden.card + A.verts.card := Finset.card_union_le _ _
            _ ≤ forbidden.card + (2 * D + 10 * m * j) :=
              Nat.add_le_add_left A.card_verts_le _
            _ ≤ simpleBudget := by simpa [Nat.add_assoc] using hsupplyCapJ
        obtain ⟨B₀, hUB⟩ := hsupply U hUcard
        have hAB : Disjoint A.verts B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzA hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzA]) hzB
        have hforbiddenB : Disjoint forbidden B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzforbidden hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzforbidden]) hzB
        have hsmall :
            (adjusterJoinSmallBarrier forbidden A B₀).card ≤ workspace := by
          have hAcore := A.core_card_le
          have hBcore := B₀.core_card_le
          have h₁ := Finset.card_union_le forbidden A.core
          have h₂ := Finset.card_union_le (forbidden ∪ A.core) B₀.core
          dsimp [adjusterJoinSmallBarrier]
          omega
        have hcard : A.core.card + B₀.core.card +
            (m + 2 * S.rounds + mB) + 1 ≤ 10 * m * (j + 1) := by
          have hrest : B₀.core.card +
              (m + 2 * S.rounds + mB) + 1 ≤ 10 * m := by
            have hBcore : B₀.core.card ≤ 10 * mB := by
              simpa using B₀.core_card_le
            calc
              B₀.core.card + (m + 2 * S.rounds + mB) + 1
                  ≤ 10 * mB + (m + 2 * S.rounds + mB) + 1 := by omega
              _ ≤ 10 * m := hjoinCapacity
          calc
            A.core.card + B₀.core.card + (m + 2 * S.rounds + mB) + 1
                = A.core.card +
                    (B₀.core.card + (m + 2 * S.rounds + mB) + 1) := by omega
            _ ≤ 10 * m * j + 10 * m := Nat.add_le_add A.core_card_le hrest
            _ = 10 * m * (j + 1) := by rw [Nat.mul_add]; simp
        exact stepOfEndpointUnionSchedule A B₀ hmB epsilon expanderK hexp forbidden
          hAB hforbiddenA hforbiddenB workspace S hsmall hcard

/-- Protected-set form of the Lemma 4.7 induction.

All joins are performed at `inflatedOrder`, and the whole protected set
`forbidden` is part of the deleted set at every connection.  Consequently
the numerical schedule is required at seed order `2 * inflatedOrder` and its
workspace bound explicitly pays for `forbidden` and both cores.  After the
induction, Proposition 3.10 shrinks the two surviving end expansions to the
requested positive order `D`; `Adjuster.replaceEnds` preserves the core and
all adjustable routes.  This is the correction needed when the protected set
is too large to be paid for at end order `D` itself. -/
theorem lemma4_7_of_inflated_simple_supply_and_schedule [Fintype V]
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V) (inflatedOrder r simpleBudget workspace : ℕ)
    (S : LMConnectorSchedule epsilon expanderK (Fintype.card V)
      (2 * inflatedOrder) workspace)
    (hDpos : 0 < D) (hDinflated : D ≤ inflatedOrder) (hrpos : 0 < r)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G inflatedOrder mB 1, Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hsupplyCap :
      forbidden.card + 2 * inflatedOrder + 10 * m * r ≤ simpleBudget)
    (hworkspaceCap :
      forbidden.card + 10 * m * r + 10 * mB ≤ workspace)
    (hjoinCapacity :
      10 * mB + (m + 2 * S.rounds + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G D m r, Disjoint forbidden A.verts := by
  obtain ⟨A, hA⟩ :=
    lemma4_7_of_simple_supply_and_schedule
      (G := G) (D := inflatedOrder) epsilon expanderK hexp forbidden r
      simpleBudget workspace S hrpos hsupply hmB hsupplyCap hworkspaceCap
      hjoinCapacity
  obtain ⟨A', _, _, _, hsub⟩ :=
    A.exists_shrinkEnds_subset hDpos hDinflated
  exact ⟨A', hA.mono_right hsub⟩

/-- Fixed-additive, strong-deletion specialization of the induction.  It is
occasionally convenient for bounded-order applications; the paper-form
arbitrary-order Lemma 4.7 must instead use the inflated-order protected-set
theorem above.
In contrast to a generic join premise, every inductive connection is
constructed here from the fixed LM-expander and literal growth inequalities.

The two budgets merely collect the elementary union bounds used in the
paper.  They make this lemma directly composable with the concrete Lemma 4.3
and with eventual numerical estimates, without hiding a graph-theoretic
connection assertion in a hypothesis. -/
theorem lemma4_7_of_simple_supply_and_expander [Fintype V]
    (epsilon expanderK : ℝ) (hexp : IsLMExpander G epsilon expanderK)
    (forbidden : Finset V) (r growthStep radius simpleBudget deletionBudget : ℕ)
    (hrpos : 0 < r)
    (hsupply : ∀ U : Finset V, U.card ≤ simpleBudget →
      ∃ B : Adjuster G D mB 1, Disjoint U B.verts)
    (hmB : mB ≤ m)
    (hlower : expanderK / 2 ≤ (D : ℝ))
    (hrate : ∀ t : ℕ, D ≤ t → t ≤ Fintype.card V / 2 →
      (((deletionBudget + growthStep : ℕ) : ℝ) ≤
        expansionEpsilon epsilon expanderK t * (t : ℝ)))
    (hsteps : Fintype.card V / 2 + 1 ≤ D + radius * growthStep)
    (hsupplyCap : forbidden.card + 2 * D + 10 * m * r ≤ simpleBudget)
    (hdeletionCap :
      forbidden.card + 10 * m * r + D + 10 * mB + D ≤ deletionBudget)
    (hjoinCapacity :
      10 * mB + (m + 2 * radius + mB) + 1 ≤ 10 * m) :
    ∃ A : Adjuster G D m r, Disjoint forbidden A.verts := by
  induction r with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        have hforbiddenBudget : forbidden.card ≤ simpleBudget := by omega
        obtain ⟨B₀, hB⟩ := hsupply forbidden hforbiddenBudget
        exact ⟨B₀.widenRadius hmB, by simpa using hB⟩
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
        have hsupplyCapJ :
            forbidden.card + 2 * D + 10 * m * j ≤ simpleBudget := by
          exact hsupplyCap.trans' <| by
            gcongr
            omega
        have hdeletionCapJ :
            forbidden.card + 10 * m * j + D + 10 * mB + D ≤ deletionBudget := by
          exact hdeletionCap.trans' <| by
            gcongr
            omega
        obtain ⟨A, hforbiddenA⟩ :=
          ih hjpos hsupplyCapJ hdeletionCapJ
        let U := forbidden ∪ A.verts
        have hUcard : U.card ≤ simpleBudget := by
          calc
            U.card ≤ forbidden.card + A.verts.card := Finset.card_union_le _ _
            _ ≤ forbidden.card + (2 * D + 10 * m * j) :=
              Nat.add_le_add_left A.card_verts_le _
            _ ≤ simpleBudget := by simpa [Nat.add_assoc] using hsupplyCapJ
        obtain ⟨B₀, hUB⟩ := hsupply U hUcard
        have hAB : Disjoint A.verts B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzA hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzA]) hzB
        have hforbiddenB : Disjoint forbidden B₀.verts := by
          rw [Finset.disjoint_left]
          intro z hzforbidden hzB
          exact Finset.disjoint_left.1 hUB (by simp [U, hzforbidden]) hzB
        have hbarrier :
            (adjusterJoinBarrier forbidden A B₀).card ≤ deletionBudget := by
          have hAcore := A.core_card_le
          have hBcore := B₀.core_card_le
          have h₁ := Finset.card_union_le forbidden A.core
          have h₂ := Finset.card_union_le (forbidden ∪ A.core) A.rightEnd.verts
          have h₃ := Finset.card_union_le
            (forbidden ∪ A.core ∪ A.rightEnd.verts) B₀.core
          have h₄ := Finset.card_union_le
            (forbidden ∪ A.core ∪ A.rightEnd.verts ∪ B₀.core)
              B₀.rightEnd.verts
          have hAright : A.rightEnd.verts.card = D := A.rightEnd.card_verts
          have hBright : B₀.rightEnd.verts.card = D := B₀.rightEnd.card_verts
          dsimp [adjusterJoinBarrier]
          omega
        have hrate' : ∀ t : ℕ, D ≤ t → t ≤ Fintype.card V / 2 →
            (((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
              expansionEpsilon epsilon expanderK t * (t : ℝ) := by
          intro t hDt ht
          have hnat :
              (adjusterJoinBarrier forbidden A B₀).card + growthStep ≤
                deletionBudget + growthStep := Nat.add_le_add_right hbarrier _
          have hreal :
              (((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
                ((deletionBudget + growthStep : ℕ) : ℝ) := by
            exact_mod_cast hnat
          exact hreal.trans (hrate t hDt ht)
        have hcard :
            A.core.card + B₀.core.card + (m + 2 * radius + mB) + 1 ≤
              10 * m * (j + 1) := by
          have hrest :
              B₀.core.card + (m + 2 * radius + mB) + 1 ≤ 10 * m := by
            have hBcore : B₀.core.card ≤ 10 * mB := by
              simpa using B₀.core_card_le
            calc
              B₀.core.card + (m + 2 * radius + mB) + 1
                  ≤ 10 * mB + (m + 2 * radius + mB) + 1 := by
                    omega
              _ ≤ 10 * m := hjoinCapacity
          calc
            A.core.card + B₀.core.card + (m + 2 * radius + mB) + 1
                = A.core.card +
                    (B₀.core.card + (m + 2 * radius + mB) + 1) := by omega
            _ ≤ 10 * m * j + 10 * m := Nat.add_le_add A.core_card_le hrest
            _ = 10 * m * (j + 1) := by rw [Nat.mul_add]; simp
        have hleftA : expanderK / 2 ≤ (A.leftEnd.verts.card : ℝ) := by
          simpa using hlower
        have hleftB : expanderK / 2 ≤ (B₀.leftEnd.verts.card : ℝ) := by
          simpa using hlower
        have hstepsA : Fintype.card V / 2 + 1 ≤
            A.leftEnd.verts.card + radius * growthStep := by simpa using hsteps
        have hstepsB : Fintype.card V / 2 + 1 ≤
            B₀.leftEnd.verts.card + radius * growthStep := by simpa using hsteps
        have hrateA : ∀ t : ℕ, A.leftEnd.verts.card ≤ t →
            t ≤ Fintype.card V / 2 →
            (((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
              expansionEpsilon epsilon expanderK t * (t : ℝ) := by
          simpa only [A.leftEnd.card_verts] using hrate'
        have hrateB : ∀ t : ℕ, B₀.leftEnd.verts.card ≤ t →
            t ≤ Fintype.card V / 2 →
            (((adjusterJoinBarrier forbidden A B₀).card + growthStep : ℕ) : ℝ) ≤
              expansionEpsilon epsilon expanderK t * (t : ℝ) := by
          simpa only [B₀.leftEnd.card_verts] using hrate'
        exact stepOfLMExpanderGrowth A B₀ hmB epsilon expanderK hexp forbidden
          hAB hforbiddenA hforbiddenB growthStep radius hleftA hleftB
          hrateA hrateB hstepsA hstepsB hcard

end AdjusterJoin

end Erdos63
