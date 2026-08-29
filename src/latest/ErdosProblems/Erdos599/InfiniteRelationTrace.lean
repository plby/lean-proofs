/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingLiteralEdgeWalk
import ErdosProblems.Erdos599.AlternatingMacroReach
import ErdosProblems.Erdos599.RelationKonig
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Infinite two-colour relation walks and alternating traces

This file is the infinite counterpart of `FiniteRelationTrace`.  It selects
an injective ray in a locally finite reachable component, colours its edges,
and cuts the ray at the first subsequent colour change.  Each resulting
integer interval is converted to a finite directed path, in the forward or
reverse orientation as appropriate, and the paths are packaged as an
`InfiniteRunWalk`.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-! ## First-change boundaries -/

/-- The first index after `n` whose colour differs from that at `n`. -/
noncomputable def firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) : ℕ :=
  Nat.find (hchange n)

theorem lt_firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) :
    n < firstChange colour hchange n :=
  (Nat.find_spec (hchange n)).1

theorem colour_firstChange_ne (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) (n : ℕ) :
    colour (firstChange colour hchange n) ≠ colour n :=
  (Nat.find_spec (hchange n)).2

theorem colour_eq_of_lt_firstChange (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n)
    {n k : ℕ} (hnk : n ≤ k) (hk : k < firstChange colour hchange n) :
    colour k = colour n := by
  by_contra hne
  have hle := Nat.find_min' (hchange n) ⟨hnk.lt_of_ne (Ne.symm (by
    intro h
    subst k
    exact hne rfl)), hne⟩
  have hle' : firstChange colour hchange n ≤ k := by
    simpa only [firstChange] using hle
  exact (Nat.not_lt_of_ge hle') hk

/-- Successive endpoints of the maximal monochromatic runs. -/
noncomputable def runBoundary (colour : ℕ → Direction)
    (hchange : ∀ n, ∃ m, n < m ∧ colour m ≠ colour n) : ℕ → ℕ
  | 0 => 0
  | n + 1 => firstChange colour hchange (runBoundary colour hchange n)

@[simp] theorem runBoundary_zero (colour : ℕ → Direction) (hchange) :
    runBoundary colour hchange 0 = 0 := rfl

@[simp] theorem runBoundary_succ (colour : ℕ → Direction) (hchange) (n : ℕ) :
    runBoundary colour hchange (n + 1) =
      firstChange colour hchange (runBoundary colour hchange n) := rfl

theorem runBoundary_lt_succ (colour : ℕ → Direction) (hchange) (n : ℕ) :
    runBoundary colour hchange n < runBoundary colour hchange (n + 1) := by
  rw [runBoundary_succ]
  exact lt_firstChange colour hchange _

theorem runBoundary_strictMono (colour : ℕ → Direction) (hchange) :
    StrictMono (runBoundary colour hchange) :=
  strictMono_nat_of_lt_succ (runBoundary_lt_succ colour hchange)

theorem colour_runBoundary_succ_ne (colour : ℕ → Direction) (hchange) (n : ℕ) :
    colour (runBoundary colour hchange (n + 1)) ≠
      colour (runBoundary colour hchange n) := by
  rw [runBoundary_succ]
  exact colour_firstChange_ne colour hchange _

theorem colour_eq_on_run (colour : ℕ → Direction) (hchange)
    {i k : ℕ} (hlo : runBoundary colour hchange i ≤ k)
    (hhi : k < runBoundary colour hchange (i + 1)) :
    colour k = colour (runBoundary colour hchange i) := by
  rw [runBoundary_succ] at hhi
  exact colour_eq_of_lt_firstChange colour hchange hlo hhi

/-! ## Finite paths cut out of an injective vertex sequence -/

/-- The forward-oriented walk of length `n` starting at position `a`. -/
def forwardIntervalWalk (vertex : ℕ → V) (a : ℕ) :
    (n : ℕ) →
      (∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1))) →
        Walk D (vertex a) (vertex (a + n))
  | 0, _ => .nil
  | n + 1, h =>
      (forwardIntervalWalk vertex a n (fun k hk ↦ h k (hk.trans (Nat.lt_succ_self n)))).concat
        (by simpa [Nat.add_assoc] using h n (Nat.lt_succ_self n))

@[simp] theorem forwardIntervalWalk_support (vertex : ℕ → V) (a n : ℕ) (h) :
    (forwardIntervalWalk (D := D) vertex a n h).support =
      List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i)) := by
  induction n with
  | zero => simp [forwardIntervalWalk]
  | succ n ih =>
      rw [forwardIntervalWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ vertex (a + i))]
      congr 1 <;> simp

theorem forwardIntervalWalk_isPath (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ) (h) :
    (forwardIntervalWalk (D := D) vertex a n h).IsPath := by
  rw [Walk.isPath_iff, forwardIntervalWalk_support]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext
    (Nat.add_left_cancel (hinj hij))

/-- The forward-oriented finite path on the closed index interval
`[a,a+n]`. -/
def forwardIntervalPath (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (a n : ℕ) (h : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1))) :
    FinitePath D where
  start := vertex a
  finish := vertex (a + n)
  walk := forwardIntervalWalk vertex a n h
  isPath := forwardIntervalWalk_isPath vertex hinj a n h

/-- The reverse-oriented walk from position `a+n` back to position `a`. -/
def backwardIntervalWalk (vertex : ℕ → V) (a : ℕ) :
    (n : ℕ) →
      (∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k))) →
        Walk D (vertex (a + n)) (vertex a)
  | 0, _ => .nil
  | n + 1, h =>
      .cons (by simpa [Nat.add_assoc] using h n (Nat.lt_succ_self n))
        (backwardIntervalWalk vertex a n
          (fun k hk ↦ h k (hk.trans (Nat.lt_succ_self n))))

@[simp] theorem backwardIntervalWalk_support (vertex : ℕ → V) (a n : ℕ) (h) :
    (backwardIntervalWalk (D := D) vertex a n h).support =
      (List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i))).reverse := by
  induction n with
  | zero => simp [backwardIntervalWalk]
  | succ n ih =>
      rw [backwardIntervalWalk, Walk.support_cons, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ vertex (a + i))]
      simp

theorem backwardIntervalWalk_isPath (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ) (h) :
    (backwardIntervalWalk (D := D) vertex a n h).IsPath := by
  rw [Walk.isPath_iff, backwardIntervalWalk_support, List.nodup_reverse]
  exact List.nodup_ofFn.mpr fun i j hij ↦ Fin.ext
    (Nat.add_left_cancel (hinj hij))

/-- The reverse-oriented finite path on the closed index interval
`[a,a+n]`. -/
def backwardIntervalPath (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (a n : ℕ) (h : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k))) :
    FinitePath D where
  start := vertex (a + n)
  finish := vertex a
  walk := backwardIntervalWalk vertex a n h
  isPath := backwardIntervalWalk_isPath vertex hinj a n h

theorem set_ofFn_add_eq_image_Icc (vertex : ℕ → V) (a n : ℕ) :
    {x | x ∈ List.ofFn (fun i : Fin (n + 1) ↦ vertex (a + i))} =
      vertex '' Set.Icc a (a + n) := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_ofFn, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨a + i, ⟨Nat.le_add_right _ _, by omega⟩, rfl⟩
  · rintro ⟨k, ⟨hak, hka⟩, rfl⟩
    refine ⟨⟨k - a, by omega⟩, ?_⟩
    rw [Nat.add_sub_of_le hak]

theorem forwardIntervalPath_support (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ) (h) :
    (forwardIntervalPath (D := D) vertex hinj a n h).support =
      vertex '' Set.Icc a (a + n) := by
  rw [FinitePath.support, forwardIntervalPath, forwardIntervalWalk_support]
  exact set_ofFn_add_eq_image_Icc vertex a n

theorem forwardIntervalWalk_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k), vertex (a + k + 1)) ∈ E) :
    (forwardIntervalWalk vertex a n hAdj).edgeSet ⊆ E := by
  induction n with
  | zero => simp [forwardIntervalWalk, Walk.edgeSet]
  | succ n ih =>
      rw [forwardIntervalWalk, RelationComponents.walkEdgeSetConcatRC]
      intro e he
      rcases he with he | he
      · exact ih (fun k hk ↦ hAdj k (hk.trans (Nat.lt_succ_self n)))
          (fun k hk ↦ hE k (hk.trans (Nat.lt_succ_self n))) he
      · simp only [Set.mem_singleton_iff] at he
        subst e
        simpa [Nat.add_assoc] using hE n (Nat.lt_succ_self n)

theorem forwardIntervalPath_edgeSet_subset (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k)) (vertex (a + k + 1)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k), vertex (a + k + 1)) ∈ E) :
    (forwardIntervalPath vertex hinj a n hAdj).edgeSet ⊆ E :=
  forwardIntervalWalk_edgeSet_subset vertex a n hAdj hE

theorem backwardIntervalPath_support (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ) (h) :
    (backwardIntervalPath (D := D) vertex hinj a n h).support =
      vertex '' Set.Icc a (a + n) := by
  rw [FinitePath.support, backwardIntervalPath, backwardIntervalWalk_support]
  simp only [List.mem_reverse]
  exact set_ofFn_add_eq_image_Icc vertex a n

theorem backwardIntervalWalk_edgeSet_subset (vertex : ℕ → V) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k + 1), vertex (a + k)) ∈ E) :
    (backwardIntervalWalk vertex a n hAdj).edgeSet ⊆ E := by
  induction n with
  | zero => simp [backwardIntervalWalk, Walk.edgeSet]
  | succ n ih =>
      rw [backwardIntervalWalk, Walk.edgeSet_cons]
      intro e he
      rcases he with he | he
      · simp only [Set.mem_singleton_iff] at he
        subst e
        simpa [Nat.add_assoc] using hE n (Nat.lt_succ_self n)
      · exact ih (fun k hk ↦ hAdj k (hk.trans (Nat.lt_succ_self n)))
          (fun k hk ↦ hE k (hk.trans (Nat.lt_succ_self n))) he

theorem backwardIntervalPath_edgeSet_subset (vertex : ℕ → V)
    (hinj : Function.Injective vertex) (a n : ℕ)
    (hAdj : ∀ k < n, D.Adj (vertex (a + k + 1)) (vertex (a + k)))
    {E : Set (V × V)}
    (hE : ∀ k < n, (vertex (a + k + 1), vertex (a + k)) ∈ E) :
    (backwardIntervalPath vertex hinj a n hAdj).edgeSet ⊆ E :=
  backwardIntervalWalk_edgeSet_subset vertex a n hAdj hE

/-! ## Compression of an injective two-colour ray -/

/-- Data sufficient to compress an injective two-colour ray.  The two edge
predicates already use ambient orientation: `backwardEdge x y` means that
the ambient graph has the edge `y → x`. -/
structure TwoColourInjectiveRay (D : Digraph V) where
  vertex : ℕ → V
  vertex_injective : Function.Injective vertex
  forwardEdge : V → V → Prop
  backwardEdge : V → V → Prop
  forward_adj : ∀ {x y}, forwardEdge x y → D.Adj x y
  backward_adj : ∀ {x y}, backwardEdge x y → D.Adj y x
  step : ∀ n, forwardEdge (vertex n) (vertex (n + 1)) ∨
    backwardEdge (vertex n) (vertex (n + 1))
  not_eventually_forward : ∀ N, ∃ n, N ≤ n ∧
    ¬ forwardEdge (vertex n) (vertex (n + 1))
  not_eventually_backward : ∀ N, ∃ n, N ≤ n ∧
    ¬ backwardEdge (vertex n) (vertex (n + 1))

namespace TwoColourInjectiveRay

variable (R : TwoColourInjectiveRay D)

noncomputable def colour (n : ℕ) : Direction := by
  classical
  exact if R.forwardEdge (R.vertex n) (R.vertex (n + 1)) then
    .forward else .backward

theorem colour_forward_iff (n : ℕ) : colour R n = Direction.forward ↔
    R.forwardEdge (R.vertex n) (R.vertex (n + 1)) := by
  classical
  unfold colour
  split <;> simp_all

theorem backwardEdge_of_colour_eq_backward (n : ℕ)
    (hcolour : colour R n = Direction.backward) :
    R.backwardEdge (R.vertex n) (R.vertex (n + 1)) := by
  classical
  by_cases h : R.forwardEdge (R.vertex n) (R.vertex (n + 1))
  · simp [colour, h] at hcolour
  · exact (R.step n).resolve_left h

theorem change_exists (n : ℕ) :
    ∃ m, n < m ∧ colour R m ≠ colour R n := by
  cases hc : colour R n with
  | forward =>
      obtain ⟨m, hnm, hm⟩ := R.not_eventually_forward (n + 1)
      refine ⟨m, by omega, ?_⟩
      have hcm : colour R m ≠ Direction.forward := by
        intro h
        exact hm ((R.colour_forward_iff m).mp h)
      simpa [hc] using hcm
  | backward =>
      obtain ⟨m, hnm, hm⟩ := R.not_eventually_backward (n + 1)
      refine ⟨m, by omega, ?_⟩
      have hcm : colour R m = Direction.forward := by
        apply (R.colour_forward_iff m).mpr
        exact (R.step m).resolve_right hm
      simp [hc, hcm]

noncomputable def boundary : ℕ → ℕ :=
  runBoundary R.colour R.change_exists

@[simp] theorem boundary_zero : R.boundary 0 = 0 := rfl

@[simp] theorem boundary_succ (i : ℕ) :
    R.boundary (i + 1) =
      firstChange R.colour R.change_exists (R.boundary i) := rfl

theorem boundary_lt_succ (i : ℕ) : R.boundary i < R.boundary (i + 1) :=
  runBoundary_lt_succ R.colour R.change_exists i

theorem boundary_strictMono : StrictMono R.boundary :=
  runBoundary_strictMono R.colour R.change_exists

theorem colour_eq_on_boundary_interval {i k : ℕ}
    (hlo : R.boundary i ≤ k) (hhi : k < R.boundary (i + 1)) :
    R.colour k = R.colour (R.boundary i) :=
  colour_eq_on_run R.colour R.change_exists hlo hhi

theorem boundary_colours_alternate (i : ℕ) :
    R.colour (R.boundary i) ≠ R.colour (R.boundary (i + 1)) := by
  exact Ne.symm (colour_runBoundary_succ_ne R.colour R.change_exists i)

/-- The `i`th maximal monochromatic interval, bundled as a projected run. -/
noncomputable def projectedRun (i : ℕ) : ProjectedRun D R.vertex := by
  classical
  let a := R.boundary i
  let b := R.boundary (i + 1)
  have hab : a < b := R.boundary_lt_succ i
  let n := b - a
  have han : a + n = b := Nat.add_sub_of_le hab.le
  by_cases hc : R.colour a = Direction.forward
  · have hAdj : ∀ k < n,
        D.Adj (R.vertex (a + k)) (R.vertex (a + k + 1)) := by
      intro k hk
      apply R.forward_adj
      apply (R.colour_forward_iff (a + k)).mp
      rw [R.colour_eq_on_boundary_interval (i := i)]
      · exact hc
      · exact Nat.le_add_right a k
      · dsimp only [a, b] at han ⊢
        rw [← han]
        omega
    let p := forwardIntervalPath R.vertex R.vertex_injective a n hAdj
    let l : Link D :=
      { path := p
        direction := .forward
        nontrivial := by
          dsimp only [p, forwardIntervalPath]
          intro heq
          have := R.vertex_injective heq
          omega }
    refine
      { first := a
        last := b
        first_lt_last := hab
        link := l
        entry_eq := ?_
        exit_eq := ?_
        support_eq := ?_ }
    · rfl
    · dsimp only [l, Link.exit, p, forwardIntervalPath]
      rw [han]
    · dsimp only [l, p]
      rw [forwardIntervalPath_support, han]
  · have hca : R.colour a = Direction.backward := by
      cases h : R.colour a <;> simp_all
    have hAdj : ∀ k < n,
        D.Adj (R.vertex (a + k + 1)) (R.vertex (a + k)) := by
      intro k hk
      apply R.backward_adj
      apply R.backwardEdge_of_colour_eq_backward (a + k)
      rw [R.colour_eq_on_boundary_interval (i := i)]
      · exact hca
      · exact Nat.le_add_right a k
      · dsimp only [a, b] at han ⊢
        rw [← han]
        omega
    let p := backwardIntervalPath R.vertex R.vertex_injective a n hAdj
    let l : Link D :=
      { path := p
        direction := .backward
        nontrivial := by
          dsimp only [p, backwardIntervalPath]
          intro heq
          have := R.vertex_injective heq
          omega }
    refine
      { first := a
        last := b
        first_lt_last := hab
        link := l
        entry_eq := ?_
        exit_eq := ?_
        support_eq := ?_ }
    · dsimp only [l, Link.entry, p, backwardIntervalPath]
    · dsimp only [l, Link.exit, p, backwardIntervalPath]
      rw [han]
    · dsimp only [l, p]
      rw [backwardIntervalPath_support, han]

@[simp] theorem projectedRun_first (i : ℕ) :
    (R.projectedRun i).first = R.boundary i := by
  classical
  by_cases hc : R.colour (R.boundary i) = Direction.forward
  · simp only [projectedRun, hc, ↓reduceDIte]
  · simp only [projectedRun, hc, ↓reduceDIte]

@[simp] theorem projectedRun_last (i : ℕ) :
    (R.projectedRun i).last = R.boundary (i + 1) := by
  classical
  by_cases hc : R.colour (R.boundary i) = Direction.forward
  · simp only [projectedRun, hc, ↓reduceDIte]
  · simp only [projectedRun, hc, ↓reduceDIte]

theorem projectedRun_direction (i : ℕ) :
    (R.projectedRun i).link.direction = R.colour (R.boundary i) := by
  classical
  by_cases hc : R.colour (R.boundary i) = Direction.forward
  · simp only [projectedRun, hc, ↓reduceDIte]
  · simp only [projectedRun, hc, ↓reduceDIte]
    cases h : R.colour (R.boundary i)
    · exact (hc h).elim
    · rfl

theorem projectedRun_forward_edgeSet (i : ℕ)
    (hdir : (R.projectedRun i).link.direction = Direction.forward) :
    (R.projectedRun i).link.path.edgeSet ⊆
      {e | R.forwardEdge e.1 e.2} := by
  classical
  by_cases hc : R.colour (R.boundary i) = Direction.forward
  · simp only [projectedRun, hc, ↓reduceDIte]
    apply forwardIntervalPath_edgeSet_subset
    intro k hk
    apply (R.colour_forward_iff (R.boundary i + k)).mp
    calc
      R.colour (R.boundary i + k) = R.colour (R.boundary i) :=
        R.colour_eq_on_boundary_interval (i := i)
          (Nat.le_add_right _ _) (by
            rw [← Nat.add_sub_of_le (R.boundary_lt_succ i).le]
            omega)
      _ = Direction.forward := hc
  · have : R.colour (R.boundary i) = Direction.backward := by
      cases h : R.colour (R.boundary i) <;> simp_all
    have hd := R.projectedRun_direction i
    rw [hdir] at hd
    exact (hc hd.symm).elim

theorem projectedRun_backward_edgeSet (i : ℕ)
    (hdir : (R.projectedRun i).link.direction = Direction.backward) :
    (R.projectedRun i).link.path.edgeSet ⊆
      {e | R.backwardEdge e.2 e.1} := by
  classical
  by_cases hc : R.colour (R.boundary i) = Direction.forward
  · have hd := R.projectedRun_direction i
    rw [hdir] at hd
    cases hd.trans hc
  · have hca : R.colour (R.boundary i) = Direction.backward := by
      cases h : R.colour (R.boundary i) <;> simp_all
    simp only [projectedRun, hc, ↓reduceDIte]
    apply backwardIntervalPath_edgeSet_subset
    intro k hk
    apply R.backwardEdge_of_colour_eq_backward
    calc
      R.colour (R.boundary i + k) = R.colour (R.boundary i) :=
        R.colour_eq_on_boundary_interval (i := i)
          (Nat.le_add_right _ _) (by
            rw [← Nat.add_sub_of_le (R.boundary_lt_succ i).le]
            omega)
      _ = Direction.backward := hca

/-- Maximal-run compression of the injective two-colour ray. -/
noncomputable def toInfiniteRunWalk : InfiniteRunWalk D where
  vertex := R.vertex
  vertex_injective := R.vertex_injective
  run := R.projectedRun
  starts_zero := by simp
  consecutive i := by simp
  ordered i j hij := by
    simp only [R.projectedRun_last, R.projectedRun_first]
    exact R.boundary_strictMono.monotone (by omega)
  directions_alternate i := by
    rw [R.projectedRun_direction, R.projectedRun_direction]
    exact R.boundary_colours_alternate i

@[simp] theorem toInfiniteRunWalk_vertex (n : ℕ) :
    R.toInfiniteRunWalk.vertex n = R.vertex n := rfl

@[simp] theorem toInfiniteRunWalk_run (i : ℕ) :
    R.toInfiniteRunWalk.run i = R.projectedRun i := rfl

end TwoColourInjectiveRay

/-! ## Specialization to the macro-edge relation -/

variable {Γ : DWeb V}

/-- An injective ray in the macro-edge relation, viewed as a two-colour
ambient walk.  Finite character rules out an eventually constant colour in
both orientations. -/
noncomputable def macroEdgeRay
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1))) :
    TwoColourInjectiveRay Γ.graph where
  vertex := vertex
  vertex_injective := hinj
  forwardEdge x y := (x, y) ∈ familyEdges Z
  backwardEdge x y := (y, x) ∈ familyEdges Y
  forward_adj h := familyEdges_subset_adj Z h
  backward_adj h := familyEdges_subset_adj Y h
  step := hstep
  not_eventually_forward N := by
    by_contra h
    push_neg at h
    apply SwitchingCore.familyEdges_not_containsDirectedRay hZ hZfinite
    let R : DirectedRay V :=
      { vertex := fun n ↦ vertex (N + n)
        injective := fun _ _ heq ↦ Nat.add_left_cancel (hinj heq) }
    refine ⟨R, ?_⟩
    rintro e ⟨n, rfl⟩
    simpa [R, Nat.add_assoc] using h (N + n) (Nat.le_add_right N n)
  not_eventually_backward N := by
    by_contra h
    push_neg at h
    apply SwitchingCore.familyEdges_not_containsReverseDirectedRay hY hYfinite
    let R : DirectedRay V :=
      { vertex := fun n ↦ vertex (N + n)
        injective := fun _ _ heq ↦ Nat.add_left_cancel (hinj heq) }
    refine ⟨R, ?_⟩
    intro n
    simpa [R, Nat.add_assoc] using h (N + n) (Nat.le_add_right N n)

/-- The compressed run walk associated to an injective macro-edge ray. -/
noncomputable def macroEdgeInfiniteRunWalk
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1))) :
    InfiniteRunWalk Γ.graph :=
  (macroEdgeRay hZ hY hZfinite hYfinite vertex hinj hstep).toInfiniteRunWalk

@[simp] theorem macroEdgeInfiniteRunWalk_vertex
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1))) (n : ℕ) :
    (macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite vertex hinj hstep).vertex n =
      vertex n := rfl

theorem macroEdgeInfiniteRunWalk_forward_fragment
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1))) (i : ℕ)
    (hdir : ((macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite
      vertex hinj hstep).run i).link.direction = Direction.forward) :
    IsFragmentOf
      ((macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite
        vertex hinj hstep).run i).link.path Z := by
  let R := macroEdgeRay hZ hY hZfinite hYfinite vertex hinj hstep
  change IsFragmentOf (R.projectedRun i).link.path Z
  apply SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hZ _ (R.projectedRun i).link.nontrivial
  have hs := R.projectedRun_forward_edgeSet i hdir
  intro e he
  have hse := hs he
  change e ∈ familyEdges Z at hse
  exact hse

theorem macroEdgeInfiniteRunWalk_backward_fragment
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1))) (i : ℕ)
    (hdir : ((macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite
      vertex hinj hstep).run i).link.direction = Direction.backward) :
    IsFragmentOf
      ((macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite
        vertex hinj hstep).run i).link.path Y := by
  let R := macroEdgeRay hZ hY hZfinite hYfinite vertex hinj hstep
  change IsFragmentOf (R.projectedRun i).link.path Y
  apply SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hY _ (R.projectedRun i).link.nontrivial
  have hs := R.projectedRun_backward_edgeSet i hdir
  intro e he
  have hse := hs he
  change e ∈ familyEdges Y at hse
  exact hse

theorem macroEdgeInfiniteRunWalk_literalLabels
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (vertex : ℕ → V) (hinj : Function.Injective vertex)
    (hstep : ∀ n, MacroEdge Z Y (vertex n) (vertex (n + 1)))
    (hstart : vertex 0 ∉ Γ.vertexSet Y) :
    InfiniteRunWalk.LiteralBracketLabels
      (macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite vertex hinj hstep) Z Y where
  reference_isWarp := hY
  backward_on := macroEdgeInfiniteRunWalk_backward_fragment
    hZ hY hZfinite hYfinite vertex hinj hstep
  forward_on := macroEdgeInfiniteRunWalk_forward_fragment
    hZ hY hZfinite hYfinite vertex hinj hstep
  initial_outside _ := hstart

/-- A locally finite infinite macro-edge component compiles to a literal
bracket-labelled infinite run walk rooted at the chosen vertex.  Safety is
intentionally not claimed here: it additionally requires the one-interval-
per-`Y`-member provenance supplied by the macro construction. -/
theorem exists_macroEdgeInfiniteRunWalk_of_reachable_infinite
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y) (root : V)
    (hroot : root ∉ Γ.vertexSet Y)
    (hinfinite : {x | Relation.ReflTransGen (MacroEdge Z Y) root x}.Infinite) :
    ∃ W : InfiniteRunWalk Γ.graph,
      W.vertex 0 = root ∧ W.LiteralBracketLabels Z Y := by
  obtain ⟨vertex, hv0, hinj, hstep⟩ :=
    RelationKonig.exists_injective_ray_of_finite_out
      (finite_macroEdge_neighbors hZ hY hZfinite hYfinite) hinfinite
  let W := macroEdgeInfiniteRunWalk hZ hY hZfinite hYfinite vertex hinj hstep
  refine ⟨W, ?_, ?_⟩
  · exact hv0
  · apply macroEdgeInfiniteRunWalk_literalLabels
    simpa only [hv0] using hroot

namespace MacroChain

/-- Compile the infinite reachable component generated by a macro chain to
an injective, maximal-run-compressed, literal bracket-alternating trace. -/
theorem exists_infiniteRunWalk
    {Z Y : Set Γ.DPath} (C : MacroChain Z Y)
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (hroot : (C.z 0).1.initial ∉ Γ.vertexSet Y) :
    ∃ W : InfiniteRunWalk Γ.graph,
      W.vertex 0 = (C.z 0).1.initial ∧
        W.LiteralBracketLabels Z Y := by
  exact exists_macroEdgeInfiniteRunWalk_of_reachable_infinite
    hZ hY hZfinite hYfinite _ hroot
      (C.macroEdge_reachable_infinite hZ hY hZfinite hYfinite hroot)

end MacroChain

/-! ## Literal bracket safety -/

namespace InfiniteRunWalk

theorem isLiteralBracketSafe_of_intervals (W : InfiniteRunWalk Γ.graph)
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hZfinite : Γ.HasFiniteCharacter Z)
    (hlabels : W.LiteralBracketLabels Z Y)
    (hIntervals : ∀ p ∈ Y,
      IsEdgeInterval
        ((.infinite W.toInfiniteTrace : AltPath Γ.graph).directionEdges .backward ∩
          p.edgeSet) p) :
    IsBracketSafe Z Y (.infinite W.toInfiniteTrace) := by
  have hbracket := W.isLiteralBracketAlternating hlabels
  have houtside :
      (.infinite W.toInfiniteTrace : AltPath Γ.graph).edgeSet \ familyEdges Y ⊆
        familyEdges Z := by
    rintro e ⟨he, heY⟩
    rw [AltPath.edgeSet_eq_iUnion_links] at he
    simp only [Set.mem_iUnion] at he
    rcases he with ⟨l, hl, hel⟩
    cases hdir : l.direction with
    | forward =>
        rcases hbracket.2 l hl hdir with ⟨p, hp, hsub⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨p, hp, hsub.2 hel⟩
    | backward =>
        exfalso
        apply heY
        rcases hbracket.1.2.1 l hl hdir with ⟨p, hp, hsub⟩
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨p, hp, hsub.2 hel⟩
  refine ⟨⟨hbracket.1, hIntervals, ?_, ?_⟩, hbracket⟩
  · rintro ⟨R, hR⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hZ hZfinite
      ⟨R, hR.trans houtside⟩
  · rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hZ hZfinite
      ⟨C, hC.trans houtside⟩

end InfiniteRunWalk

end Erdos599.Alternating
