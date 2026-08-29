/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingPrefix

/-!
# Forward orbits from internal contacts of two warp matchings

An internal cut contact need not be an unmatched end of its whole symmetric-
difference component.  Starting at its sending port nevertheless has a
canonical deterministic forward orbit.  Before the first later contact with
a closed set, left uniqueness makes that orbit simple.  This file records the
four honest outcomes: a distinct first return, a projected return to the
starting vertex, a stopped finite orbit, or an injective infinite orbit.

No ambient-source or unmatched-root hypothesis is used.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

/-- A simple one-way port sequence starting at an internal sending contact. -/
structure InfinitePortPrefix (W Y : Set Gamma.DPath) (root : V) where
  port : Nat → Port V
  starts : port 0 = .inl root
  steps : ∀ n, Step W Y (port n) (port (n + 1))
  injective : Function.Injective port

namespace InfinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

def projectedVertex (P : InfinitePortPrefix W Y root) (n : Nat) : V :=
  projectPort (P.port n)

@[simp] theorem projectedVertex_zero (P : InfinitePortPrefix W Y root) :
    P.projectedVertex 0 = root := by
  simp [projectedVertex, P.starts]

end InfinitePortPrefix

/-- A first return whose terminal projects to the starting ambient vertex.
Only the strict prefix is required to be simple; the two terminal ports can
still be distinct copies of the same ambient vertex. -/
structure FiniteProjectedReturn (W Y : Set Gamma.DPath) (X : Set V)
    (root : V) where
  lastIndex : Nat
  positive : 0 < lastIndex
  port : Fin (lastIndex + 1) → Port V
  starts : port 0 = .inl root
  steps : ∀ i : Fin lastIndex, Step W Y (port i.castSucc) (port i.succ)
  injective_before_terminal :
    Function.Injective (fun i : Fin lastIndex => port i.castSucc)
  interior_outside : ∀ i : Fin (lastIndex + 1),
    0 < i.1 → i.1 < lastIndex → projectPort (port i) ∉ X
  terminal_projects_root :
    projectPort (port ⟨lastIndex, Nat.lt_succ_self _⟩) = root

/-- The complete forward-orbit trichotomy, with the projected-root return
split off from the usable distinct-contact branch. -/
inductive ForwardOrbitOutcome (W Y : Set Gamma.DPath) (X : Set V)
    (root : V) : Type u
  | firstReturn (P : FinitePortPrefix W Y root)
      (interior_outside : ∀ i : Fin (P.lastIndex + 1),
        0 < i.1 → i.1 < P.lastIndex → P.projectedVertex i ∉ X)
      (terminal_mem : P.projectedVertex
        ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∈ X)
      (terminal_ne_root : P.projectedVertex
        ⟨P.lastIndex, Nat.lt_succ_self _⟩ ≠ root)
  | projectedReturn (P : FiniteProjectedReturn W Y X root)
  | stopped (P : FinitePortPrefix W Y root)
      (interior_outside : ∀ i : Fin (P.lastIndex + 1),
        0 < i.1 → i.1 < P.lastIndex → P.projectedVertex i ∉ X)
      (terminal_outside : P.projectedVertex
        ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∉ X)
      (terminal_stopped : ¬ ∃ b, Step W Y
        (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
  | infinite (P : InfinitePortPrefix W Y root)
      (positive_outside : ∀ n, 0 < n → P.projectedVertex n ∉ X)

private theorem chain_repeat_reaches_root
    {A : Type*} {R : A → A → Prop} (hleft : Relator.LeftUnique R)
    {f : Nat → A} {N i j : Nat}
    (hsteps : ∀ k, k < N → R (f k) (f (k + 1)))
    (hij : i < j) (hjN : j ≤ N) (heq : f i = f j) :
    ∃ n, 0 < n ∧ n ≤ j ∧ f n = f 0 := by
  induction i generalizing j with
  | zero =>
      exact ⟨j, hij, le_rfl, heq.symm⟩
  | succ i ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hiN : i < N := by omega
      have hjN' : j < N := by omega
      have hright := hsteps j hjN'
      rw [← heq] at hright
      have hprev : f i = f j := hleft (hsteps i hiN) hright
      obtain ⟨n, hnpos, hnj, hnroot⟩ := ih (by omega) (by omega) hprev
      exact ⟨n, hnpos, hnj.trans (Nat.le_succ j), hnroot⟩

/-- The deterministic forward orbit from an internal sending contact reaches
a distinct first closed-set contact, returns projectively to its start, stops
outside the closed set, or continues as a simple infinite orbit outside it. -/
theorem exists_forwardOrbitOutcome
    {W Y : Set Gamma.DPath} (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {X : Set V} {root : V} (hrootX : root ∈ X)
    (hforward : ∃ b, Step W Y (.inl root) b) :
    Nonempty (ForwardOrbitOutcome W Y X root) := by
  classical
  let f := orbit W Y root
  let Event : Nat → Prop := fun n =>
    0 < n ∧ (projectPort (f n) ∈ X ∨ ¬ ∃ b, Step W Y (f n) b)
  by_cases hevent : ∃ n, Event n
  · let N := Nat.find hevent
    have hNevent : Event N := Nat.find_spec hevent
    have hNpos : 0 < N := hNevent.1
    have hbefore : ∀ k, k < N → ∃ b, Step W Y (f k) b := by
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simpa [f] using hforward
      · by_contra hnone
        have hkEvent : Event k := ⟨Nat.pos_of_ne_zero hk0, Or.inr hnone⟩
        have hNk := Nat.find_min' hevent hkEvent
        omega
    have hsteps : ∀ k, k < N → Step W Y (f k) (f (k + 1)) := by
      intro k hk
      change Step W Y (f k) (nextPort W Y (f k))
      exact step_nextPort_of_exists (hbefore k hk)
    have hinterior : ∀ k, 0 < k → k < N → projectPort (f k) ∉ X := by
      intro k hkpos hkN hkX
      have hkEvent : Event k := ⟨hkpos, Or.inl hkX⟩
      have hNk := Nat.find_min' hevent hkEvent
      omega
    have hnoRepeatBefore : ∀ {i j}, i < j → j < N → f i ≠ f j := by
      intro i j hij hjN heq
      obtain ⟨n, hnpos, hnj, hnroot⟩ :=
        chain_repeat_reaches_root (step_biUnique hW hY).1 hsteps hij
          (Nat.le_of_lt hjN) heq
      have hnX : projectPort (f n) ∈ X := by
        rw [hnroot]
        simpa [f] using hrootX
      have hnEvent : Event n := ⟨hnpos, Or.inl hnX⟩
      have hNn := Nat.find_min' hevent hnEvent
      omega
    by_cases hNX : projectPort (f N) ∈ X
    · by_cases hNroot : projectPort (f N) = root
      · let P : FiniteProjectedReturn W Y X root := {
          lastIndex := N
          positive := hNpos
          port := fun i => f i.1
          starts := by simp [f]
          steps := by
            intro i
            exact hsteps i.1 i.2
          injective_before_terminal := by
            intro i j hij
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact hnoRepeatBefore hlt j.2 hij
            · exact hnoRepeatBefore hgt i.2 hij.symm
          interior_outside := by
            intro i hipos hiN
            exact hinterior i.1 hipos hiN
          terminal_projects_root := hNroot }
        exact ⟨.projectedReturn P⟩
      · have hnoRepeatThrough : ∀ {i j}, i < j → j ≤ N → f i ≠ f j := by
          intro i j hij hjN heq
          obtain ⟨n, hnpos, hnj, hnroot⟩ :=
            chain_repeat_reaches_root (step_biUnique hW hY).1 hsteps
              hij hjN heq
          by_cases hnlt : n < N
          · have hnX : projectPort (f n) ∈ X := by
              rw [hnroot]
              simpa [f] using hrootX
            have hnEvent : Event n := ⟨hnpos, Or.inl hnX⟩
            have hNn := Nat.find_min' hevent hnEvent
            omega
          · have hnEq : n = N := by omega
            apply hNroot
            rw [← hnEq, hnroot]
            simp [f]
        let P : FinitePortPrefix W Y root := {
          lastIndex := N
          positive := hNpos
          port := fun i => f i.1
          starts := by simp [f]
          steps := by
            intro i
            exact hsteps i.1 i.2
          injective := by
            intro i j hij
            apply Fin.ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact hnoRepeatThrough hlt (Nat.le_of_lt_succ j.2) hij
            · exact hnoRepeatThrough hgt (Nat.le_of_lt_succ i.2) hij.symm }
        exact ⟨.firstReturn P
          (by
            intro i hipos hiN
            exact hinterior i.1 hipos hiN)
          (by simpa [P, FinitePortPrefix.projectedVertex] using hNX)
          (by simpa [P, FinitePortPrefix.projectedVertex] using hNroot)⟩
    · have hNstop : ¬ ∃ b, Step W Y (f N) b :=
        hNevent.2.resolve_left hNX
      have hNoutside : projectPort (f N) ∉ X := hNX
      have hNroot : projectPort (f N) ≠ root := by
        intro h
        apply hNoutside
        rw [h]
        exact hrootX
      have hnoRepeatThrough : ∀ {i j}, i < j → j ≤ N → f i ≠ f j := by
        intro i j hij hjN heq
        obtain ⟨n, hnpos, hnj, hnroot⟩ :=
          chain_repeat_reaches_root (step_biUnique hW hY).1 hsteps hij hjN heq
        by_cases hnlt : n < N
        · have hnX : projectPort (f n) ∈ X := by
            rw [hnroot]
            simpa [f] using hrootX
          have hnEvent : Event n := ⟨hnpos, Or.inl hnX⟩
          have hNn := Nat.find_min' hevent hnEvent
          omega
        · have hnEq : n = N := by omega
          apply hNroot
          rw [← hnEq, hnroot]
          simp [f]
      let P : FinitePortPrefix W Y root := {
        lastIndex := N
        positive := hNpos
        port := fun i => f i.1
        starts := by simp [f]
        steps := by
          intro i
          exact hsteps i.1 i.2
        injective := by
          intro i j hij
          apply Fin.ext
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hnoRepeatThrough hlt (Nat.le_of_lt_succ j.2) hij
          · exact hnoRepeatThrough hgt (Nat.le_of_lt_succ i.2) hij.symm }
      exact ⟨.stopped P
        (by
          intro i hipos hiN
          exact hinterior i.1 hipos hiN)
        (by simpa [P, FinitePortPrefix.projectedVertex] using hNoutside)
        (by simpa [P] using hNstop)⟩
  · have hall : ∀ n, ∃ b, Step W Y (f n) b := by
      intro n
      by_cases hn0 : n = 0
      · subst n
        simpa [f] using hforward
      · by_contra hnone
        apply hevent
        exact ⟨n, Nat.pos_of_ne_zero hn0, Or.inr hnone⟩
    have hsteps : ∀ n, Step W Y (f n) (f (n + 1)) := by
      intro n
      change Step W Y (f n) (nextPort W Y (f n))
      exact step_nextPort_of_exists (hall n)
    have houtside : ∀ n, 0 < n → projectPort (f n) ∉ X := by
      intro n hnpos hnX
      apply hevent
      exact ⟨n, hnpos, Or.inl hnX⟩
    have hinjective : Function.Injective f := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · obtain ⟨n, hnpos, _hnj, hnroot⟩ :=
          chain_repeat_reaches_root (step_biUnique hW hY).1
            (fun k _hk => hsteps k) hlt (le_refl j) hij
        apply houtside n hnpos
        rw [hnroot]
        simpa [f] using hrootX
      · obtain ⟨n, hnpos, _hni, hnroot⟩ :=
          chain_repeat_reaches_root (step_biUnique hW hY).1
            (fun k _hk => hsteps k) hgt (le_refl i) hij.symm
        apply houtside n hnpos
        rw [hnroot]
        simpa [f] using hrootX
    let P : InfinitePortPrefix W Y root := {
      port := f
      starts := by simp [f]
      steps := hsteps
      injective := hinjective }
    exact ⟨.infinite P (by
      intro n hnpos
      exact houtside n hnpos)⟩

end

end TwoWarpMatchingTraversal
end Erdos599
