/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Core
import ErdosProblems.Erdos599.RelationalRoof
import ErdosProblems.Erdos599.Wave

/-!
# Erdős Problem 599: concrete waves

This file connects the source-faithful directed paths and roofs in
`Core.lean` to the abstract order-theoretic wave calculus in `Wave.lean`.
The elementary path-system interface and the full roofed-path interface are
instantiated outright.  The main concrete obligation is the prefix-splicing
lemma `pathSupportRoof`, proved below for both finite paths and rays.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} (Γ : DWeb V)

/-- The concrete path API as an abstract wave-calculus path system. -/
def wavePathSystem : WaveCore.DirectedPathSystem V Γ.DPath where
  support := DirectedPath.Path.support
  initial := DirectedPath.Path.initial
  terminal := Γ.terminal?
  initial_mem := DirectedPath.Path.initial_mem_support
  terminal_mem := fun _ _ h ↦ Γ.terminal_mem_support h
  trivial := Γ.trivialPath
  support_trivial := Γ.support_trivialPath
  initial_trivial := Γ.initial_trivialPath
  terminal_trivial := Γ.terminal?_trivialPath
  Extends := Γ.Extends
  extends_refl := Γ.extends_refl
  extends_trans := Γ.extends_trans
  extends_initial := Γ.extends_initial
  support_mono_of_extends := Γ.support_mono_of_extends

@[simp]
theorem wavePathSystem_support (p : Γ.DPath) :
    (Γ.wavePathSystem).support p = p.support :=
  rfl

@[simp]
theorem wavePathSystem_initial (p : Γ.DPath) :
    (Γ.wavePathSystem).initial p = p.initial :=
  rfl

@[simp]
theorem wavePathSystem_terminal (p : Γ.DPath) :
    (Γ.wavePathSystem).terminal p = Γ.terminal? p :=
  rfl

@[simp]
theorem wavePathSystem_vertexSet (W : Set Γ.DPath) :
    (Γ.wavePathSystem).vertexSet W = Γ.vertexSet W :=
  rfl

@[simp]
theorem wavePathSystem_initialSet (W : Set Γ.DPath) :
    (Γ.wavePathSystem).initialSet W = Γ.initialSet W :=
  rfl

@[simp]
theorem wavePathSystem_terminalSet (W : Set Γ.DPath) :
    (Γ.wavePathSystem).terminalSet W = Γ.terminalFrontier W :=
  rfl

@[simp]
theorem wavePathSystem_isWarp (W : Set Γ.DPath) :
    (Γ.wavePathSystem).IsWarp W ↔ Γ.IsWarp W :=
  Iff.rfl

/-! ### Prefixes and loop erasure -/

/-- A vertex of a finite walk can be reached by an initial segment of that
walk. -/
private theorem walk_exists_prefix_to_mem {a b x : V}
    (p : DirectedPath.Walk Γ.graph a b) (hx : x ∈ p.support) :
    ∃ q : DirectedPath.Walk Γ.graph a x, q.support <+: p.support := by
  let hmeet : p.Meets ({x} : Set V) := ⟨x, hx, Set.mem_singleton x⟩
  let F := DirectedPath.Walk.firstHit p ({x} : Set V) hmeet
  have hFx : F.endpoint = x := Set.mem_singleton_iff.mp F.endpoint_mem
  rw [← hFx]
  exact ⟨F.walk, F.support_prefix⟩

/-- The finite walk from the initial vertex of a ray to its `n`th vertex. -/
private def rayPrefixWalk (r : DirectedPath.Ray Γ.graph) :
    (n : ℕ) → DirectedPath.Walk Γ.graph r.initial (r n)
  | 0 => .nil
  | n + 1 => (rayPrefixWalk r n).concat (r.adj_succ n)

private theorem rayPrefixWalk_support_subset (r : DirectedPath.Ray Γ.graph)
    (n : ℕ) : ∀ {x : V}, x ∈ (Γ.rayPrefixWalk r n).support → x ∈ r.support := by
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = r 0 := by simpa [rayPrefixWalk, DirectedPath.Ray.initial] using hx
      exact hx0 ▸ r.apply_mem_support 0
  | succ n ih =>
      intro x hx
      rw [rayPrefixWalk, DirectedPath.Walk.support_concat] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      exact hx.elim ih (fun h ↦ h ▸ r.apply_mem_support (n + 1))

/-- The concrete form of the sole path-splicing obligation in
`WaveCore.RoofedPathSystem`.  It is stated separately so that its eventual
proof cannot be hidden inside an instance declaration. -/
def PathSupportRoofProperty : Prop :=
  ∀ (p : Γ.DPath) (S : Set V),
    p.initial ∈ Γ.roof S →
      (∀ t, Γ.terminal? p = some t → t ∈ S) →
      p.support ∩ S ⊆
        (match Γ.terminal? p with
        | some t => ({t} : Set V)
        | none => ∅) →
      p.support ⊆ Γ.roof S

/-- Prefix-splicing proves the concrete path-support roof property.  For a
finite member, a prefix which reached its terminal would be the whole path;
for a ray, every finite prefix avoids the terminal frontier.  Appending an
arbitrary target path and applying walk-level loop erasure via
`RelationalRoof.roof_meets_walk` gives the contradiction. -/
theorem pathSupportRoof : Γ.PathSupportRoofProperty := by
  intro p S hinit hterminal hinter x hxp q hq
  by_contra hqmeet
  have hqAvoid : ∀ {y : V}, y ∈ q.walk.support → y ∉ S := by
    intro y hy hyS
    exact hqmeet ⟨y, hy, hyS⟩
  have hxNotS : x ∉ S := by
    intro hxS
    apply hqmeet
    refine ⟨x, ?_, hxS⟩
    simpa [hq.1] using q.start_mem_support
  let qwalk : DirectedPath.Walk Γ.graph x q.finish :=
    RelationalRoof.castStart Γ.graph.Adj hq.1 q.walk
  rcases p with fp | r
  · change x ∈ fp.walk.support at hxp
    obtain ⟨pre, hpre⟩ := Γ.walk_exists_prefix_to_mem fp.walk hxp
    have hpreAvoid : ∀ {y : V}, y ∈ pre.support → y ∉ S := by
      intro y hypre hyS
      have hyp : y ∈ (Path.support (.inl fp) : Set V) := hpre.subset hypre
      have hyfinish : y = fp.finish := by
        have hy := hinter ⟨hyp, hyS⟩
        simpa using hy
      have hfinishpre : fp.finish ∈ pre.support := hyfinish ▸ hypre
      have hlast : fp.walk.support.getLast fp.walk.support_ne_nil ∈ pre.support := by
        rw [fp.walk.getLast_support]
        exact hfinishpre
      have heq : pre.support = fp.walk.support :=
        List.Nodup.eq_of_getLast_mem_of_prefix hpre hlast fp.isPath
      have hxfinish : x = fp.finish := by
        calc
          x = pre.support.getLast pre.support_ne_nil := pre.getLast_support.symm
          _ = fp.walk.support.getLast fp.walk.support_ne_nil :=
            List.getLast_congr pre.support_ne_nil fp.walk.support_ne_nil heq
          _ = fp.finish := fp.walk.getLast_support
      exact hxNotS (by simpa [hyfinish, hxfinish] using hyS)
    let w := pre.append qwalk
    have hwAvoid : ∀ {y : V}, y ∈ w.support → y ∉ S := by
      intro y hy hyS
      dsimp only [w] at hy
      rw [DirectedPath.Walk.support_append] at hy
      rcases List.mem_append.1 hy with hypre | hyq
      · exact hpreAvoid hypre hyS
      · apply hqAvoid (List.mem_of_mem_tail ?_) hyS
        simpa [qwalk, RelationalRoof.support_castStart] using hyq
    have hwMeet : w.Meets S :=
      RelationalRoof.roof_meets_walk Γ.graph.Adj Γ.target hinit w hq.2
    obtain ⟨y, hyw, hyS⟩ := hwMeet
    exact hwAvoid hyw hyS
  · obtain ⟨n, hnx⟩ := hxp
    let pre := Γ.rayPrefixWalk r n
    have hpreAvoid : ∀ {y : V}, y ∈ pre.support → y ∉ S := by
      intro y hypre hyS
      have hyr : y ∈ (Path.support (.inr r) : Set V) :=
        Γ.rayPrefixWalk_support_subset r n hypre
      have hy := hinter ⟨hyr, hyS⟩
      simpa using hy
    let qwalk' : DirectedPath.Walk Γ.graph (r n) q.finish :=
      RelationalRoof.castStart Γ.graph.Adj (hq.1.trans hnx.symm) q.walk
    let w := pre.append qwalk'
    have hwAvoid : ∀ {y : V}, y ∈ w.support → y ∉ S := by
      intro y hy hyS
      dsimp only [w] at hy
      rw [DirectedPath.Walk.support_append] at hy
      rcases List.mem_append.1 hy with hypre | hyq
      · exact hpreAvoid hypre hyS
      · apply hqAvoid (List.mem_of_mem_tail ?_) hyS
        simpa [qwalk', RelationalRoof.support_castStart] using hyq
    have hwMeet : w.Meets S :=
      RelationalRoof.roof_meets_walk Γ.graph.Adj Γ.target hinit w hq.2
    obtain ⟨y, hyw, hyS⟩ := hwMeet
    exact hwAvoid hyw hyS

/-- The full concrete instance of the abstract roofed path calculus. -/
def waveRoofSystem :
    WaveCore.RoofedPathSystem V Γ.DPath where
  toDirectedPathSystem := Γ.wavePathSystem
  roof := Γ.roof
  subset_roof := Γ.subset_roof
  roof_mono := Γ.roof_mono
  roof_cut := Γ.roof_cut
  path_support_roof := Γ.pathSupportRoof
  roof_essential := Γ.roof_essential

/-! ## Concrete wave predicates -/

/-- A concrete wave in `Γ`: a disjoint source-starting warp whose finite
terminal frontier separates the source from the target. -/
def IsWave (W : Set Γ.DPath) : Prop :=
  Γ.IsWarp W ∧ Γ.initialSet W ⊆ Γ.source ∧
    Γ.source ⊆ Γ.roof (Γ.terminalFrontier W)

/-- A wave missing a source as an initial vertex. -/
def IsHindrance (W : Set Γ.DPath) : Prop :=
  Γ.IsWave W ∧ Γ.initialSet W ≠ Γ.source

/-- No concrete hindrance exists. -/
def IsUnhindered : Prop :=
  ¬ ∃ W : Set Γ.DPath, Γ.IsHindrance W

/-- The family of all length-zero paths based at the source. -/
def trivialWave : Set Γ.DPath :=
  Γ.trivialPath '' Γ.source

/-- A concrete web is loose when its only wave is the trivial wave. -/
def IsLoose : Prop :=
  ∀ W : Set Γ.DPath, Γ.IsWave W → W = Γ.trivialWave

/-- Concrete forward extension of whole warps. -/
def ForwardExtension (U W : Set Γ.DPath) : Prop :=
  (∀ p ∈ U, ∃ q ∈ W, Γ.Extends p q) ∧
    (∀ q ∈ W, ∃ p ∈ U, Γ.Extends p q)

/-- Concrete roof order, distinct from forward extension. -/
def RoofLE (U W : Set Γ.DPath) : Prop :=
  Γ.roof (Γ.terminalFrontier U) ⊆ Γ.roof (Γ.terminalFrontier W)

theorem isWave_iff_abstract (W : Set Γ.DPath) :
    Γ.IsWave W ↔ Γ.waveRoofSystem.IsWave Γ.source W :=
  Iff.rfl

theorem forwardExtension_iff_abstract (U W : Set Γ.DPath) :
    Γ.ForwardExtension U W ↔
      Γ.waveRoofSystem.ForwardExtension U W :=
  Iff.rfl

theorem roofLE_iff_abstract (U W : Set Γ.DPath) :
    Γ.RoofLE U W ↔ Γ.waveRoofSystem.RoofLE U W :=
  Iff.rfl

/-! ## Elementary concrete wave facts -/

theorem initialSet_trivialWave : Γ.initialSet Γ.trivialWave = Γ.source := by
  exact (Γ.wavePathSystem).initialSet_trivialWarp Γ.source

theorem terminalFrontier_trivialWave :
    Γ.terminalFrontier Γ.trivialWave = Γ.source := by
  exact (Γ.wavePathSystem).terminalSet_trivialWarp Γ.source

theorem isWarp_trivialWave : Γ.IsWarp Γ.trivialWave := by
  exact (Γ.wavePathSystem).isWarp_trivialWarp Γ.source

theorem isWave_trivialWave : Γ.IsWave Γ.trivialWave := by
  refine ⟨Γ.isWarp_trivialWave, ?_, ?_⟩
  · rw [Γ.initialSet_trivialWave]
  · rw [Γ.terminalFrontier_trivialWave]
    exact Γ.subset_roof Γ.source

theorem isUnhindered_iff :
    Γ.IsUnhindered ↔
      ∀ W : Set Γ.DPath, Γ.IsWave W → Γ.initialSet W = Γ.source := by
  simp only [IsUnhindered, IsHindrance, not_exists, not_and,
    Decidable.not_not]

theorem isLoose_iff :
    Γ.IsLoose ↔
      ∀ W : Set Γ.DPath, Γ.IsWave W ↔ W = Γ.trivialWave := by
  constructor
  · intro h W
    exact ⟨h W, fun hW ↦ hW ▸ Γ.isWave_trivialWave⟩
  · intro h W hW
    exact (h W).1 hW

/-- Essential trimming preserves a concrete wave and discards every ray. -/
theorem IsWave.essentialWarpPart {W : Set Γ.DPath} (hW : Γ.IsWave W) :
    Γ.IsWave (Γ.essentialWarpPart W) := by
  refine ⟨hW.1.essentialWarpPart, ?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩
    exact hW.2.1 ⟨p, hp.1, rfl⟩
  · rw [Γ.terminalFrontier_essentialWarpPart, Γ.roof_essential]
    exact hW.2.2

/-- Every concrete wave is contained in the roof of its finite terminal
frontier.  This includes ray members, which meet that frontier nowhere. -/
theorem IsWave.self_roofing {W : Set Γ.DPath} (hW : Γ.IsWave W) :
    Γ.vertexSet W ⊆ Γ.roof (Γ.terminalFrontier W) := by
  have hA : Γ.waveRoofSystem.IsWave Γ.source W :=
    (Γ.isWave_iff_abstract W).1 hW
  exact WaveCore.RoofedPathSystem.IsWave.self_roofing Γ.waveRoofSystem hA

theorem IsWave.ray_support_subset_roof {W : Set Γ.DPath}
    (hW : Γ.IsWave W) {r : DirectedPath.Ray Γ.graph}
    (hr : (Sum.inr r : Γ.DPath) ∈ W) :
    r.support ⊆ Γ.roof (Γ.terminalFrontier W) := by
  intro x hx
  exact IsWave.self_roofing Γ hW ⟨(Sum.inr r : Γ.DPath), hr, hx⟩

/-- The concrete roof-cut lemma, exported at the wave layer. -/
theorem roof_cut_concrete {X S : Set V} (hXS : X ⊆ Γ.roof S) :
    Γ.roof X ⊆ Γ.roof S :=
  Γ.roof_cut hXS

theorem forwardExtension_refl (W : Set Γ.DPath) : Γ.ForwardExtension W W :=
  ⟨fun p hp ↦ ⟨p, hp, Γ.extends_refl p⟩,
    fun p hp ↦ ⟨p, hp, Γ.extends_refl p⟩⟩

theorem forwardExtension_trans {U W Z : Set Γ.DPath}
    (hUW : Γ.ForwardExtension U W) (hWZ : Γ.ForwardExtension W Z) :
    Γ.ForwardExtension U Z := by
  constructor
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := hUW.1 p hp
    obtain ⟨r, hr, hqr⟩ := hWZ.1 q hq
    exact ⟨r, hr, Γ.extends_trans hpq hqr⟩
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hWZ.2 r hr
    obtain ⟨p, hp, hpq⟩ := hUW.2 q hq
    exact ⟨p, hp, Γ.extends_trans hpq hqr⟩

theorem initialSet_eq_of_forwardExtension {U W : Set Γ.DPath}
    (h : Γ.ForwardExtension U W) : Γ.initialSet U = Γ.initialSet W := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := h.1 p hp
    exact ⟨q, hq, (Γ.extends_initial hpq).symm⟩
  · rintro x ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ := h.2 q hq
    exact ⟨p, hp, Γ.extends_initial hpq⟩

/-- Explicit structural conditions for a concrete splice result. -/
def IsSpliceResult (U W R : Set Γ.DPath) : Prop :=
  Γ.IsWarp R ∧ Γ.initialSet R ⊆ Γ.initialSet U ∧
    Γ.terminalFrontier R = Γ.terminalFrontier W

/-- Wave splicing after the concrete path operation has discharged its
three structural obligations. -/
theorem isWave_splice {U W R : Set Γ.DPath}
    (hU : Γ.IsWave U)
    (hW : Γ.IsWarp W ∧
      Γ.initialSet W ⊆ Γ.terminalFrontier U ∧
      Γ.terminalFrontier U ⊆ Γ.roof (Γ.terminalFrontier W))
    (hR : Γ.IsSpliceResult U W R) : Γ.IsWave R := by
  refine ⟨hR.1, hR.2.1.trans hU.2.1, ?_⟩
  exact hU.2.2.trans (Γ.roof_cut hW.2.2) |>.trans_eq
    (congrArg Γ.roof hR.2.2).symm

/-- Concrete waves packaged as a type for Zorn's lemma. -/
abbrev Wave := {W : Set Γ.DPath // Γ.IsWave W}

instance waveLE : LE Γ.Wave where
  le U W := Γ.ForwardExtension U.1 W.1

instance wavePreorder : Preorder Γ.Wave where
  le U W := Γ.ForwardExtension U.1 W.1
  lt U W := Γ.ForwardExtension U.1 W.1 ∧ ¬Γ.ForwardExtension W.1 U.1
  le_refl W := Γ.forwardExtension_refl W.1
  le_trans _ _ _ := Γ.forwardExtension_trans
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- The Zorn step with the concrete chain-upper-bound lemma supplied
explicitly.  The iterated-arrow development is responsible for that lemma. -/
theorem exists_maximal_forward_extension
    (W₀ : Γ.Wave)
    (hchain : ∀ c : Set Γ.Wave, IsChain (· ≤ ·) c → c.Nonempty →
      ∃ ub : Γ.Wave, ∀ W ∈ c, W ≤ ub) :
    ∃ M : Γ.Wave, W₀ ≤ M ∧ IsMax M := by
  apply zorn_le_nonempty_Ici₀ W₀
  · intro c hcIci hc y hy
    obtain ⟨ub, hub⟩ := hchain c hc ⟨y, hy⟩
    exact ⟨ub, hub⟩
  · exact le_rfl

end DWeb

end Erdos599
