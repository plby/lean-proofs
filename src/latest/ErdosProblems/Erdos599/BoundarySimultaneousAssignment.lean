/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SimultaneousAssignment
import ErdosProblems.Erdos599.RawAlternatingDichotomy
import ErdosProblems.Erdos599.SafeAlternatingDichotomy

/-!
# Simultaneous assignment at an internal fracture boundary

The holes `W ↾ X` in Assertion 9.31 do not in general start in the
ambient source or end in the ambient target: an endpoint may be a junction
on the closing set `X`.  The endpoint-pure specialization of Theorem 4.12 is
therefore not the right interface.

This file isolates the exact replacement.  First, the touching fragments of
a `FracturedWarp` are recombined using the honest warp already carried by
that structure.  Second, the macro-orbit proof of Theorem 4.12 is run under
the two boundary facts it actually uses: a recombined initial (respectively
terminal) which lies on the reference warp is a reference initial
(respectively terminal).  No membership in the ambient web sides occurs.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FracturedWarp

/-- Recombine all terminal--initial fracture junctions.  `edgeWarp` is part
of the definition of a fractured warp precisely to certify that this can be
done without changing the union of directed edges. -/
def recombined (Z : FracturedWarp Gamma) : FracturedWarp Gamma where
  paths := Z.edgeWarp
  edgeWarp := Z.edgeWarp
  edgeWarp_isWarp := Z.edgeWarp_isWarp
  same_edges := rfl
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    exact (hmeet (Z.edgeWarp_isWarp hp hq hpq)).elim

@[simp] theorem recombined_paths (Z : FracturedWarp Gamma) :
    Z.recombined.paths = Z.edgeWarp := rfl

theorem recombined_isWarp (Z : FracturedWarp Gamma) :
    Gamma.IsWarp Z.recombined.paths := Z.edgeWarp_isWarp

theorem familyEdges_recombined (Z : FracturedWarp Gamma) :
    familyEdges Z.recombined.paths = familyEdges Z.paths := Z.same_edges.symm

end FracturedWarp

/-- The endpoint alignment supplied by closure under the reference warp.
It is strictly weaker than requiring endpoints to lie in the ambient source
and target, and it permits internal closing-set junctions. -/
def BoundaryAligned (Z Y : Set Gamma.DPath) : Prop :=
  Gamma.initialSet Z ∩ Gamma.vertexSet Y ⊆ Gamma.initialSet Y ∧
    Gamma.terminalFrontier Z ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y

namespace BoundaryAligned

theorem initial_outside {Z Y : Set Gamma.DPath} (h : BoundaryAligned Z Y)
    {x : V} (hx : x ∈ Gamma.initialSet Z \ Gamma.initialSet Y) :
    x ∉ Gamma.vertexSet Y := by
  intro hxY
  exact hx.2 (h.1 ⟨hx.1, hxY⟩)

end BoundaryAligned

namespace MacroStep

/-- A covered terminal supplies the next macro step using only terminal
alignment, with no ambient target-side hypothesis. -/
theorem exists_of_terminal_boundary
    {Z Y : Set Gamma.DPath}
    (hterminal : Gamma.terminalFrontier Z ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hinit : Gamma.initialSet Y ⊆ Gamma.initialSet Z)
    (p : Z) (hpY : ∀ t, Gamma.terminal? p.1 = some t →
      t ∈ Gamma.vertexSet Y) :
    ∃ r : Z, MacroStep Z Y p r := by
  obtain ⟨fp, hfp⟩ := hZfinite p.2
  have hpterm : Gamma.terminal? p.1 = some fp.finish := by
    simpa [hfp]
  have htZ : fp.finish ∈ Gamma.terminalFrontier Z :=
    ⟨p.1, p.2, hpterm⟩
  have htY : fp.finish ∈ Gamma.vertexSet Y := hpY fp.finish hpterm
  rcases hterminal ⟨htZ, htY⟩ with ⟨q, hqY, hqterm⟩
  have hqinit : q.initial ∈ Gamma.initialSet Y := ⟨q, hqY, rfl⟩
  rcases hinit hqinit with ⟨r, hrZ, hrinit⟩
  exact ⟨⟨r, hrZ⟩, ⟨⟨q, hqY⟩, fp.finish, hpterm, hqterm,
    hrinit.symm⟩⟩

end MacroStep

/-- The deterministic macro orbit under literal boundary alignment. -/
theorem finiteMacroRoute_or_infiniteMacroChain_of_boundary
    {Z Y : Set Gamma.DPath}
    (hterminal : Gamma.terminalFrontier Z ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hinit : Gamma.initialSet Y ⊆ Gamma.initialSet Z)
    (p0 : Z) :
    (∃ C : FiniteMacroRoute Gamma Z Y,
      C.z ⟨0, Nat.zero_lt_succ _⟩ = p0) ∨
    (∃ C : MacroChain Z Y, C.z 0 = p0) := by
  classical
  let Covered : Z → Prop := fun p ↦
    ∀ t, Gamma.terminal? p.1 = some t → t ∈ Gamma.vertexSet Y
  have hstep (p : Z) (hp : Covered p) : ∃ r : Z, MacroStep Z Y p r :=
    MacroStep.exists_of_terminal_boundary hterminal hZfinite hinit p hp
  let next : Z → Z := fun p ↦
    if hp : Covered p then Classical.choose (hstep p hp) else p
  have next_step {p : Z} (hp : Covered p) :
      MacroStep Z Y p (next p) := by
    simp only [next, dif_pos hp]
    exact Classical.choose_spec (hstep p hp)
  let z : ℕ → Z := fun n ↦ Nat.rec p0 (fun _ p ↦ next p) n
  have z_zero : z 0 = p0 := rfl
  have z_succ (n : ℕ) : z (n + 1) = next (z n) := by simp [z]
  by_cases hall : ∀ n, Covered (z n)
  · right
    have hzstep (n : ℕ) : MacroStep Z Y (z n) (z (n + 1)) := by
      rw [z_succ]
      exact next_step (hall n)
    let y : ℕ → Y := fun n ↦ Classical.choose (hzstep n)
    let terminal : ℕ → V := fun n ↦
      Classical.choose (Classical.choose_spec (hzstep n))
    have hspec (n : ℕ) :
        Gamma.terminal? (z n).1 = some (terminal n) ∧
          Gamma.terminal? (y n).1 = some (terminal n) ∧
            (y n).1.initial = (z (n + 1)).1.initial :=
      Classical.choose_spec (Classical.choose_spec (hzstep n))
    exact ⟨{
      z := z
      y := y
      terminal := terminal
      z_terminal := fun n ↦ (hspec n).1
      y_terminal := fun n ↦ (hspec n).2.1
      joins := fun n ↦ (hspec n).2.2 }, z_zero⟩
  · left
    have hex : ∃ n, ¬ Covered (z n) := by simpa only [not_forall] using hall
    let N : ℕ := Nat.find hex
    have hN : ¬ Covered (z N) := Nat.find_spec hex
    have hbefore {n : ℕ} (hn : n < N) : Covered (z n) := by
      by_contra hncovered
      exact Nat.find_min hex hn hncovered
    have hzstep (n : Fin N) :
        MacroStep Z Y (z n.1) (z (n.1 + 1)) := by
      rw [z_succ]
      exact next_step (hbefore n.isLt)
    let y : Fin N → Y := fun n ↦ Classical.choose (hzstep n)
    let terminal : Fin N → V := fun n ↦
      Classical.choose (Classical.choose_spec (hzstep n))
    have hspec (n : Fin N) :
        Gamma.terminal? (z n.1).1 = some (terminal n) ∧
          Gamma.terminal? (y n).1 = some (terminal n) ∧
            (y n).1.initial = (z (n.1 + 1)).1.initial :=
      Classical.choose_spec (Classical.choose_spec (hzstep n))
    have hfinal : ∃ t, Gamma.terminal? (z N).1 = some t ∧
        t ∉ Gamma.vertexSet Y := by
      dsimp only [Covered] at hN
      push_neg at hN
      exact hN
    let t : V := Classical.choose hfinal
    have ht := Classical.choose_spec hfinal
    exact ⟨{
      lastIndex := N
      z := fun i ↦ z i.1
      y := y
      terminal := terminal
      z_terminal := fun i ↦ (hspec i).1
      y_terminal := fun i ↦ (hspec i).2.1
      joins := fun i ↦ (hspec i).2.2
      finalTerminal := t
      final_terminal := ht.1
      final_uncovered := ht.2 }, z_zero⟩

/-- Boundary-aligned form of Lemma 4.13. -/
theorem safeAlternatingDichotomy_of_boundary
    {Z Y : Set Gamma.DPath}
    (hterminal : Gamma.terminalFrontier Z ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinit : Gamma.initialSet Y ⊆ Gamma.initialSet Z)
    {u : V} (hu : u ∈ Gamma.initialSet Z \ Gamma.vertexSet Y) :
    SafeAlternatingDichotomy Z Y u := by
  obtain ⟨p, hpZ, hpinit⟩ := hu.1
  let p0 : Z := ⟨p, hpZ⟩
  by_cases huT : u ∈ Gamma.terminalFrontier Z
  · exact safeAlternatingDichotomy_of_mem_terminalFrontier hZ hY huT hu.2
  rcases finiteMacroRoute_or_infiniteMacroChain_of_boundary
      hterminal hZfinite hinit p0 with
      ⟨C, hC0⟩ | ⟨C, hC0⟩
  · let K := C.compilation hZ hY hZfinite hYfinite
        (by rw [hC0]; exact hpinit) huT (by rw [hC0, hpinit]; exact hu.2)
    have hfrontier : C.finalTerminal ∈ Gamma.terminalFrontier Z :=
      ⟨(C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).1,
        (C.z ⟨C.lastIndex, Nat.lt_succ_self _⟩).2, C.final_terminal⟩
    have hKinitial : K.trace.initial = u := by
      rw [K.initial_eq, hC0, hpinit]
    exact Or.inr ⟨C.finalTerminal, ⟨hfrontier, C.final_uncovered⟩,
      .finite K.trace, K.safe, hKinitial, by simp [K.terminal_eq],
      .finite K.trace.reverse,
      IsBracketAlternating.reverse_finite_of_boundary_forward hZ
        K.safe.2 K.first_forward K.last_forward,
      by simp [K.terminal_eq], by simp [hKinitial]⟩
  · let K := C.compilation hZ hY hZfinite hYfinite
        (by rw [hC0, hpinit]; exact hu.2)
    have hKinitial : K.trace.initial = u := by
      rw [K.initial_eq, hC0, hpinit]
    exact Or.inl ⟨.infinite K.trace, K.safe, hKinitial,
      by simp [AltPath.IsInfinite]⟩

/-! ## Simultaneous assignment at an arbitrary path-family boundary -/

/-- The form of Theorem 4.12 needed after cutting a linkage at an internal
set.  The distinguished source and target of the ambient web play no role:
only the two literal endpoint-alignment conditions between the cut family
and the reference warp are used. -/
def BoundarySimultaneousAssignmentStatement (Gamma : DWeb V) : Prop :=
  ∀ (Z Y : Set Gamma.DPath),
    BoundaryAligned Z Y →
    Gamma.IsWarp Z → Gamma.IsWarp Y →
    Gamma.HasFiniteCharacter Z → Gamma.HasFiniteCharacter Y →
    Gamma.initialSet Y ⊆ Gamma.initialSet Z →
    Nonempty (SimultaneousAssignment Z Y)

namespace BoundaryAligned

/-- Boundary alignment is inherited by the macro-orbit and the reference
subwarp generated by that orbit. -/
theorem macroOrbit_macroReference
    {Z Y : Set Gamma.DPath} (h : BoundaryAligned Z Y)
    (hY : Gamma.IsWarp Y) (p : Z) :
    BoundaryAligned (macroOrbit Z Y p) (macroReference Z Y p) := by
  constructor
  · rintro x ⟨⟨q, hqO, hqinit⟩, r, hrR, hxr⟩
    have hqZ : q ∈ Z := macroOrbit_subset Z Y p hqO
    have hrY : r ∈ Y := macroReference_subset Z Y p hrR
    have hxY : x ∈ Gamma.vertexSet Y := ⟨r, hrY, hxr⟩
    obtain ⟨s, hsY, hsinit⟩ := h.1 ⟨⟨q, hqZ, hqinit⟩, hxY⟩
    refine ⟨s, ⟨hsY, ?_⟩, hsinit⟩
    exact ⟨q, hqO, hqinit.trans hsinit.symm⟩
  · rintro x ⟨⟨q, hqO, hqterm⟩, r, hrR, hxr⟩
    have hqZ : q ∈ Z := macroOrbit_subset Z Y p hqO
    have hrY : r ∈ Y := macroReference_subset Z Y p hrR
    have hxY : x ∈ Gamma.vertexSet Y := ⟨r, hrY, hxr⟩
    have hxYterm : x ∈ Gamma.terminalFrontier Y :=
      h.2 ⟨⟨q, hqZ, hqterm⟩, hxY⟩
    obtain ⟨s, hsY, hsterm⟩ := hxYterm
    have hsr : s = r :=
      DWeb.IsWarp.eq_of_mem_support hY hsY hrY
        (Gamma.terminal_mem_support hsterm) hxr
    subst r
    exact ⟨s, hrR, hsterm⟩

/-- The terminal returned from one macro orbit is globally uncovered.  This
is the boundary-aligned analogue of the normalized ambient-target lemma in
`SimultaneousAssignmentGlobal`. -/
theorem terminalFrontier_macroOrbit_sdiff_reference_subset
    {Z Y : Set Gamma.DPath} (h : BoundaryAligned Z Y)
    (hinit : Gamma.initialSet Y ⊆ Gamma.initialSet Z)
    (p : Z) :
    Gamma.terminalFrontier (macroOrbit Z Y p) \
        Gamma.vertexSet (macroReference Z Y p) ⊆
      Gamma.terminalFrontier Z \ Gamma.vertexSet Y := by
  intro v hv
  refine ⟨?_, ?_⟩
  · rcases hv.1 with ⟨r, hrO, hrterm⟩
    exact ⟨r, macroOrbit_subset Z Y p hrO, hrterm⟩
  · intro hvY
    rcases hv.1 with ⟨r, hrO, hrterm⟩
    have hrZ : r ∈ Z := macroOrbit_subset Z Y p hrO
    have hvYfront : v ∈ Gamma.terminalFrontier Y :=
      h.2 ⟨⟨r, hrZ, hrterm⟩, hvY⟩
    rcases hvYfront with ⟨q, hqY, hqterm⟩
    have hqinitY : q.initial ∈ Gamma.initialSet Y := ⟨q, hqY, rfl⟩
    rcases hinit hqinitY with ⟨s, hsZ, hsinit⟩
    let rZ : Z := ⟨r, hrZ⟩
    let sZ : Z := ⟨s, hsZ⟩
    have hrs : AssignmentMacroStep Z Y rZ sZ := by
      refine ⟨⟨q, hqY⟩, v, hrterm, hqterm, ?_⟩
      exact hsinit.symm
    have hrO' : rZ.1 ∈ macroOrbit Z Y p := by
      simpa [rZ] using hrO
    have hsO : sZ.1 ∈ macroOrbit Z Y p :=
      mem_macroOrbit_of_step hrO' hrs
    have hqO : q ∈ macroReference Z Y p := by
      refine ⟨hqY, ?_⟩
      exact ⟨s, hsO, hsinit⟩
    exact hv.2 ⟨q, hqO, Gamma.terminal_mem_support hqterm⟩

end BoundaryAligned

/-- A simultaneous assignment together with the forward-family provenance
which is present in the boundary construction.  The ordinary source theorem
does not retain this field, but the fractured-warp projection in Remark 4.20
needs it in order to identify every projected forward run. -/
structure BracketSimultaneousAssignment (Z Y : Set Gamma.DPath)
    extends SimultaneousAssignment Z Y where
  bracket_safe : ∀ z, IsBracketSafe Z Y (assigned z)

/-- The boundary construction also remembers which rooted macro orbit owns
every vertex of each chosen alternating route.  This information is erased
by Theorem 4.12's public statement, but is essential when the route is split
at contacts with a later closing set. -/
structure MacroOwnedBracketSimultaneousAssignment
    (Z Y : Set Gamma.DPath) extends BracketSimultaneousAssignment Z Y where
  vertex_owner : ∀ z x, x ∈ (assigned z).vertexSet →
    ∃ q : Gamma.DPath,
      (q ∈ macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩) ∨
        q ∈ macroReference Z Y (initialPath Z ⟨z.1, z.property.1⟩)) ∧
      x ∈ q.support
  finite_terminal_orbit : ∀ z v, (assigned z).terminal? = some v →
    v ∈ Gamma.terminalFrontier
        (macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩)) \
      Gamma.vertexSet Y

private structure BoundaryOrbitAssignedData
    (Z Y : Set Gamma.DPath)
    (z : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) where
  path : AltPath Gamma.graph
  starts_at : path.initial = z.1
  safe : IsSafe Y path
  bracket_safe : IsBracketSafe Z Y path
  vertex_owner : ∀ x, x ∈ path.vertexSet →
    ∃ q : Gamma.DPath,
      (q ∈ macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩) ∨
        q ∈ macroReference Z Y (initialPath Z ⟨z.1, z.property.1⟩)) ∧
      x ∈ q.support
  leaving : IsLeaving Y path
  maximal : path.IsInfinite ∨
    ∃ v ∈ Gamma.terminalFrontier
        (macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩)) \
        Gamma.vertexSet Y,
      path.terminal? = some v

private theorem BoundaryOrbitAssignedData.finite_terminal_mem_orbit
    {Z Y : Set Gamma.DPath}
    {z : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y}}
    (A : BoundaryOrbitAssignedData Z Y z) {v : V}
    (hv : A.path.terminal? = some v) :
    v ∈ Gamma.terminalFrontier
        (macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩)) \
      Gamma.vertexSet Y := by
  rcases A.maximal with hinf | ⟨w, hw, hterm⟩
  · have hnone := A.path.isInfinite_iff_terminal?_eq_none.mp hinf
    rw [hnone] at hv
    simp at hv
  · have hvw : v = w := Option.some.inj (hv.symm.trans hterm)
    exact hvw ▸ hw

/-- The boundary construction with its rooted macro-orbit provenance
retained at every route vertex. -/
theorem boundaryMacroOwnedBracketSimultaneousAssignment
    (Gamma : DWeb V) (Z Y : Set Gamma.DPath)
    (hboundary : BoundaryAligned Z Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYZ : Gamma.initialSet Y ⊆ Gamma.initialSet Z) :
    Nonempty (MacroOwnedBracketSimultaneousAssignment Z Y) := by
  classical
  let U := {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y}
  have hrootOutside : ∀ z : U,
      (initialPath Z ⟨z.1, z.property.1⟩).1.initial ∉
        Gamma.vertexSet Y := by
    intro z
    rw [initialPath_initial]
    exact hboundary.initial_outside z.property
  have hlocal : ∀ z : U, Nonempty (BoundaryOrbitAssignedData Z Y z) := by
    intro z
    let p : Z := initialPath Z ⟨z.1, z.property.1⟩
    let Zz : Set Gamma.DPath := macroOrbit Z Y p
    let Yz : Set Gamma.DPath := macroReference Z Y p
    have hpinit : p.1.initial = z.1 := by
      simpa [p] using initialPath_initial Z ⟨z.1, z.property.1⟩
    have hpOutside : p.1.initial ∉ Gamma.vertexSet Y := by
      simpa [p] using hrootOutside z
    have hpZz : p.1 ∈ Zz := mem_macroOrbit_root Z Y p
    have hpInitialZz : p.1.initial ∈ Gamma.initialSet Zz :=
      ⟨p.1, hpZz, rfl⟩
    have hpNotYz : p.1.initial ∉ Gamma.vertexSet Yz := by
      intro hp
      apply hpOutside
      rcases hp with ⟨q, hqYz, hqp⟩
      exact ⟨q, macroReference_subset Z Y p hqYz, hqp⟩
    have hlocalBoundary : BoundaryAligned Zz Yz :=
      hboundary.macroOrbit_macroReference hY p
    have hd := safeAlternatingDichotomy_of_boundary hlocalBoundary.2
      (isWarp_macroOrbit hZ p) (isWarp_macroReference hY p)
      (hasFiniteCharacter_macroOrbit hZfinite p)
      (hasFiniteCharacter_macroReference hYfinite p)
      (initialSet_macroReference_subset p)
      ⟨hpInitialZz, hpNotYz⟩
    rcases hd with hinfinite | hfinite
    · rcases hinfinite with ⟨Q, hQ, hQi, hQinf⟩
      have hQsafe : IsSafe Y Q := by
        apply hQ.1.of_subwarp hY (macroReference_subset Z Y p)
        · intro _
          rw [hQi]
          exact hpOutside
        · intro t ht _
          have hnone := Q.isInfinite_iff_terminal?_eq_none.mp hQinf
          rw [hnone] at ht
          simp at ht
      have hQbracket : IsBracketSafe Z Y Q := by
        refine ⟨hQsafe, hQsafe.1, ?_⟩
        intro l hl hdir
        rcases hQ.2.2 l hl hdir with ⟨q, hq, hql⟩
        exact ⟨q, macroOrbit_subset Z Y p hq, hql⟩
      exact ⟨{
        path := Q
        starts_at := hQi.trans hpinit
        safe := hQsafe
        bracket_safe := hQbracket
        vertex_owner := by
          intro x hx
          rcases Q.vertexSet_subset_initial_union_links hx with hx | hx
          · have hxinitial : x = Q.initial := by simpa using hx
            subst x
            refine ⟨p.1, Or.inl (mem_macroOrbit_root Z Y p), ?_⟩
            rw [hQi]
            exact p.1.initial_mem_support
          · simp only [Set.mem_iUnion] at hx
            obtain ⟨l, hl, hxl⟩ := hx
            cases hdir : l.direction with
            | forward =>
                obtain ⟨q, hq, hsub⟩ := hQ.2.2 l hl hdir
                exact ⟨q, Or.inl hq, hsub.1 hxl⟩
            | backward =>
                obtain ⟨q, hq, hsub⟩ := hQ.2.1.2.1 l hl hdir
                exact ⟨q, Or.inr hq, hsub.1 hxl⟩
        leaving := Or.inl hQinf
        maximal := Or.inl hQinf }⟩
    · rcases hfinite with
        ⟨v, hv, Q, hQ, hQi, hQt, _T, _hT, _hTi, _hTt⟩
      have hvGlobal : v ∈ Gamma.terminalFrontier Z \
          Gamma.vertexSet Y :=
        hboundary.terminalFrontier_macroOrbit_sdiff_reference_subset hYZ p hv
      have hQsafe : IsSafe Y Q := by
        apply hQ.1.of_subwarp hY (macroReference_subset Z Y p)
        · intro _
          rw [hQi]
          exact hpOutside
        · intro t ht _
          have htv : t = v := Option.some.inj (ht.symm.trans hQt)
          exact htv ▸ hvGlobal.2
      have hQbracket : IsBracketSafe Z Y Q := by
        refine ⟨hQsafe, hQsafe.1, ?_⟩
        intro l hl hdir
        rcases hQ.2.2 l hl hdir with ⟨q, hq, hql⟩
        exact ⟨q, macroOrbit_subset Z Y p hq, hql⟩
      exact ⟨{
        path := Q
        starts_at := hQi.trans hpinit
        safe := hQsafe
        bracket_safe := hQbracket
        vertex_owner := by
          intro x hx
          rcases Q.vertexSet_subset_initial_union_links hx with hx | hx
          · have hxinitial : x = Q.initial := by simpa using hx
            subst x
            refine ⟨p.1, Or.inl (mem_macroOrbit_root Z Y p), ?_⟩
            rw [hQi]
            exact p.1.initial_mem_support
          · simp only [Set.mem_iUnion] at hx
            obtain ⟨l, hl, hxl⟩ := hx
            cases hdir : l.direction with
            | forward =>
                obtain ⟨q, hq, hsub⟩ := hQ.2.2 l hl hdir
                exact ⟨q, Or.inl hq, hsub.1 hxl⟩
            | backward =>
                obtain ⟨q, hq, hsub⟩ := hQ.2.1.2.1 l hl hdir
                exact ⟨q, Or.inr hq, hsub.1 hxl⟩
        leaving := Or.inr ⟨v, hQt, hvGlobal.2⟩
        maximal := Or.inr ⟨v, ⟨hv.1, hvGlobal.2⟩, hQt⟩ }⟩
  let data : ∀ z : U, BoundaryOrbitAssignedData Z Y z :=
    fun z ↦ Classical.choice (hlocal z)
  refine ⟨{
    assigned := fun z ↦ (data z).path
    starts_at := fun z ↦ (data z).starts_at
    safe := fun z ↦ (data z).safe
    leaving := fun z ↦ (data z).leaving
    maximal := ?_
    finite_terminals_injective := ?_
    bracket_safe := fun z ↦ (data z).bracket_safe
    vertex_owner := fun z ↦ (data z).vertex_owner
    finite_terminal_orbit := fun z v hv ↦
      (data z).finite_terminal_mem_orbit hv }⟩
  · intro z
    rcases (data z).maximal with hinf | ⟨v, hv, hterm⟩
    · exact Or.inl hinf
    · rcases hv.1 with ⟨q, hqO, hqterm⟩
      exact Or.inr ⟨v, ⟨
        ⟨q, macroOrbit_subset Z Y
          (initialPath Z ⟨z.1, z.property.1⟩) hqO, hqterm⟩,
        hv.2⟩, hterm⟩
  · intro z₁ z₂ v hv₁ hv₂
    have hvO₁ := (data z₁).finite_terminal_mem_orbit hv₁
    have hvO₂ := (data z₂).finite_terminal_mem_orbit hv₂
    rcases hvO₁.1 with ⟨p₁, hp₁O, hp₁term⟩
    rcases hvO₂.1 with ⟨p₂, hp₂O, hp₂term⟩
    have hp₁Z : p₁ ∈ Z := macroOrbit_subset Z Y
      (initialPath Z ⟨z₁.1, z₁.property.1⟩) hp₁O
    have hp₂Z : p₂ ∈ Z := macroOrbit_subset Z Y
      (initialPath Z ⟨z₂.1, z₂.property.1⟩) hp₂O
    have hpEq : p₁ = p₂ :=
      DWeb.IsWarp.eq_of_mem_support hZ hp₁Z hp₂Z
        (Gamma.terminal_mem_support hp₁term)
        (Gamma.terminal_mem_support hp₂term)
    subst p₂
    have hrootEq :
        initialPath Z ⟨z₁.1, z₁.property.1⟩ =
          initialPath Z ⟨z₂.1, z₂.property.1⟩ :=
      macroOrbit_roots_eq_of_common hZ hY
        (hrootOutside z₁) (hrootOutside z₂) hp₁O hp₂O
    apply Subtype.ext
    calc
      z₁.1 = (initialPath Z ⟨z₁.1, z₁.property.1⟩).1.initial :=
        (initialPath_initial Z ⟨z₁.1, z₁.property.1⟩).symm
      _ = (initialPath Z ⟨z₂.1, z₂.property.1⟩).1.initial :=
        congrArg (fun p : Z ↦ p.1.initial) hrootEq
      _ = z₂.1 := initialPath_initial Z ⟨z₂.1, z₂.property.1⟩

/-- Forgetting rooted ownership recovers the ordinary bracket assignment
used by the fractured projection compiler. -/
theorem boundaryBracketSimultaneousAssignment
    (Gamma : DWeb V) (Z Y : Set Gamma.DPath)
    (hboundary : BoundaryAligned Z Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYZ : Gamma.initialSet Y ⊆ Gamma.initialSet Z) :
    Nonempty (BracketSimultaneousAssignment Z Y) :=
  Nonempty.map
    MacroOwnedBracketSimultaneousAssignment.toBracketSimultaneousAssignment
    (boundaryMacroOwnedBracketSimultaneousAssignment Gamma Z Y hboundary
      hZ hY hZfinite hYfinite hYZ)

/-- The simultaneous-assignment theorem at an internal cut.  Its proof is
the same disjoint-macro-orbit assembly as the endpoint-pure theorem, with
`BoundaryAligned` replacing every ambient source/target appeal. -/
theorem boundarySimultaneousAssignmentStatement (Gamma : DWeb V) :
    BoundarySimultaneousAssignmentStatement Gamma := by
  intro Z Y hboundary hZ hY hZfinite hYfinite hYZ
  exact Nonempty.map BracketSimultaneousAssignment.toSimultaneousAssignment
    (boundaryBracketSimultaneousAssignment Gamma Z Y hboundary hZ hY
      hZfinite hYfinite hYZ)

end Alternating
end Erdos599
