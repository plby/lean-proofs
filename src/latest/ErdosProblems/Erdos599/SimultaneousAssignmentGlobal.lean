/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Global simultaneous safe assignments

This file proves the normalized form of Aharoni--Berger Theorem 4.12
without successively switching the first warp.  Successive switching is not
valid for the literal alternating paths of Definition 4.2: a forward link of
a reducing path can cross a member of the reference warp which it does not
otherwise use.

Instead, associate to a member `p` of `Z` the (unique, when it exists)
member `r` of `Z` obtained as follows.  If the terminal of `p` is covered by
`Y`, take the unique member `q` of `Y` ending there and the member `r` of `Z`
whose initial vertex is the initial vertex of `q`.  This is
`AssignmentMacroStep Z Y`.
It is both left- and right-unique.  An uncovered source is not in the range
of a macro step, so the forward macro orbits of two distinct uncovered
sources are disjoint.

For one uncovered source we restrict `Z` to its macro orbit, and restrict
`Y` to the paths whose initial vertices occur in that orbit.  The safe
alternating-path dichotomy applies to these two subwarps.  A finite outcome
ends at an uncovered terminal of the orbit; closure of the orbit under
`AssignmentMacroStep` shows that this terminal is in fact outside the whole
of `Y`.
Safety relative to the reference subwarp promotes to safety relative to all
of `Y`.  Finally, disjointness of the macro orbits makes the finite terminals
of all chosen outcomes injective.  The alternating paths themselves may,
as the theorem permits, overlap.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-! ## The endpoint macro step -/

/-- One endpoint-level step: `p : Z` and `q : Y` have the same terminal,
and `q` and the next path `r : Z` have the same initial vertex.  This local
copy keeps the global assignment proof independent of the edge-level trace
compiler. -/
def AssignmentMacroStep (Z Y : Set Γ.DPath) (p r : Z) : Prop :=
  ∃ q : Y, ∃ t : V,
    Γ.terminal? p.1 = some t ∧
      Γ.terminal? q.1 = some t ∧ q.1.initial = r.1.initial

namespace AssignmentMacroStep

/-- The macro step is left-unique. -/
theorem leftUnique
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y) :
    Relator.LeftUnique (AssignmentMacroStep Z Y) := by
  intro p p' r hpr hp'r
  rcases hpr with ⟨q, t, hpterm, hqterm, hqr⟩
  rcases hp'r with ⟨q', t', hp'term, hq'term, hq'r⟩
  have hqq' : q = q' := by
    apply Subtype.ext
    have hinit : q.1.initial = q'.1.initial := hqr.trans hq'r.symm
    exact DWeb.IsWarp.eq_of_mem_support hY q.2 q'.2
      q.1.initial_mem_support
      (hinit ▸ q'.1.initial_mem_support)
  subst q'
  have htt' : t = t' := Option.some.inj (hqterm.symm.trans hq'term)
  subst t'
  apply Subtype.ext
  exact DWeb.IsWarp.eq_of_mem_support hZ p.2 p'.2
    (Γ.terminal_mem_support hpterm)
    (Γ.terminal_mem_support hp'term)

/-- A `Z`-path whose initial vertex is outside `V[Y]` is not the target of
a macro step. -/
theorem not_mem_range_of_initial_not_mem
    {Z Y : Set Γ.DPath} (p : Z) (hp : p.1.initial ∉ Γ.vertexSet Y) :
    ¬ ∃ r : Z, AssignmentMacroStep Z Y r p := by
  rintro ⟨r, q, t, _hrterm, _hqterm, hqp⟩
  apply hp
  exact ⟨q.1, q.2, hqp ▸ q.1.initial_mem_support⟩

end AssignmentMacroStep

/-! ## A cancellation lemma for injective partial orbits -/

/-- In a left-unique relation, two forward orbits rooted at points with no
predecessor cannot merge unless their roots are equal. -/
theorem root_eq_of_reflTransGen_to_common
    {α : Type*} {R : α → α → Prop} {a b c : α}
    (hleft : Relator.LeftUnique R)
    (ha : Relation.ReflTransGen R a c)
    (hb : Relation.ReflTransGen R b c)
    (haroot : ¬ ∃ x, R x a)
    (hbroot : ¬ ∃ x, R x b) :
    a = b := by
  have ha' : Relation.ReflTransGen (Function.swap R) c a :=
    Relation.ReflTransGen.swap _ _ ha
  have hb' : Relation.ReflTransGen (Function.swap R) c b :=
    Relation.ReflTransGen.swap _ _ hb
  have hright : Relator.RightUnique (Function.swap R) := by
    intro x y z hxy hxz
    exact hleft hxy hxz
  rcases Relation.ReflTransGen.total_of_right_unique hright ha' hb' with h | h
  · have hab : Relation.ReflTransGen R b a :=
      Relation.reflTransGen_swap.mp h
    rcases Relation.ReflTransGen.cases_tail hab with hba | ⟨x, _hbx, hxa⟩
    · exact hba
    · exact False.elim (haroot ⟨x, hxa⟩)
  · have hab : Relation.ReflTransGen R a b :=
      Relation.reflTransGen_swap.mp h
    rcases Relation.ReflTransGen.cases_tail hab with hab | ⟨x, _hax, hxb⟩
    · exact hab.symm
    · exact False.elim (hbroot ⟨x, hxb⟩)

/-! ## Macro orbits and their reference subwarps -/

/-- The member of `Z` beginning at an element of `initialSet Z`. -/
noncomputable def initialPath (Z : Set Γ.DPath)
    (z : {z : V // z ∈ Γ.initialSet Z}) : Z :=
  ⟨Classical.choose z.property, (Classical.choose_spec z.property).1⟩

@[simp]
theorem initialPath_initial (Z : Set Γ.DPath)
    (z : {z : V // z ∈ Γ.initialSet Z}) :
    (initialPath Z z).1.initial = z.1 :=
  (Classical.choose_spec z.property).2

/-- The forward `AssignmentMacroStep` orbit of a member of `Z`, represented again as
a family of concrete paths. -/
def macroOrbit (Z Y : Set Γ.DPath) (p : Z) : Set Γ.DPath :=
  {q | ∃ hq : q ∈ Z,
    Relation.ReflTransGen (AssignmentMacroStep Z Y) p ⟨q, hq⟩}

@[simp]
theorem mem_macroOrbit_iff {Z Y : Set Γ.DPath} {p : Z} {q : Γ.DPath} :
    q ∈ macroOrbit Z Y p ↔
      ∃ hq : q ∈ Z,
        Relation.ReflTransGen (AssignmentMacroStep Z Y) p ⟨q, hq⟩ :=
  Iff.rfl

theorem macroOrbit_subset (Z Y : Set Γ.DPath) (p : Z) :
    macroOrbit Z Y p ⊆ Z := by
  rintro q ⟨hq, _⟩
  exact hq

theorem mem_macroOrbit_root (Z Y : Set Γ.DPath) (p : Z) :
    p.1 ∈ macroOrbit Z Y p :=
  ⟨p.2, Relation.ReflTransGen.refl⟩

theorem mem_macroOrbit_of_step {Z Y : Set Γ.DPath} {p r s : Z}
    (hr : r.1 ∈ macroOrbit Z Y p) (hrs : AssignmentMacroStep Z Y r s) :
    s.1 ∈ macroOrbit Z Y p := by
  rcases hr with ⟨hrZ, hpr⟩
  have hr_eq : (⟨r.1, hrZ⟩ : Z) = r := Subtype.ext rfl
  have hpr' : Relation.ReflTransGen (AssignmentMacroStep Z Y) p r := by
    simpa only [hr_eq] using hpr
  exact ⟨s.2, hpr'.tail hrs⟩

theorem isWarp_macroOrbit {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (p : Z) :
    Γ.IsWarp (macroOrbit Z Y p) := by
  intro q hq r hr hqr
  exact DWeb.IsWarp.disjoint Γ hZ
    (macroOrbit_subset Z Y p hq) (macroOrbit_subset Z Y p hr) hqr

theorem hasFiniteCharacter_macroOrbit {Z Y : Set Γ.DPath}
    (hZ : Γ.HasFiniteCharacter Z) (p : Z) :
    Γ.HasFiniteCharacter (macroOrbit Z Y p) := by
  intro q hq
  exact hZ (macroOrbit_subset Z Y p hq)

/-- The part of `Y` whose initial vertices occur in a macro orbit. -/
def macroReference (Z Y : Set Γ.DPath) (p : Z) : Set Γ.DPath :=
  {q | q ∈ Y ∧ q.initial ∈ Γ.initialSet (macroOrbit Z Y p)}

@[simp]
theorem mem_macroReference_iff {Z Y : Set Γ.DPath} {p : Z} {q : Γ.DPath} :
    q ∈ macroReference Z Y p ↔
      q ∈ Y ∧ q.initial ∈ Γ.initialSet (macroOrbit Z Y p) :=
  Iff.rfl

theorem macroReference_subset (Z Y : Set Γ.DPath) (p : Z) :
    macroReference Z Y p ⊆ Y := by
  intro q hq
  exact hq.1

theorem isWarp_macroReference {Z Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) (p : Z) :
    Γ.IsWarp (macroReference Z Y p) := by
  intro q hq r hr hqr
  exact DWeb.IsWarp.disjoint Γ hY hq.1 hr.1 hqr

theorem hasFiniteCharacter_macroReference {Z Y : Set Γ.DPath}
    (hY : Γ.HasFiniteCharacter Y) (p : Z) :
    Γ.HasFiniteCharacter (macroReference Z Y p) := by
  intro q hq
  exact hY hq.1

theorem initialSet_macroReference_subset {Z Y : Set Γ.DPath} (p : Z) :
    Γ.initialSet (macroReference Z Y p) ⊆
      Γ.initialSet (macroOrbit Z Y p) := by
  rintro x ⟨q, hq, rfl⟩
  exact hq.2

/-- A terminal of a macro orbit which is outside its reference subwarp is
outside the whole reference warp.  If it lay on `Y`, normalization would
make it the terminal of a `Y`-path; the corresponding macro step would put
that path's initial vertex into the orbit, hence put the `Y`-path into the
reference subwarp. -/
theorem terminalFrontier_macroOrbit_sdiff_vertexSet_macroReference_subset
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target)
    (hinit : Γ.initialSet Y ⊆ Γ.initialSet Z)
    (p : Z) :
    Γ.terminalFrontier (macroOrbit Z Y p) \
        Γ.vertexSet (macroReference Z Y p) ⊆
      Γ.terminalFrontier Z \ Γ.vertexSet Y := by
  intro v hv
  refine ⟨?_, ?_⟩
  · rcases hv.1 with ⟨r, hrO, hrterm⟩
    exact ⟨r, macroOrbit_subset Z Y p hrO, hrterm⟩
  · intro hvY
    rcases hv.1 with ⟨r, hrO, hrterm⟩
    have hrZ : r ∈ Z := macroOrbit_subset Z Y p hrO
    have hvZ : v ∈ Γ.terminalFrontier Z := ⟨r, hrZ, hrterm⟩
    have hvYfront : v ∈ Γ.terminalFrontier Y :=
      DWeb.terminalFrontier_inter_vertexSet_subset hΓ hZB ⟨hvZ, hvY⟩
    rcases hvYfront with ⟨q, hqY, hqterm⟩
    have hqinitY : q.initial ∈ Γ.initialSet Y := ⟨q, hqY, rfl⟩
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
    exact hv.2 ⟨q, hqO, Γ.terminal_mem_support hqterm⟩

/-! ## Promoting safety from a reference subwarp -/

theorem familyEdges_mono {W W' : Set Γ.DPath} (h : W ⊆ W') :
    familyEdges W ⊆ familyEdges W' := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  rcases he with ⟨p, hpW, hep⟩
  exact ⟨p, h hpW, hep⟩

/-- Literal safeness is monotone from a subwarp to the whole reference warp
once the two exposed endpoints are known to lie outside the whole warp.
Backward edges on a member omitted from the subwarp are empty because the
whole reference family is a warp. -/
theorem IsSafe.of_subwarp
    {Y₀ Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hY : Γ.IsWarp Y) (hsub : Y₀ ⊆ Y)
    (hQ : IsSafe Y₀ Q)
    (hinitial : Q.firstDirection? = some .forward →
      Q.initial ∉ Γ.vertexSet Y)
    (hterminal : ∀ t, Q.terminal? = some t →
      Q.lastDirection? = some .forward → t ∉ Γ.vertexSet Y) :
    IsSafe Y Q := by
  rcases hQ with
    ⟨⟨_hY₀, hback, _hinit₀, _hterm₀⟩, hinterval, hnray, hncycle⟩
  refine ⟨⟨hY, ?_, hinitial, hterminal⟩, ?_, ?_, ?_⟩
  · intro l hl hdir
    rcases hback l hl hdir with ⟨p, hpY₀, hlp⟩
    exact ⟨p, hsub hpY₀, hlp⟩
  · intro p hpY
    by_cases hpY₀ : p ∈ Y₀
    · exact hinterval p hpY₀
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      rcases he with ⟨heback, hep⟩
      simp only [AltPath.directionEdges, Set.mem_iUnion] at heback
      rcases heback with ⟨l, hl, hdir, hel⟩
      rcases hback l hl hdir with ⟨q, hqY₀, hlq⟩
      have hqY : q ∈ Y := hsub hqY₀
      have hqp : q ≠ p := by
        intro h
        subst q
        exact hpY₀ hqY₀
      have hdisj := DWeb.IsWarp.disjoint Γ hY hqY hpY hqp
      have helSupport := l.path.edgeSet_subset_support_prod hel
      have hepSupport := p.edgeSet_subset_support_prod hep
      exact Set.disjoint_left.1 hdisj
        (hlq.1 helSupport.1) hepSupport.1
  · intro hray
    apply hnray
    rcases hray with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro e he
    have he' := hR he
    exact ⟨he'.1, fun heY₀ ↦ he'.2 (familyEdges_mono hsub heY₀)⟩
  · intro hcycle
    apply hncycle
    rcases hcycle with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro e he
    have he' := hC he
    exact ⟨he'.1, fun heY₀ ↦ he'.2 (familyEdges_mono hsub heY₀)⟩

/-! ## Disjointness of different rooted macro orbits -/

/-- If two root orbits share a path and both roots are outside `V[Y]`, the
roots are equal. -/
theorem macroOrbit_roots_eq_of_common
    {Z Y : Set Γ.DPath} (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    {p r : Z} (hpY : p.1.initial ∉ Γ.vertexSet Y)
    (hrY : r.1.initial ∉ Γ.vertexSet Y)
    {q : Γ.DPath} (hqp : q ∈ macroOrbit Z Y p)
    (hqr : q ∈ macroOrbit Z Y r) :
    p = r := by
  rcases hqp with ⟨hqZ, hpq⟩
  rcases hqr with ⟨hqZ', hrq⟩
  have hqq : (⟨q, hqZ⟩ : Z) = ⟨q, hqZ'⟩ := Subtype.ext rfl
  rw [← hqq] at hrq
  exact root_eq_of_reflTransGen_to_common
    (AssignmentMacroStep.leftUnique hZ hY) hpq hrq
    (AssignmentMacroStep.not_mem_range_of_initial_not_mem p hpY)
    (AssignmentMacroStep.not_mem_range_of_initial_not_mem r hrY)

/-! ## One orbit's assignment data -/

private structure OrbitAssignedData
    (Z Y : Set Γ.DPath)
    (z : {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y}) where
  path : AltPath Γ.graph
  starts_at : path.initial = z.1
  safe : IsSafe Y path
  leaving : IsLeaving Y path
  maximal : path.IsInfinite ∨
    ∃ v ∈ Γ.terminalFrontier
        (macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩)) \
        Γ.vertexSet Y,
      path.terminal? = some v

private theorem OrbitAssignedData.finite_terminal_mem_orbit
    {Z Y : Set Γ.DPath}
    {z : {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y}}
    (A : OrbitAssignedData Z Y z) {v : V}
    (hv : A.path.terminal? = some v) :
    v ∈ Γ.terminalFrontier
        (macroOrbit Z Y (initialPath Z ⟨z.1, z.property.1⟩)) \
      Γ.vertexSet Y := by
  rcases A.maximal with hinf | ⟨w, hw, hterm⟩
  · have hnone := A.path.isInfinite_iff_terminal?_eq_none.mp hinf
    rw [hnone] at hv
    simp at hv
  · have hvw : v = w := Option.some.inj (hv.symm.trans hterm)
    exact hvw ▸ hw

/-! ## The global simultaneous assignment theorem -/

/-- The normalized simultaneous-assignment theorem, constructed globally
from the safe alternating-path dichotomy and without a reducing-switch
rule. -/
theorem simultaneousAssignment_of_safeAlternatingDichotomy_global
    (hDichotomy : SafeAlternatingDichotomyStatement Γ) :
    SimultaneousAssignmentStatement Γ := by
  intro hΓ Z Y hZsource hZtarget hZ hY hZfinite hYfinite hYZ
  classical
  let U := {z : V // z ∈ Γ.initialSet Z \ Γ.initialSet Y}
  have hrootOutside : ∀ z : U,
      (initialPath Z ⟨z.1, z.property.1⟩).1.initial ∉ Γ.vertexSet Y := by
    intro z
    rw [initialPath_initial]
    exact (DWeb.initialSet_sdiff_subset_initialSet_sdiff_vertexSet
      hΓ hZsource z.property).2
  have hlocal : ∀ z : U, Nonempty (OrbitAssignedData Z Y z) := by
    intro z
    let p : Z := initialPath Z ⟨z.1, z.property.1⟩
    let Zz : Set Γ.DPath := macroOrbit Z Y p
    let Yz : Set Γ.DPath := macroReference Z Y p
    have hpinit : p.1.initial = z.1 := by
      simpa [p] using initialPath_initial Z ⟨z.1, z.property.1⟩
    have hpOutside : p.1.initial ∉ Γ.vertexSet Y := by
      simpa [p] using hrootOutside z
    have hZzsource : Γ.initialSet Zz ⊆ Γ.source := by
      rintro x ⟨q, hq, rfl⟩
      exact hZsource ⟨q, macroOrbit_subset Z Y p hq, rfl⟩
    have hZztarget : Γ.terminalFrontier Zz ⊆ Γ.target := by
      rintro x ⟨q, hq, hterm⟩
      exact hZtarget ⟨q, macroOrbit_subset Z Y p hq, hterm⟩
    have hpZz : p.1 ∈ Zz := mem_macroOrbit_root Z Y p
    have hpInitialZz : p.1.initial ∈ Γ.initialSet Zz := ⟨p.1, hpZz, rfl⟩
    have hpNotYz : p.1.initial ∉ Γ.vertexSet Yz := by
      intro hp
      apply hpOutside
      rcases hp with ⟨q, hqYz, hqp⟩
      exact ⟨q, macroReference_subset Z Y p hqYz, hqp⟩
    have hd := hDichotomy hΓ Zz Yz hZzsource hZztarget
      (isWarp_macroOrbit hZ p) (isWarp_macroReference hY p)
      (hasFiniteCharacter_macroOrbit hZfinite p)
      (hasFiniteCharacter_macroReference hYfinite p)
      (initialSet_macroReference_subset p)
      p.1.initial ⟨hpInitialZz, hpNotYz⟩
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
      exact ⟨{
        path := Q
        starts_at := hQi.trans hpinit
        safe := hQsafe
        leaving := Or.inl hQinf
        maximal := Or.inl hQinf
      }⟩
    · rcases hfinite with ⟨v, hv, Q, hQ, hQi, hQt, _T, _hT, _hTi, _hTt⟩
      have hvGlobal : v ∈ Γ.terminalFrontier Z \ Γ.vertexSet Y :=
        terminalFrontier_macroOrbit_sdiff_vertexSet_macroReference_subset
          hΓ hZtarget hYZ p hv
      have hQsafe : IsSafe Y Q := by
        apply hQ.1.of_subwarp hY (macroReference_subset Z Y p)
        · intro _
          rw [hQi]
          exact hpOutside
        · intro t ht _
          have htv : t = v := Option.some.inj (ht.symm.trans hQt)
          exact htv ▸ hvGlobal.2
      exact ⟨{
        path := Q
        starts_at := hQi.trans hpinit
        safe := hQsafe
        leaving := Or.inr ⟨v, hQt, hvGlobal.2⟩
        maximal := Or.inr ⟨v, ⟨hv.1, hvGlobal.2⟩, hQt⟩
      }⟩
  let data : ∀ z : U, OrbitAssignedData Z Y z :=
    fun z ↦ Classical.choice (hlocal z)
  refine ⟨{
    assigned := fun z ↦ (data z).path
    starts_at := fun z ↦ (data z).starts_at
    safe := fun z ↦ (data z).safe
    leaving := fun z ↦ (data z).leaving
    maximal := ?_
    finite_terminals_injective := ?_
  }⟩
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
        (Γ.terminal_mem_support hp₁term)
        (Γ.terminal_mem_support hp₂term)
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

end Alternating
end Erdos599
