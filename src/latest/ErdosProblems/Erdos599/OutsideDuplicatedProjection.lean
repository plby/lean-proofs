/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentCompiler

/-!
# A truthful occurrence assignment for the one-linkage outside cut

The generic occurrence compiler keeps its paths in the duplicated web.  In
the concrete application to Assertion 9.31, the existing outside-cut
projection theorem already supplies safe paths in the original web whose
endpoints are classified by Claim 2.  This file embeds those paths in the
plain copies of the duplicated web.  Consequently the split endpoint map is
definitionally aligned with the safe projected paths; no connector edge is
contracted and no classification is inferred from endpoint data alone.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Alternating

open DirectedPath

namespace FracturedDuplication

universe u

variable {V W : Type u} {D : Digraph V} {E : Digraph W}

/-! ## Functoriality of alternating paths under an injective graph map -/

/-- Map one directed link under an injective edge-preserving vertex map. -/
def mapAltLink (f : V → W) (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) : Link E where
  path := mapFinitePath f hf hedge l.path
  direction := l.direction
  nontrivial := fun h ↦ l.nontrivial (hf h)

@[simp] theorem direction_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) :
    (mapAltLink f hf hedge l).direction = l.direction := rfl

@[simp] theorem entry_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) :
    (mapAltLink f hf hedge l).entry = f l.entry := by
  cases h : l.direction <;>
    simp [mapAltLink, Link.entry, h]

@[simp] theorem exit_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) :
    (mapAltLink f hf hedge l).exit = f l.exit := by
  cases h : l.direction <;>
    simp [mapAltLink, Link.exit, h]

theorem support_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) :
    (mapAltLink f hf hedge l).path.support = f '' l.path.support := by
  ext z
  constructor
  · intro hz
    rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hz with
      ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_support_mapFinitePath f hf hedge l.path (f x)).2
      ⟨x, hx, rfl⟩

theorem interior_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (l : Link D) :
    (mapAltLink f hf hedge l).interior = f '' l.interior := by
  ext z
  constructor
  · rintro ⟨hzsupport, hzendpoints⟩
    rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hzsupport with
      ⟨x, hx, rfl⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    simp only [Link.endpoints, Set.mem_insert_iff, Set.mem_singleton_iff,
      start_mapFinitePath, finish_mapFinitePath] at hzendpoints ⊢
    intro hxendpoints
    exact hzendpoints (hxendpoints.imp (congrArg f) (congrArg f))
  · rintro ⟨x, ⟨hxsupport, hxendpoints⟩, rfl⟩
    refine ⟨(mem_support_mapFinitePath f hf hedge l.path (f x)).2
      ⟨x, hxsupport, rfl⟩, ?_⟩
    simp only [Link.endpoints, Set.mem_insert_iff, Set.mem_singleton_iff,
      start_mapFinitePath, finish_mapFinitePath] at hxendpoints ⊢
    intro hfxendpoints
    apply hxendpoints
    rcases hfxendpoints with h | h
    · exact Or.inl (hf h)
    · exact Or.inr (hf h)

theorem compatibleInOrder_mapAltLink (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (adjacent : Prop) (l r : Link D)
    (h : CompatibleInOrder adjacent l r) :
    CompatibleInOrder adjacent (mapAltLink f hf hedge l)
      (mapAltLink f hf hedge r) := by
  cases hl : l.direction <;> cases hr : r.direction
  · simp only [CompatibleInOrder, direction_mapAltLink, entry_mapAltLink,
      exit_mapAltLink, hl, hr] at h ⊢
    intro z hzl hzr
    rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hzl with
      ⟨x, hx, hfx⟩
    rcases (mem_support_mapFinitePath f hf hedge r.path z).1 hzr with
      ⟨y, hy, hfy⟩
    have hxy : x = y := hf (hfx.trans hfy.symm)
    subst y
    rcases h hx hy with hcase | hcase
    · exact Or.inl ⟨hfx ▸ congrArg f hcase.1,
        hfx ▸ congrArg f hcase.2⟩
    · exact Or.inr ⟨hfx ▸ congrArg f hcase.1,
        hfx ▸ congrArg f hcase.2⟩
  · simp only [CompatibleInOrder, direction_mapAltLink, entry_mapAltLink,
      exit_mapAltLink, hl, hr] at h ⊢
    constructor
    · intro hadjacent
      rw [support_mapAltLink, support_mapAltLink,
        ← Set.image_inter hf, h.1 hadjacent, Set.image_singleton]
    · intro hnotadjacent
      rw [Set.disjoint_left]
      intro z hzl hzr
      rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hzl with
        ⟨x, hx, hfx⟩
      rcases (mem_support_mapFinitePath f hf hedge r.path z).1 hzr with
        ⟨y, hy, hfy⟩
      have hxy : x = y := hf (hfx.trans hfy.symm)
      subst y
      exact Set.disjoint_left.1 (h.2 hnotadjacent) hx hy
  · simp only [CompatibleInOrder, direction_mapAltLink, entry_mapAltLink,
      exit_mapAltLink, hl, hr] at h ⊢
    constructor
    · intro hadjacent z hzl hzr
      rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hzl with
        ⟨x, hx, hfx⟩
      rcases (mem_support_mapFinitePath f hf hedge r.path z).1 hzr with
        ⟨y, hy, hfy⟩
      have hxy : x = y := hf (hfx.trans hfy.symm)
      subst y
      rcases h.1 hadjacent hx hy with hcase | hcase
      · exact Or.inl (hfx ▸ congrArg f hcase)
      · right
        constructor
        · rw [interior_mapAltLink]
          exact ⟨x, hcase.1, hfx⟩
        · rw [interior_mapAltLink]
          exact ⟨x, hcase.2, hfx⟩
    · intro hnotadjacent z hz
      rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hz.1 with
        ⟨x, hx, hfx⟩
      rcases (mem_support_mapFinitePath f hf hedge r.path z).1 hz.2 with
        ⟨y, hy, hfy⟩
      have hxy : x = y := hf (hfx.trans hfy.symm)
      subst y
      have hinterior := h.2 hnotadjacent ⟨hx, hy⟩
      constructor
      · rw [interior_mapAltLink]
        exact ⟨x, hinterior.1, hfx⟩
      · rw [interior_mapAltLink]
        exact ⟨x, hinterior.2, hfx⟩
  · simp only [CompatibleInOrder, direction_mapAltLink, entry_mapAltLink,
      exit_mapAltLink, hl, hr] at h ⊢
    intro z hzl hzr
    rcases (mem_support_mapFinitePath f hf hedge l.path z).1 hzl with
      ⟨x, hx, hfx⟩
    rcases (mem_support_mapFinitePath f hf hedge r.path z).1 hzr with
      ⟨y, hy, hfy⟩
    have hxy : x = y := hf (hfx.trans hfy.symm)
    subst y
    rcases h hx hy with hcase | hcase
    · exact Or.inl ⟨hfx ▸ congrArg f hcase.1,
        hfx ▸ congrArg f hcase.2⟩
    · exact Or.inr ⟨hfx ▸ congrArg f hcase.1,
        hfx ▸ congrArg f hcase.2⟩

/-- Map a finite alternating trace under an injective graph map. -/
def mapAltFiniteTrace (f : V → W) (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (Q : FiniteTrace D) : FiniteTrace E where
  lastIndex := Q.lastIndex
  link i := mapAltLink f hf hedge (Q.link i)
  joins i := by simpa using congrArg f (Q.joins i)
  alternates i := Q.alternates i
  compatible i j hij :=
    compatibleInOrder_mapAltLink f hf hedge _ _ _ (Q.compatible i j hij)

/-- Map an infinite alternating trace under an injective graph map. -/
def mapAltInfiniteTrace (f : V → W) (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (Q : InfiniteTrace D) : InfiniteTrace E where
  link i := mapAltLink f hf hedge (Q.link i)
  joins i := by simpa using congrArg f (Q.joins i)
  alternates i := Q.alternates i
  compatible i j hij :=
    compatibleInOrder_mapAltLink f hf hedge _ _ _ (Q.compatible i j hij)

/-- Map an alternating path under an injective graph map. -/
def mapAltPath (f : V → W) (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y)) :
    AltPath D → AltPath E
  | .trivial x => .trivial (f x)
  | .finite Q => .finite (mapAltFiniteTrace f hf hedge Q)
  | .infinite Q => .infinite (mapAltInfiniteTrace f hf hedge Q)

@[simp] theorem initial_mapAltPath (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (Q : AltPath D) :
    (mapAltPath f hf hedge Q).initial = f Q.initial := by
  rcases Q with Q | Q | Q
  · rfl
  · change (mapAltLink f hf hedge Q.firstLink).entry = f Q.firstLink.entry
    exact entry_mapAltLink f hf hedge Q.firstLink
  · change (mapAltLink f hf hedge (Q.link 0)).entry = f (Q.link 0).entry
    exact entry_mapAltLink f hf hedge (Q.link 0)

@[simp] theorem terminal?_mapAltPath (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (Q : AltPath D) :
    (mapAltPath f hf hedge Q).terminal? = Q.terminal?.map f := by
  rcases Q with Q | Q | Q
  · rfl
  · change some (mapAltLink f hf hedge Q.lastLink).exit =
      some (f Q.lastLink.exit)
    rw [exit_mapAltLink]
  · rfl

@[simp] theorem isInfinite_mapAltPath (f : V → W)
    (hf : Function.Injective f)
    (hedge : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (Q : AltPath D) :
    (mapAltPath f hf hedge Q).IsInfinite ↔ Q.IsInfinite := by
  cases Q <;> simp [mapAltPath, AltPath.IsInfinite]

variable {Gamma : DWeb V}

theorem plain_injective : Function.Injective (plain : V → Vertex V) := by
  intro x y h
  simpa only [project_plain] using congrArg project h

theorem web_adj_plain (Z : FracturedWarp Gamma) {x y : V}
    (h : Gamma.graph.Adj x y) :
    (web Gamma Z).graph.Adj (plain x) (plain y) := by
  exact graph_adj_of_adj Z h

/-- Embed an original alternating path into the plain copies of the
duplicated occurrence web. -/
def plainAltPath (Z : FracturedWarp Gamma) :
    AltPath Gamma.graph → AltPath (web Gamma Z).graph :=
  mapAltPath plain plain_injective (web_adj_plain Z)

@[simp] theorem initial_plainAltPath (Z : FracturedWarp Gamma)
    (Q : AltPath Gamma.graph) :
    (plainAltPath Z Q).initial = plain Q.initial :=
  initial_mapAltPath plain plain_injective (web_adj_plain Z) Q

@[simp] theorem terminal?_plainAltPath (Z : FracturedWarp Gamma)
    (Q : AltPath Gamma.graph) :
    (plainAltPath Z Q).terminal? = Q.terminal?.map plain :=
  terminal?_mapAltPath plain plain_injective (web_adj_plain Z) Q

@[simp] theorem isInfinite_plainAltPath (Z : FracturedWarp Gamma)
    (Q : AltPath Gamma.graph) :
    (plainAltPath Z Q).IsInfinite ↔ Q.IsInfinite :=
  isInfinite_mapAltPath plain plain_injective (web_adj_plain Z) Q

/-- Regard an ordinary simultaneous assignment as an honest assignment in
the plain copies of the occurrence web.  This is used only after the
one-linkage outside projection theorem has constructed the ordinary paths;
it is not a contraction of an arbitrary split assignment. -/
noncomputable def DuplicatedFracturedAssignment.ofSimultaneousPlain
    {Z : FracturedWarp Gamma} {Y : Set Gamma.DPath}
    (A : SimultaneousAssignment Z.paths Y) :
    DuplicatedFracturedAssignment Z Y where
  splitPath s := plainAltPath Z (A.assigned s)
  projected_start := by
    intro s
    rw [initial_plainAltPath, project_plain, A.starts_at]
  projected_finite_terminal := by
    intro s z hterminal
    rw [terminal?_plainAltPath] at hterminal
    rcases hQ : (A.assigned s).terminal? with _ | v
    · simp [hQ] at hterminal
    · rw [hQ] at hterminal
      simp only [Option.map_some, Option.some.injEq] at hterminal
      subst z
      simpa only [project_plain] using A.finite_terminal_mem s hQ
  projected_finite_terminals_injective := by
    intro s₁ s₂ z₁ z₂ hterminal₁ hterminal₂ hproject
    rw [terminal?_plainAltPath] at hterminal₁ hterminal₂
    rcases hQ₁ : (A.assigned s₁).terminal? with _ | v₁
    · simp [hQ₁] at hterminal₁
    · rcases hQ₂ : (A.assigned s₂).terminal? with _ | v₂
      · simp [hQ₂] at hterminal₂
      · rw [hQ₁] at hterminal₁
        rw [hQ₂] at hterminal₂
        simp only [Option.map_some, Option.some.injEq] at hterminal₁
        simp only [Option.map_some, Option.some.injEq] at hterminal₂
        subst z₁
        subst z₂
        have hv : v₁ = v₂ := by
          simpa only [project_plain] using hproject
        subst v₂
        exact A.finite_terminals_injective hQ₁ hQ₂

@[simp] theorem endAt_ofSimultaneousPlain
    {Z : FracturedWarp Gamma} {Y : Set Gamma.DPath}
    (A : SimultaneousAssignment Z.paths Y)
    (hYfinite : Gamma.HasFiniteCharacter Y) (s : AssignmentSource Z Y) :
    (DuplicatedFracturedAssignment.ofSimultaneousPlain A).endAt
        hYfinite s =
      (A.assigned s).terminal? := by
  simp [DuplicatedFracturedAssignment.endAt,
    DuplicatedFracturedAssignment.assigned,
    DuplicatedFracturedAssignment.ofSimultaneousPlain,
    plainAltPath, Function.comp_def]

end FracturedDuplication
end Alternating
end Erdos599
