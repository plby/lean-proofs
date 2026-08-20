/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# Erdős Problem 518: finite path-cover utilities

This file contains the bookkeeping used when a minimal-counterexample argument deletes a set of
vertices, covers the induced graph on the remaining subtype, and then adds paths covering the
deleted set.  Coverage on a set is kept separate from path validity: every path in a local cover is
still an honest path of the ambient graph.
-/

open scoped SimpleGraph

namespace Erdos518

universe u v

variable {V : Type u} {W : Type v}

/-- A family of paths of `G` which covers every vertex in `S`.  The paths may also use vertices
outside `S`, as is useful for the overlapping covers in Problem 518. -/
def IsPathCoverOn (G : SimpleGraph V) (S : Set V) (ps : List (List V)) : Prop :=
  (∀ p ∈ ps, IsPath G p) ∧ ∀ v ∈ S, ∃ p ∈ ps, v ∈ p

/-- The set `S` can be covered by at most `k` paths of `G`. -/
def HasPathCoverOnAtMost (G : SimpleGraph V) (S : Set V) (k : ℕ) : Prop :=
  ∃ ps : List (List V), ps.length ≤ k ∧ IsPathCoverOn G S ps

lemma isPathCover_iff_isPathCoverOn_univ {G : SimpleGraph V} {ps : List (List V)} :
    IsPathCover G ps ↔ IsPathCoverOn G Set.univ ps := by
  simp [IsPathCover, IsPathCoverOn]

lemma hasPathCoverAtMost_iff_on_univ {G : SimpleGraph V} {k : ℕ} :
    HasPathCoverAtMost G k ↔ HasPathCoverOnAtMost G Set.univ k := by
  simp only [HasPathCoverAtMost, HasPathCoverOnAtMost, isPathCover_iff_isPathCoverOn_univ]

namespace IsPathCoverOn

lemma mono {G : SimpleGraph V} {S T : Set V} {ps : List (List V)}
    (h : IsPathCoverOn G S ps) (hTS : T ⊆ S) : IsPathCoverOn G T ps := by
  exact ⟨h.1, fun v hv ↦ h.2 v (hTS hv)⟩

lemma append {G : SimpleGraph V} {S T : Set V} {ps qs : List (List V)}
    (hps : IsPathCoverOn G S ps) (hqs : IsPathCoverOn G T qs) :
    IsPathCoverOn G (S ∪ T) (ps ++ qs) := by
  constructor
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hps.1 p hp
    · exact hqs.1 p hp
  · intro v hv
    rcases hv with hv | hv
    · obtain ⟨p, hp, hvp⟩ := hps.2 v hv
      exact ⟨p, List.mem_append_left _ hp, hvp⟩
    · obtain ⟨p, hp, hvp⟩ := hqs.2 v hv
      exact ⟨p, List.mem_append_right _ hp, hvp⟩

lemma cons {G : SimpleGraph V} {S : Set V} {p : List V} {ps : List (List V)}
    (hp : IsPath G p) (hps : IsPathCoverOn G S ps) :
    IsPathCoverOn G S (p :: ps) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have hq' : q = p ∨ q ∈ ps := by simpa only [List.mem_cons] using hq
    rcases hq' with rfl | hq'
    · exact hp
    · exact hps.1 q hq'
  · intro v hv
    obtain ⟨q, hq, hvq⟩ := hps.2 v hv
    exact ⟨q, List.mem_cons_of_mem _ hq, hvq⟩

lemma singleton_path {G : SimpleGraph V} {p : List V} (hp : IsPath G p) :
    IsPathCoverOn G {v | v ∈ p} [p] := by
  refine ⟨?_, ?_⟩
  · simpa using hp
  · intro v hv
    exact ⟨p, by simp, hv⟩

end IsPathCoverOn

namespace HasPathCoverOnAtMost

lemma mono_set {G : SimpleGraph V} {S T : Set V} {k : ℕ}
    (h : HasPathCoverOnAtMost G S k) (hTS : T ⊆ S) :
    HasPathCoverOnAtMost G T k := by
  obtain ⟨ps, hlen, hps⟩ := h
  exact ⟨ps, hlen, hps.mono hTS⟩

lemma mono {G : SimpleGraph V} {S : Set V} {k l : ℕ}
    (h : HasPathCoverOnAtMost G S k) (hkl : k ≤ l) :
    HasPathCoverOnAtMost G S l := by
  obtain ⟨ps, hlen, hps⟩ := h
  exact ⟨ps, hlen.trans hkl, hps⟩

lemma append {G : SimpleGraph V} {S T : Set V} {k l : ℕ}
    (hS : HasPathCoverOnAtMost G S k) (hT : HasPathCoverOnAtMost G T l) :
    HasPathCoverOnAtMost G (S ∪ T) (k + l) := by
  obtain ⟨ps, hpsLen, hps⟩ := hS
  obtain ⟨qs, hqsLen, hqs⟩ := hT
  refine ⟨ps ++ qs, ?_, hps.append hqs⟩
  simpa using Nat.add_le_add hpsLen hqsLen

end HasPathCoverOnAtMost

lemma HasPathCoverAtMost.mono {G : SimpleGraph V} {k l : ℕ}
    (h : HasPathCoverAtMost G k) (hkl : k ≤ l) : HasPathCoverAtMost G l := by
  obtain ⟨ps, hlen, hps⟩ := h
  exact ⟨ps, hlen.trans hkl, hps⟩

lemma IsPath.mono {G H : SimpleGraph V} (hGH : G ≤ H) {p : List V}
    (hp : IsPath G p) : IsPath H p := by
  exact ⟨hp.1, hp.2.1, hp.2.2.imp fun _ _ hadj ↦ hGH hadj⟩

lemma IsPathCoverOn.mono_graph {G H : SimpleGraph V} (hGH : G ≤ H)
    {S : Set V} {ps : List (List V)} (h : IsPathCoverOn G S ps) :
    IsPathCoverOn H S ps := by
  exact ⟨fun p hp ↦ (h.1 p hp).mono hGH, h.2⟩

lemma HasPathCoverAtMost.mono_graph {G H : SimpleGraph V} (hGH : G ≤ H) {k : ℕ}
    (h : HasPathCoverAtMost G k) : HasPathCoverAtMost H k := by
  obtain ⟨ps, hlen, hps⟩ := h
  exact ⟨ps, hlen, by
    rw [isPathCover_iff_isPathCoverOn_univ] at hps ⊢
    exact hps.mono_graph hGH⟩

lemma IsPathCover.append {G : SimpleGraph V} {ps qs : List (List V)}
    (hps : IsPathCover G ps) (hqs : IsPathCover G qs) : IsPathCover G (ps ++ qs) := by
  rw [isPathCover_iff_isPathCoverOn_univ] at hps hqs ⊢
  simpa using hps.append hqs

/-- The list of singleton paths associated to a list of vertices. -/
def singletonPathFamily (xs : List V) : List (List V) :=
  xs.map fun v ↦ [v]

@[simp] lemma singletonPathFamily_length (xs : List V) :
    (singletonPathFamily xs).length = xs.length := by
  simp [singletonPathFamily]

@[simp] lemma mem_singletonPathFamily {xs : List V} {v : V} :
    [v] ∈ singletonPathFamily xs ↔ v ∈ xs := by
  simp [singletonPathFamily]

lemma isPathCoverOn_singletonPathFamily (G : SimpleGraph V) (xs : List V) :
    IsPathCoverOn G {v | v ∈ xs} (singletonPathFamily xs) := by
  constructor
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact isPath_singleton G v
  · intro v hv
    exact ⟨[v], mem_singletonPathFamily.mpr hv, by simp⟩

/-- The singleton paths associated to a finite set, in its canonical `toList` order. -/
noncomputable def singletonPathFamilyFinset [DecidableEq V] (S : Finset V) : List (List V) :=
  singletonPathFamily S.toList

@[simp] lemma singletonPathFamilyFinset_length [DecidableEq V] (S : Finset V) :
    (singletonPathFamilyFinset S).length = S.card := by
  simp [singletonPathFamilyFinset]

@[simp] lemma mem_singletonPathFamilyFinset [DecidableEq V] {S : Finset V} {v : V} :
    [v] ∈ singletonPathFamilyFinset S ↔ v ∈ S := by
  simp [singletonPathFamilyFinset]

lemma isPathCoverOn_singletonPathFamilyFinset [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    IsPathCoverOn G (S : Set V) (singletonPathFamilyFinset S) := by
  simpa [singletonPathFamilyFinset] using isPathCoverOn_singletonPathFamily G S.toList

lemma hasPathCoverOnAtMost_finset (G : SimpleGraph V) (S : Finset V) :
    HasPathCoverOnAtMost G (S : Set V) S.card := by
  classical
  exact ⟨singletonPathFamilyFinset S, by simp, isPathCoverOn_singletonPathFamilyFinset G S⟩

lemma hasPathCoverAtMost_card (G : SimpleGraph V) [Fintype V] :
    HasPathCoverAtMost G (Fintype.card V) := by
  classical
  rw [hasPathCoverAtMost_iff_on_univ]
  simpa using hasPathCoverOnAtMost_finset G (Finset.univ : Finset V)

/-- The finite support of a list-represented path. -/
def pathSupport [DecidableEq V] (p : List V) : Finset V :=
  p.toFinset

/-- The union of the supports of all paths in a family. -/
def pathFamilySupport [DecidableEq V] (ps : List (List V)) : Finset V :=
  ps.flatten.toFinset

@[simp] lemma mem_pathSupport [DecidableEq V] {p : List V} {v : V} :
    v ∈ pathSupport p ↔ v ∈ p := by
  simp [pathSupport]

@[simp] lemma mem_pathFamilySupport [DecidableEq V] {ps : List (List V)} {v : V} :
    v ∈ pathFamilySupport ps ↔ ∃ p ∈ ps, v ∈ p := by
  simp [pathFamilySupport, List.mem_flatten]

@[simp] lemma pathSupport_card [DecidableEq V] {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) : (pathSupport p).card = p.length := by
  exact List.toFinset_card_of_nodup hp.2.1

lemma pathSupport_nonempty [DecidableEq V] {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) : (pathSupport p).Nonempty := by
  cases p with
  | nil => exact (hp.1 rfl).elim
  | cons v p => exact ⟨v, by simp [pathSupport]⟩

lemma pathFamilySupport_card_le [DecidableEq V] (ps : List (List V)) :
    (pathFamilySupport ps).card ≤ (ps.map List.length).sum := by
  simpa [pathFamilySupport, List.length_flatten] using ps.flatten.toFinset_card_le

@[simp] lemma pathFamilySupport_append [DecidableEq V] (ps qs : List (List V)) :
    pathFamilySupport (ps ++ qs) = pathFamilySupport ps ∪ pathFamilySupport qs := by
  ext v
  simp only [mem_pathFamilySupport, Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨p, hp, hvp⟩
    rcases hp with hp | hp
    · exact Or.inl ⟨p, hp, hvp⟩
    · exact Or.inr ⟨p, hp, hvp⟩
  · rintro (⟨p, hp, hvp⟩ | ⟨p, hp, hvp⟩)
    · exact ⟨p, Or.inl hp, hvp⟩
    · exact ⟨p, Or.inr hp, hvp⟩

@[simp] lemma pathFamilySupport_cons [DecidableEq V] (p : List V) (ps : List (List V)) :
    pathFamilySupport (p :: ps) = pathSupport p ∪ pathFamilySupport ps := by
  ext v
  simp

@[simp] lemma pathFamilySupport_singletonPathFamily [DecidableEq V] (xs : List V) :
    pathFamilySupport (singletonPathFamily xs) = xs.toFinset := by
  ext v
  simp only [mem_pathFamilySupport, List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, hvp⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_singleton] at hvp
    subst v
    exact hx
  · intro hv
    exact ⟨[v], mem_singletonPathFamily.mpr hv, by simp⟩

@[simp] lemma pathFamilySupport_singletonPathFamilyFinset [DecidableEq V] (S : Finset V) :
    pathFamilySupport (singletonPathFamilyFinset S) = S := by
  rw [singletonPathFamilyFinset, pathFamilySupport_singletonPathFamily]
  simp

lemma IsPathCoverOn.subset_pathFamilySupport [DecidableEq V]
    {G : SimpleGraph V} {S : Set V} {ps : List (List V)}
    (h : IsPathCoverOn G S ps) : S ⊆ (pathFamilySupport ps : Set V) := by
  intro v hv
  exact mem_pathFamilySupport.mpr (h.2 v hv)

lemma isPathCoverOn_iff_subset_support [DecidableEq V]
    {G : SimpleGraph V} {S : Set V} {ps : List (List V)} :
    IsPathCoverOn G S ps ↔
      (∀ p ∈ ps, IsPath G p) ∧ S ⊆ (pathFamilySupport ps : Set V) := by
  constructor
  · intro h
    exact ⟨h.1, h.subset_pathFamilySupport⟩
  · rintro ⟨hpaths, hsub⟩
    exact ⟨hpaths, fun v hv ↦ mem_pathFamilySupport.mp (hsub hv)⟩

lemma IsPathCover.pathFamilySupport_eq_univ [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {ps : List (List V)} (h : IsPathCover G ps) :
    pathFamilySupport ps = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  exact mem_pathFamilySupport.mpr (h.2 v)

/-! ### Mapping and lifting covers -/

lemma isPath_map_of_adj {G : SimpleGraph V} {H : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hadj : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (f y))
    {p : List V} (hp : IsPath G p) : IsPath H (p.map f) := by
  refine ⟨by simpa using hp.1, hp.2.1.map hf, ?_⟩
  rw [List.isChain_map]
  exact hp.2.2.imp fun _ _ h ↦ hadj h

lemma IsPathCoverOn.map_of_adj {G : SimpleGraph V} {H : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hadj : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (f y))
    {S : Set V} {ps : List (List V)} (h : IsPathCoverOn G S ps) :
    IsPathCoverOn H (f '' S) (ps.map (List.map f)) := by
  constructor
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact isPath_map_of_adj hf hadj (h.1 p hp)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨p, hp, hxp⟩ := h.2 x hx
    refine ⟨p.map f, List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨x, hxp, rfl⟩

lemma IsPathCoverOn.map_comap {G : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) {S : Set V} {ps : List (List V)}
    (h : IsPathCoverOn (G.comap f) S ps) :
    IsPathCoverOn G (f '' S) (ps.map (List.map f)) := by
  exact h.map_of_adj hf fun _ _ hadj ↦ hadj

lemma HasPathCoverOnAtMost.map_comap {G : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) {S : Set V} {psBound : ℕ}
    (h : HasPathCoverOnAtMost (G.comap f) S psBound) :
    HasPathCoverOnAtMost G (f '' S) psBound := by
  obtain ⟨ps, hlen, hps⟩ := h
  refine ⟨ps.map (List.map f), ?_, hps.map_comap hf⟩
  simpa using hlen

lemma HasPathCoverOnAtMost.map_of_adj {G : SimpleGraph V} {H : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hadj : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (f y))
    {S : Set V} {k : ℕ} (h : HasPathCoverOnAtMost G S k) :
    HasPathCoverOnAtMost H (f '' S) k := by
  obtain ⟨ps, hlen, hps⟩ := h
  refine ⟨ps.map (List.map f), ?_, hps.map_of_adj hf hadj⟩
  simpa using hlen

/-- Lift a cover of the induced graph on a subtype back to the ambient graph. -/
lemma lift_subtype_pathCoverOn (G : SimpleGraph V) (S : Set V)
    {ps : List (List S)}
    (h : IsPathCover (G.comap ((↑) : S → V)) ps) :
    IsPathCoverOn G S (ps.map (List.map ((↑) : S → V))) := by
  have hu : IsPathCoverOn (G.comap ((↑) : S → V)) Set.univ ps :=
    isPathCover_iff_isPathCoverOn_univ.mp h
  have hm := hu.map_comap Subtype.val_injective
  simpa only [Set.image_univ, Subtype.range_val] using hm

lemma HasPathCoverAtMost.lift_subtype (G : SimpleGraph V) (S : Set V) {k : ℕ}
    (h : HasPathCoverAtMost (G.comap ((↑) : S → V)) k) :
    HasPathCoverOnAtMost G S k := by
  obtain ⟨ps, hlen, hps⟩ := h
  refine ⟨ps.map (List.map ((↑) : S → V)), ?_, lift_subtype_pathCoverOn G S hps⟩
  simpa using hlen

/-- Finset-flavoured subtype lifting, for induced graphs on an explicitly finite vertex set. -/
lemma HasPathCoverAtMost.lift_finset (G : SimpleGraph V)
    (S : Finset V) {k : ℕ}
    (h : HasPathCoverAtMost (G.comap ((↑) : S → V)) k) :
    HasPathCoverOnAtMost G (S : Set V) k := by
  exact h.lift_subtype G (S : Set V)

/-- Combine same-colour covers of a set and its complement into an ambient cover. -/
lemma hasPathCoverAtMost_of_coverOn_compl {G : SimpleGraph V} {S : Set V} {k l : ℕ}
    (hS : HasPathCoverOnAtMost G S k) (hSc : HasPathCoverOnAtMost G Sᶜ l) :
    HasPathCoverAtMost G (k + l) := by
  rw [hasPathCoverAtMost_iff_on_univ]
  simpa only [Set.union_compl_self] using hS.append hSc

/-- Minimal-counterexample extension: lift the cover of the induced complement, and add a cover of
the removed set. -/
lemma hasPathCoverAtMost_of_induced_compl {G : SimpleGraph V} {S : Set V} {k l : ℕ}
    (hSc : HasPathCoverAtMost (G.comap ((↑) : (Sᶜ : Set V) → V)) k)
    (hS : HasPathCoverOnAtMost G S l) :
    HasPathCoverAtMost G (l + k) := by
  exact hasPathCoverAtMost_of_coverOn_compl hS (hSc.lift_subtype G Sᶜ)

/-- Finset-flavoured minimal-counterexample extension. -/
lemma hasPathCoverAtMost_of_induced_finset_compl
    {G : SimpleGraph V} {S : Finset V} {k l : ℕ}
    (hSc : HasPathCoverAtMost (G.comap ((↑) : {v // v ∉ S} → V)) k)
    (hS : HasPathCoverOnAtMost G (S : Set V) l) :
    HasPathCoverAtMost G (l + k) := by
  exact hasPathCoverAtMost_of_induced_compl (S := (S : Set V)) hSc hS

lemma hasPathCoverAtMost_of_path_and_induced_compl [DecidableEq V]
    {G : SimpleGraph V} {p : List V} {k : ℕ} (hp : IsPath G p)
    (hcomp : HasPathCoverAtMost
      (G.comap ((↑) : ({v | v ∉ pathSupport p} : Set V) → V)) k) :
    HasPathCoverAtMost G (1 + k) := by
  let S : Set V := (pathSupport p : Set V)
  have hS : HasPathCoverOnAtMost G S 1 := by
    refine ⟨[p], by simp, ?_⟩
    refine ⟨by simpa using hp, ?_⟩
    intro v hv
    exact ⟨p, by simp, mem_pathSupport.mp hv⟩
  exact hasPathCoverAtMost_of_induced_compl hcomp hS

/-! ### The elementary fixed-path cover -/

/-- A path together with singleton paths on every vertex outside it covers the whole finite graph.
This is the exact `1 + |V \ V(p)|` bound used at the start of the minimal-counterexample proof. -/
lemma hasPathCoverAtMost_path_add_compl (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {p : List V} (hp : IsPath G p) :
    HasPathCoverAtMost G (1 + (Finset.univ \ pathSupport p).card) := by
  let outside : Finset V := Finset.univ \ pathSupport p
  let ps : List (List V) := p :: singletonPathFamilyFinset outside
  refine ⟨ps, ?_, ?_⟩
  · simp [ps, outside]
  · constructor
    · intro q hq
      have hq' : q = p ∨ q ∈ singletonPathFamilyFinset outside := by
        simpa only [ps, List.mem_cons] using hq
      rcases hq' with rfl | hq'
      · exact hp
      · exact (isPathCoverOn_singletonPathFamilyFinset G outside).1 q hq'
    · intro v
      by_cases hv : v ∈ pathSupport p
      · exact ⟨p, by simp [ps], mem_pathSupport.mp hv⟩
      · have hvout : v ∈ outside := by simp [outside, hv]
        exact ⟨[v], by simp [ps, hvout], by simp⟩

end Erdos518
