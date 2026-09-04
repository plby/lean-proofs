import Mathlib

/-!
# The Füredi--Naor--Verstraëte duplication construction

This file isolates the purely graph-theoretic part of the lower construction
used for Erdős problem 59.  A set `A` of vertices is copied.  Edges from `A`
to its complement are copied, while an edge inside `A` is copied in the
direction selected by an orientation.
-/

namespace Erdos59

open scoped BigOperators
open Finset

namespace FNV

variable {V : Type*} (G : SimpleGraph V) (A : Finset V)

/-- An orientation of the edges of `G` induced by `A`. -/
structure Orientation where
  /-- `Dir x y` means that the edge is directed from `x` to `y`. -/
  Dir : V → V → Prop
  dir_adj : ∀ {x y}, Dir x y → G.Adj x y
  dir_fst_mem : ∀ {x y}, Dir x y → x ∈ A
  dir_snd_mem : ∀ {x y}, Dir x y → y ∈ A
  exactly_one : ∀ {x y}, G.Adj x y → x ∈ A → y ∈ A → (Dir x y ↔ ¬ Dir y x)

namespace Orientation

variable {G A} (O : Orientation G A)

lemma not_rev {x y : V} (h : O.Dir x y) : ¬ O.Dir y x := by
  exact (O.exactly_one (O.dir_adj h) (O.dir_fst_mem h) (O.dir_snd_mem h)).mp h

lemma resolve {x y : V} (hxy : G.Adj x y) (hx : x ∈ A) (hy : y ∈ A) :
    O.Dir x y ∨ O.Dir y x := by
  by_cases h : O.Dir x y
  · exact Or.inl h
  · exact Or.inr <| not_not.mp <| (O.exactly_one hxy hx hy).not.mp h

end Orientation

/-- The old vertices together with a disjoint copy of `A`. -/
abbrev DuplicateVertex := Sum V A

/-- Collapse a copied vertex back to its old vertex. -/
def project : DuplicateVertex A → V
  | .inl v => v
  | .inr a => a.1

variable (O : Orientation G A)

/-- The FNV graph obtained by duplicating `A` according to `O`. -/
def duplication : SimpleGraph (DuplicateVertex A) where
  Adj x y :=
    match x, y with
    | .inl x, .inl y => G.Adj x y
    | .inl x, .inr y => G.Adj x y ∧ (x ∉ A ∨ O.Dir y x)
    | .inr x, .inl y => G.Adj x y ∧ (y ∉ A ∨ O.Dir x y)
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (x | x) (y | y) h
    · exact h.symm
    · exact ⟨h.1.symm, h.2⟩
    · exact ⟨h.1.symm, h.2⟩
    · exact h⟩
  loopless := ⟨by
    rintro (x | x) h
    · exact G.loopless.irrefl _ h
    · exact h⟩

instance [DecidableEq V] [DecidableRel G.Adj] [DecidableRel O.Dir] :
    DecidableRel (duplication G A O).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [duplication] <;> infer_instance

@[simp] lemma duplication_adj_old_old (x y : V) :
    (duplication G A O).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

@[simp] lemma duplication_adj_old_new (x : V) (y : A) :
    (duplication G A O).Adj (.inl x) (.inr y) ↔
      G.Adj x y ∧ (x ∉ A ∨ O.Dir y x) := Iff.rfl

@[simp] lemma duplication_adj_new_old (x : A) (y : V) :
    (duplication G A O).Adj (.inr x) (.inl y) ↔
      G.Adj x y ∧ (y ∉ A ∨ O.Dir x y) := Iff.rfl

@[simp] lemma duplication_not_adj_new_new (x y : A) :
    ¬ (duplication G A O).Adj (.inr x) (.inr y) := by simp [duplication]

/-- Every new edge projects to an old edge. -/
def projectionHom : duplication G A O →g G where
  toFun := project A
  map_rel' := by
    intro x y h
    cases x <;> cases y <;> simp_all [duplication, project]

@[simp] lemma projectionHom_apply (x : DuplicateVertex A) :
    projectionHom G A O x = project A x := rfl

/-- A cycle is represented by six distinct cyclically adjacent vertices. -/
def IsSixCycle (H : SimpleGraph V) (x : Fin 6 → V) : Prop :=
  Function.Injective x ∧ ∀ i, H.Adj (x i) (x (i + 1))

/-- `H` has no cycle of length six. -/
def C6Free (H : SimpleGraph V) : Prop :=
  ∀ x : Fin 6 → V, ¬ IsSixCycle H x

/-- The analogous indexed definition of quadrilateral-freeness. -/
def C4Free (H : SimpleGraph V) : Prop :=
  ∀ x : Fin 4 → V, ¬ (Function.Injective x ∧ ∀ i, H.Adj (x i) (x (i + 1)))

/-- Triangle-freeness, stated using Mathlib's clique predicate. -/
abbrev TriangleFree (H : SimpleGraph V) : Prop := H.CliqueFree 3

private lemma project_eq_of_ne {x y : DuplicateVertex A}
    (hxy : project A x = project A y) (hne : x ≠ y) :
    (∃ a : A, x = .inl a.1 ∧ y = .inr a) ∨
      ∃ a : A, x = .inr a ∧ y = .inl a.1 := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact False.elim <| hne <| congrArg Sum.inl hxy
      | inr y => exact Or.inl ⟨y, by simpa [project] using hxy, rfl⟩
  | inr x =>
      cases y with
      | inl y => exact Or.inr ⟨x, rfl, by simpa [project] using hxy.symm⟩
      | inr y =>
          exact False.elim <| hne <| congrArg Sum.inr <| Subtype.ext hxy

private lemma project_fiber_three {x y z : DuplicateVertex A}
    (hxy : project A x = project A y) (hxz : project A x = project A z) :
    x = y ∨ x = z ∨ y = z := by
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Or.inl <| congrArg Sum.inl hxy
      | inr y =>
          cases z with
          | inl z => exact Or.inr <| Or.inl <| congrArg Sum.inl hxz
          | inr z =>
              right; right
              exact congrArg Sum.inr <| Subtype.ext <| hxy.symm.trans hxz
  | inr x =>
      cases y with
      | inl y =>
          cases z with
          | inl z =>
              right; right
              exact congrArg Sum.inl <| hxy.symm.trans hxz
          | inr z => exact Or.inr <| Or.inl <| congrArg Sum.inr <| Subtype.ext hxz
      | inr y => exact Or.inl <| congrArg Sum.inr <| Subtype.ext hxy

private lemma c4_collision {a b c d : V} (hfree : C4Free G)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    a = c ∨ b = d := by
  by_contra h
  push_neg at h
  apply hfree ![a, b, c, d]
  constructor
  · intro i j hij
    have hab' := hab.ne
    have hbc' := hbc.ne
    have hcd' := hcd.ne
    have hda' := hda.ne
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · simpa using hda

private lemma fin6_pair_cases (i j : Fin 6) (hij : i ≠ j) :
    j = i + 1 ∨ i = j + 1 ∨ j = i + 3 ∨
      (∃ k : Fin 6, i = k ∧ j = k + 2) ∨
      ∃ k : Fin 6, j = k ∧ i = k + 2 := by
  fin_cases i <;> fin_cases j <;> simp_all

private lemma triangle_of_opposite_collision
    (htri : TriangleFree G) {x : Fin 6 → DuplicateVertex A}
    (hadj : ∀ i, (duplication G A O).Adj (x i) (x (i + 1)))
    {i : Fin 6} (hopp : project A (x (i + 3)) = project A (x i)) : False := by
  classical
  let a := project A (x i)
  let b := project A (x (i + 1))
  let c := project A (x ((i + 1) + 1))
  have hab : G.Adj a b := (projectionHom G A O).map_rel (hadj i)
  have hbc : G.Adj b c := (projectionHom G A O).map_rel (hadj (i + 1))
  have hca : G.Adj c a := by
    have h := (projectionHom G A O).map_rel (hadj ((i + 1) + 1))
    simpa [a, c, add_assoc, hopp] using h
  exact htri {a, b, c} <| SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩

private lemma gap_two_orientation_contradiction
    (h4 : C4Free G) {x : Fin 6 → DuplicateVertex A} (hinj : Function.Injective x)
    (hadj : ∀ i, (duplication G A O).Adj (x i) (x (i + 1)))
    {k : Fin 6} (hgap : project A (x k) = project A (x (k + 2))) : False := by
  let y : Fin 6 → DuplicateVertex A := fun i ↦ x (k + i)
  have hyinj : Function.Injective y := fun _ _ h ↦ by
    exact add_left_cancel (hinj h)
  have hyadj : ∀ i, (duplication G A O).Adj (y i) (y (i + 1)) := by
    intro i
    simpa [y, add_assoc] using hadj (k + i)
  have h02 : project A (y 0) = project A (y 2) := by simpa [y] using hgap
  have h03 : G.Adj (project A (y 0)) (project A (y 3)) := by
    rw [h02]
    simpa using (projectionHom G A O).map_rel (hyadj 2)
  have h34 : G.Adj (project A (y 3)) (project A (y 4)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 3)
  have h45 : G.Adj (project A (y 4)) (project A (y 5)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 4)
  have h50 : G.Adj (project A (y 5)) (project A (y 0)) := by
    simpa using (projectionHom G A O).map_rel (hyadj 5)
  have hc := c4_collision (G := G) h4 h03 h34 h45 h50
  have h35 : project A (y 3) = project A (y 5) := by
    rcases hc with h04 | h35
    · exact False.elim <| by
        rcases project_fiber_three (A := A) h02 h04 with h | h | h
        · exact (show (0 : Fin 6) ≠ 2 by decide) (hyinj (show y 0 = y 2 from h))
        · exact (show (0 : Fin 6) ≠ 4 by decide) (hyinj (show y 0 = y 4 from h))
        · exact (show (2 : Fin 6) ≠ 4 by decide) (hyinj (show y 2 = y 4 from h))
    · exact h35
  have hne02 : y 0 ≠ y 2 := fun h ↦ by exact (by decide : (0 : Fin 6) ≠ 2) (hyinj h)
  have hne35 : y 3 ≠ y 5 := fun h ↦ by exact (by decide : (3 : Fin 6) ≠ 5) (hyinj h)
  have he23 := hyadj 2
  have he50 := hyadj 5
  rcases project_eq_of_ne (A := A) h02 hne02 with ⟨a, h0, h2⟩ | ⟨a, h0, h2⟩ <;>
    rcases project_eq_of_ne (A := A) h35 hne35 with ⟨b, h3, h5⟩ | ⟨b, h3, h5⟩
  · have he23' : G.Adj a b ∧ O.Dir a b := by
      simpa [h2, h3, duplication] using he23
    have he50' : G.Adj b a ∧ O.Dir b a := by
      simpa [h5, h0, duplication] using he50
    have hab : O.Dir a b := he23'.2
    have hba : O.Dir b a := he50'.2
    exact O.not_rev hab hba
  · simpa [h2, h3, duplication] using he23
  · simpa [h5, h0, duplication] using he50
  · have he23' : G.Adj a b ∧ O.Dir b a := by
      simpa [h2, h3, duplication] using he23
    have he50' : G.Adj b a ∧ O.Dir a b := by
      simpa [h5, h0, duplication] using he50
    have hba : O.Dir b a := he23'.2
    have hab : O.Dir a b := he50'.2
    exact O.not_rev hab hba

/-- The FNV projection lemma: duplication preserves hexagon-freeness. -/
theorem duplication_c6Free (h3 : TriangleFree G) (h4 : C4Free G) (h6 : C6Free G) :
    C6Free (duplication G A O) := by
  intro x hx
  rcases hx with ⟨hinj, hadj⟩
  let p : Fin 6 → V := fun i ↦ project A (x i)
  have padj : ∀ i, G.Adj (p i) (p (i + 1)) := fun i ↦
    (projectionHom G A O).map_rel (hadj i)
  by_cases hp : Function.Injective p
  · exact h6 p ⟨hp, padj⟩
  · rw [Function.Injective] at hp
    push_neg at hp
    obtain ⟨i, j, hpij, hij⟩ := hp
    rcases fin6_pair_cases i j hij with h | h | h | h | h
    · exact (padj i).ne <| by simpa [h] using hpij
    · exact (padj j).ne <| by simpa [h] using hpij.symm
    · exact triangle_of_opposite_collision (G := G) (A := A) (O := O)
        h3 hadj (by simpa [p, h] using hpij.symm)
    · rcases h with ⟨k, rfl, rfl⟩
      exact gap_two_orientation_contradiction (G := G) (A := A) (O := O)
        h4 hinj hadj (by simpa [p] using hpij)
    · rcases h with ⟨k, rfl, rfl⟩
      exact gap_two_orientation_contradiction (G := G) (A := A) (O := O)
        h4 hinj hadj (by simpa [p] using hpij.symm)

/-- The projection is injective on any clique of the duplicated graph. -/
private lemma project_injOn_clique {s : Finset (DuplicateVertex A)}
    (hs : (duplication G A O).IsClique s) : Set.InjOn (project A) s := by
  intro x hx y hy hxy
  by_contra hne
  exact ((projectionHom G A O).map_rel
    (hs (x := x) (y := y) hx hy hne)).ne hxy

/-- Duplication of a triangle-free graph is triangle-free. -/
theorem duplication_triangleFree (h3 : TriangleFree G) :
    TriangleFree (duplication G A O) := by
  classical
  intro s hs
  let t := s.image (project A)
  have hcard : t.card = 3 := by
    simp only [t, card_image_iff.mpr
      (project_injOn_clique (G := G) (A := A) (O := O) hs.isClique), hs.card_eq]
  apply h3 t
  refine ⟨?_, hcard⟩
  intro x hx y hy hxy
  change x ∈ t at hx
  change y ∈ t at hy
  simp only [t, Finset.mem_image] at hx hy
  obtain ⟨x', hx's, rfl⟩ := hx
  obtain ⟨y', hy's, rfl⟩ := hy
  have hxy' : x' ≠ y' := fun h ↦ hxy (congrArg (project A) h)
  exact (projectionHom G A O).map_rel (hs.isClique hx's hy's hxy')

/-! ## The exact edge increment -/

section Counting

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableRel O.Dir]

/-- Pairs `(a,x)` which give an edge from the new copy of `a` to the old `x`. -/
def addedPairs : Finset (A × V) :=
  Finset.univ.filter fun p ↦ G.Adj p.1 p.2 ∧ (p.2 ∉ A ∨ O.Dir p.1 p.2)

@[simp] lemma mem_addedPairs (p : A × V) :
    p ∈ addedPairs G A O ↔
      G.Adj p.1 p.2 ∧ (p.2 ∉ A ∨ O.Dir p.1 p.2) := by
  simp [addedPairs]

/-- The base edges with at least one endpoint in `A`. -/
def incidentEdges : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ ∃ a ∈ A, a ∈ e

@[simp] lemma mem_incidentEdges (e : Sym2 V) :
    e ∈ incidentEdges G A ↔ e ∈ G.edgeFinset ∧ ∃ a ∈ A, a ∈ e := by
  simp [incidentEdges]

private def oldEmbedding : V ↪ DuplicateVertex A :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def crossEdgeEmbedding : A × V ↪ Sym2 (DuplicateVertex A) where
  toFun p := s(Sum.inr p.1, Sum.inl p.2)
  inj' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h, -⟩
    · exact Prod.ext (Sum.inr.inj h₁) (Sum.inl.inj h₂)
    · exact False.elim <| Sum.inr_ne_inl h

private def oldEdges : Finset (Sym2 (DuplicateVertex A)) :=
  G.edgeFinset.map (oldEmbedding A).sym2Map

private def addedEdges : Finset (Sym2 (DuplicateVertex A)) :=
  (addedPairs G A O).map (crossEdgeEmbedding A)

private lemma mem_oldEdges_iff (e : Sym2 (DuplicateVertex A)) :
    e ∈ oldEdges G A ↔
      ∃ x y : V, G.Adj x y ∧ e = s(Sum.inl x, Sum.inl y) := by
  constructor
  · rw [oldEdges, Finset.mem_map]
    rintro ⟨e', he', rfl⟩
    induction e' using Sym2.inductionOn with
    | _ x y =>
        refine ⟨x, y, ?_, ?_⟩
        · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'
        · simp [oldEmbedding]
  · rintro ⟨x, y, hxy, rfl⟩
    rw [oldEdges, Finset.mem_map]
    refine ⟨s(x, y), ?_, ?_⟩
    · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
    · simp [oldEmbedding]

private lemma mem_addedEdges_iff (e : Sym2 (DuplicateVertex A)) :
    e ∈ addedEdges G A O ↔
      ∃ a : A, ∃ x : V,
        G.Adj a x ∧ (x ∉ A ∨ O.Dir a x) ∧ e = s(Sum.inr a, Sum.inl x) := by
  constructor
  · rw [addedEdges, Finset.mem_map]
    rintro ⟨⟨a, x⟩, hp, rfl⟩
    have hp' := (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mp hp
    exact ⟨a, x, hp'.1, hp'.2, rfl⟩
  · rintro ⟨a, x, hAdj, hcond, rfl⟩
    rw [addedEdges, Finset.mem_map]
    exact ⟨(a, x),
      (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mpr ⟨hAdj, hcond⟩,
      rfl⟩

private lemma edgeFinset_duplication :
    (duplication G A O).edgeFinset = oldEdges G A ∪ addedEdges G A O := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      rw [mem_oldEdges_iff, mem_addedEdges_iff]
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              simp only [duplication_adj_old_old, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Sum.inl.injEq, Prod.swap_prod_mk,
    reduceCtorEq, false_and, and_false, or_self, exists_false, or_false]
              constructor
              · intro hxy
                exact ⟨x, y, hxy, Or.inl ⟨rfl, rfl⟩⟩
              · rintro ⟨u, v, huv, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
                · exact huv
                · exact huv.symm
          | inr y => simp [duplication, Sym2.eq_iff, G.adj_comm]
      | inr x =>
          cases y with
          | inl y => simp [duplication, Sym2.eq_iff, G.adj_comm]
          | inr y => simp [duplication, Sym2.eq_iff, G.adj_comm]

private lemma oldEdges_disjoint_addedEdges :
    Disjoint (oldEdges G A) (addedEdges G A O) := by
  rw [Finset.disjoint_left]
  intro e heold headd
  simp only [oldEdges, mem_map] at heold
  simp only [addedEdges, mem_map] at headd
  rcases heold with ⟨e', -, rfl⟩
  rcases headd with ⟨p, -, hp⟩
  induction e' using Sym2.inductionOn with
  | _ x y =>
      change s(Sum.inr p.1, Sum.inl p.2) = s(Sum.inl x, Sum.inl y) at hp
      rw [Sym2.eq_iff] at hp
      rcases hp with ⟨h, -⟩ | ⟨h, -⟩
      · exact Sum.inr_ne_inl h
      · exact Sum.inr_ne_inl h

private lemma card_oldEdges : (oldEdges G A).card = G.edgeFinset.card := by
  simp [oldEdges]

private lemma baseEdge_injOn_addedPairs :
    Set.InjOn (fun p : A × V ↦ s(p.1.1, p.2)) (addedPairs G A O) := by
  rintro ⟨a, x⟩ ha ⟨b, y⟩ hb h
  have ha := (mem_addedPairs (G := G) (A := A) (O := O) (a, x)).mp ha
  have hb := (mem_addedPairs (G := G) (A := A) (O := O) (b, y)).mp hb
  rw [Sym2.eq_iff] at h
  change (a.1 = b.1 ∧ x = y) ∨ (a.1 = y ∧ x = b.1) at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Prod.ext (Subtype.ext h₁) h₂
  · have hxA : x ∈ A := h₂ ▸ b.2
    have hyA : y ∈ A := h₁.symm ▸ a.2
    have hdax : O.Dir a x := ha.2.resolve_left (by simpa using hxA)
    have hdby : O.Dir b y := hb.2.resolve_left (by simpa using hyA)
    exact False.elim <| O.not_rev hdax <| by simpa [h₁, h₂] using hdby

private lemma image_baseEdge_addedPairs :
    (addedPairs G A O).image (fun p : A × V ↦ s(p.1.1, p.2)) = incidentEdges G A := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Finset.mem_image, mem_addedPairs, mem_incidentEdges,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.eq_iff,
        Sym2.mem_iff]
      constructor
      · rintro ⟨⟨a, z⟩, ⟨haz, -⟩, h⟩
        rcases h with ⟨hax, hzy⟩ | ⟨hay, hzx⟩ <;> subst_vars
        · exact ⟨haz, a, a.2, Or.inl rfl⟩
        · exact ⟨haz.symm, a, a.2, Or.inr rfl⟩
      · rintro ⟨hxy, a, haA, ha⟩
        rcases ha with hax | hay
        · have hayAdj : G.Adj a y := by simpa [hax] using hxy
          by_cases hyA : y ∈ A
          · rcases O.resolve hayAdj haA hyA with hdir | hdir
            · exact ⟨(⟨a, haA⟩, y), ⟨hayAdj, Or.inr hdir⟩,
                Or.inl ⟨hax, rfl⟩⟩
            · exact ⟨(⟨y, hyA⟩, a), ⟨hayAdj.symm, Or.inr hdir⟩,
                Or.inr ⟨rfl, hax⟩⟩
          · exact ⟨(⟨a, haA⟩, y), ⟨hayAdj, Or.inl hyA⟩,
              Or.inl ⟨hax, rfl⟩⟩
        · have hxaAdj : G.Adj x a := by simpa [hay] using hxy
          by_cases hxA : x ∈ A
          · rcases O.resolve hxaAdj hxA haA with hdir | hdir
            · exact ⟨(⟨x, hxA⟩, a), ⟨hxaAdj, Or.inr hdir⟩,
                Or.inl ⟨rfl, hay⟩⟩
            · exact ⟨(⟨a, haA⟩, x), ⟨hxaAdj.symm, Or.inr hdir⟩,
                Or.inr ⟨hay, rfl⟩⟩
          · exact ⟨(⟨a, haA⟩, x), ⟨hxaAdj.symm, Or.inl hxA⟩,
              Or.inr ⟨hay, rfl⟩⟩

private lemma card_addedPairs_eq_incidentEdges :
    (addedPairs G A O).card = (incidentEdges G A).card := by
  rw [← image_baseEdge_addedPairs (G := G) (A := A) (O := O),
    Finset.card_image_iff.mpr (baseEdge_injOn_addedPairs (G := G) (A := A) (O := O))]

/-- The number of new edges is exactly the number of old edges incident to `A`. -/
theorem card_edgeFinset_duplication :
    (duplication G A O).edgeFinset.card =
      G.edgeFinset.card + (incidentEdges G A).card := by
  rw [edgeFinset_duplication (G := G) (A := A) (O := O),
    Finset.card_union_of_disjoint (oldEdges_disjoint_addedEdges (G := G) (A := A) (O := O)),
    card_oldEdges (G := G) (A := A)]
  simp only [addedEdges, card_map,
    card_addedPairs_eq_incidentEdges (G := G) (A := A) (O := O)]

end Counting

/-! ## Deterministic double counting over fixed-size subsets -/

section Averaging

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private lemma card_incident_subset_filter (K : ℕ) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    ((Finset.univ.powersetCard K).filter fun B : Finset V ↦
      ∃ a ∈ B, a ∈ e).card =
      (Fintype.card V).choose K - (Fintype.card V - 2).choose K := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      let S := (Finset.univ : Finset V).powersetCard K
      have havoid :
          (S.filter fun B : Finset V ↦ ¬ ∃ a ∈ B, a ∈ s(x, y)) =
            ((Finset.univ : Finset V) \ {x, y}).powersetCard K := by
        ext B
        simp only [S, Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨-, hcard⟩, hav⟩
          refine ⟨?_, hcard⟩
          intro z hz
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ z, ?_⟩
          intro hzxy
          exact hav ⟨z, hz, by simpa [Sym2.mem_iff] using hzxy⟩
        · rintro ⟨hsub, hcard⟩
          refine ⟨⟨Finset.subset_univ B, hcard⟩, ?_⟩
          rintro ⟨z, hz, hzxy⟩
          have hznot : z ∉ ({x, y} : Finset V) := (Finset.mem_sdiff.mp (hsub hz)).2
          exact hznot (by simpa [Sym2.mem_iff] using hzxy)
      have hpartition :
          (S.filter fun B : Finset V ↦ ∃ a ∈ B, a ∈ s(x, y)) =
            S \ (S.filter fun B : Finset V ↦ ¬ ∃ a ∈ B, a ∈ s(x, y)) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hBS, hP⟩
          exact ⟨hBS, fun hneg ↦ hneg.2 hP⟩
        · rintro ⟨hBS, hnot⟩
          refine ⟨hBS, ?_⟩
          by_contra hP
          exact hnot ⟨hBS, hP⟩
      rw [show (Finset.univ.powersetCard K) = S from rfl, hpartition,
        Finset.card_sdiff_of_subset (Finset.filter_subset _ _), havoid,
        Finset.card_powersetCard, Finset.card_powersetCard]
      have hpair : #({x, y} : Finset V) = 2 := by simp [hxy.ne]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ {x, y}),
        Finset.card_univ, hpair]

/-- Every edge is counted in exactly
`choose |V| K - choose (|V|-2) K` of the `K`-subsets. -/
theorem sum_card_incidentEdges_powersetCard (K : ℕ) :
    ∑ B ∈ (Finset.univ : Finset V).powersetCard K, (incidentEdges G B).card =
      G.edgeFinset.card *
        ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by
  classical
  calc
    ∑ B ∈ (Finset.univ : Finset V).powersetCard K, (incidentEdges G B).card =
        ∑ B ∈ (Finset.univ : Finset V).powersetCard K,
          ∑ e ∈ G.edgeFinset, if ∃ a ∈ B, a ∈ e then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro B hB
            simp [incidentEdges]
    _ = ∑ e ∈ G.edgeFinset,
          ∑ B ∈ (Finset.univ : Finset V).powersetCard K,
            if ∃ a ∈ B, a ∈ e then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ G.edgeFinset,
          ((Finset.univ.powersetCard K).filter fun B : Finset V ↦
            ∃ a ∈ B, a ∈ e).card := by
          apply Finset.sum_congr rfl
          intro e he
          simp
    _ = ∑ _e ∈ G.edgeFinset,
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by
          apply Finset.sum_congr rfl
          intro e he
          exact card_incident_subset_filter (G := G) K he
    _ = G.edgeFinset.card *
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) := by simp

/-- A deterministic averaging conclusion: some `K`-subset receives at least
the average number of incident edges, with denominators cleared. -/
theorem exists_subset_incidentEdges_average {K : ℕ} (hK : K ≤ Fintype.card V) :
    ∃ B : Finset V, B.card = K ∧
      G.edgeFinset.card *
          ((Fintype.card V).choose K - (Fintype.card V - 2).choose K) ≤
        (Fintype.card V).choose K * (incidentEdges G B).card := by
  classical
  let S := (Finset.univ : Finset V).powersetCard K
  have hS : S.Nonempty := by
    exact Finset.powersetCard_nonempty_of_le (by simpa [S] using hK)
  obtain ⟨B, hBS, hmax⟩ :=
    Finset.exists_max_image S (fun B ↦ (incidentEdges G B).card) hS
  refine ⟨B, Finset.mem_powersetCard_univ.mp hBS, ?_⟩
  have hsum :
      ∑ C ∈ S, (incidentEdges G C).card ≤ S.card * (incidentEdges G B).card := by
    calc
      ∑ C ∈ S, (incidentEdges G C).card ≤
          ∑ _C ∈ S, (incidentEdges G B).card :=
        Finset.sum_le_sum fun C hC ↦ hmax C hC
      _ = S.card * (incidentEdges G B).card := by simp
  rw [show S = (Finset.univ : Finset V).powersetCard K from rfl,
    sum_card_incidentEdges_powersetCard (G := G) K,
    Finset.card_powersetCard, Finset.card_univ] at hsum
  exact hsum

end Averaging

end FNV

end Erdos59
