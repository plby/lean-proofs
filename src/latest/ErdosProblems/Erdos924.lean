/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 924.
https://www.erdosproblems.com/forum/thread/924

Informal authors:
- Jaroslav Nešetřil
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos924.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos161.Ramsey

/-!
# Erdős Problem 924

Nešetřil and Rödl proved that for every finite graph `H` and every nonempty
finite edge-color palette there is a graph with the same clique number in
which every edge coloring has a monochromatic induced copy of `H`.  We
formalize the complete-graph instance: for `k ≥ 2` and `l ≥ 3`, a finite
`K_{l+1}`-free graph is edge-Ramsey for `K_l` in `k` colors.

The detailed partite construction and the Leanization map are in
`tex/924.tex`.
-/

namespace Erdos924

open Finset Fintype
open SimpleGraph
open scoped SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## The exact Ramsey property -/

/-- Every `k`-edge-coloring of `G` contains a monochromatic `l`-clique. -/
def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ C : SimpleGraph.EdgeLabeling G (Fin k),
    ∃ i : Fin k, ∃ S : Finset V, (C.labelGraph i).IsNClique l S

/-! ## Arbitrary-palette finite hypergraph Ramsey -/

/-- Pull a finite set of naturals back to the initial interval `Fin d`. -/
def pullNatEdge (d : ℕ) (e : Finset ℕ) : Finset (Fin d) :=
  e.preimage (Erdos161.finNatEmbedding d) (Erdos161.finNatEmbedding d).injective.injOn

@[simp] lemma pullNatEdge_liftFiniteEdge {d : ℕ} (e : Finset (Fin d)) :
    pullNatEdge d (Erdos161.liftFiniteEdge e) = e := by
  apply Finset.ext
  intro x
  simp [pullNatEdge, Erdos161.liftFiniteEdge, Erdos161.finNatEmbedding]

/-- The repository's proved Boolean finite hypergraph Ramsey theorem, with a
domain that is definitionally `Finset (Fin d)`. -/
lemma finite_bool_ramsey (t h : ℕ) :
    ∃ d, ∀ C : Finset (Fin d) → Bool,
      ∃ H : Finset (Fin d), H.card = h ∧
        ∃ b : Bool, ∀ e : Finset (Fin d), e.card = t → e ⊆ H → C e = b := by
  obtain ⟨d, hd⟩ := Erdos161.finite_hypergraph_ramsey t h
  refine ⟨d, fun C => ?_⟩
  let Cnat : Erdos161.InfiniteEdgeColoring t := fun e => C (pullNatEdge d e.1)
  obtain ⟨H, hH, b, hb⟩ := hd Cnat
  refine ⟨H, hH, b, ?_⟩
  intro e he hsub
  have h := hb e he hsub
  simpa [Cnat] using h

/-- Homogeneity of all `t`-subsets of a finite vertex set. -/
def FinHomogeneous {d r : ℕ} (t : ℕ) (C : Finset (Fin d) → Fin r)
    (H : Finset (Fin d)) : Prop :=
  ∃ c : Fin r, ∀ e : Finset (Fin d), e.card = t → e ⊆ H → C e = c

/-- Finite hypergraph Ramsey for an arbitrary finite palette, derived from
the proved Boolean theorem by induction on the number of colors. -/
theorem finite_fin_ramsey (r t h : ℕ) :
    ∃ d, h ≤ d ∧ ∀ C : Finset (Fin d) → Fin r,
      ∃ H : Finset (Fin d), H.card = h ∧ FinHomogeneous t C H := by
  induction r with
  | zero =>
      refine ⟨h, le_rfl, ?_⟩
      intro C
      exact Fin.elim0 (C ∅)
  | succ r ih =>
      cases r with
      | zero =>
          refine ⟨h, le_rfl, fun C => ⟨Finset.univ, by simp, ?_⟩⟩
          refine ⟨0, ?_⟩
          intro e he hsub
          apply Fin.ext
          omega
      | succ r =>
          obtain ⟨d₀, hd₀h, hd₀⟩ := ih
          obtain ⟨d, hd⟩ := finite_bool_ramsey t d₀
          refine ⟨d, ?_, ?_⟩
          · have hle : d₀ ≤ d := by
              let test : Finset (Fin d) → Bool := fun _ => false
              obtain ⟨K, hK, -⟩ := hd test
              have hcard := Finset.card_le_univ K
              simpa [hK] using hcard
            exact hd₀h.trans hle
          · intro C
            let indicator : Finset (Fin d) → Bool := fun e => decide (C e = 0)
            obtain ⟨K, hKcard, b, hb⟩ := hd indicator
            cases b with
            | false =>
                let f : Fin d₀ ↪ Fin d := (K.orderEmbOfFin hKcard).toEmbedding
                let C₀ : Finset (Fin d₀) → Fin (r + 1) := fun e =>
                  (0 : Fin (r + 1)).predAbove (C (e.map f))
                obtain ⟨H₀, hH₀card, c₀, hc₀⟩ := hd₀ C₀
                let H : Finset (Fin d) := H₀.map f
                refine ⟨H, by simp [H, hH₀card],
                  (0 : Fin (r + 2)).succAbove c₀, ?_⟩
                intro e hecard heH
                have hHK : H ⊆ K := by
                  intro x hx
                  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
                  exact Finset.orderEmbOfFin_mem K hKcard y
                let e₀ : Finset (Fin d₀) := e.preimage f f.injective.injOn
                have himage : e₀.map f = e := by
                  rw [Finset.map_eq_image]
                  rw [show e₀ = e.preimage f f.injective.injOn by rfl,
                    Finset.image_preimage]
                  apply Finset.filter_eq_self.mpr
                  intro x hx
                  obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp (heH hx)
                  exact ⟨y, hyx⟩
                have he₀card : e₀.card = t := by
                  have hcardmap : (e₀.map f).card = e₀.card := by simp
                  rw [himage, hecard] at hcardmap
                  omega
                have he₀H : e₀ ⊆ H₀ := by
                  intro x hx
                  have hxmap : f x ∈ e := by
                    rw [← himage]
                    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
                  obtain ⟨y, hyH₀, hyx⟩ := Finset.mem_map.mp (heH hxmap)
                  exact f.injective hyx ▸ hyH₀
                have hpred := hc₀ e₀ he₀card he₀H
                have hnotzero : C e ≠ 0 := by
                  intro hzero
                  have hbool := hb e hecard (heH.trans hHK)
                  simp [indicator, hzero] at hbool
                have hreconstruct :
                    (0 : Fin (r + 2)).succAbove
                        ((0 : Fin (r + 1)).predAbove (C e)) = C e := by
                  apply Fin.succAbove_predAbove (p := (0 : Fin (r + 1)))
                  simpa using hnotzero
                calc
                  C e = (0 : Fin (r + 2)).succAbove
                      ((0 : Fin (r + 1)).predAbove (C e)) := hreconstruct.symm
                  _ = (0 : Fin (r + 2)).succAbove c₀ := by
                    apply congrArg
                    simpa [C₀, himage] using hpred
            | true =>
                obtain ⟨H, hHK, hHcard⟩ := Finset.exists_subset_card_eq
                  (s := K) (n := h) (by omega)
                refine ⟨H, hHcard, 0, ?_⟩
                intro e hecard heH
                have hbool := hb e hecard (heH.trans hHK)
                simpa [indicator] using hbool

/-! ## Finite partite graphs and induced partite embeddings -/

/-- A finite graph together with a map to a finite set of parts.  The last
field says that every edge runs between distinct parts. -/
structure PartiteGraph (n : ℕ) where
  V : Type
  fintypeV : Fintype V
  decEqV : DecidableEq V
  graph : SimpleGraph V
  decAdj : DecidableRel graph.Adj
  part : V → Fin n
  part_ne_of_adj : ∀ {u v}, graph.Adj u v → part u ≠ part v

instance {n : ℕ} (P : PartiteGraph n) : Fintype P.V := P.fintypeV
instance {n : ℕ} (P : PartiteGraph n) : DecidableEq P.V := P.decEqV
instance {n : ℕ} (P : PartiteGraph n) : DecidableRel P.graph.Adj := P.decAdj

/-- An induced graph embedding which also preserves the part map. -/
structure PartiteEmbedding {n : ℕ} (P Q : PartiteGraph n) where
  toGraphEmbedding : P.graph ↪g Q.graph
  map_part : ∀ v, Q.part (toGraphEmbedding v) = P.part v

instance {n : ℕ} {P Q : PartiteGraph n} : CoeFun (PartiteEmbedding P Q)
    (fun _ => P.V → Q.V) := ⟨fun f => f.toGraphEmbedding⟩

namespace PartiteEmbedding

variable {n : ℕ} {P Q R : PartiteGraph n}

@[simp] theorem map_part_eq (f : PartiteEmbedding P Q) (v : P.V) :
    Q.part (f v) = P.part v := f.map_part v

theorem injective (f : PartiteEmbedding P Q) : Function.Injective f :=
  f.toGraphEmbedding.injective

/-- The identity induced partite embedding. -/
def refl (P : PartiteGraph n) : PartiteEmbedding P P where
  toGraphEmbedding := SimpleGraph.Embedding.refl
  map_part := fun _ => rfl

/-- Composition of induced partite embeddings. -/
def comp (g : PartiteEmbedding Q R) (f : PartiteEmbedding P Q) :
    PartiteEmbedding P R where
  toGraphEmbedding := f.toGraphEmbedding.trans g.toGraphEmbedding
  map_part := fun v => by
    change R.part (g (f v)) = P.part v
    rw [g.map_part, f.map_part]

@[simp] theorem comp_apply (g : PartiteEmbedding Q R) (f : PartiteEmbedding P Q) (v : P.V) :
    comp g f v = g (f v) := rfl

end PartiteEmbedding

namespace PartiteGraph

variable {n : ℕ}

/-- The vertices in one row. -/
abbrev Row (A : PartiteGraph n) (i : Fin n) := {x : A.V // A.part x = i}

/-- Namespace-local spelling for the global induced partite embedding. -/
abbrev Embedding (A B : PartiteGraph n) := PartiteEmbedding A B

variable (A : PartiteGraph n) (a b : Fin n)

/-- Vertices outside the two rows currently being replaced. -/
abbrev Outside := {x : A.V // A.part x ≠ a ∧ A.part x ≠ b}

/-- The data supplied by a bipartite Ramsey witness.  Each `e : E` is an induced
part-respecting copy of the bipartite graph cut out by rows `a,b` of `A`. -/
structure TwoRowData (L R E : Type) where
  rel : L → R → Prop
  left : E → Row A a ↪ L
  right : E → Row A b ↪ R
  induced : ∀ e x y, rel (left e x) (right e y) ↔ A.graph.Adj x.1 y.1

/-- Vertices of the two-row replacement: the two active rows are shared, while
every inactive old vertex gets one tagged copy for every bipartite embedding. -/
inductive ReplacementVertex (L R E : Type)
  | left : L → ReplacementVertex L R E
  | right : R → ReplacementVertex L R E
  | tagged : Outside A a b → E → ReplacementVertex L R E
  deriving DecidableEq

def replacementVertexEquiv (L R E : Type) :
    ReplacementVertex A a b L R E ≃ L ⊕ R ⊕ (Outside A a b × E) where
  toFun
    | .left x => .inl x
    | .right y => .inr (.inl y)
    | .tagged x e => .inr (.inr (x, e))
  invFun
    | .inl x => .left x
    | .inr (.inl y) => .right y
    | .inr (.inr (x, e)) => .tagged x e
  left_inv x := by cases x <;> rfl
  right_inv
    | .inl x => rfl
    | .inr (.inl y) => rfl
    | .inr (.inr (x, e)) => rfl

namespace TwoRowData

variable {A : PartiteGraph n} {a b : Fin n}
variable {L R E : Type} (D : TwoRowData A a b L R E)

/-- Extension of a bipartite embedding to the tagged replacement. -/
def extend (e : E) (x : A.V) : ReplacementVertex A a b L R E :=
  if ha : A.part x = a then
    .left (D.left e ⟨x, ha⟩)
  else if hb : A.part x = b then
    .right (D.right e ⟨x, hb⟩)
  else
    .tagged ⟨x, ha, hb⟩ e

@[simp] theorem extend_of_part_eq_left (e : E) {x : A.V} (hx : A.part x = a) :
    D.extend e x = .left (D.left e ⟨x, hx⟩) := by
  simp [extend, hx]

@[simp] theorem extend_of_part_eq_right (hab : a ≠ b) (e : E) {x : A.V}
    (hx : A.part x = b) :
    D.extend e x = .right (D.right e ⟨x, hx⟩) := by
  simp [extend, hx, hab.symm]

@[simp] theorem extend_of_part_ne (e : E) {x : A.V}
    (ha : A.part x ≠ a) (hb : A.part x ≠ b) :
    D.extend e x = .tagged ⟨x, ha, hb⟩ e := by
  simp [extend, ha, hb]

/-- Adjacency in the replacement, defined directly by cases. -/
def ReplacementAdj : ReplacementVertex A a b L R E →
    ReplacementVertex A a b L R E → Prop
  | .left x, .right y => D.rel x y
  | .right y, .left x => D.rel x y
  | .tagged x e, .tagged y f => e = f ∧ A.graph.Adj x.1 y.1
  | .tagged x e, .left y =>
      ∃ z : Row A a, D.left e z = y ∧ A.graph.Adj x.1 z.1
  | .left y, .tagged x e =>
      ∃ z : Row A a, D.left e z = y ∧ A.graph.Adj x.1 z.1
  | .tagged x e, .right y =>
      ∃ z : Row A b, D.right e z = y ∧ A.graph.Adj x.1 z.1
  | .right y, .tagged x e =>
      ∃ z : Row A b, D.right e z = y ∧ A.graph.Adj x.1 z.1
  | _, _ => False

theorem replacementAdj_symm : Std.Symm D.ReplacementAdj := ⟨by
  intro u v h
  cases u <;> cases v <;> simp_all [ReplacementAdj, SimpleGraph.adj_comm]⟩

theorem replacementAdj_loopless : Std.Irrefl D.ReplacementAdj := ⟨by
  intro u
  cases u <;> simp [ReplacementAdj]⟩

/-- The underlying simple graph of the replacement. -/
def replacementGraph : SimpleGraph (ReplacementVertex A a b L R E) where
  Adj := D.ReplacementAdj
  symm := D.replacementAdj_symm
  loopless := D.replacementAdj_loopless

@[simp] theorem replacementGraph_adj :
    D.replacementGraph.Adj x y ↔ D.ReplacementAdj x y := Iff.rfl

/-- Row map on the replacement. -/
def replacementPart : ReplacementVertex A a b L R E → Fin n
  | .left _ => a
  | .right _ => b
  | .tagged x _ => A.part x.1

theorem part_ne_of_replacementAdj (hab : a ≠ b) {x y}
    (hxy : D.ReplacementAdj x y) :
    replacementPart (A := A) (a := a) (b := b) x ≠
      replacementPart (A := A) (a := a) (b := b) y := by
  cases x with
  | left x =>
      cases y with
      | left y => simp [ReplacementAdj] at hxy
      | right y => exact hab
      | tagged y e =>
          obtain ⟨z, -, hadj⟩ := hxy
          intro h
          exact A.part_ne_of_adj hadj (h.symm.trans z.property.symm)
  | right x =>
      cases y with
      | left y => exact hab.symm
      | right y => simp [ReplacementAdj] at hxy
      | tagged y e =>
          obtain ⟨z, -, hadj⟩ := hxy
          intro h
          exact A.part_ne_of_adj hadj (h.symm.trans z.property.symm)
  | tagged x e =>
      cases y with
      | left y =>
          obtain ⟨z, -, hadj⟩ := hxy
          intro h
          exact A.part_ne_of_adj hadj (h.trans z.property.symm)
      | right y =>
          obtain ⟨z, -, hadj⟩ := hxy
          intro h
          exact A.part_ne_of_adj hadj (h.trans z.property.symm)
      | tagged y f => exact A.part_ne_of_adj hxy.2

/-- The finite partite graph produced by the two-row replacement. -/
def replacement (hab : a ≠ b) [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel] : PartiteGraph n where
  V := ReplacementVertex A a b L R E
  fintypeV := Fintype.ofEquiv _ (replacementVertexEquiv A a b L R E).symm
  decEqV := inferInstance
  graph := D.replacementGraph
  decAdj := Classical.decRel _
  part := replacementPart (A := A) (a := a) (b := b)
  part_ne_of_adj := D.part_ne_of_replacementAdj hab

@[simp] theorem replacement_part_left (hab : a ≠ b)
    [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel] (x : L) :
    (D.replacement hab).part (.left x) = a := rfl

@[simp] theorem replacement_part_right (hab : a ≠ b)
    [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel] (x : R) :
    (D.replacement hab).part (.right x) = b := rfl

@[simp] theorem replacement_part_tagged (hab : a ≠ b)
    [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel]
    (x : Outside A a b) (e : E) :
    (D.replacement hab).part (.tagged x e) = A.part x.1 := rfl

theorem extend_injective (hab : a ≠ b) (e : E) : Function.Injective (D.extend e) := by
  intro x y hxy
  by_cases hxa : A.part x = a
  · by_cases hya : A.part y = a
    · simp only [extend_of_part_eq_left D e hxa, extend_of_part_eq_left D e hya,
        ReplacementVertex.left.injEq] at hxy
      exact Subtype.ext_iff.mp ((D.left e).injective hxy)
    · by_cases hyb : A.part y = b
      · simp [extend, hxa, hya, hyb, hab.symm] at hxy
      · simp [extend, hxa, hya, hyb] at hxy
  · by_cases hxb : A.part x = b
    · by_cases hya : A.part y = a
      · simp [extend, hxa, hxb, hya, hab.symm] at hxy
      · by_cases hyb : A.part y = b
        · simp only [extend_of_part_eq_right D hab e hxb,
            extend_of_part_eq_right D hab e hyb, ReplacementVertex.right.injEq] at hxy
          exact Subtype.ext_iff.mp ((D.right e).injective hxy)
        · simp [extend, hxa, hxb, hya, hyb, hab.symm] at hxy
    · by_cases hya : A.part y = a
      · simp [extend, hxa, hxb, hya] at hxy
      · by_cases hyb : A.part y = b
        · simp [extend, hxa, hxb, hya, hyb, hab.symm] at hxy
        · simp only [extend_of_part_ne D e hxa hxb, extend_of_part_ne D e hya hyb,
            ReplacementVertex.tagged.injEq] at hxy
          exact Subtype.ext_iff.mp hxy.1

theorem extend_part (hab : a ≠ b) [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel]
    (e : E) (x : A.V) : (D.replacement hab).part (D.extend e x) = A.part x := by
  by_cases hxa : A.part x = a
  · simp [hxa]
  · by_cases hxb : A.part x = b
    · simp [extend, hxa, hxb, hab.symm]
    · simp [extend, hxa, hxb]

theorem extend_adj_iff (hab : a ≠ b) (e : E) {x y : A.V} :
    D.replacementGraph.Adj (D.extend e x) (D.extend e y) ↔ A.graph.Adj x y := by
  change D.ReplacementAdj (D.extend e x) (D.extend e y) ↔ A.graph.Adj x y
  by_cases hxa : A.part x = a
  · have hxb : A.part x ≠ b := fun h ↦ hab (hxa.symm.trans h)
    by_cases hya : A.part y = a
    · have hsource : ¬A.graph.Adj x y := fun h ↦
        A.part_ne_of_adj h (hxa.trans hya.symm)
      simp [extend, hxa, hya, hsource, ReplacementAdj]
    · by_cases hyb : A.part y = b
      · simpa [extend, hxa, hxb, hya, hyb, hab.symm, ReplacementAdj] using
          D.induced e (⟨x, hxa⟩ : Row A a) (⟨y, hyb⟩ : Row A b)
      · simp [extend, hxa, hxb, hya, hyb, hab.symm, ReplacementAdj,
          SimpleGraph.adj_comm]
  · by_cases hxb : A.part x = b
    · by_cases hya : A.part y = a
      · have hyb : A.part y ≠ b := fun h ↦ hab (hya.symm.trans h)
        rw [SimpleGraph.adj_comm]
        simpa [extend, hxa, hxb, hya, hyb, hab.symm, ReplacementAdj] using
          D.induced e (⟨y, hya⟩ : Row A a) (⟨x, hxb⟩ : Row A b)
      · by_cases hyb : A.part y = b
        · have hsource : ¬A.graph.Adj x y := fun h ↦
            A.part_ne_of_adj h (hxb.trans hyb.symm)
          simp [extend, hxa, hxb, hya, hyb, hab.symm, hsource, ReplacementAdj]
        · simp [extend, hxa, hxb, hya, hyb, hab.symm, ReplacementAdj,
            SimpleGraph.adj_comm]
    · by_cases hya : A.part y = a
      · have hyb : A.part y ≠ b := fun h ↦ hab (hya.symm.trans h)
        simp [extend, hxa, hxb, hya, hyb, ReplacementAdj,
          SimpleGraph.adj_comm]
      · by_cases hyb : A.part y = b
        · simp [extend, hxa, hxb, hya, hyb, hab.symm, ReplacementAdj,
            SimpleGraph.adj_comm]
        · simp [extend, hxa, hxb, hya, hyb, ReplacementAdj]

/-- Each selected bipartite copy extends to an induced partite embedding of `A`. -/
def extensionEmbedding (hab : a ≠ b) [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel]
    (e : E) : PartiteEmbedding A (D.replacement hab) where
  toGraphEmbedding :=
    { toFun := D.extend e
      inj' := D.extend_injective hab e
      map_rel_iff' := D.extend_adj_iff hab e }
  map_part := D.extend_part hab e

/-- The precise input expected from the bipartite Ramsey construction. -/
def HasBipartiteRamseyProperty (q : ℕ) : Prop :=
  ∀ color : ∀ {x : L} {y : R}, D.rel x y → Fin q,
    ∃ e : E, ∃ gamma : Fin q, ∀ (x : Row A a) (y : Row A b)
      (hxy : A.graph.Adj x.1 y.1),
      color ((D.induced e x y).mpr hxy) = gamma

/-- A (possibly proof-dependent) coloring of oriented edges of the replacement. -/
abbrev ReplacementColoring (q : ℕ) :=
  ∀ {x y : ReplacementVertex A a b L R E}, D.replacementGraph.Adj x y → Fin q

/-- The bipartite Ramsey property chooses an extended copy in which every old
edge across the active row pair has one color. -/
theorem exists_extension_active_monochromatic (hab : a ≠ b) {q : ℕ}
    (hRamsey : D.HasBipartiteRamseyProperty q) (color : D.ReplacementColoring q) :
    ∃ e : E, ∃ gamma : Fin q, ∀ (x : Row A a) (y : Row A b)
      (hxy : A.graph.Adj x.1 y.1),
      color ((D.extend_adj_iff hab e).mpr hxy) = gamma := by
  let activeColor : ∀ {x : L} {y : R}, D.rel x y → Fin q :=
    fun {x y} hxy ↦ color (x := .left x) (y := .right y) hxy
  obtain ⟨e, gamma, hmono⟩ := hRamsey activeColor
  refine ⟨e, gamma, ?_⟩
  intro x y hxy
  simpa only [extend_of_part_eq_left D e x.property,
    extend_of_part_eq_right D hab e y.property] using hmono x y hxy

/-- A tagged vertex can only be adjacent to vertices in the copy bearing its tag. -/
theorem mem_range_extend_of_tagged_adj (hab : a ≠ b) (x : Outside A a b) (e : E) {y}
    (hxy : D.replacementGraph.Adj (.tagged x e) y) :
    ∃ z : A.V, D.extend e z = y := by
  cases y with
  | left y =>
      obtain ⟨z, hz, -⟩ := hxy
      exact ⟨z.1, by simp [extend, z.property, hz]⟩
  | right y =>
      obtain ⟨z, hz, -⟩ := hxy
      exact ⟨z.1, by simp [extend, z.property, hab.symm, hz]⟩
  | tagged y f =>
      obtain ⟨rfl, -⟩ := hxy
      exact ⟨y.1, by simp [extend, y.property]⟩

/-- A convenient copy-based formulation of clique containment. -/
def ContainsClique (G : PartiteGraph n) (m : ℕ) : Prop :=
  ∃ f : Fin m ↪ G.V, ∀ {i j}, i ≠ j → G.graph.Adj (f i) (f j)

theorem containsClique_of_isNClique {G : PartiteGraph n} {m : ℕ} {s : Finset G.V}
    (hs : G.graph.IsNClique m s) : ContainsClique G m := by
  let q : Fin m ≃ s := Fintype.equivOfCardEq (by simp [hs.card_eq])
  let f : Fin m ↪ G.V := q.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨f, ?_⟩
  intro i j hij
  exact hs.isClique (q i).property (q j).property
    (fun h ↦ hij (q.injective (Subtype.ext h)))

theorem isNClique_of_containsClique {G : PartiteGraph n} {m : ℕ}
    (h : ContainsClique G m) : ∃ s : Finset G.V, G.graph.IsNClique m s := by
  rcases h with ⟨f, hf⟩
  refine ⟨Finset.univ.map f, ?_⟩
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact hf (fun h ↦ hij (congrArg f h))
  · simp

def IsTagged (v : ReplacementVertex A a b L R E) : Prop :=
  ∃ x e, v = .tagged x e

theorem tagged_of_triangle {x y z : ReplacementVertex A a b L R E}
    (hxy : D.replacementGraph.Adj x y) (hxz : D.replacementGraph.Adj x z)
    (hyz : D.replacementGraph.Adj y z) :
    IsTagged x ∨ IsTagged y ∨ IsTagged z := by
  cases x <;> cases y <;> cases z <;>
    simp_all [IsTagged, replacementGraph, ReplacementAdj]

/-- Every clique of size at least three in the replacement is contained in a
single extended copy of `A`; hence it pulls back to a clique of `A`. -/
theorem containsClique_replacement_iff_forward (hab : a ≠ b)
    [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel]
    {m : ℕ} (hm : 3 ≤ m) :
    ContainsClique (D.replacement hab) m → ContainsClique A m := by
  rintro ⟨f, hf⟩
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have htag := D.tagged_of_triangle (hf h01) (hf h02) (hf h12)
  rcases htag with htag | htag | htag
  · rcases htag with ⟨x, e, heq⟩
    have hrange : ∀ i, ∃ y : A.V, D.extend e y = f i := by
      intro i
      by_cases hi : i = i0
      · subst i
        exact ⟨x.1, by simpa [extend, x.property] using heq.symm⟩
      · apply D.mem_range_extend_of_tagged_adj hab x e
        rw [← heq]
        exact hf (Ne.symm hi)
    choose g hg using hrange
    have g_inj : Function.Injective g := by
      intro i j hij
      apply f.injective
      rw [← hg i, ← hg j, hij]
    let ge : Fin m ↪ A.V := ⟨g, g_inj⟩
    refine ⟨ge, ?_⟩
    intro i j hij
    change A.graph.Adj (g i) (g j)
    rw [← D.extend_adj_iff hab e, hg i, hg j]
    exact hf hij
  · rcases htag with ⟨x, e, heq⟩
    have hrange : ∀ i, ∃ y : A.V, D.extend e y = f i := by
      intro i
      by_cases hi : i = i1
      · subst i
        exact ⟨x.1, by simpa [extend, x.property] using heq.symm⟩
      · apply D.mem_range_extend_of_tagged_adj hab x e
        rw [← heq]
        exact hf (Ne.symm hi)
    choose g hg using hrange
    have g_inj : Function.Injective g := by
      intro i j hij
      apply f.injective
      rw [← hg i, ← hg j, hij]
    let ge : Fin m ↪ A.V := ⟨g, g_inj⟩
    refine ⟨ge, ?_⟩
    intro i j hij
    change A.graph.Adj (g i) (g j)
    rw [← D.extend_adj_iff hab e, hg i, hg j]
    exact hf hij
  · rcases htag with ⟨x, e, heq⟩
    have hrange : ∀ i, ∃ y : A.V, D.extend e y = f i := by
      intro i
      by_cases hi : i = i2
      · subst i
        exact ⟨x.1, by simpa [extend, x.property] using heq.symm⟩
      · apply D.mem_range_extend_of_tagged_adj hab x e
        rw [← heq]
        exact hf (Ne.symm hi)
    choose g hg using hrange
    have g_inj : Function.Injective g := by
      intro i j hij
      apply f.injective
      rw [← hg i, ← hg j, hij]
    let ge : Fin m ↪ A.V := ⟨g, g_inj⟩
    refine ⟨ge, ?_⟩
    intro i j hij
    change A.graph.Adj (g i) (g j)
    rw [← D.extend_adj_iff hab e, hg i, hg j]
    exact hf hij

/-- Exact clique-freeness preservation in Mathlib's standard formulation. -/
theorem cliqueFree_replacement (hab : a ≠ b)
    [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E] [DecidableRel D.rel]
    {m : ℕ} (hm : 3 ≤ m) (hfree : A.graph.CliqueFree m) :
    (D.replacement hab).graph.CliqueFree m := by
  intro s hs
  have hcopyB : ContainsClique (D.replacement hab) m := containsClique_of_isNClique hs
  have hcopyA : ContainsClique A m := D.containsClique_replacement_iff_forward hab hm hcopyB
  obtain ⟨t, ht⟩ := isNClique_of_containsClique hcopyA
  exact hfree t ht

end TwoRowData

end PartiteGraph

/-- Every finite clique in `P` has at most `l` vertices. -/
def CliqueBound {n : ℕ} (P : PartiteGraph n) (l : ℕ) : Prop :=
  ∀ S : Finset P.V, P.graph.IsClique S → S.card ≤ l

theorem cliqueFree_of_cliqueBound {n l : ℕ} {P : PartiteGraph n}
    (hP : CliqueBound P l) : P.graph.CliqueFree (l + 1) := by
  intro S hS
  have hle := hP S hS.isClique
  rw [hS.card_eq] at hle
  omega

/-! ## The initial disjoint union of complete columns -/

/-- The type of `l`-element sets of rows. -/
abbrev Column (n l : ℕ) := {S : Finset (Fin n) // S.card = l}

/-- A vertex in the initial graph is a row belonging to a named column. -/
abbrev ColumnVertex (n l : ℕ) := Σ S : Column n l, {i : Fin n // i ∈ S.1}

/-- Adjacency inside one column of the initial graph. -/
def columnGraph (n l : ℕ) : SimpleGraph (ColumnVertex n l) where
  Adj x y := x.1 = y.1 ∧ x.2.1 ≠ y.2.1
  symm := ⟨by
    rintro x y ⟨hS, hij⟩
    exact ⟨hS.symm, fun h => hij h.symm⟩⟩
  loopless := ⟨by simp⟩

/-- The initial `n`-partite graph: one disjoint `K_l` for each `l`-set of
parts. -/
def columnPartiteGraph (n l : ℕ) : PartiteGraph n where
  V := ColumnVertex n l
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := columnGraph n l
  decAdj := inferInstance
  part := fun x => x.2.1
  part_ne_of_adj := fun h => h.2

@[simp] theorem columnPartiteGraph_part {n l : ℕ} (x : ColumnVertex n l) :
    (columnPartiteGraph n l).part x = x.2.1 := rfl

theorem columnPartiteGraph_cliqueBound (n l : ℕ) :
    CliqueBound (columnPartiteGraph n l) l := by
  intro T hT
  by_cases hT0 : T = ∅
  · simp [hT0]
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hT0
  let target : Type := {i : Fin n // i ∈ v.1.1}
  let f : (↑T : Type) → target := fun x =>
    ⟨x.1.2.1, by
      by_cases hxv : x.1 = v
      · simpa [hxv] using x.1.2.2
      · have hadj := hT x.2 hv hxv
        change x.1.1 = v.1 ∧ x.1.2.1 ≠ v.2.1 at hadj
        simpa [hadj.1] using x.1.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hadj := hT x.2 y.2 hne
    exact hadj.2 (congrArg Subtype.val hxy)
  have hcard := Fintype.card_le_of_injective f hf
  change T.card ≤ l
  simpa [target, v.1.2] using hcard

/-! ## The induced bipartite Ramsey lemma -/

/-- A bipartite relation, with distinct types for its two sides. -/
structure BipartiteRel (L R : Type*) where
  Rel : L → R → Prop

namespace BipartiteRel

variable {L R L' R' ι K : Type*}

/-- Ordered edges of a bipartite relation. -/
def Edge (G : BipartiteRel L R) := {p : L × R // G.Rel p.1 p.2}

instance [Finite L] [Finite R] (G : BipartiteRel L R) : Finite G.Edge :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- An edge labeling of a bipartite relation. -/
def EdgeLabeling (G : BipartiteRel L R) (K : Type*) := G.Edge → K

/-- The coordinatewise power of a bipartite relation. -/
def power (G : BipartiteRel L R) (ι : Type*) : BipartiteRel (ι → L) (ι → R) where
  Rel x y := ∀ i, G.Rel (x i) (y i)

/-- A part-preserving induced embedding of bipartite relations. -/
structure InducedEmbedding (G : BipartiteRel L R) (H : BipartiteRel L' R') where
  left : L ↪ L'
  right : R ↪ R'
  map_rel_iff' : ∀ l r, H.Rel (left l) (right r) ↔ G.Rel l r

namespace InducedEmbedding

/-- The induced map on bipartite edges. -/
def mapEdge {G : BipartiteRel L R} {H : BipartiteRel L' R'}
    (f : InducedEmbedding G H) (e : G.Edge) : H.Edge :=
  ⟨(f.left e.1.1, f.right e.1.2), (f.map_rel_iff' e.1.1 e.1.2).2 e.2⟩

end InducedEmbedding

/-- A labeling has a monochromatic induced part-preserving copy. -/
def HasMonochromaticInducedCopy (G : BipartiteRel L R) (H : BipartiteRel L' R')
    (C : H.EdgeLabeling K) : Prop :=
  ∃ f : InducedEmbedding G H, ∃ c : K, ∀ e : G.Edge, C (f.mapEdge e) = c

/-- A word of source edges is an edge in the coordinatewise power. -/
def wordEdge (G : BipartiteRel L R) (w : ι → G.Edge) : (G.power ι).Edge :=
  ⟨((fun i => (w i).1.1), fun i => (w i).1.2), fun i => (w i).2⟩

/-- The left map associated to a combinatorial line. -/
def lineLeft (G : BipartiteRel L R) (line : Combinatorics.Line G.Edge ι) (l : L) : ι → L :=
  fun i => (line.idxFun i).elim l (fun e => e.1.1)

/-- The right map associated to a combinatorial line. -/
def lineRight (G : BipartiteRel L R) (line : Combinatorics.Line G.Edge ι) (r : R) : ι → R :=
  fun i => (line.idxFun i).elim r (fun e => e.1.2)

private lemma lineLeft_injective (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) : Function.Injective (lineLeft G line) := by
  intro l₁ l₂ h
  obtain ⟨i, hi⟩ := line.proper
  have h' := congrFun h i
  simpa [lineLeft, hi] using h'

private lemma lineRight_injective (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) : Function.Injective (lineRight G line) := by
  intro r₁ r₂ h
  obtain ⟨i, hi⟩ := line.proper
  have h' := congrFun h i
  simpa [lineRight, hi] using h'

private lemma power_rel_line_iff (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) (l : L) (r : R) :
    (G.power ι).Rel (lineLeft G line l) (lineRight G line r) ↔ G.Rel l r := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := line.proper
    simpa [power, lineLeft, lineRight, hi] using h i
  · intro hlr i
    cases hi : line.idxFun i with
    | none => simpa [lineLeft, lineRight, hi] using hlr
    | some e => simpa [lineLeft, lineRight, hi] using e.2

/-- The induced embedding associated to a combinatorial line. -/
def lineInducedEmbedding (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) : InducedEmbedding G (G.power ι) where
  left := ⟨lineLeft G line, lineLeft_injective G line⟩
  right := ⟨lineRight G line, lineRight_injective G line⟩
  map_rel_iff' := power_rel_line_iff G line

private lemma lineLeft_edge (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) (e : G.Edge) :
    lineLeft G line e.1.1 = fun i => (line e i).1.1 := by
  funext i
  cases hi : line.idxFun i with
  | none => simp [lineLeft, Combinatorics.Line.toFun, hi]
  | some a => simp [lineLeft, Combinatorics.Line.toFun, hi]

private lemma lineRight_edge (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) (e : G.Edge) :
    lineRight G line e.1.2 = fun i => (line e i).1.2 := by
  funext i
  cases hi : line.idxFun i with
  | none => simp [lineRight, Combinatorics.Line.toFun, hi]
  | some a => simp [lineRight, Combinatorics.Line.toFun, hi]

private lemma lineInducedEmbedding_mapEdge_eq_wordEdge (G : BipartiteRel L R)
    (line : Combinatorics.Line G.Edge ι) (e : G.Edge) :
    (lineInducedEmbedding G line).mapEdge e = wordEdge G (line e) := by
  apply Subtype.ext
  apply Prod.ext
  · exact lineLeft_edge G line e
  · exact lineRight_edge G line e

/-- Product form of the finite induced bipartite Ramsey theorem. -/
theorem exists_product_host {L R : Type} [Fintype L] [Fintype R]
    (G : BipartiteRel L R) (k : ℕ) (hk : 0 < k) :
    ∃ (ι : Type) (_ : Fintype ι),
      ∀ C : (G.power ι).EdgeLabeling (Fin k),
        HasMonochromaticInducedCopy G (G.power ι) C := by
  by_cases hne : Nonempty G.Edge
  · letI : Nonempty G.Edge := hne
    obtain ⟨ι, instι, hHJ⟩ :=
      Combinatorics.Line.exists_mono_in_high_dimension G.Edge (Fin k)
    refine ⟨ι, instι, ?_⟩
    intro C
    let wordColor : (ι → G.Edge) → Fin k := fun w => C (wordEdge G w)
    obtain ⟨line, c, hc⟩ := hHJ wordColor
    refine ⟨lineInducedEmbedding G line, c, ?_⟩
    intro e
    rw [lineInducedEmbedding_mapEdge_eq_wordEdge]
    exact hc e
  · haveI : IsEmpty G.Edge := not_nonempty_iff.mp hne
    let fL : L ↪ (Unit → L) :=
      ⟨fun x _ => x, fun x y h => congrFun h ()⟩
    let fR : R ↪ (Unit → R) :=
      ⟨fun x _ => x, fun x y h => congrFun h ()⟩
    let f : InducedEmbedding G (G.power Unit) :=
      { left := fL
        right := fR
        map_rel_iff' := fun x y => ⟨fun h => h (), fun h _ => h⟩ }
    exact ⟨Unit, inferInstance, fun _ =>
      ⟨f, ⟨0, hk⟩, fun e => isEmptyElim e⟩⟩

end BipartiteRel

/-! ## A single Ramsey replacement step -/

/-- Replacing two distinct rows by the finite product host makes that row
pair monochromatic inside some induced partite copy of `A`, for every edge
coloring.  The implication recording clique-freeness preservation is
independent of whether the source is in fact clique-free, which is the form
needed when replacement steps are iterated. -/
theorem exists_twoRow_extensionStep
    {n k m : ℕ} (A : PartiteGraph n) {a b : Fin n}
    (hab : a ≠ b) (hk : 0 < k) (hm : 3 ≤ m) :
    ∃ Q : PartiteGraph n,
      (A.graph.CliqueFree m → Q.graph.CliqueFree m) ∧
      ∀ C : SimpleGraph.EdgeLabeling Q.graph (Fin k),
        ∃ f : PartiteEmbedding A Q, ∃ gamma : Fin k,
          ∀ (x : PartiteGraph.Row A a) (y : PartiteGraph.Row A b)
            (hxy : A.graph.Adj x.1 y.1),
            C.get (f x.1) (f y.1)
                (f.toGraphEmbedding.map_rel_iff.mpr hxy) = gamma := by
  let G : BipartiteRel (PartiteGraph.Row A a) (PartiteGraph.Row A b) :=
    ⟨fun x y ↦ A.graph.Adj x.1 y.1⟩
  obtain ⟨ι, instι, hhost⟩ := BipartiteRel.exists_product_host G k hk
  letI : Fintype ι := instι
  let H := G.power ι
  let E := {p : (PartiteGraph.Row A a ↪ (ι → PartiteGraph.Row A a)) ×
      (PartiteGraph.Row A b ↪ (ι → PartiteGraph.Row A b)) //
      ∀ x y, H.Rel (p.1 x) (p.2 y) ↔ G.Rel x y}
  letI : Fintype E := inferInstance
  let D : PartiteGraph.TwoRowData A a b
      (ι → PartiteGraph.Row A a) (ι → PartiteGraph.Row A b) E :=
    { rel := H.Rel
      left := fun e ↦ e.1.1
      right := fun e ↦ e.1.2
      induced := fun e x y ↦ by
        change H.Rel (e.1.1 x) (e.1.2 y) ↔ G.Rel x y
        exact e.2 x y }
  have hRamsey : D.HasBipartiteRamseyProperty k := by
    intro color
    let C : H.EdgeLabeling (Fin k) := fun e ↦ color e.2
    obtain ⟨f, gamma, hmono⟩ := hhost C
    let e : E := ⟨(f.left, f.right), f.map_rel_iff'⟩
    refine ⟨e, gamma, ?_⟩
    intro x y hxy
    let edge : G.Edge := ⟨(x, y), hxy⟩
    simpa [C, e, D, BipartiteRel.InducedEmbedding.mapEdge, edge] using hmono edge
  let Q := D.replacement hab
  refine ⟨Q, D.cliqueFree_replacement hab hm, ?_⟩
  intro C
  let color : D.ReplacementColoring k := fun {x y} hxy ↦ C.get x y hxy
  obtain ⟨e, gamma, hmono⟩ :=
    D.exists_extension_active_monochromatic hab hRamsey color
  refine ⟨D.extensionEmbedding hab e, gamma, ?_⟩
  intro x y hxy
  change C.get (D.extend e x.1) (D.extend e y.1) _ = gamma
  exact hmono x y hxy

/-- The preceding replacement step specialized to a source already known to
be clique-free. -/
theorem exists_twoRow_monochromatic_replacement
    {n k m : ℕ} (A : PartiteGraph n) {a b : Fin n}
    (hab : a ≠ b) (hk : 0 < k) (hm : 3 ≤ m)
    (hfree : A.graph.CliqueFree m) :
    ∃ Q : PartiteGraph n,
      Q.graph.CliqueFree m ∧
      ∀ C : SimpleGraph.EdgeLabeling Q.graph (Fin k),
        ∃ f : PartiteEmbedding A Q, ∃ gamma : Fin k,
          ∀ (x : PartiteGraph.Row A a) (y : PartiteGraph.Row A b)
            (hxy : A.graph.Adj x.1 y.1),
            C.get (f x.1) (f y.1)
                (f.toGraphEmbedding.map_rel_iff.mpr hxy) = gamma := by
  obtain ⟨Q, hfreeQ, hselect⟩ := exists_twoRow_extensionStep A hab hk hm
  exact ⟨Q, hfreeQ hfree, hselect⟩

/-! ## Finite iteration over all pairs of rows -/

/-- An ordered pair of distinct rows.  Ordered pairs make the active
orientation explicit; treating both orientations is harmless and keeps the
iteration interface simple. -/
abbrev RowPair (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

namespace RowPair

def left {n : ℕ} (p : RowPair n) : Fin n := p.1.1
def right {n : ℕ} (p : RowPair n) : Fin n := p.1.2

theorem left_ne_right {n : ℕ} (p : RowPair n) : p.left ≠ p.right := p.2

end RowPair

/-- All source edges between the two designated rows have one color after
transport along the indicated induced partite embedding. -/
def PairHomogeneous {n : ℕ} {A B : PartiteGraph n} {K : Type*}
    (p : RowPair n) (C : SimpleGraph.EdgeLabeling B.graph K)
    (f : PartiteEmbedding A B) : Prop :=
  ∃ c : K, ∀ (x : PartiteGraph.Row A p.left) (y : PartiteGraph.Row A p.right)
    (hxy : A.graph.Adj x.1 y.1),
    C.get (f x.1) (f y.1) ((f.toGraphEmbedding.map_rel_iff).2 hxy) = c

/-- Pulling a coloring back and then witnessing homogeneity is the same
calculation needed for the composite embedding. -/
theorem PairHomogeneous.comp_of_pullback
    {n : ℕ} {A B D : PartiteGraph n} {K : Type*} (p : RowPair n)
    (C : SimpleGraph.EdgeLabeling D.graph K)
    (f : PartiteEmbedding B D) (g : PartiteEmbedding A B)
    (h : PairHomogeneous p (C.pullback f.toGraphEmbedding) g) :
    PairHomogeneous p C (PartiteEmbedding.comp f g) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  intro x y hxy
  simpa only [PairHomogeneous, SimpleGraph.EdgeLabeling.get_pullback,
    PartiteEmbedding.comp_apply] using hc x y hxy

/-- Homogeneity on a copy of `B` restricts to every induced partite subcopy
of `B`. -/
theorem PairHomogeneous.comp_right
    {n : ℕ} {A B D : PartiteGraph n} {K : Type*} (p : RowPair n)
    (C : SimpleGraph.EdgeLabeling D.graph K)
    (f : PartiteEmbedding B D) (g : PartiteEmbedding A B)
    (h : PairHomogeneous p C f) :
    PairHomogeneous p C (PartiteEmbedding.comp f g) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  intro x y hxy
  let gx : PartiteGraph.Row B p.left :=
    ⟨g x.1, by simpa using (g.map_part x.1).trans x.2⟩
  let gy : PartiteGraph.Row B p.right :=
    ⟨g y.1, by simpa using (g.map_part y.1).trans y.2⟩
  have hgxy : B.graph.Adj gx.1 gy.1 := (g.toGraphEmbedding.map_rel_iff).2 hxy
  simpa only [PartiteEmbedding.comp_apply] using hc gx gy hgxy

/-- Abstract specification of one pair-focusing extension.  Its target is
fixed before seeing the coloring; every target coloring selects an induced
copy of the source homogeneous on `pair`.  The second field records exactly
the clique-freeness invariant required by the finite iteration. -/
structure ExtensionStep {n : ℕ} (A : PartiteGraph n) (pair : RowPair n)
    (k m : ℕ) where
  target : PartiteGraph n
  select : ∀ C : SimpleGraph.EdgeLabeling target.graph (Fin k),
    ∃ f : PartiteEmbedding A target, PairHomogeneous pair C f
  preservesCliqueFree : A.graph.CliqueFree m → target.graph.CliqueFree m

/-- A uniform choice of a focusing extension for every intermediate graph
and every ordered pair of rows. -/
abbrev ExtensionRule (n k m : ℕ) :=
  ∀ (A : PartiteGraph n) (pair : RowPair n), ExtensionStep A pair k m

/-- Successively apply the supplied focusing extensions. -/
def iterate {n k m : ℕ} (rule : ExtensionRule n k m) :
    (A : PartiteGraph n) → List (RowPair n) → PartiteGraph n
  | A, [] => A
  | A, pair :: pairs => iterate rule (rule A pair).target pairs

@[simp] theorem iterate_nil {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n) : iterate rule A [] = A := rfl

@[simp] theorem iterate_cons {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n) (pair : RowPair n) (pairs : List (RowPair n)) :
    iterate rule A (pair :: pairs) = iterate rule (rule A pair).target pairs := rfl

/-- Every clique-freeness invariant preserved by an individual step is
preserved by their finite iteration. -/
theorem iterate_cliqueFree {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n) (pairs : List (RowPair n))
    (hfree : A.graph.CliqueFree m) :
    (iterate rule A pairs).graph.CliqueFree m := by
  induction pairs generalizing A with
  | nil => exact hfree
  | cons pair pairs ih =>
      exact ih (rule A pair).target ((rule A pair).preservesCliqueFree hfree)

/-- Given a coloring of the final iterated host, pull it backwards through
the successively selected copies.  The resulting copy of the original graph
is homogeneous on every pair already processed. -/
theorem iterate_select {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n) (pairs : List (RowPair n))
    (C : SimpleGraph.EdgeLabeling (iterate rule A pairs).graph (Fin k)) :
    ∃ f : PartiteEmbedding A (iterate rule A pairs),
      ∀ pair ∈ pairs, PairHomogeneous pair C f := by
  induction pairs generalizing A with
  | nil =>
      exact ⟨PartiteEmbedding.refl A, by simp⟩
  | cons pair pairs ih =>
      change SimpleGraph.EdgeLabeling
        (iterate rule (rule A pair).target pairs).graph (Fin k) at C
      obtain ⟨f, hf⟩ := ih (rule A pair).target C
      let pulled : SimpleGraph.EdgeLabeling (rule A pair).target.graph (Fin k) :=
        C.pullback f.toGraphEmbedding
      obtain ⟨g, hg⟩ := (rule A pair).select pulled
      refine ⟨PartiteEmbedding.comp f g, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        exact PairHomogeneous.comp_of_pullback pair C f g hg
      · exact PairHomogeneous.comp_right q C f g (hf q hq)

/-- Canonical list containing every ordered pair of distinct rows. -/
def allRowPairs (n : ℕ) : List (RowPair n) :=
  (Finset.univ : Finset (RowPair n)).toList

@[simp] theorem mem_allRowPairs {n : ℕ} (p : RowPair n) : p ∈ allRowPairs n := by
  simp [allRowPairs]

/-- The final graph obtained by focusing every ordered pair of rows. -/
def finalHost {n k m : ℕ} (rule : ExtensionRule n k m) (A : PartiteGraph n) :
    PartiteGraph n :=
  iterate rule A (allRowPairs n)

/-- Every coloring of the final host contains a copy of the original graph
that is homogeneous on every ordered pair of distinct rows. -/
theorem finalHost_select {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n)
    (C : SimpleGraph.EdgeLabeling (finalHost rule A).graph (Fin k)) :
    ∃ f : PartiteEmbedding A (finalHost rule A),
      ∀ pair : RowPair n, PairHomogeneous pair C f := by
  obtain ⟨f, hf⟩ := iterate_select rule A (allRowPairs n) C
  exact ⟨f, fun pair => hf pair (mem_allRowPairs pair)⟩

/-- Clique-freeness is retained by the all-pairs host. -/
theorem finalHost_cliqueFree {n k m : ℕ} (rule : ExtensionRule n k m)
    (A : PartiteGraph n) (hfree : A.graph.CliqueFree m) :
    (finalHost rule A).graph.CliqueFree m :=
  iterate_cliqueFree rule A (allRowPairs n) hfree

/-- The concrete extension rule furnished by the Hales--Jewett product and
the tagged partite replacement. -/
noncomputable def twoRowExtensionRule (n k m : ℕ) (hk : 0 < k) (hm : 3 ≤ m) :
    ExtensionRule n k m := fun A pair => by
  let hex := exists_twoRow_extensionStep A pair.left_ne_right hk hm
  let Q : PartiteGraph n := Classical.choose hex
  have hQ := Classical.choose_spec hex
  exact
    { target := Q
      select := by
        intro C
        obtain ⟨f, gamma, hmono⟩ := hQ.2 C
        exact ⟨f, gamma, hmono⟩
      preservesCliqueFree := hQ.1 }

/-! ## Ramsey extraction from the all-pairs homogeneous copy -/

/-- A single color function on unordered row pairs describes the pullback of
the ambient edge coloring to the selected copy of the column graph. -/
def IsRowPairHomogeneous {n l k : ℕ} {Q : PartiteGraph n}
    (f : PartiteEmbedding (columnPartiteGraph n l) Q)
    (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
    (χ : Finset (Fin n) → Fin k) : Prop :=
  ∀ x y (hxy : (columnPartiteGraph n l).graph.Adj x y),
    (C.pullback f.toGraphEmbedding).get x y hxy =
      χ {(columnPartiteGraph n l).part x,
        (columnPartiteGraph n l).part y}

/-- The increasing orientation of a two-element set of rows. -/
def RowPair.ofTwoFinset {n : ℕ} (e : Finset (Fin n)) (he : e.card = 2) : RowPair n :=
  ⟨(e.orderEmbOfFin he 0, e.orderEmbOfFin he 1), by
    intro h
    have h01 : (0 : Fin 2) = 1 := (e.orderEmbOfFin he).injective h
    omega⟩

/-- The color of a two-element row set, read using its increasing
orientation.  Values away from two-element sets are irrelevant to the
subsequent hypergraph Ramsey theorem. -/
noncomputable def rowPairColor {n l k : ℕ} {Q : PartiteGraph n}
    (f : PartiteEmbedding (columnPartiteGraph n l) Q)
    (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
    (hk : 0 < k) (hall : ∀ p : RowPair n, PairHomogeneous p C f)
    (e : Finset (Fin n)) : Fin k :=
  if he : e.card = 2 then Classical.choose (hall (RowPair.ofTwoFinset e he))
  else ⟨0, hk⟩

/-- Ordered-pair homogeneity from the finite iteration descends to an
unordered row-pair coloring.  If an edge is oppositely oriented from the
increasing orientation, symmetry of `EdgeLabeling.get` supplies the same
color. -/
theorem exists_rowPairColor_of_pairHomogeneous
    {n l k : ℕ} {Q : PartiteGraph n}
    (f : PartiteEmbedding (columnPartiteGraph n l) Q)
    (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
    (hk : 0 < k) (hall : ∀ p : RowPair n, PairHomogeneous p C f) :
    ∃ χ : Finset (Fin n) → Fin k, IsRowPairHomogeneous f C χ := by
  refine ⟨rowPairColor f C hk hall, ?_⟩
  intro x y hxy
  let i : Fin n := (columnPartiteGraph n l).part x
  let j : Fin n := (columnPartiteGraph n l).part y
  have hij : i ≠ j := (columnPartiteGraph n l).part_ne_of_adj hxy
  let e : Finset (Fin n) := {i, j}
  have he : e.card = 2 := by simp [e, hij]
  let p : RowPair n := RowPair.ofTwoFinset e he
  have hleftmem : p.left ∈ e := by
    change e.orderEmbOfFin he 0 ∈ e
    exact e.orderEmbOfFin_mem he 0
  have hrightmem : p.right ∈ e := by
    change e.orderEmbOfFin he 1 ∈ e
    exact e.orderEmbOfFin_mem he 1
  have hleft : p.left = i ∨ p.left = j := by
    simpa [e] using hleftmem
  have hright : p.right = i ∨ p.right = j := by
    simpa [e] using hrightmem
  change (C.pullback f.toGraphEmbedding).get x y hxy =
    rowPairColor f C hk hall e
  rw [rowPairColor, dif_pos he]
  change (C.pullback f.toGraphEmbedding).get x y hxy =
    Classical.choose (hall p)
  have hc := Classical.choose_spec (hall p)
  rcases hleft with hli | hlj <;> rcases hright with hri | hrj
  · exact False.elim (p.left_ne_right (hli.trans hri.symm))
  · let xx : PartiteGraph.Row (columnPartiteGraph n l) p.left :=
      ⟨x, by simpa [i] using hli.symm⟩
    let yy : PartiteGraph.Row (columnPartiteGraph n l) p.right :=
      ⟨y, by simpa [j] using hrj.symm⟩
    exact hc xx yy hxy
  · let yy : PartiteGraph.Row (columnPartiteGraph n l) p.left :=
      ⟨y, by simpa [j] using hlj.symm⟩
    let xx : PartiteGraph.Row (columnPartiteGraph n l) p.right :=
      ⟨x, by simpa [i] using hri.symm⟩
    calc
      (C.pullback f.toGraphEmbedding).get x y hxy =
          (C.pullback f.toGraphEmbedding).get y x hxy.symm := by
        exact SimpleGraph.EdgeLabeling.get_comm y x hxy
      _ = Classical.choose (hall p) := hc yy xx hxy.symm
  · exact False.elim (p.left_ne_right (hlj.trans hrj.symm))

/-- A homogeneous set of `l` rows gives a monochromatic `l`-clique in the
images under a row-pair-homogeneous embedding. -/
theorem monochromatic_clique_of_rowPairHomogeneous
    {n l k : ℕ}
    (hRamsey : ∀ χ : Finset (Fin n) → Fin k,
      ∃ H : Finset (Fin n), H.card = l ∧ FinHomogeneous 2 χ H)
    (Q : PartiteGraph n)
    (f : PartiteEmbedding (columnPartiteGraph n l) Q)
    (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
    (χ : Finset (Fin n) → Fin k)
    (hhom : IsRowPairHomogeneous f C χ) :
    ∃ c : Fin k, ∃ T : Finset Q.V, (C.labelGraph c).IsNClique l T := by
  obtain ⟨H, hHcard, c, hc⟩ := hRamsey χ
  let S : Column n l := ⟨H, hHcard⟩
  let sourceVertex : (↑H : Type) → ColumnVertex n l := fun i ↦
    ⟨S, ⟨i.1, i.2⟩⟩
  have hsourceVertex_injective : Function.Injective sourceVertex := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun x : ColumnVertex n l ↦ x.2.1) hij
  let sourceEmbedding : (↑H : Type) ↪ ColumnVertex n l :=
    ⟨sourceVertex, hsourceVertex_injective⟩
  let targetEmbedding : (↑H : Type) ↪ Q.V :=
    sourceEmbedding.trans ⟨f, f.injective⟩
  let T : Finset Q.V := Finset.univ.map targetEmbedding
  refine ⟨c, T, ?_, ?_⟩
  · rw [SimpleGraph.isClique_iff]
    intro u hu v hv huv
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hv
    have hij : i.1 ≠ j.1 := by
      intro hijval
      have hijsub : i = j := Subtype.ext hijval
      exact huv (congrArg targetEmbedding hijsub)
    have hsourceAdj :
        (columnPartiteGraph n l).graph.Adj (sourceVertex i) (sourceVertex j) := by
      exact ⟨rfl, hij⟩
    have htargetAdj : Q.graph.Adj (targetEmbedding i) (targetEmbedding j) := by
      exact f.toGraphEmbedding.map_rel_iff.mpr hsourceAdj
    rw [SimpleGraph.EdgeLabeling.labelGraph_adj]
    refine ⟨htargetAdj, ?_⟩
    have hpaircard : ({i.1, j.1} : Finset (Fin n)).card = 2 := by
      simp [hij]
    have hpairsub : ({i.1, j.1} : Finset (Fin n)) ⊆ H := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact i.2
      · exact j.2
    have hpaircolor := hc {i.1, j.1} hpaircard hpairsub
    calc
      C.get (targetEmbedding i) (targetEmbedding j) htargetAdj =
          (C.pullback f.toGraphEmbedding.toRelHom).get
            (sourceVertex i) (sourceVertex j) hsourceAdj := rfl
      _ = χ {(columnPartiteGraph n l).part (sourceVertex i),
          (columnPartiteGraph n l).part (sourceVertex j)} :=
        hhom (sourceVertex i) (sourceVertex j) hsourceAdj
      _ = χ {i.1, j.1} := rfl
      _ = c := hpaircolor
  · simp [T, hHcard]

/-- Direct composition of the ordered-pair output of `finalHost_select` with
the unordered-pair Ramsey extraction. -/
theorem monochromatic_clique_of_pairHomogeneous
    {n l k : ℕ}
    (hRamsey : ∀ χ : Finset (Fin n) → Fin k,
      ∃ H : Finset (Fin n), H.card = l ∧ FinHomogeneous 2 χ H)
    (Q : PartiteGraph n)
    (f : PartiteEmbedding (columnPartiteGraph n l) Q)
    (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
    (hk : 0 < k) (hall : ∀ p : RowPair n, PairHomogeneous p C f) :
    ∃ c : Fin k, ∃ T : Finset Q.V, (C.labelGraph c).IsNClique l T := by
  obtain ⟨χ, hχ⟩ := exists_rowPairColor_of_pairHomogeneous f C hk hall
  exact monochromatic_clique_of_rowPairHomogeneous hRamsey Q f C χ hχ

/-- The final extraction, with the number of rows chosen by finite Ramsey.
Any partite-iteration theorem supplying `IsRowPairHomogeneous` at this row
count immediately yields the desired monochromatic clique. -/
theorem exists_row_count_for_final_extraction (k l : ℕ) :
    ∃ n, l ≤ n ∧
      ∀ (Q : PartiteGraph n)
        (f : PartiteEmbedding (columnPartiteGraph n l) Q)
        (C : SimpleGraph.EdgeLabeling Q.graph (Fin k))
        (χ : Finset (Fin n) → Fin k),
        IsRowPairHomogeneous f C χ →
          ∃ c : Fin k, ∃ T : Finset Q.V,
            (C.labelGraph c).IsNClique l T := by
  obtain ⟨n, hln, hn⟩ := finite_fin_ramsey k 2 l
  refine ⟨n, hln, ?_⟩
  intro Q f C χ hhom
  exact monochromatic_clique_of_rowPairHomogeneous hn Q f C χ hhom

/-! ## Resolution of Erdős Problem 924 -/

/-- The constructive content of the affirmative answer: a finite
`K_(l+1)`-free graph which is `k`-edge-Ramsey for `K_l`. -/
theorem exists_cliqueFree_edgeRamsey_graph (k l : ℕ) (hk : 2 ≤ k) (hl : 3 ≤ l) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  obtain ⟨n, hln, hRamsey⟩ := finite_fin_ramsey k 2 l
  have hkpos : 0 < k := by omega
  have hm : 3 ≤ l + 1 := by omega
  let A : PartiteGraph n := columnPartiteGraph n l
  let rule : ExtensionRule n k (l + 1) :=
    twoRowExtensionRule n k (l + 1) hkpos hm
  let Q : PartiteGraph n := finalHost rule A
  have hAfree : A.graph.CliqueFree (l + 1) := by
    apply cliqueFree_of_cliqueBound
    exact columnPartiteGraph_cliqueBound n l
  have hQfree : Q.graph.CliqueFree (l + 1) :=
    finalHost_cliqueFree rule A hAfree
  refine ⟨Q.V, Q.fintypeV, Q.graph, hQfree, ?_⟩
  intro C
  obtain ⟨f, hall⟩ := finalHost_select rule A C
  obtain ⟨χ, hχ⟩ :=
    exists_rowPairColor_of_pairHomogeneous f C hkpos hall
  obtain ⟨c, T, hT⟩ :=
    monochromatic_clique_of_rowPairHomogeneous hRamsey Q f C χ hχ
  exact ⟨c, T, hT⟩

/-- Erdős Problem 924 has an affirmative answer.  The detailed mathematical
construction and its correspondence with this formal proof are documented in
`tex/924.tex`. -/
theorem erdos_924 :
    ∀ k l : ℕ, 2 ≤ k → 3 ≤ l →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ k l hk hl
    exact exists_cliqueFree_edgeRamsey_graph k l hk hl
  · intro _
    trivial

end

end Erdos924

#print axioms Erdos924.erdos_924
