/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fin.Embedding

/-!
# Induced Ramsey witnesses

This file records the graph-theoretic definitions used in the formalization of
Erdős Problem 565.  A coloring is defined only on the edges of the host graph.
Consequently, an induced monochromatic copy consists of a graph embedding (which
both preserves and reflects adjacency) whose image edges all receive one color.
-/

@[expose] public section

open SimpleGraph

namespace Erdos565

/-- A graph embedding is monochromatic for a two-coloring of the host edges. -/
def IsMonochromaticEmbedding {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) (coloring : H.EdgeLabeling (Fin 2))
    (color : Fin 2) (f : G ↪g H) : Prop :=
  ∀ e : G.edgeSet, coloring (f.mapEdgeSet e) = color

/-- A host-edge coloring contains a monochromatic induced copy of `G`. -/
def MonochromaticInducedCopy {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) (coloring : H.EdgeLabeling (Fin 2)) : Prop :=
  ∃ (color : Fin 2) (f : G ↪g H),
    IsMonochromaticEmbedding G H coloring color f

/-- The fixed host `H` witnesses the induced Ramsey property for `G`. -/
def IsInducedRamseyWitness {n m : ℕ} (G : SimpleGraph (Fin n))
    (H : SimpleGraph (Fin m)) : Prop :=
  ∀ coloring : H.EdgeLabeling (Fin 2), MonochromaticInducedCopy G H coloring

/-- There is an `m`-vertex host witnessing the induced Ramsey property for `G`. -/
def IsInducedRamseyOrder {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin m), IsInducedRamseyWitness G H

theorem isMonochromaticEmbedding_iff_pullback_eq {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {coloring : H.EdgeLabeling (Fin 2)} {color : Fin 2} {f : G ↪g H} :
    IsMonochromaticEmbedding G H coloring color f ↔
      coloring.pullback f.toHom = fun _ ↦ color := by
  constructor
  · intro h
    funext e
    exact h e
  · intro h e
    exact congrFun h e

theorem monochromaticInducedCopy_iff_pullback_eq {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {coloring : H.EdgeLabeling (Fin 2)} :
    MonochromaticInducedCopy G H coloring ↔
      ∃ (color : Fin 2) (f : G ↪g H),
        coloring.pullback f.toHom = fun _ ↦ color := by
  simp only [MonochromaticInducedCopy, isMonochromaticEmbedding_iff_pullback_eq]

/-- A monochromatic induced copy is, after forgetting the coloring, an induced copy. -/
theorem MonochromaticInducedCopy.isIndContained {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {coloring : H.EdgeLabeling (Fin 2)}
    (h : MonochromaticInducedCopy G H coloring) : G ⊴ H := by
  rcases h with ⟨_, f, _⟩
  exact f.isIndContained

/-- In particular, a monochromatic induced copy is an ordinary (not necessarily induced) copy. -/
theorem MonochromaticInducedCopy.isContained {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {coloring : H.EdgeLabeling (Fin 2)}
    (h : MonochromaticInducedCopy G H coloring) : G ⊑ H :=
  h.isIndContained.isContained

/-- A Ramsey host necessarily contains an induced copy of its target. -/
theorem IsInducedRamseyWitness.isIndContained {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (h : IsInducedRamseyWitness G H) : G ⊴ H :=
  (h default).isIndContained

/-- A Ramsey host also contains an ordinary copy of its target. -/
theorem IsInducedRamseyWitness.isContained {n m : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (h : IsInducedRamseyWitness G H) : G ⊑ H :=
  h.isIndContained.isContained

theorem edgeLabeling_pullback_comp {n m l : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {I : SimpleGraph (Fin l)} (coloring : I.EdgeLabeling (Fin 2))
    (f : H ↪g I) (g : G ↪g H) :
    coloring.pullback (f.comp g).toHom =
      (coloring.pullback f.toHom).pullback g.toHom := by
  funext e
  simp only [SimpleGraph.EdgeLabeling.pullback]
  apply congrArg coloring
  apply Subtype.ext
  simp [SimpleGraph.Hom.mapEdgeSet, Sym2.map_map]

/-- A monochromatic embedding remains monochromatic after embedding its host into a larger host. -/
theorem IsMonochromaticEmbedding.comp {n m l : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {I : SimpleGraph (Fin l)} {coloring : I.EdgeLabeling (Fin 2)}
    {color : Fin 2} {f : G ↪g H} (g : H ↪g I)
    (h : IsMonochromaticEmbedding G H (coloring.pullback g.toHom) color f) :
    IsMonochromaticEmbedding G I coloring color (g.comp f) := by
  rw [isMonochromaticEmbedding_iff_pullback_eq] at h ⊢
  rw [edgeLabeling_pullback_comp]
  exact h

/-- Pulling a coloring back along a host embedding detects a copy in the larger host. -/
theorem MonochromaticInducedCopy.comp {n m l : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {I : SimpleGraph (Fin l)} {coloring : I.EdgeLabeling (Fin 2)}
    (g : H ↪g I)
    (h : MonochromaticInducedCopy G H (coloring.pullback g.toHom)) :
    MonochromaticInducedCopy G I coloring := by
  rcases h with ⟨color, f, hf⟩
  exact ⟨color, g.comp f, hf.comp g⟩

/-- An induced Ramsey witness remains one after its host is embedded into a larger graph. -/
theorem IsInducedRamseyWitness.comp {n m l : ℕ}
    {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    {I : SimpleGraph (Fin l)} (g : H ↪g I)
    (h : IsInducedRamseyWitness G H) : IsInducedRamseyWitness G I := by
  intro coloring
  exact (h (coloring.pullback g.toHom)).comp g

/-- Once an order works, every larger order works (add isolated vertices to a mapped host). -/
theorem IsInducedRamseyOrder.mono {n m l : ℕ} {G : SimpleGraph (Fin n)}
    (h : IsInducedRamseyOrder G m) (hml : m ≤ l) : IsInducedRamseyOrder G l := by
  rcases h with ⟨H, hH⟩
  let f : Fin m ↪ Fin l := Fin.castLEEmb hml
  exact ⟨H.map f, hH.comp (SimpleGraph.Embedding.map f H)⟩

/-- A graph on a subsingleton vertex type has no edges, so it is its own Ramsey host. -/
theorem isInducedRamseyOrder_self_of_subsingleton {n : ℕ} [Subsingleton (Fin n)]
    (G : SimpleGraph (Fin n)) : IsInducedRamseyOrder G n := by
  have hG : G = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun v w hvw ↦ by
    have hvw' : v = w := Subsingleton.elim _ _
    subst w
    exact G.loopless.irrefl v hvw
  subst G
  refine ⟨⊥, fun _ ↦ ⟨0, SimpleGraph.Embedding.refl, ?_⟩⟩
  rintro ⟨e, he⟩
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at he

theorem isInducedRamseyOrder_zero (G : SimpleGraph (Fin 0)) :
    IsInducedRamseyOrder G 0 :=
  isInducedRamseyOrder_self_of_subsingleton G

theorem isInducedRamseyOrder_one (G : SimpleGraph (Fin 1)) :
    IsInducedRamseyOrder G 1 :=
  isInducedRamseyOrder_self_of_subsingleton G

end Erdos565
