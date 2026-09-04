-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.External

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The subhypergraph passage: `E4_Reiher ⟹ ReiherExpansion`

The headline resolutions are assembled from the *carried* hypothesis
`ReiherExpansion` — every private-vertex expansion `J⁺` of a finite bipartite
graph `J` is obligatory.  The paper's literature input **E4** (Reiher) is the
single instance that the complete bipartite expansion `K_{n,n}⁺` is obligatory.
This file discharges the *subhypergraph passage* of `lem:obligatory-closure`
that upgrades E4 to `ReiherExpansion`: a `2`-colourable graph `J` embeds into
`K_{n,n}` (`n = |V(J)|`), so `J⁺` is a sub–triple-system of `K_{n,n}⁺`, and
obligatoriness passes to sub–triple-systems.  Consequently every headline result
depends only on the literature interfaces E1–E5, not on the strengthened
`ReiherExpansion`. -/

open Cardinal Classical

namespace Erdos1177

universe u

/-- `F` is a **sub–triple-system** of `G`: an injective vertex map sending every
edge of `F` to an edge of `G`. -/
def FTS.Sub (F G : FTS) : Prop :=
  ∃ g : F.V → G.V, Function.Injective g ∧ ∀ e ∈ F.edges, e.image g ∈ G.edges

/-- **Obligatoriness passes to sub–triple-systems.**  If `F` embeds into `G` as a
sub–triple-system and `G` is obligatory, then `F` is obligatory. -/
theorem obligatory_of_sub {F G : FTS} (h : F.Sub G) (hG : FTS.Obligatory.{u} G) :
    FTS.Obligatory.{u} F := by
  obtain ⟨g, hg, hge⟩ := h
  intro W H htri huc
  obtain ⟨f, hf, hfe⟩ := hG H htri huc
  refine ⟨f ∘ g, hf.comp hg, ?_⟩
  intro e he
  have hcoe : (f ∘ g) '' (↑e : Set F.V) = f '' (↑(e.image g) : Set G.V) := by
    rw [Finset.coe_image, Set.image_comp]
  rw [hcoe]
  exact hfe _ (hge e he)

/-
**Expansion is monotone under graph embeddings.**  An injective,
adjacency-preserving vertex map `φ : J → K` induces a sub–triple-system embedding
`J⁺ ↪ K⁺`.
-/
/-- An adjacency-preserving map sends `J`-edges to `K`-edges (as `Sym2` values). -/
theorem sym2map_mem_edgeFinset {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b))
    (e : Sym2 VJ) (he : e ∈ J.edgeFinset) : Sym2.map φ e ∈ K.edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at *
  induction e with
  | h a b => rw [SimpleGraph.mem_edgeSet] at *; exact hadj a b he

theorem graphExpansion_sub_of_embedding {VJ VK : Type} [Fintype VJ] [DecidableEq VJ]
    [Fintype VK] [DecidableEq VK] (J : SimpleGraph VJ) [DecidableRel J.Adj]
    (K : SimpleGraph VK) [DecidableRel K.Adj]
    (φ : VJ → VK) (hφ : Function.Injective φ)
    (hadj : ∀ a b, J.Adj a b → K.Adj (φ a) (φ b)) :
    (graphExpansion J).Sub (graphExpansion K) := by
  refine' ⟨ _, _, _ ⟩;
  exact fun x => x.elim ( fun x => Sum.inl ( φ x ) ) fun e => Sum.inr ⟨ Sym2.map φ e.1, by
    rcases e with ⟨ e, he ⟩ ; simp_all +decide [ SimpleGraph.mem_edgeFinset ] ;
    rcases e with ⟨ a, b ⟩ ; simp_all +decide [ SimpleGraph.mem_edgeSet ] ; ⟩;
  · intro x y hxy; cases x <;> cases y <;> simp_all +decide [ hφ.eq_iff ] ;
    · grind +locals;
    · rename_i x y;
      rcases x with ⟨ ⟨ a, b ⟩, hx ⟩ ; rcases y with ⟨ ⟨ c, d ⟩, hy ⟩ ; simp_all +decide [ Quot.lift_mk ];
      grind;
  · all_goals generalize_proofs at *;
    intro e he; rcases Finset.mem_image.mp he with ⟨ e', he', rfl ⟩ ; simp_all +decide only [Finset.image_insert, Sum.elim_inl, Finset.image_singleton, Sum.elim_inr] ;
    refine' Finset.mem_image.mpr ⟨ ⟨ Sym2.map φ ↑e',
      sym2map_mem_edgeFinset J K φ hadj e'.1 e'.2 ⟩, Finset.mem_attach _ _, _ ⟩
    generalize_proofs at *;
    rcases h : Quot.out ( Sym2.map φ e'.1 ) with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
    rcases h' : Quot.out ( e'.1 : Sym2 VJ ) with ⟨ a, b ⟩ ; simp_all +decide [ Sym2.eq_swap ] ;
    have hxy := Quot.out_eq (Sym2.map φ e'.1)
    have hab := Quot.out_eq (e'.1 : Sym2 VJ)
    rw [h] at hxy
    rw [h'] at hab
    rw [← hab] at hxy
    change s(x, y) = s(φ a, φ b) at hxy
    rcases Sym2.eq_iff.mp hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      simp [hx, hy, Finset.insert_comm]


/-- **A `2`-colourable graph embeds into a complete bipartite graph.**  If `J` is
`2`-colourable then there is an `n` and an injective adjacency-preserving map
`J → K_{n,n}`. -/
theorem colorable_two_embeds_completeBipartite {VJ : Type} [Fintype VJ] [DecidableEq VJ]
    (J : SimpleGraph VJ) [DecidableRel J.Adj] (hJ : J.Colorable 2) :
    ∃ (n : ℕ) (φ : VJ → (Fin n ⊕ Fin n)), Function.Injective φ ∧
      ∀ a b, J.Adj a b → (completeBipartiteGraph (Fin n) (Fin n)).Adj (φ a) (φ b) := by
  obtain ⟨C⟩ := hJ;
  refine' ⟨ Fintype.card VJ, fun v => if C v = 0 then Sum.inl ( Fintype.equivFin VJ v ) else Sum.inr ( Fintype.equivFin VJ v ), _, _ ⟩;
  · intro v w h; by_cases hv : C v = 0 <;> by_cases hw : C w = 0 <;> simp_all +decide ;
  · intro a b hab; have := C.valid hab; simp_all +decide ;
    grind

/-- **The subhypergraph passage** (`lem:obligatory-closure`): the literature input
E4 (Reiher's theorem that `K_{n,n}⁺` is obligatory) implies the strengthened
`ReiherExpansion` (every bipartite expansion `J⁺` is obligatory). -/
theorem reiherExpansion_of_E4 (hE4 : E4_Reiher.{u}) : ReiherExpansion.{u} := by
  intro VJ _ _ J _ hJ
  obtain ⟨n, φ, hφ, hadj⟩ := colorable_two_embeds_completeBipartite J hJ
  exact obligatory_of_sub
    (graphExpansion_sub_of_embedding J (completeBipartiteGraph (Fin n) (Fin n)) φ hφ hadj)
    (hE4 n)

/-- **`ReiherExpansion` is exactly the literature input E4.**  Combined with
`E4_Reiher_of_reiherExpansion`, this shows the carried hypothesis
`ReiherExpansion` is *equivalent* to Reiher's published Theorem 1.2. -/
theorem reiherExpansion_iff_E4 : ReiherExpansion.{u} ↔ E4_Reiher.{u} :=
  ⟨E4_Reiher_of_reiherExpansion, reiherExpansion_of_E4⟩

end Erdos1177
