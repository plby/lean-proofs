import Arxiv.Arxiv2411_18291.Decomposition
import Arxiv.Arxiv2411_18291.TypicalityDensity

/-!
# Extending a clique with one edge exempted

The reserve must extend a specified edge `e` to a clique whose other edges
are present. At each step, the possible new vertices form a common
neighborhood, with the old vertex set removed.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r k h : ℕ}

def IsPuncturedClique (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (U : Finset V) : Prop :=
  e.val ⊆ U ∧ ∀ f : Block V (r + 1), f.val ⊆ U → f ∈ G ∨ f = e

omit [Fintype V] [DecidableEq V] in
theorem isPuncturedClique_self (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    IsPuncturedClique G e e.val := by
  refine ⟨Subset.refl _, fun f hf => Or.inr (Subtype.ext ?_)⟩
  exact eq_of_subset_of_card_le hf (by rw [e.property, f.property])

omit [Fintype V] [DecidableEq V] in
theorem IsPuncturedClique.mono {G : Hypergraph V (r + 1)} {e : Block V (r + 1)}
    {U W : Finset V} (hU : IsPuncturedClique G e U) (hWU : W ⊆ U) (heW : e.val ⊆ W) :
    IsPuncturedClique G e W :=
  ⟨heW, fun f hf => hU.2 f (hf.trans hWU)⟩

theorem isPuncturedClique_iff (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (U : Block V k) :
    IsPuncturedClique G e U.val ↔ e.val ⊆ U.val ∧ (cliqueEdges (r + 1) U).erase e ⊆ G := by
  simp only [IsPuncturedClique, subset_iff, mem_erase, mem_cliqueEdges]
  constructor
  · rintro ⟨he, hU⟩
    exact ⟨he, fun f hf => (hU f hf.2).resolve_right hf.1⟩
  · rintro ⟨he, hU⟩
    refine ⟨he, fun f hf => ?_⟩
    by_cases hfe : f = e
    · exact Or.inr hfe
    · exact Or.inl (hU ⟨hfe, hf⟩)

open Classical in
def puncturedCliques (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) (k : ℕ) :
    Finset (Block V k) := univ.filter fun U => IsPuncturedClique G e U.val

omit [DecidableEq V] in
@[simp] theorem mem_puncturedCliques (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (U : Block V k) : U ∈ puncturedCliques G e k ↔ IsPuncturedClique G e U.val := by
  simp [puncturedCliques]

omit [DecidableEq V] in
theorem puncturedCliques_base (G : Hypergraph V (r + 1)) (e : Block V (r + 1)) :
    puncturedCliques G e (r + 1) = {e} := by
  ext U
  simp only [mem_puncturedCliques, mem_singleton]
  constructor
  · intro hU
    apply Subtype.ext
    exact (eq_of_subset_of_card_le hU.1 (by rw [U.property, e.property])).symm
  · rintro rfl
    exact isPuncturedClique_self G _

def cliqueNextVertices (G : Hypergraph V (r + 1)) (U : Block V k) : Finset V :=
  commonNeighbors G (cliqueEdges r U) \ U.val

@[simp] theorem mem_cliqueNextVertices (G : Hypergraph V (r + 1)) (U : Block V k) (v : V) :
    v ∈ cliqueNextVertices G U ↔
      v ∈ commonNeighbors G (cliqueEdges r U) ∧ v ∉ U.val := by
  simp [cliqueNextVertices]

/-- Exactly the new vertices preserving the punctured-clique property. -/
theorem IsPuncturedClique.insert_iff {G : Hypergraph V (r + 1)} {e : Block V (r + 1)}
    {U : Block V k} (hU : IsPuncturedClique G e U.val) {v : V} (hv : v ∉ U.val) :
    IsPuncturedClique G e (insert v U.val) ↔ v ∈ cliqueNextVertices G U := by
  rw [mem_cliqueNextVertices]
  constructor
  · intro hnew
    refine ⟨?_, hv⟩
    apply (mem_commonNeighbors _ _ _).mpr
    intro S hS
    have hSU := (mem_cliqueEdges S U).mp hS
    have hvS : v ∉ S.val := fun h => hv (hSU h)
    apply (mem_neighbors _ _ _).mpr
    refine ⟨hvS, ?_⟩
    have hf : (extendBlock S v hvS).val ⊆ insert v U.val := insert_subset_insert v hSU
    rcases hnew.2 (extendBlock S v hvS) hf with hG | he
    · exact hG
    · have hve : v ∈ e.val := by rw [← he]; exact mem_insert_self _ _
      exact (hv (hU.1 hve)).elim
  · rintro ⟨hcommon, _⟩
    refine ⟨hU.1.trans (subset_insert _ _), fun f hf => ?_⟩
    by_cases hvf : v ∈ f.val
    · let S : Block V r := ⟨f.val.erase v, by
        rw [card_erase_of_mem hvf, f.property]
        omega⟩
      have hSU : S.val ⊆ U.val := by
        intro x hx
        obtain ⟨hxv, hxf⟩ := mem_erase.mp hx
        rcases mem_insert.mp (hf hxf) with h | h
        · exact (hxv h).elim
        · exact h
      obtain ⟨hvS, he⟩ := (mem_neighbors _ _ _).mp
        ((mem_commonNeighbors _ _ _).mp hcommon S ((mem_cliqueEdges S U).mpr hSU))
      have hef : extendBlock S v hvS = f := Subtype.ext (insert_erase hvf)
      exact Or.inl (hef ▸ he)
    · apply hU.2 f
      intro x hx
      rcases mem_insert.mp (hf hx) with h | h
      · exact (hvf (h ▸ hx)).elim
      · exact h

/-- Typicality supplies a lower bound even when some common neighbors lie
in the old vertex set, including the zero-dimensional face case. -/
theorem IsTypical.cliqueNextVertices_lower {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (U : Block V k) (hkh : k.choose r ≤ h) :
    (1 - c) * (Fintype.card V * density G ^ k.choose r) - k ≤
      ((cliqueNextVertices G U).card : ℝ) := by
  have ht := hT (cliqueEdges r U) (by simpa only [card_cliqueEdges] using hkh)
  rw [card_cliqueEdges] at ht
  have hlo := (abs_le.mp ht).1
  have hc : ((commonNeighbors G (cliqueEdges r U)).card : ℝ) ≤
      (cliqueNextVertices G U).card + (k : ℝ) := by
    have hcard := card_le_card_sdiff_add_card
      (s := commonNeighbors G (cliqueEdges r U)) (t := U.val)
    rw [U.property] at hcard
    exact_mod_cast hcard
  nlinarith

theorem IsTypical.cliqueNextVertices_half {G : Hypergraph V (r + 1)} {c : ℝ}
    (hT : IsTypical G c h) (U : Block V k) (hkh : k.choose r ≤ h) (hc : c ≤ 1 / 4)
    (hsize : (k : ℝ) ≤ Fintype.card V * density G ^ k.choose r / 4) :
    (Fintype.card V : ℝ) / 2 * density G ^ k.choose r ≤
      ((cliqueNextVertices G U).card : ℝ) := by
  have hl := hT.cliqueNextVertices_lower U hkh
  have hp : 0 ≤ (Fintype.card V : ℝ) * density G ^ k.choose r :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (density_nonneg G) _)
  nlinarith [mul_le_mul_of_nonneg_right hc hp]

end Arxiv2411_18291
