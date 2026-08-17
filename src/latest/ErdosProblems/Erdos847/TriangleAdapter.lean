/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos847.TriangleBase
import ErdosProblems.Erdos847.FiniteArch
import ErdosProblems.Erdos847.Iteration

/-!
# Adapter from the complete-graph triangle model to the RRS finite interfaces

This file packages `Erdos847TriangleBase` as an
`Erdos847Pictures.ThreeGraph`, then proves the precise Ramsey, fractional,
and linear properties consumed by the picture iteration.
-/

namespace Erdos847TriangleAdapter

open scoped BigOperators
open Erdos847Pictures Erdos847FiniteArch Erdos847Iteration
open Erdos847TriangleBase

/-- Vertices of the finite base are the edges of the complete graph on
`Fin N`. -/
abbrev Vertex (N : ℕ) := {e : ℕ × ℕ // e ∈ vertices N}

/-- The predicate defining a hyperedge on the finite vertex subtype. -/
def IsTriangleEdge {N : ℕ} (E : Finset (Vertex N)) : Prop :=
  ∃ a b c : Vertex N,
    IsHyperedge a.1 b.1 c.1 ∧ E = {a, b, c}

/-- The `3`-graph of graph triangles in the complete graph on `Fin N`. -/
noncomputable def triangleGraph (N : ℕ) : ThreeGraph (Vertex N) where
  edges := by
    classical
    exact (Finset.univ.powersetCard 3).filter IsTriangleEdge
  uniform := by
    classical
    intro E hE
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).2

/-- Exact edge membership in `triangleGraph`.  The cardinality conjunct is
kept explicit, so this correspondence does not need a separate proof that
`IsTriangle` itself forces its three arguments to be distinct. -/
@[simp] theorem mem_triangleGraph_edges {N : ℕ} {E : Finset (Vertex N)} :
    E ∈ (triangleGraph N).edges ↔ E.card = 3 ∧ IsTriangleEdge E := by
  classical
  change E ∈ (Finset.univ.powersetCard 3).filter IsTriangleEdge ↔ _
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, htri⟩
    exact ⟨hcard, htri⟩
  · rintro ⟨hcard, htri⟩
    exact ⟨⟨Finset.subset_univ E, hcard⟩, htri⟩

/-- A listed triangle of three distinct subtype vertices is an edge. -/
theorem triple_mem_triangleGraph {N : ℕ} {a b c : Vertex N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htri : IsHyperedge a.1 b.1 c.1) :
    ({a, b, c} : Finset (Vertex N)) ∈ (triangleGraph N).edges := by
  rw [mem_triangleGraph_edges]
  refine ⟨by simp [hab, hac, hbc], a, b, c, htri, rfl⟩

/-- Convert the concrete monochromatic-triangle statement into the abstract
`ThreeGraph.RamseyFor` interface. -/
theorem triangleGraph_ramseyFor_of {N r : ℕ}
    (hRamsey : ∀ color : Vertex N → Fin r,
      ∃ e₀ e₁ e₂ : Vertex N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂) :
    Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) := by
  classical
  intro color
  obtain ⟨e₀, e₁, e₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ := hRamsey color
  let E : Finset (Vertex N) := {e₀, e₁, e₂}
  have hE : E ∈ (triangleGraph N).edges := by
    exact triple_mem_triangleGraph h₀₁ h₀₂ h₁₂ htri
  refine ⟨⟨E, hE⟩, color e₀, ?_⟩
  intro v hv
  change v ∈ E at hv
  simp only [E, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · rfl
  · exact hc₀.symm
  · exact hc₁.symm.trans hc₀.symm

/-- A finite triangle base exists for every finite color set. -/
theorem exists_triangleGraph_ramseyFor (r : ℕ) :
    ∃ N : ℕ,
      Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) := by
  obtain ⟨N, hN⟩ := exists_monochromatic_hyperedge_on_vertices r
  exact ⟨N, triangleGraph_ramseyFor_of hN⟩

/-- Forget the finite-bound proofs on a set of base vertices. -/
def edgeVal {N : ℕ} (E : Finset (Vertex N)) : Finset (ℕ × ℕ) :=
  E.image Subtype.val

theorem edgeVal_injective {N : ℕ} : Function.Injective (@edgeVal N) := by
  classical
  intro E F hEF
  apply Finset.ext
  intro x
  have hmem := congrArg (fun S : Finset (ℕ × ℕ) ↦ x.1 ∈ S) hEF
  simpa [edgeVal] using hmem

theorem edgeVal_card {N : ℕ} (E : Finset (Vertex N)) :
    (edgeVal E).card = E.card := by
  classical
  exact Finset.card_image_of_injective E Subtype.val_injective

theorem edgeVal_isHyperedgeSet {N : ℕ} {E : Finset (Vertex N)}
    (hE : IsTriangleEdge E) : IsHyperedgeSet (edgeVal E) := by
  classical
  rcases hE with ⟨a, b, c, htri, rfl⟩
  refine ⟨a.1, b.1, c.1, htri, ?_⟩
  simp [edgeVal]

/-- The complete-graph triangle model is a linear `ThreeGraph`. -/
theorem triangleGraph_linear (N : ℕ) : (triangleGraph N).Linear := by
  classical
  intro E F htwo
  by_contra hEF
  have hvalNe : edgeVal E.1 ≠ edgeVal F.1 := by
    intro h
    exact hEF (Subtype.ext (edgeVal_injective h))
  have hElin : IsHyperedgeSet (edgeVal E.1) :=
    edgeVal_isHyperedgeSet (mem_triangleGraph_edges.mp E.2).2
  have hFlin : IsHyperedgeSet (edgeVal F.1) :=
    edgeVal_isHyperedgeSet (mem_triangleGraph_edges.mp F.2).2
  have hbase := hyperedgeSets_linear hElin hFlin hvalNe
  have hsub : edgeVal (E.1 ∩ F.1) ⊆ edgeVal E.1 ∩ edgeVal F.1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hv' := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_image.mpr ⟨v, hv'.1, rfl⟩,
      Finset.mem_image.mpr ⟨v, hv'.2, rfl⟩⟩
  have himage : 2 ≤ (edgeVal E.1 ∩ edgeVal F.1).card := by
    calc
      2 ≤ (E.1 ∩ F.1).card := htwo
      _ = (edgeVal (E.1 ∩ F.1)).card := (edgeVal_card _).symm
      _ ≤ (edgeVal E.1 ∩ edgeVal F.1).card := Finset.card_le_card hsub
  omega

/-- The max-cut half bound implies the cleared-denominator `1/3`
fractional property required by the finite RRS architecture. -/
theorem triangleGraph_natFractionalThird (N : ℕ) :
    NatFractionalThird (triangleGraph N).edges := by
  classical
  intro w
  let ambientWeight : (ℕ × ℕ) → ℕ := fun e ↦
    if he : e ∈ vertices N then w ⟨e, he⟩ else 0
  have hne : ∀ e ∈ vertices N, e.1 ≠ e.2 := by
    intro e he
    exact ne_of_lt (mem_vertices.mp he).1
  obtain ⟨cut, hcut⟩ := exists_weighted_cut (vertices N) ambientWeight hne
  let crossing : Finset (ℕ × ℕ) :=
    (vertices N).filter fun e ↦ cut e.1 ≠ cut e.2
  let I : Finset (Vertex N) :=
    Finset.univ.filter fun e ↦ cut e.1.1 ≠ cut e.1.2
  have htotal :
      (∑ e ∈ vertices N, ambientWeight e) = ∑ v : Vertex N, w v := by
    calc
      (∑ e ∈ vertices N, ambientWeight e) =
          ∑ v : Vertex N, ambientWeight v.1 := by
            exact Finset.sum_subtype (vertices N) (fun _ ↦ Iff.rfl) ambientWeight
      _ = ∑ v : Vertex N, w v := by
        apply Finset.sum_congr rfl
        intro v hv
        dsimp [ambientWeight]
        rw [if_pos v.2]
  have hselected :
      (∑ e ∈ crossing, ambientWeight e) = ∑ v ∈ I, w v := by
    apply Finset.sum_bij
      (fun e he ↦ (⟨e, (Finset.mem_filter.mp he).1⟩ : Vertex N))
    · intro e he
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp he).2
    · intro e₁ he₁ e₂ he₂ h
      exact congrArg Subtype.val h
    · intro v hv
      refine ⟨v.1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨v.2, (Finset.mem_filter.mp hv).2⟩
      · rfl
    · intro e he
      dsimp [ambientWeight]
      rw [dif_pos (Finset.mem_filter.mp he).1]
  refine ⟨I, ?_, ?_⟩
  · intro E hE hEI
    obtain ⟨hcard, a, b, c, htri, rfl⟩ := mem_triangleGraph_edges.mp hE
    have haI : a ∈ I := hEI (by simp)
    have hbI : b ∈ I := hEI (by simp)
    have hcI : c ∈ I := hEI (by simp)
    have haCross : cut a.1.1 ≠ cut a.1.2 := (Finset.mem_filter.mp haI).2
    have hbCross : cut b.1.1 ≠ cut b.1.2 := (Finset.mem_filter.mp hbI).2
    have hcCross : cut c.1.1 ≠ cut c.1.2 := (Finset.mem_filter.mp hcI).2
    rcases htri with ⟨i, j, k, hij, hjk, hset⟩
    have hcross : ∀ e ∈ ({a.1, b.1, c.1} : Set (ℕ × ℕ)),
        cut e.1 ≠ cut e.2 := by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact haCross
      · exact hbCross
      · exact hcCross
    have hIJ : cut i ≠ cut j := hcross (i, j) (by rw [hset]; simp)
    have hJK : cut j ≠ cut k := hcross (j, k) (by rw [hset]; simp)
    have hIK : cut i ≠ cut k := hcross (i, k) (by rw [hset]; simp)
    cases hi : cut i <;> cases hj : cut j <;> cases hk : cut k <;> simp_all
  · rw [← htotal, ← hselected]
    change 2 * (∑ e ∈ crossing, ambientWeight e) ≥
      ∑ e ∈ vertices N, ambientWeight e at hcut
    omega

/-- Inclusion of complete-graph edge vertices when the ambient order grows. -/
def vertexInclusion {N M : ℕ} (hNM : N ≤ M) : Vertex N → Vertex M := fun e ↦
  ⟨e.1, mem_vertices.mpr ⟨(mem_vertices.mp e.2).1,
    lt_of_lt_of_le (mem_vertices.mp e.2).2 hNM⟩⟩

theorem vertexInclusion_injective {N M : ℕ} (hNM : N ≤ M) :
    Function.Injective (vertexInclusion hNM) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : Vertex M ↦ x.1) h

/-- Concrete monochromatic triangles persist when extra complete-graph
vertices are added. -/
theorem monochromatic_hyperedge_mono {N M r : ℕ} (hNM : N ≤ M)
    (hRamsey : ∀ color : Vertex N → Fin r,
      ∃ e₀ e₁ e₂ : Vertex N,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂) :
    ∀ color : Vertex M → Fin r,
      ∃ e₀ e₁ e₂ : Vertex M,
        e₀ ≠ e₁ ∧ e₀ ≠ e₂ ∧ e₁ ≠ e₂ ∧
          IsHyperedge e₀.1 e₁.1 e₂.1 ∧
          color e₀ = color e₁ ∧ color e₁ = color e₂ := by
  intro color
  let inc := vertexInclusion hNM
  obtain ⟨e₀, e₁, e₂, h₀₁, h₀₂, h₁₂, htri, hc₀, hc₁⟩ :=
    hRamsey (fun e ↦ color (inc e))
  refine ⟨inc e₀, inc e₁, inc e₂, ?_, ?_, ?_, ?_, hc₀, hc₁⟩
  · exact (vertexInclusion_injective hNM).ne h₀₁
  · exact (vertexInclusion_injective hNM).ne h₀₂
  · exact (vertexInclusion_injective hNM).ne h₁₂
  · exact htri

/-- Bundled finite base, enlarged to have at least three complete-graph
vertices for the picture-zero fiber construction. -/
theorem exists_triangleBase_package (r : ℕ) :
    ∃ N : ℕ, 3 ≤ N ∧
      Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) ∧
      NatFractionalThird (triangleGraph N).edges ∧
      (triangleGraph N).Linear := by
  obtain ⟨N, hN⟩ := exists_monochromatic_hyperedge_on_vertices r
  let M := N + 3
  have hNM : N ≤ M := by simp [M]
  have hRamseyM := monochromatic_hyperedge_mono hNM hN
  refine ⟨M, by simp [M], triangleGraph_ramseyFor_of hRamseyM,
    triangleGraph_natFractionalThird M, triangleGraph_linear M⟩

/-- The positive-color-count form used by the RRS construction. -/
theorem all_positive_color_counts_have_triangleBase :
    ∀ r : ℕ, 0 < r → ∃ N : ℕ,
      Erdos847Iteration.ThreeGraph.RamseyFor (triangleGraph N) (Fin r) ∧
      NatFractionalThird (triangleGraph N).edges ∧
      (triangleGraph N).Linear := by
  intro r _
  obtain ⟨N, _, hR, hF, hL⟩ := exists_triangleBase_package r
  exact ⟨N, hR, hF, hL⟩

/-! ## A fiber-doubled initial picture -/

section DoubledPictureZero

variable {V : Type*} [DecidableEq V]
variable (G : ThreeGraph V)

/-- Two tagged copies of every point of picture zero. -/
abbrev DoubledZeroPoint := ZeroPoint G × Bool

/-- One extra coordinate records the Boolean tag. -/
abbrev DoubledZeroCoord := ZeroCoord G ⊕ Unit

def boolTag (b : Bool) : Alphabet := if b then 1 else 0

theorem boolTag_injective : Function.Injective boolTag := by
  intro a b h
  cases a <;> cases b <;> simp [boolTag] at h ⊢

def doubledZeroWord (p : DoubledZeroPoint G) : DoubledZeroCoord G → Alphabet
  | Sum.inl c => zeroWord G p.1 c
  | Sum.inr _ => boolTag p.2

noncomputable def doubledZeroProj (p : DoubledZeroPoint G) : V := zeroProj G p.1

theorem doubledZeroWord_injective : Function.Injective (doubledZeroWord G) := by
  intro p q hpq
  have hfirst : p.1 = q.1 := by
    apply zeroWord_injective G
    funext c
    exact congrFun hpq (Sum.inl c)
  have htag : p.2 = q.2 := by
    apply boolTag_injective
    exact congrFun hpq (Sum.inr ())
  exact Prod.ext hfirst htag

/-- The Boolean tag is constant along every doubled quasiline. -/
theorem doubled_quasiline_tag_constant
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    ∃ b : Bool, ∀ i, (l i).2 = b := by
  rcases hl.2 (Sum.inr ()) with hconst | hinj
  · refine ⟨(l 0).2, fun i ↦ ?_⟩
    apply boolTag_injective
    exact (hconst.choose_spec i).trans (hconst.choose_spec 0).symm
  · exfalso
    have htagInj : Function.Injective (fun i ↦ (l i).2) := by
      intro i j h
      apply hinj
      exact congrArg boolTag h
    exact (Fintype.not_injective_of_card_lt (fun i : Alphabet ↦ (l i).2) (by decide)) htagInj

/-- Forgetting the Boolean tag turns a doubled quasiline into a picture-zero
quasiline. -/
theorem doubled_quasiline_first
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    IsQuasiline (zeroWord G) (fun i ↦ (l i).1) := by
  obtain ⟨b, hb⟩ := doubled_quasiline_tag_constant G l hl
  refine ⟨?_, ?_⟩
  · intro i j h
    apply hl.1
    apply Prod.ext h
    exact (hb i).trans (hb j).symm
  · intro c
    simpa [doubledZeroWord] using hl.2 (Sum.inl c)

/-- A fixed-tag lift of a picture-zero line is a line in the doubled
picture. -/
theorem doubled_line_of_zero_line (l : Alphabet → ZeroPoint G) (b : Bool)
    (hl : IsCombinatorialLine (zeroWord G) l) :
    IsCombinatorialLine (doubledZeroWord G) (fun i ↦ (l i, b)) := by
  rcases hl with ⟨hinj, σ, hσ⟩
  refine ⟨fun i j h ↦ hinj (congrArg Prod.fst h), σ, ?_⟩
  intro c
  cases c with
  | inl c => simpa [doubledZeroWord] using hσ c
  | inr _ => exact Or.inl ⟨boolTag b, fun _ ↦ rfl⟩

theorem doubled_quasiline_is_line
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    IsCombinatorialLine (doubledZeroWord G) l := by
  obtain ⟨b, hb⟩ := doubled_quasiline_tag_constant G l hl
  obtain ⟨_, σ, hσ⟩ := zero_quasiline_is_line G (fun i ↦ (l i).1)
    (doubled_quasiline_first G l hl)
  refine ⟨hl.1, σ, ?_⟩
  intro c
  cases c with
  | inl c => simpa [doubledZeroWord] using hσ c
  | inr _ =>
      exact Or.inl ⟨boolTag b, fun i ↦ by simp [doubledZeroWord, hb i]⟩

theorem doubled_quasiline_maps_edge
    (l : Alphabet → DoubledZeroPoint G)
    (hl : IsQuasiline (doubledZeroWord G) l) :
    MapsOntoEdge G (doubledZeroProj G) l := by
  obtain ⟨e, he⟩ := zero_quasiline_maps_edge G (fun i ↦ (l i).1)
    (doubled_quasiline_first G l hl)
  refine ⟨e, ?_⟩
  change Set.range (fun i ↦ zeroProj G (l i).1) = (e.1 : Set V)
  exact he

/-- Picture zero with every point duplicated.  The extra tag coordinate
prevents a quasiline from mixing the two copies. -/
noncomputable def doubledPictureZero :
    Picture G (DoubledZeroPoint G) (DoubledZeroCoord G) where
  embed := doubledZeroWord G
  embed_injective := doubledZeroWord_injective G
  proj := doubledZeroProj G
  quasiline_is_line := doubled_quasiline_is_line G
  quasiline_maps_edge := doubled_quasiline_maps_edge G

/-- Fixed-tag copies still realize every base edge. -/
theorem doubledPictureZero_realizesEveryEdge :
    RealizesEveryEdge (doubledPictureZero G) := by
  intro e
  obtain ⟨l, hl, hrange⟩ := pictureZero_realizesEveryEdge G e
  refine ⟨fun a ↦ (l a, false), doubled_line_of_zero_line G l false hl, ?_⟩
  change Set.range (fun a ↦ zeroProj G (l a)) = (e.1 : Set V)
  change Set.range (fun a ↦ zeroProj G (l a)) = (e.1 : Set V) at hrange
  exact hrange

/-- Every fiber of the doubled picture is nontrivial as soon as the
corresponding base vertex lies in one base edge. -/
theorem doubledPictureZero_fiber_nontrivial
    (hincident : ∀ x : V, ∃ e : G.Edge, x ∈ e.1) (x : V) :
    Nontrivial (Erdos847Iteration.Fiber (doubledPictureZero G) x) := by
  obtain ⟨e, hxe⟩ := hincident x
  let vx : {v : V // v ∈ e.1} := ⟨x, hxe⟩
  obtain ⟨a, ha⟩ := (G.edgeEquiv e).surjective vx
  have hproj : doubledZeroProj G ((e, a), false) = x := by
    exact congrArg Subtype.val ha
  refine ⟨⟨((e, a), false), hproj⟩, ⟨((e, a), true), ?_⟩, ?_⟩
  · exact hproj
  · intro h
    have hp := congrArg Subtype.val h
    have hb := congrArg (fun p : DoubledZeroPoint G ↦ p.2) hp
    simp at hb

end DoubledPictureZero

/-! ## Incidence and doubled fibers for the triangle base -/

/-- When `N ≥ 3`, every complete-graph edge belongs to a graph triangle,
hence every vertex of `triangleGraph N` lies in a hyperedge. -/
theorem triangleGraph_vertex_incident {N : ℕ} (hN : 3 ≤ N) (x : Vertex N) :
    ∃ e : (triangleGraph N).Edge, x ∈ e.1 := by
  classical
  rcases x with ⟨⟨i, j⟩, hx⟩
  have hij : i < j := (mem_vertices.mp hx).1
  have hjN : j < N := (mem_vertices.mp hx).2
  by_cases hi0 : i = 0
  · subst i
    by_cases hj1 : j = 1
    · subst j
      let b : Vertex N := ⟨(0, 2), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      let c : Vertex N := ⟨(1, 2), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      have hxb : (⟨(0, 1), hx⟩ : Vertex N) ≠ b := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.2) h
        simp [b] at this
      have hxc : (⟨(0, 1), hx⟩ : Vertex N) ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [c] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [b, c] at this
      have htri : IsHyperedge (0, 1) b.1 c.1 := by
        refine ⟨0, 1, 2, by omega, by omega, ?_⟩
        ext e
        simp [b, c, or_comm]
      let E : Finset (Vertex N) := {⟨(0, 1), hx⟩, b, c}
      have hE : E ∈ (triangleGraph N).edges :=
        triple_mem_triangleGraph hxb hxc hbc htri
      exact ⟨⟨E, hE⟩, by simp [E]⟩
    · have h1j : 1 < j := by omega
      let b : Vertex N := ⟨(0, 1), mem_vertices.mpr ⟨by omega, by omega⟩⟩
      let c : Vertex N := ⟨(1, j), mem_vertices.mpr ⟨h1j, hjN⟩⟩
      have hxb : (⟨(0, j), hx⟩ : Vertex N) ≠ b := by
        intro h
        apply hj1
        exact congrArg (fun v : Vertex N ↦ v.1.2) h
      have hxc : (⟨(0, j), hx⟩ : Vertex N) ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [c] at this
      have hbc : b ≠ c := by
        intro h
        have := congrArg (fun v : Vertex N ↦ v.1.1) h
        simp [b, c] at this
      have htri : IsHyperedge (0, j) b.1 c.1 := by
        refine ⟨0, 1, j, by omega, h1j, ?_⟩
        ext e
        simp [b, c, or_comm, or_left_comm]
      let E : Finset (Vertex N) := {⟨(0, j), hx⟩, b, c}
      have hE : E ∈ (triangleGraph N).edges :=
        triple_mem_triangleGraph hxb hxc hbc htri
      exact ⟨⟨E, hE⟩, by simp [E]⟩
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let b : Vertex N := ⟨(0, i), mem_vertices.mpr ⟨hiPos, lt_trans hij hjN⟩⟩
    let c : Vertex N := ⟨(0, j), mem_vertices.mpr ⟨lt_trans hiPos hij, hjN⟩⟩
    have hxb : (⟨(i, j), hx⟩ : Vertex N) ≠ b := by
      intro h
      apply hi0
      exact congrArg (fun v : Vertex N ↦ v.1.1) h
    have hxc : (⟨(i, j), hx⟩ : Vertex N) ≠ c := by
      intro h
      apply hi0
      exact congrArg (fun v : Vertex N ↦ v.1.1) h
    have hbc : b ≠ c := by
      intro h
      have := congrArg (fun v : Vertex N ↦ v.1.2) h
      exact (ne_of_lt hij) this
    have htri : IsHyperedge (i, j) b.1 c.1 := by
      refine ⟨0, i, j, hiPos, hij, ?_⟩
      ext e
      simp [b, c, or_left_comm]
    let E : Finset (Vertex N) := {⟨(i, j), hx⟩, b, c}
    have hE : E ∈ (triangleGraph N).edges :=
      triple_mem_triangleGraph hxb hxc hbc htri
    exact ⟨⟨E, hE⟩, by simp [E]⟩

/-- Consequently every source fiber of the doubled initial triangle picture
is nontrivial for the bundled bases (`N ≥ 3`). -/
theorem doubledTrianglePicture_fiber_nontrivial {N : ℕ} (hN : 3 ≤ N)
    (x : Vertex N) :
    Nontrivial (Erdos847Iteration.Fiber
      (doubledPictureZero (triangleGraph N)) x) :=
  doubledPictureZero_fiber_nontrivial (triangleGraph N)
    (triangleGraph_vertex_incident hN) x

end Erdos847TriangleAdapter
