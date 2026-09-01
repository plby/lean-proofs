/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 800.
https://www.erdosproblems.com/forum/thread/800

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos800.md
-/
/-
# Erdős Problem 800

Alon's theorem that a graph whose vertices of degree at least three form an
independent set has Ramsey number at most twelve times its order.

The proof follows N. Alon, *Subdivided graphs have linear Ramsey numbers*,
J. Graph Theory 18 (1994), 343--347.  One input in the paper is replaced by
the elementary `sparse_target_embedding` lemma below.
-/
import Mathlib

open Finset

namespace Erdos800

noncomputable section

universe u v

/-- The host graph contains an ordinary (not necessarily induced) copy of the target. -/
abbrev HasCopy {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β) : Prop := SimpleGraph.IsContained H G

/-- Every red/blue colouring of `K_N` has a monochromatic copy of `H`. -/
def RamseyFor {α : Type u} (H : SimpleGraph α) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), HasCopy H G ∨ HasCopy H Gᶜ

/-- The hypothesis in Problem 800: no edge has two endpoints of degree at least three. -/
def NoAdjacentHighDegree {α : Type u} [Fintype α]
    (H : SimpleGraph α) : Prop := by
  classical
  exact ∀ ⦃x y : α⦄, H.Adj x y → H.degree x < 3 ∨ H.degree y < 3

/-- A convenient pointwise formulation of “there is no independent triple”. -/
def NoIndependentTriple {α : Type u} (G : SimpleGraph α) : Prop :=
  ∀ ⦃a b c : α⦄, a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- The number of edges of a finite graph, packaged without exposing
decidability instances in theorem statements. -/
def edgeCount {α : Type u} [Fintype α] (G : SimpleGraph α) : ℕ :=
  Nat.card G.edgeSet

/-- A clique containing at least as many vertices as the target contains a copy
of the target. -/
lemma hasCopy_of_clique {α : Type u} {β : Type v}
    [Fintype α] (H : SimpleGraph α) (G : SimpleGraph β)
    {Q : Finset β} (hQ : G.IsClique Q) (hcard : Fintype.card α ≤ Q.card) :
    HasCopy H G := by
  classical
  let e : α ↪ Q := (Function.Embedding.nonempty_of_card_le (by simpa using hcard)).some
  refine ⟨{
    toHom := {
      toFun := fun x ↦ (e x : β)
      map_rel' := ?_
    }
    injective' := fun x y hxy ↦ e.injective (Subtype.ext hxy)
  }⟩
  exact fun {x y} hxy ↦ hQ (e x).property (e y).property
    (fun h ↦ H.ne_of_adj hxy (e.injective (Subtype.ext h)))

/-- The finite set of vertices other than `z` which are not adjacent to `z`. -/
def nonneighbors {β : Type v} [Fintype β] (G : SimpleGraph β) (z : β) : Finset β := by
  classical
  exact (univ.erase z).filter fun x ↦ ¬ G.Adj z x

/-- The non-neighbours of one vertex form a clique when there is no independent
triple.  The centre itself is erased so that the three vertices really are
distinct. -/
lemma nonneighbors_clique {β : Type v} [Fintype β]
    (G : SimpleGraph β) (hG : NoIndependentTriple G) (z : β) :
    G.IsClique (nonneighbors G z) := by
  classical
  intro x hx y hy hxy
  have hx' : x ∈ nonneighbors G z := hx
  have hy' : y ∈ nonneighbors G z := hy
  simp only [nonneighbors, mem_filter, mem_erase, mem_univ, and_true] at hx' hy'
  rcases hx' with ⟨hxz, hzx⟩
  rcases hy' with ⟨hyz, hzy⟩
  rcases hG hxz.symm hyz.symm hxy with hzx' | hzy' | hxy'
  · exact (hzx hzx').elim
  · exact (hzy hzy').elim
  · exact hxy'

/-- In a host with no independent triple, if the target is absent then every
non-neighbourhood has fewer vertices than the target. -/
lemma card_nonneighbors_lt {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (H : SimpleGraph α) (G : SimpleGraph β)
    (hG : NoIndependentTriple G) (hno : ¬ HasCopy H G) (z : β) :
    (nonneighbors G z).card < Fintype.card α := by
  by_contra h
  have hle : Fintype.card α ≤
      (nonneighbors G z).card := Nat.le_of_not_gt h
  exact hno (hasCopy_of_clique H G (nonneighbors_clique G hG z) hle)

/-- A coarse form of the Sidorenko--Goddard--Kleitman size Ramsey lemma,
sufficient for Alon's argument.  A graph with no independent triple and at
least `2 * e(H) + v(H)` vertices contains `H`. -/
theorem sparse_target_embedding {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (H : SimpleGraph α) (G : SimpleGraph β)
    (hG : NoIndependentTriple G)
    (hcard : 2 * edgeCount H + Fintype.card α ≤ Fintype.card β) :
    HasCopy H G := by
  classical
  induction p : Fintype.card α using Nat.strong_induction_on generalizing α with
  | h p ih =>
      cases isEmpty_or_nonempty α with
      | inl hα => exact SimpleGraph.IsContained.of_isEmpty
      | inr hα =>
          let _ := hα
          by_contra hno
          obtain ⟨v, hv⟩ := H.exists_minimal_degree_vertex
          let A : Type u := {x : α // x ≠ v}
          let H' : SimpleGraph A := H.induce {v}ᶜ
          have hpos : 0 < Fintype.card α := Fintype.card_pos
          have hAcard : Fintype.card A < Fintype.card α := by
            simpa [A] using hpos
          have hedges : edgeCount H' ≤ edgeCount H := by
            exact Finite.card_le_of_embedding (SimpleGraph.Copy.induce H {v}ᶜ).mapEdgeSet
          have hsmall :
              2 * edgeCount H' + Fintype.card A ≤ Fintype.card β := by
            have hAc : Fintype.card A ≤ Fintype.card α := Nat.le_of_lt hAcard
            omega
          obtain ⟨f⟩ := ih (Fintype.card A) (by rw [← p]; exact hAcard)
            H' hsmall rfl
          let used : Finset β := univ.image fun x : A ↦ f x
          let unused : Finset β := univ \ used
          have hused : used.card = Fintype.card A := by
            simp only [used]
            rw [card_image_of_injective]
            · simp
            · exact f.injective
          have hunused : 2 * edgeCount H < unused.card := by
            have hu : unused.card = Fintype.card β - Fintype.card A := by
              rw [show unused = univ \ used by rfl, card_sdiff]
              simp [hused]
            rw [hu]
            have hAc : Fintype.card A + 1 = Fintype.card α := by
              simp [A]
              omega
            omega
          have hdegree : H.degree v * Fintype.card α ≤ 2 * edgeCount H := by
            calc
              H.degree v * Fintype.card α = ∑ x : α, H.degree v := by
                simp [Nat.mul_comm]
              _ ≤ ∑ x : α, H.degree x := by
                exact sum_le_sum fun x _ ↦ by
                  rw [← hv]
                  exact H.minDegree_le_degree x
              _ = 2 * edgeCount H := by
                rw [H.sum_degrees_eq_twice_card_edges, edgeCount,
                  Nat.card_eq_fintype_card]
                congr 1
                exact H.edgeFinset_card
          let bad : Finset β := H.neighborFinset v |>.biUnion fun x ↦
            if hx : x ≠ v then nonneighbors G (f ⟨x, hx⟩) else ∅
          have hbad : bad.card ≤ 2 * edgeCount H := by
            calc
              bad.card ≤ ∑ x ∈ H.neighborFinset v,
                  (if hx : x ≠ v then nonneighbors G (f ⟨x, hx⟩) else ∅).card := by
                exact card_biUnion_le
              _ ≤ ∑ _x ∈ H.neighborFinset v, (Fintype.card α - 1) := by
                apply sum_le_sum
                intro x hx
                have hxv : x ≠ v := (H.ne_of_adj (by simpa using hx)).symm
                simp only [dif_pos hxv]
                have hlt := card_nonneighbors_lt H G hG hno (f ⟨x, hxv⟩)
                omega
              _ = H.degree v * (Fintype.card α - 1) := by
                simp only [sum_const, SimpleGraph.card_neighborFinset_eq_degree,
                  Nat.nsmul_eq_mul]
              _ ≤ H.degree v * Fintype.card α :=
                Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ ≤ 2 * edgeCount H := hdegree
          have hcandidate : ∃ z ∈ unused, ∀ x : A, H.Adj v x → G.Adj z (f x) := by
            by_contra hn
            push Not at hn
            have hsub : unused ⊆ bad := by
              intro z hz
              obtain ⟨x, hvx, hzx⟩ := hn z hz
              have hxv : (x : α) ≠ v := x.property
              have hzused : z ∉ used := (mem_sdiff.mp hz).2
              have hzne : z ≠ f x := by
                intro heq
                apply hzused
                exact mem_image.mpr ⟨x, mem_univ _, heq.symm⟩
              apply mem_biUnion.mpr
              refine ⟨(x : α), ?_, ?_⟩
              · simpa using hvx
              · simp only [dif_pos hxv, nonneighbors, mem_filter, mem_erase, mem_univ,
                  and_true]
                exact ⟨hzne, fun h ↦ hzx h.symm⟩
            have := card_le_card hsub
            omega
          obtain ⟨z, hzunused, hz⟩ := hcandidate
          let g : α → β := fun x ↦ if hx : x = v then z else f ⟨x, hx⟩
          have hginj : Function.Injective g := by
            intro x y hxy
            by_cases hx : x = v <;> by_cases hy : y = v
            · exact hx.trans hy.symm
            · subst x
              simp only [g, dite_true, hy, dite_false] at hxy
              exfalso
              exact (mem_sdiff.mp hzunused).2
                (mem_image.mpr ⟨⟨y, hy⟩, mem_univ _, hxy.symm⟩)
            · subst y
              simp only [g, hx, dite_false, dite_true] at hxy
              exfalso
              exact (mem_sdiff.mp hzunused).2
                (mem_image.mpr ⟨⟨x, hx⟩, mem_univ _, hxy⟩)
            · simp only [g, hx, dite_false, hy] at hxy
              have he : (⟨x, hx⟩ : A) = ⟨y, hy⟩ := f.injective hxy
              exact congrArg Subtype.val he
          apply hno
          refine ⟨{
            toHom := {
              toFun := g
              map_rel' := ?_
            }
            injective' := hginj
          }⟩
          intro x y hxy
          by_cases hx : x = v <;> by_cases hy : y = v
          · subst x
            subst y
            exact (H.irrefl hxy).elim
          · subst x
            simp only [g, dite_true, hy, dite_false]
            exact hz ⟨y, hy⟩ hxy
          · subst y
            simp only [g, hx, dite_false, dite_true]
            exact (hz ⟨x, hx⟩ hxy.symm).symm
          · simp only [g, hx, dite_false, hy]
            apply f.toHom.map_rel
            exact hxy

/-! ## The target decomposition -/

/-- Vertices of degree at least three. -/
def highVertices {α : Type u} [Fintype α] (H : SimpleGraph α) : Finset α := by
  classical
  exact univ.filter fun x ↦ 3 ≤ H.degree x

lemma highVertices_independent {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hH : NoAdjacentHighDegree H) : H.IsIndepSet (highVertices H) := by
  classical
  intro x hx y hy hxy hxy'
  have hxdeg : 3 ≤ H.degree x := by simpa [highVertices] using hx
  have hydeg : 3 ≤ H.degree y := by simpa [highVertices] using hy
  rcases hH hxy' with hxlt | hylt <;> omega

/-- Extend the high-degree vertices to a maximal independent set.  Maximality
implies that every outside vertex has a neighbour in it. -/
lemma exists_independent_core {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hH : NoAdjacentHighDegree H) :
    ∃ W : Finset α,
      highVertices H ⊆ W ∧ H.IsIndepSet W ∧
        ∀ x ∉ W, ∃ w ∈ W, H.Adj x w := by
  classical
  let C : Finset (Finset α) := univ.powerset.filter fun W ↦
    highVertices H ⊆ W ∧ H.IsIndepSet W
  have hC : C.Nonempty := by
    refine ⟨highVertices H, ?_⟩
    simp only [C, mem_filter, mem_powerset, subset_univ, true_and]
    exact ⟨Subset.rfl, highVertices_independent H hH⟩
  obtain ⟨W, hWmax⟩ := C.exists_maximalFor card hC
  have hWmem : W ∈ C := hWmax.1
  have hWprops : highVertices H ⊆ W ∧ H.IsIndepSet W := by
    simpa only [C, mem_filter, mem_powerset, mem_univ, subset_univ, true_and]
      using hWmem
  refine ⟨W, hWprops.1, hWprops.2, ?_⟩
  intro x hx
  by_contra hn
  push Not at hn
  have hind : H.IsIndepSet (↑(insert x W) : Set α) := by
    intro a ha b hb hab hab'
    simp only [coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hab rfl
    · exact hn b hb hab'
    · exact hn a ha hab'.symm
    · exact hWprops.2 ha hb hab hab'
  have hin : insert x W ∈ C := by
    simp only [C, mem_filter, mem_powerset, subset_univ, true_and]
    exact ⟨hWprops.1.trans (subset_insert _ _), hind⟩
  have hle : W.card ≤ (insert x W).card := by
    rw [card_insert_of_notMem hx]
    omega
  have hback := hWmax.2 hin hle
  rw [card_insert_of_notMem hx] at hback
  omega

/-- Neighbours of `x` which lie outside the core set. -/
def outsideNeighbors {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (x : α) : Finset α := by
  classical
  exact H.neighborFinset x \ W

/-- Every outside vertex has at most one outside neighbour. -/
lemma outsideNeighbors_card_le_one {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α)
    (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    {x : α} (hx : x ∉ W) : (outsideNeighbors H W x).card ≤ 1 := by
  classical
  have hxlow : H.degree x < 3 := by
    have hxnh : x ∉ highVertices H := fun h ↦ hx (hhigh h)
    simpa [highVertices] using hxnh
  obtain ⟨w, hwW, hxw⟩ := hdom x hx
  have hinter : 1 ≤ (H.neighborFinset x ∩ W).card := by
    apply card_pos.mpr
    exact ⟨w, mem_inter.mpr ⟨by simpa, hwW⟩⟩
  have hsplit := card_sdiff_add_card_inter (H.neighborFinset x) W
  change (H.neighborFinset x \ W).card ≤ 1
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hsplit
  omega

/-- The type of vertices outside a chosen core set. -/
abbrev Outside {α : Type u} (W : Finset α) := {x : α // x ∉ W}

/-- Number of vertices outside `W`, without exposing decidability instances. -/
def outsideCount {α : Type u} [Fintype α] (W : Finset α) : ℕ :=
  Nat.card (Outside W)

lemma outside_degree_le_two {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (hhigh : highVertices H ⊆ W)
    (x : Outside W) : (by classical exact H.degree x ≤ 2) := by
  classical
  have hxnh : (x : α) ∉ highVertices H := fun hx ↦ x.property (hhigh hx)
  have hxlt : H.degree x < 3 := by simpa [highVertices] using hxnh
  omega

/-- A fixed neighbour in `W` for each outside vertex. -/
def coreAnchor {α : Type u} [Fintype α] (H : SimpleGraph α) (W : Finset α)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (x : Outside W) : W :=
  ⟨(hdom x x.property).choose, (hdom x x.property).choose_spec.1⟩

lemma coreAnchor_adj {α : Type u} [Fintype α] (H : SimpleGraph α) (W : Finset α)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (x : Outside W) :
    H.Adj x (coreAnchor H W hdom x) :=
  (hdom x x.property).choose_spec.2

/-- Other core neighbours of `x`, after removing its fixed anchor. -/
def otherCoreNeighbors {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) : Finset W := by
  classical
  exact univ.filter fun w ↦ w ≠ coreAnchor H W hdom x ∧ H.Adj x w

lemma otherCoreNeighbors_card_le_one {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (x : Outside W) :
    (otherCoreNeighbors H W hdom x).card ≤ 1 := by
  classical
  rw [card_le_one]
  intro a ha b hb
  simp only [otherCoreNeighbors, mem_filter, mem_univ, true_and] at ha hb
  by_contra hab
  have ha0 : (a : α) ≠ coreAnchor H W hdom x := by
    exact fun he ↦ ha.1 (Subtype.ext he)
  have hb0 : (b : α) ≠ coreAnchor H W hdom x := by
    exact fun he ↦ hb.1 (Subtype.ext he)
  have habv : (a : α) ≠ b := fun he ↦ hab (Subtype.ext he)
  let T : Finset α :=
    {(a : α), (b : α), (coreAnchor H W hdom x : α)}
  have hTcard : T.card = 3 := by simp [T, ha0, hb0, habv]
  have hTsub : T ⊆ H.neighborFinset x := by
    intro y hy
    simp only [T, mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using ha.2
    · simpa using hb.2
    · simpa using coreAnchor_adj H W hdom x
  have hle := card_le_card hTsub
  rw [hTcard, SimpleGraph.card_neighborFinset_eq_degree] at hle
  exact (not_lt_of_ge (outside_degree_le_two H W hhigh x)) hle

/-- The possible second core neighbour, or the anchor again when none exists. -/
def secondAnchor {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) : W :=
  if h : (otherCoreNeighbors H W hdom x).Nonempty then h.choose
  else coreAnchor H W hdom x

lemma coreNeighbor_eq_anchor_or_second {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) (w : W) (hxw : H.Adj x w) :
    w = coreAnchor H W hdom x ∨ w = secondAnchor H W hdom x := by
  classical
  by_cases hw : w = coreAnchor H W hdom x
  · exact Or.inl hw
  · right
    have hwmem : w ∈ otherCoreNeighbors H W hdom x := by
      simp [otherCoreNeighbors, hw, hxw]
    have hne : (otherCoreNeighbors H W hdom x).Nonempty := ⟨w, hwmem⟩
    rw [secondAnchor, dif_pos hne]
    exact (card_le_one.mp (otherCoreNeighbors_card_le_one H W hhigh hdom x))
      w hwmem hne.choose hne.choose_spec

/-- The unique outside mate, with `x` itself used as a harmless default for a
singleton component. -/
def outsideMate {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (x : Outside W) : Outside W := by
  classical
  exact if h : (outsideNeighbors H W x).Nonempty then
      ⟨h.choose, (mem_sdiff.mp h.choose_spec).2⟩
    else x

lemma outsideMate_eq_of_adj {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α)
    (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x y : Outside W) (hxy : H.Adj x y) : outsideMate H W x = y := by
  classical
  have hymem : (y : α) ∈ outsideNeighbors H W x := by
    exact mem_sdiff.mpr ⟨by simpa, y.property⟩
  have hne : (outsideNeighbors H W x).Nonempty := ⟨y, hymem⟩
  rw [outsideMate, dif_pos hne]
  apply Subtype.ext
  exact (card_le_one.mp
    (outsideNeighbors_card_le_one H W hhigh hdom x.property))
      hne.choose hne.choose_spec y hymem

/-- The connector recording the (at most two) core neighbours of an outside
vertex.  A diagonal pair is harmless and is discarded by `fromEdgeSet`. -/
def innerConnector {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) : Sym2 W :=
  s(coreAnchor H W hdom x, secondAnchor H W hdom x)

/-- The connector recording the anchors at the two ends of an outside edge. -/
def crossConnector {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) : Sym2 W :=
  s(coreAnchor H W hdom x, coreAnchor H W hdom (outsideMate H W x))

/-- All connector pairs.  There are at most twice as many as outside vertices. -/
def connectorFinset {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) : Finset (Sym2 W) := by
  classical
  exact (univ.image (innerConnector H W hdom)) ∪
    (univ.image (crossConnector H W hdom))

/-- Alon's auxiliary target graph on the independent core. -/
def connectorGraph {α : Type u} [Fintype α] (H : SimpleGraph α)
    (W : Finset α) (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) : SimpleGraph W :=
  SimpleGraph.fromEdgeSet (connectorFinset H W hdom)

lemma connectorGraph_adj_inner {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (x : Outside W)
    (hne : coreAnchor H W hdom x ≠ secondAnchor H W hdom x) :
    (connectorGraph H W hdom).Adj
      (coreAnchor H W hdom x) (secondAnchor H W hdom x) := by
  classical
  rw [connectorGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hne⟩
  change s(coreAnchor H W hdom x, secondAnchor H W hdom x) ∈
    connectorFinset H W hdom
  apply mem_union.mpr
  left
  exact mem_image.mpr ⟨x, mem_univ _, rfl⟩

lemma connectorGraph_adj_cross {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α)
    (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (x y : Outside W)
    (hxy : H.Adj x y)
    (hne : coreAnchor H W hdom x ≠ coreAnchor H W hdom y) :
    (connectorGraph H W hdom).Adj
      (coreAnchor H W hdom x) (coreAnchor H W hdom y) := by
  classical
  rw [connectorGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hne⟩
  have hm : outsideMate H W x = y :=
    outsideMate_eq_of_adj H W hhigh hdom x y hxy
  change s(coreAnchor H W hdom x, coreAnchor H W hdom y) ∈
    connectorFinset H W hdom
  apply mem_union.mpr
  right
  apply mem_image.mpr
  refine ⟨x, mem_univ _, ?_⟩
  simp only [crossConnector, hm]

lemma edgeCount_connectorGraph_le {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) :
    edgeCount (connectorGraph H W hdom) ≤ 2 * outsideCount W := by
  classical
  have hsub : (connectorGraph H W hdom).edgeFinset ⊆ connectorFinset H W hdom := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset, connectorGraph,
      SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  have hconn := card_le_card hsub
  have hunion := card_union_le
    (univ.image (innerConnector H W hdom))
    (univ.image (crossConnector H W hdom))
  have hi := card_image_le (s := (univ : Finset (Outside W)))
    (f := innerConnector H W hdom)
  have hc := card_image_le (s := (univ : Finset (Outside W)))
    (f := crossConnector H W hdom)
  have hedge : edgeCount (connectorGraph H W hdom) =
      (connectorGraph H W hdom).edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card]
    exact (connectorGraph H W hdom).edgeFinset_card.symm
  rw [hedge]
  simp only [connectorFinset] at hconn
  simp only [card_univ] at hi hc
  have hout : Fintype.card (Outside W) = outsideCount W := by
    rw [outsideCount, Nat.card_eq_fintype_card]
  omega

lemma connectorGraph_adj_of_two_core_neighbors {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x : Outside W) (a b : W) (ha : H.Adj x a) (hb : H.Adj x b)
    (hab : a ≠ b) : (connectorGraph H W hdom).Adj a b := by
  rcases coreNeighbor_eq_anchor_or_second H W hhigh hdom x a ha with ha' | ha' <;>
    rcases coreNeighbor_eq_anchor_or_second H W hhigh hdom x b hb with hb' | hb'
  · exact (hab (ha'.trans hb'.symm)).elim
  · subst a
    subst b
    exact connectorGraph_adj_inner H W hdom x hab
  · subst a
    subst b
    exact (connectorGraph_adj_inner H W hdom x hab.symm).symm
  · exact (hab (ha'.trans hb'.symm)).elim

/-! ## The auxiliary graph in a dense colour class -/

/-- Common neighbours of two host vertices. -/
def commonNeighbors {β : Type v} [Fintype β]
    (G : SimpleGraph β) (a b : β) : Finset β := by
  classical
  exact G.neighborFinset a ∩ G.neighborFinset b

lemma mem_commonNeighbors {β : Type v} [Fintype β]
    (G : SimpleGraph β) (a b z : β) :
    z ∈ commonNeighbors G a b ↔ G.Adj a z ∧ G.Adj b z := by
  classical
  simp [commonNeighbors]

/-- Two vertices of `U` are adjacent when they have at least `2n` common
neighbours in the chosen colour. -/
def auxiliaryGraph {N : ℕ} (G : SimpleGraph (Fin N)) (n : ℕ)
    (U : Finset (Fin N)) : SimpleGraph U :=
  SimpleGraph.fromRel fun a b ↦ 2 * n ≤ (commonNeighbors G a b).card

lemma auxiliaryGraph_adj_iff {N n : ℕ} (G : SimpleGraph (Fin N))
    (U : Finset (Fin N)) (a b : U) :
    (auxiliaryGraph G n U).Adj a b ↔
      a ≠ b ∧ 2 * n ≤ (commonNeighbors G a b).card := by
  classical
  rw [auxiliaryGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hab | hba⟩
    · exact ⟨hne, hab⟩
    · exact ⟨hne, by simpa [commonNeighbors, inter_comm] using hba⟩
  · rintro ⟨hne, hab⟩
    exact ⟨hne, Or.inl hab⟩

/-- Six-`n` vertices of degree at least six-`n` produce an auxiliary graph
with no independent triple. -/
lemma auxiliary_noIndependentTriple {n : ℕ} (G : SimpleGraph (Fin (12 * n)))
    (U : Finset (Fin (12 * n)))
    (hdense : by classical exact ∀ u ∈ U, 6 * n ≤ G.degree u) :
    NoIndependentTriple (auxiliaryGraph G n U) := by
  classical
  let _ : DecidableEq (Fin (12 * n)) := Classical.decEq _
  let _ : DecidableRel G.Adj := Classical.decRel _
  intro a b c hab hac hbc
  by_contra hn
  push Not at hn
  rcases hn with ⟨hnab, hnac, hnbc⟩
  have hiab : (commonNeighbors G a b).card < 2 * n := by
    exact Nat.lt_of_not_ge fun h ↦
      hnab ((auxiliaryGraph_adj_iff G U a b).2 ⟨hab, h⟩)
  have hiac : (commonNeighbors G a c).card < 2 * n := by
    exact Nat.lt_of_not_ge fun h ↦
      hnac ((auxiliaryGraph_adj_iff G U a c).2 ⟨hac, h⟩)
  have hibc : (commonNeighbors G b c).card < 2 * n := by
    exact Nat.lt_of_not_ge fun h ↦
      hnbc ((auxiliaryGraph_adj_iff G U b c).2 ⟨hbc, h⟩)
  let A := G.neighborFinset (a : Fin (12 * n))
  let B := G.neighborFinset (b : Fin (12 * n))
  let C := G.neighborFinset (c : Fin (12 * n))
  have hA : 6 * n ≤ A.card := by
    simpa [A, SimpleGraph.card_neighborFinset_eq_degree] using hdense a a.property
  have hB : 6 * n ≤ B.card := by
    simpa [B, SimpleGraph.card_neighborFinset_eq_degree] using hdense b b.property
  have hC : 6 * n ≤ C.card := by
    simpa [C, SimpleGraph.card_neighborFinset_eq_degree] using hdense c c.property
  have hiAB : (A ∩ B).card < 2 * n := by simpa [A, B, commonNeighbors] using hiab
  have hiAC : (A ∩ C).card < 2 * n := by simpa [A, C, commonNeighbors] using hiac
  have hiBC : (B ∩ C).card < 2 * n := by simpa [B, C, commonNeighbors] using hibc
  have hABeq := card_union_add_card_inter A B
  have hABClimit : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [union_inter_distrib_right]
    exact card_union_le _ _
  have hABCeq := card_union_add_card_inter (A ∪ B) C
  have hABCupper : ((A ∪ B) ∪ C).card ≤ 12 * n := by
    calc
      ((A ∪ B) ∪ C).card ≤ (univ : Finset (Fin (12 * n))).card :=
        card_le_card (subset_univ _)
      _ = 12 * n := by simp
  omega

lemma coreNeighbor_eq_anchor_of_outside_adj {α : Type u} [Fintype α]
    (H : SimpleGraph α) (W : Finset α) (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (x y : Outside W) (hxy : H.Adj x y) (w : W) (hxw : H.Adj x w) :
    w = coreAnchor H W hdom x := by
  classical
  by_contra hw
  have haw : (coreAnchor H W hdom x : α) ≠ w :=
    fun h ↦ hw (Subtype.ext h.symm)
  have hay : (coreAnchor H W hdom x : α) ≠ y := by
    intro h
    exact y.property (h ▸ (coreAnchor H W hdom x).property)
  have hwy : (w : α) ≠ y := by
    intro h
    exact y.property (h ▸ w.property)
  let T : Finset α :=
    {(coreAnchor H W hdom x : α), (w : α), (y : α)}
  have hTcard : T.card = 3 := by simp [T, haw, hay, hwy]
  have hTsub : T ⊆ H.neighborFinset x := by
    intro z hz
    simp only [T, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simpa using coreAnchor_adj H W hdom x
    · simpa using hxw
    · simpa using hxy
  have hc := card_le_card hTsub
  rw [hTcard, SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact (not_lt_of_ge (outside_degree_le_two H W hhigh x)) hc

/-- If the complementary colour contains no target copy, every set of at
least target order contains an edge in the present colour. -/
lemma exists_edge_of_no_compl_copy {n N : ℕ} (H : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin N)) (hno : ¬ HasCopy H Gᶜ)
    (P : Finset (Fin N)) (hP : n ≤ P.card) :
    ∃ a ∈ P, ∃ b ∈ P, G.Adj a b := by
  classical
  by_contra hn
  push Not at hn
  apply hno
  apply hasCopy_of_clique H Gᶜ
  · intro a ha b hb hab
    simp only [SimpleGraph.compl_adj]
    exact ⟨hab, hn a ha b hb⟩
  · simpa using hP

/-- A partial ordinary embedding whose domain contains the core and is a union
of components of the graph induced outside the core. -/
structure PartialEmbedding {α : Type u} {β : Type v}
    [DecidableEq α] (H : SimpleGraph α) (G : SimpleGraph β)
    (W S : Finset α) (φ : W → β) where
  core_subset : W ⊆ S
  outside_closed : ∀ ⦃x⦄, x ∈ S → x ∉ W → ∀ ⦃y⦄, y ∉ W → H.Adj x y → y ∈ S
  toFun : α → β
  injOn : Set.InjOn toFun S
  map_adj : ∀ ⦃x y⦄, x ∈ S → y ∈ S → H.Adj x y → G.Adj (toFun x) (toFun y)
  agrees : ∀ w : W, toFun w = φ w

lemma initialPartialEmbedding {α : Type u} {β : Type v}
    [DecidableEq α] [Nonempty β]
    (H : SimpleGraph α) (G : SimpleGraph β) (W : Finset α)
    (hWind : H.IsIndepSet W) (φ : W → β) (hφ : Function.Injective φ) :
    Nonempty (PartialEmbedding H G W W φ) := by
  classical
  let f : α → β := fun x ↦ if hx : x ∈ W then φ ⟨x, hx⟩ else Classical.choice inferInstance
  refine ⟨{
    core_subset := Subset.rfl
    outside_closed := ?_
    toFun := f
    injOn := ?_
    map_adj := ?_
    agrees := ?_
  }⟩
  · intro x hx hxout
    exact (hxout hx).elim
  · intro x hx y hy hxy
    have hx' : x ∈ W := hx
    have hy' : y ∈ W := hy
    have hfx : f x = φ ⟨x, hx'⟩ := by simp [f, hx']
    have hfy : f y = φ ⟨y, hy'⟩ := by simp [f, hy']
    have hφxy : φ ⟨x, hx⟩ = φ ⟨y, hy⟩ := hfx.symm.trans (hxy.trans hfy)
    have he : (⟨x, hx⟩ : W) = ⟨y, hy⟩ := hφ hφxy
    exact congrArg Subtype.val he
  · intro x y hx hy hxy
    exact (hWind hx hy (H.ne_of_adj hxy) hxy).elim
  · intro w
    simp [f, w.property]

/-- The properties of the embedded connector graph that are used when the
outside components are inserted. -/
structure CorePlacement {α : Type u} [Fintype α] (H : SimpleGraph α)
    {n : ℕ} (G : SimpleGraph (Fin (12 * n))) (W : Finset α)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) (φ : W → Fin (12 * n)) : Prop where
  injective : Function.Injective φ
  dense : (by classical exact ∀ w : W, 6 * n ≤ G.degree (φ w))
  common : ∀ ⦃a b : W⦄, (connectorGraph H W hdom).Adj a b →
    2 * n ≤ (commonNeighbors G (φ a) (φ b)).card

/-- Host vertices which can receive `x` while respecting all already embedded
core neighbours. -/
def extensionPool {α : Type u} [Fintype α] (H : SimpleGraph α)
    {n : ℕ} (G : SimpleGraph (Fin (12 * n))) (W : Finset α)
    (φ : W → Fin (12 * n)) (x : α) : Finset (Fin (12 * n)) := by
  classical
  exact univ.filter fun z ↦ ∀ w : W, H.Adj x w → G.Adj z (φ w)

lemma extensionPool_card_ge {α : Type u} [Fintype α] (H : SimpleGraph α)
    {n : ℕ} (G : SimpleGraph (Fin (12 * n))) (W : Finset α)
    (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (φ : W → Fin (12 * n)) (hφ : CorePlacement H G W hdom φ)
    (x : Outside W) : 2 * n ≤ (extensionPool H G W φ x).card := by
  classical
  let a := coreAnchor H W hdom x
  let b := secondAnchor H W hdom x
  by_cases hab : a = b
  · have hsub : G.neighborFinset (φ a) ⊆ extensionPool H G W φ x := by
      intro z hz
      simp only [extensionPool, mem_filter, mem_univ, true_and]
      intro w hxw
      rcases coreNeighbor_eq_anchor_or_second H W hhigh hdom x w hxw with hw | hw
      · subst w
        simpa using (show G.Adj (φ a) z by simpa using hz).symm
      · rw [show w = b from hw, ← hab]
        simpa using (show G.Adj (φ a) z by simpa using hz).symm
    have hc := card_le_card hsub
    have hd := hφ.dense a
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  · have hsub : commonNeighbors G (φ a) (φ b) ⊆ extensionPool H G W φ x := by
      intro z hz
      have hz' := (mem_commonNeighbors G (φ a) (φ b) z).mp hz
      have hza : G.Adj z (φ a) := by
        exact hz'.1.symm
      have hzb : G.Adj z (φ b) := by
        exact hz'.2.symm
      simp only [extensionPool, mem_filter, mem_univ, true_and]
      intro w hxw
      rcases coreNeighbor_eq_anchor_or_second H W hhigh hdom x w hxw with hw | hw
      · simpa [a] using hw ▸ hza
      · simpa [b] using hw ▸ hzb
    have hc := card_le_card hsub
    have hcore : (connectorGraph H W hdom).Adj a b := by
      exact connectorGraph_adj_inner H W hdom x hab
    exact (hφ.common hcore).trans hc

lemma pair_extensionPool_card_ge {α : Type u} [Fintype α]
    (H : SimpleGraph α)
    {n : ℕ} (G : SimpleGraph (Fin (12 * n))) (W : Finset α)
    (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (φ : W → Fin (12 * n)) (hφ : CorePlacement H G W hdom φ)
    (x y : Outside W) (hxy : H.Adj x y) :
    2 * n ≤ ((extensionPool H G W φ x) ∩
      (extensionPool H G W φ y)).card := by
  classical
  let a := coreAnchor H W hdom x
  let b := coreAnchor H W hdom y
  by_cases hab : a = b
  · have hsub : G.neighborFinset (φ a) ⊆
        (extensionPool H G W φ x) ∩ (extensionPool H G W φ y) := by
      intro z hz
      have hza : G.Adj z (φ a) :=
        (show G.Adj (φ a) z by simpa using hz).symm
      apply mem_inter.mpr
      constructor
      · simp only [extensionPool, mem_filter, mem_univ, true_and]
        intro w hxw
        have hw := coreNeighbor_eq_anchor_of_outside_adj H W hhigh hdom x y hxy w hxw
        simpa [a] using hw ▸ hza
      · simp only [extensionPool, mem_filter, mem_univ, true_and]
        intro w hyw
        have hw := coreNeighbor_eq_anchor_of_outside_adj H W hhigh hdom y x hxy.symm w hyw
        rw [show w = b from hw, ← hab]
        exact hza
    have hc := card_le_card hsub
    have hd := hφ.dense a
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  · have hsub : commonNeighbors G (φ a) (φ b) ⊆
        (extensionPool H G W φ x) ∩ (extensionPool H G W φ y) := by
      intro z hz
      have hz' := (mem_commonNeighbors G (φ a) (φ b) z).mp hz
      have hza : G.Adj z (φ a) := hz'.1.symm
      have hzb : G.Adj z (φ b) := hz'.2.symm
      apply mem_inter.mpr
      constructor
      · simp only [extensionPool, mem_filter, mem_univ, true_and]
        intro w hxw
        have hw := coreNeighbor_eq_anchor_of_outside_adj H W hhigh hdom x y hxy w hxw
        simpa [a] using hw ▸ hza
      · simp only [extensionPool, mem_filter, mem_univ, true_and]
        intro w hyw
        have hw := coreNeighbor_eq_anchor_of_outside_adj H W hhigh hdom y x hxy.symm w hyw
        simpa [b] using hw ▸ hzb
    have hc := card_le_card hsub
    have hcore := connectorGraph_adj_cross H W hhigh hdom x y hxy hab
    exact (hφ.common hcore).trans hc

lemma outsideCount_add_card {α : Type u} [Fintype α] (W : Finset α) :
    outsideCount W + W.card = Fintype.card α := by
  classical
  have hc' : Fintype.card (Outside W) = Fintype.card α - W.card := by
    simp
  have hle : W.card ≤ Fintype.card α := Finset.card_le_univ W
  rw [outsideCount, Nat.card_eq_fintype_card, hc']
  omega

/-- Embed the connector graph in the common-neighbour auxiliary graph. -/
lemma exists_corePlacement {n : ℕ} (H : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin (12 * n)))
    (U : Finset (Fin (12 * n))) (hUcard : U.card = 6 * n)
    (hdense : by classical exact ∀ u ∈ U, 6 * n ≤ G.degree u)
    (W : Finset (Fin n))
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w) :
    ∃ φ : W → Fin (12 * n), CorePlacement H G W hdom φ := by
  classical
  let K := connectorGraph H W hdom
  let T := auxiliaryGraph G n U
  have htriple : NoIndependentTriple T := by
    exact auxiliary_noIndependentTriple G U hdense
  have hedge := edgeCount_connectorGraph_le H W hdom
  have hout := outsideCount_add_card W
  have hsmall : 2 * edgeCount K + Fintype.card W ≤ Fintype.card U := by
    have hWcard : Fintype.card W = W.card := Fintype.card_coe W
    have hU : Fintype.card U = 6 * n := by simpa using hUcard
    have hout' : outsideCount W + W.card = n := by simpa using hout
    have hedge' : edgeCount K ≤ 2 * outsideCount W := by simpa [K] using hedge
    rw [hWcard, hU]
    omega
  obtain ⟨e⟩ := sparse_target_embedding K T htriple hsmall
  let φ : W → Fin (12 * n) := fun w ↦ (e w : U)
  refine ⟨φ, {
    injective := ?_
    dense := ?_
    common := ?_
  }⟩
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · intro w
    exact hdense (e w) (e w).property
  · intro a b hab
    have he := e.toHom.map_rel hab
    exact (auxiliaryGraph_adj_iff G U (e a) (e b)).mp he |>.2

lemma extend_singleton {α : Type u} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) {n : ℕ} (G : SimpleGraph (Fin (12 * n)))
    (W S : Finset α) (φ : W → Fin (12 * n))
    (p : PartialEmbedding H G W S φ) (x : Outside W) (hxS : (x : α) ∉ S)
    (hsingle : ∀ y : Outside W, ¬ H.Adj x y)
    (z : Fin (12 * n)) (hzpool : z ∈ extensionPool H G W φ x)
    (hzunused : z ∉ S.image p.toFun) :
    Nonempty (PartialEmbedding H G W (insert (x : α) S) φ) := by
  classical
  let f : α → Fin (12 * n) := fun a ↦ if a = x then z else p.toFun a
  refine ⟨{
    core_subset := p.core_subset.trans (subset_insert _ _)
    outside_closed := ?_
    toFun := f
    injOn := ?_
    map_adj := ?_
    agrees := ?_
  }⟩
  · intro a ha haW b hbW hab
    simp only [mem_insert] at ha ⊢
    rcases ha with rfl | ha
    · exact (hsingle ⟨b, hbW⟩ hab).elim
    · exact Or.inr (p.outside_closed ha haW hbW hab)
  · intro a ha b hb hab
    simp only [coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have he : z = p.toFun b := by simpa [f, hbx] using hab
      exact (hzunused (mem_image.mpr ⟨b, hb, he.symm⟩)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have he : p.toFun a = z := by simpa [f, hax] using hab
      exact (hzunused (mem_image.mpr ⟨a, ha, he⟩)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      apply p.injOn ha hb
      simpa [f, hax, hbx] using hab
  · intro a b ha hb hab
    simp only [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (H.irrefl hab).elim
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      simp only [f, if_pos, if_neg hbx]
      by_cases hbW : b ∈ W
      · have hz := (by
          simpa only [extensionPool, mem_filter, mem_univ, true_and] using hzpool :
            ∀ w : W, H.Adj x w → G.Adj z (φ w))
        simpa [p.agrees ⟨b, hbW⟩] using hz ⟨b, hbW⟩ hab
      · exact (hsingle ⟨b, hbW⟩ hab).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      simp only [f, if_neg hax, if_pos]
      by_cases haW : a ∈ W
      · have hz := (by
          simpa only [extensionPool, mem_filter, mem_univ, true_and] using hzpool :
            ∀ w : W, H.Adj x w → G.Adj z (φ w))
        simpa [p.agrees ⟨a, haW⟩] using (hz ⟨a, haW⟩ hab.symm).symm
      · exact (hsingle ⟨a, haW⟩ hab.symm).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      simpa [f, hax, hbx] using p.map_adj ha hb hab
  · intro w
    have hwx : (w : α) ≠ x := fun h ↦ x.property (h ▸ w.property)
    simp [f, hwx, p.agrees]

lemma extend_pair {α : Type u} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α)
    {n : ℕ} (G : SimpleGraph (Fin (12 * n)))
    (W S : Finset α) (hhigh : highVertices H ⊆ W)
    (hdom : ∀ x ∉ W, ∃ w ∈ W, H.Adj x w)
    (φ : W → Fin (12 * n)) (p : PartialEmbedding H G W S φ)
    (x y : Outside W) (hxS : (x : α) ∉ S) (hyS : (y : α) ∉ S)
    (hxy : H.Adj x y)
    (z t : Fin (12 * n))
    (hzpool : z ∈ (extensionPool H G W φ x) ∩ (extensionPool H G W φ y))
    (htpool : t ∈ (extensionPool H G W φ x) ∩ (extensionPool H G W φ y))
    (hzunused : z ∉ S.image p.toFun) (htunused : t ∉ S.image p.toFun)
    (hzt : G.Adj z t) :
    Nonempty (PartialEmbedding H G W (insert (x : α) (insert (y : α) S)) φ) := by
  classical
  have hxyne : (x : α) ≠ y := H.ne_of_adj hxy
  have hzx : ∀ w : W, H.Adj x w → G.Adj z (φ w) := by
    simpa only [extensionPool, mem_filter, mem_univ, true_and]
      using (mem_inter.mp hzpool).1
  have hzy : ∀ w : W, H.Adj y w → G.Adj z (φ w) := by
    simpa only [extensionPool, mem_filter, mem_univ, true_and]
      using (mem_inter.mp hzpool).2
  have htx : ∀ w : W, H.Adj x w → G.Adj t (φ w) := by
    simpa only [extensionPool, mem_filter, mem_univ, true_and]
      using (mem_inter.mp htpool).1
  have hty : ∀ w : W, H.Adj y w → G.Adj t (φ w) := by
    simpa only [extensionPool, mem_filter, mem_univ, true_and]
      using (mem_inter.mp htpool).2
  let f : α → Fin (12 * n) := fun a ↦
    if a = x then z else if a = y then t else p.toFun a
  refine ⟨{
    core_subset := p.core_subset.trans
      ((subset_insert (y : α) S).trans (subset_insert (x : α) (insert (y : α) S)))
    outside_closed := ?_
    toFun := f
    injOn := ?_
    map_adj := ?_
    agrees := ?_
  }⟩
  · intro a ha haW b hbW hab
    simp only [mem_insert] at ha ⊢
    rcases ha with rfl | rfl | ha
    · have hm₁ := outsideMate_eq_of_adj H W hhigh hdom x y hxy
      have hm₂ := outsideMate_eq_of_adj H W hhigh hdom x ⟨b, hbW⟩ hab
      exact Or.inr (Or.inl (congrArg Subtype.val (hm₂.symm.trans hm₁)))
    · have hm₁ := outsideMate_eq_of_adj H W hhigh hdom y x hxy.symm
      have hm₂ := outsideMate_eq_of_adj H W hhigh hdom y ⟨b, hbW⟩ hab
      exact Or.inl (congrArg Subtype.val (hm₂.symm.trans hm₁))
    · exact Or.inr (Or.inr (p.outside_closed ha haW hbW hab))
  · intro a ha b hb hab
    simp only [coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
    · rfl
    · exfalso
      have : z = t := by simpa [f, hxyne, hxyne.symm] using hab
      exact hzt.ne this
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      have he : z = p.toFun b := by simpa [f, hbx, hby] using hab
      exact (hzunused (mem_image.mpr ⟨b, hb, he.symm⟩)).elim
    · exfalso
      have : t = z := by simpa [f, hxyne, hxyne.symm] using hab
      exact hzt.ne this.symm
    · rfl
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      have he : t = p.toFun b := by
        simpa [f, hxyne, hxyne.symm, hbx, hby] using hab
      exact (htunused (mem_image.mpr ⟨b, hb, he.symm⟩)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      have he : p.toFun a = z := by simpa [f, hax, hay] using hab
      exact (hzunused (mem_image.mpr ⟨a, ha, he⟩)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      have he : p.toFun a = t := by
        simpa [f, hxyne, hxyne.symm, hax, hay] using hab
      exact (htunused (mem_image.mpr ⟨a, ha, he⟩)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      apply p.injOn ha hb
      simpa [f, hax, hay, hbx, hby] using hab
  · intro a b ha hb hab
    simp only [mem_insert] at ha hb
    rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
    · exact (H.irrefl hab).elim
    · simpa [f, hxyne, hxyne.symm] using hzt
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      simp only [f, if_pos, if_neg hbx, if_neg hby]
      by_cases hbW : b ∈ W
      · simpa [p.agrees ⟨b, hbW⟩] using hzx ⟨b, hbW⟩ hab
      · exact (hxS (p.outside_closed hb hbW x.property hab.symm)).elim
    · simpa [f, hxyne, hxyne.symm] using hzt.symm
    · exact (H.irrefl hab).elim
    · have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      simp only [f, if_neg hxyne.symm, if_pos, if_neg hbx, if_neg hby]
      by_cases hbW : b ∈ W
      · simpa [p.agrees ⟨b, hbW⟩] using hty ⟨b, hbW⟩ hab
      · exact (hyS (p.outside_closed hb hbW y.property hab.symm)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      simp only [f, if_neg hax, if_neg hay, if_pos]
      by_cases haW : a ∈ W
      · simpa [p.agrees ⟨a, haW⟩] using (hzx ⟨a, haW⟩ hab.symm).symm
      · exact (hxS (p.outside_closed ha haW x.property hab)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      simp only [f, if_neg hax, if_neg hay, if_neg hxyne.symm, if_pos]
      by_cases haW : a ∈ W
      · simpa [p.agrees ⟨a, haW⟩] using (hty ⟨a, haW⟩ hab.symm).symm
      · exact (hyS (p.outside_closed ha haW y.property hab)).elim
    · have hax : a ≠ (x : α) := fun h ↦ hxS (h ▸ ha)
      have hay : a ≠ (y : α) := fun h ↦ hyS (h ▸ ha)
      have hbx : b ≠ (x : α) := fun h ↦ hxS (h ▸ hb)
      have hby : b ≠ (y : α) := fun h ↦ hyS (h ▸ hb)
      simpa [f, hax, hay, hbx, hby] using p.map_adj ha hb hab
  · intro w
    have hwx : (w : α) ≠ x := fun h ↦ x.property (h ▸ w.property)
    have hwy : (w : α) ≠ y := fun h ↦ y.property (h ▸ w.property)
    simp [f, hwx, hwy, p.agrees]

/-- Alon's embedding argument for one colour which is dense on `6n` host
vertices.  The alternative is a target copy in the complementary colour. -/
theorem oneColorRamsey {n : ℕ} (H : SimpleGraph (Fin n))
    (hH : NoAdjacentHighDegree H) (G : SimpleGraph (Fin (12 * n)))
    (U : Finset (Fin (12 * n))) (hUcard : U.card = 6 * n)
    (hdense : by classical exact ∀ u ∈ U, 6 * n ≤ G.degree u) :
    HasCopy H G ∨ HasCopy H Gᶜ := by
  classical
  by_cases hn : n = 0
  · subst n
    left
    exact SimpleGraph.IsContained.of_isEmpty
  let _ : Nonempty (Fin (12 * n)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨W, hhigh, hWind, hdom⟩ := exists_independent_core H hH
  obtain ⟨φ, hφ⟩ := exists_corePlacement H G U hUcard hdense W hdom
  by_cases hblue : HasCopy H Gᶜ
  · exact Or.inr hblue
  left
  let C : Finset (Finset (Fin n)) := univ.powerset.filter fun S ↦
    Nonempty (PartialEmbedding H G W S φ)
  have hC : C.Nonempty := by
    refine ⟨W, ?_⟩
    simp only [C, mem_filter, mem_powerset, subset_univ, true_and]
    exact initialPartialEmbedding H G W hWind φ hφ.injective
  obtain ⟨S, hSmax⟩ := C.exists_maximalFor card hC
  have hSmem : S ∈ C := hSmax.1
  obtain ⟨p⟩ : Nonempty (PartialEmbedding H G W S φ) := by
    simpa only [C, mem_filter, mem_powerset, mem_univ, subset_univ, true_and]
      using hSmem
  have hSuniv : S = univ := by
    by_contra hSne
    have hex : ∃ x : Fin n, x ∉ S := by
      by_contra hall
      push Not at hall
      exact hSne (eq_univ_of_forall hall)
    obtain ⟨x, hxS⟩ := hex
    have hxW : x ∉ W := fun hx ↦ hxS (p.core_subset hx)
    let xo : Outside W := ⟨x, hxW⟩
    let used : Finset (Fin (12 * n)) := S.image p.toFun
    have hused : used.card = S.card := by
      rw [show used = S.image p.toFun by rfl, card_image_iff]
      exact p.injOn
    have hSsize : S.card + 1 ≤ n := by
      have hc := card_le_card (subset_univ (insert x S))
      rw [card_insert_of_notMem hxS] at hc
      simpa using hc
    by_cases hmate : ∃ y : Outside W, H.Adj xo y
    · obtain ⟨yo, hxy⟩ := hmate
      have hxyne : x ≠ (yo : Fin n) := H.ne_of_adj hxy
      have hyS : (yo : Fin n) ∉ S := by
        intro hy
        exact hxS (p.outside_closed hy yo.property hxW hxy.symm)
      let P := (extensionPool H G W φ xo) ∩ (extensionPool H G W φ yo)
      have hP : 2 * n ≤ P.card := by
        exact pair_extensionPool_card_ge H G W hhigh hdom φ hφ xo yo hxy
      let A : Finset (Fin (12 * n)) := P \ used
      have hpairsize : S.card + 2 ≤ n := by
        have hxins : x ∉ insert (yo : Fin n) S := by simp [hxS, hxyne]
        have hc := card_le_card (subset_univ (insert x (insert (yo : Fin n) S)))
        rw [card_insert_of_notMem hxins, card_insert_of_notMem hyS] at hc
        simpa [Nat.add_assoc] using hc
      have hA : n ≤ A.card := by
        have hinter : (used ∩ P).card ≤ used.card := card_le_card inter_subset_left
        rw [show A = P \ used by rfl, card_sdiff]
        omega
      obtain ⟨z, hzA, t, htA, hzt⟩ :=
        exists_edge_of_no_compl_copy H G hblue A hA
      have hz := mem_sdiff.mp hzA
      have ht := mem_sdiff.mp htA
      have hnew := extend_pair H G W S hhigh hdom φ p xo yo hxS hyS hxy
        z t hz.1 ht.1 hz.2 ht.2 hzt
      have hnewmem : insert x (insert (yo : Fin n) S) ∈ C := by
        simp only [C, mem_filter, mem_powerset, subset_univ, true_and]
        exact hnew
      have hforward : S.card ≤ (insert x (insert (yo : Fin n) S)).card := by
        rw [card_insert_of_notMem (by simp [hxS, hxyne]), card_insert_of_notMem hyS]
        omega
      have hback := hSmax.2 hnewmem hforward
      rw [card_insert_of_notMem (by simp [hxS, hxyne]), card_insert_of_notMem hyS]
        at hback
      omega
    · push Not at hmate
      let P := extensionPool H G W φ xo
      have hP : 2 * n ≤ P.card := extensionPool_card_ge H G W hhigh hdom φ hφ xo
      let A : Finset (Fin (12 * n)) := P \ used
      have hA : 0 < A.card := by
        have hinter : (used ∩ P).card ≤ used.card := card_le_card inter_subset_left
        rw [show A = P \ used by rfl, card_sdiff]
        omega
      obtain ⟨z, hzA⟩ := card_pos.mp hA
      have hz := mem_sdiff.mp hzA
      have hnew := extend_singleton H G W S φ p xo hxS hmate z hz.1 hz.2
      have hnewmem : insert x S ∈ C := by
        simp only [C, mem_filter, mem_powerset, subset_univ, true_and]
        exact hnew
      have hforward : S.card ≤ (insert x S).card := by
        rw [card_insert_of_notMem hxS]
        omega
      have hback := hSmax.2 hnewmem hforward
      rw [card_insert_of_notMem hxS] at hback
      omega
  refine ⟨{
    toHom := {
      toFun := p.toFun
      map_rel' := ?_
    }
    injective' := ?_
  }⟩
  · intro x y hxy
    apply p.map_adj
    · rw [hSuniv]
      exact mem_univ x
    · rw [hSuniv]
      exact mem_univ y
    · exact hxy
  · intro x y hxy
    apply p.injOn
    · rw [hSuniv]
      exact mem_univ x
    · rw [hSuniv]
      exact mem_univ y
    · exact hxy

/-! ## Final Ramsey theorem -/

/-- Erdős Problem 800, in the explicit form proved by Alon: every graph on
`n` vertices with no adjacent pair of degree at least three has diagonal
Ramsey number at most `12n`. -/
theorem erdos_800 (n : ℕ) (H : SimpleGraph (Fin n))
    (hH : NoAdjacentHighDegree H) : RamseyFor H (12 * n) := by
  classical
  intro G
  by_cases hn : n = 0
  · subst n
    left
    exact SimpleGraph.IsContained.of_isEmpty
  let D : Finset (Fin (12 * n)) := univ.filter fun v ↦ 6 * n ≤ G.degree v
  by_cases hD : 6 * n ≤ D.card
  · obtain ⟨U, hUD, hUcard⟩ := exists_subset_card_eq hD
    have hdense : ∀ u ∈ U, 6 * n ≤ G.degree u := by
      intro u hu
      have huD := hUD hu
      simpa [D] using huD
    exact oneColorRamsey H hH G U hUcard hdense
  · have hDlt : D.card < 6 * n := Nat.lt_of_not_ge hD
    let B : Finset (Fin (12 * n)) := univ \ D
    have hBcard : 6 * n ≤ B.card := by
      have heq : B.card = 12 * n - D.card := by
        rw [show B = univ \ D by rfl, card_sdiff]
        simp
      omega
    obtain ⟨U, hUB, hUcard⟩ := exists_subset_card_eq hBcard
    let _ : DecidableRel Gᶜ.Adj := Classical.decRel _
    have hdense : (by classical exact ∀ u ∈ U, 6 * n ≤ Gᶜ.degree u) := by
      intro u hu
      have huB := hUB hu
      have huD : u ∉ D := (mem_sdiff.mp huB).2
      have hulow : G.degree u < 6 * n := by simpa [D] using huD
      rw [SimpleGraph.degree_compl]
      simp only [Fintype.card_fin]
      omega
    rcases oneColorRamsey H hH Gᶜ U hUcard hdense with hblue | hred
    · exact Or.inr hblue
    · left
      simpa using hred

/-- Big-O wording of Problem 800, with the absolute constant made explicit. -/
theorem erdos_800_linear :
    ∃ C : ℕ, ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
      NoAdjacentHighDegree H → RamseyFor H (C * n) := by
  exact ⟨12, erdos_800⟩

end

end Erdos800
