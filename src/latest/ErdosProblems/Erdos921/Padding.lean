/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.Cycles
import ErdosProblems.Erdos921.Quantitative

open Function Set SimpleGraph
open scoped ENat

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v

/-- The canonical homomorphism into the graph mapped along an embedding. -/
def mapEmbeddingHom {V : Type u} {W : Type v} (f : V ↪ W)
    (G : SimpleGraph V) : G →g G.map f where
  toFun := f
  map_rel' h := SimpleGraph.map_adj_apply' h (f.injective.ne h.ne)

@[simp] lemma mapEmbeddingHom_apply {V : Type u} {W : Type v}
    (f : V ↪ W) (G : SimpleGraph V) (x : V) :
    mapEmbeddingHom f G x = f x := rfl

/-- Lift a walk in the graph obtained by mapping along an embedding, provided
its initial vertex lies in the image. -/
lemma exists_lift_walk_map {V : Type u} {W : Type v} {G : SimpleGraph V}
    (f : V ↪ W) {x y : W} (w : (G.map f).Walk x y)
    (hx : x ∈ Set.range f) :
    ∃ a b : V, ∃ p : G.Walk a b,
      f a = x ∧ f b = y ∧
        HEq (p.map (mapEmbeddingHom f G)) w := by
  induction w with
  | nil =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, a, .nil, rfl, rfl, by simp⟩
  | @cons x z y hxz p ih =>
      obtain ⟨a, z', haz, hax, hz'z⟩ := (SimpleGraph.map_adj f G x z).mp hxz
      subst x
      subst z
      obtain ⟨b, c, q, hbz, hcy, hq⟩ := ih ⟨z', rfl⟩
      have hb : b = z' := f.injective hbz
      subst b
      subst y
      cases hq
      refine ⟨a, c, .cons haz q, rfl, rfl, ?_⟩
      rfl

/-- Every nonempty closed walk in a mapped graph is the image of a closed
walk in the original graph. -/
lemma exists_lift_closed_walk_map {V : Type u} {W : Type v} {G : SimpleGraph V}
    (f : V ↪ W) {x : W} (w : (G.map f).Walk x x) (hw : ¬w.Nil) :
    ∃ a : V, f a = x ∧ ∃ p : G.Walk a a,
      HEq (p.map (mapEmbeddingHom f G)) w := by
  have hadj := w.adj_snd hw
  obtain ⟨a, b, hab, hax, _⟩ := (SimpleGraph.map_adj f G x w.snd).mp hadj
  obtain ⟨a', b', p, ha'x, hb'x, hp⟩ := exists_lift_walk_map f w ⟨a, hax⟩
  have hab' : a' = b' := f.injective (ha'x.trans hb'x.symm)
  subst b'
  exact ⟨a', ha'x, p, hp⟩

/-- Mapping along an embedding (and hence adjoining isolated vertices) does
not create new bounded odd cycles. -/
lemma no_short_odd_cycle_map {V : Type u} {W : Type v} {G : SimpleGraph V}
    (f : V ↪ W) {L : ℕ} (hodd : ¬ HasOddCycleAtMost G L) :
    ¬ HasOddCycleAtMost (G.map f) L := by
  rintro ⟨x, w, hwc, hwo, hwlen⟩
  obtain ⟨a, hax, p, hp⟩ := exists_lift_closed_walk_map f w hwc.not_nil
  subst x
  have hp' : p.map (mapEmbeddingHom f G) = w := eq_of_heq hp
  subst w
  have hinj : Function.Injective (mapEmbeddingHom f G) := by
    intro b c hbc
    exact f.injective hbc
  have hlenmap : (p.map (mapEmbeddingHom f G)).length = p.length :=
    Walk.length_map (mapEmbeddingHom f G) p
  have hwo' : Odd p.length := hlenmap ▸ hwo
  have hwlen' : p.length ≤ L := hlenmap ▸ hwlen
  apply hodd
  refine ⟨a, p, ?_, ?_, ?_⟩
  · rw [← Walk.isCycle_map_iff_of_injective hinj]
    exact hwc
  · exact hwo'
  · exact hwlen'

/-- The canonical embedding into a larger `Fin` type. -/
def embeddingFinOfCardLE (V : Type u) [Fintype V] {n : ℕ}
    (h : Fintype.card V ≤ n) : V ↪ Fin n :=
  (Fintype.equivFin V).toEmbedding.trans (Fin.castLEEmb h)

/-- A finite graph padded with isolated vertices to have exactly `n`
vertices. -/
def padGraph {V : Type u} [Fintype V] (G : SimpleGraph V) {n : ℕ}
    (h : Fintype.card V ≤ n) : SimpleGraph (Fin n) :=
  G.map (embeddingFinOfCardLE V h)

lemma padGraph_colorable {V : Type u} [Fintype V] {G : SimpleGraph V}
    {n c : ℕ} (hn : Fintype.card V ≤ n) [NeZero c]
    (hc : G.Colorable c) : (padGraph G hn).Colorable c :=
  hc.map (embeddingFinOfCardLE V hn)

lemma padGraph_not_colorable {V : Type u} [Fintype V] {G : SimpleGraph V}
    {n c : ℕ} (hn : Fintype.card V ≤ n)
    (hc : ¬G.Colorable c) : ¬(padGraph G hn).Colorable c := by
  intro hpad
  exact hc (hpad.of_hom (SimpleGraph.Embedding.map (embeddingFinOfCardLE V hn) G).toHom)

lemma padGraph_chromaticNumber {V : Type u} [Fintype V] {G : SimpleGraph V}
    {n c : ℕ} (hcpos : 0 < c) (hn : Fintype.card V ≤ n)
    (hcol : G.Colorable c) (hnot : ¬G.Colorable (c - 1)) :
    (padGraph G hn).chromaticNumber = (c : ℕ∞) := by
  let : NeZero c := ⟨hcpos.ne'⟩
  have hpadcol := padGraph_colorable hn hcol
  have hpadnot := padGraph_not_colorable hn hnot
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  exact (chromaticNumber_eq_iff_colorable_not_colorable).2 ⟨hpadcol, by simpa using hpadnot⟩

lemma padGraph_no_short_odd_cycle {V : Type u} [Fintype V]
    {G : SimpleGraph V} {n L : ℕ} (hn : Fintype.card V ≤ n)
    (hodd : ¬ HasOddCycleAtMost G L) :
    ¬ HasOddCycleAtMost (padGraph G hn) L :=
  no_short_odd_cycle_map (embeddingFinOfCardLE V hn) hodd

end

end Erdos921
