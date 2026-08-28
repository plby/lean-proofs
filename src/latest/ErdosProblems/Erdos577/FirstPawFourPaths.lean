import ErdosProblems.Erdos577.FirstPawFourPairs
import ErdosProblems.Erdos577.LocalPathComplement

/-! Transport every complementary path of pattern (4), with its exact original vertex support. -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def terminalSet (p : Paw G) (q : Quadrilateral G) : Finset V := {p.leaf, q 1, q 3}

def vertexSet (p : Paw G) (q : Quadrilateral G) : Finset V :=
  {p.leaf, p.vertices 2, p.vertices 3, q 1, q 3}

omit [DecidableRel G.Adj] in
lemma terminalSet_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    PairTable.terminalSet.image (PawEncoding.labeling p q hd) = terminalSet p q := by
  simp only [PairTable.terminalSet, image_insert, image_singleton]
  rfl

omit [DecidableRel G.Adj] in
lemma vertexSet_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    PairTable.vertexSet.image (PawEncoding.labeling p q hd) = vertexSet p q := by
  simp only [PairTable.vertexSet, image_insert, image_singleton]
  rfl

lemma path_for_indices (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (u v w : Fin 8) (hu : u ∈ PairTable.terminalSet)
    (hv : v ∈ PairTable.vertexSet.erase u) (hw : w ∈ PairTable.vertexSet.erase u) (hvw : v ≠ w) :
    ∃ d : LocalPathPartition G (p.support ∪ q.support),
      d.terminal = PawEncoding.labeling p q hd u ∧
      ((d.triple 0 = PawEncoding.labeling p q hd v ∧
          d.triple 2 = PawEncoding.labeling p q hd w) ∨
        (d.triple 0 = PawEncoding.labeling p q hd w ∧
          d.triple 2 = PawEncoding.labeling p q hd v)) := by
  obtain ⟨miss, hrows⟩ := exists_lower_rows p q h hheavy
  obtain ⟨tag, htag, hend⟩ := PairTable.endpoint_coverage u v w hu hv hw hvw
  let f := copy p q hd h.1 miss hrows
  let d := ((PairTable.partition miss tag).image f).withSupport (copy_image p q hd h.1 miss hrows)
  have h0 : d.triple 0 = PawEncoding.labeling p q hd (PairTable.endpoint0 tag) := by
    change f ((PairTable.partition miss tag).triple 0) = _
    rw [PairTable.partition_triple]
    rfl
  have h2 : d.triple 2 = PawEncoding.labeling p q hd (PairTable.endpoint2 tag) := by
    change f ((PairTable.partition miss tag).triple 2) = _
    rw [PairTable.partition_triple]
    rfl
  refine ⟨d, ?_, ?_⟩
  · change f (PairTable.partition miss tag).terminal = _
    rw [PairTable.partition_terminal, htag]
    rfl
  · rcases hend with ⟨hv', hw'⟩ | ⟨hw', hv'⟩
    · rw [hv'] at h0
      rw [hw'] at h2
      exact Or.inl ⟨h0, h2⟩
    · rw [hw'] at h0
      rw [hv'] at h2
      exact Or.inr ⟨h0, h2⟩

lemma path_partition (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (u v w : V) (hu : u ∈ terminalSet p q)
    (hv : v ∈ (vertexSet p q).erase u) (hw : w ∈ (vertexSet p q).erase u) (hvw : v ≠ w) :
    ∃ d : LocalPathPartition G (p.support ∪ q.support), d.terminal = u ∧
      ((d.triple 0 = v ∧ d.triple 2 = w) ∨ (d.triple 0 = w ∧ d.triple 2 = v)) := by
  let e := PawEncoding.labeling p q hd
  have heterm : PairTable.terminalSet.image e = terminalSet p q := terminalSet_image p q hd
  have hevertices : PairTable.vertexSet.image e = vertexSet p q := vertexSet_image p q hd
  rw [← heterm] at hu
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  rw [← hevertices, ← image_erase hinj] at hv hw
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
  exact path_for_indices p q hd h hheavy i j l hi hj hl (fun hh ↦ hvw (congrArg e hh))

theorem complementary_path (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (u v w : V) (hu : u ∈ terminalSet p q)
    (hv : v ∈ (vertexSet p q).erase u) (hw : w ∈ (vertexSet p q).erase u) (hvw : v ≠ w) :
    ∃ z ∈ (p.support ∪ q.support) \ {u, v, w}, G.Adj z v ∧ G.Adj z w ∧
      QuadOn G ((p.support ∪ q.support) \ {u, v, w, z}) := by
  obtain ⟨d, hdu, hend⟩ := path_partition p q hd h hheavy u v w hu hv hw hvw
  obtain ⟨hz, hvz, hzw, hquad⟩ := d.middle_spec
  rcases hend with ⟨hdv, hdw⟩ | ⟨hdw, hdv⟩
  · simp only [hdu, hdv, hdw] at hz hvz hzw hquad
    exact ⟨d.triple 1, hz, hvz.symm, hzw, hquad⟩
  · simp only [hdu, hdv, hdw] at hz hvz hzw hquad
    refine ⟨d.triple 1, ?_, hzw, hvz.symm, ?_⟩
    · have he : ({u, w, v} : Finset V) = {u, v, w} := by
        ext x
        simp only [mem_insert, mem_singleton]
        tauto
      exact he ▸ hz
    · simpa only [insert_comm] using hquad

variable [Fintype V]

lemma no_common_replacement {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (u v w : V) (hu : u ∈ terminalSet p q)
    (hv : v ∈ (vertexSet p q).erase u) (hw : w ∈ (vertexSet p q).erase u) (hvw : v ≠ w) :
    ¬CommonReplacement G v w u a := by
  obtain ⟨d, hdu, hend⟩ := path_partition p q hd h hheavy u v w hu hv hw hvw
  let d' := d.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  have hno := c.no_common_replacement hcard hn hb ha hab d'
  change ¬CommonReplacement G (d.triple 0) (d.triple 2) d.terminal a at hno
  rw [hdu] at hno
  rcases hend with ⟨hdv, hdw⟩ | ⟨hdw, hdv⟩
  · rw [hdv, hdw] at hno
    exact hno
  · rw [hdv, hdw] at hno
    rintro ⟨z, hz, hvz, hwz, hrep⟩
    exact hno ⟨z, hz, hwz, hvz, hrep⟩

end Erdos577.FirstPawFour
