import ErdosProblems.Erdos577.WeightedFifteenUpper
import ErdosProblems.Erdos577.WeightedNineteenPaths

/-! The two improved paths and paired heavy outside block in weighted pattern (15). -/

namespace Erdos577.WeightedFifteen

open Finset

/-- False is the source's L3, true is its L4. -/
def pathVertices (fourth : Bool) : Fin 4 → Fin 8 :=
  if fourth then ![5, 3, 1, 0] else ![7, 4, 0, 1]

def corePath (fourth : Bool) : FourPath graph where
  vertices := ⟨pathVertices fourth, by cases fourth <;> decide +kernel⟩
  adjacent := by cases fourth <;> decide +kernel

lemma corePath_inside (fourth : Bool) :
    contacts upperGraph (corePath fourth).support univ = 14 := by
  cases fourth <;> decide +kernel

lemma corePath_quad (fourth : Bool) : QuadOn graph (univ \ (corePath fourth).support) :=
  QuadOn.of_degreeIn (by cases fourth <;> decide +kernel) (by cases fourth <;> decide +kernel)

lemma corePath_edges (fourth : Bool) :
    edgeCount graph (univ \ (corePath fourth).support) = 6 := by
  cases fourth <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def path (fourth : Bool) (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) : FourPath G := (corePath fourth).image (coreCopy p q hd h)

lemma path_support (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    (path fourth p q hd h).support =
      (corePath fourth).support.image (PawEncoding.labeling p q hd) :=
  (corePath fourth).image_support (coreCopy p q hd h)

lemma path_subset (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    (path fourth p q hd h).support ⊆ p.support ∪ q.support := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  exact image_subset_image (subset_univ _)

lemma complement_image (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    (p.support ∪ q.support) \ (path fourth p q hd h).support =
      (univ \ (corePath fourth).support).image (coreCopy p q hd h) := by
  have hinj : Function.Injective (coreCopy p q hd h : Fin 8 → V) := (coreCopy p q hd h).injective
  rw [image_sdiff _ _ hinj, coreCopy_image, path_support]
  rfl

lemma path_complement_quad (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    QuadOn G ((p.support ∪ q.support) \ (path fourth p q hd h).support) := by
  rw [complement_image]
  exact (corePath_quad fourth).image (coreCopy p q hd h)

lemma path_complement_clique (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    G.IsNClique 4 ((p.support ∪ q.support) \ (path fourth p q hd h).support) := by
  have hcard := (path_complement_quad fourth p q hd h).card
  apply clique_of_four_six hcard
  have hmax := edgeCount_le_six G hcard
  have hmin := edgeCount_image_le (coreCopy p q hd h) (univ \ (corePath fourth).support)
  rw [corePath_edges, ← complement_image] at hmin
  omega

lemma path_gain (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    edgeCount G q.support <
      edgeCount G ((p.support ∪ q.support) \ (path fourth p q hd h).support) := by
  rw [complement_image, old_edgeCount p q h]
  have he := edgeCount_image_le (coreCopy p q hd h) (univ \ (corePath fourth).support)
  rw [corePath_edges] at he
  omega

lemma path_inside (fourth : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j)) :
    contacts G (path fourth p q hd h).support (p.support ∪ q.support) ≤ 14 := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  have hb := contacts_image_le_of_adj G upperGraph (PawEncoding.labeling p q hd)
    (PawEncoding.labeling p q hd).injective (corePath fourth).support univ
    (fun i _ j _ ↦ adj_upper p q hd h hleaf hcenter i j)
  exact hb.trans (le_of_eq (corePath_inside fourth))

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧
      17 ≤ contacts G (path false p q hd h).support a +
        contacts G (path true p q hd h).support a := by
  have hleaf := c.paw_nonadjacent hcard hn p hp
  have hcenter := center_absent hc hcard hn p hp hb q hq hd h
  have hfirst := path_inside false p q hd h hleaf hcenter
  have hsecond := path_inside true p q hd h hleaf hcenter
  rw [hp, hq] at hfirst hsecond
  exact c.exists_paired_heavy_outside_core hcard hdeg hb
    (path false p q hd h).support (path true p q hd h).support
    (path false p q hd h).card_support (path true p q hd h).card_support (by omega)

end Erdos577.WeightedFifteen
