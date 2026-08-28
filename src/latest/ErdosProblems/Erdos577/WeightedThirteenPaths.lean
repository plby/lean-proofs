import ErdosProblems.Erdos577.WeightedThirteenUpper
import ErdosProblems.Erdos577.WeightedNineteenPaths

/-! The two improved paths and paired heavy outside block in weighted pattern (13). -/

namespace Erdos577.WeightedThirteen

open Finset

/-- False is the source's L1, true is its L2. -/
def pathVertices (second : Bool) : Fin 4 → Fin 8 :=
  if second then ![0, 1, 3, 5] else ![0, 1, 2, 7]

def corePath (second : Bool) : FourPath graph where
  vertices := ⟨pathVertices second, by cases second <;> decide +kernel⟩
  adjacent := by cases second <;> decide +kernel

lemma corePath_inside (second : Bool) :
    contacts upperGraph (corePath second).support univ = 15 := by
  cases second <;> decide +kernel

lemma corePath_quad (second : Bool) : QuadOn graph (univ \ (corePath second).support) :=
  QuadOn.of_degreeIn (by cases second <;> decide +kernel) (by cases second <;> decide +kernel)

def coreQuad (second : Bool) : Quadrilateral graph :=
  Quadrilateral.ofEdges
    ⟨if second then ![2, 4, 7, 6] else ![3, 4, 5, 6],
      by cases second <;> decide +kernel⟩ (by cases second <;> decide +kernel)

lemma coreQuad_support (second : Bool) :
    (coreQuad second).support = univ \ (corePath second).support := by
  cases second <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def path (second : Bool) (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) : FourPath G := (corePath second).image (coreCopy p q hd h)

lemma path_support (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    (path second p q hd h).support =
      (corePath second).support.image (PawEncoding.labeling p q hd) :=
  (corePath second).image_support (coreCopy p q hd h)

lemma path_subset (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    (path second p q hd h).support ⊆ p.support ∪ q.support := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  exact image_subset_image (subset_univ _)

lemma complement_image (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    (p.support ∪ q.support) \ (path second p q hd h).support =
      (univ \ (corePath second).support).image (coreCopy p q hd h) := by
  have hinj : Function.Injective (coreCopy p q hd h : Fin 8 → V) := (coreCopy p q hd h).injective
  rw [image_sdiff _ _ hinj, coreCopy_image, path_support]
  rfl

lemma path_complement_quad (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    QuadOn G ((p.support ∪ q.support) \ (path second p q hd h).support) := by
  rw [complement_image]
  exact (corePath_quad second).image (coreCopy p q hd h)

def newQuad (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    Quadrilateral G := (coreCopy p q hd h).comp (coreQuad second)

lemma newQuad_support (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    (newQuad second p q hd h).support =
      (p.support ∪ q.support) \ (path second p q hd h).support := by
  rw [complement_image, ← coreQuad_support]
  change univ.image (newQuad second p q hd h) =
    (univ.image (coreQuad second)).image (coreCopy p q hd h)
  rw [image_image]
  rfl

lemma path_gain_exact (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    edgeCount G ((p.support ∪ q.support) \ (path second p q hd h).support) =
      edgeCount G q.support + 1 := by
  rw [← newQuad_support, (newQuad second p q hd h).edgeCount_eq, q.edgeCount_eq, if_neg h.1]
  cases second
  · change 4 + (if G.Adj (p.vertices 3) (q 1) then 1 else 0) +
      (if G.Adj (q 0) (q 2) then 1 else 0) = _
    rw [if_pos ((h.2.2.2 1).mpr (by decide))]
    omega
  · change 4 + (if G.Adj (p.vertices 2) (q 3) then 1 else 0) +
      (if G.Adj (q 0) (q 2) then 1 else 0) = _
    rw [if_pos ((h.2.2.1 3).mpr (by decide))]
    omega

lemma path_gain (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    edgeCount G q.support <
      edgeCount G ((p.support ∪ q.support) \ (path second p q hd h).support) := by
  rw [path_gain_exact]
  omega

lemma path_inside (second : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3)) :
    contacts G (path second p q hd h).support (p.support ∪ q.support) ≤ 15 := by
  rw [path_support, ← PawEncoding.labeling_image p q hd]
  have hb := contacts_image_le_of_adj G upperGraph (PawEncoding.labeling p q hd)
    (PawEncoding.labeling p q hd).injective (corePath second).support univ
    (fun i _ j _ ↦ adj_upper p q hd h hleaf hcenter i j)
  exact hb.trans (le_of_eq (corePath_inside second))

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧
      17 ≤ contacts G (path false p q hd h).support a +
        contacts G (path true p q hd h).support a := by
  have hleaf := c.paw_nonadjacent hcard hn p hp
  have hcenter := center_absent p q hd h (by rw [hp, hq]; exact c.no_local_factor hcard hn hb)
  have hfirst := path_inside false p q hd h hleaf hcenter
  have hsecond := path_inside true p q hd h hleaf hcenter
  rw [hp, hq] at hfirst hsecond
  exact c.exists_paired_heavy_outside_core hcard hdeg hb
    (path false p q hd h).support (path true p q hd h).support
    (path false p q hd h).card_support (path true p q hd h).card_support (by omega)

end Erdos577.WeightedThirteen
