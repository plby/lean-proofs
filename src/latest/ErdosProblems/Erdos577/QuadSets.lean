import ErdosProblems.Erdos577.Blocks

/-! Explicit set witnesses for ordinary four-cycles. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Adjacent vertices are already distinct; only the two opposite pairs
need additional distinctness hypotheses. -/
lemma QuadOn.of_vertices {a b c d : V} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    QuadOn G {a, b, c, d} := by
  let q := Quadrilateral.ofVertices a b c d hab.ne hac hda.ne.symm hbc.ne hbd hcd.ne
    hab hbc hcd hda
  refine ⟨q, ?_⟩
  change univ.image (![a, b, c, d] : Fin 4 → V) = {a, b, c, d}
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [hu]
  simp

end Erdos577
