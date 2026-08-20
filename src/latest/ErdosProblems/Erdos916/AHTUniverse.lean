/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Assembly

/-!
# Universe transport for the AHT false-twin theorem

The finite Menger machinery used in the source-level proof of the
Aboulker--Havet--Trotignon theorem is currently stated in universe zero.
This file proves once and for all that its resulting false-twin theorem on
ordinary finite types implies the universe-polymorphic principle needed by
the final Erdős 916 assembly.  The transport is along the canonical
equivalence with `Fin (Fintype.card V)`.
-/

namespace Erdos916

open SimpleGraph

/-- Universe-zero version of the minimum-degree false-twin principle. -/
def DegreeThreeFalseTwinPrinciple0 : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    4 ≤ Fintype.card W →
      (∀ w : W, 3 ≤ H.degree w) →
        ¬HasWheelWitness H →
          ∃ u v : W, AreFalseTwins H u v ∧ H.degree u = 3

universe u

/-- A universe-zero proof of the AHT false-twin theorem suffices for finite
graphs in every universe: relabel the graph by a finite ordinal, apply the
theorem there, and transport the wheel obstruction and false twins back
through the graph isomorphism. -/
theorem degreeThreeFalseTwinPrinciple_of_typeZero
    (h0 : DegreeThreeFalseTwinPrinciple0) :
    DegreeThreeFalseTwinPrinciple.{u} := by
  intro V _ _ G _ hcard hdeg hnoWheel
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.map e
  let φ : G ≃g H := SimpleGraph.Iso.map e G
  letI : DecidableRel H.Adj := Classical.decRel _
  have hcardH : 4 ≤ Fintype.card (Fin (Fintype.card V)) := by
    simpa using hcard
  have hdegH (x : Fin (Fintype.card V)) : 3 ≤ H.degree x := by
    have hx := hdeg (e.symm x)
    have hφx : φ (e.symm x) = x := by
      change e (e.symm x) = x
      exact e.apply_symm_apply x
    have hdegree := φ.degree_eq (e.symm x)
    rw [hφx] at hdegree
    omega
  have hnoWheelH : ¬HasWheelWitness H := by
    intro hH
    apply hnoWheel
    exact HasWheelWitness.mapHomOfInjective
      φ.symm.toHom φ.symm.injective hH
  obtain ⟨u, v, htwin, hdegree⟩ :=
    h0 (Fin (Fintype.card V)) H hcardH hdegH hnoWheelH
  refine ⟨φ.symm u, φ.symm v, ?_, ?_⟩
  · constructor
    · exact φ.symm.injective.ne htwin.1
    · ext w
      simp only [SimpleGraph.mem_neighborSet]
      have huv := htwin.adj_iff (φ w)
      have huMap := φ.symm.map_adj_iff
        (v := u) (w := φ w)
      have hvMap := φ.symm.map_adj_iff
        (v := v) (w := φ w)
      simpa using huMap.trans (huv.trans hvMap.symm)
  · have hdegreeMap := φ.symm.degree_eq u
    exact hdegreeMap.trans hdegree

end Erdos916
