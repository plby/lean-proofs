import Submission.Preamble

open Classical
open scoped Real
noncomputable section

namespace Erdos652

/-- Quotient a finite family of non-loop arcs by its unordered endpoint pair.
If every pair occurs at most `M` times, at least `|A|/M` edges remain. -/
lemma endpointPairMultiplicitySimpleGraph
    {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (A : Finset ι) (endpoint : ι → Sym2 V) (M : ℕ) (hM : 1 ≤ M)
    (h_nondiag : ∀ i ∈ A, ¬ (endpoint i).IsDiag)
    (h_multiplicity : ∀ e ∈ A.image endpoint,
      (A.filter (fun i => endpoint i = e)).card ≤ M) :
    ∃ G : SimpleGraph V, ∃ (_ : Fintype G.edgeSet),
      (A.card : ℝ) / M ≤ (G.edgeFinset.card : ℝ) ∧
        G.edgeFinset = A.image endpoint := by
  classical
  let E : Finset (Sym2 V) := A.image endpoint
  let G : SimpleGraph V := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  haveI : Fintype G.edgeSet := by
    dsimp [G]
    infer_instance
  have h_edgeFinset : G.edgeFinset = E := by
    ext e
    constructor
    · intro he
      have heSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      have heDiff : e ∈ (E : Set (Sym2 V)) \ Sym2.diagSet := by
        simpa [G] using heSet
      simpa [E] using heDiff.1
    · intro he
      have hnotdiag : ¬ e.IsDiag := by
        rcases Finset.mem_image.mp (by simpa [E] using he) with ⟨i, hi, rfl⟩
        exact h_nondiag i hi
      apply SimpleGraph.mem_edgeFinset.mpr
      have heSet : e ∈
          (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).edgeSet := by
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨by simpa using he, by simpa using hnotdiag⟩
      simpa [G] using heSet
  have hcard_sum :
      A.card = ∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card := by
    simpa [E] using Finset.card_eq_sum_card_image endpoint A
  have hsum_le :
      (∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card) ≤
        ∑ _e ∈ E, M := by
    exact Finset.sum_le_sum (fun e he => h_multiplicity e (by simpa [E] using he))
  have hcard_le : A.card ≤ M * E.card := by
    calc
      A.card = ∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card := hcard_sum
      _ ≤ ∑ _e ∈ E, M := hsum_le
      _ = M * E.card := by simp [Finset.sum_const, Nat.mul_comm]
  refine ⟨G, inferInstance, ?_, h_edgeFinset⟩
  have hreal : (A.card : ℝ) ≤ M * (E.card : ℝ) := by exact_mod_cast hcard_le
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  rw [h_edgeFinset]
  exact (div_le_iff₀ hMreal).2 (by simpa [mul_comm] using hreal)

end Erdos652
