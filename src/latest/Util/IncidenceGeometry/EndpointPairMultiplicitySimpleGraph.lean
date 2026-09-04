import Util.IncidenceGeometry.Basic

open Classical
open scoped Real
noncomputable section

lemma EndpointPairMultiplicitySimpleGraph {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (A : Finset ι) (endpoint : ι → Sym2 V)
    (h_nondiag : ∀ i ∈ A, ¬ (endpoint i).IsDiag)
    (h_multiplicity : ∀ e ∈ A.image endpoint,
      (A.filter (fun i => endpoint i = e)).card ≤ 2) :
    ∃ G : SimpleGraph V, ∃ (_ : Fintype G.edgeSet),
      (A.card : ℝ) / 2 ≤ (G.edgeFinset.card : ℝ) ∧
        G.edgeFinset = A.image endpoint := by
  classical
  let E : Finset (Sym2 V) := A.image endpoint
  let G : SimpleGraph V := SimpleGraph.fromEdgeSet ((E : Set (Sym2 V)))
  have : Fintype G.edgeSet := by
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
          (SimpleGraph.fromEdgeSet ((E : Set (Sym2 V)))).edgeSet := by
        rw [SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨by simpa using he, by simpa using hnotdiag⟩
      simpa [G] using heSet
  have hcard_sum :
      A.card = ∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card := by
    simpa [E] using Finset.card_eq_sum_card_image endpoint A
  have hsum_le :
      (∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card) ≤
        ∑ e ∈ E, 2 := by
    exact Finset.sum_le_sum (by
      intro e he
      exact h_multiplicity e (by simpa [E] using he))
  have hcard_le : A.card ≤ 2 * E.card := by
    calc
      A.card = ∑ e ∈ E, (A.filter (fun i => endpoint i = e)).card := hcard_sum
      _ ≤ ∑ e ∈ E, 2 := hsum_le
      _ = 2 * E.card := by
        simp [Finset.sum_const, Nat.mul_comm]
  refine ⟨G, inferInstance, ?_⟩
  have hreal : (A.card : ℝ) ≤ 2 * (E.card : ℝ) := by
    exact_mod_cast hcard_le
  have hGcard : G.edgeFinset.card = E.card := by
    rw [h_edgeFinset]
  constructor
  · rw [hGcard]
    nlinarith
  · exact h_edgeFinset
