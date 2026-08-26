import ErdosProblems.Erdos1148.FiniteOrbitPartition
import ErdosProblems.Erdos1148.SubadditiveEntropyTransfer

/-! # Subadditivity and linear bounds for finite orbit entropy -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

namespace FiniteMeasurablePartition

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

lemma sum_mass (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] : (∑ i, μ.real (P.atom i)) = 1 := by
  rw [← measureReal_iUnion_fintype P.disjoint_atom P.measurable_atom, P.iUnion_atom]
  simp

lemma entropy_nonneg (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] : 0 ≤ finitePartitionEntropy μ P.atom :=
  finiteEntropy_nonneg (fun _ => measureReal_nonneg) (P.sum_mass μ)

lemma entropy_le_log_card (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] : finitePartitionEntropy μ P.atom ≤ Real.log (Fintype.card ι) :=
  finiteEntropy_le_log_card (fun _ => measureReal_nonneg) (P.sum_mass μ)

noncomputable def orbitEntropy (P : FiniteMeasurablePartition X ι)
    (μ : Measure X) (f : X → X) (n : ℕ) : ℝ :=
  finitePartitionEntropy μ (P.orbitAtom f n)

lemma orbitEntropy_nonneg (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → X} (hf : Measurable f) (n : ℕ) :
    0 ≤ P.orbitEntropy μ f n := (P.orbitPartition hf n).entropy_nonneg μ

lemma orbitEntropy_le_linear (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → X} (hf : Measurable f) (n : ℕ) :
    P.orbitEntropy μ f n ≤ n * Real.log (Fintype.card ι) := by
  have h := (P.orbitPartition hf n).entropy_le_log_card μ
  simpa only [orbitEntropy, orbitPartition, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Real.log_pow] using h

lemma orbitEntropy_zero (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → X) : P.orbitEntropy μ f 0 = 0 := by
  simp [orbitEntropy, finitePartitionEntropy, finiteEntropy, orbitAtom]

theorem orbitEntropy_subadditive (P : FiniteMeasurablePartition X ι) (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → X} (hf : Measurable f)
    (hinv : Measure.map f μ = μ) : Subadditive (P.orbitEntropy μ f) := by
  intro n m
  let s := P.orbitAtom f n
  let t := P.orbitAtom f m
  have hs := P.measurableSet_orbitAtom hf n
  have ht := P.measurableSet_orbitAtom hf m
  have htpre : ∀ w, MeasurableSet (f^[n] ⁻¹' t w) :=
    fun w => (ht w).preimage (hf.iterate n)
  have htdisj : Pairwise (Disjoint on fun w => f^[n] ⁻¹' t w) :=
    fun _ _ h => (P.pairwise_disjoint_orbitAtom f m h).preimage _
  have htcover : (⋃ w, f^[n] ⁻¹' t w) = Set.univ := by
    rw [← Set.preimage_iUnion, P.iUnion_orbitAtom f m, Set.preimage_univ]
  have hpres : MeasurePreserving f μ μ := ⟨hf, hinv⟩
  have hpre := finitePartitionEntropy_preimage_of_invariant μ t ht (hf.iterate n)
    (hpres.iterate n).map_eq
  have hjoin := finitePartitionEntropy_join_le μ s (fun w => f^[n] ⁻¹' t w)
    hs htpre (P.pairwise_disjoint_orbitAtom f n) htdisj
    (P.iUnion_orbitAtom f n) htcover
  have heq : P.orbitEntropy μ f (n + m) =
      finitePartitionEntropy μ (fun w : (Fin n → ι) × (Fin m → ι) =>
        s w.1 ∩ f^[n] ⁻¹' t w.2) := by
    rw [orbitEntropy, ← finitePartitionEntropy_reindex μ _ (Fin.appendEquiv n m)]
    congr 1
    funext w
    exact P.orbitAtom_append f w.1 w.2
  rw [heq]
  simpa only [hpre, orbitEntropy, s, t] using hjoin

end FiniteMeasurablePartition

end Erdos1148.DukeArithmetic
