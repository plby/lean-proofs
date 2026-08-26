import ErdosProblems.Erdos1038.RecoveryPositivePotentialLp

/-!
# Diagonal recovery across positive-buffer measures

Each fixed positive-buffer probability is recovered by a sequence of
empirical polynomials.  This file supplies the topological diagonal argument
needed when the buffer parameter itself varies and its negative-set volumes
converge to the sharp target.
-/

open scoped ENNReal
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

/-- A first-countable diagonal selection theorem.  The outer indices may be
passed to a subsequence; this is exactly what recovery from a varying family
of limiting objects requires. -/
theorem exists_subseq_diagonal_tendsto
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {u : ℕ → ℕ → X} {v : ℕ → X} {V : X}
    (hu : ∀ n, Tendsto (u n) atTop (𝓝 (v n)))
    (hv : Tendsto v atTop (𝓝 V)) :
    ∃ k m : ℕ → ℕ, Tendsto (fun n ↦ u (k n) (m n)) atTop (𝓝 V) := by
  obtain ⟨idx, hidx, hB⟩ := (nhds_basis_opens V).exists_antitone_subbasis
  let B : ℕ → Set X := fun n ↦ idx n
  have hexv : ∀ n, ∃ k, v k ∈ B n := by
    intro n
    have hmem : B n ∈ 𝓝 V := hB.mem n
    exact (hv.eventually hmem).exists
  choose k hk using hexv
  have hexu : ∀ n, ∃ m, u (k n) m ∈ B n := by
    intro n
    have hopen : IsOpen (B n) := (hidx n).2
    have hnhds : B n ∈ 𝓝 (v (k n)) := hopen.mem_nhds (hk n)
    exact ((hu (k n)).eventually hnhds).exists
  choose m hm using hexu
  refine ⟨k, m, (atTop_basis.tendsto_iff hB.toHasBasis).2 ?_⟩
  intro j hj
  refine ⟨j, trivial, ?_⟩
  intro n hn
  exact hB.antitone hn (hm n)

/-- If every value in a convergent `ℝ≥0∞` sequence is itself recoverable by
admissible polynomial sublevel volumes, then the limit is recoverable by one
diagonal polynomial sequence. -/
theorem exists_admissiblePolynomials_tendsto_of_recoverableVolumes
    {V : ℕ → ℝ≥0∞} {target : ℝ≥0∞}
    (hrecover : ∀ n, ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun j ↦ sublevelVolume (f j).1) atTop (𝓝 (V n)))
    (hV : Tendsto V atTop (𝓝 target)) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 target) := by
  choose f hf using hrecover
  obtain ⟨k, m, hdiag⟩ := exists_subseq_diagonal_tendsto
    (u := fun n j ↦ sublevelVolume (f n j).1) hf hV
  let g : ℕ → AdmissiblePolynomial := fun n ↦ f (k n) (m n)
  exact ⟨g, hdiag⟩

/-- Recovery from a varying sequence of positive buffers.  The only
remaining inputs are pointwise zero-level nullity for each buffer and
convergence of their pointwise negative-set volumes. -/
theorem exists_admissiblePolynomials_tendsto_of_positiveBuffers
    (s alpha : ℕ → ℝ)
    (hs : ∀ n, 0 < s n) (hs1 : ∀ n, s n < 1)
    (halpha : ∀ n, 0 ≤ alpha n) (halphas : ∀ n, alpha n ≤ s n)
    (hzero : ∀ n, volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s n) (alpha n) x = 0} = 0)
    {target : ℝ≥0∞}
    (hvolume : Tendsto (fun n ↦ volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s n) (alpha n) x < 0})
      atTop (𝓝 target)) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 target) := by
  apply exists_admissiblePolynomials_tendsto_of_recoverableVolumes
    (V := fun n ↦ volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s n) (alpha n) x < 0})
  · intro n
    exact exists_admissiblePolynomials_sublevelVolume_tendsto_positiveBuffer
      (hs n) (hs1 n) (halpha n) (halphas n) (hzero n)
  · exact hvolume

end

end Erdos1038
