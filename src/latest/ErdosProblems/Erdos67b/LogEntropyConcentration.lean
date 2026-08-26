import ErdosProblems.Erdos67b.LogBlockEntropy
import ErdosProblems.Erdos67b.LogResidueUniformity

/-!
# Entropy deficits of logarithmic residue laws

Reuse the proved residue-equidistribution estimate, turn it into a small
entropy deficit, and combine it with the finite entropy decrement.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open FiniteEntropy

theorem entropy_uniformFiniteLaw
    {α : Type*} [Fintype α] [Nonempty α] :
    entropy (uniformFiniteLaw α) = Real.log (Fintype.card α) := by
  have hN : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Fintype.card_pos)
  simp only [entropy, uniformFiniteLaw_apply, Real.negMulLog, Real.log_inv,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem logProbFiniteLaw_residue_l1Dist_uniform_le_of_double
    {L U M : ℕ} [NeZero M] (hL : 0 < L) (hU : 2 * L ≤ U) :
    l1Dist
      (law (logProbFiniteLaw L U hL (by omega)) (fun n ↦ (n.1 : ZMod M)))
      (uniformFiniteLaw (ZMod M)) ≤ 4 * M / L := by
  have hdist := logProbFiniteLaw_residue_l1Dist_uniform_le (M := M) hL (by omega : L ≤ U)
  have hmass := half_le_logProbMassNN hL hU
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hden : (L : ℝ) / 2 ≤ (L : ℝ) * logProbMassNN L U := by nlinarith
  have hbound := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * M)
    (by positivity : (0 : ℝ) < (L : ℝ) / 2) hden
  exact hdist.trans (by convert hbound using 1 <;> field_simp <;> ring)

/-- A uniform lower-endpoint threshold gives nearly maximal residue
entropy for all upper endpoints at least twice the lower endpoint. -/
theorem exists_logProb_residue_entropy_deficit_lt
    (M : ℕ) [NeZero M] {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U),
      L₀ ≤ L → Real.log M - entropy
        (law (logProbFiniteLaw L U hL (by omega)) (fun n ↦ (n.1 : ZMod M))) < ε := by
  obtain ⟨δ, hδ, hmod⟩ := exists_delta_entropy_sub_abs_lt (α := ZMod M) hε
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * M / δ)
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  intro L U hL hU hNL
  have hNl : (N : ℝ) < L := by exact_mod_cast (show N < L by omega)
  have hsmall : 4 * (M : ℝ) / L < δ := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hL)).mpr
    have h := (div_lt_iff₀ hδ).mp (hN.trans hNl)
    simpa only [mul_comm] using h
  have hdist := (logProbFiniteLaw_residue_l1Dist_uniform_le_of_double (M := M) hL hU).trans_lt hsmall
  have hent := hmod _ _ hdist
  rw [entropy_uniformFiniteLaw, ZMod.card, abs_sub_comm] at hent
  exact (le_abs_self _).trans_lt hent

/-- One selected logarithmic block has both small mutual information and
small residue entropy deficit. The common lower endpoint is fixed before
the arbitrary sequence is supplied. -/
theorem exists_logProb_block_entropy_control
    {α : Type*} [Fintype α] [Nonempty α]
    {H₀ : ℕ} (hH₀ : 2 ≤ H₀) {τ C : ℝ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (P : ℕ → ℕ) [∀ j, NeZero (P j)]
    (hP : ∀ j, Real.log (P j) ≤ C * entropyScale H₀ j) :
    ∃ J L₀ : ℕ, 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J,
        rvMutualInfo (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1)
            (fun n ↦ (n.1 : ZMod (P j))) ≤
          τ * entropyScale H₀ j / Real.log (entropyScale H₀ j) ∧
        Real.log (P j) - entropy
          (law (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ (n.1 : ZMod (P j)))) ≤ 1 := by
  classical
  obtain ⟨J, Lbase, hJ, hbase, hselect⟩ :=
    exists_logProb_block_small_mutualInfo (α := α) hH₀ hτ hC P hP
  have hdefExists (j : ℕ) := exists_logProb_residue_entropy_deficit_lt
    (P j) (by norm_num : (0 : ℝ) < 1)
  choose T hT hdef using hdefExists
  refine ⟨J, max Lbase ((Finset.range J).sup T), hJ, hbase.trans_le (le_max_left _ _), ?_⟩
  intro L U hL hU hLL F
  obtain ⟨j, hj, hinfo⟩ := hselect L U hL hU ((le_max_left _ _).trans hLL) F
  refine ⟨j, hj, hinfo, ?_⟩
  have hTL : T j ≤ L := (Finset.le_sup (f := T) (Finset.mem_range.mpr hj)).trans
    ((le_max_right _ _).trans hLL)
  exact (hdef j L U hL hU hTL).le

/-- Full-primorial specialization of the common entropy-control threshold. -/
theorem exists_logProb_primorial_block_entropy_control
    {α : Type*} [Fintype α] [Nonempty α]
    {H₀ : ℕ} (hH₀ : 2 ≤ H₀) {τ : ℝ} (hτ : 0 < τ) :
    ∃ J L₀ : ℕ, 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (hL : 0 < L) (hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → α, ∃ j < J,
        rvMutualInfo (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ finiteSequenceBlock F (entropyScale H₀ j) n.1)
            (fun n ↦ (n.1 : ZMod (primorial (entropyScale H₀ j)))) ≤
          τ * entropyScale H₀ j / Real.log (entropyScale H₀ j) ∧
        Real.log (primorial (entropyScale H₀ j)) - entropy
          (law (logProbFiniteLaw L U hL (by omega))
            (fun n ↦ (n.1 : ZMod (primorial (entropyScale H₀ j))))) ≤ 1 := by
  let : ∀ j, NeZero (primorial (entropyScale H₀ j)) := fun j ↦ inferInstance
  exact exists_logProb_block_entropy_control hH₀ hτ
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    (fun j ↦ primorial (entropyScale H₀ j)) (fun j ↦ log_primorial_le_log_four_mul _)

/-- The selected-scale information and entropy-deficit bounds transfer
every adaptive rare event to the actual logarithmic sampling law. -/
theorem logProb_block_rare_event_le
    {α : Type*} [Fintype α] {L U H P : ℕ} [NeZero P]
    (hL : 0 < L) (hLU : L ≤ U) (F : ℕ → α)
    (E : (Fin H → α) → Finset (ZMod P)) {r η : ℝ} (hr : 0 < r)
    (hrare : ∀ b, ((E b).card : ℝ) * Real.exp r ≤ P)
    (hinfo : rvMutualInfo (logProbFiniteLaw L U hL hLU)
      (fun n ↦ finiteSequenceBlock F H n.1) (fun n ↦ (n.1 : ZMod P)) ≤ η)
    (hdeficit : Real.log P - entropy
      (law (logProbFiniteLaw L U hL hLU) (fun n ↦ (n.1 : ZMod P))) ≤ 1) :
    finiteEventMass (logProbFiniteLaw L U hL hLU)
      {n | (n.1 : ZMod P) ∈ E (finiteSequenceBlock F H n.1)} ≤ (η + 2) / r := by
  let p := logProbFiniteLaw L U hL hLU
  let X : LogProbIndex L U → Fin H → α := fun n ↦ finiteSequenceBlock F H n.1
  let Y : LogProbIndex L U → ZMod P := fun n ↦ n.1
  have h := finiteEventMass_joint_rare_le (jointLaw p X Y) E hr
    (by simpa only [ZMod.card] using hrare) hinfo
    (by simpa only [sndMarginal_jointLaw, ZMod.card] using hdeficit)
  change finiteEventMass (law p (fun n ↦ (X n, Y n))) _ ≤ _ at h
  rw [finiteEventMass_law] at h
  have hset : (fun n ↦ (X n, Y n)) ⁻¹' {z | z.2 ∈ E z.1} =
      {n : LogProbIndex L U | (n.1 : ZMod P) ∈ E (finiteSequenceBlock F H n.1)} := rfl
  rw [hset] at h
  simpa only [p, add_assoc, one_add_one_eq_two] using h

end Erdos67b
