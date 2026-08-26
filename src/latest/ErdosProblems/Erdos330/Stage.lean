/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.Basic
import ErdosProblems.Erdos330.Elementary
import ErdosProblems.Erdos330.ResidueBlock

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Abstract stage data for Erdős Problem 330

This file records the finite state and CRT gadget interfaces used by the
priority construction.  The hard quadratic-residue and CRT proofs can later
instantiate these interfaces without changing the global construction layer.
-/

namespace Erdos330

open scoped BigOperators
open scoped Pointwise

/-- A finite protected block produced when servicing an active element. -/
structure ProtectedBlockCertificate (S : Finset ℕ) (a endpoint : ℕ) where
  block : Finset ℕ
  block_subset_private :
    ∀ n ∈ block, n ∈ privateSet {x : ℕ | x ∈ S} a
  block_le_endpoint : ∀ n ∈ block, n ≤ endpoint
  block_lt_endpoint : ∀ n ∈ block, n < endpoint
  densityNumerator : ℕ
  densityDenominator : ℕ
  densityDenominator_pos : 0 < densityDenominator
  block_density_lower :
    densityNumerator * endpoint ≤ densityDenominator * block.card

/--
The bounded-resource CRT gadget used by one stage of the construction.

The selected-coordinate and base-projection fields from the roadmap will be
added once the concrete CRT representation is fixed.  The fields here are the
parts already needed by the abstract coverage and privacy arguments.
-/
structure CRTGadget (P : Finset ℕ) (m : ℕ → ℕ) (M a : ℕ)
    (D : Finset (ZMod M)) where
  T : Finset (ZMod M)
  Pstar : Finset (ZMod M)
  Tbase : Finset (ZMod M)
  Tbase_subset_T : Tbase ⊆ T
  T_subset_D : T ⊆ D
  Pstar_subset_D : Pstar ⊆ D
  D_add_Tbase_full :
    ((D : Set (ZMod M)) + (Tbase : Set (ZMod M))) = Set.univ
  selectedCoord : ZMod M → ZMod (m a)
  selectedCoord_natCast : ∀ n : ℕ, selectedCoord (n : ZMod M) = (n : ZMod (m a))
  privateResidue : ZMod (m a)
  privateResidue_ne_active : privateResidue ≠ (a : ZMod (m a))
  T_selected_avoid : ∀ t ∈ T, selectedCoord t ≠ (a : ZMod (m a))
  Pstar_selected : ∀ r ∈ Pstar, selectedCoord r = privateResidue
  D_nat_avoid :
    ∀ c ∈ P, ∀ n : ℕ, (n : ZMod M) ∈ D → (n : ZMod (m c)) ≠ (c : ZMod (m c))
  T_add_T_compl_private :
    ((T : Set (ZMod M)) + (T : Set (ZMod M))) =
      Set.univ \ ((fun x : ZMod M => (a : ZMod M) + x) '' (Pstar : Set (ZMod M)))
  D_add_T_full :
    ((D : Set (ZMod M)) + (T : Set (ZMod M))) = Set.univ
  Pstar_card_formula :
    (Pstar.card : ℝ) / (M : ℝ) =
      (1 : ℝ) / (m a : ℝ) *
        (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ))

theorem CRTGadget.Pstar_density_lower_half {P : Finset ℕ} {m : ℕ → ℕ} {M a : ℕ}
    {D : Finset (ZMod M)} (G : CRTGadget P m M a D)
    (hma_pos : 0 < m a) (hm_pos : ∀ b ∈ P.erase a, 0 < m b)
    (hbudget : (P.erase a).sum (fun b => (1 : ℝ) / (m b : ℝ)) ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) / (m a : ℝ) * (1 / 2 : ℝ) ≤ (G.Pstar.card : ℝ) / (M : ℝ) := by
  have hprod_lower : (1 / 2 : ℝ) ≤
      (P.erase a).prod (fun b => 1 - (1 : ℝ) / (m b : ℝ)) := by
    have hbasic := one_sub_sum_le_prod_one_sub (P.erase a)
      (fun b => (1 : ℝ) / (m b : ℝ)) ?_ ?_
    · linarith
    · intro b hb
      positivity
    · intro b hb
      have hbpos : (0 : ℝ) < (m b : ℝ) := by exact_mod_cast hm_pos b hb
      rw [div_le_one hbpos]
      exact_mod_cast (Nat.succ_le_of_lt (hm_pos b hb))
  rw [G.Pstar_card_formula]
  have hmaR : (0 : ℝ) ≤ (1 : ℝ) / (m a : ℝ) := by
    positivity
  exact mul_le_mul_of_nonneg_left hprod_lower hmaR

theorem CRTGadget.Pstar_card_pos {P : Finset ℕ} {m : ℕ → ℕ} {M a : ℕ}
    {D : Finset (ZMod M)} (G : CRTGadget P m M a D)
    (hM_pos : 0 < M) (hma_pos : 0 < m a)
    (hm_ge2 : ∀ b ∈ P.erase a, 2 ≤ m b) :
    0 < G.Pstar.card := by
  have hdiv_pos : 0 < ((G.Pstar.card : ℝ) / (M : ℝ)) := by
    rw [G.Pstar_card_formula]
    apply mul_pos
    · have hmaR : (0 : ℝ) < (m a : ℝ) := by exact_mod_cast hma_pos
      exact div_pos zero_lt_one hmaR
    · apply Finset.prod_pos
      intro b hb
      have hb_ge2 : 2 ≤ m b := hm_ge2 b hb
      have hbR_pos : (0 : ℝ) < (m b : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hb_ge2)
      have hbR_gt1 : (1 : ℝ) < (m b : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hb_ge2)
      have hfrac_lt : (1 : ℝ) / (m b : ℝ) < 1 := by
        rw [div_lt_iff₀ hbR_pos]
        simpa using hbR_gt1
      linarith
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hcardR : (0 : ℝ) < (G.Pstar.card : ℝ) := by
    have hmul := mul_pos hdiv_pos hMposR
    rwa [div_mul_cancel₀ _ (ne_of_gt hMposR)] at hmul
  exact_mod_cast hcardR

theorem CRTGadget.M_le_two_mul_selected_mul_Pstar_card {P : Finset ℕ} {m : ℕ → ℕ}
    {M a : ℕ} {D : Finset (ZMod M)} (G : CRTGadget P m M a D)
    (hM_pos : 0 < M) (hma_pos : 0 < m a)
    (hm_pos : ∀ b ∈ P.erase a, 0 < m b)
    (hbudget : (P.erase a).sum (fun b => (1 : ℝ) / (m b : ℝ)) ≤ (1 / 2 : ℝ)) :
    M ≤ 2 * m a * G.Pstar.card := by
  have hreal := G.Pstar_density_lower_half hma_pos hm_pos hbudget
  have hmaR : (0 : ℝ) < (m a : ℝ) := by exact_mod_cast hma_pos
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hcast : (M : ℝ) ≤ (2 * m a * G.Pstar.card : ℕ) := by
    field_simp [ne_of_gt hmaR, ne_of_gt hMR] at hreal
    have htarget :
        ((2 * m a * G.Pstar.card : ℕ) : ℝ) =
          (m a : ℝ) * 2 * (G.Pstar.card : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [htarget]
    nlinarith
  exact_mod_cast hcast

/--
Finite state at one stage of the priority construction.

The state stores a full-residue reservoir and coverage up to `R`; later stage
lemmas extend this state while preserving isolation of active elements.
-/
structure StageState where
  S : Finset ℕ
  P : Finset ℕ
  m : ℕ → ℕ
  M : ℕ
  D : Finset (ZMod M)
  H : ℕ
  X : ℕ
  R : ℕ
  coverStart : ℕ
  P_subset_S : P ⊆ S
  S_le_X : ∀ s ∈ S, s ≤ X
  m_prime : ∀ a ∈ P, Nat.Prime (m a)
  m_ge23 : ∀ a ∈ P, 23 ≤ m a
  m_mod4 : ∀ a ∈ P, m a % 4 = 3
  m_pairwise_coprime :
    ∀ ⦃a⦄, a ∈ P → ∀ ⦃b⦄, b ∈ P → a ≠ b → Nat.Coprime (m a) (m b)
  M_def : M = P.prod m
  isolated :
    ∀ a ∈ P, ∀ s ∈ S, (s : ZMod (m a)) = (a : ZMod (m a)) → s = a
  reservoir_subset :
    residueBlockFinset M D H X ⊆ S
  reservoir_multiplicity :
    ∀ Jlo, H ≤ Jlo → Jlo + 3 * M ≤ X →
      ∀ ρ ∈ D,
        ∃ u ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
        ∃ v ∈ residueBlockFinset M ({ρ} : Finset (ZMod M)) Jlo (Jlo + 3 * M),
          u ≠ v ∧ u ∈ S ∧ v ∈ S
  reservoir_long : H + 3 * M ≤ X
  headroom : H + X + 3 * M ≤ R
  coverage : ∀ n, coverStart ≤ n → n ≤ R → n ∈ twoFoldFinset S
  exists_dormant : ∃ b ∈ S, b ∉ P

namespace StageState

theorem active_mem_state (st : StageState) {a : ℕ} (ha : a ∈ st.P) : a ∈ st.S :=
  st.P_subset_S ha

theorem active_le_X (st : StageState) {a : ℕ} (ha : a ∈ st.P) : a ≤ st.X :=
  st.S_le_X a (st.active_mem_state ha)

theorem modulus_pos (st : StageState) {a : ℕ} (ha : a ∈ st.P) : 0 < st.m a :=
  (st.m_prime a ha).pos

theorem D_nat_avoid (st : StageState) :
    ∀ c ∈ st.P, ∀ n : ℕ, (n : ZMod st.M) ∈ st.D →
      (n : ZMod (st.m c)) ≠ (c : ZMod (st.m c)) := by
  intro c hc n hnD hncong
  have hdiv : st.m c ∣ st.M := by
    rw [st.M_def]
    exact Finset.dvd_prod_of_mem st.m hc
  obtain ⟨u, huBlock, v, hvBlock, huv, huS, hvS⟩ :=
    st.reservoir_multiplicity st.H le_rfl st.reservoir_long (n : ZMod st.M) hnD
  rw [mem_residueBlockFinset] at huBlock hvBlock
  have huM : (u : ZMod st.M) = (n : ZMod st.M) := by
    simpa using huBlock.2.2
  have hvM : (v : ZMod st.M) = (n : ZMod st.M) := by
    simpa using hvBlock.2.2
  have huC : (u : ZMod (st.m c)) = (c : ZMod (st.m c)) := by
    have hmap : (u : ZMod (st.m c)) = (n : ZMod (st.m c)) := by
      simpa [ZMod.castHom_apply, ZMod.cast_natCast] using
        congrArg (ZMod.castHom hdiv (ZMod (st.m c))) huM
    exact hmap.trans hncong
  have hvC : (v : ZMod (st.m c)) = (c : ZMod (st.m c)) := by
    have hmap : (v : ZMod (st.m c)) = (n : ZMod (st.m c)) := by
      simpa [ZMod.castHom_apply, ZMod.cast_natCast] using
        congrArg (ZMod.castHom hdiv (ZMod (st.m c))) hvM
    exact hmap.trans hncong
  have hu_eq : u = c := st.isolated c hc u huS huC
  have hv_eq : v = c := st.isolated c hc v hvS hvC
  exact huv (hu_eq.trans hv_eq.symm)

end StageState

/-- Abstract certificate that one finite stage extends another. -/
structure StageExtension (st st' : StageState) where
  S_subset : st.S ⊆ st'.S
  P_subset : st.P ⊆ st'.P
  m_eq_on_old : ∀ a ∈ st.P, st'.m a = st.m a
  coverStart_eq : st'.coverStart = st.coverStart
  X_mono : st.X ≤ st'.X
  R_mono : st.R ≤ st'.R
  new_elements_above_old_X :
    ∀ n ∈ st'.S, n ∉ st.S → st.X < n

namespace StageExtension

theorem old_coverage {st st' : StageState} (h : StageExtension st st')
    {n : ℕ} (hn_start : st.coverStart ≤ n) (hn_R : n ≤ st.R) :
    n ∈ twoFoldFinset st'.S :=
  twoFoldFinset_mono h.S_subset (st.coverage n hn_start hn_R)

end StageExtension

/-- A stage extension that services one active element and records a protected block. -/
structure ServiceExtension (st st' : StageState) (a : ℕ) where
  toStageExtension : StageExtension st st'
  served_active : a ∈ st.P
  protectedEndpoint : ℕ
  protectedEndpoint_le_X : protectedEndpoint ≤ st'.X
  protectedBlock : ProtectedBlockCertificate st'.S a protectedEndpoint

end Erdos330
