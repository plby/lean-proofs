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
import ErdosProblems.Erdos330.Stage

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
# Local reservoir lemmas for Erdős Problem 330

These lemmas are the first stage-construction bridge between the finite CRT
gadget and the stored reservoir invariant.  They show how `D + T = univ`
and the two-helper reservoir multiplicity produce actual old helpers from
the finite set `S`.
-/

namespace Erdos330

open scoped Pointwise

lemma nat_eq_of_zmod_eq_of_le_lt {p X u v : ℕ}
    (huX : u ≤ X) (hvX : v ≤ X) (hXp : X < p)
    (huv : (u : ZMod p) = (v : ZMod p)) : u = v := by
  have hmod : u ≡ v [MOD p] := (ZMod.natCast_eq_natCast_iff u v p).mp huv
  exact hmod.eq_of_lt_of_lt (lt_of_le_of_lt huX hXp) (lt_of_le_of_lt hvX hXp)

lemma exists_reservoir_helper_avoiding_zmod (st : StageState)
    {Jlo p : ℕ} [NeZero p] {ρ : ZMod st.M} (hρ : ρ ∈ st.D)
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod p) :
    ∃ u : ℕ,
      u ∈ residueBlockFinset st.M ({ρ} : Finset (ZMod st.M)) Jlo (Jlo + 3 * st.M) ∧
      u ∈ st.S ∧ (u : ZMod p) ≠ forbidden := by
  obtain ⟨u, huBlock, v, hvBlock, huv_ne, huS, hvS⟩ :=
    st.reservoir_multiplicity Jlo hJlo hJhi ρ hρ
  have huX : u ≤ st.X := by
    rw [mem_residueBlockFinset] at huBlock
    exact huBlock.2.1.trans hJhi
  have hvX : v ≤ st.X := by
    rw [mem_residueBlockFinset] at hvBlock
    exact hvBlock.2.1.trans hJhi
  by_cases hu_forbid : (u : ZMod p) = forbidden
  · refine ⟨v, hvBlock, hvS, ?_⟩
    intro hv_forbid
    apply huv_ne
    exact nat_eq_of_zmod_eq_of_le_lt huX hvX hpX (hu_forbid.trans hv_forbid.symm)
  · exact ⟨u, huBlock, huS, hu_forbid⟩

lemma exists_reservoir_helper_satisfying_of_residue_avoid (st : StageState)
    {Jlo p : ℕ} [NeZero p]
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod p) {Q : ℕ → Prop}
    (hQ : ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ → (u : ZMod p) ≠ forbidden → Q u) :
    ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧ Q u := by
  rcases hQ with ⟨ρ, hρ, hQρ⟩
  obtain ⟨u, huBlock, huS, huAvoid⟩ :=
    exists_reservoir_helper_avoiding_zmod st hρ hJlo hJhi hpX forbidden
  rw [mem_residueBlockFinset] at huBlock
  refine ⟨u, huS, huBlock.1, huBlock.2.1, ?_⟩
  exact hQρ u (by simpa using huBlock.2.2) huAvoid

lemma exists_reservoir_helper_for_target_from_old_residue_lift (st : StageState)
    {Jlo p Mplus : ℕ} [NeZero p]
    (Ω : Finset (ZMod Mplus))
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod Mplus → ZMod p)
    (hchoose : ∀ γ : ZMod Mplus, ∃ ρ ∈ st.D, ∀ u : ℕ,
      (u : ZMod st.M) = ρ → (u : ZMod p) ≠ forbidden γ →
        γ - (u : ZMod Mplus) ∈ Ω) :
    ∀ γ : ZMod Mplus,
      ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
        γ - (u : ZMod Mplus) ∈ Ω := by
  intro γ
  exact exists_reservoir_helper_satisfying_of_residue_avoid st hJlo hJhi hpX
    (forbidden γ) (hchoose γ)

lemma exists_helper_window (H X N L C n : ℕ)
    (hHCX : H + C ≤ X) (hCL : C ≤ L)
    (hnlo : H + N + C ≤ n) (hnhi : n + C ≤ X + N + L) :
    ∃ Jlo : ℕ, H ≤ Jlo ∧ Jlo + C ≤ X ∧
      n - (N + L) ≤ Jlo ∧ Jlo + C ≤ n - N := by
  refine ⟨max H (n - (N + L)), ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · omega
  · exact le_max_right _ _
  · omega

lemma exists_reservoir_helper_for_gadget_in_window (st : StageState) {a Jlo : ℕ}
    (G : CRTGadget st.P st.m st.M a st.D)
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
      γ - (u : ZMod st.M) ∈ G.T := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.D_add_T_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, _v, _hvBlock, _hne, huS, _hvS⟩ :=
    st.reservoir_multiplicity Jlo hJlo hJhi ρ hρ
  rw [mem_residueBlockFinset] at huBlock
  refine ⟨u, huS, huBlock.1, huBlock.2.1, ?_⟩
  have huρ : (u : ZMod st.M) = ρ := by simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

lemma exists_reservoir_helper_for_gadget_base_avoiding_in_window (st : StageState)
    {a Jlo p : ℕ} [NeZero p]
    (G : CRTGadget st.P st.m st.M a st.D)
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod p) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
      γ - (u : ZMod st.M) ∈ G.Tbase ∧ (u : ZMod p) ≠ forbidden := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.Tbase : Set (ZMod st.M)) := by
    rw [G.D_add_Tbase_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, huS, hup⟩ :=
    exists_reservoir_helper_avoiding_zmod st hρ hJlo hJhi hpX forbidden
  rw [mem_residueBlockFinset] at huBlock
  refine ⟨u, huS, huBlock.1, huBlock.2.1, ?_, hup⟩
  have huρ : (u : ZMod st.M) = ρ := by
    simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

lemma exists_reservoir_helper_for_gadget_avoiding_in_window (st : StageState)
    {a Jlo p : ℕ} [NeZero p]
    (G : CRTGadget st.P st.m st.M a st.D)
    (hJlo : st.H ≤ Jlo) (hJhi : Jlo + 3 * st.M ≤ st.X)
    (hpX : st.X < p) (forbidden : ZMod p) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ Jlo ≤ u ∧ u ≤ Jlo + 3 * st.M ∧
      γ - (u : ZMod st.M) ∈ G.T ∧ (u : ZMod p) ≠ forbidden := by
  obtain ⟨u, huS, huLo, huHi, huBase, hup⟩ :=
    exists_reservoir_helper_for_gadget_base_avoiding_in_window st G hJlo hJhi hpX
      forbidden γ
  exact ⟨u, huS, huLo, huHi, G.Tbase_subset_T huBase, hup⟩

theorem exists_reservoir_helper_for_gadget (st : StageState) {a : ℕ}
    (G : CRTGadget st.P st.m st.M a st.D) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ γ - (u : ZMod st.M) ∈ G.T := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.D_add_T_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, _v, _hvBlock, _hne, huS, _hvS⟩ :=
    st.reservoir_multiplicity st.H (le_rfl) st.reservoir_long ρ hρ
  refine ⟨u, huS, ?_⟩
  rw [mem_residueBlockFinset] at huBlock
  have huρ : (u : ZMod st.M) = ρ := by simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

theorem residueBlock_helper_cover (M H X N L C : ℕ) (Ω : Finset (ZMod M))
    (S : Finset ℕ)
    (hhelper : ∀ Jlo, H ≤ Jlo → Jlo + C ≤ X → ∀ γ : ZMod M,
      ∃ u : ℕ, u ∈ S ∧ Jlo ≤ u ∧ u ≤ Jlo + C ∧ γ - (u : ZMod M) ∈ Ω)
    (hHCX : H + C ≤ X) (hCL : C ≤ L) {n : ℕ}
    (hnlo : H + N + C ≤ n) (hnhi : n + C ≤ X + N + L) :
    n ∈ twoFoldFinset (S ∪ residueBlockFinset M Ω N (N + L)) := by
  obtain ⟨Jlo, hJlo, hJhi, _hJlow, _hJn⟩ :=
    exists_helper_window H X N L C n hHCX hCL hnlo hnhi
  obtain ⟨u, huS, huJlo, huJhi, huΩ⟩ := hhelper Jlo hJlo hJhi (n : ZMod M)
  have hu_le_n : u ≤ n := by omega
  have hN : N ≤ n - u := by omega
  have hNL : n - u ≤ N + L := by omega
  have hcast : ((n - u : ℕ) : ZMod M) = (n : ZMod M) - (u : ZMod M) := by
    rw [Nat.cast_sub hu_le_n]
  have hyΩ : ((n - u : ℕ) : ZMod M) ∈ Ω := by
    rwa [hcast]
  have hyBlock : n - u ∈ residueBlockFinset M Ω N (N + L) := by
    rw [mem_residueBlockFinset]
    exact ⟨hN, hNL, hyΩ⟩
  refine ⟨u, Finset.mem_union.mpr (Or.inl huS), n - u,
    Finset.mem_union.mpr (Or.inr hyBlock), ?_⟩
  omega

theorem gadget_residueBlock_cover (st : StageState) {a N L n : ℕ}
    (G : CRTGadget st.P st.m st.M a st.D)
    (hCL : 3 * st.M ≤ L)
    (hnlo : st.H + N + 3 * st.M ≤ n)
    (hnhi : n + 3 * st.M ≤ st.X + N + L) :
    n ∈ twoFoldFinset (st.S ∪ residueBlockFinset st.M G.T N (N + L)) := by
  refine residueBlock_helper_cover st.M st.H st.X N L (3 * st.M) G.T st.S ?_
    st.reservoir_long hCL hnlo hnhi
  intro Jlo hJlo hJhi γ
  exact exists_reservoir_helper_for_gadget_in_window st G hJlo hJhi γ

theorem gadget_T_middle_residueBlock_cover (st : StageState) {a N L n : ℕ}
    [NeZero st.M] (G : CRTGadget st.P st.m st.M a st.D)
    (hML : st.M ≤ L) (hnlo : 2 * N + st.M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - st.M)
    (hnot_private : (n : ZMod st.M) ∉
      ((fun x : ZMod st.M => (a : ZMod st.M) + x) '' (G.Pstar : Set (ZMod st.M)))) :
    n ∈ twoFoldFinset (residueBlockFinset st.M G.T N (N + L)) := by
  have hres : (n : ZMod st.M) ∈
      (G.T : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.T_add_T_compl_private]
    exact ⟨Set.mem_univ _, hnot_private⟩
  exact residueBlockFinset_middle_mem_twoFold_self (M := st.M) (N := N) (L := L)
    (n := n) hML hnlo hnhi hres

theorem exists_reservoir_helper_for_gadget_avoiding (st : StageState) {a p : ℕ}
    [NeZero p] (G : CRTGadget st.P st.m st.M a st.D)
    (hpX : st.X < p) (forbidden : ZMod p) (γ : ZMod st.M) :
    ∃ u : ℕ, u ∈ st.S ∧ γ - (u : ZMod st.M) ∈ G.T ∧
      (u : ZMod p) ≠ forbidden := by
  classical
  have hγ : γ ∈ (st.D : Set (ZMod st.M)) + (G.T : Set (ZMod st.M)) := by
    rw [G.D_add_T_full]
    exact Set.mem_univ γ
  rcases hγ with ⟨ρ, hρ, t, ht, hsum⟩
  obtain ⟨u, huBlock, huS, hup⟩ :=
    exists_reservoir_helper_avoiding_zmod st hρ (Jlo := st.H) (le_rfl) st.reservoir_long
      hpX forbidden
  refine ⟨u, huS, ?_, hup⟩
  rw [mem_residueBlockFinset] at huBlock
  have huρ : (u : ZMod st.M) = ρ := by simpa using huBlock.2.2
  have hdiff : γ - (u : ZMod st.M) = t := by
    rw [huρ, ← hsum]
    ring
  rwa [hdiff]

end Erdos330
