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
import ErdosProblems.Erdos330.StageConstruction

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
# Initial state for Erdős Problem 330

This file constructs the one-active-element reservoir state used to start the
priority construction.  The numeric parameters are kept explicit: later global
construction code can choose any sufficiently large `H` and `X`.
-/

namespace Erdos330

open scoped Pointwise

/-- The allowed residues for a one-element active set. -/
def initialAllowed (m a : ℕ) [NeZero m] : Finset (ZMod m) :=
  (Finset.univ : Finset (ZMod m)).erase (a : ZMod m)

theorem mem_initialAllowed {m a : ℕ} [NeZero m] {x : ZMod m} :
    x ∈ initialAllowed m a ↔ x ≠ (a : ZMod m) := by
  rw [initialAllowed, Finset.mem_erase]
  simp

theorem initialAllowed_add_self_eq_univ (m a : ℕ) [NeZero m] (hm3 : 3 ≤ m) :
    ((initialAllowed m a : Set (ZMod m)) +
      (initialAllowed m a : Set (ZMod m))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  let α : ZMod m := (a : ZMod m)
  let bad : Finset (ZMod m) := {α, z - α}
  have hbad_card : bad.card ≤ 2 := by
    calc
      bad.card ≤ ({z - α} : Finset (ZMod m)).card + 1 := Finset.card_insert_le α {z - α}
      _ = 2 := by simp
  have huniv_card : (Finset.univ : Finset (ZMod m)).card = m := by
    rw [Finset.card_univ, ZMod.card]
  have hbad_lt : bad.card < (Finset.univ : Finset (ZMod m)).card := by
    rw [huniv_card]
    omega
  obtain ⟨x, _hx_univ, hx_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
  have hx_ne : x ≠ α := by
    intro hx
    exact hx_bad (by simp [bad, hx])
  have hy_ne : z - x ≠ α := by
    intro hy
    have hx_eq : x = z - α := by
      rw [← hy]
      abel
    exact hx_bad (by simp [bad, hx_eq])
  refine ⟨x, ?_, z - x, ?_, ?_⟩
  · exact (mem_initialAllowed.mpr hx_ne : x ∈ (initialAllowed m a : Set (ZMod m)))
  · exact (mem_initialAllowed.mpr hy_ne : z - x ∈ (initialAllowed m a : Set (ZMod m)))
  · abel_nf

/-- The finite set of the initial state. -/
def initialS (a m H X : ℕ) [NeZero m] : Finset ℕ :=
  insert a (residueBlockFinset m (initialAllowed m a) H X)

/--
Construct an initial stage with one active element `a`, personal modulus `m`,
and a long reservoir `[H,X]` avoiding `a mod m`.

The condition `H + 4*m ≤ X` supplies both the reservoir multiplicity and the
initial headroom required by `StageState`.
-/
noncomputable def initialStageState (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) : StageState := by
  classical
  letI : NeZero m := NeZero.of_pos hmPrime.pos
  let D : Finset (ZMod m) := initialAllowed m a
  let S : Finset ℕ := initialS a m H X
  exact {
    S := S
    P := {a}
    m := fun _ => m
    M := m
    D := D
    H := H
    X := X
    R := 2 * X - m
    coverStart := 2 * H + m
    P_subset_S := by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst s
      exact Finset.mem_insert_self a (residueBlockFinset m D H X)
    S_le_X := by
      intro s hs
      simp [S, initialS] at hs
      rcases hs with rfl | hsBlock
      · exact haX
      · rw [mem_residueBlockFinset] at hsBlock
        exact hsBlock.2.1
    m_prime := by
      intro s _hs
      exact hmPrime
    m_ge23 := by
      intro s _hs
      exact hm23
    m_mod4 := by
      intro s _hs
      exact hmMod4
    m_pairwise_coprime := by
      intro s hs t ht hst
      simp at hs ht
      subst s
      subst t
      exact (hst rfl).elim
    M_def := by
      simp
    isolated := by
      intro c hc s hs hcong
      simp at hc
      subst c
      simp [S, initialS] at hs
      rcases hs with rfl | hsBlock
      · rfl
      · rw [mem_residueBlockFinset] at hsBlock
        have hsAvoid : (s : ZMod m) ≠ (a : ZMod m) :=
          mem_initialAllowed.mp hsBlock.2.2
        exact (hsAvoid hcong).elim
    reservoir_subset := by
      intro n hn
      exact Finset.mem_insert_of_mem hn
    reservoir_multiplicity := by
      intro Jlo hJlo hJhi ρ hρ
      obtain ⟨u, huBlock, v, hvBlock, huv⟩ :=
        exists_two_in_residueBlock_triple_window m Jlo ρ
      have huS : u ∈ S := by
        simp [S, initialS]
        right
        rw [mem_residueBlockFinset] at huBlock ⊢
        have huρ : (u : ZMod m) = ρ := by simpa using huBlock.2.2
        exact ⟨hJlo.trans huBlock.1, huBlock.2.1.trans hJhi,
          by simpa [huρ] using hρ⟩
      have hvS : v ∈ S := by
        simp [S, initialS]
        right
        rw [mem_residueBlockFinset] at hvBlock ⊢
        have hvρ : (v : ZMod m) = ρ := by simpa using hvBlock.2.2
        exact ⟨hJlo.trans hvBlock.1, hvBlock.2.1.trans hJhi,
          by simpa [hvρ] using hρ⟩
      exact ⟨u, huBlock, v, hvBlock, huv, huS, hvS⟩
    reservoir_long := by
      omega
    headroom := by
      omega
    coverage := by
      intro n hn_start hn_end
      have hHX : H ≤ X := by omega
      have hblock : n ∈ twoFoldFinset (residueBlockFinset m D H X) := by
        have hmiddle : n ∈
            twoFoldFinset (residueBlockFinset m D H (H + (X - H))) := by
          refine residueBlock_middle_cover_of_add_univ D
            (initialAllowed_add_self_eq_univ m a (by omega)) ?_ ?_ ?_
          · omega
          · exact hn_start
          · omega
        simpa [Nat.add_sub_of_le hHX] using hmiddle
      exact twoFoldFinset_mono (by
        intro s hs
        exact Finset.mem_insert_of_mem hs) hblock
    exists_dormant := by
      let ρ : ZMod m := (a + 1 : ℕ)
      have hρ_ne : ρ ≠ (a : ZMod m) := by
        intro hρ
        have hsucc : (a : ZMod m) + 1 = (a : ZMod m) := by
          simpa [ρ, Nat.cast_add] using hρ
        have hone_zero : (1 : ZMod m) = 0 := by
          calc
            (1 : ZMod m) = ((a : ZMod m) + 1) - (a : ZMod m) := by abel
            _ = (a : ZMod m) - (a : ZMod m) := by rw [hsucc]
            _ = 0 := by abel
        have hone_ne : ((1 : ℕ) : ZMod m) ≠ 0 :=
          zmod_natCast_ne_zero_of_pos_lt (by omega) hmPrime.one_lt
        exact hone_ne (by simpa using hone_zero)
      have hρD : ρ ∈ D := mem_initialAllowed.mpr hρ_ne
      obtain ⟨x, hxlo, hxhi, hxρ⟩ := exists_natCast_eq_zmod_in_Icc_len m H ρ
      have hxS : x ∈ S := by
        simp [S, initialS]
        right
        rw [mem_residueBlockFinset]
        exact ⟨hxlo, hxhi.trans (by omega), by simpa [hxρ] using hρD⟩
      have hxDormant : x ∉ ({a} : Finset ℕ) := by
        intro hxP
        have hxa : x = a := by simpa using hxP
        apply hρ_ne
        rw [← hxρ, hxa]
      exact ⟨x, hxS, hxDormant⟩
  }

theorem initialStageState_active (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) :
    (initialStageState a m H X hmPrime hm23 hmMod4 haX hlong).P = {a} := by
  rfl

theorem initialStageState_hasCanonicalD (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) :
    (initialStageState a m H X hmPrime hm23 hmMod4 haX hlong).HasCanonicalD := by
  classical
  let : NeZero m := NeZero.of_pos hmPrime.pos
  let st := initialStageState a m H X hmPrime hm23 hmMod4 haX hlong
  intro c hc
  have hc_eq : c = a := by
    simpa [st, initialStageState_active a m H X hmPrime hm23 hmMod4 haX hlong] using hc
  subst c
  have haP : a ∈ st.P := by
    simp [st, initialStageState_active a m H X hmPrime hm23 hmMod4 haX hlong]
  let : NeZero st.M := by
    change NeZero m
    infer_instance
  ext z
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [natCast_mem_stageCRTAllowedFinsetAtM_iff st haP]
  change (n : ZMod m) ∈ initialAllowed m a ↔
    (n : ZMod m) ≠ (a : ZMod m) ∧
      ∀ i : NonselectedIndex ({a} : Finset ℕ) a,
        (n : ZMod m) ≠ ((i : ℕ) : ZMod m)
  constructor
  · intro hn
    refine ⟨mem_initialAllowed.mp hn, ?_⟩
    intro i
    rcases Finset.mem_erase.mp i.property with ⟨hia, hiP⟩
    simp at hiP
    exact (hia hiP).elim
  · intro hn
    exact mem_initialAllowed.mpr hn.1

theorem exists_initialStageState :
    ∃ st : StageState, st.HasCanonicalD := by
  obtain ⟨m, hm23, hmPrime, hmMod4⟩ := exists_prime_three_mod_four_ge 23
  let H := m + 2
  let X := H + 4 * m
  refine ⟨initialStageState 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega), ?_⟩
  exact initialStageState_hasCanonicalD 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega)

end Erdos330
