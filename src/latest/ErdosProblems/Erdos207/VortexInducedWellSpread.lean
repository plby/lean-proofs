/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexInducedCount

/-! # Well-spreadness of the absorber-induced forbidden family -/

namespace Erdos207

open Finset

noncomputable section

lemma absorberInduced_uniform
    {V : Type*} [Fintype V] [DecidableEq V] {q j : ℕ}
    {B : TripleSystemOn V} (S : TripleSystemOn V)
    (hS : S ∈ absorberInducedConfigurationsOn q j B) :
    S.card = j - 2 ∧ IsPackingOn S := by
  obtain ⟨hScard, rho, hrho5, _hrhoq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hS
  have hSE : S ⊆ E := by
    intro T hTS
    have hTdiff : T ∈ E \ B := by rw [hEout]; exact hTS
    exact (mem_sdiff.mp hTdiff).1
  exact ⟨hScard, (IsErdosConfig.isPackingOn hE hrho5).mono hSE⟩

/-- Equal-remainder pairs inject into the first profiled singleton-extension
family. -/
lemma card_profiledEqualRemainderPairs_le_extensions
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (T T' : TripleOn V) (t : VortexProfile ell) :
    (W.profiledEqualRemainderPairs F T T' t).card ≤
      (W.profiledExtensions F {T} t).card := by
  let pairs := W.profiledEqualRemainderPairs F T T' t
  let exts := W.profiledExtensions F {T} t
  apply Finset.card_le_card_of_injOn (fun p ↦ p.1)
  · intro p hp
    have hm := W.mem_profiledEqualRemainderPairs_iff F T T' t p |>.mp hp
    apply W.mem_profiledExtensions_iff F {T} t p.1 |>.mpr
    refine ⟨hm.1, ?_, ?_⟩
    · simpa using hm.2.2.1
    · simpa only [sdiff_singleton_eq_erase] using hm.2.2.2.2.2
  · intro p hp p' hp' hfirst
    change p.1 = p'.1 at hfirst
    apply Prod.ext hfirst
    rcases W.mem_profiledEqualRemainderPairs_iff F T T' t p |>.mp hp with
      ⟨_hpF, _hp2F, _hTp, hT'p2, hrem, _hprof⟩
    rcases W.mem_profiledEqualRemainderPairs_iff F T T' t p' |>.mp hp' with
      ⟨_hp'F, _hp'2F, _hTp', hT'p'2, hrem', _hprof'⟩
    have herase : p.2.erase T' = p'.2.erase T' := by
      rw [← hrem, ← hrem', hfirst]
    calc
      p.2 = insert T' (p.2.erase T') := (insert_erase hT'p2).symm
      _ = insert T' (p'.2.erase T') := by rw [herase]
      _ = p'.2 := insert_erase hT'p'2

lemma card_profiledEqualRemainderPairs_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V)
    (T T' : TripleOn V) (t : VortexProfile ell)
    (hj : 3 ≤ j) (hterminal : 0 < W.terminalSize) :
    (W.profiledEqualRemainderPairs
        (absorberInducedConfigurationsOn q j B) T T' t).card ≤
      (inducedVortexCoefficient q ell B * W.terminalSize) *
        W.terminalSize ^ (j - t.mass - 4) * W.profileScale t := by
  have hsingle := card_profiledExtensions_absorberInduced_le
    (q := q) W B {T} t hj (by simp) (by simp; omega) hterminal
  have hbase : 1 ≤ W.terminalSize := by omega
  let a := j - t.mass - 3
  let b := j - t.mass - 4
  have hab : a ≤ b + 1 := by dsimp only [a, b]; omega
  have hpow : W.terminalSize ^ a ≤ W.terminalSize ^ (b + 1) :=
    pow_le_pow_right₀ hbase hab
  calc
    (W.profiledEqualRemainderPairs
        (absorberInducedConfigurationsOn q j B) T T' t).card ≤
        (W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) {T} t).card :=
      card_profiledEqualRemainderPairs_le_extensions W _ T T' t
    _ ≤ inducedVortexCoefficient q ell B *
        W.terminalSize ^ (j - t.mass - vortexRootExponent j 1) *
        W.profileScale t := hsingle
    _ = inducedVortexCoefficient q ell B *
        W.terminalSize ^ a * W.profileScale t := by
      simp only [vortexRootExponent_one, a]
    _ ≤ inducedVortexCoefficient q ell B *
        W.terminalSize ^ (b + 1) * W.profileScale t := by gcongr
    _ = (inducedVortexCoefficient q ell B * W.terminalSize) *
        W.terminalSize ^ (j - t.mass - 4) * W.profileScale t := by
      rw [pow_succ]
      dsimp only [b]
      ring

/-- An order-four terminal-pair extension is determined by its other
triangle, which lies completely in the terminal vortex set. -/
lemma card_terminalPairExtensions_le_terminal_cube
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (hcard : ∀ E ∈ F, E.card = 2)
    (T : TripleOn V) (P : VortexPairOn V) :
    (W.terminalPairExtensions F T P).card ≤ W.terminalSize ^ 3 := by
  let G := W.terminalPairExtensions F T P
  let other : G → TripleOn V := fun E ↦ Classical.choose (card_eq_one.mp (by
    have hm := W.mem_terminalPairExtensions_iff F T P E.1 |>.mp E.2
    rw [card_erase_of_mem hm.2.1, hcard E.1 hm.1]))
  have hotherSet : ∀ E : G, E.1.erase T = {other E} := by
    intro E
    exact Classical.choose_spec (card_eq_one.mp (by
      have hm := W.mem_terminalPairExtensions_iff F T P E.1 |>.mp E.2
      rw [card_erase_of_mem hm.2.1, hcard E.1 hm.1]))
  have hotherMem : ∀ E : G, other E ∈ E.1.erase T := by
    intro E
    rw [hotherSet E]
    simp
  let pick : G → triplesSupportedOn (W.U (Fin.last ell)) := fun E ↦ by
    have hm := W.mem_terminalPairExtensions_iff F T P E.1 |>.mp E.2
    refine ⟨other E, ?_⟩
    apply mem_triplesSupportedOn_iff.mpr
    let D₀ := hm.2.2.choose
    have hD₀mem := hm.2.2.choose_spec.1
    have hD₀eq : D₀ = other E := by
      have hsingle : D₀ ∈ ({other E} : Finset (TripleOn V)) := by
        apply (show E.1.erase T ⊆ {other E} by rw [hotherSet E])
        exact hD₀mem
      exact mem_singleton.mp hsingle
    have hD₀level := hm.2.2.choose_spec.2.1
    change W.level D₀ = Fin.last ell at hD₀level
    rw [← hD₀eq]
    simpa only [hD₀level] using W.subset_at_level D₀
  have hpick : Function.Injective pick := by
    intro E E' hEE'
    apply Subtype.ext
    have hm := W.mem_terminalPairExtensions_iff F T P E.1 |>.mp E.2
    have hm' := W.mem_terminalPairExtensions_iff F T P E'.1 |>.mp E'.2
    have hD : other E = other E' := by
      have h := congrArg (fun D : triplesSupportedOn
        (W.U (Fin.last ell)) ↦ D.1) hEE'
      change other E = other E' at h
      exact h
    have hErase : E.1.erase T = E'.1.erase T := by
      rw [hotherSet E, hotherSet E', hD]
    calc
      E.1 = insert T (E.1.erase T) := (insert_erase hm.2.1).symm
      _ = insert T (E'.1.erase T) := by rw [hErase]
      _ = E'.1 := insert_erase hm'.2.1
  calc
    G.card = Fintype.card G := (Fintype.card_coe G).symm
    _ ≤ Fintype.card (triplesSupportedOn (W.U (Fin.last ell))) :=
      Fintype.card_le_of_injective pick hpick
    _ = (triplesSupportedOn (W.U (Fin.last ell))).card :=
      Fintype.card_coe _
    _ ≤ (W.U (Fin.last ell)).card ^ 3 :=
      card_triplesSupportedOn_le_cube _
    _ = W.terminalSize ^ 3 := rfl

/-- A coarse but fully finite version of KSSS Lemma 7.2.  Its coefficient is
constant whenever the absorber bank and terminal set are fixed. -/
theorem absorberInduced_vortexWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V)
    (hj : 3 ≤ j) (hterminal : 0 < W.terminalSize) :
    VortexWellSpread W j (absorberInducedConfigurationsOn q j B)
      (inducedVortexCoefficient q ell B)
      (inducedVortexCoefficient q ell B * W.terminalSize +
        W.terminalSize ^ 3) := by
  let c := inducedVortexCoefficient q ell B
  let z := c * W.terminalSize + W.terminalSize ^ 3
  have hc_le_z : c ≤ z := by
    have hN : 1 ≤ W.terminalSize := by omega
    calc
      c ≤ c * W.terminalSize := Nat.le_mul_of_pos_right c hterminal
      _ ≤ z := Nat.le_add_right _ _
  refine ⟨absorberInduced_uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    exact (card_profiledExtensions_absorberInduced_le
      W B R t hj hR hRcard hterminal).trans (by gcongr)
  · intro T T' t
    exact (card_profiledEqualRemainderPairs_absorberInduced_le
      W B T T' t hj hterminal).trans (by
        gcongr
        exact Nat.le_add_right _ _)
  · intro hj4 T P _hPT
    have hc := card_terminalPairExtensions_le_terminal_cube W
      (absorberInducedConfigurationsOn q j B)
      (fun E hE ↦ by
        have := (absorberInduced_uniform E hE).1
        omega) T P
    exact hc.trans (by
      exact Nat.le_add_left _ _)
  · intro T t
    exact card_profiledExtensions_absorberInduced_le
      W B {T} t hj (by simp) (by simp; omega) hterminal

end

end Erdos207
