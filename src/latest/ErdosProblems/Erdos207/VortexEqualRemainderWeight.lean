/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexSharpWeight
import ErdosProblems.Erdos207.VortexInducedWellSpread

/-!
# Weighted equal-remainder collisions along a vortex

Condition W2 bounds pairs of forbidden configurations which become equal
after deleting distinguished triangles.  This file converts its finite
profile count into the level-weighted collision estimate used by the
second-moment argument.  Crucially, all `r - 3` density factors survive.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The level-weighted W2 collision sum for two distinguished triangles.
Every pair in the profiled class has the same remainder weight. -/
def vortexEqualRemainderWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (r : ℕ)
    (c : ℝ≥0) (T T' : TripleOn V) : ℝ≥0 :=
  ∑ t ∈ W.rootProfileSupport F {T},
    ((W.profiledEqualRemainderPairs F T T' t).card : ℝ≥0) *
      vortexProfileWeight W c (r - 3) t

/-- One W2 profile contributes at most `z * c^(r-3)`.  The terminal
denominator dominates the (possibly truncated) terminal power in W2, while
the outer profile scale cancels exactly. -/
theorem vortexEqualRemainder_profileTerm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r z : ℕ} (W : Vortex V ell) (c : ℝ≥0)
    (t : VortexProfile ell) (hmass : t.mass ≤ r - 3)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) :
    (((z * W.terminalSize ^ (r - t.mass - 4) *
          W.profileScale t : ℕ) : ℝ≥0) *
        vortexProfileWeight W c (r - 3) t) ≤
      (z : ℝ≥0) * c ^ (r - 3) := by
  let a := r - t.mass - 4
  let b := r - 3 - t.mass
  have hab : a ≤ b := by
    dsimp only [a, b]
    omega
  have hN : (1 : ℝ≥0) ≤ W.terminalSize := by
    exact_mod_cast hterminal
  have hterminalFactor :
      (W.terminalSize : ℝ≥0) ^ a *
          (c / (W.terminalSize : ℝ≥0)) ^ b ≤ c ^ b := by
    calc
      (W.terminalSize : ℝ≥0) ^ a *
            (c / (W.terminalSize : ℝ≥0)) ^ b =
          c ^ b * ((W.terminalSize : ℝ≥0) ^ a *
            (1 / (W.terminalSize : ℝ≥0)) ^ b) := by
        rw [div_eq_mul_inv, mul_pow]
        simp only [one_div]
        ring
      _ ≤ c ^ b * 1 := by
        gcongr
        exact nnreal_pow_mul_one_div_pow_le_one _ hN hab
      _ = c ^ b := by simp
  unfold vortexProfileWeight
  push_cast
  rw [show r - t.mass - 4 = a by rfl,
    show r - 3 - t.mass = b by rfl]
  calc
    (z : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ a *
          (W.profileScale t : ℝ≥0) *
          ((∏ i : Fin ell,
              (c / (W.U i.castSucc).card) ^ t i) *
            (c / W.terminalSize) ^ b) =
        (z : ℝ≥0) *
          ((W.profileScale t : ℝ≥0) *
            ∏ i : Fin ell,
              (c / (W.U i.castSucc).card) ^ t i) *
          ((W.terminalSize : ℝ≥0) ^ a *
            (c / W.terminalSize) ^ b) := by ring
    _ = (z : ℝ≥0) * c ^ t.mass *
          ((W.terminalSize : ℝ≥0) ^ a *
            (c / W.terminalSize) ^ b) := by
      rw [W.profileScale_mul_outerWeight c t houter]
    _ ≤ (z : ℝ≥0) * c ^ t.mass * c ^ b := by gcongr
    _ = (z : ℝ≥0) * c ^ (r - 3) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hmass]

/-- If the common remainder contains a terminal-level triangle, the extra
factor of the terminal size in the W2 coefficient cancels as well.  This is
the sharp form used for absorber-induced families, whose direct W2 count has
coefficient `z * terminalSize`. -/
theorem vortexEqualRemainder_terminal_profileTerm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r z : ℕ} (W : Vortex V ell) (c : ℝ≥0)
    (t : VortexProfile ell) (hmass : t.mass < r - 3)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) :
    (((z * W.terminalSize) *
          W.terminalSize ^ (r - t.mass - 4) *
          W.profileScale t : ℕ) : ℝ≥0) *
        vortexProfileWeight W c (r - 3) t ≤
      (z : ℝ≥0) * c ^ (r - 3) := by
  have hmass_le : t.mass ≤ r - 3 := Nat.le_of_lt hmass
  have hexp : r - 3 - t.mass = r - t.mass - 4 + 1 := by omega
  have hcoeff :
      (z * W.terminalSize) *
          W.terminalSize ^ (r - t.mass - 4) * W.profileScale t =
        z * W.terminalSize ^ (r - 3 - t.mass) * W.profileScale t := by
    rw [hexp, pow_succ]
    ring
  rw [hcoeff]
  exact le_of_eq
    (vortexProfileScaleWeight_eq W c t hmass_le houter hterminal)

/-- The terminal-supported part of the W2 collision sum.  Profiles with
`mass < r-3` are precisely those whose common remainder has at least one
terminal-level triangle. -/
def vortexTerminalEqualRemainderWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (r : ℕ)
    (c : ℝ≥0) (T T' : TripleOn V) : ℝ≥0 :=
  ∑ t ∈ (W.rootProfileSupport F {T}).filter (fun t ↦ t.mass < r - 3),
    ((W.profiledEqualRemainderPairs F T T' t).card : ℝ≥0) *
      vortexProfileWeight W c (r - 3) t

/-- W2 gives a uniform weighted collision bound, with the complete phase
density saving and only the finite number of possible vortex profiles as
loss. -/
theorem VortexWellSpread.vortexEqualRemainderWeight_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0)
    (hr : 3 ≤ r)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T T' : TripleOn V) :
    vortexEqualRemainderWeight W F r c T T' ≤
      ((r + 1) ^ ell * z : ℝ≥0) * c ^ (r - 3) := by
  unfold vortexEqualRemainderWeight
  calc
    ∑ t ∈ W.rootProfileSupport F {T},
        ((W.profiledEqualRemainderPairs F T T' t).card : ℝ≥0) *
          vortexProfileWeight W c (r - 3) t ≤
      ∑ _t ∈ W.rootProfileSupport F {T},
        (z : ℝ≥0) * c ^ (r - 3) := by
      apply sum_le_sum
      intro t ht
      by_cases hpairs :
          (W.profiledEqualRemainderPairs F T T' t).Nonempty
      · obtain ⟨p, hp⟩ := hpairs
        have hm := W.mem_profiledEqualRemainderPairs_iff F T T' t p |>.mp hp
        have hcard : (p.1.erase T).card = r - 3 := by
          rw [card_erase_of_mem hm.2.2.1, (h.uniform p.1 hm.1).1]
          omega
        have hmass : t.mass ≤ r - 3 := by
          rw [← hm.2.2.2.2.2]
          exact (W.outerProfile_mass_le_card (p.1.erase T)).trans_eq hcard
        calc
          ((W.profiledEqualRemainderPairs F T T' t).card : ℝ≥0) *
                vortexProfileWeight W c (r - 3) t ≤
              (((z * W.terminalSize ^ (r - t.mass - 4) *
                    W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (r - 3) t) := by
            gcongr
            exact_mod_cast h.equal_remainders T T' t
          _ ≤ (z : ℝ≥0) * c ^ (r - 3) :=
            vortexEqualRemainder_profileTerm_le W c t hmass
              houter hterminal
      · rw [not_nonempty_iff_eq_empty.mp hpairs]
        simp
    _ = ((W.rootProfileSupport F {T}).card : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (r - 3)) := by simp
    _ ≤ (((r + 1) ^ ell : ℕ) : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (r - 3)) := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le F
        (fun E hEF ↦ (h.uniform E hEF).1) {T}
    _ = ((r + 1) ^ ell * z : ℝ≥0) * c ^ (r - 3) := by
      push_cast
      ring

/-- For one absorber-induced indexed family, the direct W2 coefficient is
`inducedVortexCoefficient * terminalSize`.  On terminal-supported profiles
the terminal factor cancels, leaving a coefficient independent of every
ambient vortex size. -/
theorem vortexTerminalEqualRemainderWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q j : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (c : ℝ≥0) (hj : 3 ≤ j)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T T' : TripleOn V) :
    vortexTerminalEqualRemainderWeight W
        (absorberInducedConfigurationsOn q j B) j c T T' ≤
      ((j + 1) ^ ell * inducedVortexCoefficient q ell B : ℝ≥0) *
        c ^ (j - 3) := by
  unfold vortexTerminalEqualRemainderWeight
  calc
    ∑ t ∈ (W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) {T}).filter
            (fun t ↦ t.mass < j - 3),
        ((W.profiledEqualRemainderPairs
          (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) *
          vortexProfileWeight W c (j - 3) t ≤
      ∑ _t ∈ (W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) {T}).filter
            (fun t ↦ t.mass < j - 3),
        (inducedVortexCoefficient q ell B : ℝ≥0) * c ^ (j - 3) := by
      apply sum_le_sum
      intro t ht
      have hmass : t.mass < j - 3 := (mem_filter.mp ht).2
      calc
        ((W.profiledEqualRemainderPairs
            (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) *
              vortexProfileWeight W c (j - 3) t ≤
            ((((inducedVortexCoefficient q ell B * W.terminalSize) *
                W.terminalSize ^ (j - t.mass - 4) *
                W.profileScale t : ℕ)) : ℝ≥0) *
              vortexProfileWeight W c (j - 3) t := by
          gcongr
          exact_mod_cast
            card_profiledEqualRemainderPairs_absorberInduced_le
              W B T T' t hj hterminal
        _ ≤ (inducedVortexCoefficient q ell B : ℝ≥0) * c ^ (j - 3) :=
          vortexEqualRemainder_terminal_profileTerm_le W c t hmass
            houter hterminal
    _ = (((W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) {T}).filter
            (fun t ↦ t.mass < j - 3)).card : ℝ≥0) *
        ((inducedVortexCoefficient q ell B : ℝ≥0) * c ^ (j - 3)) := by
      simp
    _ ≤ (((j + 1) ^ ell : ℕ) : ℝ≥0) *
        ((inducedVortexCoefficient q ell B : ℝ≥0) * c ^ (j - 3)) := by
      gcongr
      exact_mod_cast (show
          ((W.rootProfileSupport
            (absorberInducedConfigurationsOn q j B) {T}).filter
              (fun t ↦ t.mass < j - 3)).card ≤ (j + 1) ^ ell from
        (card_filter_le _ _).trans
          (W.card_rootProfileSupport_le
            (absorberInducedConfigurationsOn q j B)
            (fun E hE ↦ (absorberInduced_uniform E hE).1) {T}))
    _ = ((j + 1) ^ ell * inducedVortexCoefficient q ell B : ℝ≥0) *
        c ^ (j - 3) := by
      push_cast
      ring

end

end Erdos207
