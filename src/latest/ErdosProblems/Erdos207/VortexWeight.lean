/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexWellSpread
import ErdosProblems.Erdos207.WeightSystem

/-! # Level-dependent weights on a finite vortex -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A triangle at level `i` receives weight `c / |U_i|`. -/
def vortexTripleWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (T : TripleOn V) : ℝ≥0 :=
  c / (W.U (W.level T)).card

/-- Exact factorization of the weight of a triangle set by vortex level. -/
theorem setWeight_vortexTripleWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (C : TripleSystemOn V) :
    setWeight (vortexTripleWeight W c) C =
      ∏ i : Fin (ell + 1),
        (c / (W.U i).card) ^ W.levelCount C i := by
  classical
  unfold setWeight vortexTripleWeight
  rw [← Finset.prod_fiberwise' C W.level
    (fun i ↦ c / (W.U i).card)]
  apply Finset.prod_congr rfl
  intro i _hi
  calc
    ∏ T ∈ C with W.level T = i, c / (W.U i).card =
        (c / (W.U i).card) ^ #(C.filter fun T ↦ W.level T = i) := by
          rw [Finset.prod_const]
    _ = (c / (W.U i).card) ^ W.levelCount C i := by
      congr 1
      apply congrArg Finset.card
      ext T
      simp [Vortex.levelCount, Vortex.trianglesAtLevel]

/-- The factorization split into the outer profile and terminal level. -/
theorem setWeight_vortexTripleWeight_outer_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (C : TripleSystemOn V) :
    setWeight (vortexTripleWeight W c) C =
      (∏ i : Fin ell,
        (c / (W.U i.castSucc).card) ^ W.outerProfile C i) *
      (c / W.terminalSize) ^ W.levelCount C (Fin.last ell) := by
  rw [setWeight_vortexTripleWeight, Fin.prod_univ_castSucc]
  rfl

/-- The level counts recover both the outer profile mass and the terminal
count. -/
theorem Vortex.outerProfile_mass_add_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) :
    (W.outerProfile C).mass + W.levelCount C (Fin.last ell) = C.card := by
  have h := W.sum_levelCount C
  rw [Fin.sum_univ_castSucc] at h
  simpa [VortexProfile.mass, Vortex.outerProfile] using h

/-- Consequently the terminal count is the family size minus the outer
profile mass. -/
theorem Vortex.terminal_levelCount_eq_sub_mass
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) :
    W.levelCount C (Fin.last ell) = C.card - (W.outerProfile C).mass := by
  have h := W.outerProfile_mass_add_terminal C
  omega

/-- Common weight of a family of size `m` with outer profile `t`. -/
def vortexProfileWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (m : ℕ)
    (t : VortexProfile ell) : ℝ≥0 :=
  (∏ i : Fin ell,
      (c / (W.U i.castSucc).card) ^ t i) *
    (c / W.terminalSize) ^ (m - t.mass)

theorem setWeight_vortexTripleWeight_eq_profileWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (C : TripleSystemOn V)
    (t : VortexProfile ell) (ht : W.outerProfile C = t) :
    setWeight (vortexTripleWeight W c) C =
      vortexProfileWeight W c C.card t := by
  rw [setWeight_vortexTripleWeight_outer_terminal]
  unfold vortexProfileWeight
  subst t
  rw [W.terminal_levelCount_eq_sub_mass C]

/-- All profiles which actually occur among the remainders above `R`. -/
def Vortex.rootProfileSupport
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (R : TripleSystemOn V) : Finset (VortexProfile ell) :=
  F.image fun E ↦ W.outerProfile (E \ R)

@[simp]
lemma Vortex.mem_rootProfileSupport_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (R : TripleSystemOn V) (t : VortexProfile ell) :
    t ∈ W.rootProfileSupport F R ↔
      ∃ E ∈ F, W.outerProfile (E \ R) = t := by
  simp [Vortex.rootProfileSupport]

lemma Vortex.rootProfileSupport_subset_box
    {V : Type*} [Fintype V] [DecidableEq V] {ell r : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (hcard : ∀ E ∈ F, E.card = r - 2)
    (R : TripleSystemOn V) :
    W.rootProfileSupport F R ⊆ vortexProfileBox ell r := by
  intro t ht
  obtain ⟨E, hEF, rfl⟩ := W.mem_rootProfileSupport_iff F R t |>.mp ht
  rw [mem_vortexProfileBox_iff]
  intro i
  calc
    W.outerProfile (E \ R) i ≤ (E \ R).card :=
      W.outerProfile_apply_le_card (E \ R) i
    _ ≤ E.card := card_le_card sdiff_subset
    _ = r - 2 := hcard E hEF
    _ ≤ r := Nat.sub_le _ _

lemma Vortex.card_rootProfileSupport_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell r : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (hcard : ∀ E ∈ F, E.card = r - 2)
    (R : TripleSystemOn V) :
    (W.rootProfileSupport F R).card ≤ (r + 1) ^ ell := by
  calc
    (W.rootProfileSupport F R).card ≤ (vortexProfileBox ell r).card :=
      card_le_card (W.rootProfileSupport_subset_box F hcard R)
    _ = (r + 1) ^ ell := card_vortexProfileBox ell r

/-- Exact profile decomposition of a level-weighted extension sum for a
fixed-size family. -/
theorem extensionWeight_vortex_eq_profile_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell m : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (hcard : ∀ E ∈ F, E.card = m)
    (c : ℝ≥0) (R : TripleSystemOn V) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) R =
      ∑ t ∈ W.rootProfileSupport F R,
        ((W.profiledExtensions F R t).card : ℝ≥0) *
          vortexProfileWeight W c (m - R.card) t := by
  classical
  unfold extensionWeight
  calc
    (∑ E : F, if R ⊆ E.1 then
        setWeight (vortexTripleWeight W c) (E.1 \ R) else 0) =
        ∑ E ∈ F, if R ⊆ E then
          setWeight (vortexTripleWeight W c) (E \ R) else 0 := by
      exact (Finset.sum_subtype F (by simp)
        (fun E ↦ if R ⊆ E then
          setWeight (vortexTripleWeight W c) (E \ R) else 0)).symm
    _ = ∑ t ∈ W.rootProfileSupport F R,
        ∑ E ∈ F with W.outerProfile (E \ R) = t,
          (if R ⊆ E then
            setWeight (vortexTripleWeight W c) (E \ R) else 0) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro E hEF
      exact W.mem_rootProfileSupport_iff F R _ |>.mpr
        ⟨E, hEF, rfl⟩
    _ = ∑ t ∈ W.rootProfileSupport F R,
        ∑ _E ∈ W.profiledExtensions F R t,
          vortexProfileWeight W c (m - R.card) t := by
      apply sum_congr rfl
      intro t _ht
      rw [← sum_filter]
      apply sum_congr
      · ext E
        simp only [mem_filter, Vortex.profiledExtensions]
        tauto
      · intro E hE
        have hm := (W.mem_profiledExtensions_iff F R t E).mp hE
        have hEF : E ∈ F := hm.1
        have hRE : R ⊆ E := hm.2.1
        have hprofile : W.outerProfile (E \ R) = t := hm.2.2
        have hdiff : (E \ R).card = m - R.card := by
          rw [card_sdiff_of_subset hRE, hcard E hEF]
        calc
          setWeight (vortexTripleWeight W c) (E \ R) =
              vortexProfileWeight W c (E \ R).card t :=
            setWeight_vortexTripleWeight_eq_profileWeight
              W c (E \ R) t hprofile
          _ = vortexProfileWeight W c (m - R.card) t := by rw [hdiff]
    _ = ∑ t ∈ W.rootProfileSupport F R,
        ((W.profiledExtensions F R t).card : ℝ≥0) *
          vortexProfileWeight W c (m - R.card) t := by
      apply sum_congr rfl
      intro t _ht
      simp

/-- The exact finite W1 budget above a nonempty root.  Later asymptotic
lemmas simplify this sum by cancelling the profile scale against the
level-dependent product weight. -/
def vortexWellSpreadExtensionBudget
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (r z : ℕ) (F : ForbiddenFamilyOn V)
    (c : ℝ≥0) (R : TripleSystemOn V) : ℝ≥0 :=
  ∑ t ∈ W.rootProfileSupport F R,
    (z * W.terminalSize ^
        (r - t.mass - vortexRootExponent r R.card) *
      W.profileScale t : ℕ) *
      vortexProfileWeight W c (r - 2 - R.card) t

/-- The outer profile scale cancels the outer denominators in the vortex
weight. -/
theorem Vortex.profileScale_mul_outerWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (t : VortexProfile ell)
    (hpos : ∀ i : Fin ell, 0 < (W.U i.castSucc).card) :
    (W.profileScale t : ℝ≥0) *
        (∏ i : Fin ell,
          (c / (W.U i.castSucc).card) ^ t i) =
      c ^ t.mass := by
  unfold Vortex.profileScale VortexProfile.mass
  push_cast
  rw [← Finset.prod_mul_distrib]
  calc
    ∏ i : Fin ell,
        ((W.U i.castSucc).card : ℝ≥0) ^ t i *
          (c / (W.U i.castSucc).card) ^ t i =
        ∏ i : Fin ell, c ^ t i := by
      apply prod_congr rfl
      intro i _hi
      rw [← mul_pow, mul_div_cancel₀]
      exact_mod_cast (Nat.ne_of_gt (hpos i))
    _ = c ^ ∑ i : Fin ell, t i := by
      exact Finset.prod_pow_eq_pow_sum univ t c

lemma nnreal_pow_mul_one_div_pow_le_one
    (x : ℝ≥0) (hx : 1 ≤ x) {a b : ℕ} (hab : a ≤ b) :
    x ^ a * (1 / x) ^ b ≤ 1 := by
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (div_le_one₀ (pow_pos (zero_lt_one.trans_le hx) _)).2
  exact pow_le_pow_right' hx hab

/-- Each individual W1 profile contribution is at most `z` once every
vortex set is nonempty and the density constant is at most one. -/
theorem vortexWellSpread_profileTerm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r z : ℕ} (W : Vortex V ell) (c : ℝ≥0)
    (hc : c ≤ 1) (R : TripleSystemOn V) (t : VortexProfile ell)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) :
    ((z * W.terminalSize ^
          (r - t.mass - vortexRootExponent r R.card) *
        W.profileScale t : ℕ) : ℝ≥0) *
        vortexProfileWeight W c (r - 2 - R.card) t ≤ z := by
  let a := r - t.mass - vortexRootExponent r R.card
  let b := r - 2 - R.card - t.mass
  have hab : a ≤ b := by
    dsimp only [a, b]
    have hexp := add_two_le_vortexRootExponent r R.card
    omega
  have hN : (1 : ℝ≥0) ≤ W.terminalSize := by
    exact_mod_cast hterminal
  have hcPow : c ^ t.mass ≤ (1 : ℝ≥0) := by
    exact pow_le_one₀ (by positivity) hc
  have hdiv : c / (W.terminalSize : ℝ≥0) ≤
      1 / (W.terminalSize : ℝ≥0) := by
    gcongr
  have hterminalFactor :
      (W.terminalSize : ℝ≥0) ^ a *
          (c / (W.terminalSize : ℝ≥0)) ^ b ≤ 1 := by
    calc
      (W.terminalSize : ℝ≥0) ^ a *
          (c / (W.terminalSize : ℝ≥0)) ^ b ≤
          (W.terminalSize : ℝ≥0) ^ a *
            (1 / (W.terminalSize : ℝ≥0)) ^ b := by gcongr
      _ ≤ 1 := nnreal_pow_mul_one_div_pow_le_one _ hN hab
  unfold vortexProfileWeight
  push_cast
  rw [show r - t.mass - vortexRootExponent r R.card = a by rfl,
    show r - 2 - R.card - t.mass = b by rfl]
  calc
    (z : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ a *
        (W.profileScale t : ℝ≥0) *
        ((∏ i : Fin ell,
          (c / (W.U i.castSucc).card) ^ t i) *
          (c / W.terminalSize) ^ b) =
        (z : ℝ≥0) * c ^ t.mass *
          ((W.terminalSize : ℝ≥0) ^ a *
            (c / W.terminalSize) ^ b) := by
      calc
        (z : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ a *
            (W.profileScale t : ℝ≥0) *
            ((∏ i : Fin ell,
              (c / (W.U i.castSucc).card) ^ t i) *
              (c / W.terminalSize) ^ b) =
            (z : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ a *
              ((W.profileScale t : ℝ≥0) *
                (∏ i : Fin ell,
                  (c / (W.U i.castSucc).card) ^ t i)) *
              (c / W.terminalSize) ^ b := by ring
        _ = (z : ℝ≥0) * c ^ t.mass *
            ((W.terminalSize : ℝ≥0) ^ a *
              (c / W.terminalSize) ^ b) := by
          rw [W.profileScale_mul_outerWeight c t houter]
          ring
    _ ≤ (z : ℝ≥0) * 1 * 1 := by gcongr
    _ = (z : ℝ≥0) := by simp

/-- W1 gives the corresponding level-weighted extension estimate for every
nonempty root. -/
theorem VortexWellSpread.extensionWeight_nonempty_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ r - 2) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) R ≤
      vortexWellSpreadExtensionBudget W r z F c R := by
  rw [extensionWeight_vortex_eq_profile_sum W F
    (fun E hEF ↦ (h.uniform E hEF).1) c R]
  unfold vortexWellSpreadExtensionBudget
  apply sum_le_sum
  intro t _ht
  gcongr
  exact_mod_cast h.extensions R t hR hRcard

/-- Profile cancellation makes the nonempty-root extension coefficient
independent of all ambient vortex sizes. -/
theorem VortexWellSpread.extensionWeight_nonempty_le_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ r - 2) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) R ≤
      (((r + 1) ^ ell * z : ℕ) : ℝ≥0) := by
  apply (h.extensionWeight_nonempty_le c R hR hRcard).trans
  unfold vortexWellSpreadExtensionBudget
  calc
    ∑ t ∈ W.rootProfileSupport F R,
        ((z * W.terminalSize ^
              (r - t.mass - vortexRootExponent r R.card) *
            W.profileScale t : ℕ) : ℝ≥0) *
          vortexProfileWeight W c (r - 2 - R.card) t ≤
        ∑ _t ∈ W.rootProfileSupport F R, (z : ℝ≥0) := by
      apply sum_le_sum
      intro t _ht
      exact vortexWellSpread_profileTerm_le W c hc R t houter hterminal
    _ = ((W.rootProfileSupport F R).card : ℝ≥0) * z := by simp
    _ ≤ (((r + 1) ^ ell : ℕ) : ℝ≥0) * z := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le F
        (fun E hEF ↦ (h.uniform E hEF).1) R
    _ = (((r + 1) ^ ell * z : ℕ) : ℝ≥0) := by norm_cast

/-- W4 replaces `z` by the sharper singleton coefficient `y`. -/
theorem VortexWellSpread.extensionWeight_singleton_le_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) {T} ≤
      (((r + 1) ^ ell * y : ℕ) : ℝ≥0) := by
  rw [extensionWeight_vortex_eq_profile_sum W F
    (fun E hEF ↦ (h.uniform E hEF).1) c {T}]
  calc
    ∑ t ∈ W.rootProfileSupport F {T},
        ((W.profiledExtensions F {T} t).card : ℝ≥0) *
          vortexProfileWeight W c (r - 2 - ({T} : TripleSystemOn V).card) t ≤
        ∑ t ∈ W.rootProfileSupport F {T},
          (((y * W.terminalSize ^ (r - t.mass - 3) *
              W.profileScale t : ℕ) : ℝ≥0) *
            vortexProfileWeight W c
              (r - 2 - ({T} : TripleSystemOn V).card) t) := by
      apply sum_le_sum
      intro t _ht
      gcongr
      exact_mod_cast h.singleton_extensions T t
    _ ≤ ∑ _t ∈ W.rootProfileSupport F {T}, (y : ℝ≥0) := by
      apply sum_le_sum
      intro t _ht
      simpa only [card_singleton, vortexRootExponent_one] using
        (vortexWellSpread_profileTerm_le
          (r := r) (z := y) W c hc ({T} : TripleSystemOn V) t
            houter hterminal)
    _ = ((W.rootProfileSupport F {T}).card : ℝ≥0) * y := by simp
    _ ≤ (((r + 1) ^ ell : ℕ) : ℝ≥0) * y := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le F
        (fun E hEF ↦ (h.uniform E hEF).1) {T}
    _ = (((r + 1) ^ ell * y : ℕ) : ℝ≥0) := by norm_cast

end

end Erdos207
