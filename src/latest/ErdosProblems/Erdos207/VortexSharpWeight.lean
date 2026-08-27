/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexWeight

/-!
# Density-sensitive vortex extension weights

The coarse cancellation estimates in `VortexWeight` replace every power of
the phase density by one.  The master iteration needs the sharper statement:
for a singleton root in an `r`-vertex indexed family, all `r - 3` remaining
triangles retain their factors of `c`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Exact cancellation of a profile count scale against its vortex weight.
The exponent `m` is the number of unplanted triangles. -/
theorem vortexProfileScaleWeight_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell m z : ℕ}
    (W : Vortex V ell) (c : ℝ≥0) (t : VortexProfile ell)
    (ht : t.mass ≤ m)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) :
    (((z * W.terminalSize ^ (m - t.mass) * W.profileScale t : ℕ) : ℝ≥0) *
        vortexProfileWeight W c m t) =
      (z : ℝ≥0) * c ^ m := by
  have hterminal_ne : (W.terminalSize : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hterminal)
  have hterminal_cancel :
      (W.terminalSize : ℝ≥0) ^ (m - t.mass) *
          (c / W.terminalSize) ^ (m - t.mass) =
        c ^ (m - t.mass) := by
    rw [← mul_pow, mul_div_cancel₀]
    exact hterminal_ne
  unfold vortexProfileWeight
  push_cast
  calc
    (z : ℝ≥0) * (W.terminalSize : ℝ≥0) ^ (m - t.mass) *
          (W.profileScale t : ℝ≥0) *
          ((∏ i : Fin ell,
              (c / (W.U i.castSucc).card) ^ t i) *
            (c / W.terminalSize) ^ (m - t.mass)) =
        (z : ℝ≥0) *
          ((W.profileScale t : ℝ≥0) *
            ∏ i : Fin ell,
              (c / (W.U i.castSucc).card) ^ t i) *
          ((W.terminalSize : ℝ≥0) ^ (m - t.mass) *
            (c / W.terminalSize) ^ (m - t.mass)) := by ring
    _ = (z : ℝ≥0) * c ^ t.mass * c ^ (m - t.mass) := by
      rw [W.profileScale_mul_outerWeight c t houter,
        hterminal_cancel]
    _ = (z : ℝ≥0) * c ^ m := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le ht]

/-- W1 with the full density saving associated to every unplanted triangle.
The profile count may have fewer terminal powers than the endpoint case; the
missing powers only improve the estimate because the terminal vortex is
nonempty. -/
theorem VortexWellSpread.extensionWeight_nonempty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ r - 2) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) R ≤
      ((r + 1) ^ ell * z : ℝ≥0) * c ^ (r - 2 - R.card) := by
  rw [extensionWeight_vortex_eq_profile_sum W F
    (fun E hEF ↦ (h.uniform E hEF).1) c R]
  calc
    ∑ t ∈ W.rootProfileSupport F R,
        ((W.profiledExtensions F R t).card : ℝ≥0) *
          vortexProfileWeight W c (r - 2 - R.card) t ≤
      ∑ _t ∈ W.rootProfileSupport F R,
        (z : ℝ≥0) * c ^ (r - 2 - R.card) := by
      apply sum_le_sum
      intro t ht
      by_cases hprof : (W.profiledExtensions F R t).Nonempty
      · obtain ⟨E, hE⟩ := hprof
        have hm := W.mem_profiledExtensions_iff F R t E |>.mp hE
        have hdiff : (E \ R).card = r - 2 - R.card := by
          rw [card_sdiff_of_subset hm.2.1, (h.uniform E hm.1).1]
        have hmass : t.mass ≤ r - 2 - R.card := by
          rw [← hm.2.2]
          exact (W.outerProfile_mass_le_card (E \ R)).trans_eq hdiff
        have hexp :
            r - t.mass - vortexRootExponent r R.card ≤
              (r - 2 - R.card) - t.mass := by
          have hrootexp := add_two_le_vortexRootExponent r R.card
          omega
        have hN : 1 ≤ W.terminalSize := by omega
        calc
          ((W.profiledExtensions F R t).card : ℝ≥0) *
                vortexProfileWeight W c (r - 2 - R.card) t ≤
              (((z * W.terminalSize ^
                    (r - t.mass - vortexRootExponent r R.card) *
                  W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (r - 2 - R.card) t) := by
            gcongr
            exact_mod_cast h.extensions R t hR hRcard
          _ ≤ (((z * W.terminalSize ^
                    ((r - 2 - R.card) - t.mass) *
                  W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (r - 2 - R.card) t) := by
            gcongr
          _ = (z : ℝ≥0) * c ^ (r - 2 - R.card) :=
            vortexProfileScaleWeight_eq W c t hmass houter hterminal
      · rw [not_nonempty_iff_eq_empty.mp hprof]
        simp
    _ = ((W.rootProfileSupport F R).card : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (r - 2 - R.card)) := by simp
    _ ≤ (((r + 1) ^ ell : ℕ) : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (r - 2 - R.card)) := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le F
        (fun E hEF ↦ (h.uniform E hEF).1) R
    _ = ((r + 1) ^ ell * z : ℝ≥0) * c ^ (r - 2 - R.card) := by
      push_cast
      ring

/-- W4 with the full phase-density saving. -/
theorem VortexWellSpread.extensionWeight_singleton_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell r y z : ℕ} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (c : ℝ≥0)
    (hr : 3 ≤ r)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight (fun E : F ↦ E.1) (vortexTripleWeight W c) {T} ≤
      ((r + 1) ^ ell * y : ℝ≥0) * c ^ (r - 3) := by
  rw [extensionWeight_vortex_eq_profile_sum W F
    (fun E hEF ↦ (h.uniform E hEF).1) c {T}]
  calc
    ∑ t ∈ W.rootProfileSupport F {T},
        ((W.profiledExtensions F {T} t).card : ℝ≥0) *
          vortexProfileWeight W c (r - 2 - ({T} : TripleSystemOn V).card) t ≤
      ∑ _t ∈ W.rootProfileSupport F {T},
        (y : ℝ≥0) * c ^ (r - 3) := by
      apply sum_le_sum
      intro t ht
      have hcard : r - 2 - ({T} : TripleSystemOn V).card = r - 3 := by
        simp only [card_singleton]
        omega
      rw [hcard]
      by_cases hprof : (W.profiledExtensions F {T} t).Nonempty
      · obtain ⟨E, hE⟩ := hprof
        have hm := W.mem_profiledExtensions_iff F {T} t E |>.mp hE
        have hdiff : (E \ {T}).card = r - 3 := by
          rw [card_sdiff_of_subset hm.2.1, (h.uniform E hm.1).1]
          simp
          omega
        have hmass : t.mass ≤ r - 3 := by
          rw [← hm.2.2]
          exact (W.outerProfile_mass_le_card (E \ {T})).trans_eq hdiff
        calc
          ((W.profiledExtensions F {T} t).card : ℝ≥0) *
                vortexProfileWeight W c (r - 3) t ≤
              (((y * W.terminalSize ^ (r - t.mass - 3) *
                  W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (r - 3) t) := by
            gcongr
            exact_mod_cast h.singleton_extensions T t
          _ = (y : ℝ≥0) * c ^ (r - 3) := by
            simpa only [show r - t.mass - 3 = r - 3 - t.mass by omega] using
              (vortexProfileScaleWeight_eq W c t hmass houter hterminal
                (z := y))
      · rw [not_nonempty_iff_eq_empty.mp hprof]
        simp
    _ = ((W.rootProfileSupport F {T}).card : ℝ≥0) *
        ((y : ℝ≥0) * c ^ (r - 3)) := by simp
    _ ≤ (((r + 1) ^ ell : ℕ) : ℝ≥0) *
        ((y : ℝ≥0) * c ^ (r - 3)) := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le F
        (fun E hEF ↦ (h.uniform E hEF).1) {T}
    _ = ((r + 1) ^ ell * y : ℝ≥0) * c ^ (r - 3) := by
      push_cast
      ring

end

end Erdos207
