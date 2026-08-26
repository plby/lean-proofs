import ErdosProblems.Erdos1148.FineModularPartition
import ErdosProblems.Erdos1148.MarkedOrbitLiftCover
import ErdosProblems.Erdos1148.ModularTimeOne
import ErdosProblems.Erdos1148.MeasurableLiftCover

/-! # Measurable Bowen covers of finite orbit atoms -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def orbitWordLabel {N n : ℕ} (w : Fin n → Option (Fin N)) (k : ℕ) : Option (Fin N) :=
  if h : k < n then w ⟨k, h⟩ else none

lemma orbitWordLabel_val {N n : ℕ} (w : Fin n → Option (Fin N)) (j : Fin n) :
    orbitWordLabel w j.val = w j := by simp only [orbitWordLabel, dif_pos j.isLt]

noncomputable def exceptionalWordStepCount {N n : ℕ} (w : Fin (n + 1) → Option (Fin N)) : ℕ :=
  ((Finset.range n).filter (fun k => orbitWordLabel w (k + 1) = none)).card

theorem FineModularPartition.orbitAtom_bowen_cover (P : FineModularPartition) {n : ℕ}
    (w : Fin (n + 1) → Option (Fin P.size)) (hfirst : w 0 ≠ none) :
    ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
      (N : ℝ) ≤ (33 ^ 3 * Real.exp 1) ^ exceptionalWordStepCount w ∧
      (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
      P.partition.orbitAtom modularTimeOne (n + 1) w ⊆ ⋃ i, B i ∧
      ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * P.radius) (n : ℝ) := by
  classical
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hfirst
  obtain ⟨E₀, hE₀, hclose₀⟩ := P.regular_lifts a
  let A := P.partition.orbitAtom modularTimeOne (n + 1) w
  have hA : A ⊆ modularMk '' E₀ := by
    intro x hx
    rw [hE₀]
    have hx0 := hx (0 : Fin (n + 1))
    simpa only [Fin.val_zero, Function.iterate_zero_apply, ha] using hx0
  obtain ⟨E, hEA, hstart⟩ := coherent_lifts_restrict hclose₀ hA
  have hword (g : SL(2, ℝ)) (hg : g ∈ E) (k : ℕ) (hk : k < n + 1) :
      modularMk (g * diagonalFlow (k : ℝ)) ∈ P.partition.atom (orbitWordLabel w k) := by
    have hmk : modularMk g ∈ A := by rw [← hEA]; exact ⟨g, hg, rfl⟩
    have h := hmk ⟨k, hk⟩
    simpa only [modularTimeOne_iterate_mk, orbitWordLabel, dif_pos hk] using h
  have hgood (k : ℕ) (hk : k < n) (hnot : ¬orbitWordLabel w (k + 1) = none) :
      (∀ g ∈ E, modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)) ∈ P.core) ∧
      (∀ g ∈ E, ∀ h ∈ E,
        (modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)),
          modularMk (h * diagonalFlow ((k + 1 : ℕ) : ℝ))) ∈ modularClosePairs P.radius) := by
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hnot
    have hmem (g : SL(2, ℝ)) (hg : g ∈ E) :
        modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)) ∈ P.partition.atom (some b) := by
      simpa only [hb] using hword g hg (k + 1) (by omega)
    exact ⟨fun g hg => P.regular_subset_core b (hmem g hg),
      fun g hg h hh => P.regular_pairs b ⟨hmem g hg, hmem h hh⟩⟩
  have hηhalf : P.radius ≤ 1 / 2 := P.radius_le.trans (by norm_num)
  have hcover := marked_orbit_lift_cover P.radius_pos hηhalf P.lift_upgrade E hstart
    (fun k => orbitWordLabel w k = none) n hgood
  obtain ⟨N, B, hN, hcompact, hmeas, hcov, hpairs⟩ :=
    hcover.measurable_modular_cover P.radius_pos.le hηhalf (Nat.cast_nonneg n)
  refine ⟨N, B, hN, hcompact, hmeas, ?_, hpairs⟩
  rwa [hEA] at hcov

end Erdos1148.DukeArithmetic
