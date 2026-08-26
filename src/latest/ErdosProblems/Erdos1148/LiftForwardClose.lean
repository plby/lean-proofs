import ErdosProblems.Erdos1148.ForwardBowenTube
import ErdosProblems.Erdos1148.ModularForwardBowenPairs

/-! # Forward closeness of coherent lifts and concatenation of orbit segments -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def LiftForwardClose (η S : ℝ) (E : Set SL(2, ℝ)) : Prop :=
  ∀ g ∈ E, ∀ h ∈ E, ∀ t ∈ Set.Icc 0 S,
    EntryCloseOne η ((g * diagonalFlow t)⁻¹ * (h * diagonalFlow t))

theorem LiftForwardClose.mono {η S : ℝ} {E F : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (hFE : F ⊆ E) : LiftForwardClose η S F := by
  intro g hg h hh t ht
  exact hE g (hFE hg) h (hFE hh) t ht

theorem LiftForwardClose.time_mono {η S T : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η T E) (hST : S ≤ T) : LiftForwardClose η S E := by
  intro g hg h hh t ht
  exact hE g hg h hh t ⟨ht.1, ht.2.trans hST⟩

theorem LiftForwardClose.left_mul {η S : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (a : SL(2, ℝ)) :
    LiftForwardClose η S ((fun g => a * g) '' E) := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ t ht
  have heq : ((a * g) * diagonalFlow t)⁻¹ * ((a * h) * diagonalFlow t) =
      (g * diagonalFlow t)⁻¹ * (h * diagonalFlow t) := by group
  rw [heq]
  exact hE g hg h hh t ht

theorem liftForwardClose_left_mul_iff {η S : ℝ} {E : Set SL(2, ℝ)} (a : SL(2, ℝ)) :
    LiftForwardClose η S ((fun g => a * g) '' E) ↔ LiftForwardClose η S E := by
  constructor
  · intro hE g hg h hh t ht
    have hc := hE (a * g) ⟨g, hg, rfl⟩ (a * h) ⟨h, hh, rfl⟩ t ht
    have heq : ((a * g) * diagonalFlow t)⁻¹ * ((a * h) * diagonalFlow t) =
        (g * diagonalFlow t)⁻¹ * (h * diagonalFlow t) := by group
    rwa [heq] at hc
  · exact fun hE => hE.left_mul a

theorem LiftForwardClose.append {η S T : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E)
    (hF : LiftForwardClose η T ((fun g => g * diagonalFlow S) '' E)) :
    LiftForwardClose η (S + T) E := by
  intro g hg h hh t ht
  by_cases hle : t ≤ S
  · exact hE g hg h hh t ⟨ht.1, hle⟩
  · have hshift := hF (g * diagonalFlow S) ⟨g, hg, rfl⟩
      (h * diagonalFlow S) ⟨h, hh, rfl⟩ (t - S) ⟨by linarith, by linarith [ht.2]⟩
    have heq : S + (t - S) = t := by ring
    simpa only [mul_assoc, ← diagonalFlow_add, heq] using hshift

theorem LiftForwardClose.modular_image {η S : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (hS : 0 ≤ S) :
    (modularMk '' E) ×ˢ (modularMk '' E) ⊆ modularForwardBowenPairs η S := by
  rintro ⟨_, _⟩ ⟨⟨g, hg, rfl⟩, ⟨h, hh, rfl⟩⟩
  exact mem_modularForwardBowenPairs_of_lifts hS g h (hE g hg h hh)

end Erdos1148.DukeArithmetic
