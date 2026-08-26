import ErdosProblems.Erdos941.ModularTargets
import ErdosProblems.Erdos941.EdgeAvoidance

/-! # Strict avoidance bounds for the three modular targets -/

namespace Erdos941

open PairLocal

abbrev ModularTriple (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2)

def modularBadTurn (p : ℕ) (target : ModularTriple p → Prop)
    (s : Axis × ModularTriple p) (i : Fin 3) : Prop :=
  normThree (mapCoeffs (primeSquareReduce p) s.2) ≠ 0 ∨
    (target s.2 ∧ s.1 = (true, false) ∧ otherAxis s.1 i = (true, true))

noncomputable def modularAvoidance (p : ℕ) (t : ZMod (p ^ 2))
    (target : ModularTriple p → Prop) (k : ℕ) (s : (Axis × ModularTriple p) × Bool) : ℕ :=
  avoidanceCount (hitFlagStep (fun a v => linearTurn t a v) (modularBadTurn p target))
    hitFlagTarget k s

theorem exists_modular_avoidance (p : ℕ) [NeZero (p ^ 2)] (t : ZMod (p ^ 2))
    (target : ModularTriple p → Prop) (ht : 3 * t = 1)
    (hword : ∀ v : ModularTriple p, normThree (mapCoeffs (primeSquareReduce p) v) = 0 →
      ∃ w : List Axis, target (linearWord t w v)) :
    ∃ K : ℕ, 0 < K ∧ ∀ (j : ℕ) (s : (Axis × ModularTriple p) × Bool),
      modularAvoidance p t target (K * j) s ≤ (3 ^ K - 1) ^ j := by
  apply exists_uniform_edge_avoidance (fun a v => linearTurn t a v) (modularBadTurn p target)
  rintro ⟨a, v⟩
  by_cases hv : normThree (mapCoeffs (primeSquareReduce p) v) = 0
  · obtain ⟨w, hw⟩ := hword v hv
    refine ⟨((true, false), linearWord t w v), ?_, ?_⟩
    · have h := turnReach_word (fun a v => linearTurn t a v)
        (linearTurn_involutive ht) a (true, false) v w
      rwa [runAxes_linearTurn] at h
    · obtain ⟨i, hi⟩ := exists_otherAxis (by decide : (true, true) ≠ (true, false))
      exact ⟨i, Or.inr ⟨hw, rfl, hi⟩⟩
  · exact ⟨(a, v), .refl, 0, Or.inl hv⟩

theorem exists_five_modular_avoidance :
    ∃ K : ℕ, 0 < K ∧ ∀ (j : ℕ) (s : (Axis × ModularTriple 5) × Bool),
      modularAvoidance 5 17 (fun v => v.2.2 = 0) (K * j) s ≤ (3 ^ K - 1) ^ j :=
  exists_modular_avoidance 5 17 _ (by decide) exists_five_modular_target

theorem exists_thirteen_modular_avoidance :
    ∃ K : ℕ, 0 < K ∧ ∀ (j : ℕ) (s : (Axis × ModularTriple 13) × Bool),
      modularAvoidance 13 113 (fun v => v.2.2 = 0) (K * j) s ≤ (3 ^ K - 1) ^ j :=
  exists_modular_avoidance 13 113 _ (by decide) exists_thirteen_modular_target

theorem exists_seven_modular_avoidance :
    ∃ K : ℕ, 0 < K ∧ ∀ (j : ℕ) (s : (Axis × ModularTriple 7) × Bool),
      modularAvoidance 7 33 SevenModularTarget (K * j) s ≤ (3 ^ K - 1) ^ j :=
  exists_modular_avoidance 7 33 _ (by decide) exists_seven_modular_target

end Erdos941
