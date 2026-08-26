import ErdosProblems.Erdos941.OrientedTrajectories
import ErdosProblems.Erdos941.ModularAvoidance
import ErdosProblems.Erdos941.AvoidingWords

/-! # Encoding integral trajectories by three-choice words -/

namespace Erdos941

open PairLocal

noncomputable def orientedChoice (s : OrientedTriple) : Fin 3 :=
  Classical.choose (exists_otherAxis (nextAxis_ne s))

theorem orientedChoice_axis (s : OrientedTriple) : otherAxis s.1.1 (orientedChoice s) = nextAxis s :=
  Classical.choose_spec (exists_otherAxis (nextAxis_ne s))

noncomputable def trajectoryChoices : ℕ → OrientedTriple → List (Fin 3)
  | 0, _ => []
  | k + 1, s => orientedChoice s :: trajectoryChoices k (orientedStep s)

theorem trajectoryChoices_length (k : ℕ) (s : OrientedTriple) :
    (trajectoryChoices k s).length = k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp only [trajectoryChoices, List.length_cons, ih]

theorem trajectoryChoices_equal_axes {k : ℕ} {s t : OrientedTriple}
    (ha : s.1.1 = t.1.1) (hw : trajectoryChoices k s = trajectoryChoices k t) :
    ∀ i, i < k → nextAxis (orientedStep^[i] s) = nextAxis (orientedStep^[i] t) := by
  induction k generalizing s t with
  | zero => omega
  | succ k ih =>
    have hh := List.cons.inj hw
    have hnext : nextAxis s = nextAxis t := by
      rw [← orientedChoice_axis s, ← orientedChoice_axis t, ha, hh.1]
    intro i hi
    cases i with
    | zero => exact hnext
    | succ i =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih hnext hh.2 i (by omega)

theorem intCast_rotate_linearTurn {R : Type*} [CommRing R] (t : R) (ht : 3 * t = 1)
    {a : Axis} {v : Triple} (ha : Admissible a v) :
    mapCoeffs (Int.castRingHom R) (rotate a v) =
      linearTurn t a (mapCoeffs (Int.castRingHom R) v) := by
  have hd : 3 * (axisDot a v / 3) = axisDot a v := Int.mul_ediv_cancel' ha
  have hdR : (3 : R) * ((axisDot a v / 3 : ℤ) : R) = (axisDot a v : R) := by
    have h := congrArg (fun x : ℤ => (x : R)) hd
    simpa only [Int.cast_mul, Int.cast_ofNat] using h
  have hk : ((axisDot a v / 3 : ℤ) : R) = t * (axisDot a v : R) := by
    rw [← hdR, ← mul_assoc, mul_comm t 3, ht, one_mul]
  ext <;> simp only [mapCoeffs, rotate, linearTurn_apply, Int.coe_castRingHom,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat] <;> rw [hk] <;>
    simp only [axisDot, Int.cast_add, Int.cast_mul] <;> ring

def orientedModState (p : ℕ) (s : OrientedTriple) : Axis × ModularTriple p :=
  (s.1.1, mapCoeffs (Int.castRingHom (ZMod (p ^ 2))) s.1.2)

theorem orientedModState_step (p : ℕ) (t : ZMod (p ^ 2)) (ht : 3 * t = 1) (s : OrientedTriple) :
    turnStateStep (fun a v => linearTurn t a v) (orientedModState p s) (orientedChoice s) =
      orientedModState p (orientedStep s) := by
  change (otherAxis s.1.1 (orientedChoice s),
    linearTurn t (otherAxis s.1.1 (orientedChoice s))
      (mapCoeffs (Int.castRingHom (ZMod (p ^ 2))) s.1.2)) = _
  rw [orientedChoice_axis]
  apply Prod.ext
  · rfl
  · exact (intCast_rotate_linearTurn t ht (nextAxis_admissible s)).symm

theorem trajectoryChoices_avoid (p : ℕ) (t : ZMod (p ^ 2)) (target : ModularTriple p → Prop)
    (ht : 3 * t = 1) (k : ℕ) (s : OrientedTriple)
    (hbad : ∀ i, i < k → ¬ modularBadTurn p target
      (orientedModState p (orientedStep^[i] s)) (orientedChoice (orientedStep^[i] s))) :
    AvoidsWord (hitFlagStep (fun a v => linearTurn t a v) (modularBadTurn p target))
      hitFlagTarget (trajectoryChoices k s) (orientedModState p s, false) := by
  classical
  induction k generalizing s with
  | zero => simp [trajectoryChoices, AvoidsWord, hitFlagTarget]
  | succ k ih =>
    change ¬ hitFlagTarget (orientedModState p s, false) ∧ _
    refine ⟨by simp [hitFlagTarget], ?_⟩
    have hs := hbad 0 (by omega)
    have hstep : hitFlagStep (fun a v => linearTurn t a v) (modularBadTurn p target)
        (orientedModState p s, false) (orientedChoice s) =
        (orientedModState p (orientedStep s), false) := by
      change (turnStateStep (fun a v => linearTurn t a v) (orientedModState p s) (orientedChoice s),
        false || decide (modularBadTurn p target (orientedModState p s) (orientedChoice s))) = _
      rw [orientedModState_step p t ht s]
      simp only [Function.iterate_zero_apply] at hs
      simp only [decide_eq_false hs, Bool.false_or]
    rw [hstep]
    apply ih
    intro i hi
    have h := hbad (i + 1) (by omega)
    rwa [Function.iterate_succ_apply] at h

noncomputable def trajectoryCode (p L : ℕ) (s : OrientedTriple) :
    (Axis × ModularTriple p) × List (Fin 3) :=
  (orientedModState p (centeredState L s 0), trajectoryChoices (2 * L) (centeredState L s 0))

theorem trajectoryCode_eq_shadow {p L n : ℕ} {s t : OrientedTriple}
    (hn : n % 3 = 2) (hs : tripleNorm s.1.2 = n) (ht : tripleNorm t.1.2 = n)
    (hcode : trajectoryCode p L s = trajectoryCode p L t) :
    (s.1.2, t.1.2) ∈ shadowPairs n (3 ^ (2 * L)) := by
  apply centered_axes_equal_shadow hn hs ht
  have ha : (centeredState L s 0).1.1 = (centeredState L t 0).1.1 :=
    congrArg (fun c => c.1.1) hcode
  have hw : trajectoryChoices (2 * L) (centeredState L s 0) =
      trajectoryChoices (2 * L) (centeredState L t 0) := congrArg Prod.snd hcode
  exact trajectoryChoices_equal_axes ha hw

end Erdos941
