import ErdosProblems.Erdos941.ShadowPairCount
import ErdosProblems.Erdos941.NonbacktrackingReach

/-! # Reversible integral trajectories with their incoming axes -/

namespace Erdos941

abbrev OrientedTriple := {s : Axis × Triple // tripleNorm s.2 % 3 = 2 ∧ Admissible s.1 s.2}

noncomputable def nextAxis (s : OrientedTriple) : Axis :=
  Classical.choose (existsUnique_other_admissible s.2.1 s.2.2)

theorem nextAxis_admissible (s : OrientedTriple) : Admissible (nextAxis s) s.1.2 :=
  (Classical.choose_spec (existsUnique_other_admissible s.2.1 s.2.2)).1.1

theorem nextAxis_ne (s : OrientedTriple) : nextAxis s ≠ s.1.1 :=
  (Classical.choose_spec (existsUnique_other_admissible s.2.1 s.2.2)).1.2

theorem nextAxis_eq (s : OrientedTriple) {a : Axis}
    (ha : Admissible a s.1.2) (hne : a ≠ s.1.1) : nextAxis s = a :=
  ((Classical.choose_spec (existsUnique_other_admissible s.2.1 s.2.2)).2 a ⟨ha, hne⟩).symm

noncomputable def orientedForward (s : OrientedTriple) : OrientedTriple :=
  ⟨(nextAxis s, rotate (nextAxis s) s.1.2), by
    rw [rotate_norm (nextAxis_admissible s)]
    exact ⟨s.2.1, rotate_admissible (nextAxis_admissible s)⟩⟩

def orientedReflect (s : OrientedTriple) : OrientedTriple :=
  ⟨(s.1.1, rotate s.1.1 s.1.2), by
    rw [rotate_norm s.2.2]
    exact ⟨s.2.1, rotate_admissible s.2.2⟩⟩

noncomputable def orientedBackward (s : OrientedTriple) : OrientedTriple :=
  ⟨(nextAxis (orientedReflect s), (orientedReflect s).1.2),
    (orientedReflect s).2.1, nextAxis_admissible (orientedReflect s)⟩

theorem orientedForward_backward (s : OrientedTriple) :
    orientedForward (orientedBackward s) = s := by
  have hnext : nextAxis (orientedBackward s) = s.1.1 := by
    apply nextAxis_eq
    · exact (orientedReflect s).2.2
    · exact (nextAxis_ne (orientedReflect s)).symm
  apply Subtype.ext
  change (nextAxis (orientedBackward s),
    rotate (nextAxis (orientedBackward s)) (rotate s.1.1 s.1.2)) = s.1
  rw [hnext, rotate_involutive s.2.2]

theorem orientedBackward_forward (s : OrientedTriple) :
    orientedBackward (orientedForward s) = s := by
  have hv : (orientedReflect (orientedForward s)).1.2 = s.1.2 :=
    rotate_involutive (nextAxis_admissible s)
  have hnext : nextAxis (orientedReflect (orientedForward s)) = s.1.1 := by
    apply nextAxis_eq
    · rw [hv]
      exact s.2.2
    · exact (nextAxis_ne s).symm
  apply Subtype.ext
  exact Prod.ext hnext hv

noncomputable def orientedStep : OrientedTriple ≃ OrientedTriple where
  toFun := orientedForward
  invFun := orientedBackward
  left_inv := orientedBackward_forward
  right_inv := orientedForward_backward

theorem orientedStep_norm (s : OrientedTriple) :
    tripleNorm (orientedStep s).1.2 = tripleNorm s.1.2 :=
  rotate_norm (nextAxis_admissible s)

theorem orientedStep_symm_norm (s : OrientedTriple) :
    tripleNorm (orientedStep.symm s).1.2 = tripleNorm s.1.2 := rotate_norm s.2.2

theorem orientedStep_iterate_norm (s : OrientedTriple) (k : ℕ) :
    tripleNorm (orientedStep^[k] s).1.2 = tripleNorm s.1.2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', orientedStep_norm, ih]

theorem orientedStep_symm_iterate_norm (s : OrientedTriple) (k : ℕ) :
    tripleNorm (orientedStep.symm^[k] s).1.2 = tripleNorm s.1.2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', orientedStep_symm_norm, ih]

noncomputable def centeredState (L : ℕ) (s : OrientedTriple) (i : ℕ) : OrientedTriple :=
  orientedStep^[i] (orientedStep.symm^[L] s)

theorem centeredState_center (L : ℕ) (s : OrientedTriple) : centeredState L s L = s :=
  (Function.LeftInverse.iterate orientedForward_backward L) s

theorem centeredState_succ (L : ℕ) (s : OrientedTriple) (i : ℕ) :
    centeredState L s (i + 1) = orientedStep (centeredState L s i) :=
  Function.iterate_succ_apply' _ _ _

theorem centeredState_norm (L : ℕ) (s : OrientedTriple) (i : ℕ) :
    tripleNorm (centeredState L s i).1.2 = tripleNorm s.1.2 :=
  (orientedStep_iterate_norm _ _).trans (orientedStep_symm_iterate_norm _ _)

noncomputable def centeredAxes (L : ℕ) (s : OrientedTriple) (i : ℕ) : Axis :=
  nextAxis (centeredState L s i)

theorem centeredAxes_admissible (L : ℕ) (s : OrientedTriple) (i : ℕ) :
    Admissible (centeredAxes L s i) (centeredState L s i).1.2 := nextAxis_admissible _

theorem centeredAxes_rotate (L : ℕ) (s : OrientedTriple) (i : ℕ) :
    (centeredState L s (i + 1)).1.2 = rotate (centeredAxes L s i) (centeredState L s i).1.2 := by
  rw [centeredState_succ]
  rfl

theorem centeredAxes_reduced (L : ℕ) (s : OrientedTriple) (i : ℕ) :
    centeredAxes L s i ≠ centeredAxes L s (i + 1) := by
  have h := nextAxis_ne (centeredState L s (i + 1))
  rw [centeredState_succ] at h
  change nextAxis (centeredState L s i) ≠ nextAxis (centeredState L s (i + 1))
  rw [centeredState_succ]
  exact h.symm

theorem centered_axes_equal_shadow {L n : ℕ} {s t : OrientedTriple}
    (hn : n % 3 = 2) (hs : tripleNorm s.1.2 = n) (ht : tripleNorm t.1.2 = n)
    (haxes : ∀ i, i < 2 * L → centeredAxes L s i = centeredAxes L t i) :
    (s.1.2, t.1.2) ∈ shadowPairs n (3 ^ (2 * L)) := by
  have h := centered_trajectory_dot_congruence L n (centeredAxes L s)
    (fun i => (centeredState L s i).1.2) (fun i => (centeredState L t i).1.2) hn
    (fun i _ => (centeredState_norm L s i).trans hs)
    (fun i _ => (centeredState_norm L t i).trans ht)
    (fun i _ => ⟨centeredAxes_admissible L s i, centeredAxes_rotate L s i⟩)
    (by
      intro i hi
      rw [haxes i hi]
      exact ⟨centeredAxes_admissible L t i, centeredAxes_rotate L t i⟩)
    (fun i _ => centeredAxes_reduced L s i)
  rw [centeredState_center, centeredState_center] at h
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨mem_spherePoints.mpr hs, mem_spherePoints.mpr ht⟩, ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

end Erdos941
