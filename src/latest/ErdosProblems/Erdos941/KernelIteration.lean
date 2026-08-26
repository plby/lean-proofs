import ErdosProblems.Erdos941.KernelWords

/-! # Repetition of a prime-square kernel word -/

namespace Erdos941

theorem kernelLinear_comp {R : Type*} [CommRing R] {p : R} (hp : p ^ 2 = 0)
    (u t : R) (v : R × R × R) :
    kernelLinear p u (kernelLinear p t v) = kernelLinear p (t + u) v := by
  apply Prod.ext
  · dsimp [kernelLinear]
    linear_combination u * t * (v.2.1 - v.1) * hp
  · apply Prod.ext
    · dsimp [kernelLinear]
      linear_combination -u * t * (v.2.1 - v.1) * hp
    · dsimp [kernelLinear]
      linear_combination -2 * u * t * v.2.2 * hp

theorem linearWord_replicate_kernel {R : Type*} [CommRing R] {p t u : R}
    (hp : p ^ 2 = 0) (w : List Axis) (hw : linearWord t w = kernelLinear p u)
    (j : ℕ) (v : R × R × R) :
    linearWord t (List.replicate j w).flatten v = kernelLinear p ((j : R) * u) v := by
  induction j generalizing v with
  | zero => simp [kernelLinear]
  | succ j ih =>
    rw [List.replicate_succ, List.flatten_cons, linearWord_append, hw, ih,
      kernelLinear_comp hp]
    congr 2
    push_cast
    ring

end Erdos941
