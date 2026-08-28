import Wikipedia.NoExoticSixSphere.SkewRotationComplement

/-!
# Orthonormal rotation partners throughout the complement

For an antipodal exponential, the Gram eigenbasis of a rotation plane's
complement has orthonormal rotation partners in the same complement. Every
associated speed is at least `π`. These are pointwise spectral choices for a
fixed operator; no continuity in the operator is asserted.
-/

namespace NoExoticSixSphere.SkewRotationComplement

open GLOrthonormalization CayleyTransform SkewSpectralPlane SkewRotationExponential
  SkewAntipodalSpectrum OrthogonalExponential

variable {n : ℕ} (K : SkewOperators n) {α : ℝ} {x y : Vector n}
  (hx : (K : Vector n →L[ℝ] Vector n) x = α • y)
  (hy : (K : Vector n →L[ℝ] Vector n) y = (-α) • x)

structure RotationData where
  speed : Fin (Module.finrank ℝ (complement x y)) → ℝ
  partner : Fin (Module.finrank ℝ (complement x y)) → complement x y
  speed_ge_pi : ∀ i, Real.pi ≤ speed i
  orthonormal_partner : Orthonormal ℝ partner
  map_basis : ∀ i, (K : Vector n →L[ℝ] Vector n) (basis K hx hy i : Vector n) =
    speed i • (partner i : Vector n)
  map_partner : ∀ i, (K : Vector n →L[ℝ] Vector n) (partner i : Vector n) =
    (-speed i) • (basis K hx hy i : Vector n)

theorem exists_rotationData
    (hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    Nonempty (RotationData K hx hy) := by
  let b := basis K hx hy
  have hnorm (i : Fin (Module.finrank ℝ (complement x y))) : ‖(b i : Vector n)‖ = 1 :=
    b.orthonormal.norm_eq_one i
  have hpos (i : Fin (Module.finrank ℝ (complement x y))) :
      0 < eigenvalue K hx hy i :=
    gram_eigenvalue_pos K hexp (hnorm i) (gram_basis K hx hy i)
  have hex (i : Fin (Module.finrank ℝ (complement x y))) :=
    exists_rotationPartner K (hpos i) (hnorm i) (gram_basis K hx hy i)
  choose β w hβ hn hw hKv hKw hsq using hex
  have hmem (i : Fin (Module.finrank ℝ (complement x y))) : w i ∈ complement x y := by
    apply ((complement x y).smul_mem_iff (hβ i).ne').mp
    rw [← hKv i]
    exact map_mem_complement K hx hy (b i).2
  have horth (i j : Fin (Module.finrank ℝ (complement x y))) (hij : i ≠ j) :
      inner ℝ (w i) (w j) = 0 := by
    have hgram : inner ℝ ((K : Vector n →L[ℝ] Vector n) (b i))
        ((K : Vector n →L[ℝ] Vector n) (b j)) = 0 := by
      calc
        _ = inner ℝ (b i : Vector n) (gram K (b j)) :=
          ((K : Vector n →L[ℝ] Vector n).adjoint_inner_right
            (b i) ((K : Vector n →L[ℝ] Vector n) (b j))).symm
        _ = 0 := by
          rw [gram_basis K hx hy j, inner_smul_right]
          change eigenvalue K hx hy j * inner ℝ (b i) (b j) = 0
          rw [b.orthonormal.inner_eq_zero hij, mul_zero]
    have hh : β j * (β i * inner ℝ (w i) (w j)) = 0 := by
      simpa only [hKv, inner_smul_left, inner_smul_right, RCLike.conj_to_real] using hgram
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (hβ j).ne')).resolve_left (hβ i).ne'
  refine ⟨{
    speed := β
    partner := fun i ↦ ⟨w i, hmem i⟩
    speed_ge_pi := ?_
    orthonormal_partner := ⟨hn, horth⟩
    map_basis := hKv
    map_partner := hKw
  }⟩
  intro i
  have hgap := speed_gap (hβ i)
    (cos_speed_eq_neg_one K (hKv i) (hKw i) (hnorm i) (hw i) hexp)
  rcases hgap with h | h
  · exact h.ge
  · linarith [Real.pi_pos]

end NoExoticSixSphere.SkewRotationComplement
