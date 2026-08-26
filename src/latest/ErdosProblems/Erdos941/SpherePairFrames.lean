import ErdosProblems.Erdos941.SpherePairGroup
import ErdosProblems.Erdos941.PairLocal.PairStabilizer

/-! # Explicit rational and unramified transporters between sphere pairs -/

namespace Erdos941

open PairLocal

def crossThree {R : Type*} [CommRing R] (v w : R × R × R) : R × R × R :=
  (v.2.1 * w.2.2 - v.2.2 * w.2.1,
    v.2.2 * w.1 - v.1 * w.2.2, v.1 * w.2.1 - v.2.1 * w.1)

theorem dotThree_cross_left {R : Type*} [CommRing R] (v w : R × R × R) :
    dotThree v (crossThree v w) = 0 := by dsimp [dotThree, crossThree]; ring

theorem dotThree_cross_right {R : Type*} [CommRing R] (v w : R × R × R) :
    dotThree w (crossThree v w) = 0 := by dsimp [dotThree, crossThree]; ring

theorem normThree_cross {R : Type*} [CommRing R] (v w : R × R × R) :
    normThree (crossThree v w) = normThree v * normThree w - dotThree v w ^ 2 := by
  dsimp [normThree, crossThree, dotThree]
  ring

def sphereFrame {R : Type*} [CommRing R] (v w : R × R × R) : Matrix (Fin 3) (Fin 3) R :=
  tripleFrame v w (crossThree v w)

theorem sphereFrame_det {R : Type*} [CommRing R] (v w : R × R × R) :
    (sphereFrame v w).det = normThree v * normThree w - dotThree v w ^ 2 := by
  simp [sphereFrame, tripleFrame, Matrix.det_fin_three, normThree, crossThree, dotThree]
  ring

theorem spherePair_frame_det {R : Type*} [CommRing R] {n e : R} (p : SpherePair R n e) :
    (sphereFrame p.1.1 p.1.2).det = n ^ 2 - e ^ 2 := by
  rw [sphereFrame_det, p.2.1, p.2.2.1, p.2.2.2, pow_two n]

theorem coeffMatrixMap_sphereFrame {R : Type*} [CommRing R] (t u v : R × R × R) :
    coeffMatrixMap (sphereFrame t u) v =
      v.1 • t + v.2.1 • u + v.2.2 • crossThree t u := by
  ext <;> simp [coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLin'_apply, sphereFrame, tripleFrame] <;> ring

theorem normThree_combination {R : Type*} [CommRing R] (t u w : R × R × R) (x y z : R) :
    normThree (x • t + y • u + z • w) =
      x ^ 2 * normThree t + y ^ 2 * normThree u + z ^ 2 * normThree w +
        2 * x * y * dotThree t u + 2 * x * z * dotThree t w + 2 * y * z * dotThree u w := by
  dsimp [normThree, dotThree]
  ring

theorem normThree_sphereFrame {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (v : R × R × R) :
    normThree (coeffMatrixMap (sphereFrame p.1.1 p.1.2) v) =
      v.1 ^ 2 * n + v.2.1 ^ 2 * n + v.2.2 ^ 2 * (n ^ 2 - e ^ 2) + 2 * v.1 * v.2.1 * e := by
  rw [coeffMatrixMap_sphereFrame, normThree_combination,
    dotThree_cross_left, dotThree_cross_right, normThree_cross, p.2.1, p.2.2.1, p.2.2.2]
  ring

noncomputable def sphereFrameEquiv {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) :
    (R × R × R) ≃ₗ[R] (R × R × R) :=
  coeffMatrixEquiv (sphereFrame p.1.1 p.1.2) ((spherePair_frame_det p).symm ▸ h)

theorem sphereFrameEquiv_apply {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) (v : R × R × R) :
    sphereFrameEquiv p h v = coeffMatrixMap (sphereFrame p.1.1 p.1.2) v :=
  coeffMatrixEquiv_apply _ _ _

theorem sphereFrameEquiv_det {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) :
    LinearMap.det (sphereFrameEquiv p h).toLinearMap = n ^ 2 - e ^ 2 := by
  rw [sphereFrameEquiv, coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, spherePair_frame_det]

theorem sphereFrameEquiv_first {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) : sphereFrameEquiv p h (1, 0, 0) = p.1.1 := by
  rw [sphereFrameEquiv_apply, coeffMatrixMap_sphereFrame]
  simp

theorem sphereFrameEquiv_second {R : Type*} [CommRing R] {n e : R}
    (p : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) : sphereFrameEquiv p h (0, 1, 0) = p.1.2 := by
  rw [sphereFrameEquiv_apply, coeffMatrixMap_sphereFrame]
  simp

noncomputable def sphereFrameTransport {R : Type*} [CommRing R] {n e : R}
    (p q : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) : sphereSpecialGroup R :=
  ⟨(sphereFrameEquiv p h).symm.trans (sphereFrameEquiv q h), by
    constructor
    · intro v
      change normThree (sphereFrameEquiv q h ((sphereFrameEquiv p h).symm v)) = normThree v
      calc
        _ = normThree (sphereFrameEquiv p h ((sphereFrameEquiv p h).symm v)) := by
          rw [sphereFrameEquiv_apply, sphereFrameEquiv_apply,
            normThree_sphereFrame, normThree_sphereFrame]
        _ = _ := by rw [LinearEquiv.apply_symm_apply]
    · change LinearMap.det ((sphereFrameEquiv q h).toLinearMap.comp
        (sphereFrameEquiv p h).symm.toLinearMap) = 1
      rw [LinearMap.det_comp, sphereFrameEquiv_det, ← sphereFrameEquiv_det p h]
      exact LinearEquiv.det_mul_det_symm _⟩

theorem sphereFrameTransport_first {R : Type*} [CommRing R] {n e : R}
    (p q : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) :
    (sphereFrameTransport p q h).1 p.1.1 = q.1.1 := by
  change sphereFrameEquiv q h ((sphereFrameEquiv p h).symm p.1.1) = q.1.1
  rw [← sphereFrameEquiv_first p h, LinearEquiv.symm_apply_apply, sphereFrameEquiv_first]

theorem sphereFrameTransport_second {R : Type*} [CommRing R] {n e : R}
    (p q : SpherePair R n e) (h : IsUnit (n ^ 2 - e ^ 2)) :
    (sphereFrameTransport p q h).1 p.1.2 = q.1.2 := by
  change sphereFrameEquiv q h ((sphereFrameEquiv p h).symm p.1.2) = q.1.2
  rw [← sphereFrameEquiv_second p h, LinearEquiv.symm_apply_apply, sphereFrameEquiv_second]

theorem exists_sphere_transporter {K : Type*} [Field K] {n e : K}
    (p q : SpherePair K n e) (h : e ^ 2 ≠ n ^ 2) :
    ∃ g : sphereSpecialGroup K, g.1 p.1.1 = q.1.1 ∧ g.1 p.1.2 = q.1.2 := by
  have hu : IsUnit (n ^ 2 - e ^ 2) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h.symm)
  exact ⟨sphereFrameTransport p q hu, sphereFrameTransport_first p q hu,
    sphereFrameTransport_second p q hu⟩

end Erdos941
