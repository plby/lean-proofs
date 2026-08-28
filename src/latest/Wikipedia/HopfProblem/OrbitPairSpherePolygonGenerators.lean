import Wikipedia.HopfProblem.OrbitPairSpherePolygonStationarity
import Wikipedia.HopfProblem.OrbitPairSphereAngleLogarithm

/-!
# Critical sphere polygons have one actual skew generator

The generator of an edge is the wedge of its initial point with its
outgoing logarithmic velocity. The reverse logarithm gives the negative
of the same generator at its terminal point. Hence the checked tangent
balance equations identify consecutive edge generators, including when
an edge is constant. Each edge exponential recovers its actual endpoint.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereAngle

open NoExoticSixSphere GLOrthonormalization CayleyTransform SkewWedge

variable {n : ℕ}

theorem skew_smul_right (r : ℝ) (x y : Vector n) : skew x (r • y) = r • skew x y := by
  apply Subtype.ext
  exact operator_smul_right r x y

theorem skew_neg_right (x y : Vector n) : skew x (-y) = -skew x y := by
  simpa only [neg_one_smul] using skew_smul_right (-1) x y

theorem skew_reverse (x y : Vector n) : skew y x = -skew x y := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  change inner ℝ y z • x - inner ℝ x z • y = -(inner ℝ x z • y - inner ℝ y z • x)
  abel

theorem skew_logVector (x y : Vector n) :
    skew x (logVector x y) = factor (inner ℝ x y) • skew x y := by
  rw [logVector, skew_smul_right]
  congr 1
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  change inner ℝ x z • (y - inner ℝ x y • x) -
    inner ℝ (y - inner ℝ x y • x) z • x = inner ℝ x z • y - inner ℝ y z • x
  simp only [inner_sub_left, real_inner_smul_left]
  module

theorem skew_logVector_reverse (x y : Vector n) :
    skew y (logVector y x) = -skew x (logVector x y) := by
  have hcomm : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [skew_logVector, skew_logVector, hcomm, skew_reverse, smul_neg]

end Wikipedia.HopfProblem.OrbitPair.SphereAngle

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization CayleyTransform SkewWedge
  SphereVertexSpace SphereAngle SphereTangentExponential OrthogonalExponential

variable {n m : ℕ}

def edgeGenerator (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) : SkewOperators (n + 1) :=
  skew (vertices a b v i.castSucc).val (outgoingLog a b τ v i)

theorem edgeGenerator_reverse (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) :
    edgeGenerator a b τ v i =
      -skew (vertices a b v i.succ).val (incomingLog a b τ v i) := by
  unfold edgeGenerator outgoingLog incomingLog
  rw [skew_smul_right, skew_smul_right, skew_logVector_reverse,
    smul_neg]

theorem adjacent_edgeGenerator_eq_of_stationary (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (j : Fin m) :
    edgeGenerator a b τ v j.castSucc = edgeGenerator a b τ v j.succ := by
  have he : vertices a b v j.succ.castSucc = v j := by
    simpa only [Fin.succ_castSucc] using vertices_interior a b v j
  rw [edgeGenerator_reverse, vertices_interior,
    incoming_eq_neg_outgoing_of_stationary a b τ v hv hstat j,
    skew_neg_right, neg_neg, edgeGenerator, he]

theorem edgeGenerator_eq_first_of_stationary (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    edgeGenerator a b τ v i = edgeGenerator a b τ v 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    exact (adjacent_edgeGenerator_eq_of_stationary a b τ v hv hstat i).symm.trans ih

theorem edgeGenerator_scaled (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) (hstep : τ i.succ - τ i.castSucc ≠ 0) :
    (τ i.succ - τ i.castSucc) • edgeGenerator a b τ v i =
      generator (vertices a b v i.castSucc).val
        (tangentLog (vertices a b v i.castSucc).val (vertices a b v i.succ).val
          (ClosedHemisphere.unit_norm _)) := by
  unfold edgeGenerator outgoingLog
  rw [skew_smul_right, smul_smul]
  have he : (τ i.succ - τ i.castSucc) * (1 / (τ i.succ - τ i.castSucc)) = 1 := by
    field_simp
  rw [he, one_smul]
  rfl

theorem edgeGenerator_endpoint (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) (i : Fin (m + 1)) :
    (exp ((τ i.succ - τ i.castSucc) • edgeGenerator a b τ v i)).1.1
      (vertices a b v i.castSucc).val = (vertices a b v i.succ).val := by
  have hstep : τ i.succ - τ i.castSucc ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hτ (show i.castSucc < i.succ by simp)))
  rw [edgeGenerator_scaled a b τ v i hstep]
  simpa only [curve, one_smul] using curve_tangentLog_one
    (ClosedHemisphere.unit_norm (vertices a b v i.castSucc))
    (ClosedHemisphere.unit_norm (vertices a b v i.succ)) (hv i)

theorem exp_add_apply (K : SkewOperators (n + 1)) (s t : ℝ) (x : Vector (n + 1)) :
    (exp ((s + t) • K)).1.1 x = (exp (s • K)).1.1 ((exp (t • K)).1.1 x) := by
  rw [exp_add_smul]
  rfl

theorem vertices_eq_exp_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (j : Fin (m + 2)) :
    (vertices a b v j).val =
      (exp ((τ j - τ 0) • edgeGenerator a b τ v 0)).1.1 a.val := by
  induction j using Fin.induction with
  | zero =>
    simp only [vertices_zero, sub_self, zero_smul, exp_zero]
    rfl
  | succ i ih =>
    have he := edgeGenerator_endpoint a b τ hτ v hv i
    rw [edgeGenerator_eq_first_of_stationary a b τ v hv hstat i, ih] at he
    rw [← exp_add_apply] at he
    have ht : (τ i.succ - τ i.castSucc) + (τ i.castSucc - τ 0) = τ i.succ - τ 0 := by ring
    rw [ht] at he
    exact he.symm

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
