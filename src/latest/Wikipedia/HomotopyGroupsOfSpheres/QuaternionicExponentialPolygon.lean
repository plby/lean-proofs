import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRealization
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialPolygon

/-!
# Sampling a symplectic exponential into the actual polygon model

If each scaled generator lies in the local logarithm target, the polygon
generators are exactly those scaled operators. Realization recovers the
original exponential on the whole unit interval, and its finite energy
is the squared Hilbert--Schmidt norm of the generator.
-/

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization VertexSpace Exponential

variable {n m : ℕ}

noncomputable def exponentialVertices (a : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (K : SkewSpace n) : Space n m :=
  fun i ↦ a * exp (τ i.castSucc.succ • K)

theorem continuous_exponentialVertices (a : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) :
    Continuous (exponentialVertices a τ) := by
  apply continuous_pi
  intro i
  have hs : Continuous (fun K : SkewSpace n ↦ τ i.castSucc.succ • K) :=
    continuous_const_smul _
  have he : Continuous (fun K : SkewSpace n ↦ exp (τ i.castSucc.succ • K)) :=
    contMDiff_exp.continuous.comp hs
  exact continuous_const.mul he

theorem vertices_exponentialVertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b) (j : Fin (m + 2)) :
    vertices a b (exponentialVertices a τ K) j = a * exp (τ j • K) := by
  induction j using Fin.cases with
  | zero => simp only [vertices_zero, hzero, zero_smul, exp_zero, mul_one]
  | succ j =>
    induction j using Fin.lastCases with
    | last =>
      change vertices a b (exponentialVertices a τ K) (Fin.last (m + 1)) =
        a * exp (τ (Fin.last (m + 1)) • K)
      rw [vertices_last, hone, one_smul, hend]
    | cast j => rw [vertices_interior]; rfl

theorem increment_exponentialVertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b) (i : Fin (m + 1)) :
    increment a b (exponentialVertices a τ K) i = exp ((τ i.succ - τ i.castSucc) • K) := by
  rw [increment, vertices_exponentialVertices a b τ hzero hone K hend,
    vertices_exponentialVertices a b τ hzero hone K hend]
  simp only [mul_inv_rev, _root_.mul_assoc, inv_mul_cancel_left]
  apply mul_left_cancel (a := exp (τ i.castSucc • K))
  rw [mul_inv_cancel_left, ← exp_add_smul]
  congr 2
  ring

theorem exponentialVertices_admissible (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ compatibleTarget n) :
    exponentialVertices a τ K ∈ admissible a b m := by
  intro i
  rw [increment_exponentialVertices a b τ hzero hone K hend]
  exact exp_mem_compatibleDomain _ (hK i)

theorem generator_exponentialVertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ compatibleTarget n)
    (i : Fin (m + 1)) :
    generator a b (exponentialVertices a τ K) i = (τ i.succ - τ i.castSucc) • K := by
  rw [generator, increment_exponentialVertices a b τ hzero hone K hend,
    logarithmChart_exp _ (hK i).1]

theorem forget_exponentialVertices (a : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (K : SkewSpace n) :
    forget (exponentialVertices a τ K) =
      NoExoticSixSphere.OrthogonalPolygon.exponentialVertices a.val τ (toOrthogonalSkew n K) := by
  funext i
  change a.val * NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (τ i.castSucc.succ • K)) =
      a.val * NoExoticSixSphere.OrthogonalExponential.exp
        (τ i.castSucc.succ • toOrthogonalSkew n K)
  rw [map_smul]

theorem path_exponentialVertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ compatibleTarget n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    path a b τ (exponentialVertices a τ K) t = a * exp (t • K) := by
  have hv := exponentialVertices_admissible a b τ hzero hone K hend hK
  have hendO : a.val * NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n K) =
      b.val := congrArg (fun q : symplecticSubgroup n => q.val) hend
  have hKO (i : Fin (m + 1)) :
      (τ i.succ - τ i.castSucc) • toOrthogonalSkew n K ∈
        (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).target := by
    rw [← map_smul]
    exact (hK i).2
  apply Subtype.ext
  rw [path_forget a b τ hv, forget_exponentialVertices]
  change NoExoticSixSphere.OrthogonalPolygon.path a.val b.val τ
      (NoExoticSixSphere.OrthogonalPolygon.exponentialVertices a.val τ (toOrthogonalSkew n K)) t =
    a.val * NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (t • K))
  rw [map_smul]
  exact NoExoticSixSphere.OrthogonalPolygon.path_exponentialVertices
    a.val b.val τ hτ hzero hone (toOrthogonalSkew n K) hendO hKO ht

theorem energy_exponentialVertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewSpace n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ compatibleTarget n) :
    energy a b τ (exponentialVertices a τ K) =
      NoExoticSixSphere.HilbertSchmidt.squareNorm K.val := by
  have hendO : a.val * NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n K) =
      b.val := congrArg (fun q : symplecticSubgroup n => q.val) hend
  have hKO (i : Fin (m + 1)) :
      (τ i.succ - τ i.castSucc) • toOrthogonalSkew n K ∈
        (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).target := by
    rw [← map_smul]
    exact (hK i).2
  rw [energy, forget_exponentialVertices]
  exact NoExoticSixSphere.OrthogonalPolygon.energy_exponentialVertices
    a.val b.val τ hτ hzero hone (toOrthogonalSkew n K) hendO hKO

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
