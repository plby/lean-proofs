import Wikipedia.NoExoticSixSphere.OrthogonalPolygonEnergy
import Wikipedia.NoExoticSixSphere.OrthogonalCompactLogarithm

/-!
# Sampling a single exponential into the actual polygon model

If each scaled generator lies in the local logarithm target, the polygon
generators are exactly those scaled operators. Realization recovers the
original exponential on the whole unit interval, and its finite energy
is the squared Hilbert--Schmidt norm of the generator.
-/

open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  OrthogonalPathEnergy

variable {n m : ℕ}

noncomputable def exponentialVertices (a : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (K : SkewOperators n) : Space n m :=
  fun i ↦ a * exp (τ i.castSucc.succ • K)

theorem continuous_exponentialVertices (a : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    Continuous (exponentialVertices a τ) := by
  apply continuous_pi
  intro i
  have hs : Continuous (fun K : SkewOperators n ↦ τ i.castSucc.succ • K) :=
    continuous_const_smul _
  have he : Continuous (fun K : SkewOperators n ↦ exp (τ i.castSucc.succ • K)) :=
    contMDiff_exp.continuous.comp hs
  exact continuous_const.mul he

theorem vertices_exponentialVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b) (j : Fin (m + 2)) :
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

theorem increment_exponentialVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b) (i : Fin (m + 1)) :
    increment a b (exponentialVertices a τ K) i = exp ((τ i.succ - τ i.castSucc) • K) := by
  rw [increment, vertices_exponentialVertices a b τ hzero hone K hend,
    vertices_exponentialVertices a b τ hzero hone K hend]
  simp only [mul_inv_rev, _root_.mul_assoc, inv_mul_cancel_left]
  apply mul_left_cancel (a := exp (τ i.castSucc • K))
  rw [mul_inv_cancel_left, ← exp_add_smul]
  congr 2
  ring

theorem exponentialVertices_admissible (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ (logarithmChart n).target) :
    exponentialVertices a τ K ∈ admissible a b m := by
  intro i
  rw [increment_exponentialVertices a b τ hzero hone K hend]
  exact exp_mem_logarithmChart_source _ (hK i)

theorem generator_exponentialVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ (logarithmChart n).target)
    (i : Fin (m + 1)) :
    generator a b (exponentialVertices a τ K) i = (τ i.succ - τ i.castSucc) • K := by
  rw [generator, increment_exponentialVertices a b τ hzero hone K hend,
    logarithmChart_exp _ (hK i)]

theorem path_exponentialVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ (logarithmChart n).target)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    path a b τ (exponentialVertices a τ K) t = a * exp (t • K) := by
  have hv := exponentialVertices_admissible a b τ hzero hone K hend hK
  have ht' : t ∈ Icc (τ 0) (τ (Fin.last (m + 1))) := by rwa [hzero, hone]
  obtain ⟨i, hi⟩ := IntervalPartition.exists_mem_adjacent τ ht'
  have hδ : τ i.succ - τ i.castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show i.castSucc < i.succ by simp)).ne'
  rw [path_eq_segment a b τ hτ hv i hi, rescaledSegment,
    vertices_exponentialVertices a b τ hzero hone K hend,
    generator_exponentialVertices a b τ hzero hone K hend hK, smul_smul,
    div_mul_cancel₀ _ hδ, _root_.mul_assoc, ← exp_add_smul]
  congr 2
  congr 1
  ring

theorem energy_exponentialVertices (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (K : SkewOperators n) (hend : a * exp K = b)
    (hK : ∀ i : Fin (m + 1), (τ i.succ - τ i.castSucc) • K ∈ (logarithmChart n).target) :
    energy a b τ (exponentialVertices a τ K) =
      HilbertSchmidt.squareNorm (K : Vector n →L[ℝ] Vector n) := by
  have hv := exponentialVertices_admissible a b τ hzero hone K hend hK
  have he := path_energy_eq a b τ hτ hv
  rw [hzero, hone] at he
  have hc := OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    (fun t ht ↦ congrArg (fun q : OrthogonalOperators n ↦ q.1.1)
      (path_exponentialVertices a b τ hτ hzero hone K hend hK ht))
  rw [energy_left_exp] at hc
  simpa only [sub_zero, one_mul] using he.symm.trans hc

end NoExoticSixSphere.OrthogonalPolygon
