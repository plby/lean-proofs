import Wikipedia.NoExoticSixSphere.OrthogonalPolygon
import Wikipedia.NoExoticSixSphere.OrderedFactors
import Wikipedia.NoExoticSixSphere.RealIntervalProgress

/-!
# Actual continuous realization of fixed-endpoint polygons

The realization is an ordered product of clamped exponential factors.
It is jointly continuous in admissible interior vertices and real time.
On each subdivision interval, it is exactly the corresponding rescaled
exponential segment, and it hits every prescribed vertex.
-/

open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  OrthogonalPathEnergy RealIntervalProgress OrderedFactors

variable {n m : ℕ}

noncomputable def factor (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) (i : Fin (m + 1)) : OrthogonalOperators n :=
  exp (progress (τ i.castSucc) (τ i.succ) t • generator a b v i)

noncomputable def path (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) : OrthogonalOperators n :=
  a * Fin.partialProd (factor a b τ v t) (Fin.last (m + 1))

theorem continuous_factor (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) :
    Continuous (fun p : (admissible a b m) × ℝ ↦ factor a b τ p.1.1 p.2 i) := by
  have hg : Continuous (fun p : (admissible a b m) × ℝ ↦ generator a b p.1.1 i) :=
    (contMDiffOn_generator a b i).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_fst) (fun p ↦ p.1.2)
  have ht : Continuous (fun p : (admissible a b m) × ℝ ↦ progress (τ i.castSucc) (τ i.succ) p.2) :=
    (continuous_progress _ _).comp continuous_snd
  exact contMDiff_exp.continuous.comp (ht.smul hg)

noncomputable def family (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    C((admissible a b m) × ℝ, OrthogonalOperators n) where
  toFun p := path a b τ p.1.1 p.2
  continuous_toFun := continuous_const.mul
    (continuous_partialProd (continuous_factor a b τ) (Fin.last (m + 1)))

theorem path_eq_segment (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    path a b τ v t = rescaledSegment (vertices a b v i.castSucc) (generator a b v i)
      (τ i.castSucc) (τ i.succ) t := by
  have htime (j : Fin (m + 1)) : τ j.castSucc < τ j.succ :=
    hτ (show j.castSucc < j.succ by simp)
  have hbefore (j : Fin (m + 1)) (hj : j < i) :
      factor a b τ v t j = exp (generator a b v j) := by
    have hji : j.succ ≤ i.castSucc := hj
    rw [factor, progress_after (htime j) ((hτ.monotone hji).trans ht.1), one_smul]
  have hafter (j : Fin (m + 1)) (hj : i < j) : factor a b τ v t j = 1 := by
    have hij : i.succ ≤ j.castSucc := hj
    rw [factor, progress_before (htime j).le (ht.2.trans (hτ.monotone hij)), zero_smul, exp_zero]
  have hp : a * Fin.partialProd (fun j ↦ exp (generator a b v j)) i.castSucc =
      vertices a b v i.castSucc := by
    have hgen : (fun j ↦ exp (generator a b v j)) = (fun j ↦ increment a b v j) :=
      funext (exp_generator a b hv)
    rw [hgen]
    simpa only [Pi.smul_apply, smul_eq_mul, vertices_zero, increment] using
      congrFun (Fin.partialProd_left_inv (vertices a b v)) i.castSucc
  rw [path, partialProd_last_eq (factor a b τ v t)
    (fun j ↦ exp (generator a b v j)) i hbefore hafter, ← mul_assoc, hp,
    factor, progress_of_mem (htime i) ht]
  rfl

theorem path_start (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    path a b τ v (τ 0) = a := by
  have h := path_eq_segment a b τ hτ hv (0 : Fin (m + 1))
    (t := τ 0) ⟨le_rfl, (hτ (show (0 : Fin (m + 2)) < (0 : Fin (m + 1)).succ by simp)).le⟩
  change path a b τ v (τ 0) =
    rescaledSegment a (generator a b v 0) (τ 0) (τ (0 : Fin (m + 1)).succ) (τ 0) at h
  rw [rescaledSegment_start] at h
  exact h

theorem path_end (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    path a b τ v (τ (Fin.last (m + 1))) = b := by
  let i : Fin (m + 1) := Fin.last m
  have htime : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
  have h := path_eq_segment a b τ hτ hv i (t := τ i.succ) ⟨htime.le, le_rfl⟩
  rw [rescaledSegment_end _ _ _ _ htime.ne, generator_endpoint a b hv i] at h
  change path a b τ v (τ (Fin.last (m + 1))) = vertices a b v (Fin.last (m + 1)) at h
  rw [vertices_last] at h
  exact h

theorem path_vertex (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) (j : Fin (m + 2)) :
    path a b τ v (τ j) = vertices a b v j := by
  induction j using Fin.lastCases with
  | last => rw [path_end a b τ hτ hv, vertices_last]
  | cast i =>
    have htime : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
    rw [path_eq_segment a b τ hτ hv i ⟨le_rfl, htime.le⟩, rescaledSegment_start]

end NoExoticSixSphere.OrthogonalPolygon
