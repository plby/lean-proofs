import Wikipedia.NoExoticSixSphere.OrthogonalVertexSpace
import Wikipedia.NoExoticSixSphere.OrthogonalSegmentEnergy
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed-endpoint orthogonal polygons and their energy

Only the interior vertices vary. The endpoints are inserted into the actual
finite vertex list; each edge increment is the group quotient of consecutive
vertices. On the open logarithm domain, the polygon energy is smooth and is
the sum of the actual exponential-segment energies.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  HilbertSchmidt OrthogonalPathEnergy

variable {n m : ℕ}

noncomputable def vertices (a b : OrthogonalOperators n) (v : Space n m) :
    Fin (m + 2) → OrthogonalOperators n := Fin.cons a (Fin.snoc v b)

theorem vertices_zero (a b : OrthogonalOperators n) (v : Space n m) : vertices a b v 0 = a := rfl

theorem vertices_last (a b : OrthogonalOperators n) (v : Space n m) :
    vertices a b v (Fin.last (m + 1)) = b := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ OrthogonalOperators n) v b (Fin.last m) = b
  simp only [Fin.snoc_last]

theorem vertices_interior (a b : OrthogonalOperators n) (v : Space n m) (i : Fin m) :
    vertices a b v i.castSucc.succ = v i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ OrthogonalOperators n) v b i.castSucc = v i
  simp only [Fin.snoc_castSucc]

theorem contMDiff_vertices (a b : OrthogonalOperators n) (i : Fin (m + 2)) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewOperators n) ∞
      (fun v : Space n m ↦ vertices a b v i) := by
  induction i using Fin.cases with
  | zero => exact contMDiff_const
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [vertices, Fin.cons_succ, Fin.snoc_last] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewOperators n) ∞
          (fun _ : Space n m ↦ b))
    | cast i =>
      simpa only [vertices, Fin.cons_succ, Fin.snoc_castSucc] using contMDiff_eval (n := n) i

noncomputable def increment (a b : OrthogonalOperators n) (v : Space n m) (i : Fin (m + 1)) :
    OrthogonalOperators n := (vertices a b v i.castSucc)⁻¹ * vertices a b v i.succ

theorem contMDiff_increment (a b : OrthogonalOperators n) (i : Fin (m + 1)) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewOperators n) ∞
      (fun v : Space n m ↦ increment a b v i) :=
  (contMDiff_vertices a b i.castSucc).inv.mul (contMDiff_vertices a b i.succ)

def admissible (a b : OrthogonalOperators n) (m : ℕ) : Set (Space n m) :=
  {v | ∀ i : Fin (m + 1), increment a b v i ∈ (logarithmChart n).source}

theorem isOpen_admissible (a b : OrthogonalOperators n) (m : ℕ) : IsOpen (admissible a b m) := by
  change IsOpen {v : Space n m | ∀ i : Fin (m + 1), increment a b v i ∈ (logarithmChart n).source}
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦ (logarithmChart n).open_source.preimage
    (contMDiff_increment a b i).continuous)

noncomputable def generator (a b : OrthogonalOperators n) (v : Space n m) (i : Fin (m + 1)) :
    SkewOperators n := logarithmChart n (increment a b v i)

theorem exp_generator (a b : OrthogonalOperators n) {v : Space n m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) : exp (generator a b v i) = increment a b v i :=
  exp_logarithmChart _ (hv i)

theorem generator_endpoint (a b : OrthogonalOperators n) {v : Space n m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    vertices a b v i.castSucc * exp (generator a b v i) = vertices a b v i.succ := by
  rw [exp_generator a b hv i, increment, ← mul_assoc, mul_inv_cancel, one_mul]

theorem contMDiffOn_generator (a b : OrthogonalOperators n) (i : Fin (m + 1)) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewOperators n) ∞
      (fun v : Space n m ↦ generator a b v i) (admissible a b m) :=
  (logarithmChart n).contMDiffOn_toFun.comp (contMDiff_increment a b i).contMDiffOn
    (fun _ hv ↦ hv i)

noncomputable def energy (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : ℝ :=
  ∑ i : Fin (m + 1), squareNorm (generator a b v i : Vector n →L[ℝ] Vector n) /
    (τ i.succ - τ i.castSucc)

theorem contMDiffOn_energy (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞ (energy a b τ) (admissible a b m) := by
  apply contMDiffOn_finsetSum
  intro i _
  have hgen : ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞
      (fun v : Space n m ↦ (generator a b v i : Vector n →L[ℝ] Vector n))
      (admissible a b m) :=
    ((skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contMDiff.contMDiffOn
      (s := univ)).comp (contMDiffOn_generator a b i) (fun _ _ ↦ mem_univ _)
  have hsq : ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞
      (fun v : Space n m ↦ squareNorm (generator a b v i : Vector n →L[ℝ] Vector n))
      (admissible a b m) :=
    ((contDiff_squareNorm (n := n)).contMDiff.contMDiffOn (s := univ)).comp hgen
      (fun _ _ ↦ mem_univ _)
  exact hsq.div_const _

theorem energy_nonneg (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m) : 0 ≤ energy a b τ v := by
  apply Finset.sum_nonneg
  intro i _
  apply div_nonneg (squareNorm_nonneg _) (sub_nonneg.mpr _)
  exact (hτ (show i.castSucc < i.succ by simp)).le

theorem energy_eq_segment_sum (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : energy a b τ v =
      ∑ i : Fin (m + 1), OrthogonalPathEnergy.energy
        (fun t ↦ (rescaledSegment (vertices a b v i.castSucc) (generator a b v i)
          (τ i.castSucc) (τ i.succ) t).1.1) (τ i.castSucc) (τ i.succ) := by
  simp only [energy, energy_rescaledSegment]

end NoExoticSixSphere.OrthogonalPolygon
