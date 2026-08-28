import Wikipedia.HopfProblem.OrbitPairSphereVertexSpace
import Wikipedia.HopfProblem.OrbitPairSphereNonantipodalEnergy
import Wikipedia.NoExoticSixSphere.IntervalPartition
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The actual finite sphere polygon energy

Only interior vertices vary; both endpoints are fixed in the vertex list.
The energy is the sum of squared spherical angles divided by the actual
time increments. It is continuous on the compact original vertex space
and smooth on a constructed open short-edge domain. Its sublevel sets in
the full vertex space are compact, and sampling a smooth unit-valued path
never gives greater polygon energy than that path's actual integral energy.

No stationary-polygon classification, path realization, negative-index
transfer, or suspension theorem is assumed by this construction.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SpherePairedGeodesic

structure CostDomain (n : ℕ) where
  set : Set (Sphere n × Sphere n)
  isOpen : IsOpen set
  diagonal : ∀ x : Sphere n, (x, x) ∈ set
  smooth : ContMDiffOn ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (sphereCost n) set

def costDomain (n : ℕ) : CostDomain n where
  set := nonantipodal n
  isOpen := isOpen_nonantipodal n
  diagonal := diagonal_mem_nonantipodal
  smooth := contMDiffOn_sphereCost_nonantipodal n

theorem nonempty_costDomain (n : ℕ) : Nonempty (CostDomain n) := ⟨costDomain n⟩

variable {n m : ℕ}

def vertices (a b : Sphere n) (v : Space n m) : Fin (m + 2) → Sphere n :=
  Fin.cons a (Fin.snoc v b)

theorem vertices_zero (a b : Sphere n) (v : Space n m) : vertices a b v 0 = a := rfl

theorem vertices_last (a b : Sphere n) (v : Space n m) :
    vertices a b v (Fin.last (m + 1)) = b := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => Sphere n) v b (Fin.last m) = b
  simp only [Fin.snoc_last]

theorem vertices_interior (a b : Sphere n) (v : Space n m) (i : Fin m) :
    vertices a b v i.castSucc.succ = v i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => Sphere n) v b i.castSucc = v i
  simp only [Fin.snoc_castSucc]

theorem contMDiff_vertices (a b : Sphere n) (i : Fin (m + 2)) :
    ContMDiff 𝓘(ℝ, Model n m) (𝓡 n) ∞ (fun v : Space n m => vertices a b v i) := by
  induction i using Fin.cases with
  | zero => exact contMDiff_const
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [vertices, Fin.cons_succ, Fin.snoc_last] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, Model n m) (𝓡 n) ∞ (fun _ : Space n m => b))
    | cast i => simpa only [vertices, Fin.cons_succ, Fin.snoc_castSucc] using
        contMDiff_eval (n := n) i

def edge (a b : Sphere n) (v : Space n m) (i : Fin (m + 1)) : Sphere n × Sphere n :=
  (vertices a b v i.castSucc, vertices a b v i.succ)

theorem contMDiff_edge (a b : Sphere n) (i : Fin (m + 1)) :
    ContMDiff 𝓘(ℝ, Model n m) ((𝓡 n).prod (𝓡 n)) ∞
      (fun v : Space n m => edge a b v i) :=
  (contMDiff_vertices a b i.castSucc).prodMk (contMDiff_vertices a b i.succ)

def admissible (D : CostDomain n) (a b : Sphere n) (m : ℕ) : Set (Space n m) :=
  {v | ∀ i : Fin (m + 1), edge a b v i ∈ D.set}

theorem isOpen_admissible (D : CostDomain n) (a b : Sphere n) (m : ℕ) :
    IsOpen (admissible D a b m) := by
  change IsOpen {v : Space n m | ∀ i : Fin (m + 1), edge a b v i ∈ D.set}
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i => D.isOpen.preimage (contMDiff_edge a b i).continuous)

def energy (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : ℝ :=
  ∑ i : Fin (m + 1), sphereCost n (edge a b v i) / (τ i.succ - τ i.castSucc)

theorem contMDiffOn_energy (D : CostDomain n) (a b : Sphere n) (τ : Fin (m + 2) → ℝ) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞ (energy a b τ) (admissible D a b m) := by
  apply contMDiffOn_finsetSum
  intro i _
  have hc : ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞
      (fun v : Space n m => sphereCost n (edge a b v i)) (admissible D a b m) :=
    D.smooth.comp (contMDiff_edge a b i).contMDiffOn (fun _ hv => hv i)
  exact hc.div_const _

theorem continuous_energy (a b : Sphere n) (τ : Fin (m + 2) → ℝ) : Continuous (energy a b τ) := by
  apply continuous_finsetSum
  intro i _
  exact ((continuous_sphereCost n).comp (contMDiff_edge a b i).continuous).div_const _

theorem energy_nonneg (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m) : 0 ≤ energy a b τ v := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)

theorem isCompact_sublevel (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (c : ℝ) :
    IsCompact {v : Space n m | energy a b τ v ≤ c} :=
  (isClosed_le (continuous_energy a b τ) continuous_const).isCompact

theorem energy_le_of_matching_vertices (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} (hγ : ContDiff ℝ ∞ γ)
    (hunit : ∀ t, ‖γ t‖ = 1) (hmatch : ∀ j, γ (τ j) = (vertices a b v j).val) :
    energy a b τ v ≤ SpherePathEnergy.energy γ (τ 0) (τ (Fin.last (m + 1))) := by
  have hs : Continuous (fun t => ‖deriv γ t‖ ^ 2) := ((hγ.deriv' (n := ∞)).continuous.norm).pow 2
  unfold SpherePathEnergy.energy
  rw [IntervalPartition.integral_eq_sum_adjacent τ _
    (fun i => hs.intervalIntegrable (τ i.castSucc) (τ i.succ))]
  apply Finset.sum_le_sum
  intro i _
  have hlen := hτ (show i.castSucc < i.succ by simp)
  apply (div_le_iff₀ (sub_pos.mpr hlen)).mpr
  have h := SphereCurveAngle.endpoint_angle_sq_le_energy hγ hunit hlen
  rw [hmatch, hmatch] at h
  simpa only [sphereCost, edge, mul_comm] using h

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
