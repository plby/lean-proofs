import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonEnergy

/-!
# Realization of symplectic polygons by actual exponential paths

The ordered product of clamped symplectic exponentials is jointly continuous.
On the compatible logarithm domain it agrees, as an actual operator path,
with the orthogonal realization. Consequently it hits the prescribed vertices
and its integral energy equals the finite polygon energy.
-/

noncomputable section

open scoped ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.RealIntervalProgress
open NoExoticSixSphere.OrderedFactors VertexSpace Exponential

variable {n m : ℕ}

def factor (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) (i : Fin (m + 1)) : symplecticSubgroup n :=
  exp (progress (τ i.castSucc) (τ i.succ) t • generator a b v i)

def path (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (t : ℝ) : symplecticSubgroup n :=
  a * Fin.partialProd (factor a b τ v t) (Fin.last (m + 1))

theorem continuous_factor (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) :
    Continuous (fun p : (admissible a b m) × ℝ => factor a b τ p.1.val p.2 i) := by
  have hg : Continuous (fun p : (admissible a b m) × ℝ => generator a b p.1.val i) :=
    (contMDiffOn_generator a b i).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_fst) (fun p => p.1.property)
  have ht : Continuous (fun p : (admissible a b m) × ℝ => progress (τ i.castSucc) (τ i.succ) p.2) :=
    (continuous_progress _ _).comp continuous_snd
  exact contMDiff_exp.continuous.comp (ht.smul hg)

def family (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) :
    C((admissible a b m) × ℝ, symplecticSubgroup n) where
  toFun p := path a b τ p.1.val p.2
  continuous_toFun := continuous_const.mul
    (continuous_partialProd (continuous_factor a b τ) (Fin.last (m + 1)))

theorem partialProd_val {N : ℕ} (f : Fin N → symplecticSubgroup n) (k : Fin (N + 1)) :
    (Fin.partialProd f k).val = Fin.partialProd (fun i => (f i).val) k := by
  induction k using Fin.inductionOn with
  | zero => simp only [Fin.partialProd_zero]; rfl
  | succ j ih =>
    rw [Fin.partialProd_succ, Fin.partialProd_succ]
    change (Fin.partialProd f j.castSucc).val * (f j).val = _
    rw [ih]

theorem factor_forget (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) (t : ℝ) (i : Fin (m + 1)) :
    (factor a b τ v t i).val =
      NoExoticSixSphere.OrthogonalPolygon.factor a.val b.val τ (forget v) t i := by
  change NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (progress (τ i.castSucc) (τ i.succ) t • generator a b v i)) =
    NoExoticSixSphere.OrthogonalExponential.exp
      (progress (τ i.castSucc) (τ i.succ) t •
        NoExoticSixSphere.OrthogonalPolygon.generator a.val b.val (forget v) i)
  rw [map_smul, generator_forget a b hv i]

theorem path_forget (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) (t : ℝ) :
    (path a b τ v t).val =
      NoExoticSixSphere.OrthogonalPolygon.path a.val b.val τ (forget v) t := by
  have hf : (fun i => (factor a b τ v t i).val) =
      NoExoticSixSphere.OrthogonalPolygon.factor a.val b.val τ (forget v) t :=
    funext (factor_forget a b τ hv t)
  change a.val * (Fin.partialProd (factor a b τ v t) (Fin.last (m + 1))).val = _
  rw [partialProd_val, hf]
  rfl

theorem path_vertex (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) (j : Fin (m + 2)) :
    path a b τ v (τ j) = vertices a b v j := by
  apply Subtype.ext
  rw [path_forget a b τ hv, vertices_forget]
  exact NoExoticSixSphere.OrthogonalPolygon.path_vertex a.val b.val τ hτ
    (admissible_forget a b hv) j

theorem path_start (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    path a b τ v (τ 0) = a := by rw [path_vertex a b τ hτ hv, vertices_zero]

theorem path_end (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    path a b τ v (τ (Fin.last (m + 1))) = b := by
  rw [path_vertex a b τ hτ hv, vertices_last]

theorem path_energy_eq (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m) :
    NoExoticSixSphere.OrthogonalPathEnergy.energy (fun t => (path a b τ v t).val.val.val)
      (τ 0) (τ (Fin.last (m + 1))) = energy a b τ v := by
  simp_rw [path_forget a b τ hv]
  exact NoExoticSixSphere.OrthogonalPolygon.path_energy_eq a.val b.val τ hτ
    (admissible_forget a b hv)

theorem energy_le_of_matching_vertices (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : Space n m} (hv : v ∈ admissible a b m)
    {γ : ℝ → symplecticSubgroup n} (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val))
    (hmatch : ∀ j, γ (τ j) = vertices a b v j)
    (hshort : ∀ i, ‖generator a b v i‖ ≤ Real.pi) :
    energy a b τ v ≤ NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t => (γ t).val.val.val) (τ 0) (τ (Fin.last (m + 1))) := by
  apply NoExoticSixSphere.OrthogonalPolygon.energy_le_of_matching_vertices a.val b.val τ hτ
    (admissible_forget a b hv) (γ := fun t => (γ t).val) hγ
  · intro j
    rw [hmatch, vertices_forget]
  · intro i
    rw [generator_forget a b hv i]
    exact hshort i

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
