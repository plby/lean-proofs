import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexSpace
import Wikipedia.NoExoticSixSphere.OrthogonalShortPolygons

/-!
# Actual symplectic polygon vertices, local generators, and smooth energy

The finite energy is the restriction of the original orthogonal polygon
energy to symplectic vertices. On the proved admissible domain, compatibility
of the logarithms identifies every summand with the genuine symplectic
generator. All spaces retain their original product and subspace topologies.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open VertexSpace Exponential

variable {n m : ℕ}

def forget (v : Space n m) : NoExoticSixSphere.OrthogonalVertexSpace.Space (4 * n + 4) m :=
  fun i => (v i).val

def vertices (a b : symplecticSubgroup n) (v : Space n m) : Fin (m + 2) → symplecticSubgroup n :=
  Fin.cons a (Fin.snoc v b)

theorem vertices_zero (a b : symplecticSubgroup n) (v : Space n m) : vertices a b v 0 = a := rfl

theorem vertices_last (a b : symplecticSubgroup n) (v : Space n m) :
    vertices a b v (Fin.last (m + 1)) = b := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => symplecticSubgroup n) v b (Fin.last m) = b
  simp only [Fin.snoc_last]

theorem vertices_interior (a b : symplecticSubgroup n) (v : Space n m) (i : Fin m) :
    vertices a b v i.castSucc.succ = v i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) => symplecticSubgroup n) v b i.castSucc = v i
  simp only [Fin.snoc_castSucc]

theorem contMDiff_vertices (a b : symplecticSubgroup n) (i : Fin (m + 2)) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewSpace n) ∞ (fun v : Space n m => vertices a b v i) := by
  induction i using Fin.cases with
  | zero => exact contMDiff_const
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [vertices, Fin.cons_succ, Fin.snoc_last] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewSpace n) ∞
          (fun _ : Space n m => b))
    | cast i => simpa only [vertices, Fin.cons_succ, Fin.snoc_castSucc] using
        contMDiff_eval (n := n) i

def increment (a b : symplecticSubgroup n) (v : Space n m) (i : Fin (m + 1)) :
    symplecticSubgroup n := (vertices a b v i.castSucc)⁻¹ * vertices a b v i.succ

theorem contMDiff_increment (a b : symplecticSubgroup n) (i : Fin (m + 1)) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewSpace n) ∞ (fun v : Space n m => increment a b v i) :=
  (contMDiff_vertices a b i.castSucc).inv.mul (contMDiff_vertices a b i.succ)

def admissible (a b : symplecticSubgroup n) (m : ℕ) : Set (Space n m) :=
  {v | ∀ i : Fin (m + 1), increment a b v i ∈ compatibleDomain n}

theorem isOpen_admissible (a b : symplecticSubgroup n) (m : ℕ) : IsOpen (admissible a b m) := by
  change IsOpen {v : Space n m | ∀ i : Fin (m + 1), increment a b v i ∈ compatibleDomain n}
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i => (isOpen_compatibleDomain n).preimage
    (contMDiff_increment a b i).continuous)

def generator (a b : symplecticSubgroup n) (v : Space n m) (i : Fin (m + 1)) : SkewSpace n :=
  logarithmChart n (increment a b v i)

theorem exp_generator (a b : symplecticSubgroup n) {v : Space n m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    exp (generator a b v i) = increment a b v i := exp_logarithmChart _ (hv i).1

theorem generator_endpoint (a b : symplecticSubgroup n) {v : Space n m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    vertices a b v i.castSucc * exp (generator a b v i) = vertices a b v i.succ := by
  rw [exp_generator a b hv i, increment, ← mul_assoc, mul_inv_cancel, one_mul]

theorem contMDiffOn_generator (a b : symplecticSubgroup n) (i : Fin (m + 1)) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewSpace n) ∞
      (fun v : Space n m => generator a b v i) (admissible a b m) :=
  (logarithmChart n).contMDiffOn_toFun.comp (contMDiff_increment a b i).contMDiffOn
    (fun _ hv => (hv i).1)

theorem vertices_forget (a b : symplecticSubgroup n) (v : Space n m) (i : Fin (m + 2)) :
    (vertices a b v i).val =
      NoExoticSixSphere.OrthogonalPolygon.vertices a.val b.val (forget v) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    induction i using Fin.lastCases with
    | last => simp only [vertices, NoExoticSixSphere.OrthogonalPolygon.vertices,
        Fin.cons_succ, Fin.snoc_last]
    | cast i => rw [vertices_interior, NoExoticSixSphere.OrthogonalPolygon.vertices_interior]; rfl

theorem increment_forget (a b : symplecticSubgroup n) (v : Space n m) (i : Fin (m + 1)) :
    (increment a b v i).val =
      NoExoticSixSphere.OrthogonalPolygon.increment a.val b.val (forget v) i := by
  change (vertices a b v i.castSucc).val⁻¹ * (vertices a b v i.succ).val = _
  rw [vertices_forget, vertices_forget]
  rfl

theorem admissible_forget (a b : symplecticSubgroup n) {v : Space n m}
    (hv : v ∈ admissible a b m) :
    forget v ∈ NoExoticSixSphere.OrthogonalPolygon.admissible a.val b.val m := by
  intro i
  rw [← increment_forget]
  exact compatibleDomain_mem_orthogonal_source _ (hv i)

theorem generator_forget (a b : symplecticSubgroup n) {v : Space n m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    NoExoticSixSphere.OrthogonalPolygon.generator a.val b.val (forget v) i =
      toOrthogonalSkew n (generator a b v i) := by
  unfold NoExoticSixSphere.OrthogonalPolygon.generator
  rw [← increment_forget]
  exact orthogonal_logarithm_eq _ (hv i)

def energy (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : ℝ :=
  NoExoticSixSphere.OrthogonalPolygon.energy a.val b.val τ (forget v)

theorem energy_eq_sum (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) :
    energy a b τ v = ∑ i : Fin (m + 1), squareNorm (generator a b v i).val /
      (τ i.succ - τ i.castSucc) := by
  unfold energy NoExoticSixSphere.OrthogonalPolygon.energy
  apply Finset.sum_congr rfl
  intro i _
  rw [generator_forget a b hv i]
  rfl

theorem contMDiffOn_energy (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞ (energy a b τ) (admissible a b m) := by
  have hsum : ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞
      (fun v => ∑ i : Fin (m + 1), squareNorm (generator a b v i).val /
        (τ i.succ - τ i.castSucc)) (admissible a b m) := by
    apply contMDiffOn_finsetSum
    intro i _
    have hL : ContDiff ℝ ∞ (CayleyAtlas.skewInclusion n) :=
      finiteLinearMap_contDiff (E := SkewSpace n)
        (F := Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))
        (CayleyAtlas.skewInclusion n).toLinearMap
    have hgen : ContMDiffOn 𝓘(ℝ, Model n m)
        𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
        (fun v => (generator a b v i).val) (admissible a b m) :=
      hL.contMDiff.comp_contMDiffOn (contMDiffOn_generator a b i)
    have hsq := (contDiff_squareNorm (n := 4 * n + 4)).contMDiff.comp_contMDiffOn hgen
    exact hsq.div_const _
  exact hsum.congr (fun v hv => energy_eq_sum a b τ hv)

theorem energy_nonneg (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m) : 0 ≤ energy a b τ v :=
  NoExoticSixSphere.OrthogonalPolygon.energy_nonneg a.val b.val τ hτ (forget v)

def shortDomain (a b : symplecticSubgroup n) (m : ℕ) : Set (Space n m) :=
  {v | v ∈ admissible a b m ∧ ∀ i, ‖generator a b v i‖ < Real.pi}

theorem isOpen_shortDomain (a b : symplecticSubgroup n) (m : ℕ) : IsOpen (shortDomain a b m) := by
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  have hU := (isOpen_admissible a b m).mem_nhds hv.1
  have hnorm (i : Fin (m + 1)) : ∀ᶠ w in nhds v, ‖generator a b w i‖ < Real.pi := by
    have hc := ((contMDiffOn_generator a b i).contMDiffAt hU).continuousAt
    have hcn : ContinuousAt (fun w : Space n m => ‖generator a b w i‖) v :=
      ContinuousAt.norm (E := SkewSpace n) hc
    exact hcn.eventually (gt_mem_nhds (hv.2 i))
  filter_upwards [hU, eventually_all.mpr hnorm] with w hw hn
  exact ⟨hw, hn⟩

theorem shortDomain_forget (a b : symplecticSubgroup n) {v : Space n m}
    (hv : v ∈ shortDomain a b m) :
    forget v ∈ NoExoticSixSphere.OrthogonalPolygon.shortDomain a.val b.val m := by
  refine ⟨admissible_forget a b hv.1, fun i => ?_⟩
  rw [generator_forget a b hv.1 i]
  exact hv.2 i

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
