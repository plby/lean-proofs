import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryVertexSpace
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySegments
import Wikipedia.NoExoticSixSphere.OrthogonalShortPolygons

/-! # Constrained polygon vertices, generators, and the actual smooth energy -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace ComplexMatrixRealRepresentation NoExoticSixSphere.HilbertSchmidt

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

def vertices (a b : SpecialSpace N) (v : VertexSpace.Space N m) : Fin (m + 2) → SpecialSpace N :=
  Fin.cons a (Fin.snoc v b)

theorem vertices_zero (a b : SpecialSpace N) (v : VertexSpace.Space N m) :
    vertices a b v 0 = a := rfl

theorem vertices_last (a b : SpecialSpace N) (v : VertexSpace.Space N m) :
    vertices a b v (Fin.last (m + 1)) = b := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ SpecialSpace N) v b (Fin.last m) = b
  simp only [Fin.snoc_last]

theorem vertices_interior (a b : SpecialSpace N) (v : VertexSpace.Space N m) (i : Fin m) :
    vertices a b v i.castSucc.succ = v i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ SpecialSpace N) v b i.castSucc = v i
  simp only [Fin.snoc_castSucc]

theorem contMDiff_vertices (a b : SpecialSpace N) (i : Fin (m + 2)) :
    ContMDiff 𝓘(ℝ, Model N m) 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
      (fun v : VertexSpace.Space N m ↦ vertices a b v i) := by
  induction i using Fin.cases with
  | zero => exact contMDiff_const
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [vertices, Fin.cons_succ, Fin.snoc_last] using
        (contMDiff_const : ContMDiff 𝓘(ℝ, Model N m) 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
          (fun _ : VertexSpace.Space N m ↦ b))
    | cast i => simpa only [vertices, Fin.cons_succ, Fin.snoc_castSucc] using
        (contMDiff_eval (N := N) i)

theorem vertices_forget (a b : SpecialSpace N) (v : VertexSpace.Space N m) (i : Fin (m + 2)) :
    specialOrthogonal (vertices a b v i) =
      NoExoticSixSphere.OrthogonalPolygon.vertices (specialOrthogonal a) (specialOrthogonal b)
        (forget v) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    induction i using Fin.lastCases with
    | last => simp only [vertices, NoExoticSixSphere.OrthogonalPolygon.vertices,
        Fin.cons_succ, Fin.snoc_last]
    | cast i => rw [vertices_interior,
        NoExoticSixSphere.OrthogonalPolygon.vertices_interior]; rfl

def admissible (a b : SpecialSpace N) (m : ℕ) : Set (VertexSpace.Space N m) :=
  {v | ∀ i : Fin (m + 1), (vertices a b v i.castSucc, vertices a b v i.succ) ∈ ShortLog.domain N}

theorem isOpen_admissible (a b : SpecialSpace N) (m : ℕ) : IsOpen (admissible a b m) := by
  change IsOpen {v : VertexSpace.Space N m | ∀ i : Fin (m + 1),
    (vertices a b v i.castSucc, vertices a b v i.succ) ∈ ShortLog.domain N}
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦ ShortLog.isOpen_domain.preimage
    ((contMDiff_vertices a b i.castSucc).continuous.prodMk
      (contMDiff_vertices a b i.succ).continuous))

def generator (a b : SpecialSpace N) (v : VertexSpace.Space N m) (i : Fin (m + 1)) :
    ComplexSkewMatrices.Space N :=
  ShortLog.generator (vertices a b v i.castSucc) (vertices a b v i.succ)

theorem admissible_forget (a b : SpecialSpace N) {v : VertexSpace.Space N m}
    (hv : v ∈ admissible a b m) :
    forget v ∈ NoExoticSixSphere.OrthogonalPolygon.admissible
      (specialOrthogonal a) (specialOrthogonal b) m := by
  intro i
  have h := ComplexSkewMatrices.CompatibleLog.orthogonal_mem_source _ (hv i)
  rw [ShortLog.orthogonal_relative, vertices_forget, vertices_forget] at h
  exact h

theorem generator_forget (a b : SpecialSpace N) {v : VertexSpace.Space N m}
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    NoExoticSixSphere.OrthogonalPolygon.generator (specialOrthogonal a) (specialOrthogonal b)
      (forget v) i = ComplexSkewMatrices.toOrthogonalSkew (generator a b v i) := by
  have h := ShortLog.orthogonal_logarithm_eq (hv i)
  rw [vertices_forget, vertices_forget] at h
  exact h

theorem shortDomain_forget (a b : SpecialSpace N) {v : VertexSpace.Space N m}
    (hv : v ∈ admissible a b m) :
    forget v ∈ NoExoticSixSphere.OrthogonalPolygon.shortDomain
      (specialOrthogonal a) (specialOrthogonal b) m := by
  refine ⟨admissible_forget a b hv, fun i ↦ ?_⟩
  rw [generator_forget a b hv i]
  exact (ComplexSkewMatrices.CompatibleLog.logarithm_mem_target _ (hv i)).2.2

def energy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (v : VertexSpace.Space N m) : ℝ :=
  NoExoticSixSphere.OrthogonalPolygon.energy
    (specialOrthogonal a) (specialOrthogonal b) τ (forget v)

theorem energy_eq_sum (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) :
    energy a b τ v = ∑ i : Fin (m + 1), squareNorm (action (generator a b v i).val) /
      (τ i.succ - τ i.castSucc) := by
  unfold energy NoExoticSixSphere.OrthogonalPolygon.energy
  apply Finset.sum_congr rfl
  intro i _
  rw [generator_forget a b hv i]
  rfl

theorem energy_eq_frobenius_sum (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) :
    energy a b τ v = ∑ i : Fin (m + 1), (2 * ‖generator a b v i‖ ^ 2) /
      (τ i.succ - τ i.castSucc) := by
  rw [energy_eq_sum a b τ hv]
  simp_rw [squareNorm_action, ← frobenius_norm_sq]
  rfl

theorem energy_nonneg (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) : 0 ≤ energy a b τ v :=
  NoExoticSixSphere.OrthogonalPolygon.energy_nonneg _ _ τ hτ (forget v)

theorem contMDiffOn_energy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) :
    ContMDiffOn 𝓘(ℝ, Model N m) 𝓘(ℝ, ℝ) ∞ (energy a b τ) (admissible a b m) :=
  (NoExoticSixSphere.OrthogonalPolygon.contMDiffOn_energy _ _ τ).comp
    (contMDiff_forget (N := N) (m := m)).contMDiffOn (fun _ hv ↦ admissible_forget a b hv)

theorem continuousOn_energy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (energy a b τ) (admissible a b m) := (contMDiffOn_energy a b τ).continuousOn

local instance modelSelfChart :
    LocalLogarithm.NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

theorem contDiffOn_localEnergy (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) :
    ContDiffOn ℝ ∞ (fun K : Model N m ↦ energy a b τ ((atVertices v).symm K))
      ((atVertices v).symm ⁻¹' admissible a b m) := by
  have h := (NoExoticSixSphere.OrthogonalPolygon.contMDiffOn_energy
      (specialOrthogonal a) (specialOrthogonal b) τ).comp
    (contMDiff_forget_chart v).contMDiffOn (fun _ hK ↦ admissible_forget a b hK)
  simpa only [] using! h.contDiffOn

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
