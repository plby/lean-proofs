import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureVertices
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureSegments
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygon

/-!
# Polygon energy restricted to quaternionic complex structures

Admissibility requires every edge to lie in the common short-logarithm
domain. The energy is the actual symplectic polygon energy restricted to
these vertices; it is smooth in the local product coordinates.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices
open NoExoticSixSphere.HilbertSchmidt

variable {n m : ℕ}

def vertices (a b : ComplexStructures.Space n) (v : ComplexStructureVertices.Space n m) :
    Fin (m + 2) → ComplexStructures.Space n := Fin.cons a (Fin.snoc v b)

theorem vertices_zero (a b : ComplexStructures.Space n) (v : ComplexStructureVertices.Space n m) :
    vertices a b v 0 = a := rfl

theorem vertices_last (a b : ComplexStructures.Space n) (v : ComplexStructureVertices.Space n m) :
    vertices a b v (Fin.last (m + 1)) = b := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ ComplexStructures.Space n) v b (Fin.last m) = b
  simp only [Fin.snoc_last]

theorem vertices_interior (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (i : Fin m) :
    vertices a b v i.castSucc.succ = v i := by
  change Fin.snoc (α := fun _ : Fin (m + 1) ↦ ComplexStructures.Space n) v b i.castSucc = v i
  simp only [Fin.snoc_castSucc]

theorem continuous_vertices (a b : ComplexStructures.Space n) (i : Fin (m + 2)) :
    Continuous (fun v : ComplexStructureVertices.Space n m ↦ vertices a b v i) := by
  induction i using Fin.cases with
  | zero => exact continuous_const
  | succ i =>
    induction i using Fin.lastCases with
    | last => simpa only [vertices, Fin.cons_succ, Fin.snoc_last] using
        (continuous_const : Continuous (fun _ : ComplexStructureVertices.Space n m ↦ b))
    | cast i => simpa only [vertices, Fin.cons_succ, Fin.snoc_castSucc] using
        (continuous_apply i : Continuous (fun v : ComplexStructureVertices.Space n m ↦ v i))

theorem vertices_forget (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (i : Fin (m + 2)) :
    toSymplectic (vertices a b v i) =
      Polygon.vertices (toSymplectic a) (toSymplectic b) (forget v) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    induction i using Fin.lastCases with
    | last => rw [show (Fin.last m).succ = Fin.last (m + 1) from rfl,
        vertices_last, Polygon.vertices_last]
    | cast i => rw [vertices_interior, Polygon.vertices_interior]; rfl

theorem relative_forget (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (i : Fin (m + 1)) :
    Cayley.relative (vertices a b v i.castSucc) (vertices a b v i.succ) =
      Polygon.increment (toSymplectic a) (toSymplectic b) (forget v) i := by
  unfold Cayley.relative Polygon.increment
  rw [vertices_forget, vertices_forget]

def admissible (a b : ComplexStructures.Space n) (m : ℕ) :
    Set (ComplexStructureVertices.Space n m) :=
  {v | ∀ i : Fin (m + 1), (vertices a b v i.castSucc, vertices a b v i.succ) ∈ ShortLog.domain n}

theorem isOpen_admissible (a b : ComplexStructures.Space n) (m : ℕ) :
    IsOpen (admissible a b m) := by
  change IsOpen {v : ComplexStructureVertices.Space n m | ∀ i : Fin (m + 1),
    (vertices a b v i.castSucc, vertices a b v i.succ) ∈ ShortLog.domain n}
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦ (ShortLog.isOpen_domain n).preimage
    ((continuous_vertices a b i.castSucc).prodMk (continuous_vertices a b i.succ)))

theorem admissible_forget (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) :
    forget v ∈ Polygon.admissible (toSymplectic a) (toSymplectic b) m := by
  intro i
  rw [← relative_forget]
  exact ShortLog.relative_mem_compatibleDomain (hv i)

def generator (a b : ComplexStructures.Space n) (v : ComplexStructureVertices.Space n m)
    (i : Fin (m + 1)) : SkewSpace n :=
  ShortLog.generator (vertices a b v i.castSucc) (vertices a b v i.succ)

theorem generator_forget (a b : ComplexStructures.Space n)
    (v : ComplexStructureVertices.Space n m) (i : Fin (m + 1)) :
    Polygon.generator (toSymplectic a) (toSymplectic b) (forget v) i = generator a b v i := by
  unfold Polygon.generator generator ShortLog.generator
  rw [relative_forget]

theorem generator_norm_lt (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    ‖generator a b v i‖ < ShortLog.radius n := ShortLog.generator_norm_lt (hv i)

theorem shortDomain_forget (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) :
    forget v ∈ Polygon.shortDomain (toSymplectic a) (toSymplectic b) m := by
  refine ⟨admissible_forget a b hv, fun i ↦ ?_⟩
  rw [generator_forget]
  exact (generator_norm_lt a b hv i).trans (ShortLog.radius_lt_pi n)

theorem admissible_of_forget (a b : ComplexStructures.Space n)
    {v : ComplexStructureVertices.Space n m}
    (hv : forget v ∈ Polygon.admissible (toSymplectic a) (toSymplectic b) m)
    (hn : ∀ i, ‖generator a b v i‖ < ShortLog.radius n) : v ∈ admissible a b m := by
  intro i
  refine ⟨?_, hn i⟩
  change Cayley.relative _ _ ∈ (Exponential.logarithmChart n).source
  rw [relative_forget]
  exact (hv i).1

def energy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) : ℝ :=
  Polygon.energy (toSymplectic a) (toSymplectic b) τ (forget v)

theorem energy_eq_sum (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m) :
    energy a b τ v = ∑ i : Fin (m + 1), squareNorm (generator a b v i).val /
      (τ i.succ - τ i.castSucc) := by
  rw [energy, Polygon.energy_eq_sum _ _ τ (admissible_forget a b hv)]
  simp_rw [generator_forget]

theorem energy_nonneg (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) : 0 ≤ energy a b τ v :=
  Polygon.energy_nonneg _ _ τ hτ (forget v)

theorem continuousOn_energy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (energy a b τ) (admissible a b m) :=
  (Polygon.contMDiffOn_energy (toSymplectic a) (toSymplectic b) τ).continuousOn.comp
    (continuous_forget (n := n) (m := m)).continuousOn
    (fun _ hv ↦ admissible_forget a b hv)

theorem contDiffOn_localEnergy (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (v : ComplexStructureVertices.Space n m) :
    ContDiffOn ℝ ∞ (fun K : Model v ↦ energy a b τ ((atVertices v).symm K))
      ((atVertices v).symm ⁻¹' admissible a b m) := by
  have h : ContMDiffOn 𝓘(ℝ, Model v) 𝓘(ℝ, ℝ) ∞
      (fun K : Model v ↦ energy a b τ ((atVertices v).symm K))
      ((atVertices v).symm ⁻¹' admissible a b m) :=
    (Polygon.contMDiffOn_energy (toSymplectic a) (toSymplectic b) τ).comp
      (contMDiff_forget_chart v).contMDiffOn
      (fun _ hK ↦ admissible_forget a b hK)
  exact contMDiffOn_iff_contDiffOn.mp h

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
