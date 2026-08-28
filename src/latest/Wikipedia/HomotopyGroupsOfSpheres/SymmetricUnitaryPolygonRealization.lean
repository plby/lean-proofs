import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonEnergy

/-!
# Actual continuous constrained polygon paths and their integral energy

An ordered product of complex unitary exponentials agrees with the real
orthogonal realization. On each edge it is the proved constrained segment;
outside the partition it is constant. Thus the full path stays in the
original symmetric determinant-one subtype, with exactly the finite energy.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace ComplexMatrixRealRepresentation
open NoExoticSixSphere.RealIntervalProgress NoExoticSixSphere.OrderedFactors

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

theorem continuous_generator (a b : SpecialSpace N) (i : Fin (m + 1)) :
    Continuous (fun v : admissible a b m ↦ generator a b v.val i) := by
  let F : C(admissible a b m, ShortLog.domain N) :=
    ⟨fun v ↦ ⟨(vertices a b v.val i.castSucc, vertices a b v.val i.succ), v.property i⟩,
      (((contMDiff_vertices a b i.castSucc).continuous.comp continuous_subtype_val).prodMk
        ((contMDiff_vertices a b i.succ).continuous.comp continuous_subtype_val)).subtype_mk _⟩
  simpa only [Function.comp_def, generator] using!
    (ShortLog.continuous_generator (N := N)).comp F.continuous

def factor (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (t : ℝ) (i : Fin (m + 1)) : unitary (Matrix N N ℂ) :=
  ComplexSkewMatrices.exponential (progress (τ i.castSucc) (τ i.succ) t • generator a b v i)

def unitaryPath (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (v : VertexSpace.Space N m) (t : ℝ) : unitary (Matrix N N ℂ) :=
  a.val.val * Fin.partialProd (factor a b τ v t) (Fin.last (m + 1))

theorem continuous_factor (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) :
    Continuous (fun p : admissible a b m × ℝ ↦ factor a b τ p.1.val p.2 i) := by
  have hg : Continuous (fun p : admissible a b m × ℝ ↦ generator a b p.1.val i) :=
    (continuous_generator a b i).comp continuous_fst
  have ht : Continuous (fun p : admissible a b m × ℝ ↦ progress (τ i.castSucc) (τ i.succ) p.2) :=
    (continuous_progress _ _).comp continuous_snd
  exact ComplexSkewMatrices.continuous_exponential.comp (ht.smul hg)

def unitaryFamily (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) :
    C(admissible a b m × ℝ, unitary (Matrix N N ℂ)) where
  toFun p := unitaryPath a b τ p.1.val p.2
  continuous_toFun := continuous_const.mul
    (continuous_partialProd (continuous_factor a b τ) (Fin.last (m + 1)))

theorem partialProd_orthogonal {q : ℕ} (f : Fin q → unitary (Matrix N N ℂ)) (k : Fin (q + 1)) :
    orthogonal (Fin.partialProd f k) = Fin.partialProd (fun i ↦ orthogonal (f i)) k := by
  induction k using Fin.inductionOn with
  | zero => simp only [Fin.partialProd_zero, map_one]
  | succ j ih => rw [Fin.partialProd_succ, map_mul, ih, Fin.partialProd_succ]

theorem factor_orthogonal (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (t : ℝ) (i : Fin (m + 1)) :
    orthogonal (factor a b τ v t i) =
      NoExoticSixSphere.OrthogonalPolygon.factor (specialOrthogonal a) (specialOrthogonal b)
        τ (forget v) t i := by
  change orthogonal (ComplexSkewMatrices.exponential
    (progress (τ i.castSucc) (τ i.succ) t • generator a b v i)) = _
  rw [ComplexSkewMatrices.orthogonal_exponential, map_smul]
  unfold NoExoticSixSphere.OrthogonalPolygon.factor
  rw [generator_forget a b hv i]

theorem unitaryPath_orthogonal (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (t : ℝ) :
    orthogonal (unitaryPath a b τ v t) =
      NoExoticSixSphere.OrthogonalPolygon.path (specialOrthogonal a) (specialOrthogonal b)
        τ (forget v) t := by
  have hf : (fun i ↦ orthogonal (factor a b τ v t i)) =
      NoExoticSixSphere.OrthogonalPolygon.factor (specialOrthogonal a) (specialOrthogonal b)
        τ (forget v) t := funext (factor_orthogonal a b τ hv t)
  rw [unitaryPath, map_mul, partialProd_orthogonal, hf]
  rfl

theorem unitaryPath_vertex (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m)
    (j : Fin (m + 2)) : unitaryPath a b τ v (τ j) = (vertices a b v j).val.val := by
  apply orthogonal_injective
  change orthogonal (unitaryPath a b τ v (τ j)) = specialOrthogonal (vertices a b v j)
  rw [unitaryPath_orthogonal a b τ hv, vertices_forget]
  exact NoExoticSixSphere.OrthogonalPolygon.path_vertex _ _ τ hτ (admissible_forget a b hv) j

private theorem unitaryPath_before (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) {t : ℝ} (ht : t ≤ τ 0) :
    unitaryPath a b τ v t = unitaryPath a b τ v (τ 0) := by
  have hf : factor a b τ v t = factor a b τ v (τ 0) := by
    funext i
    have hi : τ i.castSucc ≤ τ i.succ := (hτ (show i.castSucc < i.succ by simp)).le
    have hz : τ 0 ≤ τ i.castSucc := hτ.monotone (Fin.zero_le _)
    rw [factor, factor, progress_before hi (ht.trans hz), progress_before hi hz]
  exact congrArg (fun f : Fin (m + 1) → unitary (Matrix N N ℂ) ↦
    a.val.val * Fin.partialProd f (Fin.last (m + 1))) hf

private theorem unitaryPath_after (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space N m) {t : ℝ}
    (ht : τ (Fin.last (m + 1)) ≤ t) :
    unitaryPath a b τ v t = unitaryPath a b τ v (τ (Fin.last (m + 1))) := by
  have hf : factor a b τ v t = factor a b τ v (τ (Fin.last (m + 1))) := by
    funext i
    have hi : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
    have hz : τ i.succ ≤ τ (Fin.last (m + 1)) := hτ.monotone (Fin.le_last _)
    rw [factor, factor, progress_after hi (hz.trans ht), progress_after hi hz]
  exact congrArg (fun f : Fin (m + 1) → unitary (Matrix N N ℂ) ↦
    a.val.val * Fin.partialProd f (Fin.last (m + 1))) hf

theorem unitaryPath_eq_segment (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    unitaryPath a b τ v t =
      (ShortLog.segment (vertices a b v i.castSucc) (vertices a b v i.succ) (hv i)
        ((t - τ i.castSucc) / (τ i.succ - τ i.castSucc))).val.val := by
  apply orthogonal_injective
  change orthogonal (unitaryPath a b τ v t) = specialOrthogonal (ShortLog.segment _ _ _ _)
  rw [unitaryPath_orthogonal a b τ hv,
    NoExoticSixSphere.OrthogonalPolygon.path_eq_segment _ _ τ hτ (admissible_forget a b hv) i ht,
    ShortLog.segment_orthogonal, vertices_forget, generator_forget a b hv i]
  rfl

theorem unitaryPath_relations (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m) (t : ℝ) :
    (unitaryPath a b τ v t).val.transpose = (unitaryPath a b τ v t).val ∧
      (unitaryPath a b τ v t).val.det = 1 := by
  by_cases ht0 : t ≤ τ 0
  · rw [unitaryPath_before a b τ hτ v ht0, unitaryPath_vertex a b τ hτ hv, vertices_zero]
    exact ⟨a.val.property, congrArg (fun z : Circle ↦ (z : ℂ)) a.property⟩
  by_cases ht1 : τ (Fin.last (m + 1)) ≤ t
  · rw [unitaryPath_after a b τ hτ v ht1, unitaryPath_vertex a b τ hτ hv, vertices_last]
    exact ⟨b.val.property, congrArg (fun z : Circle ↦ (z : ℂ)) b.property⟩
  obtain ⟨i, hi⟩ := NoExoticSixSphere.IntervalPartition.exists_mem_adjacent τ
    ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩
  rw [unitaryPath_eq_segment a b τ hτ hv i hi]
  exact ⟨(ShortLog.segment _ _ (hv i) _).val.property,
    congrArg (fun z : Circle ↦ (z : ℂ)) (ShortLog.segment _ _ (hv i) _).property⟩

def path (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (t : ℝ) : SpecialSpace N :=
  ⟨⟨unitaryPath a b τ v t, (unitaryPath_relations a b τ hτ hv t).1⟩, by
    apply Circle.ext
    exact (unitaryPath_relations a b τ hτ hv t).2⟩

theorem path_unitary (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (t : ℝ) :
    (path a b τ hτ v hv t).val.val = unitaryPath a b τ v t := rfl

def family (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) :
    C(admissible a b m × ℝ, SpecialSpace N) where
  toFun p := path a b τ hτ p.1.val p.1.property p.2
  continuous_toFun := ((unitaryFamily a b τ).continuous.subtype_mk _).subtype_mk _

theorem path_orthogonal (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (t : ℝ) :
    specialOrthogonal (path a b τ hτ v hv t) =
      NoExoticSixSphere.OrthogonalPolygon.path (specialOrthogonal a) (specialOrthogonal b)
        τ (forget v) t := unitaryPath_orthogonal a b τ hv t

theorem path_vertex (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (j : Fin (m + 2)) :
    path a b τ hτ v hv (τ j) = vertices a b v j :=
  Subtype.ext (Subtype.ext (unitaryPath_vertex a b τ hτ hv j))

theorem path_start (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) : path a b τ hτ v hv (τ 0) = a := by
  rw [path_vertex, vertices_zero]

theorem path_end (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    path a b τ hτ v hv (τ (Fin.last (m + 1))) = b := by rw [path_vertex, vertices_last]

theorem path_eq_segment (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) (i : Fin (m + 1))
    {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    path a b τ hτ v hv t = ShortLog.segment (vertices a b v i.castSucc)
      (vertices a b v i.succ) (hv i) ((t - τ i.castSucc) / (τ i.succ - τ i.castSucc)) :=
  Subtype.ext (Subtype.ext (unitaryPath_eq_segment a b τ hτ hv i ht))

theorem path_energy_eq (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible a b m) :
    NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ action (path a b τ hτ v hv t).val.val.val) (τ 0) (τ (Fin.last (m + 1))) =
        energy a b τ v := by
  change NoExoticSixSphere.OrthogonalPathEnergy.energy
    (fun t ↦ (specialOrthogonal (path a b τ hτ v hv t)).val.val) _ _ = _
  simp_rw [path_orthogonal]
  exact NoExoticSixSphere.OrthogonalPolygon.path_energy_eq _ _ τ hτ (admissible_forget a b hv)

theorem energy_le_of_matching_vertices (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : VertexSpace.Space N m} (hv : v ∈ admissible a b m)
    {γ : ℝ → SpecialSpace N} (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hmatch : ∀ j, γ (τ j) = vertices a b v j) :
    energy a b τ v ≤ NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ action (γ t).val.val.val) (τ 0) (τ (Fin.last (m + 1))) := by
  apply NoExoticSixSphere.OrthogonalPolygon.energy_le_of_matching_vertices
    (specialOrthogonal a) (specialOrthogonal b) τ hτ (admissible_forget a b hv)
    (γ := fun t ↦ specialOrthogonal (γ t)) ((contDiff_action (N := N)).comp hγ)
  · intro j
    rw [hmatch, vertices_forget]
  · intro i
    exact ((shortDomain_forget a b hv).2 i).le

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
