import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonSegments

/-!
# Actual continuous polygon paths in the complex-structure space

The symplectic polygon realization remains in the complex-structure locus:
on each edge it is the verified anticommuting exponential segment, and
outside the time partition it is constant. Thus its restriction is an actual
continuous family in that locus, with the same integral and finite energies.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices
open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.RealIntervalProgress

variable {n m : ℕ}

private theorem ambient_path_before (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space n m) {t : ℝ} (ht : t ≤ τ 0) :
    Polygon.path a b τ v t = Polygon.path a b τ v (τ 0) := by
  have hf : Polygon.factor a b τ v t = Polygon.factor a b τ v (τ 0) := by
    funext i
    have htime : τ i.castSucc ≤ τ i.succ := (hτ (show i.castSucc < i.succ by simp)).le
    have hzero : τ 0 ≤ τ i.castSucc := hτ.monotone (Fin.zero_le _)
    rw [Polygon.factor, Polygon.factor, progress_before htime (ht.trans hzero),
      progress_before htime hzero]
  exact congrArg (fun f : Fin (m + 1) → symplecticSubgroup n ↦
    a * Fin.partialProd f (Fin.last (m + 1))) hf

private theorem ambient_path_after (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : VertexSpace.Space n m) {t : ℝ}
    (ht : τ (Fin.last (m + 1)) ≤ t) :
    Polygon.path a b τ v t = Polygon.path a b τ v (τ (Fin.last (m + 1))) := by
  have hf : Polygon.factor a b τ v t = Polygon.factor a b τ v (τ (Fin.last (m + 1))) := by
    funext i
    have htime : τ i.castSucc < τ i.succ := hτ (show i.castSucc < i.succ by simp)
    have hlast : τ i.succ ≤ τ (Fin.last (m + 1)) := hτ.monotone (Fin.le_last _)
    rw [Polygon.factor, Polygon.factor, progress_after htime (hlast.trans ht),
      progress_after htime hlast]
  exact congrArg (fun f : Fin (m + 1) → symplecticSubgroup n ↦
    a * Fin.partialProd f (Fin.last (m + 1))) hf

theorem ambient_path_eq_segment (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t =
      toSymplectic (ShortLog.segment (vertices a b v i.castSucc) (vertices a b v i.succ)
        (hv i) ((t - τ i.castSucc) / (τ i.succ - τ i.castSucc))) := by
  rw [Polygon.path_eq_segment _ _ τ hτ (admissible_forget a b hv) i ht,
    Polygon.rescaledSegment, ShortLog.segment_toSymplectic, vertices_forget, generator_forget]
  rfl

theorem ambient_path_square (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) {v : ComplexStructureVertices.Space n m} (hv : v ∈ admissible a b m)
    (t : ℝ) :
    (Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t).val.val.val.comp
      (Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t).val.val.val =
        -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  by_cases ht0 : t ≤ τ 0
  · rw [ambient_path_before _ _ τ hτ _ ht0,
      Polygon.path_start _ _ τ hτ (admissible_forget a b hv)]
    exact a.property
  by_cases ht1 : τ (Fin.last (m + 1)) ≤ t
  · rw [ambient_path_after _ _ τ hτ _ ht1,
      Polygon.path_end _ _ τ hτ (admissible_forget a b hv)]
    exact b.property
  obtain ⟨i, hi⟩ := NoExoticSixSphere.IntervalPartition.exists_mem_adjacent τ
    ⟨(lt_of_not_ge ht0).le, (lt_of_not_ge ht1).le⟩
  rw [ambient_path_eq_segment a b τ hτ hv i hi]
  exact (ShortLog.segment _ _ (hv i) _).property

def path (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) (t : ℝ) :
    ComplexStructures.Space n :=
  ofSymplecticSquare (Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t)
    (ambient_path_square a b τ hτ hv t)

theorem path_toSymplectic (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (t : ℝ) : toSymplectic (path a b τ hτ v hv t) =
      Polygon.path (toSymplectic a) (toSymplectic b) τ (forget v) t :=
  toSymplectic_ofSymplecticSquare _ _

def family (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) :
    C(admissible a b m × ℝ, ComplexStructures.Space n) where
  toFun p := path a b τ hτ p.1.val p.1.property p.2
  continuous_toFun := by
    apply continuous_of_toSymplectic
    let F : C(admissible a b m, Polygon.admissible (toSymplectic a) (toSymplectic b) m) :=
      ⟨fun v ↦ ⟨forget v.val, admissible_forget a b v.property⟩,
        (continuous_forget.comp continuous_subtype_val).subtype_mk _⟩
    let G : C(admissible a b m × ℝ, symplecticSubgroup n) :=
      (Polygon.family (toSymplectic a) (toSymplectic b) τ).comp
        ⟨fun p ↦ (F p.1, p.2), (F.continuous.comp continuous_fst).prodMk continuous_snd⟩
    exact G.continuous.congr (fun p ↦ (path_toSymplectic _ _ _ _ _ _ _).symm)

theorem path_vertex (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (j : Fin (m + 2)) : path a b τ hτ v hv (τ j) = vertices a b v j := by
  apply toSymplectic_injective
  rw [path_toSymplectic, Polygon.path_vertex _ _ τ hτ (admissible_forget a b hv), vertices_forget]

theorem path_start (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    path a b τ hτ v hv (τ 0) = a := by rw [path_vertex, vertices_zero]

theorem path_end (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    path a b τ hτ v hv (τ (Fin.last (m + 1))) = b := by rw [path_vertex, vertices_last]

theorem path_eq_segment (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m)
    (i : Fin (m + 1)) {t : ℝ} (ht : t ∈ Icc (τ i.castSucc) (τ i.succ)) :
    path a b τ hτ v hv t =
      ShortLog.segment (vertices a b v i.castSucc) (vertices a b v i.succ)
        (hv i) ((t - τ i.castSucc) / (τ i.succ - τ i.castSucc)) := by
  apply toSymplectic_injective
  rw [path_toSymplectic]
  exact ambient_path_eq_segment a b τ hτ hv i ht

theorem path_energy_eq (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : ComplexStructureVertices.Space n m) (hv : v ∈ admissible a b m) :
    NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ (path a b τ hτ v hv t).val.val) (τ 0) (τ (Fin.last (m + 1))) =
        energy a b τ v :=
  Polygon.path_energy_eq _ _ τ hτ (admissible_forget a b hv)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
