import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygon
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCompactness
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryCompactLogarithm
import Wikipedia.NoExoticSixSphere.UniformTimePartition

/-! # Compact constrained polygon energy sublevels on sufficiently fine meshes -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open ComplexSkewMatrices.CompatibleLog NoExoticSixSphere.UniformTimePartition

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

private theorem summand_le_weighted_sum {q : ℕ} (w δ : Fin q → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hδ : ∀ j, 0 < δ j) (i : Fin q) :
    w i ≤ (∑ j, w j / δ j) * δ i := by
  apply (div_le_iff₀ (hδ i)).mp
  exact Finset.single_le_sum (fun j _ ↦ div_nonneg (hw j) (hδ j).le) (Finset.mem_univ i)

def boundedIncrements (a b : SpecialSpace N) (m : ℕ) (r : ℝ) : Set (VertexSpace.Space N m) :=
  {v | ∀ i : Fin (m + 1), ShortLog.relative (vertices a b v i.castSucc) (vertices a b v i.succ) ∈
    compactIncrements N r}

theorem isClosed_boundedIncrements (a b : SpecialSpace N) (m : ℕ) (r : ℝ) :
    IsClosed (boundedIncrements a b m r) := by
  change IsClosed {v : VertexSpace.Space N m | ∀ i : Fin (m + 1),
    ShortLog.relative (vertices a b v i.castSucc) (vertices a b v i.succ) ∈ compactIncrements N r}
  rw [ofPred_forall]
  exact isClosed_iInter (fun i ↦ (isCompact_compactIncrements r).isClosed.preimage
    (ShortLog.continuous_relative.comp ((contMDiff_vertices a b i.castSucc).continuous.prodMk
      (contMDiff_vertices a b i.succ).continuous)))

theorem isCompact_boundedIncrements (a b : SpecialSpace N) (m : ℕ) (r : ℝ) :
    IsCompact (boundedIncrements a b m r) := (isClosed_boundedIncrements a b m r).isCompact

theorem mem_boundedIncrements_iff (a b : SpecialSpace N) {r : ℝ} (hr : r < radius N)
    (v : VertexSpace.Space N m) :
    v ∈ boundedIncrements a b m r ↔ v ∈ admissible a b m ∧ ∀ i, ‖generator a b v i‖ ≤ r := by
  constructor
  · intro hv
    exact ⟨fun i ↦ ((mem_compactIncrements_iff hr _).mp (hv i)).1,
      fun i ↦ ((mem_compactIncrements_iff hr _).mp (hv i)).2⟩
  · rintro ⟨hv, hn⟩ i
    exact (mem_compactIncrements_iff hr _).mpr ⟨hv i, hn i⟩

theorem boundedIncrements_subset_admissible (a b : SpecialSpace N) {r : ℝ} (hr : r < radius N) :
    boundedIncrements a b m r ⊆ admissible a b m :=
  fun v hv ↦ ((mem_boundedIncrements_iff a b hr v).mp hv).1

theorem twice_generator_norm_sq_le_energy_mul (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : VertexSpace.Space N m)
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    2 * ‖generator a b v i‖ ^ 2 ≤ energy a b τ v * (τ i.succ - τ i.castSucc) := by
  let w : Fin (m + 1) → ℝ := fun j ↦ 2 * ‖generator a b v j‖ ^ 2
  let δ : Fin (m + 1) → ℝ := fun j ↦ τ j.succ - τ j.castSucc
  have hw (j : Fin (m + 1)) : 0 ≤ w j := mul_nonneg (by norm_num) (sq_nonneg _)
  have hδ (j : Fin (m + 1)) : 0 < τ j.succ - τ j.castSucc :=
    sub_pos.mpr (hτ (show j.castSucc < j.succ by simp))
  have he : energy a b τ v = ∑ j, w j / δ j := energy_eq_frobenius_sum a b τ hv
  calc
    2 * ‖generator a b v i‖ ^ 2 = w i := rfl
    _ ≤ (∑ j, w j / δ j) * δ i := summand_le_weighted_sum w δ hw hδ i
    _ = energy a b τ v * (τ i.succ - τ i.castSucc) := by rw [← he]

theorem generator_norm_sq_le_energy_mul (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : VertexSpace.Space N m)
    (hv : v ∈ admissible a b m) (i : Fin (m + 1)) :
    ‖generator a b v i‖ ^ 2 ≤ energy a b τ v * (τ i.succ - τ i.castSucc) := by
  have h := twice_generator_norm_sq_le_energy_mul a b τ hτ v hv i
  nlinarith [sq_nonneg ‖generator a b v i‖]

def energySublevel (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ) (E : ℝ) :
    Set (VertexSpace.Space N m) := {v | v ∈ admissible a b m ∧ energy a b τ v ≤ E}

theorem sublevel_subset_boundedIncrements (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r) (hr : r < radius N)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    energySublevel a b τ E ⊆ boundedIncrements a b m r := by
  intro v hv
  apply (mem_boundedIncrements_iff a b hr v).mpr
  refine ⟨hv.1, fun i ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg (generator a b v i)) hr0).mp
  exact (generator_norm_sq_le_energy_mul a b τ hτ v hv.1 i).trans
    ((mul_le_mul_of_nonneg_right hv.2
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hmesh i))

theorem isCompact_energySublevel (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r) (hr : r < radius N)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    IsCompact (energySublevel a b τ E) := by
  have heq : energySublevel a b τ E =
      boundedIncrements a b m r ∩ energy a b τ ⁻¹' Iic E := by
    ext v
    constructor
    · intro hv
      exact ⟨sublevel_subset_boundedIncrements a b τ hτ hr0 hr hmesh hv, hv.2⟩
    · rintro ⟨hv, he⟩
      exact ⟨boundedIncrements_subset_admissible a b hr hv, he⟩
  rw [heq]
  have hc := (continuousOn_energy a b τ).mono (boundedIncrements_subset_admissible a b hr)
  exact (hc.preimage_isClosed_of_isClosed
    (isClosed_boundedIncrements a b m r) isClosed_Iic).isCompact

theorem isCompact_energySublevel_of_le (a b : SpecialSpace N)
    (τ : Fin (m + 2) → ℝ) {E B : ℝ} (hEB : E ≤ B)
    (hB : IsCompact (energySublevel a b τ B)) : IsCompact (energySublevel a b τ E) := by
  have he : ContinuousOn (energy a b τ) (energySublevel a b τ B) :=
    (continuousOn_energy a b τ).mono (fun _ hz ↦ hz.1)
  have heq : energySublevel a b τ E = energySublevel a b τ B ∩ energy a b τ ⁻¹' Iic E := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.trans hEB⟩, hz.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.2⟩
  rw [heq]
  exact (he.preimage_isClosed_of_isClosed hB.isClosed isClosed_Iic).isCompact

theorem exists_compact_sublevels_partition (N : Type*) [Fintype N] [DecidableEq N]
    (E : ℝ) (lower : ℕ) :
    ∃ m : ℕ, lower ≤ m ∧ ∀ a b : SpecialSpace N, ∀ C : ℝ, C ≤ E →
      IsCompact (energySublevel a b (time m) C) ∧
      ∀ v ∈ energySublevel a b (time m) C, ∀ i, ‖generator a b v i‖ ≤ radius N / 2 := by
  have hr0 : 0 < radius N / 2 := half_pos (radius_pos (N := N))
  have hr : radius N / 2 < radius N := half_lt_self (radius_pos (N := N))
  obtain ⟨m, hNm, hm⟩ := exists_small_energy_steps_above E hr0 lower
  refine ⟨m, hNm, fun a b C hC ↦ ?_⟩
  have hτ := strictMono_time m
  have hmesh (i : Fin (m + 1)) : C *
      (time m i.succ - time m i.castSucc) ≤ (radius N / 2) ^ 2 :=
    (mul_le_mul_of_nonneg_right hC
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hm i).le
  refine ⟨isCompact_energySublevel a b _ hτ hr0.le hr hmesh, ?_⟩
  intro v hv i
  exact ((mem_boundedIncrements_iff a b hr v).mp
    (sublevel_subset_boundedIncrements a b _ hτ hr0.le hr hmesh hv)).2 i

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
