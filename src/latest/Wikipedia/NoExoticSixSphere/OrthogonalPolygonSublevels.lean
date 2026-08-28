import Wikipedia.NoExoticSixSphere.OrthogonalCompactLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalShortPolygons
import Wikipedia.NoExoticSixSphere.HilbertSchmidtBound
import Wikipedia.NoExoticSixSphere.UniformTimePartition

/-!
# Compact energy sublevels of sufficiently finely partitioned polygons

A bound on energy bounds each logarithm by the square root of energy times
the adjacent time length. If these bounds fit in a closed ball in the
logarithm target, the sublevel is a closed subset of the actual compact
vertex product and lies entirely within the admissible chart domain.
-/

open Set Metric

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  HilbertSchmidt

variable {n m : ℕ}

def boundedIncrements (a b : OrthogonalOperators n) (m : ℕ) (r : ℝ) : Set (Space n m) :=
  {v | ∀ i, increment a b v i ∈ compactIncrements n r}

theorem isClosed_boundedIncrements (a b : OrthogonalOperators n) (m : ℕ) (r : ℝ) :
    IsClosed (boundedIncrements a b m r) := by
  change IsClosed {v : Space n m | ∀ i, increment a b v i ∈ compactIncrements n r}
  rw [ofPred_forall]
  exact isClosed_iInter (fun i ↦ (isCompact_compactIncrements n r).isClosed.preimage
    (contMDiff_increment a b i).continuous)

theorem isCompact_boundedIncrements (a b : OrthogonalOperators n) (m : ℕ) (r : ℝ) :
    IsCompact (boundedIncrements a b m r) := (isClosed_boundedIncrements a b m r).isCompact

theorem mem_boundedIncrements_iff (a b : OrthogonalOperators n) {r : ℝ}
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target) (v : Space n m) :
    v ∈ boundedIncrements a b m r ↔ v ∈ admissible a b m ∧ ∀ i, ‖generator a b v i‖ ≤ r := by
  constructor
  · intro hv
    exact ⟨fun i ↦ ((mem_compactIncrements_iff hr _).mp (hv i)).1,
      fun i ↦ ((mem_compactIncrements_iff hr _).mp (hv i)).2⟩
  · rintro ⟨hv, hn⟩ i
    exact (mem_compactIncrements_iff hr _).mpr ⟨hv i, hn i⟩

theorem boundedIncrements_subset_admissible (a b : OrthogonalOperators n) {r : ℝ}
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target) :
    boundedIncrements a b m r ⊆ admissible a b m :=
  fun v hv ↦ ((mem_boundedIncrements_iff a b hr v).mp hv).1

theorem generator_squareNorm_le_energy_mul (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m) (i : Fin (m + 1)) :
    squareNorm (generator a b v i : Vector n →L[ℝ] Vector n) ≤
      energy a b τ v * (τ i.succ - τ i.castSucc) := by
  have hδ (j : Fin (m + 1)) : 0 < τ j.succ - τ j.castSucc :=
    sub_pos.mpr (hτ (show j.castSucc < j.succ by simp))
  apply (div_le_iff₀ (hδ i)).mp
  unfold energy
  exact Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (m + 1)))) ↦
      div_nonneg (squareNorm_nonneg (generator a b v j : Vector n →L[ℝ] Vector n))
        (hδ j).le) (Finset.mem_univ i)

theorem generator_norm_sq_le_energy_mul (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m) (i : Fin (m + 1)) :
    ‖generator a b v i‖ ^ 2 ≤ energy a b τ v * (τ i.succ - τ i.castSucc) :=
  (norm_sq_le_squareNorm (generator a b v i : Vector n →L[ℝ] Vector n)).trans
    (generator_squareNorm_le_energy_mul a b τ hτ v i)

def energySublevel (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (E : ℝ) :
    Set (Space n m) := {v | v ∈ admissible a b m ∧ energy a b τ v ≤ E}

theorem sublevel_subset_boundedIncrements (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r)
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    energySublevel a b τ E ⊆ boundedIncrements a b m r := by
  intro v hv
  apply (mem_boundedIncrements_iff a b hr v).mpr
  refine ⟨hv.1, fun i ↦ ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) hr0).mp
  exact (generator_norm_sq_le_energy_mul a b τ hτ v i).trans
    ((mul_le_mul_of_nonneg_right hv.2
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hmesh i))

theorem isCompact_energySublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r)
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target)
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
  exact ((contMDiffOn_energy a b τ).continuousOn.mono
    (boundedIncrements_subset_admissible a b hr)).preimage_isClosed_of_isClosed
      (isClosed_boundedIncrements a b m r) isClosed_Iic |>.isCompact

theorem energySublevel_subset_shortDomain (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r) (hrπ : r < Real.pi)
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    energySublevel a b τ E ⊆ shortDomain a b m := by
  intro v hv
  have hb := (mem_boundedIncrements_iff a b hr v).mp
    (sublevel_subset_boundedIncrements a b τ hτ hr0 hr hmesh hv)
  exact ⟨hb.1, fun i ↦ (hb.2 i).trans_lt hrπ⟩

/-- Arbitrarily fine uniform partitions make every sublevel below a given
energy bound compact and contained in the strictly short domain, for all endpoints. -/
theorem exists_compact_sublevels_partition (n : ℕ) (E : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : OrthogonalOperators n, ∀ C : ℝ, C ≤ E →
      IsCompact (energySublevel a b (UniformTimePartition.time m) C) ∧
      energySublevel a b (UniformTimePartition.time m) C ⊆ shortDomain a b m := by
  obtain ⟨r, hr0, hrπ, hr⟩ := exists_compactLogarithm_radius n
  obtain ⟨m, hNm, hm⟩ := UniformTimePartition.exists_small_energy_steps_above E hr0 N
  refine ⟨m, hNm, fun a b C hC ↦ ?_⟩
  have hτ := UniformTimePartition.strictMono_time m
  have hmesh (i : Fin (m + 1)) : C *
      (UniformTimePartition.time m i.succ - UniformTimePartition.time m i.castSucc) ≤ r ^ 2 :=
    (mul_le_mul_of_nonneg_right hC
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hm i).le
  exact ⟨isCompact_energySublevel a b _ hτ hr0.le hr hmesh,
    energySublevel_subset_shortDomain a b _ hτ hr0.le hrπ hr hmesh⟩

end NoExoticSixSphere.OrthogonalPolygon
