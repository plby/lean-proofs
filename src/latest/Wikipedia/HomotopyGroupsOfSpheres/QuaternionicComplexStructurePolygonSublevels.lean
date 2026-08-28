import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygon
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonSublevels

/-!
# Compact energy sublevels inside the complex-structure polygon domain

For sufficiently fine meshes, the energy bound puts all edge logarithms
strictly within the common short-logarithm radius. The restricted sublevel
is then exactly the inverse image of the actual symplectic sublevel, so it
is closed in the compact complex-structure vertex product.
-/

open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices Exponential
open NoExoticSixSphere.UniformTimePartition

variable {n m : ℕ}

def energySublevel (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) (E : ℝ) :
    Set (ComplexStructureVertices.Space n m) :=
  {v | v ∈ admissible a b m ∧ energy a b τ v ≤ E}

theorem smaller_closedBall {r : ℝ} (hr : r ≤ ShortLog.radius n) :
    closedBall (0 : SkewSpace n) r ⊆ compatibleTarget n :=
  (closedBall_subset_closedBall hr).trans (ShortLog.radius_closedBall n)

theorem admissible_of_ambient_sublevel (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ShortLog.radius n)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2)
    {v : ComplexStructureVertices.Space n m}
    (hv : forget v ∈ Polygon.energySublevel (toSymplectic a) (toSymplectic b) τ E) :
    v ∈ admissible a b m ∧ ∀ i, ‖generator a b v i‖ ≤ r := by
  have hb := (Polygon.mem_boundedIncrements_iff (toSymplectic a) (toSymplectic b)
    (smaller_closedBall hr.le) (forget v)).mp
      (Polygon.sublevel_subset_boundedIncrements (toSymplectic a) (toSymplectic b)
        τ hτ hr0 (smaller_closedBall hr.le) hmesh hv)
  have hn (i : Fin (m + 1)) : ‖generator a b v i‖ ≤ r := by
    rw [← generator_forget]
    exact hb.2 i
  exact ⟨admissible_of_forget a b hb.1 (fun i ↦ (hn i).trans_lt hr), hn⟩

theorem energySublevel_eq_preimage (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ShortLog.radius n)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    energySublevel a b τ E =
      forget ⁻¹' Polygon.energySublevel (toSymplectic a) (toSymplectic b) τ E := by
  ext v
  constructor
  · intro hv
    exact ⟨admissible_forget a b hv.1, hv.2⟩
  · intro hv
    exact ⟨(admissible_of_ambient_sublevel a b τ hτ hr0 hr hmesh hv).1, hv.2⟩

theorem isCompact_energySublevel (a b : ComplexStructures.Space n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) {E r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ShortLog.radius n)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) ≤ r ^ 2) :
    IsCompact (energySublevel a b τ E) := by
  rw [energySublevel_eq_preimage a b τ hτ hr0 hr hmesh]
  have hc := Polygon.isCompact_energySublevel (toSymplectic a) (toSymplectic b)
    τ hτ hr0 (smaller_closedBall hr.le) hmesh
  exact (hc.isClosed.preimage (continuous_forget (n := n) (m := m))).isCompact

theorem exists_compact_sublevels_partition (n : ℕ) (E : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : ComplexStructures.Space n, ∀ C : ℝ, C ≤ E →
      IsCompact (energySublevel a b (time m) C) ∧
      ∀ v ∈ energySublevel a b (time m) C, ∀ i,
        ‖generator a b v i‖ ≤ ShortLog.radius n / 2 := by
  have hr0 : 0 < ShortLog.radius n / 2 := half_pos (ShortLog.radius_pos n)
  have hr : ShortLog.radius n / 2 < ShortLog.radius n := half_lt_self (ShortLog.radius_pos n)
  obtain ⟨m, hNm, hm⟩ := exists_small_energy_steps_above E hr0 N
  refine ⟨m, hNm, fun a b C hC ↦ ?_⟩
  have hτ := strictMono_time m
  have hmesh (i : Fin (m + 1)) : C *
      (time m i.succ - time m i.castSucc) ≤ (ShortLog.radius n / 2) ^ 2 :=
    (mul_le_mul_of_nonneg_right hC
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans (hm i).le
  refine ⟨isCompact_energySublevel a b _ hτ hr0.le hr hmesh, ?_⟩
  intro v hv i
  exact (admissible_of_ambient_sublevel a b _ hτ hr0.le hr hmesh
    ⟨admissible_forget a b hv.1, hv.2⟩).2 i

theorem isCompact_energySublevel_of_le (a b : ComplexStructures.Space n)
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

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
