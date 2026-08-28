import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalCompactLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalExponentialSubdivision

/-!
# Compatible local logarithms for symplectic polygon calculations

On a proved identity neighborhood, the native symplectic logarithm agrees
with the real orthogonal logarithm. Compact small exponential neighborhoods
and compact-family subdivisions stay in that neighborhood. No global
logarithm or global restriction of the orthogonal chart is asserted.
-/

noncomputable section

open scoped Manifold ContDiff Topology unitInterval
open Set Metric Filter

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

def compatibleTarget (n : ℕ) : Set (SkewSpace n) :=
  (logarithmChart n).target ∩ (toOrthogonalSkew n) ⁻¹'
    (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).target

theorem isOpen_compatibleTarget (n : ℕ) : IsOpen (compatibleTarget n) :=
  (logarithmChart n).open_target.inter
    ((NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).open_target.preimage
      (continuous_toOrthogonalSkew n))

theorem zero_mem_compatibleTarget (n : ℕ) : 0 ∈ compatibleTarget n :=
  ⟨zero_mem_logarithmChart_target n, by
    change toOrthogonalSkew n 0 ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).target
    rw [map_zero]
    exact NoExoticSixSphere.OrthogonalExponential.zero_mem_logarithmChart_target _⟩

def compatibleDomain (n : ℕ) : Set (symplecticSubgroup n) :=
  {a | a ∈ (logarithmChart n).source ∧
    toOrthogonalSkew n (logarithmChart n a) ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).target}

theorem isOpen_compatibleDomain (n : ℕ) : IsOpen (compatibleDomain n) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hs := (logarithmChart n).open_source.mem_nhds ha.1
  have hc : ContinuousAt (fun b => toOrthogonalSkew n (logarithmChart n b)) a :=
    (continuous_toOrthogonalSkew n).continuousAt.comp
      ((logarithmChart n).contMDiffOn_toFun.continuousOn.continuousAt hs)
  have ht := hc
    ((NoExoticSixSphere.OrthogonalExponential.logarithmChart
      (4 * n + 4)).open_target.mem_nhds ha.2)
  filter_upwards [hs, ht] with b hb ht
  exact ⟨hb, ht⟩

theorem one_mem_compatibleDomain (n : ℕ) : 1 ∈ compatibleDomain n := by
  refine ⟨one_mem_logarithmChart_source n, ?_⟩
  rw [logarithmChart_one, map_zero]
  exact NoExoticSixSphere.OrthogonalExponential.zero_mem_logarithmChart_target _

theorem orthogonal_exp_logarithm (a : symplecticSubgroup n)
    (ha : a ∈ (logarithmChart n).source) :
    NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (logarithmChart n a)) =
      a.val := congrArg (fun b : symplecticSubgroup n => b.val) (exp_logarithmChart a ha)

theorem compatibleDomain_mem_orthogonal_source (a : symplecticSubgroup n)
    (ha : a ∈ compatibleDomain n) :
    a.val ∈ (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4)).source := by
  have h := NoExoticSixSphere.OrthogonalExponential.exp_mem_logarithmChart_source
    (toOrthogonalSkew n (logarithmChart n a)) ha.2
  rwa [orthogonal_exp_logarithm a ha.1] at h

theorem orthogonal_logarithm_eq (a : symplecticSubgroup n) (ha : a ∈ compatibleDomain n) :
    NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4) a.val =
      toOrthogonalSkew n (logarithmChart n a) := by
  rw [← orthogonal_exp_logarithm a ha.1]
  exact NoExoticSixSphere.OrthogonalExponential.logarithmChart_exp _ ha.2

theorem orthogonal_logarithm_mem_commutant (a : symplecticSubgroup n)
    (ha : a ∈ compatibleDomain n) :
    (NoExoticSixSphere.OrthogonalExponential.logarithmChart (4 * n + 4) a.val).val ∈
      commutant n := by
  rw [orthogonal_logarithm_eq a ha]
  exact (logarithmChart n a).property.2

theorem exp_mem_logarithmChart_source (K : SkewSpace n)
    (hK : K ∈ (logarithmChart n).target) : exp K ∈ (logarithmChart n).source := by
  have hs := (logarithmChart n).map_target' hK
  have he : exp K = (logarithmChart n).symm K := by
    calc
      exp K = exp (logarithmChart n ((logarithmChart n).symm K)) :=
        congrArg exp ((logarithmChart n).right_inv' hK).symm
      _ = (logarithmChart n).symm K := exp_logarithmChart _ hs
  rwa [he]

theorem exp_mem_compatibleDomain (K : SkewSpace n) (hK : K ∈ compatibleTarget n) :
    exp K ∈ compatibleDomain n := by
  refine ⟨exp_mem_logarithmChart_source K hK.1, ?_⟩
  rw [logarithmChart_exp K hK.1]
  exact hK.2

theorem exists_compatible_radius (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r < Real.pi ∧ closedBall (0 : SkewSpace n) r ⊆ compatibleTarget n := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_compatibleTarget n).mem_nhds (zero_mem_compatibleTarget n))
  let r := min (ε / 2) (Real.pi / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrπ : r < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  exact ⟨r, hr, hrπ, fun _ hK => hball (lt_of_le_of_lt hK hrε)⟩

def compactIncrements (n : ℕ) (r : ℝ) : Set (symplecticSubgroup n) :=
  exp '' closedBall (0 : SkewSpace n) r

theorem isCompact_compactIncrements (n : ℕ) (r : ℝ) : IsCompact (compactIncrements n r) :=
  (isCompact_closedBall (0 : SkewSpace n) r).image contMDiff_exp.continuous

theorem mem_compactIncrements_iff {r : ℝ}
    (hr : closedBall (0 : SkewSpace n) r ⊆ compatibleTarget n) (a : symplecticSubgroup n) :
    a ∈ compactIncrements n r ↔ a ∈ compatibleDomain n ∧ ‖logarithmChart n a‖ ≤ r := by
  constructor
  · rintro ⟨K, hK, rfl⟩
    refine ⟨exp_mem_compatibleDomain K (hr hK), ?_⟩
    rw [logarithmChart_exp K (hr hK).1]
    calc
      ‖K‖ = dist K (0 : SkewSpace n) := (dist_zero_right K).symm
      _ ≤ r := hK
  · intro ha
    refine ⟨logarithmChart n a, ?_, exp_logarithmChart a ha.1.1⟩
    change dist (logarithmChart n a) (0 : SkewSpace n) ≤ r
    calc
      _ = ‖logarithmChart n a‖ := dist_zero_right (logarithmChart n a)
      _ ≤ r := ha.2

/-- Compact symplectic path families have uniform increments in any identity neighborhood. -/
theorem exists_incrementSubdivision {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, symplecticSubgroup n)) (U : Set (symplecticSubgroup n))
    (hU : U ∈ nhds (1 : symplecticSubgroup n)) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x, (H (t i, x))⁻¹ * H (u, x) ∈ U := by
  rw [nhds_subtype] at hU
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hU
  let HO : C(I × X, OrthogonalOperators (4 * n + 4)) :=
    ⟨fun p => (H p).val, continuous_subtype_val.comp H.continuous⟩
  obtain ⟨t, ht0, hmono, hend, ht⟩ :=
    NoExoticSixSphere.OrthogonalExponential.exists_incrementSubdivision HO V hV
  exact ⟨t, ht0, hmono, hend, fun i u hu x => hsub (ht i u hu x)⟩

theorem exists_small_compatible_subdivision {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, symplecticSubgroup n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        (H (t i, x))⁻¹ * H (u, x) ∈ compatibleDomain n ∧
          ‖logarithmChart n ((H (t i, x))⁻¹ * H (u, x))‖ < ε := by
  apply exists_incrementSubdivision H
    {a | a ∈ compatibleDomain n ∧ ‖logarithmChart n a‖ < ε}
  have hs := (isOpen_compatibleDomain n).mem_nhds (one_mem_compatibleDomain n)
  have hc : ContinuousAt (logarithmChart n) (1 : symplecticSubgroup n) :=
    (logarithmChart n).contMDiffOn_toFun.continuousOn.continuousAt
      ((logarithmChart n).open_source.mem_nhds (one_mem_logarithmChart_source n))
  have hn : ‖logarithmChart n (1 : symplecticSubgroup n)‖ < ε := by
    rw [logarithmChart_one]
    have hz : ‖(0 : SkewSpace n)‖ = 0 := norm_zero (E := SkewSpace n)
    rwa [hz]
  have hcn : ContinuousAt (fun a : symplecticSubgroup n => ‖logarithmChart n a‖) 1 :=
    ContinuousAt.norm (E := SkewSpace n) hc
  have ht := hcn (gt_mem_nhds hn)
  filter_upwards [hs, ht] with a ha hn
  exact ⟨ha, hn⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential
