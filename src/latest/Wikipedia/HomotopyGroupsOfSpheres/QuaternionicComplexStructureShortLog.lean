import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureCompatibleLog

/-!
# A symmetric short-logarithm domain for quaternionic complex structures

One fixed positive radius works at every complex structure. Relative
logarithms on this open domain are compatible with the orthogonal logarithm,
anticommute with the starting structure, and change sign on reversal.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.ShortLog

open Exponential CompatibleLog NoExoticSixSphere.UniformTimePartition

variable {n : ℕ}

private theorem real_norm_neg {V : Type*} [NormedAddCommGroup V] (v : V) :
    ‖-v‖ = ‖v‖ := norm_neg v

def radius (n : ℕ) : ℝ := (exists_compatible_radius n).choose

theorem radius_pos (n : ℕ) : 0 < radius n :=
  (exists_compatible_radius n).choose_spec.1

theorem radius_lt_pi (n : ℕ) : radius n < Real.pi :=
  (exists_compatible_radius n).choose_spec.2.1

theorem radius_closedBall (n : ℕ) :
    closedBall (0 : SkewSpace n) (radius n) ⊆ compatibleTarget n :=
  (exists_compatible_radius n).choose_spec.2.2

theorem logarithm_inv {a : symplecticSubgroup n} {r : ℝ}
    (hr : closedBall (0 : SkewSpace n) r ⊆ (Exponential.logarithmChart n).target)
    (ha : a ∈ groupLogarithmBall n r) :
    a⁻¹ ∈ groupLogarithmBall n r ∧
      Exponential.logarithmChart n a⁻¹ = -(Exponential.logarithmChart n a) := by
  let K := Exponential.logarithmChart n a
  have hK : -K ∈ (Exponential.logarithmChart n).target := by
    apply hr
    rw [mem_closedBall, dist_zero_right (-K), real_norm_neg (V := SkewSpace n)]
    exact ha.2.le
  have he : exp (-K) = a⁻¹ := by rw [exp_neg, exp_logarithmChart a ha.1]
  have hs : a⁻¹ ∈ (Exponential.logarithmChart n).source := by
    rw [← he]
    exact exp_mem_logarithmChart_source (-K) hK
  have hl : Exponential.logarithmChart n a⁻¹ = -K := by
    rw [← he]
    exact Exponential.logarithmChart_exp (-K) hK
  refine ⟨⟨hs, ?_⟩, hl⟩
  rw [hl, real_norm_neg (V := SkewSpace n)]
  exact ha.2

def domain (n : ℕ) : Set (Space n × Space n) :=
  {p | Cayley.relative p.1 p.2 ∈ groupLogarithmBall n (radius n)}

theorem isOpen_domain (n : ℕ) : IsOpen (domain n) :=
  (isOpen_groupLogarithmBall n (radius n)).preimage continuous_relative_pair

theorem diagonal_mem_domain (J : Space n) : (J, J) ∈ domain n := by
  change Cayley.relative J J ∈ groupLogarithmBall n (radius n)
  rw [Cayley.relative_self]
  exact one_mem_groupLogarithmBall n (radius_pos n)

def generator (J J' : Space n) : SkewSpace n :=
  Exponential.logarithmChart n (Cayley.relative J J')

theorem generator_norm_lt {J J' : Space n} (h : (J, J') ∈ domain n) :
    ‖generator J J'‖ < radius n := h.2

theorem generator_mem_target {J J' : Space n} (h : (J, J') ∈ domain n) :
    generator J J' ∈ compatibleTarget n := by
  apply radius_closedBall n
  rw [mem_closedBall, dist_zero_right (generator J J')]
  exact h.2.le

theorem relative_mem_compatibleDomain {J J' : Space n} (h : (J, J') ∈ domain n) :
    Cayley.relative J J' ∈ compatibleDomain n :=
  ⟨h.1, (generator_mem_target h).2⟩

theorem generator_anticommute {J J' : Space n} (h : (J, J') ∈ domain n) :
    J.val.val.comp (generator J J').val = -((generator J J').val.comp J.val.val) :=
  logarithm_anticommute J (Cayley.relative J J')
    (fun _ hK ↦ (radius_closedBall n hK).1) h (Cayley.relative_reversible J J')

theorem exp_generator {J J' : Space n} (h : (J, J') ∈ domain n) :
    exp (generator J J') = Cayley.relative J J' :=
  exp_logarithmChart _ h.1

theorem generator_self (J : Space n) : generator J J = 0 := by
  rw [generator, Cayley.relative_self, Exponential.logarithmChart_one]

theorem relative_swap (J J' : Space n) :
    Cayley.relative J' J = (Cayley.relative J J')⁻¹ := by
  simp only [Cayley.relative, mul_inv_rev, inv_inv]

theorem swap_mem_domain {J J' : Space n} (h : (J, J') ∈ domain n) :
    (J', J) ∈ domain n := by
  change Cayley.relative J' J ∈ groupLogarithmBall n (radius n)
  rw [relative_swap]
  exact (logarithm_inv (fun _ hK ↦ (radius_closedBall n hK).1) h).1

theorem generator_swap {J J' : Space n} (h : (J, J') ∈ domain n) :
    generator J' J = -(generator J J') := by
  change Exponential.logarithmChart n (Cayley.relative J' J) = _
  rw [relative_swap]
  exact (logarithm_inv (fun _ hK ↦ (radius_closedBall n hK).1) h).2

theorem continuous_generator :
    Continuous (fun p : domain n ↦ generator p.val.1 p.val.2) :=
  (Exponential.logarithmChart n).contMDiffOn_toFun.continuousOn.comp_continuous
    (continuous_relative_pair.comp continuous_subtype_val) (fun p ↦ p.property.1)

theorem exists_uniform_partition {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Space n)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x), H (u, x)) ∈ domain n := by
  let F : C(I × X, symplecticSubgroup n) :=
    ⟨fun z ↦ toSymplectic (H z), continuous_toSymplectic.comp H.continuous⟩
  exact Exponential.exists_uniform_increment_partition F
    (groupLogarithmBall n (radius n))
    ((isOpen_groupLogarithmBall n (radius n)).mem_nhds
      (one_mem_groupLogarithmBall n (radius_pos n))) N

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.ShortLog
