import Wikipedia.NoExoticSixSphere.JamesSphereReducedCone
import Wikipedia.NoExoticSixSphere.MetricPointCofibration
import Mathlib.Topology.Homotopy.Contractible

/-!
# Strong contraction of the actual reduced cone

Precomposing every prefix by a shrinking interval gives a jointly
continuous contraction. It stays in the actual cone and fixes the
constant prefix. The same contraction supplies neighborhood-deformation
data for the cone point, without a CW hypothesis.
-/

noncomputable section

open Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.ReducedCone

def contractedCurve (n : ℕ) : C(I × Space n, C(I, Sphere (n + 1))) :=
  (⟨fun p : (I × Space n) × I ↦ p.1.2.val (σ p.1.1 * p.2),
    continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst.snd).prodMk
        ((continuous_symm.comp continuous_fst.fst).mul continuous_snd))⟩ :
    C((I × Space n) × I, Sphere (n + 1))).curry

theorem contractedCurve_apply (n : ℕ) (s : I) (p : Space n) (t : I) :
    contractedCurve n (s, p) t = p.val (σ s * t) := rfl

theorem contractedCurve_presentation (n : ℕ) (s : I) (x : Sphere n) (t : I) :
    contractedCurve n (s, presentation n (x, t)) = prefixCurve n (x, σ s * t) := by
  apply ContinuousMap.ext
  intro u
  change loopEvaluation n (x, t * (σ s * u)) = loopEvaluation n (x, (σ s * t) * u)
  rw [mul_left_comm t (σ s) u, ← mul_assoc]

theorem contractedCurve_mem (n : ℕ) (s : I) (p : Space n) :
    contractedCurve n (s, p) ∈ space n := by
  obtain ⟨⟨x, t⟩, rfl⟩ := presentation_surjective n p
  rw [contractedCurve_presentation]
  exact Set.mem_range_self (x, σ s * t)

def contract (n : ℕ) : C(I × Space n, Space n) :=
  ⟨fun p ↦ ⟨contractedCurve n p, contractedCurve_mem n p.1 p.2⟩,
    (contractedCurve n).continuous.subtype_mk _⟩

theorem contract_zero (n : ℕ) (p : Space n) : contract n (0, p) = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change p.val (σ 0 * t) = p.val t
  rw [symm_zero, one_mul]

theorem contract_one (n : ℕ) (p : Space n) : contract n (1, p) = base n := by
  obtain ⟨⟨x, t⟩, rfl⟩ := presentation_surjective n p
  apply Subtype.ext
  change contractedCurve n (1, presentation n (x, t)) = (base n).val
  rw [contractedCurve_presentation, symm_one, zero_mul, prefix_zero, base_val]

theorem contract_base (n : ℕ) (s : I) : contract n (s, base n) = base n := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (base n).val (σ s * t) = (base n).val t
  rw [base_val]
  rfl

def contraction (n : ℕ) : (ContinuousMap.id (Space n)).HomotopyRel
    (ContinuousMap.const (Space n) (base n)) {base n} where
  toContinuousMap := contract n
  map_zero_left := contract_zero n
  map_one_left := contract_one n
  prop' s p hp := by
    have he : p = base n := hp
    subst p
    exact contract_base n s

instance (n : ℕ) : ContractibleSpace (Space n) :=
  (contractible_iff_id_nullhomotopic (Space n)).mpr
    ⟨base n, ⟨(contraction n).toHomotopy⟩⟩

def pointData (n : ℕ) : NeighborhoodDeformation.Data (MetricPointCofibration.inclusion (base n)) :=
  MetricPointCofibration.data (base n) isOpen_univ (Set.subset_univ _)
    ((contract n).comp
      ((ContinuousMap.id I).prodMap ⟨Subtype.val, continuous_subtype_val⟩))
    (fun p ↦ contract_zero n p.val)
    (fun t p hp ↦ by change contract n (t, p.val) = base n; rw [hp]; exact contract_base n t)
    (fun p ↦ contract_one n p.val)

theorem point_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (MetricPointCofibration.inclusion (base n)) :=
  NeighborhoodDeformation.hasHomotopyExtension (pointData n) IsEmbedding.subtypeVal

end NoExoticSixSphere.JamesSphere.ReducedCone
