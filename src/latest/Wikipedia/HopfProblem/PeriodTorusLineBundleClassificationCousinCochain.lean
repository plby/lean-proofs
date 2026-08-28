import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycle
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic

/-!
# The actual smooth cochain of a two-variable holomorphic cocycle

The input is an arbitrary indexed open cover of `ℂ × ℂ` and holomorphic
additive transition functions on its pairwise overlaps.  A subordinate
smooth partition of unity is constructed from that cover.  Its locally
finite weighted sum gives real-smooth local functions whose differences
are proved to be the original transitions.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

local notation "Iℝ" => modelWithCornersSelf ℝ (ℂ × ℂ)
local notation "I₁ℝ" => modelWithCornersSelf ℝ ℂ

/-- Genuine additive holomorphic transition data on an arbitrary open cover.
No global cochain, forcing term, or Cousin solution occurs among the fields. -/
structure Cocycle (ι : Type*) where
  domain : ι → Set (ℂ × ℂ)
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ x, ∃ i, x ∈ domain i
  transition : ι → ι → ℂ × ℂ → ℂ
  holomorphic : ∀ i j, AnalyticOnNhd ℂ (transition i j) (domain i ∩ domain j)
  additive : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition i j x + transition j k x = transition i k x

namespace Cocycle

variable {ι : Type*} (C : Cocycle ι)

theorem exists_subordinatePartition :
    ∃ ρ : SmoothPartitionOfUnity ι Iℝ (ℂ × ℂ) univ, ρ.IsSubordinate C.domain :=
  SmoothPartitionOfUnity.exists_isSubordinate Iℝ isClosed_univ C.domain C.isOpen_domain
    (fun x _ => mem_iUnion.mpr (C.cover x))

/-- An actual subordinate partition, obtained from the general existence theorem. -/
def partition : SmoothPartitionOfUnity ι Iℝ (ℂ × ℂ) univ :=
  C.exists_subordinatePartition.choose

theorem partition_subordinate : C.partition.IsSubordinate C.domain :=
  C.exists_subordinatePartition.choose_spec

/-- The explicit locally finite weighted sum of the original transitions. -/
def cochain (i : ι) : ℂ × ℂ → ℂ :=
  HolomorphicCousin.partitionCochain C.partition C.transition i

theorem cochain_contDiffOn (i : ι) : ContDiffOn ℝ ∞ (C.cochain i) (C.domain i) := by
  have ht (j k : ι) : ContMDiffOn Iℝ I₁ℝ ∞ (C.transition j k) (C.domain j ∩ C.domain k) :=
    ((C.holomorphic j k).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
      |>.contMDiffOn
  exact (HolomorphicCousin.partitionCochain_contMDiffOn C.isOpen_domain
    C.partition_subordinate ht i).contDiffOn

theorem cochain_contDiffAt {i : ι} {x : ℂ × ℂ} (hx : x ∈ C.domain i) :
    ContDiffAt ℝ ∞ (C.cochain i) x :=
  (C.cochain_contDiffOn i x hx).contDiffAt ((C.isOpen_domain i).mem_nhds hx)

/-- The constructed smooth cochain has precisely the original coboundary. -/
theorem cochain_sub (i j : ι) {x : ℂ × ℂ}
    (hi : x ∈ C.domain i) (hj : x ∈ C.domain j) :
    C.cochain i x - C.cochain j x = C.transition i j x :=
  HolomorphicCousin.partitionCochain_sub_eq C.partition_subordinate C.additive i j hi hj

theorem cochain_sub_eventuallyEq (i j : ι) {x : ℂ × ℂ}
    (hi : x ∈ C.domain i) (hj : x ∈ C.domain j) :
    (fun y => C.cochain i y - C.cochain j y) =ᶠ[𝓝 x] C.transition i j :=
  HolomorphicCousin.partitionCochain_sub_eventuallyEq C.isOpen_domain
    C.partition_subordinate C.additive i j hi hj

theorem cochain_sub_analyticOnNhd (i j : ι) :
    AnalyticOnNhd ℂ (fun x => C.cochain i x - C.cochain j x) (C.domain i ∩ C.domain j) := by
  apply AnalyticOnNhd.congr ((C.isOpen_domain i).inter (C.isOpen_domain j)) (C.holomorphic i j)
  intro x hx
  exact (C.cochain_sub i j hx.1 hx.2).symm

/-- An actual local representative is selected at each point; later gluing
proves that the resulting derivative coefficients are independent of the selection. -/
def indexAt (x : ℂ × ℂ) : ι := (C.cover x).choose

theorem mem_domain_indexAt (x : ℂ × ℂ) : x ∈ C.domain (C.indexAt x) :=
  (C.cover x).choose_spec

end Cocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
