import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth cochains for additive local cocycles

An actual subordinate smooth partition of unity turns an additive cocycle on
an open cover into a smooth local cochain.  The cocycle functions below are
represented by total functions, but only their restrictions to pairwise
overlaps are used: neither regularity nor identities are required elsewhere.
`partitionCochain_congr` explicitly proves independence of those other values.

No trivialization on a whole affine chart, holomorphic splitting, or
cohomology-vanishing statement is assumed.  The construction works for an
arbitrary indexed open cover, and therefore in particular for a finite one.
-/

noncomputable section

open Function Filter Set
open scoped Topology Manifold ContDiff BigOperators

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The local cochain formed from the actual overlap functions and a smooth
partition of unity.  At each point this is a finite sum. -/
def partitionCochain (ρ : SmoothPartitionOfUnity ι I M univ)
    (h : ι → ι → M → F) (i : ι) (x : M) : F :=
  ∑ᶠ k, ρ k x • h i k x

/-- Membership of the pointwise support identifies an actual overlap chart. -/
theorem mem_cover_of_mem_finsupport {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {x : M} {k : ι} (hk : k ∈ ρ.finsupport x) : x ∈ U k := by
  apply hρ k
  apply subset_tsupport
  simpa only [ρ.mem_finsupport, mem_support] using hk

/-- The cochain is smooth on its own chart even though an overlap function
need not be smooth outside that overlap.  The support of its coefficient is
exactly what makes the local smoothness argument valid. -/
theorem partitionCochain_contMDiffOn {U : ι → Set M} (hU : ∀ i, IsOpen (U i))
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j)) (i : ι) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (partitionCochain ρ h i) (U i) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply ρ.contMDiffAt_finsum
  intro k hk
  exact (hh i k).contMDiffAt ((hU i).inter (hU k) |>.mem_nhds ⟨hx, hρ k hk⟩)

/-- The construction only depends on values on genuine pairwise overlaps. -/
theorem partitionCochain_congr {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {h h' : ι → ι → M → F}
    (he : ∀ i j, EqOn (h i j) (h' i j) (U i ∩ U j)) (i : ι) :
    EqOn (partitionCochain ρ h i) (partitionCochain ρ h' i) (U i) := by
  intro x hx
  unfold partitionCochain
  rw [← ρ.sum_finsupport_smul_eq_finsum x (h i),
    ← ρ.sum_finsupport_smul_eq_finsum x (h' i)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [he i k ⟨hx, mem_cover_of_mem_finsupport hρ hk⟩]

/-- The coboundary of the constructed smooth local cochain is the original
additive cocycle, pointwise on every pairwise overlap. -/
theorem partitionCochain_sub_eq {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x)
    (i j : ι) {x : M} (hi : x ∈ U i) (hj : x ∈ U j) :
    partitionCochain ρ h i x - partitionCochain ρ h j x = h i j x := by
  classical
  unfold partitionCochain
  rw [← ρ.sum_finsupport_smul_eq_finsum x (h i),
    ← ρ.sum_finsupport_smul_eq_finsum x (h j), ← Finset.sum_sub_distrib]
  calc
    (∑ k ∈ ρ.finsupport x, (ρ k x • h i k x - ρ k x • h j k x)) =
        ∑ k ∈ ρ.finsupport x, ρ k x • h i j x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← smul_sub, sub_eq_iff_eq_add.mpr
        (hc i j k x hi hj (mem_cover_of_mem_finsupport hρ hk)).symm]
    _ = (∑ k ∈ ρ.finsupport x, ρ k x) • h i j x := (Finset.sum_smul ..).symm
    _ = h i j x := by rw [ρ.sum_finsupport x (mem_univ x), one_smul]

/-- The overlap identity holds on a full neighborhood of every overlap
point, so local differential operators can be applied to it. -/
theorem partitionCochain_sub_eventuallyEq {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i))
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x)
    (i j : ι) {x : M} (hi : x ∈ U i) (hj : x ∈ U j) :
    (fun y => partitionCochain ρ h i y - partitionCochain ρ h j y) =ᶠ[𝓝 x]
      h i j := by
  filter_upwards [((hU i).inter (hU j)).mem_nhds ⟨hi, hj⟩] with y hy
  exact partitionCochain_sub_eq hρ hc i j hy.1 hy.2

/-- If all partition functions except a distinguished one vanish at a point,
the distinguished cochain is zero there. -/
theorem partitionCochain_eq_zero_of_weights_single {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M univ} {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x)
    (j : ι) {x : M} (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) :
    partitionCochain ρ h j x = 0 := by
  have hdiag : h j j x = 0 := add_eq_left.mp (hc j j j x hj hj hj)
  have hz : ∀ k, ρ k x • h j k x = 0 := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [hdiag, smul_zero]
    · rw [hρ0 k hkj, zero_smul]
  simp only [partitionCochain, hz, finsum_zero]

/-- Near a region where the partition uses only chart `j`, each other local
cochain is exactly the original overlap function with chart `j`. -/
theorem partitionCochain_eq_overlap_of_weights_single {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x)
    (i j : ι) {x : M} (hi : x ∈ U i) (hj : x ∈ U j)
    (hρ0 : ∀ k, k ≠ j → ρ k x = 0) :
    partitionCochain ρ h i x = h i j x := by
  have he := partitionCochain_sub_eq hρ hc i j hi hj
  rwa [partitionCochain_eq_zero_of_weights_single hc j hj hρ0, sub_zero] at he

section Existence

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Every smooth additive cocycle on an open cover of a finite-dimensional
Hausdorff sigma-compact smooth real manifold admits a smooth local cochain.
The subordinate partition of unity is constructed, not supplied as a premise. -/
theorem exists_smooth_cocycle_cochain {U : ι → Set M} (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → M → F,
      (∀ i, ContMDiffOn I 𝓘(ℝ, F) ∞ (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ U hU
    (fun x _ => mem_iUnion.mpr (hcover x))
  exact ⟨partitionCochain ρ h, partitionCochain_contMDiffOn hU hρ hh,
    fun i j _ hi hj => partitionCochain_sub_eq hρ hc i j hi hj⟩

end Existence

/-- A concrete complex-plane version: a holomorphic additive cocycle gives
real-smooth local cochains, with no global holomorphic extension hypothesis. -/
theorem exists_smooth_cochain_of_holomorphic_cocycle {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → ℂ → ℂ,
      (∀ i, ContDiffOn ℝ ∞ (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  have hsmooth i j : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h i j) (U i ∩ U j) :=
    ((hh i j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ |>.contMDiffOn
  obtain ⟨s, hs, he⟩ := exists_smooth_cocycle_cochain hU hcover hsmooth hc
  exact ⟨s, fun i => (hs i).contDiffOn, he⟩

end Wikipedia.HopfProblem.HolomorphicCousin
