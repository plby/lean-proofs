/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceProfileConditions
import ErdosProblems.Erdos4b.SourceDyadicPrimeSupport
import ErdosProblems.Erdos4b.SourceDyadicSmoothBudget
import ErdosProblems.Erdos4b.SourceDyadicBoundaryBudget
import ErdosProblems.Erdos4b.SourceDyadicTailBudget
import ErdosProblems.Erdos4b.SourceFreshPrimeReserve
import ErdosProblems.Erdos4b.SourceFiniteCover

/-!
# The simultaneous dyadic specialization of the finite global cover

One ray and one absolute residual-mass constant work for all multipliers
and all eligible smooth profiles. The only remaining variational input
is an actual profile with sufficiently small exponential miss factor.
-/

universe u

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

def dyadicProfileCoverLevel {I : Type*} {K : ℕ} (D : ℕ)
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) : ℝ :=
  dyadicAllocationDensity D * sourceProfileRatio S F G / 16

theorem dyadicProfileCoverLevel_eq {I : Type*} {K : ℕ} (D : ℕ)
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) :
    dyadicProfileCoverLevel D S F G = dyadicAllocationDensity D *
      (∑ h : Fin K, sourcePinnedFirstVariationalIntegral S F h *
        sourcePinnedCompanionVariationalIntegral K G) /
        (16 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) := by
  unfold dyadicProfileCoverLevel sourceProfileRatio
  ring

private theorem four_budgets_lt_reserve {g smooth tail boundary missed reserve : ℝ}
    (hg : 0 ≤ g) (hs : smooth ≤ (1 / 128 : ℝ) * g) (ht : tail ≤ (1 / 128 : ℝ) * g)
    (hb : boundary ≤ (1 / 128 : ℝ) * g) (hm : missed ≤ (1 / 128 : ℝ) * g)
    (hr : g / 16 ≤ reserve) : smooth + tail + boundary + missed < reserve + 1 := by
  linarith

theorem exists_dyadicRay_profileCovers :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type u) (K D : ℕ) (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ),
      0 < D → SourceProfileConditions S F G →
      Real.exp (-dyadicProfileCoverLevel D S F G) * C * D ≤ (1 / 128 : ℝ) →
      ∀ᶠ r in atTop, ∃ data : SurvivorCoverData (D * intervalLength a r)
          (smoothFrontier r) (residualPrimeFrontier a r),
        smoothFrontier r ≤ residualPrimeFrontier a r ∧
        residualPrimeFrontier a r ≤ primaryFrontier a r ∧
        (∀ p ∈ data.measurePrimes, p ≤ primaryFrontier a r) ∧
        (∀ p ∈ data.freshPrimes, p ≤ primaryFrontier a r) := by
  classical
  obtain ⟨a, hsmooth⟩ := exists_dyadicRay_smoothException_vanishing
  obtain ⟨C, hC, htotal⟩ := exists_uniform_sum_dyadicResidualPrimeFiber_total_bound
  refine ⟨a, C, hC, ?_⟩
  intro I K D S F G hD hP hmiss
  have hcoverage := eventually_dyadicAllocated_residualCoverage hP.dimension_pos S F G
    hP.first_compact hP.first_smooth hP.companion_compact hP.companion_smooth
    hP.first_simplex hP.first_ceiling hP.companion_support a hD hP.main_pos hP.pinned_pos
  have hnormal := uniform_dyadicSourceResidueNormalization_pos_and_upper hP.dimension_pos S F G
    hP.first_compact hP.first_smooth hP.companion_compact hP.companion_smooth
    hP.first_simplex hP.first_ceiling hP.companion_support a D hP.main_pos
  have hfresh := (tendsto_dyadicPrimaryFrontier_atTop a).eventually eventually_sourceFreshPrimeCount_ge
  filter_upwards [hsmooth D hD (1 / 128) (by norm_num), htotal a D hD,
    eventually_sum_dyadicBoundaryPrimeCount_le hP.dimension_pos hD a (by norm_num : (0 : ℝ) < 1 / 128),
    eventually_sum_dyadicLargeCofactorPrimeCount_le hD a (by norm_num : (0 : ℝ) < 1 / 128),
    hcoverage, hnormal, eventually_dyadicAllocated_intervals a hD,
    eventually_sum_dyadicAllocatedLength_le_quarter a hD, hfresh,
    eventually_dyadicSmoothFrontier_le_residual a, eventually_ge_atTop 2]
    with r hs ht hb hl hc hn ha hlength hfr hyz hr
  let X := primaryFrontier a r
  let U := D * intervalLength a r
  let y := smoothFrontier r
  let z := residualPrimeFrontier a r
  let B := D * fullResidualCofactorCutoff r
  let M := smallResidualCofactorCutoff D r
  let H := dyadicPinnedBoundary K a r
  let E := residualEvenCofactors 0 M
  let length := dyadicAllocatedLength a D r
  let base := (X + 1) / 2
  let A := sourceAllocatedStart E length base
  let Z := sourceAllocatedEnd E length base
  let Q := fun m ↦ auxiliaryPrimeInterval (A m) (Z m)
  let total := ∑ m ∈ E, length m
  let R := auxiliaryPrimeInterval (base + total) X
  let N := max (jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r)) y
  let μ := fun m q b ↦ dyadicSourceResidueMass S F G a D r m q N b
  let t := dyadicProfileCoverLevel D S F G
  let g : ℝ := (X : ℝ) / dyadicAmbientScale a r
  have hN : jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N :=
    le_max_left _ _
  have hYN : smoothFrontier r ≤ N := le_max_right _ _
  have hEsmall : ∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ M := by
    intro m hm
    have hd := mem_residualEvenCofactors.mp hm
    exact ⟨hd.1, hd.2.2, hd.2.1⟩
  have hErange : ∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ B := by
    intro m hm
    have hd := hEsmall m hm
    exact ⟨hd.1, hd.2.1, hd.2.2.trans (smallResidualCofactorCutoff_le_full D r)⟩
  have hall := ha E hErange
  have hlen : (total : ℝ) ≤ (X : ℝ) / 4 := hlength E hErange
  have hXfour : 4 ≤ X := by
    have he : 2 ≤ primaryExponent a r := hr.trans (self_le_primaryExponent a r)
    change 4 ≤ 2 ^ primaryExponent a r
    simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) he
  have hreserveData := sourceFreshInterval_length hXfour hlen
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hg : 0 < g := div_pos (by exact_mod_cast primaryFrontier_pos a r) hV
  have hqdata : ∀ m ∈ E, ∀ q ∈ Q m, dyadicSourceRange a D r m q := by
    intro m hm q hqm
    have hmdata := hErange m hm
    have hi := hall.1 m hm
    have hqd := mem_auxiliaryPrimeInterval.mp hqm
    exact ⟨hmdata.1, hmdata.2.1, hmdata.2.2, hqd.2.2,
      hi.1.trans (Nat.mul_le_mul_left 2 hqd.1), hqd.2.1.le.trans hi.2.2.1⟩
  have hprimeQ : ∀ m ∈ E, ∀ q ∈ Q m, q.Prime :=
    fun m hm q hqm ↦ (hqdata m hm q hqm).2.2.2.1
  have hsupportQ : ∀ m ∈ E, ∀ q ∈ Q m, z < q := by
    intro m hm q hqm
    exact residualPrimeFrontier_lt_upperHalf hr (hqdata m hm q hqm).2.2.2.2.1
  have hprimeR : ∀ q ∈ R, q.Prime := fun q hq ↦ (mem_auxiliaryPrimeInterval.mp hq).2.2
  have hsupportR : ∀ q ∈ R, z < q := by
    intro q hq
    have hd := mem_auxiliaryPrimeInterval.mp hq
    exact residualPrimeFrontier_lt_upperHalf hr
      (hreserveData.1.trans (Nat.mul_le_mul_left 2 hd.1))
  have hμ : ∀ m ∈ E, ∀ q ∈ Q m, ∀ b, 0 ≤ μ m q b :=
    fun m _ q _ b ↦ dyadicSourceResidueMass_nonneg S F G a D r m q N b
  have hsum : ∀ m ∈ E, ∀ q ∈ Q m, ∑ b, μ m q b = 1 := by
    intro m hm q hqm
    exact sum_dyadicSourceResidueMass_eq_one (hprimeQ m hm q hqm).pos S F G a D r m N
      (hn m q N (hqdata m hm q hqm) hN).1
  have hcov : ∀ m, ∀ hm : m ∈ E, ∀ p ∈ residualPrimeFiber U y z m, H ≤ p →
      t ≤ ∑ q : Q m, μ m q.val ⟨p % q.val, Nat.mod_lt p (hprimeQ m hm q.val q.property).pos⟩ := by
    intro m hm p hp hHp
    have hh := hc E N hErange hN hYN m hm p hp hHp
    dsimp only [t]
    rw [dyadicProfileCoverLevel_eq]
    exact hh
  have hs' : ((smoothResidualException U y).card : ℝ) ≤ (1 / 128 : ℝ) * g := hs
  have hb' : ((∑ m ∈ E, (residualPrimeFiberBelow U y z m H).card : ℕ) : ℝ) ≤
      (1 / 128 : ℝ) * g := by
    simpa only [Nat.cast_sum] using hb E hEsmall
  have hl' : ((∑ m ∈ residualEvenCofactors M B, (residualPrimeFiber U y z m).card : ℕ) : ℝ) ≤
      (1 / 128 : ℝ) * g := by
    have hh := hl (residualEvenCofactors M B) (Finset.filter_subset _ _)
      (fun m hm ↦ (mem_residualEvenCofactors.mp hm).2.2)
    simpa only [Nat.cast_sum] using hh
  have ht' : ((∑ m ∈ E, (residualPrimeFiber U y z m).card : ℕ) : ℝ) ≤ C * D * g := by
    simpa only [Nat.cast_sum] using ht E hErange
  have hmiss' : ((∑ m ∈ E, (residualPrimeFiber U y z m).card : ℕ) : ℝ) * Real.exp (-t) ≤
      (1 / 128 : ℝ) * g := by
    calc
      _ ≤ (C * D * g) * Real.exp (-t) := mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le
      _ = (Real.exp (-t) * C * D) * g := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmiss hg.le
  have hreserve : g / 16 ≤ (R.card : ℝ) := by
    calc
      _ = (X : ℝ) / (16 * dyadicAmbientScale a r) := by dsimp only [g]; ring
      _ ≤ _ := hfr total hlen
  have hUeq : U = z * B := by
    dsimp only [U, z, B]
    rw [intervalLength_eq_residualPrimeFrontier_mul_cutoff]
    ring
  obtain ⟨data, hmeasure, hfresh⟩ := exists_sourceSurvivorCoverData_of_fibres
    (U := U) (y := y) (z := z) (B := B) (M := M) (H := H)
    (one_lt_dyadicSmoothFrontier (by omega)) (residualPrimeFrontier_one_lt a r)
    hUeq E rfl Q R hprimeQ hprimeR hsupportQ hsupportR hall.2
    (fun m hm ↦ sourceAllocated_disjoint_fresh length base X hm) μ hμ hsum t hcov
    (four_budgets_lt_reserve hg.le hs' hl' hb' hmiss' hreserve)
  refine ⟨data, hyz, residualPrimeFrontier_le_primary a r, ?_, ?_⟩
  · intro p hp
    rw [hmeasure] at hp
    obtain ⟨m, hm, hpm⟩ := Finset.mem_biUnion.mp hp
    exact (hqdata m hm p hpm).2.2.2.2.2
  · intro p hp
    rw [hfresh] at hp
    exact (mem_auxiliaryPrimeInterval.mp hp).2.1.le

end

end Erdos4b.SmoothParameters
