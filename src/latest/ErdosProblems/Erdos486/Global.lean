import ErdosProblems.Erdos486.Analysis
import ErdosProblems.Erdos486.BlockInterface
import ErdosProblems.Erdos486.LogBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Conditional global gliding-hump construction

Starting from `DyadicBlockInterface`, this module recursively installs long
runs of finite dyadic blocks.  Every new run begins at a cutoff where the
finite past has recovered.  The resulting fixed congruence system has a high
cofinal sequence and a low cofinal sequence of logarithmic averages.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

/-- The scales installed in an epoch beginning just above exponent `a`. -/
def epochScales (a : ℕ) : Finset ℕ :=
  Finset.Icc (a + 1) (2 * a + 1)

@[simp]
theorem mem_epochScales {a j : ℕ} :
    j ∈ epochScales a ↔ a + 1 ≤ j ∧ j ≤ 2 * a + 1 := by
  simp [epochScales]

@[simp]
theorem card_epochScales (a : ℕ) : (epochScales a).card = a + 1 := by
  simp [epochScales]
  omega

/-- Dyadic real cutoffs tend to infinity. -/
theorem tendsto_dyadic : Tendsto dyadic atTop atTop := by
  have hfun : dyadic = fun j : ℕ ↦ (2 : ℝ) ^ j := by
    funext j
    simp [dyadic, dyadicNat]
  rw [hfun]
  exact tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)

/-- Finite-past recovery supplies arbitrarily late dyadic recovery cutoffs.
The extra lower bounds are harmless and make the deletion estimate uniform. -/
theorem exists_recovery_start (I : DyadicBlockInterface) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, I.geometry.firstScale ≤ j) (bound : ℕ) :
    ∃ a : ℕ,
      bound ≤ a ∧ 100 ≤ a ∧ I.geometry.firstScale ≤ a + 1 ∧
        (49 : ℝ) / 50 ≤
          logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a) := by
  obtain ⟨d, hd, hd_lower⟩ := I.finite_recovery J
  have hfoot := I.tail_budget J hJ
  have htarget : (49 : ℝ) / 50 < d := by
    linarith
  have hseq :
      Tendsto
        (fun a : ℕ ↦ logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a))
        atTop (nhds d) :=
    hd.comp tendsto_dyadic
  have heventually :
      ∀ᶠ a : ℕ in atTop,
        (49 : ℝ) / 50 <
          logAverage (blockSurvivors I.geometry (J : Set ℕ)) (dyadic a) :=
    hseq.eventually (Ioi_mem_nhds htarget)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
  let a := max N (max bound (max 100 I.geometry.firstScale))
  refine ⟨a, ?_, ?_, ?_, (hN a ?_).le⟩ <;>
    dsimp [a] <;> omega

/-- The finite state retained by the recursive gliding-hump construction. -/
structure GlideState (I : DyadicBlockInterface) where
  scales : Finset ℕ
  valid : ∀ j ∈ scales, I.geometry.firstScale ≤ j
  last : ℕ

/-- The empty initial finite past. -/
def initialGlideState (I : DyadicBlockInterface) : GlideState I where
  scales := ∅
  valid := by simp
  last := max 100 I.geometry.firstScale

/-- A recovery exponent chosen after the current finite past. -/
noncomputable def nextEpochStart (I : DyadicBlockInterface) (s : GlideState I) : ℕ :=
  Classical.choose (exists_recovery_start I s.scales s.valid (2 * s.last + 2))

theorem nextEpochStart_spec (I : DyadicBlockInterface) (s : GlideState I) :
    2 * s.last + 2 ≤ nextEpochStart I s ∧
      100 ≤ nextEpochStart I s ∧
      I.geometry.firstScale ≤ nextEpochStart I s + 1 ∧
      (49 : ℝ) / 50 ≤
        logAverage (blockSurvivors I.geometry (s.scales : Set ℕ))
          (dyadic (nextEpochStart I s)) :=
  Classical.choose_spec (exists_recovery_start I s.scales s.valid (2 * s.last + 2))

/-- Install one full epoch after its chosen recovery cutoff. -/
noncomputable def advanceGlideState (I : DyadicBlockInterface)
    (s : GlideState I) : GlideState I where
  scales := s.scales ∪ epochScales (nextEpochStart I s)
  valid := by
    intro j hj
    rcases Finset.mem_union.1 hj with hj | hj
    · exact s.valid j hj
    · exact (nextEpochStart_spec I s).2.2.1.trans (mem_epochScales.1 hj).1
  last := nextEpochStart I s

/-- The state before epoch `t`, defined by primitive recursion. -/
noncomputable def glideState (I : DyadicBlockInterface) : ℕ → GlideState I
  | 0 => initialGlideState I
  | t + 1 => advanceGlideState I (glideState I t)

/-- Start exponent of epoch `t`. -/
noncomputable def epochStart (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  nextEpochStart I (glideState I t)

@[simp]
theorem glideState_zero_scales (I : DyadicBlockInterface) :
    (glideState I 0).scales = ∅ := rfl

@[simp]
theorem glideState_succ_scales (I : DyadicBlockInterface) (t : ℕ) :
    (glideState I (t + 1)).scales =
      (glideState I t).scales ∪ epochScales (epochStart I t) := rfl

@[simp]
theorem glideState_succ_last (I : DyadicBlockInterface) (t : ℕ) :
    (glideState I (t + 1)).last = epochStart I t := rfl

theorem epochStart_spec (I : DyadicBlockInterface) (t : ℕ) :
    2 * (glideState I t).last + 2 ≤ epochStart I t ∧
      100 ≤ epochStart I t ∧
      I.geometry.firstScale ≤ epochStart I t + 1 ∧
      (49 : ℝ) / 50 ≤
        logAverage
          (blockSurvivors I.geometry ((glideState I t).scales : Set ℕ))
          (dyadic (epochStart I t)) :=
  nextEpochStart_spec I (glideState I t)

/-- Consecutive epoch starts have enough room for the preceding run. -/
theorem epochStart_growth (I : DyadicBlockInterface) (t : ℕ) :
    2 * epochStart I t + 2 ≤ epochStart I (t + 1) := by
  simpa using (epochStart_spec I (t + 1)).1

theorem epochStart_strictMono (I : DyadicBlockInterface) :
    StrictMono (epochStart I) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have h := epochStart_growth I t
  omega

theorem epochStart_tendsto (I : DyadicBlockInterface) :
    Tendsto (epochStart I) atTop atTop :=
  (epochStart_strictMono I).tendsto_atTop

/-- The state before epoch `t` consists exactly of the earlier epochs. -/
theorem mem_glideState_scales_iff (I : DyadicBlockInterface) {t j : ℕ} :
    j ∈ (glideState I t).scales ↔
      ∃ s < t, j ∈ epochScales (epochStart I s) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [glideState_succ_scales, Finset.mem_union]
      constructor
      · rintro (hj | hj)
        · obtain ⟨s, hst, hs⟩ := ih.1 hj
          exact ⟨s, Nat.lt_succ_of_lt hst, hs⟩
        · exact ⟨t, Nat.lt_succ_self t, hj⟩
      · rintro ⟨s, hst, hs⟩
        by_cases h : s < t
        · exact Or.inl (ih.2 ⟨s, h, hs⟩)
        · have hst' : s = t := by omega
          exact Or.inr (hst' ▸ hs)

/-- All scales installed over the infinite recursion. -/
def installedScales (I : DyadicBlockInterface) : Set ℕ :=
  {j | ∃ t, j ∈ epochScales (epochStart I t)}

theorem installedScales_valid (I : DyadicBlockInterface) {j : ℕ}
    (hj : j ∈ installedScales I) : I.geometry.firstScale ≤ j := by
  obtain ⟨t, ht⟩ := hj
  exact (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 ht).1

theorem glideState_scales_subset_installed (I : DyadicBlockInterface) (t : ℕ) :
    ((glideState I t).scales : Set ℕ) ⊆ installedScales I := by
  intro j hj
  obtain ⟨s, _hst, hs⟩ := (mem_glideState_scales_iff I).1 hj
  exact ⟨s, hs⟩

/-- The one fixed set of moduli installed by all epochs. -/
def globalModuli (I : DyadicBlockInterface) : Set ℕ :=
  blockModuli I.geometry (installedScales I)

/-- The one fixed residue assignment; equal moduli are grouped by
`blockResidues`. -/
def globalResidues (I : DyadicBlockInterface)
    (q : globalModuli I) : Set (ZMod (q : ℕ)) :=
  blockResidues I.geometry (installedScales I) q

/-- The final survivor set of the fixed global system. -/
def globalSurvivors (I : DyadicBlockInterface) : Set ℕ :=
  survivors (globalModuli I) (globalResidues I)

theorem globalSurvivors_eq (I : DyadicBlockInterface) :
    globalSurvivors I = blockSurvivors I.geometry (installedScales I) := rfl

theorem zero_not_mem_globalModuli (I : DyadicBlockInterface) :
    0 ∉ globalModuli I :=
  I.geometry.zero_not_mem_blockModuli fun _j hj ↦ installedScales_valid I hj

/-- The first scale of each epoch has at least one endpoint. -/
theorem epochBaseEndpoints_nonempty (I : DyadicBlockInterface) (t : ℕ) :
    (I.geometry.endpoints (epochStart I t + 1)).Nonempty := by
  apply Finset.card_pos.1
  have hcard :=
    I.geometry.enough_endpoints (epochStart_spec I t).2.2.1
  have hpow := dyadicNat_pos (epochStart I t + 1)
  omega

/-- A fixed endpoint chosen from the first scale of epoch `t`. -/
noncomputable def epochBaseEndpoint (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  Classical.choose (epochBaseEndpoints_nonempty I t)

theorem epochBaseEndpoint_mem (I : DyadicBlockInterface) (t : ℕ) :
    epochBaseEndpoint I t ∈
      I.geometry.endpoints (epochStart I t + 1) :=
  Classical.choose_spec (epochBaseEndpoints_nonempty I t)

/-- The modulus assigned to `epochBaseEndpoint`. -/
noncomputable def epochBaseModulus (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  I.geometry.modulus (epochStart I t + 1) (epochBaseEndpoint I t)

theorem epochBaseScale_mem (I : DyadicBlockInterface) (t : ℕ) :
    epochStart I t + 1 ∈ epochScales (epochStart I t) := by
  rw [mem_epochScales]
  constructor
  · rfl
  · have h := (epochStart_spec I t).2.1
    omega

theorem epochBaseModulus_mem_global (I : DyadicBlockInterface) (t : ℕ) :
    epochBaseModulus I t ∈ globalModuli I := by
  exact ⟨epochStart I t + 1, ⟨t, epochBaseScale_mem I t⟩,
    epochBaseEndpoint I t, epochBaseEndpoint_mem I t, rfl⟩

/-- Scale separation makes the selected epoch moduli strictly increasing. -/
theorem epochBaseModulus_strictMono (I : DyadicBlockInterface) :
    StrictMono (epochBaseModulus I) := by
  intro s t hst
  apply I.geometry.modulus_lt_of_scale_lt (epochStart_spec I s).2.2.1
  · have h := epochStart_strictMono I hst
    omega
  · exact epochBaseEndpoint_mem I s
  · exact epochBaseEndpoint_mem I t

/-- The fixed global system contains infinitely many distinct moduli. -/
theorem globalModuli_infinite (I : DyadicBlockInterface) :
    (globalModuli I).Infinite := by
  apply
    (Set.infinite_range_of_injective
      (epochBaseModulus_strictMono I).injective).mono
  intro q hq
  obtain ⟨t, rfl⟩ := hq
  exact epochBaseModulus_mem_global I t

/-- Future rows are inactive below the recovery cutoff, so the final survivor
set agrees there with the finite state used to choose that cutoff. -/
theorem globalSurvivors_iff_finitePast {I : DyadicBlockInterface} {t m : ℕ}
    (hmcut : (m : ℝ) < dyadic (epochStart I t)) :
    m ∈ globalSurvivors I ↔
      m ∈ blockSurvivors I.geometry ((glideState I t).scales : Set ℕ) := by
  let G := I.geometry
  have hmcut_nat : m < dyadicNat (epochStart I t) := by
    have hmcut' : (m : ℝ) < (dyadicNat (epochStart I t) : ℝ) := by
      simpa [dyadic] using hmcut
    exact_mod_cast hmcut'
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro q hqm hres
    let qGlobal : blockModuli G (installedScales I) :=
      ⟨(q : ℕ), by
        obtain ⟨j, hj, e, he, hq⟩ := q.property
        exact ⟨j, glideState_scales_subset_installed I t hj, e, he, hq⟩⟩
    apply hm.2 qGlobal hqm
    obtain ⟨j, hj, e, he, hq, hr⟩ := hres
    exact ⟨j, glideState_scales_subset_installed I t hj, e, he, hq, hr⟩
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro q hqm hres
    obtain ⟨j, hj, e, he, hq, hr⟩ := hres
    obtain ⟨s, hs⟩ := hj
    by_cases hst : s < t
    · have hjpast : j ∈ (glideState I t).scales :=
        (mem_glideState_scales_iff I).2 ⟨s, hst, hs⟩
      let qPast : blockModuli G ((glideState I t).scales : Set ℕ) :=
        ⟨(q : ℕ), ⟨j, hjpast, e, he, hq⟩⟩
      apply hm.2 qPast hqm
      exact ⟨j, hjpast, e, he, hq, hr⟩
    · have hts : t ≤ s := by omega
      have hstart : epochStart I t ≤ epochStart I s :=
        (epochStart_strictMono I).monotone hts
      have hjlower : epochStart I s + 1 ≤ j := (mem_epochScales.1 hs).1
      have hexp : epochStart I t + 1 ≤ j := by omega
      have hpow : dyadicNat (epochStart I t + 1) ≤ dyadicNat j :=
        Nat.pow_le_pow_right (by norm_num) hexp
      have hjvalid : G.firstScale ≤ j := installedScales_valid I ⟨s, hs⟩
      have hmod := G.modulus_lower hjvalid he
      have hqcut : dyadicNat (epochStart I t) < (q : ℕ) := by
        rw [dyadic_succ] at hpow
        rw [hq] at hmod
        have hp := dyadicNat_pos (epochStart I t)
        omega
      omega

/-- Recovery cutoffs witness the high logarithmic averages of the final
fixed system. -/
theorem global_high (I : DyadicBlockInterface) (t : ℕ) :
    (49 : ℝ) / 50 ≤
      logAverage (globalSurvivors I) (dyadic (epochStart I t)) := by
  calc
    (49 : ℝ) / 50 ≤
        logAverage
          (blockSurvivors I.geometry ((glideState I t).scales : Set ℕ))
          (dyadic (epochStart I t)) := (epochStart_spec I t).2.2.2
    _ = logAverage (globalSurvivors I) (dyadic (epochStart I t)) := by
      symm
      apply logAverage_congr_below
      intro m hm
      exact globalSurvivors_iff_finitePast hm

/-- Endpoints contributed by every scale in epoch `t`. -/
noncomputable def epochEndpoints (I : DyadicBlockInterface) (t : ℕ) : Finset ℕ :=
  (epochScales (epochStart I t)).biUnion I.geometry.endpoints

/-- Endpoint intervals at different scales of one epoch are disjoint. -/
theorem epochEndpoints_pairwiseDisjoint (I : DyadicBlockInterface) (t : ℕ) :
    ((epochScales (epochStart I t) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      I.geometry.endpoints := by
  intro j hj k hk hjk
  apply Finset.disjoint_left.2
  intro m hmj hmk
  have hjvalid : I.geometry.firstScale ≤ j :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1
  have hkvalid : I.geometry.firstScale ≤ k :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hk).1
  rcases lt_or_gt_of_ne hjk with hjk' | hkj'
  · exact (Nat.lt_irrefl m)
      (I.geometry.endpoint_lt_of_scale_lt hjvalid hjk' hmj hmk)
  · exact (Nat.lt_irrefl m)
      (I.geometry.endpoint_lt_of_scale_lt hkvalid hkj' hmk hmj)

/-- A full epoch carries the sum of its per-scale harmonic deletion masses. -/
theorem epochEndpoints_harmonic_mass (I : DyadicBlockInterface) (t : ℕ) :
    ((epochStart I t + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) ≤
      ∑ m ∈ epochEndpoints I t, (m : ℝ)⁻¹ := by
  let S := epochScales (epochStart I t)
  have hpair : (S : Set ℕ).PairwiseDisjoint I.geometry.endpoints := by
    simpa [S] using epochEndpoints_pairwiseDisjoint I t
  calc
    ((epochStart I t + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) =
        ∑ _j ∈ S, ((15 : ℝ) / 76) := by
      simp [S]
    _ ≤ ∑ j ∈ S, ∑ m ∈ I.geometry.endpoints j, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact I.geometry.endpoint_harmonic_mass
        ((epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1)
    _ = ∑ m ∈ epochEndpoints I t, (m : ℝ)⁻¹ := by
      symm
      exact Finset.sum_biUnion hpair

/-- Every endpoint in epoch `t` lies below its deletion cutoff. -/
theorem epochEndpoints_subset_range (I : DyadicBlockInterface) (t : ℕ) :
    epochEndpoints I t ⊆
      Finset.range (dyadicNat (2 * epochStart I t + 2)) := by
  intro m hm
  obtain ⟨j, hj, hm⟩ := Finset.mem_biUnion.1 hm
  have hjvalid : I.geometry.firstScale ≤ j :=
    (epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1
  have hmj := I.geometry.endpoint_lt_next_dyadic hjvalid hm
  have hexp : j + 1 ≤ 2 * epochStart I t + 2 := by
    have := (mem_epochScales.1 hj).2
    omega
  have hpow : dyadicNat (j + 1) ≤ dyadicNat (2 * epochStart I t + 2) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  exact Finset.mem_range.2 (hmj.trans_le hpow)

/-- Every endpoint of an installed epoch is absent from the final survivor. -/
theorem epochEndpoints_not_mem_global (I : DyadicBlockInterface) (t : ℕ) :
    ∀ m ∈ epochEndpoints I t, m ∉ globalSurvivors I := by
  intro m hm
  obtain ⟨j, hj, hm⟩ := Finset.mem_biUnion.1 hm
  change m ∉ blockSurvivors I.geometry (installedScales I)
  exact I.geometry.endpoint_not_mem_blockSurvivors
    ⟨t, hj⟩ hm
    ((epochStart_spec I t).2.2.1.trans (mem_epochScales.1 hj).1)

/-- Removing a finite set below an integral cutoff subtracts its full
harmonic mass from the universal harmonic-number upper bound. -/
theorem logSum_add_deleted_le_harmonic (B : Set ℕ) (N : ℕ) (D : Finset ℕ)
    (hsub : D ⊆ Finset.range N) (hdisj : ∀ m ∈ D, m ∉ B) :
    logSum B (N : ℝ) + ∑ m ∈ D, (m : ℝ)⁻¹ ≤ (harmonic N : ℝ) := by
  have hlog :
      logSum B (N : ℝ) ≤
        ∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0 := by
    unfold logSum
    simp only [Nat.ceil_natCast]
    apply Finset.sum_le_sum
    intro m hm
    have hmN : m < N := Finset.mem_range.1 hm
    have hmN' : (m : ℝ) < N := by exact_mod_cast hmN
    by_cases hmB : m ∈ B
    · have hmD : m ∉ D := fun hmD ↦ hdisj m hmD hmB
      simp [hmB, hmD, hmN']
    · by_cases hmD : m ∈ D <;> simp [hmB, hmD]
  have hsplit :
      (∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0) +
          ∑ m ∈ D, (m : ℝ)⁻¹ =
        ∑ m ∈ Finset.range N, (m : ℝ)⁻¹ := by
    rw [← Finset.sum_filter]
    have hfilter :
        (Finset.range N).filter (fun m ↦ m ∉ D) = Finset.range N \ D := by
      ext m
      simp
    rw [hfilter]
    exact Finset.sum_sdiff hsub
  have htotal :
      (∑ m ∈ Finset.range N, (m : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
    by_cases hN : N = 0
    · simp [hN]
    · have hzero : 0 ∈ Finset.range N :=
        Finset.mem_range.2 (Nat.pos_of_ne_zero hN)
      have herase :
          (∑ m ∈ Finset.range N, (m : ℝ)⁻¹) =
            ∑ m ∈ (Finset.range N).erase 0, (m : ℝ)⁻¹ := by
        symm
        simpa using
          (Finset.sum_erase_add (s := Finset.range N)
            (f := fun m : ℕ ↦ (m : ℝ)⁻¹) hzero)
      rw [herase, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        simp only [Finset.mem_erase, Finset.mem_range] at hm
        exact Finset.mem_Icc.2
          ⟨Nat.one_le_iff_ne_zero.2 hm.1, Nat.le_of_lt hm.2⟩
      · intro m _hm _hnot
        positivity
  calc
    logSum B (N : ℝ) + ∑ m ∈ D, (m : ℝ)⁻¹ ≤
        (∑ m ∈ Finset.range N, if m ∉ D then (m : ℝ)⁻¹ else 0) +
          ∑ m ∈ D, (m : ℝ)⁻¹ := add_le_add hlog le_rfl
    _ = ∑ m ∈ Finset.range N, (m : ℝ)⁻¹ := hsplit
    _ ≤ (harmonic N : ℝ) := htotal

/-- The deletion cutoff at epoch `t` has logarithmic average at most
`177 / 200`. -/
theorem global_low (I : DyadicBlockInterface) (t : ℕ) :
    logAverage (globalSurvivors I)
        (dyadic (2 * epochStart I t + 2)) ≤ (177 : ℝ) / 200 := by
  let a := epochStart I t
  let e := 2 * a + 2
  let N := dyadicNat e
  let D := epochEndpoints I t
  have hsub : D ⊆ Finset.range N := by
    simpa [D, N, e, a] using epochEndpoints_subset_range I t
  have hdisj : ∀ m ∈ D, m ∉ globalSurvivors I := by
    simpa [D] using epochEndpoints_not_mem_global I t
  have hdeleted :=
    logSum_add_deleted_le_harmonic (globalSurvivors I) N D hsub hdisj
  have htotal :
      logSum (globalSurvivors I) (dyadic e) +
          ∑ m ∈ D, (m : ℝ)⁻¹ ≤
        1 + Real.log (dyadic e) := by
    have h := hdeleted.trans (harmonic_le_one_add_log N)
    simpa [N, dyadic] using h
  have hmass :
      (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) ≤
        ∑ m ∈ D, (m : ℝ)⁻¹ := by
    simpa [a, D] using epochEndpoints_harmonic_mass I t
  have hnum :
      logSum (globalSurvivors I) (dyadic e) ≤
        1 + Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) := by
    linarith
  have hlog_eq :
      Real.log (dyadic e) = (e : ℝ) * Real.log 2 := by
    simp [dyadic, dyadicNat, Real.log_pow]
  have hlog_two_lower : (1 : ℝ) / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog_two_upper : Real.log 2 < (3 : ℝ) / 4 := by
    linarith [Real.log_two_lt_d9]
  have ha100 : 100 ≤ a := by
    simpa [a] using (epochStart_spec I t).2.1
  have ha100_real : (100 : ℝ) ≤ a := by exact_mod_cast ha100
  have he_cast : (e : ℝ) = 2 * (a : ℝ) + 2 := by
    simp [e]
  have hlog_gt : 100 < Real.log (dyadic e) := by
    rw [hlog_eq, he_cast]
    nlinarith
  have hlog_pos : 0 < Real.log (dyadic e) := by linarith
  have herror :
      1 / Real.log (dyadic e) < (1 : ℝ) / 100 := by
    apply (div_lt_iff₀ hlog_pos).2
    nlinarith
  have hconstant :
      (1 : ℝ) / 4 * Real.log 2 < (15 : ℝ) / 76 := by
    nlinarith
  have ha_pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hmass_ratio :
      (1 : ℝ) / 8 <
        (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
          Real.log (dyadic e) := by
    apply (lt_div_iff₀ hlog_pos).2
    calc
      (1 : ℝ) / 8 * Real.log (dyadic e) =
          ((a + 1 : ℕ) : ℝ) * ((1 : ℝ) / 4 * Real.log 2) := by
        rw [hlog_eq, he_cast]
        push_cast
        ring
      _ < ((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76) :=
        mul_lt_mul_of_pos_left hconstant ha_pos
  have hnormalized :
      logAverage (globalSurvivors I) (dyadic e) ≤
        1 + 1 / Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
            Real.log (dyadic e) := by
    rw [logAverage]
    calc
      logSum (globalSurvivors I) (dyadic e) / Real.log (dyadic e) ≤
          (1 + Real.log (dyadic e) -
              (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76))) /
            Real.log (dyadic e) :=
        (div_le_div_iff_of_pos_right hlog_pos).2 hnum
      _ = 1 + 1 / Real.log (dyadic e) -
          (((a + 1 : ℕ) : ℝ) * ((15 : ℝ) / 76)) /
            Real.log (dyadic e) := by
        field_simp [ne_of_gt hlog_pos]
        ring
  have hfinal :
      logAverage (globalSurvivors I) (dyadic e) ≤ (177 : ℝ) / 200 := by
    linarith
  simpa [e, a] using hfinal

/-- Exponents of the high recovery cutoffs. -/
noncomputable def recoveryExponent (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  epochStart I t

/-- Exponents of the low deletion cutoffs. -/
noncomputable def deletionExponent (I : DyadicBlockInterface) (t : ℕ) : ℕ :=
  2 * epochStart I t + 2

/-- The cofinal high cutoff sequence. -/
noncomputable def recoveryCutoff (I : DyadicBlockInterface) (t : ℕ) : ℝ :=
  dyadic (recoveryExponent I t)

/-- The cofinal low cutoff sequence. -/
noncomputable def deletionCutoff (I : DyadicBlockInterface) (t : ℕ) : ℝ :=
  dyadic (deletionExponent I t)

theorem recoveryExponent_strictMono (I : DyadicBlockInterface) :
    StrictMono (recoveryExponent I) := by
  simpa [recoveryExponent] using! epochStart_strictMono I

theorem deletionExponent_strictMono (I : DyadicBlockInterface) :
    StrictMono (deletionExponent I) := by
  intro s t hst
  have h := epochStart_strictMono I hst
  simp only [deletionExponent]
  omega

theorem recoveryCutoff_tendsto (I : DyadicBlockInterface) :
    Tendsto (recoveryCutoff I) atTop atTop := by
  exact tendsto_dyadic.comp (recoveryExponent_strictMono I).tendsto_atTop

theorem deletionCutoff_tendsto (I : DyadicBlockInterface) :
    Tendsto (deletionCutoff I) atTop atTop := by
  exact tendsto_dyadic.comp (deletionExponent_strictMono I).tendsto_atTop

theorem recoveryCutoff_high (I : DyadicBlockInterface) (t : ℕ) :
    (49 : ℝ) / 50 ≤
      logAverage (globalSurvivors I) (recoveryCutoff I t) := by
  simpa [recoveryCutoff, recoveryExponent] using global_high I t

theorem deletionCutoff_low (I : DyadicBlockInterface) (t : ℕ) :
    logAverage (globalSurvivors I) (deletionCutoff I t) ≤
      (177 : ℝ) / 200 := by
  simpa [deletionCutoff, deletionExponent] using global_low I t

/-- The cofinal deletion cutoffs make the low inequality frequent at
`atTop`. -/
theorem frequently_global_low (I : DyadicBlockInterface) :
    ∃ᶠ x in (atTop : Filter ℝ),
      logAverage (globalSurvivors I) x ≤ (177 : ℝ) / 200 := by
  intro hnot
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        ¬logAverage (globalSurvivors I) (deletionCutoff I t) ≤
          (177 : ℝ) / 200 :=
    deletionCutoff_tendsto I hnot
  obtain ⟨t, ht⟩ := heventually.exists
  exact ht (deletionCutoff_low I t)

/-- The cofinal recovery cutoffs make the high inequality frequent at
`atTop`. -/
theorem frequently_global_high (I : DyadicBlockInterface) :
    ∃ᶠ x in (atTop : Filter ℝ),
      (49 : ℝ) / 50 ≤ logAverage (globalSurvivors I) x := by
  intro hnot
  have heventually :
      ∀ᶠ t : ℕ in atTop,
        ¬(49 : ℝ) / 50 ≤
          logAverage (globalSurvivors I) (recoveryCutoff I t) :=
    recoveryCutoff_tendsto I hnot
  obtain ⟨t, ht⟩ := heventually.exists
  exact ht (recoveryCutoff_high I t)

/-- The low cofinal sequence bounds the actual filter liminf. -/
theorem global_liminf_le (I : DyadicBlockInterface) :
    liminf (logAverage (globalSurvivors I)) atTop ≤ (177 : ℝ) / 200 := by
  exact liminf_le_of_frequently_le
    (frequently_global_low I)
    (logAverage_isBoundedUnder_ge (globalSurvivors I))

/-- The high cofinal sequence bounds the actual filter limsup. -/
theorem le_global_limsup (I : DyadicBlockInterface) :
    (49 : ℝ) / 50 ≤
      limsup (logAverage (globalSurvivors I)) atTop := by
  exact le_limsup_of_frequently_le
    (frequently_global_high I)
    (logAverage_isBoundedUnder_le (globalSurvivors I))

/-- The two cofinal sequences rule out every logarithmic density value. -/
theorem global_hasNoLogDensity (I : DyadicBlockInterface) :
    ¬∃ d : ℝ, HasLogDensity (globalSurvivors I) d := by
  rintro ⟨d, hd⟩
  exact (not_hasLogDensity_of_cofinal_ge_of_cofinal_le
    (globalSurvivors I) (by norm_num)
    (recoveryCutoff I) (deletionCutoff I)
    (recoveryCutoff_tendsto I) (deletionCutoff_tendsto I)
    (recoveryCutoff_high I) (deletionCutoff_low I) d) hd

/-- Conditional global theorem.  The moduli and residue sets in the
conclusion are fixed before either cofinal cutoff sequence is considered. -/
theorem exists_fixed_system_of_dyadicBlockInterface (I : DyadicBlockInterface) :
    ∃ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))),
      0 ∉ A ∧
      ∃ upper lower : ℕ → ℝ,
        Tendsto upper atTop atTop ∧
        Tendsto lower atTop atTop ∧
        (∀ t, (49 : ℝ) / 50 ≤ logAverage (survivors A X) (upper t)) ∧
        (∀ t, logAverage (survivors A X) (lower t) ≤ (177 : ℝ) / 200) ∧
        (∀ d : ℝ, ¬HasLogDensity (survivors A X) d) := by
  refine ⟨globalModuli I, globalResidues I, zero_not_mem_globalModuli I,
    recoveryCutoff I, deletionCutoff I,
    recoveryCutoff_tendsto I, deletionCutoff_tendsto I, ?_, ?_, ?_⟩
  · intro t
    exact recoveryCutoff_high I t
  · intro t
    exact deletionCutoff_low I t
  · exact not_hasLogDensity_of_cofinal_ge_of_cofinal_le
      (globalSurvivors I) (by norm_num)
      (recoveryCutoff I) (deletionCutoff I)
      (recoveryCutoff_tendsto I) (deletionCutoff_tendsto I)
      (recoveryCutoff_high I) (deletionCutoff_low I)

/-- Every instance of the finite dyadic-block interface yields the complete
quantitative counterexample claimed in the manuscript. -/
theorem quantitativeCounterexample_of_dyadicBlockInterface
    (I : DyadicBlockInterface) : QuantitativeCounterexample := by
  refine ⟨globalModuli I, globalModuli_infinite I,
    zero_not_mem_globalModuli I, globalResidues I,
    global_hasNoLogDensity I, global_liminf_le I, le_global_limsup I⟩

/-- The finite-block interface implies a negative answer to the original
universal assertion. -/
theorem not_erdos486Assertion_of_dyadicBlockInterface
    (I : DyadicBlockInterface) : ¬Erdos486Assertion := by
  exact quantitativeCounterexample_not_assertion
    (quantitativeCounterexample_of_dyadicBlockInterface I)

end Erdos486
