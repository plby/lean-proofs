/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.HallOuter
import ErdosProblems.Erdos515.HallRadialSup
import ErdosProblems.Erdos515.HallOuterUniform

/-!
# A concrete form of Hall's radial lemma

This file closes the potential-theoretic estimates in `Hall` for a continuous subharmonic
function on the unit disk.  The first auxiliary result is a closure-safe compact radial
selection which remembers an arbitrary property of every selected radius.  This is needed to
apply the separate inner- and outer-radius Green-kernel estimates.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos515

/-- The open superlevel set in which Hall places the circular slits. -/
def hallSlitRegion (w : ℂ → ℝ) : Set ℂ :=
  unitDisk ∩ (fun z ↦ 1 - w z) ⁻¹' Ioi (1 / 2 : ℝ)

lemma isOpen_hallSlitRegion {w : ℂ → ℝ} (hw : SubharmonicOn w unitDisk) :
    IsOpen (hallSlitRegion w) := by
  exact (continuousOn_const.sub hw.continuousOn).isOpen_inter_preimage
    hw.isOpen isOpen_Ioi

lemma hallSlitRegion_subset_unitDisk (w : ℂ → ℝ) :
    hallSlitRegion w ⊆ unitDisk := inter_subset_left

lemma one_half_lt_one_sub_of_nonpos {w : ℂ → ℝ} {z : ℂ} (hz : w z ≤ 0) :
    (1 / 2 : ℝ) < 1 - w z := by linarith

/-- Inner regularity lets one prove an angular-measure bound on compact subsets. -/
lemma volume_le_of_forall_isCompact_subset_le {S : Set ℝ} {B : ℝ≥0∞}
    (hS : MeasurableSet S)
    (hcompact : ∀ K : Set ℝ, IsCompact K → K ⊆ S → volume K ≤ B) :
    volume S ≤ B := by
  by_contra hnot
  have hlt : B < volume S := lt_of_not_ge hnot
  obtain ⟨K, hKS, hKcompact, hBK⟩ := hS.exists_lt_isCompact hlt
  exact (not_lt_of_ge (hcompact K hKcompact hKS)) hBK

/-- Maximum-principle comparison on a slit disk.  The hypotheses are the concrete data supplied
by a finite Green potential: a global bound, uniform decay at the unit circle, and a compact
slit contained in a strict superlevel set of the positive superharmonic majorant. -/
theorem slitPotential_le_two_mul_of_uniform_bound
    {φ ψ : ℂ → ℝ} {K O : Set ℂ} {L : ℝ}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hOopen : IsOpen O) (hKO : K ⊆ O)
    (hOψ : ∀ z ∈ O, (1 / 2 : ℝ) < ψ z)
    (hψnonneg : ∀ z ∈ unitDisk, 0 ≤ ψ z)
    (hL : 0 ≤ L) (hφbound : ∀ z ∈ unitDisk \ K, φ z ≤ L)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧
      ∀ z : ℂ, ‖z‖ < 1 → 1 - d < ‖z‖ → φ z < ε)
    (hsub : SubharmonicOn (fun z ↦ φ z - (2 * L) * ψ z) (unitDisk \ K)) :
    ∀ z ∈ unitDisk \ K, φ z ≤ (2 * L) * ψ z := by
  apply subharmonicDifference_nonpos_of_exhaustions hsub
  intro z hz ε hε
  obtain ⟨e, he, hthick⟩ :=
    hKcompact.exists_thickening_subset_open hOopen hKO
  have hdistz : 0 < Metric.infDist z K :=
    (hKcompact.isClosed.notMem_iff_infDist_pos hKnonempty).1 hz.2
  obtain ⟨d, hd, hdecayε⟩ := hdecay ε hε
  have hzgap : 0 < 1 - ‖z‖ := by
    simpa [unitDisk] using hz.1
  let η : ℝ := min (e / 2) (Metric.infDist z K / 2)
  let d' : ℝ := min d (1 - ‖z‖)
  let R : ℝ := 1 - d' / 2
  let V : Set ℂ := Metric.ball 0 R ∩
    (fun y ↦ Metric.infDist y K) ⁻¹' Ioi η
  have hη : 0 < η := by
    simp only [η, lt_min_iff]
    exact ⟨half_pos he, half_pos hdistz⟩
  have hηe : η < e :=
    (min_le_left (e / 2) (Metric.infDist z K / 2)).trans_lt (half_lt_self he)
  have hηz : η < Metric.infDist z K :=
    (min_le_right (e / 2) (Metric.infDist z K / 2)).trans_lt (half_lt_self hdistz)
  have hd' : 0 < d' := by
    simp only [d', lt_min_iff]
    exact ⟨hd, hzgap⟩
  have hd'd : d' ≤ d := min_le_left _ _
  have hd'gap : d' ≤ 1 - ‖z‖ := min_le_right _ _
  have hRz : ‖z‖ < R := by
    dsimp [R]
    nlinarith
  have hRone : R < 1 := by
    dsimp [R]
    linarith
  have hdecayR : 1 - d < R := by
    dsimp [R]
    nlinarith
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_Ioi.preimage (Metric.continuous_infDist_pt K))
  have hVbounded : Bornology.IsBounded V :=
    Metric.isBounded_ball.subset inter_subset_left
  have hzV : z ∈ V := ⟨by simpa [Metric.mem_ball, dist_zero_right], hηz⟩
  have hVclosure : closure V ⊆ unitDisk \ K := by
    intro y hy
    have hyBallClosure : y ∈ closure (Metric.ball (0 : ℂ) R) :=
      closure_mono inter_subset_left hy
    have hyClosedBall : y ∈ Metric.closedBall (0 : ℂ) R :=
      Metric.closure_ball_subset_closedBall hyBallClosure
    have hynorm : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hyClosedBall
    have hyDistClosure : y ∈ closure ((fun q ↦ Metric.infDist q K) ⁻¹' Ioi η) :=
      closure_mono inter_subset_right hy
    have hyDistImage : Metric.infDist y K ∈ closure (Ioi η) :=
      ((Metric.continuous_infDist_pt K).closure_preimage_subset (Ioi η)) hyDistClosure
    have hydist : η ≤ Metric.infDist y K := by
      simpa using hyDistImage
    have hyunit : y ∈ unitDisk := by
      simpa [unitDisk] using lt_of_le_of_lt hynorm hRone
    have hynot : y ∉ K :=
      (hKcompact.isClosed.notMem_iff_infDist_pos hKnonempty).2 (hη.trans_le hydist)
    exact ⟨hyunit, hynot⟩
  refine ⟨V, hVopen, hVbounded, hzV, hVclosure, ?_⟩
  intro y hyfront
  rcases frontier_inter_subset (Metric.ball (0 : ℂ) R)
      ((fun q ↦ Metric.infDist q K) ⁻¹' Ioi η) hyfront with hout | hnear
  · have hySphere : y ∈ Metric.sphere (0 : ℂ) R :=
      Metric.frontier_ball_subset_sphere hout.1
    have hynorm : ‖y‖ = R := by
      simpa [Metric.mem_sphere, dist_zero_right] using hySphere
    have hyunit : ‖y‖ < 1 := hynorm.trans_lt hRone
    have hyψ : 0 ≤ ψ y := hψnonneg y (by simpa [unitDisk] using hyunit)
    have hyφ : φ y < ε := hdecayε y hyunit (by rw [hynorm]; exact hdecayR)
    have hCψ : 0 ≤ (2 * L) * ψ y :=
      mul_nonneg (mul_nonneg (by norm_num) hL) hyψ
    linarith
  · have hyDistFront : Metric.infDist y K ∈ frontier (Ioi η) :=
      ((Metric.continuous_infDist_pt K).frontier_preimage_subset (Ioi η)) hnear.2
    have hydist : Metric.infDist y K = η := by
      simpa using hyDistFront
    have hyThick : y ∈ Metric.thickening e K :=
      (Metric.mem_thickening_iff_infDist_lt hKnonempty).2 (hydist.trans_lt hηe)
    have hyO : y ∈ O := hthick hyThick
    have hyClosure : y ∈ closure V := frontier_subset_closure hyfront
    have hyunit : y ∈ unitDisk := (hVclosure hyClosure).1
    have hyφ : φ y ≤ L := hφbound y (hVclosure hyClosure)
    have hyψ : (1 / 2 : ℝ) < ψ y := hOψ y hyO
    nlinarith

/-- Every selected angular piece has finite measure once the family is supported in the
standard finite angular interval. -/
lemma volume_arc_angles_ne_top_of_angularSupport_subset
    (A : DisjointRadialArcs) (hangle : A.angularSupport ⊆ angleDomain) (i : Fin A.n) :
    volume (A.arc i).angles ≠ ∞ := by
  have hle : volume (A.arc i).angles ≤ volume angleDomain := by
    apply measure_mono
    intro θ hθ
    exact hangle (Set.mem_iUnion.2 ⟨i, hθ⟩)
  exact ne_top_of_le_ne_top (by rw [volume_angleDomain]; exact ENNReal.ofReal_ne_top) hle

lemma carrier_nonempty_of_angularSupport_nonempty (A : DisjointRadialArcs)
    (h : A.angularSupport.Nonempty) : A.carrier.Nonempty := by
  obtain ⟨θ, hθ⟩ := h
  simp only [DisjointRadialArcs.angularSupport, Set.mem_iUnion] at hθ
  obtain ⟨i, hθi⟩ := hθ
  refine ⟨radialPoint (A.arc i).radius θ, ?_⟩
  exact Set.mem_iUnion.2 ⟨i, radialPoint_mem_carrier (A.arc i) hθi⟩

lemma isCompact_closure_disjointRadialArcs_carrier (A : DisjointRadialArcs) :
    IsCompact (closure A.carrier) := by
  have hcarrier : A.carrier ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    simp only [DisjointRadialArcs.carrier, Set.mem_iUnion] at hz
    obtain ⟨i, θ, hθ, rfl⟩ := hz
    simpa [Metric.mem_closedBall, norm_radialPoint (A.arc i).radius_pos.le]
      using (A.arc i).radius_lt_one.le
  have hclosure : closure A.carrier ⊆ Metric.closedBall (0 : ℂ) 1 :=
    closure_minimal hcarrier Metric.isClosed_closedBall
  exact (isCompact_closedBall (0 : ℂ) 1)
    |>.of_isClosed_subset isClosed_closure hclosure

/-- A nonempty finite slit family has a common radius bound strictly below one. -/
lemma exists_common_radius_bound (A : DisjointRadialArcs) (hcarrier : A.carrier.Nonempty) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, (A.arc i).radius ≤ ρ := by
  obtain ⟨z, hz⟩ := hcarrier
  simp only [DisjointRadialArcs.carrier, Set.mem_iUnion] at hz
  obtain ⟨i₀, _hi₀⟩ := hz
  obtain ⟨imax, _himem, himax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin A.n)) (fun i ↦ (A.arc i).radius)
    ⟨i₀, Finset.mem_univ i₀⟩
  let ρ : ℝ := ((A.arc imax).radius + 1) / 2
  refine ⟨ρ, ?_, ?_, ?_⟩
  · dsimp [ρ]
    linarith [(A.arc imax).radius_pos]
  · dsimp [ρ]
    linarith [(A.arc imax).radius_lt_one]
  · intro i
    have hi : (A.arc i).radius ≤ (A.arc imax).radius := himax i (Finset.mem_univ i)
    dsimp [ρ]
    linarith [(A.arc imax).radius_lt_one]

lemma greenPotentialReal_logMeasure_le_of_uniform_bound
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hpot : ∀ z : ℂ, ‖z‖ < 1 → greenPotential A.logMeasure z ≤ ENNReal.ofReal L)
    {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) :
    greenPotentialReal A.logMeasure z ≤ L := by
  rw [← ENNReal.ofReal_le_ofReal_iff hL]
  rw [ofReal_greenPotentialReal_logMeasure_eq_greenPotential A hfinite hz]
  exact hpot z (by simpa [unitDisk] using hz.1)

/-- The uniform Green-potential bound and boundary decay imply the concrete slit comparison
with the positive superharmonic function `1 - w`. -/
theorem greenPotentialReal_logMeasure_le_two_mul_one_sub
    (A : DisjointRadialArcs) {w : ℂ → ℝ} {L : ℝ}
    (hangle : A.angularSupport ⊆ angleDomain) (hcarrier : A.carrier.Nonempty)
    (hclosure : closure A.carrier ⊆ hallSlitRegion w)
    (hw : SubharmonicOn w unitDisk)
    (hwle : ∀ z ∈ unitDisk, w z ≤ 1)
    (hL : 0 ≤ L)
    (hpot : ∀ z : ℂ, ‖z‖ < 1 → greenPotential A.logMeasure z ≤ ENNReal.ofReal L) :
    ∀ z ∈ unitDisk \ closure A.carrier,
      greenPotentialReal A.logMeasure z ≤ (2 * L) * (1 - w z) := by
  let φ : ℂ → ℝ := greenPotentialReal A.logMeasure
  let ψ : ℂ → ℝ := fun z ↦ 1 - w z
  have hfinite : ∀ i, volume (A.arc i).angles ≠ ∞ :=
    volume_arc_angles_ne_top_of_angularSupport_subset A hangle
  have hKcompact : IsCompact (closure A.carrier) :=
    isCompact_closure_disjointRadialArcs_carrier A
  have hKnonempty : (closure A.carrier).Nonempty := hcarrier.mono subset_closure
  have hψnonneg : ∀ z ∈ unitDisk, 0 ≤ ψ z := by
    intro z hz
    dsimp [ψ]
    linarith [hwle z hz]
  have hφbound : ∀ z ∈ unitDisk \ closure A.carrier, φ z ≤ L := by
    intro z hz
    exact greenPotentialReal_logMeasure_le_of_uniform_bound A hfinite hL hpot hz
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_common_radius_bound A hcarrier
  have hdecay : ∀ ε : ℝ, 0 < ε → ∃ d : ℝ, 0 < d ∧
      ∀ z : ℂ, ‖z‖ < 1 → 1 - d < ‖z‖ → φ z < ε := by
    intro ε hε
    obtain ⟨d, hd, hdec⟩ :=
      greenPotentialReal_logMeasure_tends_uniformly_zero_of_radius_le
        A hfinite hρ0 hρ1 hρ ε hε
    exact ⟨d, hd, fun z hz hzbd ↦ lt_of_le_of_lt (le_abs_self (φ z)) (hdec z hz hzbd)⟩
  have hGopen : IsOpen (unitDisk \ closure A.carrier) :=
    hw.isOpen.sdiff isClosed_closure
  have hnegψ : SubharmonicOn (fun z ↦ -ψ z) (unitDisk \ closure A.carrier) := by
    have hs := superharmonicOn_one_sub hw
    change SubharmonicOn (fun z ↦ -(1 - w z)) unitDisk at hs
    exact hs.mono hGopen inter_subset_left
  have hsub : SubharmonicOn (fun z ↦ φ z - (2 * L) * ψ z)
      (unitDisk \ closure A.carrier) := by
    have hcoeff : 0 ≤ (2 : ℝ) * L := mul_nonneg (by norm_num) hL
    have hscaled := hnegψ.nonneg_mul hcoeff
    have hadd := (greenPotentialReal_logMeasure_subharmonicOn A hfinite).add hscaled
    convert hadd using 1
    ext z
    dsimp [φ]
    ring
  exact slitPotential_le_two_mul_of_uniform_bound
    hKcompact hKnonempty (isOpen_hallSlitRegion hw) hclosure
    (fun z hz ↦ hz.2) hψnonneg hL hφbound hdecay hsub

/-- Closure-safe compact radial selection, retaining a property of every chosen radius.

The selector in `HallOuter` deliberately exposes only its geometric conclusions.  In the
concrete Hall proof we also need to remember whether the selected radius is at most or at least
`1 / 4`; the predicate `P` records precisely that information. -/
theorem exists_disjointRadialArcs_closure_subset_of_isCompact_of_radiusProperty
    {P : ℝ → Prop} {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r : ℝ, 0 < r ∧ r < 1 ∧ P r ∧ radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.angularSupport ⊆ angleDomain ∧
        closure A.carrier ⊆ Ω ∧ (∀ i, P (A.arc i).radius) := by
  classical
  let rad : K → ℝ := fun θ ↦ Classical.choose (hmeet θ θ.2)
  have hrad : ∀ θ : K,
      0 < rad θ ∧ rad θ < 1 ∧ P (rad θ) ∧ radialPoint (rad θ) θ.1 ∈ Ω :=
    fun θ ↦ Classical.choose_spec (hmeet θ θ.2)
  let U : K → Set ℝ := fun θ ↦ (fun φ ↦ radialPoint (rad θ) φ) ⁻¹' Ω
  have hUopen : ∀ θ, IsOpen (U θ) := by
    intro θ
    apply hΩ.preimage
    unfold radialPoint
    fun_prop
  have hexists : ∀ θ : K, ∃ ε : ℝ, 0 < ε ∧ Metric.ball θ.1 ε ⊆ U θ := by
    intro θ
    exact Metric.isOpen_iff.mp (hUopen θ) θ.1 (hrad θ).2.2.2
  choose ε hεpos hεsub using hexists
  let core : K → Set ℝ := fun θ ↦ Metric.ball θ.1 (ε θ / 2)
  have hcoreOpen : ∀ θ, IsOpen (core θ) := fun _ ↦ Metric.isOpen_ball
  have hKcore : K ⊆ ⋃ θ, core θ := by
    intro θ hθ
    simp only [Set.mem_iUnion]
    refine ⟨⟨θ, hθ⟩, ?_⟩
    simp [core, hεpos]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover core hcoreOpen hKcore
  let e : Fin t.card ≃ t := (Finset.equivFin t).symm
  let idx : Fin t.card → K := fun i ↦ (e i).1
  let Ufin : Fin t.card → Set ℝ := fun i ↦ core (idx i)
  have hKUfin : K ⊆ ⋃ i, Ufin i := by
    intro θ hθ
    have hx := ht hθ
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨a, haT, haU⟩ := hx
    let ati : t := ⟨a, haT⟩
    refine ⟨(Finset.equivFin t) ati, ?_⟩
    have he : e ((Finset.equivFin t) ati) = ati := by simp [e]
    simpa [Ufin, idx, he, ati] using haU
  have hUfinOpen : ∀ i, IsOpen (Ufin i) := fun i ↦ hcoreOpen _
  have hclosureRefine : ∀ i,
      closure (disjointRefinement Ufin i ∩ angleDomain) ⊆ U (idx i) := by
    intro i
    have hsubCore : disjointRefinement Ufin i ∩ angleDomain ⊆ Ufin i :=
      inter_subset_left.trans (disjointRefinement_subset Ufin i)
    have hhalf : ε (idx i) / 2 < ε (idx i) := by linarith [hεpos (idx i)]
    calc
      closure (disjointRefinement Ufin i ∩ angleDomain) ⊆ closure (Ufin i) :=
        closure_mono hsubCore
      _ = closure (Metric.ball (idx i).1 (ε (idx i) / 2)) := by rfl
      _ ⊆ Metric.closedBall (idx i).1 (ε (idx i) / 2) :=
        Metric.closure_ball_subset_closedBall
      _ ⊆ Metric.ball (idx i).1 (ε (idx i)) := Metric.closedBall_subset_ball hhalf
      _ ⊆ U (idx i) := hεsub (idx i)
  let arc : Fin t.card → CircularArc := fun i ↦
    { radius := rad (idx i)
      angles := disjointRefinement Ufin i ∩ angleDomain
      radius_pos := (hrad (idx i)).1
      radius_lt_one := (hrad (idx i)).2.1
      measurableSet_angles :=
        (measurableSet_disjointRefinement (fun j ↦ (hUfinOpen j).measurableSet) i).inter
          measurableSet_Ico }
  let A : DisjointRadialArcs :=
    { n := t.card
      arc := arc
      angle_disjoint := by
        intro i _ j _ hij
        exact (pairwise_disjointRefinement Ufin hij).mono inter_subset_left inter_subset_left }
  have hcover : K ⊆ A.angularSupport := by
    intro θ hθ
    have hθU : θ ∈ ⋃ i, Ufin i := hKUfin hθ
    rw [← iUnion_disjointRefinement_eq Ufin] at hθU
    simp only [DisjointRadialArcs.angularSupport, Set.mem_iUnion] at hθU ⊢
    obtain ⟨i, hi⟩ := hθU
    exact ⟨i, hi, hKangle hθ⟩
  have hangleSupport : A.angularSupport ⊆ angleDomain := by
    intro θ hθ
    simp only [DisjointRadialArcs.angularSupport, Set.mem_iUnion] at hθ
    obtain ⟨i, hi⟩ := hθ
    simpa [A, arc] using hi.2
  let closedCarrier : Set ℂ :=
    ⋃ i, (fun θ ↦ radialPoint (A.arc i).radius θ) '' closure (A.arc i).angles
  have hcompactAngles : ∀ i, IsCompact (closure (A.arc i).angles) := by
    intro i
    have hang : (A.arc i).angles ⊆ Icc (0 : ℝ) (2 * Real.pi) := by
      intro θ hθ
      have hθ' : θ ∈ angleDomain := by
        simpa [A, arc] using hθ.2
      exact ⟨hθ'.1, hθ'.2.le⟩
    have hcl : closure (A.arc i).angles ⊆ Icc (0 : ℝ) (2 * Real.pi) :=
      closure_minimal hang isClosed_Icc
    exact isCompact_Icc.of_isClosed_subset isClosed_closure hcl
  have hclosedPiece : ∀ i,
      IsClosed ((fun θ ↦ radialPoint (A.arc i).radius θ) '' closure (A.arc i).angles) := by
    intro i
    have hcont : Continuous (fun θ ↦ radialPoint (A.arc i).radius θ) := by
      unfold radialPoint
      fun_prop
    exact ((hcompactAngles i).image hcont).isClosed
  have hclosedCarrier : IsClosed closedCarrier :=
    isClosed_iUnion_of_finite hclosedPiece
  have hcarrierSub : A.carrier ⊆ closedCarrier := by
    intro z hz
    simp only [DisjointRadialArcs.carrier, CircularArc.carrier, Set.mem_iUnion] at hz
    obtain ⟨i, θ, hθ, rfl⟩ := hz
    simp only [closedCarrier, Set.mem_iUnion]
    exact ⟨i, θ, subset_closure hθ, rfl⟩
  have hclosedCarrierSub : closedCarrier ⊆ Ω := by
    intro z hz
    simp only [closedCarrier, Set.mem_iUnion] at hz
    obtain ⟨i, θ, hθ, rfl⟩ := hz
    have hθU : θ ∈ U (idx i) := by
      apply hclosureRefine i
      simpa [A, arc] using hθ
    exact hθU
  refine ⟨A, hcover, hangleSupport,
    (closure_minimal hcarrierSub hclosedCarrier).trans hclosedCarrierSub, ?_⟩
  intro i
  simpa [A, arc] using (hrad (idx i)).2.2.1

/-- Logarithmically normalized form of the radius-property selector. -/
theorem exists_logNormalized_disjointRadialArcs_closure_subset_of_isCompact_of_radiusProperty
    {P : ℝ → Prop} {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r : ℝ, 0 < r ∧ r < 1 ∧ P r ∧ radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.angularSupport ⊆ angleDomain ∧
        closure A.carrier ⊆ Ω ∧ (∀ i, P (A.arc i).radius) ∧
          greenPotential A.logMeasure 0 = volume A.angularSupport := by
  obtain ⟨A, hcover, hangle, hclosure, hradius⟩ :=
    exists_disjointRadialArcs_closure_subset_of_isCompact_of_radiusProperty
      hΩ hK hKangle hmeet
  exact ⟨A, hcover, hangle, hclosure, hradius, greenPotential_logMeasure_zero A⟩

/-- A compact subset of the inner bad directions admits logarithmically normalized slits,
all of radius at most `1 / 4`, whose closed carrier lies in `hallSlitRegion w`. -/
theorem exists_inner_logNormalized_slits_of_isCompact
    {w : ℂ → ℝ} {δ : ℝ} {K : Set ℝ}
    (hw : SubharmonicOn w unitDisk) (hw0 : w 0 = 1 - δ) (hδ : δ < 1)
    (hK : IsCompact K) (hKbad : K ⊆ innerBadDirections w) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.angularSupport ⊆ angleDomain ∧
        closure A.carrier ⊆ hallSlitRegion w ∧
          (∀ i, (A.arc i).radius ≤ (1 / 4 : ℝ)) ∧
            greenPotential A.logMeasure 0 = volume A.angularSupport := by
  apply exists_logNormalized_disjointRadialArcs_closure_subset_of_isCompact_of_radiusProperty
    (P := fun r ↦ r ≤ (1 / 4 : ℝ))
    (isOpen_hallSlitRegion hw) hK (fun θ hθ ↦ (hKbad hθ).1)
  intro θ hθ
  obtain ⟨_hangle, r, hr, hrw⟩ := hKbad hθ
  have hrne : r ≠ 0 := by
    intro hre
    subst r
    rw [radialPoint_zero, hw0] at hrw
    linarith
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hrne)
  refine ⟨r, hrpos, hr.2.trans_lt (by norm_num), hr.2, ?_⟩
  exact ⟨radialPoint_mem_unitDisk ⟨hr.1, hr.2.trans_lt (by norm_num)⟩,
    one_half_lt_one_sub_of_nonpos hrw⟩

/-- A compact subset of the outer bad directions admits logarithmically normalized slits,
all of radius at least `1 / 4`, whose closed carrier lies in `hallSlitRegion w`. -/
theorem exists_outer_logNormalized_slits_of_isCompact
    {w : ℂ → ℝ} {K : Set ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hK : IsCompact K) (hKbad : K ⊆ outerBadDirections w) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.angularSupport ⊆ angleDomain ∧
        closure A.carrier ⊆ hallSlitRegion w ∧
          (∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius) ∧
            greenPotential A.logMeasure 0 = volume A.angularSupport := by
  apply exists_logNormalized_disjointRadialArcs_closure_subset_of_isCompact_of_radiusProperty
    (P := fun r ↦ (1 / 4 : ℝ) ≤ r)
    (isOpen_hallSlitRegion hw) hK (fun θ hθ ↦ (hKbad hθ).1)
  intro θ hθ
  obtain ⟨_hangle, r, hr, hrw⟩ := hKbad hθ
  refine ⟨r, (by linarith [hr.1]), hr.2, hr.1.le, ?_⟩
  exact ⟨radialPoint_mem_unitDisk ⟨(by linarith [hr.1]), hr.2⟩,
    one_half_lt_one_sub_of_nonpos hrw⟩

/-- Hall's compact inner bad-direction estimate, obtained from the direct normalized Green
kernel, slit selection, and the maximum-principle comparison above. -/
theorem volume_compact_innerBadDirections_le
    {w : ℂ → ℝ} {δ : ℝ} {K : Set ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hwle : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw0 : w 0 = 1 - δ) (hδ : δ ≤ 1 / 2)
    (hK : IsCompact K) (hKbad : K ⊆ innerBadDirections w) :
    volume K ≤ ENNReal.ofReal ((10 * Real.pi) * δ) := by
  by_cases hKempty : K = ∅
  · simp [hKempty]
  have hKnonempty : K.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
  have hδlt : δ < 1 := hδ.trans_lt (by norm_num)
  obtain ⟨A, hcover, hangle, hclosure, hradius, hzero⟩ :=
    exists_inner_logNormalized_slits_of_isCompact hw hw0 hδlt hK hKbad
  have hangularNonempty : A.angularSupport.Nonempty := hKnonempty.mono hcover
  have hcarrier : A.carrier.Nonempty :=
    carrier_nonempty_of_angularSupport_nonempty A hangularNonempty
  have hcomparison := greenPotentialReal_logMeasure_le_two_mul_one_sub
    A hangle hcarrier hclosure hw hwle
      (show 0 ≤ 5 * Real.pi by positivity)
      (fun z hz ↦ greenPotential_logMeasure_le_inner A hz hradius hangle)
  have h0unit : (0 : ℂ) ∈ unitDisk := by simp [unitDisk]
  have h0away : (0 : ℂ) ∉ closure A.carrier := by
    intro h0
    have hslit := hclosure h0
    have : (1 / 2 : ℝ) < δ := by
      simpa [hallSlitRegion, hw0] using hslit.2
    linarith
  have h0G : (0 : ℂ) ∈ unitDisk \ closure A.carrier := ⟨h0unit, h0away⟩
  have hreal : greenPotentialReal A.logMeasure 0 ≤ (10 * Real.pi) * δ := by
    have hcomp0 := hcomparison 0 h0G
    rw [hw0] at hcomp0
    convert hcomp0 using 1 <;> ring
  have hfinite : ∀ i, volume (A.arc i).angles ≠ ∞ :=
    volume_arc_angles_ne_top_of_angularSupport_subset A hangle
  calc
    volume K ≤ volume A.angularSupport := measure_mono hcover
    _ = greenPotential A.logMeasure 0 := hzero.symm
    _ = ENNReal.ofReal (greenPotentialReal A.logMeasure 0) :=
      (ofReal_greenPotentialReal_logMeasure_eq_greenPotential A hfinite h0G).symm
    _ ≤ ENNReal.ofReal ((10 * Real.pi) * δ) := ENNReal.ofReal_le_ofReal hreal

/-- The full measurable inner bad-direction estimate. -/
theorem volume_innerBadDirections_le
    {w : ℂ → ℝ} {δ : ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hwle : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw0 : w 0 = 1 - δ) (hδ : δ ≤ 1 / 2) :
    volume (innerBadDirections w) ≤ ENNReal.ofReal ((10 * Real.pi) * δ) := by
  apply volume_le_of_forall_isCompact_subset_le (measurableSet_innerBadDirections hw.continuousOn)
  intro K hK hKbad
  exact volume_compact_innerBadDirections_le hw hwle hw0 hδ hK hKbad

/-- Hall's compact outer bad-direction estimate, obtained from the uniform outer normalized
Green-kernel bound and the same slit-domain comparison as in the inner estimate. -/
theorem volume_compact_outerBadDirections_le
    {w : ℂ → ℝ} {δ : ℝ} {K : Set ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hwle : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw0 : w 0 = 1 - δ) (hδ : δ ≤ 1 / 2)
    (hK : IsCompact K) (hKbad : K ⊆ outerBadDirections w) :
    volume K ≤ ENNReal.ofReal ((256 * Real.pi) * δ) := by
  by_cases hKempty : K = ∅
  · simp [hKempty]
  have hKnonempty : K.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
  obtain ⟨A, hcover, hangle, hclosure, hradius, hzero⟩ :=
    exists_outer_logNormalized_slits_of_isCompact hw hK hKbad
  have hangularNonempty : A.angularSupport.Nonempty := hKnonempty.mono hcover
  have hcarrier : A.carrier.Nonempty :=
    carrier_nonempty_of_angularSupport_nonempty A hangularNonempty
  have hcomparison := greenPotentialReal_logMeasure_le_two_mul_one_sub
    A hangle hcarrier hclosure hw hwle
      (show 0 ≤ 128 * Real.pi by positivity)
      (fun z hz ↦ greenPotential_logMeasure_le_outer A hz hradius hangle)
  have h0unit : (0 : ℂ) ∈ unitDisk := by simp [unitDisk]
  have h0away : (0 : ℂ) ∉ closure A.carrier := by
    intro h0
    have hslit := hclosure h0
    have : (1 / 2 : ℝ) < δ := by
      simpa [hallSlitRegion, hw0] using hslit.2
    linarith
  have h0G : (0 : ℂ) ∈ unitDisk \ closure A.carrier := ⟨h0unit, h0away⟩
  have hreal : greenPotentialReal A.logMeasure 0 ≤ (256 * Real.pi) * δ := by
    have hcomp0 := hcomparison 0 h0G
    rw [hw0] at hcomp0
    convert hcomp0 using 1 <;> ring
  have hfinite : ∀ i, volume (A.arc i).angles ≠ ∞ :=
    volume_arc_angles_ne_top_of_angularSupport_subset A hangle
  calc
    volume K ≤ volume A.angularSupport := measure_mono hcover
    _ = greenPotential A.logMeasure 0 := hzero.symm
    _ = ENNReal.ofReal (greenPotentialReal A.logMeasure 0) :=
      (ofReal_greenPotentialReal_logMeasure_eq_greenPotential A hfinite h0G).symm
    _ ≤ ENNReal.ofReal ((256 * Real.pi) * δ) := ENNReal.ofReal_le_ofReal hreal

/-- The full measurable outer bad-direction estimate. -/
theorem volume_outerBadDirections_le
    {w : ℂ → ℝ} {δ : ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hwle : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw0 : w 0 = 1 - δ) (hδ : δ ≤ 1 / 2) :
    volume (outerBadDirections w) ≤ ENNReal.ofReal ((256 * Real.pi) * δ) := by
  apply volume_le_of_forall_isCompact_subset_le (measurableSet_outerBadDirections hw.continuousOn)
  intro K hK hKbad
  exact volume_compact_outerBadDirections_le hw hwle hw0 hδ hK hKbad

/-- Unconditional quantitative Hall radial theorem for the concrete finite-circle-submean
notion of subharmonicity used throughout the LRW construction. -/
theorem hall_radial_unconditional (w : ℂ → ℝ) (δ : ℝ)
    (hw : SubharmonicOn w unitDisk)
    (_hw_nonneg : ∀ z ∈ unitDisk, 0 ≤ w z)
    (hw_le_one : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw_center : w 0 = 1 - δ)
    (hδ0 : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / 512) :
    ENNReal.ofReal Real.pi ≤ volume (goodDirections w) := by
  have hδhalf : δ ≤ 1 / 2 := by linarith
  have hinner := volume_innerBadDirections_le hw hw_le_one hw_center hδhalf
  have houter := volume_outerBadDirections_le hw hw_le_one hw_center hδhalf
  have hlower := hall_measure_lower_bound w
    (ENNReal.ofReal ((10 * Real.pi) * δ))
    (ENNReal.ofReal ((256 * Real.pi) * δ)) hinner houter
  have h10 : 0 ≤ (10 * Real.pi) * δ := by positivity
  have h256 : 0 ≤ (256 * Real.pi) * δ := by positivity
  have hpi :
      ENNReal.ofReal Real.pi ≤
        ENNReal.ofReal (2 * Real.pi) -
          (ENNReal.ofReal ((10 * Real.pi) * δ) +
            ENNReal.ofReal ((256 * Real.pi) * δ)) := by
    apply ENNReal.le_sub_of_add_le_left (by simp)
    rw [← ENNReal.ofReal_add h10 h256,
      ← ENNReal.ofReal_add (add_nonneg h10 h256) Real.pi_pos.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [Real.pi_pos]
  exact hpi.trans hlower

/-- Existence form of `hall_radial_unconditional`. -/
theorem exists_hall_good_direction_unconditional (w : ℂ → ℝ) (δ : ℝ)
    (hw : SubharmonicOn w unitDisk)
    (hw_nonneg : ∀ z ∈ unitDisk, 0 ≤ w z)
    (hw_le_one : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw_center : w 0 = 1 - δ)
    (hδ0 : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / 512) :
    ∃ θ ∈ angleDomain, ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) := by
  apply exists_goodDirection_of_pos w
  have hπ : 0 < ENNReal.ofReal Real.pi := ENNReal.ofReal_pos.2 Real.pi_pos
  exact hπ.trans_le
    (hall_radial_unconditional w δ hw hw_nonneg hw_le_one hw_center hδ0 hδsmall)

end Erdos515
