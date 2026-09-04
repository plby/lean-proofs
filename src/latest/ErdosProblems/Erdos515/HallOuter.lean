/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Hall
import ErdosProblems.Erdos515.BoundaryAccess

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos515

/-- Ordered disjointification of a finite family of sets. -/
def disjointRefinement {n : ℕ} (U : Fin n → Set ℝ) (i : Fin n) : Set ℝ :=
  U i \ ⋃ j : Fin i.1, U (Fin.castLE (Nat.le_of_lt i.2) j)

lemma disjointRefinement_subset {n : ℕ} (U : Fin n → Set ℝ) (i : Fin n) :
    disjointRefinement U i ⊆ U i := fun _ hx ↦ hx.1

lemma measurableSet_disjointRefinement {n : ℕ} {U : Fin n → Set ℝ}
    (hU : ∀ i, MeasurableSet (U i)) (i : Fin n) :
    MeasurableSet (disjointRefinement U i) := by
  apply (hU i).diff
  exact MeasurableSet.iUnion fun j ↦ hU _

lemma pairwise_disjointRefinement {n : ℕ} (U : Fin n → Set ℝ) :
    Pairwise fun i j : Fin n ↦ Disjoint (disjointRefinement U i) (disjointRefinement U j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hxUi : x ∈ U i := hxi.1
    have hcast : Fin.castLE (Nat.le_of_lt j.2) ⟨i.1, hij⟩ = i := by ext; rfl
    exact hxj.2 (by
      simp only [Set.mem_iUnion]
      refine ⟨⟨i.1, hij⟩, ?_⟩
      simpa only [hcast] using hxUi)
  · exact (by
      rw [disjoint_comm, Set.disjoint_left]
      intro x hxj hxi
      have hxUj : x ∈ U j := hxj.1
      have hcast : Fin.castLE (Nat.le_of_lt i.2) ⟨j.1, hji⟩ = j := by ext; rfl
      exact hxi.2 (by
        simp only [Set.mem_iUnion]
        refine ⟨⟨j.1, hji⟩, ?_⟩
        simpa only [hcast] using hxUj))

lemma iUnion_disjointRefinement_eq {n : ℕ} (U : Fin n → Set ℝ) :
    (⋃ i, disjointRefinement U i) = ⋃ i, U i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, hi.1⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    let P : ℕ → Prop := fun k ↦ ∃ hk : k < n, x ∈ U ⟨k, hk⟩
    have hP : ∃ k, P k := ⟨i.1, i.2, hi⟩
    let k := Nat.find hP
    have hkP : P k := Nat.find_spec hP
    obtain ⟨hkn, hxUk⟩ := hkP
    let kfin : Fin n := ⟨k, hkn⟩
    refine ⟨kfin, hxUk, ?_⟩
    intro hxprior
    simp only [Set.mem_iUnion] at hxprior
    obtain ⟨j, hxUj⟩ := hxprior
    have hjk : j.1 < Nat.find hP := by simpa [kfin, k] using j.2
    have hnot : ¬ P j.1 := Nat.find_min hP hjk
    apply hnot
    exact ⟨lt_trans j.2 hkn, by
      have hcast : Fin.castLE (Nat.le_of_lt hkn) j =
          (⟨j.1, lt_trans j.2 hkn⟩ : Fin n) := by ext; rfl
      simpa only [hcast] using hxUj⟩

end Erdos515

namespace Erdos515

/-- Compact outer radial projection can be represented by finitely many circular pieces with
pairwise disjoint angular supports, all lying in the given open set. -/
theorem exists_disjointRadialArcs_of_isCompact
    {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r ∈ Ioo (1 / 4 : ℝ) 1, radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ ⋃ i, (A.arc i).angles ∧ A.carrier ⊆ Ω := by
  classical
  let rad : K → ℝ := fun θ ↦ Classical.choose (hmeet θ θ.2)
  have hrad : ∀ θ : K, rad θ ∈ Ioo (1 / 4 : ℝ) 1 := fun θ ↦
    (Classical.choose_spec (hmeet θ θ.2)).1
  have hpoint : ∀ θ : K, radialPoint (rad θ) θ.1 ∈ Ω := fun θ ↦
    (Classical.choose_spec (hmeet θ θ.2)).2
  let U : K → Set ℝ := fun θ ↦ (fun φ ↦ radialPoint (rad θ) φ) ⁻¹' Ω
  have hUopen : ∀ θ, IsOpen (U θ) := by
    intro θ
    apply hΩ.preimage
    unfold radialPoint
    fun_prop
  have hKU : K ⊆ ⋃ θ, U θ := by
    intro θ hθ
    simp only [Set.mem_iUnion]
    exact ⟨⟨θ, hθ⟩, hpoint ⟨θ, hθ⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hKU
  let e : Fin t.card ≃ t := (Finset.equivFin t).symm
  let idx : Fin t.card → K := fun i ↦ (e i).1
  let Ufin : Fin t.card → Set ℝ := fun i ↦ U (idx i)
  have hKUfin : K ⊆ ⋃ i, Ufin i := by
    intro θ hθ
    have hx := ht hθ
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨a, haT, haU⟩ := hx
    let ati : t := ⟨a, haT⟩
    refine ⟨(Finset.equivFin t) ati, ?_⟩
    have he : e ((Finset.equivFin t) ati) = ati := by simp [e]
    simpa [Ufin, idx, he, ati] using haU
  have hUfinOpen : ∀ i, IsOpen (Ufin i) := fun i ↦ hUopen _
  let arc : Fin t.card → CircularArc := fun i ↦
    { radius := rad (idx i)
      angles := disjointRefinement Ufin i ∩ angleDomain
      radius_pos := lt_trans (by norm_num) (hrad (idx i)).1
      radius_lt_one := (hrad (idx i)).2
      measurableSet_angles :=
        (measurableSet_disjointRefinement (fun j ↦ (hUfinOpen j).measurableSet) i).inter
          measurableSet_Ico }
  let A : DisjointRadialArcs :=
    { n := t.card
      arc := arc
      angle_disjoint := by
        intro i _ j _ hij
        exact (pairwise_disjointRefinement Ufin hij).mono inter_subset_left inter_subset_left }
  refine ⟨A, ?_, ?_⟩
  · intro θ hθ
    have hθU : θ ∈ ⋃ i, Ufin i := hKUfin hθ
    rw [← iUnion_disjointRefinement_eq Ufin] at hθU
    simp only [Set.mem_iUnion] at hθU ⊢
    obtain ⟨i, hi⟩ := hθU
    exact ⟨i, hi, hKangle hθ⟩
  · intro z hz
    simp only [A, DisjointRadialArcs.carrier, Set.mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    obtain ⟨θ, hθ, rfl⟩ := hzi
    have hθU : θ ∈ Ufin i := (disjointRefinement_subset Ufin i) hθ.1
    exact hθU

end Erdos515

namespace Erdos515

/-- Strengthened compact selection: the angular neighborhoods are shrunk before the finite
subcover is chosen.  Consequently the closure of the resulting finite carrier, not merely the
carrier itself, stays in the prescribed open set.  This is the form needed on the slit boundary
in the maximum-principle comparison. -/
theorem exists_disjointRadialArcs_closure_subset_of_isCompact
    {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r ∈ Ioo (0 : ℝ) 1, radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ ⋃ i, (A.arc i).angles ∧ (⋃ i, (A.arc i).angles) ⊆ angleDomain ∧
        closure A.carrier ⊆ Ω := by
  classical
  let rad : K → ℝ := fun θ ↦ Classical.choose (hmeet θ θ.2)
  have hrad : ∀ θ : K, rad θ ∈ Ioo (0 : ℝ) 1 := fun θ ↦
    (Classical.choose_spec (hmeet θ θ.2)).1
  have hpoint : ∀ θ : K, radialPoint (rad θ) θ.1 ∈ Ω := fun θ ↦
    (Classical.choose_spec (hmeet θ θ.2)).2
  let U : K → Set ℝ := fun θ ↦ (fun φ ↦ radialPoint (rad θ) φ) ⁻¹' Ω
  have hUopen : ∀ θ, IsOpen (U θ) := by
    intro θ
    apply hΩ.preimage
    unfold radialPoint
    fun_prop
  have hexists : ∀ θ : K, ∃ ε : ℝ, 0 < ε ∧ Metric.ball θ.1 ε ⊆ U θ := by
    intro θ
    exact Metric.isOpen_iff.mp (hUopen θ) θ.1 (hpoint θ)
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
      radius_lt_one := (hrad (idx i)).2
      measurableSet_angles :=
        (measurableSet_disjointRefinement (fun j ↦ (hUfinOpen j).measurableSet) i).inter
          measurableSet_Ico }
  let A : DisjointRadialArcs :=
    { n := t.card
      arc := arc
      angle_disjoint := by
        intro i _ j _ hij
        exact (pairwise_disjointRefinement Ufin hij).mono inter_subset_left inter_subset_left }
  have hcover : K ⊆ ⋃ i, (A.arc i).angles := by
    intro θ hθ
    have hθU : θ ∈ ⋃ i, Ufin i := hKUfin hθ
    rw [← iUnion_disjointRefinement_eq Ufin] at hθU
    simp only [Set.mem_iUnion] at hθU ⊢
    obtain ⟨i, hi⟩ := hθU
    exact ⟨i, hi, hKangle hθ⟩
  have hangleSupport : (⋃ i, (A.arc i).angles) ⊆ angleDomain := by
    intro θ hθ
    simp only [Set.mem_iUnion] at hθ
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
  refine ⟨A, hcover, hangleSupport, ?_⟩
  exact (closure_minimal hcarrierSub hclosedCarrier).trans hclosedCarrierSub

end Erdos515

namespace Erdos515

/-- Extended-real Green potential restricted to a measurable or nonmeasurable shell. -/
noncomputable def greenPotentialOn (ν : Measure ℂ) (S : Set ℂ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ in S, diskGreenENNReal z ζ ∂ν

/-- Any two countable shell covers give the `hdecomp` inequality needed by the dyadic argument. -/
theorem greenPotentialOn_le_dyadic_decomposition {ν : Measure ℂ} {S : Set ℂ} (z : ℂ)
    (far near : ℕ → Set ℂ)
    (hcover : S ⊆ (⋃ j, far j) ∪ ⋃ j, near j) :
    greenPotentialOn ν S z ≤
      (∑' j, greenPotentialOn ν (far j) z) +
        ∑' j, greenPotentialOn ν (near j) z := by
  calc
    greenPotentialOn ν S z ≤
        greenPotentialOn ν ((⋃ j, far j) ∪ ⋃ j, near j) z :=
      MeasureTheory.lintegral_mono_set hcover
    _ ≤ greenPotentialOn ν (⋃ j, far j) z +
        greenPotentialOn ν (⋃ j, near j) z :=
      MeasureTheory.lintegral_union_le _ _ _
    _ ≤ (∑' j, greenPotentialOn ν (far j) z) +
        ∑' j, greenPotentialOn ν (near j) z := by
      exact add_le_add
        (MeasureTheory.lintegral_iUnion_le far (diskGreenENNReal z))
        (MeasureTheory.lintegral_iUnion_le near (diskGreenENNReal z))

/-- On a far shell the extended Green potential is bounded by the rational kernel from (11). -/
theorem greenPotentialOn_far_le {ν : Measure ℂ} {S : Set ℂ} {z : ℂ}
    (hS : MeasurableSet S) (hz : ‖z‖ < 1)
    (hinside : ∀ ζ ∈ S, ‖ζ‖ < 1) (hoff : z ∉ S) :
    greenPotentialOn ν S z ≤
      ∫⁻ ζ in S, ENNReal.ofReal
        (2 * (1 - ‖z‖) * (1 - ‖ζ‖) / ‖z - ζ‖ ^ 2) ∂ν := by
  apply MeasureTheory.setLIntegral_mono' hS
  intro ζ hζ
  have hne : z ≠ ζ := fun h ↦ hoff (h ▸ hζ)
  rw [diskGreenENNReal_of_ne hne]
  exact ENNReal.ofReal_le_ofReal (diskGreen_le_two_mul hz (hinside ζ hζ) hne)

/-- On a near shell the extended Green potential is bounded by the local logarithmic kernel
from (12). -/
theorem greenPotentialOn_near_le {ν : Measure ℂ} {S : Set ℂ} {z : ℂ}
    (hS : MeasurableSet S) (hz : ‖z‖ < 1) (hoff : z ∉ S)
    (hclose : ∀ ζ ∈ S, ‖z - ζ‖ ≤ (1 - ‖z‖) / 2) :
    greenPotentialOn ν S z ≤
      ∫⁻ ζ in S, ENNReal.ofReal
        (Real.log (3 * (1 - ‖z‖) / ‖z - ζ‖)) ∂ν := by
  apply MeasureTheory.setLIntegral_mono' hS
  intro ζ hζ
  have hne : z ≠ ζ := fun h ↦ hoff (h ▸ hζ)
  rw [diskGreenENNReal_of_ne hne]
  exact ENNReal.ofReal_le_ofReal (diskGreen_le_localLog hz hne (hclose ζ hζ))

/-- A shellwise majorant immediately supplies the real-valued dyadic hypothesis used by
`greenPotential_disjointArcs_le`. This small lemma is useful after converting finite ENNReal
shell integrals to real values. -/
theorem dyadic_hdecomp_of_shell_bounds {φ : ℝ} {far near farMajor nearMajor : ℕ → ℝ}
    (hdecomp : φ ≤ (∑' j, far j) + ∑' j, near j)
    (hfar : ∀ j, far j ≤ farMajor j) (hnear : ∀ j, near j ≤ nearMajor j)
    (sfar : Summable far) (snear : Summable near)
    (sfarMajor : Summable farMajor) (snearMajor : Summable nearMajor) :
    φ ≤ (∑' j, farMajor j) + ∑' j, nearMajor j := by
  exact hdecomp.trans (add_le_add
    (sfar.tsum_le_tsum hfar sfarMajor) (snear.tsum_le_tsum hnear snearMajor))

/-! ### The exact projection estimate at the origin

The normalization of `CircularArc.weightedMeasure` was chosen so that the elementary
one-variable inequality `1 - r ≤ log (1 / r)` turns the Green potential at the origin into
angular measure.  The following lemmas carry out that calculation for the actual mapped and
weighted measures, and then sum it over the finite disjoint family. -/

lemma one_sub_le_log_one_div {r : ℝ} (hr : 0 < r) :
    1 - r ≤ Real.log (1 / r) := by
  have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
  rw [one_div, Real.log_inv]
  linarith

@[simp] lemma norm_radialPoint {r θ : ℝ} (hr : 0 ≤ r) :
    ‖radialPoint r θ‖ = r := by
  simp [radialPoint, abs_of_nonneg hr]

lemma radialPoint_ne_zero {r θ : ℝ} (hr : 0 < r) :
    radialPoint r θ ≠ 0 := by
  intro h
  have hz : r = 0 := by
    have := congrArg norm h
    simpa [norm_radialPoint hr.le] using this
  exact hr.ne' hz

lemma diskGreen_zero_radialPoint {r θ : ℝ} (hr : 0 < r) :
    diskGreen 0 (radialPoint r θ) = Real.log (1 / r) := by
  rw [diskGreen_zero, norm_radialPoint hr.le]

lemma diskGreenENNReal_zero_radialPoint {r θ : ℝ} (hr : 0 < r) :
    diskGreenENNReal 0 (radialPoint r θ) =
      ENNReal.ofReal (Real.log (1 / r)) := by
  rw [diskGreenENNReal_of_ne (radialPoint_ne_zero hr).symm,
    diskGreen_zero_radialPoint hr]

lemma measurable_diskGreenENNReal_zero :
    Measurable (fun ζ : ℂ ↦ diskGreenENNReal 0 ζ) := by
  unfold diskGreenENNReal diskGreen
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_const measurable_id
  · exact measurable_const
  · fun_prop

lemma measurable_diskGreen_zero : Measurable (fun ζ : ℂ ↦ diskGreen 0 ζ) := by
  simp_rw [diskGreen_zero]
  fun_prop

lemma greenPotential_weightedMeasure_zero (a : CircularArc) :
    greenPotential a.weightedMeasure 0 =
      ENNReal.ofReal (a.radius / (1 - a.radius)) *
        (ENNReal.ofReal (Real.log (1 / a.radius)) * volume a.angles) := by
  rw [greenPotential, CircularArc.weightedMeasure,
    MeasureTheory.lintegral_smul_measure]
  change ENNReal.ofReal (a.radius / (1 - a.radius)) *
      (∫⁻ ζ, diskGreenENNReal 0 ζ ∂Measure.map
        (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) = _
  rw [MeasureTheory.lintegral_map measurable_diskGreenENNReal_zero]
  · simp_rw [diskGreenENNReal_zero_radialPoint a.radius_pos]
    rw [MeasureTheory.lintegral_const]
    rw [Measure.restrict_apply_univ]
  · unfold radialPoint
    fun_prop

lemma quarter_le_weighted_green_coefficient (a : CircularArc)
    (hr : (1 / 4 : ℝ) ≤ a.radius) :
    ENNReal.ofReal (1 / 4 : ℝ) ≤
      ENNReal.ofReal (a.radius / (1 - a.radius)) *
        ENNReal.ofReal (Real.log (1 / a.radius)) := by
  have hgap : 0 < 1 - a.radius := sub_pos.mpr a.radius_lt_one
  have hlog0 : 0 ≤ Real.log (1 / a.radius) := by
    exact Real.log_nonneg (one_le_one_div a.radius_pos a.radius_lt_one.le)
  have hlog : 1 - a.radius ≤ Real.log (1 / a.radius) :=
    one_sub_le_log_one_div a.radius_pos
  have hcoeff : (1 / 4 : ℝ) ≤
      (a.radius / (1 - a.radius)) * Real.log (1 / a.radius) := by
    calc
      (1 / 4 : ℝ) ≤ a.radius := hr
      _ = (a.radius / (1 - a.radius)) * (1 - a.radius) := by
        field_simp
      _ ≤ (a.radius / (1 - a.radius)) * Real.log (1 / a.radius) := by
        exact mul_le_mul_of_nonneg_left hlog (div_nonneg a.radius_pos.le hgap.le)
  rw [← ENNReal.ofReal_mul (div_nonneg a.radius_pos.le hgap.le)]
  exact ENNReal.ofReal_le_ofReal hcoeff

/-- The angular support of the finite family of selected circular arcs. -/
def DisjointRadialArcs.angularSupport (A : DisjointRadialArcs) : Set ℝ :=
  ⋃ i, (A.arc i).angles

/-- For one selected arc of radius at least `1/4`, angular projection costs at most four
times its Green potential at the origin. -/
theorem circularArc_projection_le_four_greenPotential (a : CircularArc)
    (hr : (1 / 4 : ℝ) ≤ a.radius) :
    volume a.angles ≤ 4 * greenPotential a.weightedMeasure 0 := by
  rw [greenPotential_weightedMeasure_zero]
  have hc := quarter_le_weighted_green_coefficient a hr
  have hquarter : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul]
    exact ENNReal.mul_inv_cancel (a := (4 : ℝ≥0∞)) (by norm_num) (by norm_num)
  calc
    volume a.angles =
        (4 * ENNReal.ofReal (1 / 4 : ℝ)) * volume a.angles := by
          rw [hquarter, one_mul]
    _ ≤ (4 * (ENNReal.ofReal (a.radius / (1 - a.radius)) *
          ENNReal.ofReal (Real.log (1 / a.radius)))) * volume a.angles := by
      gcongr
    _ = 4 * (ENNReal.ofReal (a.radius / (1 - a.radius)) *
          (ENNReal.ofReal (Real.log (1 / a.radius)) * volume a.angles)) := by
      ac_rfl

/-- The complete finite-family origin estimate from Hall's outer argument.  Disjointness is
not needed for this upper bound (subadditivity suffices), but it is part of the selected-family
structure and is used by the uniform-potential estimate away from the origin. -/
theorem disjointRadialArcs_projection_le_four_greenPotential
    (A : DisjointRadialArcs)
    (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius) :
    volume A.angularSupport ≤ 4 * greenPotential A.measure 0 := by
  calc
    volume A.angularSupport ≤ ∑ i, volume (A.arc i).angles := by
      simpa [DisjointRadialArcs.angularSupport] using
        measure_iUnion_fintype_le volume (fun i ↦ (A.arc i).angles)
    _ ≤ ∑ i, 4 * greenPotential (A.arc i).weightedMeasure 0 := by
      exact Finset.sum_le_sum fun i _ ↦
        circularArc_projection_le_four_greenPotential (A.arc i) (hr i)
    _ = 4 * greenPotential A.measure 0 := by
      simp [greenPotential, DisjointRadialArcs.measure, Finset.mul_sum]

/-- A covered angular set inherits the finite-family origin estimate. -/
theorem angularSet_le_four_greenPotential_of_subset {K : Set ℝ}
    (A : DisjointRadialArcs) (hK : K ⊆ A.angularSupport)
    (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius) :
    volume K ≤ 4 * greenPotential A.measure 0 :=
  (measure_mono hK).trans (disjointRadialArcs_projection_le_four_greenPotential A hr)

/-! ### Logarithmically normalized slit measures

For the direct version of Hall's slit argument it is convenient to put mass
`dθ / log (1 / r)` on an arc of radius `r`.  Its Green potential at zero is then *exactly*
the angular measure of the arc.  This avoids the loss of four and, more importantly, works at
every positive radius below one. -/

namespace CircularArc

noncomputable def logWeightedMeasure (a : CircularArc) : Measure ℂ :=
  ENNReal.ofReal (1 / Real.log (1 / a.radius)) •
    Measure.map (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)

lemma log_one_div_pos (a : CircularArc) : 0 < Real.log (1 / a.radius) := by
  apply Real.log_pos
  exact one_lt_one_div a.radius_pos a.radius_lt_one

/-- The original arclength/boundary-distance weight is bounded by the logarithmically
normalized weight. -/
lemma radius_div_one_sub_le_one_div_log (a : CircularArc) :
    a.radius / (1 - a.radius) ≤ 1 / Real.log (1 / a.radius) := by
  have hgap : 0 < 1 - a.radius := sub_pos.mpr a.radius_lt_one
  have hlog := a.log_one_div_pos
  have hlogUpper : Real.log (1 / a.radius) ≤ (1 - a.radius) / a.radius := by
    have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr a.radius_pos)
    calc
      Real.log (1 / a.radius) ≤ 1 / a.radius - 1 := h
      _ = (1 - a.radius) / a.radius := by field_simp [a.radius_pos.ne']
  have hm := mul_le_mul_of_nonneg_left hlogUpper a.radius_pos.le
  have hmul : a.radius * Real.log (1 / a.radius) ≤ 1 - a.radius := by
    calc
    a.radius * Real.log (1 / a.radius) ≤
        a.radius * ((1 - a.radius) / a.radius) := hm
    _ = 1 - a.radius := by field_simp [a.radius_pos.ne']
  apply (div_le_iff₀ hgap).2
  rw [one_div, ← div_eq_inv_mul]
  exact (le_div_iff₀ hlog).2 hmul

/-- Above radius `1/4`, the logarithmic weight is at most four times the original weight. -/
lemma one_div_log_le_four_radius_div_one_sub (a : CircularArc)
    (hr : (1 / 4 : ℝ) ≤ a.radius) :
    1 / Real.log (1 / a.radius) ≤ 4 * (a.radius / (1 - a.radius)) := by
  have hgap : 0 < 1 - a.radius := sub_pos.mpr a.radius_lt_one
  have hlog := a.log_one_div_pos
  have hlogLower : 1 - a.radius ≤ Real.log (1 / a.radius) :=
    one_sub_le_log_one_div a.radius_pos
  have hfour : 1 ≤ 4 * a.radius := by linarith
  apply (div_le_iff₀ hlog).2
  calc
    1 ≤ 4 * a.radius := hfour
    _ = (4 * (a.radius / (1 - a.radius))) * (1 - a.radius) := by
      field_simp [hgap.ne']
    _ ≤ (4 * (a.radius / (1 - a.radius))) * Real.log (1 / a.radius) := by
      exact mul_le_mul_of_nonneg_left hlogLower (by positivity)

lemma weightedMeasure_le_logWeightedMeasure (a : CircularArc) :
    a.weightedMeasure ≤ a.logWeightedMeasure := by
  unfold weightedMeasure logWeightedMeasure
  refine Measure.le_iff.mpr fun s _hs ↦ ?_
  simp only [Measure.smul_apply]
  exact mul_le_mul (ENNReal.ofReal_le_ofReal
    a.radius_div_one_sub_le_one_div_log) le_rfl bot_le bot_le

lemma logWeightedMeasure_le_four_smul_weightedMeasure (a : CircularArc)
    (hr : (1 / 4 : ℝ) ≤ a.radius) :
    a.logWeightedMeasure ≤ (4 : ℝ≥0∞) • a.weightedMeasure := by
  unfold weightedMeasure logWeightedMeasure
  rw [smul_smul]
  have h := ENNReal.ofReal_le_ofReal (a.one_div_log_le_four_radius_div_one_sub hr)
  have hc : ENNReal.ofReal (1 / Real.log (1 / a.radius)) ≤
      4 * ENNReal.ofReal (a.radius / (1 - a.radius)) := by
    simpa [← ENNReal.ofReal_mul (show 0 ≤ (4 : ℝ) by norm_num)] using h
  refine Measure.le_iff.mpr fun s _hs ↦ ?_
  simp only [Measure.smul_apply]
  exact mul_le_mul hc le_rfl bot_le bot_le

end CircularArc

namespace DisjointRadialArcs

noncomputable def logMeasure (A : DisjointRadialArcs) : Measure ℂ :=
  ∑ i, (A.arc i).logWeightedMeasure

lemma measure_le_logMeasure (A : DisjointRadialArcs) : A.measure ≤ A.logMeasure := by
  unfold measure logMeasure
  exact Finset.sum_le_sum fun i _ ↦ (A.arc i).weightedMeasure_le_logWeightedMeasure

lemma logMeasure_le_four_smul_measure (A : DisjointRadialArcs)
    (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius) :
    A.logMeasure ≤ (4 : ℝ≥0∞) • A.measure := by
  unfold measure logMeasure
  rw [Finset.smul_sum]
  exact Finset.sum_le_sum fun i _ ↦
    (A.arc i).logWeightedMeasure_le_four_smul_weightedMeasure (hr i)

end DisjointRadialArcs

lemma greenPotential_measure_le_logMeasure (A : DisjointRadialArcs) (z : ℂ) :
    greenPotential A.measure z ≤ greenPotential A.logMeasure z :=
  greenPotential_mono_measure A.measure_le_logMeasure z

lemma greenPotential_logMeasure_le_four_mul_measure (A : DisjointRadialArcs) (z : ℂ)
    (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius) :
    greenPotential A.logMeasure z ≤ 4 * greenPotential A.measure z := by
  exact (greenPotential_mono_measure (A.logMeasure_le_four_smul_measure hr) z).trans_eq (by
    simp [greenPotential, MeasureTheory.lintegral_smul_measure])

theorem greenPotential_logMeasure_le_of_weighted {A : DisjointRadialArcs} {z : ℂ}
    {C : ℝ≥0∞} (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius)
  (hweighted : greenPotential A.measure z ≤ C) :
    greenPotential A.logMeasure z ≤ 4 * C :=
  (greenPotential_logMeasure_le_four_mul_measure A z hr).trans
    (mul_le_mul le_rfl hweighted bot_le bot_le)

lemma greenPotential_logWeightedMeasure_zero (a : CircularArc) :
    greenPotential a.logWeightedMeasure 0 = volume a.angles := by
  rw [greenPotential, CircularArc.logWeightedMeasure,
    MeasureTheory.lintegral_smul_measure]
  change ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
      (∫⁻ ζ, diskGreenENNReal 0 ζ ∂Measure.map
        (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) = _
  rw [MeasureTheory.lintegral_map measurable_diskGreenENNReal_zero]
  · simp_rw [diskGreenENNReal_zero_radialPoint a.radius_pos]
    rw [MeasureTheory.lintegral_const]
    rw [Measure.restrict_apply_univ]
    have hlog := a.log_one_div_pos
    have hcoeff : ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
        ENNReal.ofReal (Real.log (1 / a.radius)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.log (1 / a.radius))]
      have hreal : (1 / Real.log (1 / a.radius)) * Real.log (1 / a.radius) = 1 := by
        field_simp
      rw [hreal, ENNReal.ofReal_one]
    calc
      ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
          (ENNReal.ofReal (Real.log (1 / a.radius)) * volume a.angles) =
          (ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
            ENNReal.ofReal (Real.log (1 / a.radius))) * volume a.angles := by ac_rfl
      _ = volume a.angles := by rw [hcoeff, one_mul]
  · unfold radialPoint
    fun_prop

/-- Real-valued counterpart of `greenPotential_logWeightedMeasure_zero`.  Finiteness of the
angular support is exactly the hypothesis under which the Bochner integral represents the
extended nonnegative integral rather than taking its conventional nonintegrable value. -/
lemma greenPotentialReal_logWeightedMeasure_zero (a : CircularArc)
    (_hfinite : volume a.angles ≠ ∞) :
    greenPotentialReal a.logWeightedMeasure 0 = (volume a.angles).toReal := by
  rw [greenPotentialReal, CircularArc.logWeightedMeasure,
    MeasureTheory.integral_smul_measure]
  change (ENNReal.ofReal (1 / Real.log (1 / a.radius))).toReal *
      (∫ ζ, diskGreen 0 ζ ∂Measure.map
        (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) = _
  rw [MeasureTheory.integral_map]
  · simp_rw [diskGreen_zero_radialPoint a.radius_pos]
    rw [MeasureTheory.integral_const]
    rw [Measure.real_def, Measure.restrict_apply_univ]
    simp only [smul_eq_mul]
    have hlog := a.log_one_div_pos
    rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hlog.le)]
    field_simp
  · unfold radialPoint
    fun_prop
  · exact measurable_diskGreen_zero.stronglyMeasurable.aestronglyMeasurable

lemma measurableSet_angularSupport (A : DisjointRadialArcs) :
    MeasurableSet A.angularSupport := by
  exact MeasurableSet.iUnion fun i ↦ (A.arc i).measurableSet_angles

lemma volume_angularSupport (A : DisjointRadialArcs) :
    volume A.angularSupport = ∑ i, volume (A.arc i).angles := by
  have hpair : Pairwise (fun i j ↦ Disjoint (A.arc i).angles (A.arc j).angles) := by
    intro i j hij
    exact A.angle_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
  rw [DisjointRadialArcs.angularSupport, measure_iUnion hpair
    (fun i ↦ (A.arc i).measurableSet_angles), tsum_fintype]

/-- With logarithmic normalization, the finite slit potential at the origin equals its angular
projection measure exactly. -/
theorem greenPotential_logMeasure_zero (A : DisjointRadialArcs) :
    greenPotential A.logMeasure 0 = volume A.angularSupport := by
  rw [greenPotential, DisjointRadialArcs.logMeasure,
    MeasureTheory.lintegral_finsetSum_measure]
  change (∑ i, greenPotential (A.arc i).logWeightedMeasure 0) = _
  rw [Finset.sum_congr rfl (fun i _ ↦ greenPotential_logWeightedMeasure_zero (A.arc i))]
  exact (volume_angularSupport A).symm

/-- Compact radial selection with a normalized slit measure whose origin potential is exactly
the measure of the covered angular support. -/
theorem exists_logNormalized_disjointRadialArcs_of_isCompact
    {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r ∈ Ioo (1 / 4 : ℝ) 1, radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.carrier ⊆ Ω ∧
        greenPotential A.logMeasure 0 = volume A.angularSupport := by
  obtain ⟨A, hcover, hcarrier⟩ :=
    exists_disjointRadialArcs_of_isCompact hΩ hK hKangle hmeet
  exact ⟨A, hcover, hcarrier, greenPotential_logMeasure_zero A⟩

/-- All-radii, closure-safe form of the logarithmically normalized compact selector. -/
theorem exists_logNormalized_disjointRadialArcs_closure_subset_of_isCompact
    {Ω : Set ℂ} {K : Set ℝ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKangle : K ⊆ angleDomain)
    (hmeet : ∀ θ ∈ K, ∃ r ∈ Ioo (0 : ℝ) 1, radialPoint r θ ∈ Ω) :
    ∃ A : DisjointRadialArcs,
      K ⊆ A.angularSupport ∧ A.angularSupport ⊆ angleDomain ∧ closure A.carrier ⊆ Ω ∧
        greenPotential A.logMeasure 0 = volume A.angularSupport := by
  obtain ⟨A, hcover, hangle, hclosure⟩ :=
    exists_disjointRadialArcs_closure_subset_of_isCompact hΩ hK hKangle hmeet
  exact ⟨A, hcover, hangle, hclosure, greenPotential_logMeasure_zero A⟩

/-! ### Maximum-principle comparison on slit-domain exhaustions -/

/-- A subharmonic difference with nonpositive frontier values is nonpositive throughout a
bounded open comparison domain.  This is the precise sign-normalized maximum-principle step
used for `φ - C ψ` on components of a slit disk. -/
theorem subharmonicDifference_nonpos_on_bounded_open
    {φ ψ : ℂ → ℝ} {Ω V : Set ℂ} {C : ℝ}
    (hsub : SubharmonicOn (fun z ↦ φ z - C * ψ z) Ω)
    (hVopen : IsOpen V) (hVbounded : Bornology.IsBounded V)
    (hVclosure : closure V ⊆ Ω)
    (hfront : ∀ z ∈ frontier V, φ z ≤ C * ψ z) :
    ∀ z ∈ V, φ z ≤ C * ψ z := by
  intro z hz
  have hle := hsub.le_on_bounded_open_of_frontier_le hVopen hVbounded hVclosure
    (M := 0) (fun y hy ↦ by linarith [hfront y hy]) z hz
  linarith

/-- Exhaustion form of the slit-domain comparison.  It isolates exactly what remains after
the boundary behavior of the Green potential supplies, for each positive error, a bounded
comparison domain around `z`. -/
theorem subharmonicDifference_nonpos_of_exhaustions
    {φ ψ : ℂ → ℝ} {Ω G : Set ℂ} {C : ℝ}
    (hsub : SubharmonicOn (fun z ↦ φ z - C * ψ z) Ω)
    (hexhaust : ∀ z ∈ G, ∀ ε : ℝ, 0 < ε →
      ∃ V : Set ℂ, IsOpen V ∧ Bornology.IsBounded V ∧ z ∈ V ∧ closure V ⊆ Ω ∧
        ∀ y ∈ frontier V, φ y - C * ψ y ≤ ε) :
    ∀ z ∈ G, φ z ≤ C * ψ z := by
  intro z hz
  by_contra hnot
  have hpos : 0 < φ z - C * ψ z := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨V, hVopen, hVbounded, hzV, hVclosure, hfront⟩ :=
    hexhaust z hz ((φ z - C * ψ z) / 2) (by positivity)
  have hle := hsub.le_on_bounded_open_of_frontier_le hVopen hVbounded hVclosure
    (M := (φ z - C * ψ z) / 2) hfront z hzV
  linarith

noncomputable def arcGreenPotential (a : CircularArc) (z : ℂ) : ℝ :=
  ∫ θ in a.angles, diskGreen z (radialPoint a.radius θ)

lemma radialPoint_mem_carrier (a : CircularArc) {θ : ℝ} (hθ : θ ∈ a.angles) :
    radialPoint a.radius θ ∈ a.carrier :=
  ⟨θ, hθ, rfl⟩

lemma arc_carrier_subset_disjoint_carrier (A : DisjointRadialArcs) (i : Fin A.n) :
    (A.arc i).carrier ⊆ A.carrier := by
  intro z hz
  exact Set.mem_iUnion.2 ⟨i, hz⟩

lemma diskGreen_bound_on_ball_away
    {c ζ w : ℂ} {e : ℝ}
    (he : 0 < e) (hw : w ∈ Metric.ball c (e / 2))
    (hcζ : e ≤ ‖c - ζ‖) (hwunit : ‖w‖ < 1) (hζunit : ‖ζ‖ < 1) :
    ‖diskGreen w ζ‖ ≤ 2 / e ^ 2 := by
  have hdist : e / 2 ≤ ‖w - ζ‖ := by
    have htri : ‖c - ζ‖ ≤ ‖c - w‖ + ‖w - ζ‖ := by
      calc
        ‖c - ζ‖ = ‖(c - w) + (w - ζ)‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    have hcw : ‖c - w‖ < e / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
    linarith
  have hne : w ≠ ζ := by
    intro h
    subst ζ
    simpa using (show 0 < e / 2 by positivity)
      |>.trans_le hdist
  have hnonneg := diskGreen_nonneg hwunit hζunit hne
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  refine (diskGreen_le_greenQuotient hwunit hζunit hne).trans ?_
  have hwfac : 0 ≤ 1 - ‖w‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖w‖ by linarith)
      (show 0 ≤ 1 + ‖w‖ by positivity)]
  have hζfac : 0 ≤ 1 - ‖ζ‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖ζ‖ by linarith)
      (show 0 ≤ 1 + ‖ζ‖ by positivity)]
  have hnum : (1 - ‖w‖ ^ 2) * (1 - ‖ζ‖ ^ 2) ≤ 1 := by
    have hwle : 1 - ‖w‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
    have hζle : 1 - ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖ζ‖]
    calc
      (1 - ‖w‖ ^ 2) * (1 - ‖ζ‖ ^ 2) ≤ (1 - ‖w‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hζle hwfac
      _ ≤ 1 := by simpa using hwle
  have hden : e ^ 2 / 2 ≤ 2 * ‖w - ζ‖ ^ 2 := by
    nlinarith [sq_le_sq₀ (by positivity : 0 ≤ e / 2) (norm_nonneg (w - ζ)) |>.2 hdist]
  have hdistpos : 0 < ‖w - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hdenpos : 0 < 2 * ‖w - ζ‖ ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hdistpos)
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  calc
    ((1 - ‖w‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) / (2 * ‖w - ζ‖ ^ 2)
        ≤ 1 / (2 * ‖w - ζ‖ ^ 2) := div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ 2 / e ^ 2 := by
      rw [div_le_div_iff₀ hdenpos he2]
      nlinarith

lemma continuousAt_arcGreenPotential
    (a : CircularArc) (hfinite : volume a.angles ≠ ∞)
    {z : ℂ} (hzunit : z ∈ unitDisk) (hzaway : z ∉ closure a.carrier) :
    ContinuousAt (arcGreenPotential a) z := by
  have hOpenUD : IsOpen unitDisk := by
    simpa [unitDisk] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
  have hΩ : IsOpen (unitDisk \ closure a.carrier) :=
    hOpenUD.sdiff isClosed_closure
  have hzΩ : z ∈ unitDisk \ closure a.carrier := ⟨hzunit, hzaway⟩
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hΩ z hzΩ
  have hsep : ∀ θ ∈ a.angles, e ≤ ‖z - radialPoint a.radius θ‖ := by
    intro θ hθ
    by_contra hnot
    have hlt : ‖z - radialPoint a.radius θ‖ < e := lt_of_not_ge hnot
    have hmem : radialPoint a.radius θ ∈ Metric.ball z e := by
      simpa [Metric.mem_ball, dist_eq_norm'] using hlt
    exact (hball hmem).2 (subset_closure (radialPoint_mem_carrier a hθ))
  unfold arcGreenPotential
  apply MeasureTheory.continuousAt_of_dominated
      (μ := volume.restrict a.angles) (bound := fun _ ↦ 2 / e ^ 2)
  · filter_upwards [] with w
    unfold diskGreen radialPoint
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [Metric.ball_mem_nhds z (half_pos he)] with w hw
    filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    exact diskGreen_bound_on_ball_away he hw (hsep θ hθ)
      (by simpa [unitDisk] using (hball
        (Metric.ball_subset_ball (half_le_self he.le) hw)).1)
      (by simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one)
  · exact integrableOn_const hfinite
  · filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    apply continuousAt_diskGreen_left
    · intro h
      exact hzaway (subset_closure (h ▸ radialPoint_mem_carrier a hθ))
    · intro hzero
      have hprod : ‖radialPoint a.radius θ‖ * ‖z‖ = 1 := by
        have hone : (starRingEnd ℂ) (radialPoint a.radius θ) * z = 1 :=
          (sub_eq_zero.mp hzero).symm
        have := congrArg norm hone
        simpa [norm_mul, Complex.norm_conj] using this
      have hlt : ‖radialPoint a.radius θ‖ * ‖z‖ < 1 := by
        have hzunit' : ‖z‖ < 1 := by simpa [unitDisk] using hzunit
        calc
          ‖radialPoint a.radius θ‖ * ‖z‖ ≤ ‖radialPoint a.radius θ‖ * 1 :=
            mul_le_mul_of_nonneg_left hzunit'.le (norm_nonneg _)
          _ < 1 := by simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one
      linarith

lemma integrableOn_diskGreen_radial
    (a : CircularArc) (hfinite : volume a.angles ≠ ∞)
    {z : ℂ} (hzunit : z ∈ unitDisk) (hzaway : z ∉ closure a.carrier) :
    Integrable (fun θ ↦ diskGreen z (radialPoint a.radius θ))
      (volume.restrict a.angles) := by
  have hOpenUD : IsOpen unitDisk := by
    simpa [unitDisk] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
  have hΩ : IsOpen (unitDisk \ closure a.carrier) := hOpenUD.sdiff isClosed_closure
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hΩ z ⟨hzunit, hzaway⟩
  have hsep : ∀ θ ∈ a.angles, e ≤ ‖z - radialPoint a.radius θ‖ := by
    intro θ hθ
    by_contra hnot
    have hlt : ‖z - radialPoint a.radius θ‖ < e := lt_of_not_ge hnot
    have hmem : radialPoint a.radius θ ∈ Metric.ball z e := by
      simpa [Metric.mem_ball, dist_eq_norm'] using hlt
    exact (hball hmem).2 (subset_closure (radialPoint_mem_carrier a hθ))
  apply (integrableOn_const (C := 2 / e ^ 2) hfinite).mono'
  · unfold diskGreen radialPoint
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    exact diskGreen_bound_on_ball_away he
        (show z ∈ Metric.ball z (e / 2) by simp [half_pos he]) (hsep θ hθ)
        (by simpa [unitDisk] using hzunit)
        (by simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one)

lemma integrable_diskGreen_logWeightedMeasure
    (a : CircularArc) (hfinite : volume a.angles ≠ ∞)
    {z : ℂ} (hzunit : z ∈ unitDisk) (hzaway : z ∉ closure a.carrier) :
    Integrable (fun ζ ↦ diskGreen z ζ) a.logWeightedMeasure := by
  have hparam := integrableOn_diskGreen_radial a hfinite hzunit hzaway
  have hradmeas : Measurable (fun θ ↦ radialPoint a.radius θ) := by
    unfold radialPoint
    fun_prop
  have hkmeas : AEStronglyMeasurable (fun ζ ↦ diskGreen z ζ)
      (Measure.map (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) := by
    unfold diskGreen
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hmapped : Integrable (fun ζ ↦ diskGreen z ζ)
      (Measure.map (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) :=
    (integrable_map_measure hkmeas hradmeas.aemeasurable).2 hparam
  rw [CircularArc.logWeightedMeasure]
  exact hmapped.smul_measure ENNReal.ofReal_ne_top

lemma greenPotentialReal_logMeasure_eq_sum_arcGreenPotential
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} (hzunit : z ∈ unitDisk) (hzaway : z ∉ closure A.carrier) :
    greenPotentialReal A.logMeasure z =
      ∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
        arcGreenPotential (A.arc i) z := by
  have hawayArc : ∀ i, z ∉ closure (A.arc i).carrier := by
    intro i hzi
    exact hzaway (closure_mono (arc_carrier_subset_disjoint_carrier A i) hzi)
  have hint : ∀ i, Integrable (fun ζ ↦ diskGreen z ζ) (A.arc i).logWeightedMeasure :=
    fun i ↦ integrable_diskGreen_logWeightedMeasure (A.arc i) (hfinite i) hzunit (hawayArc i)
  rw [greenPotentialReal, DisjointRadialArcs.logMeasure,
    MeasureTheory.integral_finsetSum_measure (fun i _ ↦ hint i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [CircularArc.logWeightedMeasure, MeasureTheory.integral_smul_measure]
  change (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
      (∫ ζ, diskGreen z ζ ∂Measure.map
        (fun θ ↦ radialPoint (A.arc i).radius θ) (volume.restrict (A.arc i).angles)) = _
  rw [MeasureTheory.integral_map]
  · rfl
  · unfold radialPoint
    fun_prop
  · unfold diskGreen
    exact Measurable.aestronglyMeasurable (by fun_prop)

lemma circleAverage_arcGreenPotential_eq
    (a : CircularArc) (hfinite : volume a.angles ≠ ∞)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ unitDisk \ closure a.carrier) :
    Real.circleAverage (arcGreenPotential a) c R = arcGreenPotential a c := by
  have hΩopen : IsOpen (unitDisk \ closure a.carrier) := by
    have : IsOpen unitDisk := by
      simpa [unitDisk] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
    exact this.sdiff isClosed_closure
  obtain ⟨e, he, hthick⟩ :=
    (isCompact_closedBall c R).exists_thickening_subset_open hΩopen hball
  have hsep : ∀ w ∈ Metric.closedBall c R, ∀ θ ∈ a.angles,
      e ≤ ‖w - radialPoint a.radius θ‖ := by
    intro w hw θ hθ
    by_contra hnot
    have hlt : dist (radialPoint a.radius θ) w < e := by
      simpa [dist_eq_norm, norm_sub_rev] using (lt_of_not_ge hnot)
    have hmem : radialPoint a.radius θ ∈ Metric.thickening e (Metric.closedBall c R) :=
      Metric.mem_thickening_iff.2 ⟨w, hw, hlt⟩
    exact (hthick hmem).2 (subset_closure (radialPoint_mem_carrier a hθ))
  have hprod : Integrable
      (Function.uncurry fun t θ ↦
        diskGreen (circleMap c R t) (radialPoint a.radius θ))
      ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict a.angles)) := by
    have hmeas : AEStronglyMeasurable
        (Function.uncurry fun t θ ↦
          diskGreen (circleMap c R t) (radialPoint a.radius θ))
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod
          (volume.restrict a.angles)) := by
      unfold diskGreen radialPoint circleMap
      exact Measurable.aestronglyMeasurable (by fun_prop)
    have hbound : ∀ᵐ p ∂((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod
          (volume.restrict a.angles)),
        ‖diskGreen (circleMap c R p.1) (radialPoint a.radius p.2)‖ ≤ 2 / e ^ 2 := by
      apply (Measure.ae_prod_iff_ae_ae (by
        exact measurableSet_le (by
          unfold diskGreen radialPoint circleMap
          fun_prop) measurable_const)).2
      filter_upwards [ae_restrict_mem
        (measurableSet_uIoc : MeasurableSet (Set.uIoc (0 : ℝ) (2 * Real.pi)))] with t ht
      filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
      have hwSphere : circleMap c R t ∈ Metric.sphere c R := by
        simpa [abs_of_pos hR] using circleMap_mem_sphere' c R t
      have hwClosed : circleMap c R t ∈ Metric.closedBall c R :=
        Metric.sphere_subset_closedBall hwSphere
      exact diskGreen_bound_on_ball_away he
        (Metric.mem_ball_self (half_pos he)) (hsep _ hwClosed _ hθ)
        (by simpa [unitDisk] using (hball hwClosed).1)
        (by simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one)
    have hfirst : volume (Set.uIoc (0 : ℝ) (2 * Real.pi)) ≠ ∞ := by
      simp only [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        Real.volume_Ioc, sub_zero, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    have hprodFinite :
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod
          (volume.restrict a.angles)) Set.univ ≠ ∞ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
        Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top hfirst hfinite
    let : IsFiniteMeasure
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod
          (volume.restrict a.angles)) :=
      ⟨lt_top_iff_ne_top.2 hprodFinite⟩
    exact (integrable_const (2 / e ^ 2)).mono' hmeas hbound
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ *
      (∫ t in (0 : ℝ)..2 * Real.pi,
        ∫ θ in a.angles, diskGreen (circleMap c R t) (radialPoint a.radius θ)) = _
  rw [MeasureTheory.intervalIntegral_integral_swap hprod]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
  change Real.circleAverage (fun w ↦ diskGreen w (radialPoint a.radius θ)) c R =
    diskGreen c (radialPoint a.radius θ)
  exact circleAverage_diskGreen_left hR
    (fun w hw ↦ (hball hw).1)
    (by simpa [unitDisk, norm_radialPoint a.radius_pos.le] using a.radius_lt_one)
    (fun hζ ↦ (hball hζ).2 (subset_closure (radialPoint_mem_carrier a hθ)))

lemma continuousOn_greenPotentialReal_logMeasure
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞) :
    ContinuousOn (greenPotentialReal A.logMeasure)
      (unitDisk \ closure A.carrier) := by
  intro z hz
  have hOpenUD : IsOpen unitDisk := by
    simpa [unitDisk] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
  have hΩopen : IsOpen (unitDisk \ closure A.carrier) := hOpenUD.sdiff isClosed_closure
  let rhs : ℂ → ℝ := fun w ↦
    ∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
      arcGreenPotential (A.arc i) w
  have hawayArc : ∀ i, z ∉ closure (A.arc i).carrier := by
    intro i hzi
    exact hz.2 (closure_mono (arc_carrier_subset_disjoint_carrier A i) hzi)
  have hrhs : ContinuousAt rhs z := by
    unfold rhs
    apply tendsto_finsetSum
    intro i hi
    exact continuousAt_const.mul
      (continuousAt_arcGreenPotential (A.arc i) (hfinite i) hz.1 (hawayArc i))
  have heq : greenPotentialReal A.logMeasure =ᶠ[𝓝 z] rhs := by
    filter_upwards [hΩopen.mem_nhds hz] with w hw
    exact greenPotentialReal_logMeasure_eq_sum_arcGreenPotential A hfinite hw.1 hw.2
  exact (hrhs.congr_of_eventuallyEq heq).continuousWithinAt

theorem greenPotentialReal_logMeasure_subharmonicOn
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞) :
    SubharmonicOn (greenPotentialReal A.logMeasure)
      (unitDisk \ closure A.carrier) := by
  have hOpenUD : IsOpen unitDisk := by
    simpa [unitDisk] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1))
  have hΩopen : IsOpen (unitDisk \ closure A.carrier) := hOpenUD.sdiff isClosed_closure
  refine ⟨hΩopen, continuousOn_greenPotentialReal_logMeasure A hfinite, ?_⟩
  intro c hc R hR hball
  let coeff : Fin A.n → ℝ := fun i ↦
    (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal
  let rhs : ℂ → ℝ := fun w ↦ ∑ i, coeff i * arcGreenPotential (A.arc i) w
  have heq : Set.EqOn (greenPotentialReal A.logMeasure) rhs
      (unitDisk \ closure A.carrier) := by
    intro w hw
    exact greenPotentialReal_logMeasure_eq_sum_arcGreenPotential A hfinite hw.1 hw.2
  have hsphere : Metric.sphere c R ⊆ unitDisk \ closure A.carrier :=
    Metric.sphere_subset_closedBall.trans hball
  have hci : ∀ i, CircleIntegrable
      (fun w ↦ coeff i * arcGreenPotential (A.arc i) w) c R := by
    intro i
    have hcont : ContinuousOn (arcGreenPotential (A.arc i)) (Metric.sphere c R) := by
      intro w hw
      apply (continuousAt_arcGreenPotential (A.arc i) (hfinite i)
        (hsphere hw).1 ?_).continuousWithinAt
      intro hwa
      exact (hsphere hw).2
        (closure_mono (arc_carrier_subset_disjoint_carrier A i) hwa)
    exact (continuousOn_const.mul hcont).circleIntegrable hR.le
  calc
    greenPotentialReal A.logMeasure c = rhs c := heq hc
    _ = ∑ i, coeff i * arcGreenPotential (A.arc i) c := rfl
    _ = ∑ i, coeff i *
        Real.circleAverage (arcGreenPotential (A.arc i)) c R := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [circleAverage_arcGreenPotential_eq (A.arc i) (hfinite i) hR]
      intro w hw
      have hwA := hball hw
      exact ⟨hwA.1, fun hwa ↦ hwA.2
        (closure_mono (arc_carrier_subset_disjoint_carrier A i) hwa)⟩
    _ = ∑ i, Real.circleAverage
        (fun w ↦ coeff i * arcGreenPotential (A.arc i) w) c R := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := coeff i)
          (f := arcGreenPotential (A.arc i)) (c := c) (R := R)).symm
    _ = Real.circleAverage rhs c R := by
      rw [Real.circleAverage_fun_sum (s := Finset.univ) (fun i _ ↦ hci i)]
    _ ≤ Real.circleAverage (greenPotentialReal A.logMeasure) c R := by
      apply le_of_eq
      apply Real.circleAverage_congr_sphere
      intro w hw
      exact (heq (hsphere (by simpa [abs_of_pos hR] using hw))).symm

lemma diskGreen_norm_le_boundary_rate {z ζ : ℂ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hζρ : ‖ζ‖ ≤ ρ) (hρz : ρ < ‖z‖) (hz1 : ‖z‖ < 1)
    (hζ1 : ‖ζ‖ < 1) :
    ‖diskGreen z ζ‖ ≤ (1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2) := by
  have hne : z ≠ ζ := by
    intro h
    subst ζ
    linarith
  have hnonneg := diskGreen_nonneg hz1 hζ1 hne
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  refine (diskGreen_le_greenQuotient hz1 hζ1 hne).trans ?_
  have hzfac : 0 ≤ 1 - ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith)
      (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hζfac : 0 ≤ 1 - ‖ζ‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖ζ‖ by linarith)
      (show 0 ≤ 1 + ‖ζ‖ by positivity)]
  have hζfac_le : 1 - ‖ζ‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖ζ‖]
  have hdist : ‖z‖ - ρ ≤ ‖z - ζ‖ := by
    have htri : ‖z‖ ≤ ‖z - ζ‖ + ‖ζ‖ := by
      calc
        ‖z‖ = ‖(z - ζ) + ζ‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hgap : 0 < ‖z‖ - ρ := sub_pos.mpr hρz
  have hden : 0 < 2 * ‖z - ζ‖ ^ 2 := by
    have : 0 < ‖z - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    positivity
  have hrden : 0 < 2 * (‖z‖ - ρ) ^ 2 := by positivity
  calc
    ((1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) / (2 * ‖z - ζ‖ ^ 2)
        ≤ (1 - ‖z‖ ^ 2) / (2 * ‖z - ζ‖ ^ 2) := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa using mul_le_mul_of_nonneg_left hζfac_le hzfac
    _ ≤ (1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2) := by
      exact div_le_div_of_nonneg_left hzfac
        (by positivity) (by nlinarith [sq_le_sq₀ hgap.le (norm_nonneg (z - ζ)) |>.2 hdist])

lemma abs_arcGreenPotential_le_boundary_rate
    (a : CircularArc) (hfinite : volume a.angles ≠ ∞) {z : ℂ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (har : a.radius ≤ ρ) (hρz : ρ < ‖z‖) (hz1 : ‖z‖ < 1) :
    |arcGreenPotential a z| ≤
      ((1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2)) * (volume a.angles).toReal := by
  let μ : Measure ℝ := volume.restrict a.angles
  have hμfinite : μ Set.univ ≠ ∞ := by
    simpa [μ, Measure.restrict_apply_univ] using hfinite
  let : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hμfinite⟩
  rw [arcGreenPotential, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const
    (C := (1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2)) ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    exact diskGreen_norm_le_boundary_rate hρ0
      (by simpa [norm_radialPoint a.radius_pos.le] using har) hρz hz1
      (by simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one)
  · rw [measureReal_def]
    simp [μ, Measure.restrict_apply_univ, hfinite]

noncomputable def logMeasureMass (A : DisjointRadialArcs) : ℝ :=
  ∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
    (volume (A.arc i).angles).toReal

lemma logMeasureMass_nonneg (A : DisjointRadialArcs) : 0 ≤ logMeasureMass A := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma closure_carrier_subset_closedBall_of_radius_le
    (A : DisjointRadialArcs) {ρ : ℝ} (hr : ∀ i, (A.arc i).radius ≤ ρ) :
    closure A.carrier ⊆ Metric.closedBall 0 ρ := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  simp only [DisjointRadialArcs.carrier, Set.mem_iUnion] at hz
  obtain ⟨i, θ, hθ, rfl⟩ := hz
  simpa [Metric.mem_closedBall, norm_radialPoint (A.arc i).radius_pos.le] using hr i

lemma abs_greenPotentialReal_logMeasure_le_boundary_rate
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr : ∀ i, (A.arc i).radius ≤ ρ) (hρz : ρ < ‖z‖) (hz1 : ‖z‖ < 1) :
    |greenPotentialReal A.logMeasure z| ≤
      ((1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2)) * logMeasureMass A := by
  have hzunit : z ∈ unitDisk := by simpa [unitDisk] using hz1
  have hzaway : z ∉ closure A.carrier := by
    intro hz
    have hzball := closure_carrier_subset_closedBall_of_radius_le A hr hz
    have : ‖z‖ ≤ ρ := by simpa [Metric.mem_closedBall] using hzball
    linarith
  rw [greenPotentialReal_logMeasure_eq_sum_arcGreenPotential A hfinite hzunit hzaway]
  let rate : ℝ := (1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2)
  have hrate : 0 ≤ rate := by
    unfold rate
    exact div_nonneg (by
      nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith)
        (show 0 ≤ 1 + ‖z‖ by positivity)]) (by positivity)
  calc
    |∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
        arcGreenPotential (A.arc i) z| ≤
        ∑ i, |(ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
          arcGreenPotential (A.arc i) z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
          |arcGreenPotential (A.arc i) z| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ ∑ i, (ENNReal.ofReal (1 / Real.log (1 / (A.arc i).radius))).toReal *
          (rate * (volume (A.arc i).angles).toReal) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (abs_arcGreenPotential_le_boundary_rate (A.arc i) (hfinite i)
          hρ0 (hr i) hρz hz1) ENNReal.toReal_nonneg
    _ = rate * logMeasureMass A := by
      rw [logMeasureMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma abs_greenPotentialReal_logMeasure_le_boundary_linear
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr : ∀ i, (A.arc i).radius ≤ ρ)
    (hmid : (1 + ρ) / 2 < ‖z‖) (hz1 : ‖z‖ < 1) :
    |greenPotentialReal A.logMeasure z| ≤
      (2 * (1 - ‖z‖ ^ 2) / (1 - ρ) ^ 2) * logMeasureMass A := by
  have hρz : ρ < ‖z‖ := by linarith
  refine (abs_greenPotentialReal_logMeasure_le_boundary_rate
    A hfinite hρ0 hρ1 hr hρz hz1).trans ?_
  have hnum : 0 ≤ 1 - ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith)
      (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hgap : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hxgap : (1 - ρ) / 2 < ‖z‖ - ρ := by linarith
  have hden : (1 - ρ) ^ 2 / 2 ≤ 2 * (‖z‖ - ρ) ^ 2 := by
    nlinarith [sq_le_sq₀ (by positivity : 0 ≤ (1 - ρ) / 2)
      (by linarith : 0 ≤ ‖z‖ - ρ) |>.2 hxgap.le]
  have hmass := logMeasureMass_nonneg A
  apply mul_le_mul_of_nonneg_right _ hmass
  calc
    (1 - ‖z‖ ^ 2) / (2 * (‖z‖ - ρ) ^ 2) ≤
        (1 - ‖z‖ ^ 2) / ((1 - ρ) ^ 2 / 2) := by
      exact div_le_div_of_nonneg_left hnum (by positivity) hden
    _ = 2 * (1 - ‖z‖ ^ 2) / (1 - ρ) ^ 2 := by
      field_simp
      <;> ring

theorem greenPotentialReal_logMeasure_tends_uniformly_zero_of_radius_le
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr : ∀ i, (A.arc i).radius ≤ ρ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ < 1 → 1 - δ < ‖z‖ →
        |greenPotentialReal A.logMeasure z| < ε := by
  intro ε hε
  let gap : ℝ := 1 - ρ
  let M : ℝ := logMeasureMass A
  let C : ℝ := 4 * M / gap ^ 2
  have hgap : 0 < gap := by simpa [gap] using sub_pos.mpr hρ1
  have hM : 0 ≤ M := logMeasureMass_nonneg A
  have hC : 0 ≤ C := by
    unfold C
    positivity
  let δ : ℝ := min (gap / 2) (ε / (C + 1))
  have hδ : 0 < δ := by
    simp only [δ, lt_min_iff]
    exact ⟨half_pos hgap, div_pos hε (by linarith)⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz1 hzδ
  have hmid : (1 + ρ) / 2 < ‖z‖ := by
    have hδgap : δ ≤ gap / 2 := min_le_left _ _
    dsimp [gap] at hδgap
    linarith
  have hbound := abs_greenPotentialReal_logMeasure_le_boundary_linear
    A hfinite hρ0 hρ1 hr hmid hz1
  have hnum : 1 - ‖z‖ ^ 2 < 2 * δ := by
    have hx0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hleft : 0 < 1 - ‖z‖ := by linarith
    calc
      1 - ‖z‖ ^ 2 = (1 - ‖z‖) * (1 + ‖z‖) := by ring
      _ < (1 - ‖z‖) * 2 :=
        mul_lt_mul_of_pos_left (by linarith) hleft
      _ < δ * 2 := mul_lt_mul_of_pos_right (by linarith) (by norm_num)
      _ = 2 * δ := by ring
  have hlinear :
      (2 * (1 - ‖z‖ ^ 2) / (1 - ρ) ^ 2) * logMeasureMass A ≤ C * δ := by
    dsimp [C, M, gap]
    have hgapSq : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (sub_pos.mpr hρ1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [mul_nonneg hM (inv_nonneg.mpr hgapSq.le)]
  have hδeps : δ ≤ ε / (C + 1) := min_le_right _ _
  have hCeps : C * δ < ε := by
    calc
      C * δ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hδeps hC
      _ = ε * C / (C + 1) := by ring
      _ < ε := by
        rw [div_lt_iff₀ (by linarith : 0 < C + 1)]
        nlinarith
  exact lt_of_le_of_lt (hbound.trans hlinear) hCeps


end Erdos515

namespace Erdos515

lemma integrable_diskGreen_logMeasure
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) :
    Integrable (fun ζ ↦ diskGreen z ζ) A.logMeasure := by
  rw [DisjointRadialArcs.logMeasure]
  apply integrable_finsetSum_measure.2
  intro i hi
  exact integrable_diskGreen_logWeightedMeasure (A.arc i) (hfinite i) hz.1
    (fun hzi ↦ hz.2 (closure_mono (arc_carrier_subset_disjoint_carrier A i) hzi))

lemma ae_diskGreen_nonneg_logWeightedMeasure
    (a : CircularArc) {z : ℂ} (hzunit : z ∈ unitDisk)
    (hzaway : z ∉ closure a.carrier) :
    ∀ᵐ ζ ∂a.logWeightedMeasure, 0 ≤ diskGreen z ζ := by
  rw [CircularArc.logWeightedMeasure]
  apply Measure.ae_smul_measure
  have hradmeas : Measurable (fun θ ↦ radialPoint a.radius θ) := by
    unfold radialPoint
    fun_prop
  rw [ae_map_iff hradmeas.aemeasurable]
  · filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    apply diskGreen_nonneg
    · simpa [unitDisk] using hzunit
    · simpa [norm_radialPoint a.radius_pos.le] using a.radius_lt_one
    · intro h
      exact hzaway (subset_closure (h ▸ radialPoint_mem_carrier a hθ))
  · exact measurableSet_le measurable_const (by
      unfold diskGreen
      fun_prop)

lemma ae_diskGreen_nonneg_logMeasure
    (A : DisjointRadialArcs) {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) :
    ∀ᵐ ζ ∂A.logMeasure, 0 ≤ diskGreen z ζ := by
  rw [DisjointRadialArcs.logMeasure, ae_finsetSum_measure_iff]
  intro i hi
  exact ae_diskGreen_nonneg_logWeightedMeasure (A.arc i) hz.1
    (fun hzi ↦ hz.2 (closure_mono (arc_carrier_subset_disjoint_carrier A i) hzi))

lemma ae_diskGreenENNReal_eq_ofReal_logWeightedMeasure
    (a : CircularArc) {z : ℂ} (hzaway : z ∉ closure a.carrier) :
    ∀ᵐ ζ ∂a.logWeightedMeasure,
      diskGreenENNReal z ζ = ENNReal.ofReal (diskGreen z ζ) := by
  rw [CircularArc.logWeightedMeasure]
  apply Measure.ae_smul_measure
  have hradmeas : Measurable (fun θ ↦ radialPoint a.radius θ) := by
    unfold radialPoint
    fun_prop
  rw [ae_map_iff hradmeas.aemeasurable]
  · filter_upwards [ae_restrict_mem a.measurableSet_angles] with θ hθ
    exact diskGreenENNReal_of_ne fun h ↦
      hzaway (subset_closure (h ▸ radialPoint_mem_carrier a hθ))
  · apply measurableSet_eq_fun
    · unfold diskGreenENNReal diskGreen
      apply Measurable.ite
      · exact measurableSet_eq_fun measurable_const measurable_id
      · exact measurable_const
      · fun_prop
    · unfold diskGreen
      fun_prop

lemma ae_diskGreenENNReal_eq_ofReal_logMeasure
    (A : DisjointRadialArcs) {z : ℂ} (hzaway : z ∉ closure A.carrier) :
    ∀ᵐ ζ ∂A.logMeasure,
      diskGreenENNReal z ζ = ENNReal.ofReal (diskGreen z ζ) := by
  rw [DisjointRadialArcs.logMeasure, ae_finsetSum_measure_iff]
  intro i hi
  exact ae_diskGreenENNReal_eq_ofReal_logWeightedMeasure (A.arc i)
    (fun hzi ↦ hzaway (closure_mono (arc_carrier_subset_disjoint_carrier A i) hzi))

theorem ofReal_greenPotentialReal_logMeasure_eq_greenPotential
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) :
    ENNReal.ofReal (greenPotentialReal A.logMeasure z) =
      greenPotential A.logMeasure z := by
  rw [greenPotentialReal, greenPotential,
    ofReal_integral_eq_lintegral_ofReal
      (integrable_diskGreen_logMeasure A hfinite hz)
      (ae_diskGreen_nonneg_logMeasure A hz)]
  exact lintegral_congr_ae
    ((ae_diskGreenENNReal_eq_ofReal_logMeasure A hz.2).mono fun ζ hζ ↦ hζ.symm)

lemma greenPotentialReal_logMeasure_nonneg
    (A : DisjointRadialArcs) {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) :
    0 ≤ greenPotentialReal A.logMeasure z := by
  rw [greenPotentialReal]
  exact integral_nonneg_of_ae (ae_diskGreen_nonneg_logMeasure A hz)

lemma greenPotentialReal_logMeasure_le_of_greenPotential_le_ofReal
    (A : DisjointRadialArcs) (hfinite : ∀ i, volume (A.arc i).angles ≠ ∞)
    {z : ℂ} (hz : z ∈ unitDisk \ closure A.carrier) {B : ℝ} (hB : 0 ≤ B)
    (hpot : greenPotential A.logMeasure z ≤ ENNReal.ofReal B) :
    greenPotentialReal A.logMeasure z ≤ B := by
  rw [← ofReal_greenPotentialReal_logMeasure_eq_greenPotential A hfinite hz] at hpot
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hpot

end Erdos515
