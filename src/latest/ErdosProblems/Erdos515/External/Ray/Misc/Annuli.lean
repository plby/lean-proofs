module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Misc.Connected

/-!
## Finite and infinite annuli
-/

open MeasureTheory (volume)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open scoped Real Topology
noncomputable section

/-- The region strictly outside radius `r` -/
@[expose] public def norm_Ioi (r : ℝ) : Set ℂ := {w : ℂ | r < ‖w‖}

/-- The region weakly outside radius `r` -/
@[expose] public def norm_Ici (r : ℝ) : Set ℂ := {w : ℂ | r ≤ ‖w‖}

/-- A closed annulus around the origin -/
@[expose] public def norm_Icc (r s : ℝ) : Set ℂ := Norm.norm ⁻¹' Icc r s

/-- An open annulus around the origin -/
@[expose] public def norm_Ioo (r s : ℝ) : Set ℂ := Norm.norm ⁻¹' Ioo r s

/-- A half-open annulus around `c` -/
@[expose] public def annulus_oc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ closedBall c r0

/-- A closed annulus around `c` -/
@[expose] public def annulus_cc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ ball c r0

public lemma isOpen_norm_Ioi {r : ℝ} : IsOpen (norm_Ioi r) := by
  simp only [norm_Ioi]; exact isOpen_Ioi.preimage continuous_norm

public lemma isOpen_norm_Ioo {r s : ℝ} : IsOpen (norm_Ioo r s) := by
  simp only [norm_Ioo]; exact isOpen_Ioo.preimage continuous_norm

public lemma isClosed_norm_Ici {r : ℝ} : IsClosed (norm_Ici r) := by
  simp only [norm_Ici]; exact isClosed_Ici.preimage continuous_norm

public lemma norm_Icc_eq_diff {r s : ℝ} : norm_Icc r s = closedBall 0 s \ ball 0 r := by
  ext z
  simp only [norm_Icc, mem_preimage, mem_Icc, mem_sdiff, Metric.mem_closedBall, dist_zero_right,
    Metric.mem_ball, not_lt, and_comm]

@[simp] public lemma norm_Ici_diff_norm_Ioi {r : ℝ} : norm_Ici r \ norm_Ioi r = sphere 0 r := by
  ext z
  simp only [norm_Ici, norm_Ioi, mem_sdiff, mem_ofPred_eq, not_lt, ← le_antisymm_iff,
    mem_sphere_iff_norm, sub_zero, eq_comm]

public lemma isCompact_norm_Icc {r s : ℝ} : IsCompact (norm_Icc r s) := by
  rw [norm_Icc_eq_diff]; exact (isCompact_closedBall _ _).diff isOpen_ball

public lemma isCompact_annulus_cc {c : ℂ} {r s : ℝ} : IsCompact (annulus_cc c r s) := by
  exact (isCompact_closedBall _ _).diff isOpen_ball

public lemma norm_Ioi_subset_norm_Ici {r : ℝ} : norm_Ioi r ⊆ norm_Ici r := by
  simp only [norm_Ioi, norm_Ici, ofPred_subset_ofPred]; intro _; exact le_of_lt

public lemma norm_Icc_subset_norm_Ici {r s : ℝ} : norm_Icc r s ⊆ norm_Ici r := by
  simp only [norm_Icc, norm_Ici, preimage_subset_iff, mem_Icc, mem_ofPred_eq, and_imp]
  intro _ h _; exact h

public lemma norm_Ici_mono {r s : ℝ} (rs : r ≤ s) : norm_Ici s ⊆ norm_Ici r := by
  simp only [norm_Ici, ofPred_subset_ofPred]; intro _ h; linarith

@[simp] public lemma norm_Ici_eq_univ {r : ℝ} (r0 : r ≤ 0) : norm_Ici r = univ := by
  ext z
  simp only [norm_Ici, mem_ofPred_eq, mem_univ, iff_true]
  exact le_trans r0 (by bound)

public lemma isPathConnected_norm_Ici {r : ℝ} : IsPathConnected (norm_Ici r) := by
  cases' lt_or_ge r 0 with r0 r0
  · simp only [norm_Ici_eq_univ r0.le, isPathConnected_univ]
  simp only [norm_Ici, ← Set.preimage_ofPred_eq, Ici_def]
  refine IsPathConnected.of_frontier ?_ continuous_norm isClosed_Ici
  simp only [nonempty_Iio, frontier_Ici']
  convert Complex.isPathConnected_sphere (z := 0) r0
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_sphere_iff_norm, sub_zero]

public lemma isPreconnected_norm_Ioi {r : ℝ} : IsPreconnected (norm_Ioi r) := by
  set f : ℝᵒᵈ → Set ℂ := fun s ↦ norm_Ici (OrderDual.ofDual s)
  have e : norm_Ioi r = ⋃₀ (f '' Iio (OrderDual.toDual r)) := by
    ext z
    simp only [norm_Ioi, mem_ofPred_eq, norm_Ici, Iio_toDual, sUnion_image, mem_preimage, mem_Ioi,
      mem_iUnion, exists_prop, OrderDual.exists, OrderDual.ofDual_toDual, f]
    constructor
    · intro rz; exact ⟨‖z‖, rz, le_refl _⟩
    · intro ⟨s,rs,sz⟩; exact lt_of_lt_of_le rs sz
  rw [e]
  apply IsPreconnected.sUnion_directed
  · simp only [DirectedOn, Iio_toDual, mem_image, mem_preimage, mem_Ioi, OrderDual.exists,
      OrderDual.ofDual_toDual, exists_exists_and_eq_and, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a ar b br
    exact ⟨min a b, by bound, norm_Ici_mono (by bound), norm_Ici_mono (by bound)⟩
  · simp only [Iio_toDual, mem_image, mem_preimage, mem_Ioi, OrderDual.exists, f,
      OrderDual.ofDual_toDual, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      isPathConnected_norm_Ici.isConnected.isPreconnected, implies_true]

public lemma compl_norm_Ioi {r : ℝ} : (norm_Ioi r)ᶜ = closedBall 0 r := by
  ext z
  simp [norm_Ioi]

@[simp] public lemma frontier_norm_Ioi {r : ℝ} : frontier (norm_Ioi r) = sphere 0 r := by
  rw [← frontier_compl, compl_norm_Ioi, frontier_closedBall']

@[simp] public lemma closure_norm_Ioi {r : ℝ} : closure (norm_Ioi r) = norm_Ici r := by
  simp only [closure_eq_interior_union_frontier, frontier_norm_Ioi, isOpen_norm_Ioi.interior_eq]
  ext z
  simp [norm_Ioi, norm_Ici, eq_comm (b := r), le_iff_lt_or_eq]

@[simp] public lemma norm_Ioi_subset_norm_Ioi {r s : ℝ} (sr : s ≤ r) : norm_Ioi r ⊆ norm_Ioi s := by
  intro z m
  simp only [mem_ofPred_eq, norm_Ioi] at m ⊢
  order

@[simp] public lemma norm_Ici_subset_norm_Ioi {r s : ℝ} (sr : s < r) : norm_Ici r ⊆ norm_Ioi s := by
  intro z m
  simp only [norm_Ici, mem_ofPred_eq, norm_Ioi] at m ⊢
  order

public lemma annulus_oc_subset_annulus_cc {c : ℂ} {r0 r1 : ℝ} :
    annulus_oc c r0 r1 ⊆ annulus_cc c r0 r1 :=
  sdiff_subset_sdiff (subset_refl _) Metric.ball_subset_closedBall

public lemma measurableSet_annulus_oc {c : ℂ} {r0 r1 : ℝ} :
    MeasurableSet (annulus_oc c r0 r1) :=
  measurableSet_closedBall.diff measurableSet_closedBall

public lemma measurableSet_annulus_cc {c : ℂ} {r0 r1 : ℝ} :
    MeasurableSet (annulus_cc c r0 r1) :=
  measurableSet_closedBall.diff measurableSet_ball

@[simp, aesop (rule_sets := [finiteness]) safe apply] public lemma finite_measure_annulus_cc {c : ℂ}
    {r0 r1 : ℝ} : volume (annulus_cc c r0 r1) ≠ ⊤ := isCompact_annulus_cc.measure_ne_top

public lemma annulus_oc_subset_norm_Ioi {a r s : ℝ} (ar : a ≤ r) : annulus_oc 0 r s ⊆ norm_Ioi a := by
  intro z m
  simp only [annulus_oc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, not_le, norm_Ioi,
    mem_ofPred_eq] at m ⊢
  exact lt_of_le_of_lt ar m.2

public lemma annulus_cc_subset_norm_Ioi {a r s : ℝ} (ar : a < r) :
    annulus_cc 0 r s ⊆ norm_Ioi a := by
  intro z m
  simp only [annulus_cc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball, not_lt,
    norm_Ioi, mem_ofPred_eq] at m ⊢
  exact lt_of_lt_of_le ar m.2

public lemma symmDiff_annulus_oc_annulus_cc {c : ℂ} {r s : ℝ} (rs : r ≤ s) :
    (symmDiff (annulus_oc c r s) (annulus_cc c r s)) = sphere c r := by
  ext z
  simp only [annulus_oc, annulus_cc, mem_symmDiff, mem_sdiff, Metric.mem_closedBall, dist_eq_norm,
    not_le, Metric.mem_ball, not_lt, not_and, mem_sphere_iff_norm]
  -- `grind` used to close the goal at this point, but doesn't anymore due to a bug
  constructor
  · intro h
    rcases h with h | ⟨⟨zs,rz⟩,zr⟩
    · grind
    · linarith [zr zs]
  · intro e
    simp [e, rs]
