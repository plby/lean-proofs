/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Subharmonic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Nested sublevel domains for the Lewis--Rossi--Weitsman construction

This file isolates the elementary topology of the domains obtained by taking the connected
component, through a fixed base point, of a strict sublevel set of a continuous function on the
complex plane.  These are the domains used in the recursive construction for Erdős Problem 515.

The statements below do not use an extended-real convention: the function is finite and
continuous.  In particular, sublevel components are open, path connected, monotone in the level,
have boundary on the prescribed level, and exhaust the plane as the levels tend to infinity.
-/

open Filter Metric Set Topology

namespace Erdos515

/-- The strict sublevel set of a real-valued function. -/
def strictSublevel (u : ℂ → ℝ) (c : ℝ) : Set ℂ :=
  {z | u z < c}

/-- The connected component through `a` of a strict sublevel set. -/
noncomputable def sublevelComponent (u : ℂ → ℝ) (c : ℝ) (a : ℂ) : Set ℂ :=
  connectedComponentIn (strictSublevel u c) a

@[simp] lemma mem_strictSublevel {u : ℂ → ℝ} {c : ℝ} {z : ℂ} :
    z ∈ strictSublevel u c ↔ u z < c :=
  Iff.rfl

lemma isOpen_strictSublevel {u : ℂ → ℝ} (hu : Continuous u) (c : ℝ) :
    IsOpen (strictSublevel u c) := by
  exact isOpen_lt hu continuous_const

lemma sublevelComponent_subset (u : ℂ → ℝ) (c : ℝ) (a : ℂ) :
    sublevelComponent u c a ⊆ strictSublevel u c :=
  connectedComponentIn_subset _ _

lemma mem_sublevelComponent_self {u : ℂ → ℝ} {c : ℝ} {a : ℂ}
    (ha : u a < c) :
    a ∈ sublevelComponent u c a :=
  mem_connectedComponentIn ha

@[simp] lemma sublevelComponent_nonempty_iff {u : ℂ → ℝ} {c : ℝ} {a : ℂ} :
    (sublevelComponent u c a).Nonempty ↔ u a < c :=
  connectedComponentIn_nonempty_iff

lemma isOpen_sublevelComponent {u : ℂ → ℝ} (hu : Continuous u) (c : ℝ) (a : ℂ) :
    IsOpen (sublevelComponent u c a) :=
  (isOpen_strictSublevel hu c).connectedComponentIn

lemma isPreconnected_sublevelComponent (u : ℂ → ℝ) (c : ℝ) (a : ℂ) :
    IsPreconnected (sublevelComponent u c a) :=
  isPreconnected_connectedComponentIn

lemma isConnected_sublevelComponent {u : ℂ → ℝ} {c : ℝ} {a : ℂ}
    (ha : u a < c) :
    IsConnected (sublevelComponent u c a) :=
  isConnected_connectedComponentIn_iff.mpr ha

lemma isPathConnected_sublevelComponent {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℝ} {a : ℂ} (ha : u a < c) :
    IsPathConnected (sublevelComponent u c a) := by
  rw [← (isOpen_sublevelComponent hu c a).isConnected_iff_isPathConnected]
  exact isConnected_sublevelComponent ha

/-- Components through a common base point are nested as the sublevel increases. -/
lemma sublevelComponent_mono {u : ℂ → ℝ} {c d : ℝ} (a : ℂ) (hcd : c ≤ d) :
    sublevelComponent u c a ⊆ sublevelComponent u d a := by
  apply connectedComponentIn_mono a
  intro z hz
  exact lt_of_lt_of_le hz hcd

/-- Membership identifies the same connected component with the member as its base point. -/
lemma sublevelComponent_eq_of_mem {u : ℂ → ℝ} {c : ℝ} {a z : ℂ}
    (hz : z ∈ sublevelComponent u c a) :
    sublevelComponent u c a = sublevelComponent u c z :=
  connectedComponentIn_eq hz

/-- The closure of a strict-sublevel component lies in the corresponding closed sublevel. -/
lemma closure_sublevelComponent_subset_closedSublevel {u : ℂ → ℝ} (hu : Continuous u)
    (c : ℝ) (a : ℂ) :
    closure (sublevelComponent u c a) ⊆ {z | u z ≤ c} := by
  apply closure_minimal
  · intro z hz
    have hz' := sublevelComponent_subset u c a hz
    change u z < c at hz'
    exact hz'.le
  · exact isClosed_le hu continuous_const

/-- A point of the strict sublevel which lies in the closure of a component already belongs to
that component.  Equivalently, a connected component of an open set is closed relative to that
open set. -/
lemma mem_sublevelComponent_of_mem_closure_of_lt {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℝ} {a z : ℂ} (hzClosure : z ∈ closure (sublevelComponent u c a))
    (hzSub : u z < c) :
    z ∈ sublevelComponent u c a := by
  let D := sublevelComponent u c a
  let C := sublevelComponent u c z
  have hCopen : IsOpen C := isOpen_sublevelComponent hu c z
  have hzC : z ∈ C := mem_sublevelComponent_self hzSub
  obtain ⟨y, hyC, hyD⟩ :=
    (mem_closure_iff_nhds.mp hzClosure C (hCopen.mem_nhds hzC))
  have hDC : D = C :=
    (sublevelComponent_eq_of_mem hyD).trans (sublevelComponent_eq_of_mem hyC).symm
  change z ∈ D
  exact hDC.symm ▸ hzC

/-- With a strict increase of levels, the closure of the lower component is contained in the
higher component.  This is stronger than ordinary nesting and is the key fact ensuring that all
of the old boundary is available at the next recursive stage. -/
lemma closure_sublevelComponent_subset_of_lt {u : ℂ → ℝ} (hu : Continuous u)
    {c d : ℝ} {a : ℂ} (ha : u a < c) (hcd : c < d) :
    closure (sublevelComponent u c a) ⊆ sublevelComponent u d a := by
  apply (isPreconnected_sublevelComponent u c a).closure.subset_connectedComponentIn
    (subset_closure (mem_sublevelComponent_self ha))
  intro z hz
  change u z < d
  exact lt_of_le_of_lt (closure_sublevelComponent_subset_closedSublevel hu c a hz) hcd

lemma frontier_sublevelComponent_subset_of_lt {u : ℂ → ℝ} (hu : Continuous u)
    {c d : ℝ} {a : ℂ} (ha : u a < c) (hcd : c < d) :
    frontier (sublevelComponent u c a) ⊆ sublevelComponent u d a :=
  frontier_subset_closure.trans (closure_sublevelComponent_subset_of_lt hu ha hcd)

/-- A frontier point of a sublevel component cannot still lie in the strict sublevel.  Indeed,
the component through that frontier point is an open neighborhood which meets the original
component, so the two components coincide; this contradicts openness of the original component.
-/
lemma not_mem_strictSublevel_of_mem_frontier_sublevelComponent {u : ℂ → ℝ}
    (hu : Continuous u) {c : ℝ} {a z : ℂ}
    (hz : z ∈ frontier (sublevelComponent u c a)) :
    z ∉ strictSublevel u c := by
  intro hzSub
  let D := sublevelComponent u c a
  let C := sublevelComponent u c z
  have hDopen : IsOpen D := isOpen_sublevelComponent hu c a
  have hCopen : IsOpen C := isOpen_sublevelComponent hu c z
  have hzC : z ∈ C := mem_sublevelComponent_self hzSub
  have hzClosure : z ∈ closure D := frontier_subset_closure hz
  obtain ⟨y, hyC, hyD⟩ :=
    (mem_closure_iff_nhds.mp hzClosure C (hCopen.mem_nhds hzC))
  have hDC : D = C :=
    (sublevelComponent_eq_of_mem hyD).trans (sublevelComponent_eq_of_mem hyC).symm
  have hzD : z ∈ D := hDC.symm ▸ hzC
  have hzBoth : z ∈ D ∩ frontier D := ⟨hzD, hz⟩
  rw [hDopen.inter_frontier_eq] at hzBoth
  exact hzBoth

/-- Every frontier point of a nonempty strict-sublevel component lies on the exact level.  This
is the boundary-level fact used when one recursively passes from one LRW domain to the next. -/
lemma eq_level_of_mem_frontier_sublevelComponent {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℝ} {a z : ℂ} (hz : z ∈ frontier (sublevelComponent u c a)) :
    u z = c := by
  apply le_antisymm
  · exact closure_sublevelComponent_subset_closedSublevel hu c a (frontier_subset_closure hz)
  · exact le_of_not_gt (not_mem_strictSublevel_of_mem_frontier_sublevelComponent hu hz)

/-- Setwise form of the exact boundary-level theorem. -/
lemma frontier_sublevelComponent_subset_levelSet {u : ℂ → ℝ} (hu : Continuous u)
    (c : ℝ) (a : ℂ) :
    frontier (sublevelComponent u c a) ⊆ {z | u z = c} :=
  fun _ hz ↦ eq_level_of_mem_frontier_sublevelComponent hu hz

/-- A proper, nonempty component has a frontier point, necessarily at the exact level. -/
lemma exists_boundary_point_at_level {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℝ} {a : ℂ} (ha : u a < c) (hproper : sublevelComponent u c a ≠ univ) :
    ∃ z, z ∈ frontier (sublevelComponent u c a) ∧ u z = c := by
  have hfront : (frontier (sublevelComponent u c a)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨a, mem_sublevelComponent_self ha⟩, hproper⟩
  obtain ⟨z, hz⟩ := hfront
  exact ⟨z, hz, eq_level_of_mem_frontier_sublevelComponent hu hz⟩

/-- A point at or above the level witnesses that the corresponding component is proper. -/
lemma sublevelComponent_ne_univ_of_le_value {u : ℂ → ℝ} {c : ℝ} {a z : ℂ}
    (hz : c ≤ u z) :
    sublevelComponent u c a ≠ univ := by
  intro hD
  have hzD : z ∈ sublevelComponent u c a := hD.symm ▸ mem_univ z
  have hzSub := sublevelComponent_subset u c a hzD
  change u z < c at hzSub
  exact (not_lt_of_ge hz) hzSub

/-- If the base lies below the level and the function reaches the level somewhere, there is a
boundary point at exactly that level. -/
lemma exists_boundary_point_at_level_of_le_value {u : ℂ → ℝ} (hu : Continuous u)
    {c : ℝ} {a z : ℂ} (ha : u a < c) (hz : c ≤ u z) :
    ∃ w, w ∈ frontier (sublevelComponent u c a) ∧ u w = c :=
  exists_boundary_point_at_level hu ha (sublevelComponent_ne_univ_of_le_value hz)

/-- A bounded lower component has compact closure. -/
lemma isCompact_closure_sublevelComponent {u : ℂ → ℝ} {c : ℝ} {a : ℂ}
    (hbounded : Bornology.IsBounded (sublevelComponent u c a)) :
    IsCompact (closure (sublevelComponent u c a)) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbounded.closure⟩

/-!
## The exact maximum-principle interface for Jordan interiors

This formulation is independent of a particular encoding of Jordan curves.  A Jordan interior is
a bounded open preconnected set, and its frontier is the Jordan curve.  Thus the filling theorem
below is exactly the analytic/topological step in the classical argument once a bounded-domain
maximum principle is available.
-/

/-- The weak maximum principle on bounded open subsets of the complex plane. -/
def HasBoundedOpenMaximumPrinciple (u : ℂ → ℝ) : Prop :=
  ∀ {V : Set ℂ} {M : ℝ}, IsOpen V → Bornology.IsBounded V →
    (∀ z ∈ frontier V, u z ≤ M) → ∀ z ∈ V, u z ≤ M

/-- Abstract Jordan-interior filling lemma.  If the frontier of a bounded connected open set is
inside a strict-sublevel component, the maximum principle puts the whole open set below the same
level; relative closedness of the component then puts the whole set in that component. -/
lemma bounded_open_subset_sublevelComponent_of_frontier_subset
    {u : ℂ → ℝ} (hu : Continuous u) (hmax : HasBoundedOpenMaximumPrinciple u)
    {c : ℝ} {a : ℂ} {V : Set ℂ} (hVopen : IsOpen V)
    (hVbounded : Bornology.IsBounded V) (hVpre : IsPreconnected V)
    (hVfront : (frontier V).Nonempty)
    (hfrontD : frontier V ⊆ sublevelComponent u c a) :
    V ⊆ sublevelComponent u c a := by
  have hfrontBounded : Bornology.IsBounded (frontier V) :=
    hVbounded.closure.subset frontier_subset_closure
  have hfrontCompact : IsCompact (frontier V) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_frontier, hfrontBounded⟩
  obtain ⟨w, hwFront, hwmax⟩ :=
    hfrontCompact.exists_isMaxOn hVfront hu.continuousOn
  have hwD : w ∈ sublevelComponent u c a := hfrontD hwFront
  have hwlt : u w < c := sublevelComponent_subset u c a hwD
  have hVsub : V ⊆ strictSublevel u c := by
    intro z hz
    change u z < c
    exact lt_of_le_of_lt (hmax hVopen hVbounded (fun y hy ↦ hwmax hy) z hz) hwlt
  have hDopen : IsOpen (sublevelComponent u c a) := isOpen_sublevelComponent hu c a
  have hwClosureV : w ∈ closure V := frontier_subset_closure hwFront
  obtain ⟨y, hyD, hyV⟩ := mem_closure_iff_nhds.mp hwClosureV _ (hDopen.mem_nhds hwD)
  apply hVpre.subset_of_closure_inter_subset hDopen ⟨y, hyV, hyD⟩
  intro z hz
  apply mem_sublevelComponent_of_mem_closure_of_lt hu hz.1
  exact hVsub hz.2

/-!
## Nesting and exhaustion

The line segment from the fixed base point to any prescribed point is compact and connected.
Continuity therefore bounds `u` on that segment.  A level sequence tending to infinity eventually
lies above this bound, placing the whole segment in one strict sublevel component.
-/

lemma isCompact_segment_complex (a z : ℂ) : IsCompact (segment ℝ a z) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

lemma isPreconnected_segment_complex (a z : ℂ) : IsPreconnected (segment ℝ a z) :=
  (convex_segment a z).isPreconnected

/-- Every line segment from the base point is eventually contained in a component from any level
sequence tending to infinity. -/
lemma exists_sublevelComponent_containing_segment {u : ℂ → ℝ} (hu : Continuous u)
    {level : ℕ → ℝ} (hlevel : Tendsto level atTop atTop) (a z : ℂ) :
    ∃ n, segment ℝ a z ⊆ sublevelComponent u (level n) a := by
  let K : Set ℂ := segment ℝ a z
  have hKcompact : IsCompact K := isCompact_segment_complex a z
  have hKnonempty : K.Nonempty := ⟨a, left_mem_segment ℝ a z⟩
  obtain ⟨w, hwK, hwmax⟩ := hKcompact.exists_isMaxOn hKnonempty hu.continuousOn
  obtain ⟨n, hn⟩ : ∃ n, u w + 1 ≤ level n := (tendsto_atTop.mp hlevel (u w + 1)).exists
  have hKsub : K ⊆ strictSublevel u (level n) := by
    intro y hy
    change u y < level n
    have hymax : u y ≤ u w := hwmax hy
    linarith
  refine ⟨n, (isPreconnected_segment_complex a z).subset_connectedComponentIn
    (left_mem_segment ℝ a z) hKsub⟩

/-- The increasing union of base-point sublevel components is the whole complex plane whenever
the levels tend to infinity.  Monotonicity of the sequence is not needed for this exhaustion
identity. -/
theorem iUnion_sublevelComponent_eq_univ {u : ℂ → ℝ} (hu : Continuous u)
    {level : ℕ → ℝ} (hlevel : Tendsto level atTop atTop) (a : ℂ) :
    ⋃ n, sublevelComponent u (level n) a = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨n, hn⟩ := exists_sublevelComponent_containing_segment hu hlevel a z
  exact mem_iUnion.mpr ⟨n, hn (right_mem_segment ℝ a z)⟩

/-- A monotone level sequence gives a nested sequence of components. -/
lemma monotone_sublevelComponent {u : ℂ → ℝ} {level : ℕ → ℝ}
    (hlevel : Monotone level) (a : ℂ) :
    Monotone (fun n ↦ sublevelComponent u (level n) a) := by
  intro m n hmn
  exact sublevelComponent_mono a (hlevel hmn)

/-- Consecutive domains in a monotone recursive construction are nested. -/
lemma sublevelComponent_succ_subset {u : ℂ → ℝ} {level : ℕ → ℝ}
    (hlevel : Monotone level) (a : ℂ) (n : ℕ) :
    sublevelComponent u (level n) a ⊆ sublevelComponent u (level (n + 1)) a :=
  monotone_sublevelComponent hlevel a (Nat.le_succ n)

/-!
## A bundled recursive tower
-/

/-- Data asserting that a fixed-base sequence of strict-sublevel components is a nested
exhaustion.  The actual domains are `sublevelComponent u (level n) a`; bundling only the
hypotheses keeps downstream recursive constructions free of repeated bookkeeping. -/
structure IsNestedSublevelExhaustion (u : ℂ → ℝ) (level : ℕ → ℝ) (a : ℂ) : Prop where
  continuous : Continuous u
  strictMono_level : StrictMono level
  tendsto_level : Tendsto level atTop atTop
  base_mem_first : u a < level 0

namespace IsNestedSublevelExhaustion

variable {u : ℂ → ℝ} {level : ℕ → ℝ} {a : ℂ}

lemma base_mem (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    u a < level n :=
  h.base_mem_first.trans_le (h.strictMono_level.monotone (Nat.zero_le n))

lemma isOpen (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    IsOpen (sublevelComponent u (level n) a) :=
  isOpen_sublevelComponent h.continuous _ _

lemma isPathConnected (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    IsPathConnected (sublevelComponent u (level n) a) :=
  isPathConnected_sublevelComponent h.continuous (h.base_mem n)

lemma monotone (h : IsNestedSublevelExhaustion u level a) :
    Monotone (fun n ↦ sublevelComponent u (level n) a) :=
  monotone_sublevelComponent h.strictMono_level.monotone a

lemma closure_subset_succ (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    closure (sublevelComponent u (level n) a) ⊆
      sublevelComponent u (level (n + 1)) a :=
  closure_sublevelComponent_subset_of_lt h.continuous (h.base_mem n)
    (h.strictMono_level (Nat.lt_succ_self n))

lemma frontier_subset_succ (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    frontier (sublevelComponent u (level n) a) ⊆
      sublevelComponent u (level (n + 1)) a :=
  frontier_subset_closure.trans (h.closure_subset_succ n)

lemma frontier_eq_level (h : IsNestedSublevelExhaustion u level a) (n : ℕ) :
    frontier (sublevelComponent u (level n) a) ⊆ {z | u z = level n} :=
  frontier_sublevelComponent_subset_levelSet h.continuous _ _

lemma iUnion_eq_univ (h : IsNestedSublevelExhaustion u level a) :
    ⋃ n, sublevelComponent u (level n) a = univ :=
  iUnion_sublevelComponent_eq_univ h.continuous h.tendsto_level a

/-- If `u` is unbounded above, every domain in the tower is proper and has a boundary point at
its prescribed level. -/
lemma exists_boundary_point (h : IsNestedSublevelExhaustion u level a)
    (hu_unbounded : ∀ c : ℝ, ∃ z, c ≤ u z) (n : ℕ) :
    ∃ z, z ∈ frontier (sublevelComponent u (level n) a) ∧ u z = level n := by
  obtain ⟨z, hz⟩ := hu_unbounded (level n)
  exact exists_boundary_point_at_level_of_le_value h.continuous (h.base_mem n) hz

end IsNestedSublevelExhaustion

/-!
For a `Subharmonic u`, all topology above applies through `Subharmonic.continuous`.  The remaining
step in the classical LRW argument is the planar Jordan-domain maximum principle: a Jordan curve
contained in one component has its bounded complementary domain in the same component.  Mathlib
v4.33.0 supplies neither a Jordan curve theorem nor the planar criterion identifying such an open
connected, hole-free set with `IsSimplyConnected`; consequently that independent planar-topology
theorem is deliberately not postulated here.
-/

lemma isOpen_sublevelComponent_of_subharmonic {u : ℂ → ℝ} (hu : Subharmonic u)
    (c : ℝ) (a : ℂ) :
    IsOpen (sublevelComponent u c a) :=
  isOpen_sublevelComponent hu.continuous c a

lemma isPathConnected_sublevelComponent_of_subharmonic {u : ℂ → ℝ}
    (hu : Subharmonic u) {c : ℝ} {a : ℂ} (ha : u a < c) :
    IsPathConnected (sublevelComponent u c a) :=
  isPathConnected_sublevelComponent hu.continuous ha

lemma frontier_sublevelComponent_subset_levelSet_of_subharmonic {u : ℂ → ℝ}
    (hu : Subharmonic u) (c : ℝ) (a : ℂ) :
    frontier (sublevelComponent u c a) ⊆ {z | u z = c} :=
  frontier_sublevelComponent_subset_levelSet hu.continuous c a

end Erdos515
