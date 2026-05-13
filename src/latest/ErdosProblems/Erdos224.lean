/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 224.
https://www.erdosproblems.com/forum/thread/224

Informal authors:
- Ludwig Danzer
- Branko Grünbaum

Formal authors:
- GPT-5.2 Thinking
- Codex
- Coder-Osman

URLs:
- https://www.erdosproblems.com/forum/thread/224#post-3157
- https://github.com/SpringSense-Innovation-Institute/ai-for-math-lean/blob/main/erdos-problems/erdos224/Erdos224.lean
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Closure
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Affine.Isometry

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.cdot false

/-
Danzer–Grünbaum (Lean4 + mathlib)

Core route (contrapositive):
  NoObtuse(A) → card(A) ≤ 2^d
So if card(A) = 2^d + 1 then ¬NoObtuse(A), i.e. there exists an obtuse triple.

from SpringSense Innovation Institute
-/


open scoped BigOperators
open scoped Real
open scoped RealInnerProductSpace
open scoped Pointwise  -- Minkowski sum / scalar actions on sets often live here
open MeasureTheory
open Filter

namespace Erdos224

noncomputable section

variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

local instance (d : ℕ) : MeasurableSpace (E d) := borel (E d)
local instance (d : ℕ) : BorelSpace (E d) := ⟨rfl⟩
local instance (S : AffineSubspace ℝ (E d)) :
    NormedAddTorsor S.direction S.direction :=
  SeminormedAddCommGroup.toNormedAddTorsor

def ObtuseAt {d : ℕ} (x y z : E d) : Prop :=
  ⟪y - x, z - x⟫ < 0

-- Single-vertex version, chosen to make the final negation lightweight.
def NoObtuse {d : ℕ} (A : Finset (E d)) : Prop :=
  ∀ ⦃x y z : E d⦄, x ∈ A → y ∈ A → z ∈ A →
    x ≠ y → x ≠ z → y ≠ z →
    ¬ ObtuseAt (d:=d) x y z

/-
========== Key bound: NoObtuse(A) → card(A) ≤ 2^d ==========
This is the Danzer–Grünbaum core: a no-obtuse set has at most 2^d points.
You can split it into three layers:
  (1) NoObtuse → slab/antipodal property
  (2) Use convex hull P = conv(A) and define half-size copies P_a ⊆ P
  (3) Show interiors are pairwise disjoint; volume counting gives |A| ≤ 2^d
-/

-- (1) NoObtuse → slab property: for x ≠ y, projections along v=y-x lie between endpoints
lemma slab_property_of_noObtuse
  (A : Finset (E d)) (hNo : NoObtuse (d:=d) A) :
  ∀ ⦃x y z : E d⦄, x ∈ A → y ∈ A → z ∈ A → x ≠ y →
    let v : E d := y - x;
    (⟪v, z⟫ ≥ ⟪v, x⟫) ∧ (⟪v, z⟫ ≤ ⟪v, y⟫) := by
  classical
  intro x y z hx hy hz hxy
  -- Use hNo to exclude obtuse angles at x and at y:
  --  ¬ObtuseAt x y z  gives  ⟪y-x, z-x⟫ ≥ 0  →  ⟪v,z⟫ ≥ ⟪v,x⟫
  --  ¬ObtuseAt y x z  gives  ⟪x-y, z-y⟫ ≥ 0  →  ⟪v,z⟫ ≤ ⟪v,y⟫
  -- Convert "¬(inner < 0)" to "0 ≤ inner" via `not_lt`,
  -- and expand ⟪v, z-x⟫ as ⟪v,z⟫ - ⟪v,x⟫.
  have hxy' : ⟪y - x, x⟫ ≤ ⟪y - x, y⟫ := by
    have hv : 0 ≤ ⟪y - x, y - x⟫ := real_inner_self_nonneg
    have hv' : 0 ≤ ⟪y - x, y⟫ - ⟪y - x, x⟫ := by
      rw [← inner_sub_right]
      exact hv
    linarith
  have hgoal :
      (⟪y - x, z⟫ ≥ ⟪y - x, x⟫) ∧ (⟪y - x, z⟫ ≤ ⟪y - x, y⟫) := by
    by_cases hzx : z = x
    · subst hzx
      refine ⟨by linarith, hxy'⟩
    by_cases hzy : z = y
    · subst hzy
      refine ⟨by linarith [hxy'], by linarith⟩
    have hxz_ne : x ≠ z := by
      simpa [ne_comm] using hzx
    have hyz_ne : y ≠ z := by
      simpa [ne_comm] using hzy
    have hxz : 0 ≤ ⟪y - x, z - x⟫ := by
      exact not_lt.mp (hNo hx hy hz hxy hxz_ne hyz_ne)
    have hxz' : ⟪y - x, x⟫ ≤ ⟪y - x, z⟫ := by
      have hxz'' : 0 ≤ ⟪y - x, z⟫ - ⟪y - x, x⟫ := by
        simpa [inner_sub_right] using hxz
      linarith
    have hyz : 0 ≤ ⟪x - y, z - y⟫ := by
      exact not_lt.mp (hNo hy hx hz hxy.symm hyz_ne hxz_ne)
    have hsub : x - y = -(y - x) := by
      simp
    have hyz' : ⟪y - x, z - y⟫ ≤ 0 := by
      have hyz0 := hyz
      rw [hsub, inner_neg_left] at hyz0
      -- from 0 ≤ -a conclude a ≤ 0
      linarith
    have hyz'' : ⟪y - x, z⟫ ≤ ⟪y - x, y⟫ := by
      have hyz''' : ⟪y - x, z⟫ - ⟪y - x, y⟫ ≤ 0 := by
        simpa [inner_sub_right] using hyz'
      linarith
    exact ⟨by linarith [hxz'], hyz''⟩
  simpa using hgoal

-- (2) Define the convex hull P
def P (A : Finset (E d)) : Set (E d) :=
  convexHull ℝ (A : Set (E d))

-- Difference body P - P (written as P + (-P))
def Pminus (A : Finset (E d)) : Set (E d) :=
  P (d:=d) A + (-P (d:=d) A)

lemma exists_pos_smul_add_mem_of_mem_interior
  {s : Set (E d)} {x v : E d} (hx : x ∈ interior s) (hv : v ≠ 0) :
  ∃ t : ℝ, 0 < t ∧ x + t • v ∈ s := by
  have hnhds : s ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨r, hrpos, hrsub⟩
  let t : ℝ := r / (2 * ‖v‖)
  have htpos : 0 < t := by
    have hvn : 0 < ‖v‖ := by simpa [norm_eq_zero] using hv
    have hden : 0 < (2 * ‖v‖) := by nlinarith [hvn]
    have : 0 < r / (2 * ‖v‖) := by exact div_pos hrpos hden
    simpa [t] using this
  have hnorm : ‖t • v‖ < r := by
    have hnorm_eq : ‖t • v‖ = t * ‖v‖ := by
      have := norm_smul t v
      simpa [abs_of_pos htpos] using this
    have hvn : ‖v‖ ≠ 0 := by
      exact (norm_ne_zero_iff).2 hv
    have hnorm_val : t * ‖v‖ = r / 2 := by
      have hden : (2 * ‖v‖) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hvn
      calc
        t * ‖v‖ = r / (2 * ‖v‖) * ‖v‖ := by rfl
        _ = r / 2 := by field_simp [hden]
    have : (r / 2 : ℝ) < r := by linarith [hrpos]
    nlinarith [hnorm_eq, hnorm_val, this]
  have hball : x + t • v ∈ Metric.ball x r := by
    have : ‖(x + t • v) - x‖ < r := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm
    simpa [Metric.mem_ball] using this
  exact ⟨t, htpos, hrsub hball⟩

-- (2) For each a∈A, define the 1/2-scaled copy of P centered at a.
-- Standard: AffineMap.homothety a (1/2) '' P
def halfCopy (A : Finset (E d)) (a : E d) : Set (E d) :=
  (AffineMap.homothety a (1/2 : ℝ)) '' (P (d:=d) A)

-- halfCopy ⊆ P
lemma halfCopy_subset_P
  (A : Finset (E d)) {a : E d} (ha : a ∈ A) :
  halfCopy (d:=d) A a ⊆ P (d:=d) A := by
  classical
  -- Points of the homothety lie on the segment a–p; convexity keeps the segment in P.
  -- Use convexity of convexHull and expand `AffineMap.homothety_apply`.
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  have hconv : Convex ℝ (P (d:=d) A) := by
    simpa [P] using (convex_convexHull ℝ (A : Set (E d)))
  have haP : a ∈ P (d:=d) A := by
    exact subset_convexHull ℝ (A : Set (E d)) ha
  have hpP : p ∈ P (d:=d) A := hp
  have hmem : (1 / 2 : ℝ) • p + (1 - (1 / 2 : ℝ)) • a ∈ P (d:=d) A := by
    refine hconv hpP haP ?_ ?_ ?_
    · nlinarith
    · nlinarith
    · ring
  have hrew :
      (1 / 2 : ℝ) • p + (1 - (1 / 2 : ℝ)) • a =
        (1 / 2 : ℝ) • (p - a) + a := by
    have hcoef' : (1 - (1 / 2 : ℝ)) = (- (1 / 2 : ℝ) + 1) := by
      ring
    have hcoef'' : (1 - (1 / 2 : ℝ)) • a = (- (1 / 2 : ℝ) + 1) • a :=
      congrArg (fun t => t • a) hcoef'
    have hcoef''' :
        (1 / 2 : ℝ) • p + (1 - (1 / 2 : ℝ)) • a =
          (1 / 2 : ℝ) • p + ((- (1 / 2 : ℝ) + 1) • a) :=
      congrArg (fun t => (1 / 2 : ℝ) • p + t) hcoef''
    calc
      (1 / 2 : ℝ) • p + (1 - (1 / 2 : ℝ)) • a
          = (1 / 2 : ℝ) • p + ((- (1 / 2 : ℝ) + 1) • a) := hcoef'''
      _ = (1 / 2 : ℝ) • p + ((- (1 / 2 : ℝ)) • a + (1 : ℝ) • a) := by
              simp [add_smul]
      _ = (1 / 2 : ℝ) • p - (1 / 2 : ℝ) • a + a := by
              simp [sub_eq_add_neg, add_assoc]
      _ = (1 / 2 : ℝ) • (p - a) + a := by
              simp [smul_sub]
  have hmem' : (1 / 2 : ℝ) • (p - a) + a ∈ P (d:=d) A := by
    have hmem' := hmem
    rw [hrew] at hmem'
    exact hmem'
  simpa [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using hmem'

-- (3) Interiors are pairwise disjoint: a≠b ⇒ interior(halfCopy a) ∩ interior(halfCopy b) = ∅.
-- Key idea: translate to P - P and show the same point is interior and boundary.
lemma interiors_disjoint_of_noObtuse
  (A : Finset (E d)) (hNo : NoObtuse (d:=d) A) :
  ∀ ⦃a b : E d⦄, a ∈ A → b ∈ A → a ≠ b →
    (interior (halfCopy (d:=d) A a)) ∩ (interior (halfCopy (d:=d) A b)) = (∅ : Set (E d)) := by
  classical
  intro a b ha hb hne
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  have hxA' : x ∈ halfCopy (d:=d) A a := by
    exact interior_subset hxA
  have hxB' : x ∈ halfCopy (d:=d) A b := by
    exact interior_subset hxB
  rcases hxA' with ⟨p, hp, rfl⟩
  rcases hxB' with ⟨q, hq, hxq⟩
  -- Convert the second membership to a concrete equation.
  have hxq' :
      (AffineMap.homothety b (1 / 2 : ℝ)) q =
        (AffineMap.homothety a (1 / 2 : ℝ)) p := by
    simpa using hxq
  -- Rewrite homothety in linear form for later algebra.
  have hxq'' :
      (1 / 2 : ℝ) • (q - b) + b =
        (1 / 2 : ℝ) • (p - a) + a := by
    simpa [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using hxq'
  -- From the equality above, derive a relation between a-b and p-q.
  have hdiff : a - b = q - p := by
    have hsum := congrArg (fun t => (2 : ℝ) • t) hxq''
    have hsum' : q + b = p + a := by
      simpa [smul_add, smul_smul, smul_sub, sub_eq_add_neg, two_smul,
        add_assoc, add_left_comm, add_comm] using hsum
    have hsum'' := congrArg (fun t => t - b - p) hsum'
    have hsum''' : q - p = a - b := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum''
    exact hsum'''.symm
  -- With hdiff, use the slab property to force a-b onto the boundary of P-P.
  -- This is the geometric core of the disjointness argument.
  have hPminus_mem : a - b ∈ Pminus (d:=d) A := by
    -- `a - b` is in P - P because a,b ∈ P.
    have haP : a ∈ P (d:=d) A := by
      exact subset_convexHull ℝ (A : Set (E d)) ha
    have hbP : b ∈ P (d:=d) A := by
      exact subset_convexHull ℝ (A : Set (E d)) hb
    have hbneg : -b ∈ -P (d:=d) A := by
      simpa using hbP
    refine (Set.mem_add).2 ?_
    refine ⟨a, haP, -b, hbneg, by simp [sub_eq_add_neg]⟩
  have hPminus_int : a - b ∈ interior (Pminus (d:=d) A) := by
    -- From x in both interiors of halfCopy, show a-b in interior(P-P).
    have hhalf_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have hcont_a :
        Continuous (fun x : E d => (1 / 2 : ℝ) • (x - a) + a) := by
      fun_prop
    have hcont_b :
        Continuous (fun x : E d => (1 / 2 : ℝ) • (x - b) + b) := by
      fun_prop
    have hcont_a' : Continuous (AffineMap.homothety a (1 / 2 : ℝ)) := by
      simpa [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using hcont_a
    have hcont_b' : Continuous (AffineMap.homothety b (1 / 2 : ℝ)) := by
      simpa [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using hcont_b
    have hinj_a : Function.Injective (AffineMap.homothety a (1 / 2 : ℝ)) := by
      intro x y hxy
      have hxy' : (1 / 2 : ℝ) • (x - a) = (1 / 2 : ℝ) • (y - a) := by
        have := congrArg (fun z => z - a) hxy
        simpa [AffineMap.homothety_apply, vsub_eq_sub, sub_eq_add_neg, add_assoc] using this
      have hunit : IsUnit (1 / 2 : ℝ) := by
        exact isUnit_iff_ne_zero.2 hhalf_ne
      have hsub : x - a = y - a := (hunit.smul_left_cancel).1 hxy'
      have hsub' := congrArg (fun z => z + a) hsub
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub'
    have hinj_b : Function.Injective (AffineMap.homothety b (1 / 2 : ℝ)) := by
      intro x y hxy
      have hxy' : (1 / 2 : ℝ) • (x - b) = (1 / 2 : ℝ) • (y - b) := by
        have := congrArg (fun z => z - b) hxy
        simpa [AffineMap.homothety_apply, vsub_eq_sub, sub_eq_add_neg, add_assoc] using this
      have hunit : IsUnit (1 / 2 : ℝ) := by
        exact isUnit_iff_ne_zero.2 hhalf_ne
      have hsub : x - b = y - b := (hunit.smul_left_cancel).1 hxy'
      have hsub' := congrArg (fun z => z + b) hsub
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub'
    have hp_int : p ∈ interior (P (d:=d) A) := by
      have hxApre' :
          p ∈ interior ((AffineMap.homothety a (1 / 2 : ℝ)) ⁻¹' (halfCopy (d:=d) A a)) := by
        have hxApre : p ∈ (AffineMap.homothety a (1 / 2 : ℝ)) ⁻¹' interior (halfCopy (d:=d) A a) := by
          simpa [Set.mem_preimage] using hxA
        exact (preimage_interior_subset_interior_preimage hcont_a') hxApre
      have hpreimg :
          (AffineMap.homothety a (1 / 2 : ℝ)) ⁻¹' (halfCopy (d:=d) A a) = P (d:=d) A := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have : y = x := hinj_a hxy
          simpa [this] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hxApre'' := hxApre'
      rw [hpreimg] at hxApre''
      simpa using hxApre''
    have hq_int : q ∈ interior (P (d:=d) A) := by
      have hxB' : (AffineMap.homothety b (1 / 2 : ℝ)) q ∈ interior (halfCopy (d:=d) A b) := by
        have hxB' := hxB
        rw [hxq.symm] at hxB'
        exact hxB'
      have hxBpre' :
          q ∈ interior ((AffineMap.homothety b (1 / 2 : ℝ)) ⁻¹' (halfCopy (d:=d) A b)) := by
        have hxBpre : q ∈ (AffineMap.homothety b (1 / 2 : ℝ)) ⁻¹' interior (halfCopy (d:=d) A b) := by
          simpa [Set.mem_preimage] using hxB'
        exact (preimage_interior_subset_interior_preimage hcont_b') hxBpre
      have hpreimg :
          (AffineMap.homothety b (1 / 2 : ℝ)) ⁻¹' (halfCopy (d:=d) A b) = P (d:=d) A := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨y, hy, hxy⟩
          have : y = x := hinj_b hxy
          simpa [this] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hxBpre'' := hxBpre'
      rw [hpreimg] at hxBpre''
      simpa using hxBpre''
    have hnegp_int : -p ∈ interior (-P (d:=d) A) := by
      have hmem : -p ∈ (Homeomorph.neg (E d)) '' interior (P (d:=d) A) := by
        refine ⟨p, hp_int, ?_⟩
        simp
      have himg :
          (Homeomorph.neg (E d)) '' interior (P (d:=d) A) =
            interior ((Homeomorph.neg (E d)) '' P (d:=d) A) := by
        simpa using (Homeomorph.image_interior (Homeomorph.neg (E d)) (P (d:=d) A))
      have hmem' := hmem
      rw [himg] at hmem'
      -- rewrite the image under negation to `-P`
      simpa [Set.image_neg_eq_neg] using hmem'
    have hsum_mem : q + (-p) ∈ interior (P (d:=d) A) + interior (-P (d:=d) A) :=
      Set.add_mem_add hq_int hnegp_int
    have hsum_int :
        q + (-p) ∈ interior (P (d:=d) A + -P (d:=d) A) := by
      exact (subset_interior_add hsum_mem)
    have hsum_int' : q - p ∈ interior (Pminus (d:=d) A) := by
      simpa [Pminus, sub_eq_add_neg] using hsum_int
    simpa [hdiff] using hsum_int'
  have hPminus_bd : a - b ∈ frontier (Pminus (d:=d) A) := by
    -- Antipodal/slab property implies extreme direction lies on boundary.
    -- Set up the linear functional f(z) = ⟪v, z⟫ with v = a - b.
    let v : E d := a - b
    have hv_ne : v ≠ 0 := by
      intro hv
      have : a = b := by
        have hv' : a - b = 0 := by simpa [v] using hv
        exact sub_eq_zero.mp hv'
      exact hne this
    have hv_norm : 0 < ‖v‖ := by
      simpa [norm_eq_zero] using hv_ne
    let f : E d → ℝ := fun z => ⟪v, z⟫
    have hlin : IsLinearMap ℝ f := by
      refine ⟨?map_add, ?map_smul⟩
      · intro x y
        simp [f, inner_add_right]
      · intro c x
        simp [f, inner_smul_right]
    -- All points of A are between the hyperplanes through b and a.
    have hA_le : ∀ z ∈ (A : Set (E d)), f z ≤ f a := by
      intro z hz
      have hslab := slab_property_of_noObtuse (d:=d) A hNo hb ha hz hne.symm
      simpa [v, f] using hslab.2
    have hA_ge : ∀ z ∈ (A : Set (E d)), f b ≤ f z := by
      intro z hz
      have hslab := slab_property_of_noObtuse (d:=d) A hNo hb ha hz hne.symm
      simpa [v, f] using hslab.1
    -- Extend the bounds to all of P = convexHull A.
    have hP_le : ∀ z ∈ P (d:=d) A, f z ≤ f a := by
      have hconv : Convex ℝ {z | f z ≤ f a} := convex_halfSpace_le hlin _
      have hsubset : (A : Set (E d)) ⊆ {z | f z ≤ f a} := by
        intro z hz
        exact hA_le z hz
      have hPsubset : P (d:=d) A ⊆ {z | f z ≤ f a} := by
        exact convexHull_min hsubset hconv
      intro z hz
      exact (hPsubset hz)
    have hP_ge : ∀ z ∈ P (d:=d) A, f b ≤ f z := by
      have hconv : Convex ℝ {z | f b ≤ f z} := convex_halfSpace_ge hlin _
      have hsubset : (A : Set (E d)) ⊆ {z | f b ≤ f z} := by
        intro z hz
        exact hA_ge z hz
      have hPsubset : P (d:=d) A ⊆ {z | f b ≤ f z} := by
        exact convexHull_min hsubset hconv
      intro z hz
      exact (hPsubset hz)
    -- Hence `a - b` maximizes `f` on `P - P`.
    have hmax : ∀ y ∈ Pminus (d:=d) A, f y ≤ f (a - b) := by
      intro y hy
      rcases (Set.mem_add).1 hy with ⟨p, hp, q, hq, rfl⟩
      have hp_le : f p ≤ f a := hP_le p hp
      have hq' : -q ∈ P (d:=d) A := by
        simpa using hq
      have hq_ge : f b ≤ f (-q) := hP_ge (-q) hq'
      have hq_le : f q ≤ -f b := by
        have : f q = -f (-q) := by
          simp [f]
        linarith
      have hf_add : f (p + q) = f p + f q := by
        simp [f, inner_add_right]
      have hf_le : f (p + q) ≤ f a - f b := by
        calc
          f (p + q) = f p + f q := hf_add
          _ ≤ f a - f b := by linarith
      have hf_le' : f (p + q) ≤ f (a - b) := by
        have hf_ab : f a - f b = f (a - b) := by
          simp [f, inner_sub_right]
        simpa [hf_ab] using hf_le
      simpa using hf_le'
    -- If `a-b` were interior, we could move slightly in direction `v`.
    have hcl : a - b ∈ closure (Pminus (d:=d) A) := by
      exact subset_closure hPminus_mem
    have hnot_int : a - b ∉ interior (Pminus (d:=d) A) := by
      intro hInt
      rcases exists_pos_smul_add_mem_of_mem_interior (s:=Pminus (d:=d) A) (x:=a - b) (v:=v)
        hInt hv_ne with ⟨t, htpos, hmem_set⟩
      have hf_strict : f ((a - b) + t • v) > f (a - b) := by
        have hvpos : 0 < ⟪v, v⟫ := by
          have := (real_inner_self_pos (x:=v)).2 hv_ne
          simpa using this
        calc
          f ((a - b) + t • v)
              = f (a - b) + t * ⟪v, v⟫ := by
                  simp [f, inner_add_right, inner_smul_right]
          _ > f (a - b) := by nlinarith
      have hf_le := hmax ((a - b) + t • v) hmem_set
      linarith
    exact by
      -- frontier = closure \ interior
      exact ⟨hcl, hnot_int⟩
  have hdisj : Disjoint (interior (Pminus (d:=d) A)) (frontier (Pminus (d:=d) A)) :=
    disjoint_interior_frontier
  exact (Set.disjoint_left.1 hdisj) hPminus_int hPminus_bd

-- (4) Volume scaling: vol(halfCopy a) = vol(P)/2^d
lemma volume_halfCopy
  (A : Finset (E d)) (a : E d) :
  volume (halfCopy (d:=d) A a) =
    ENNReal.ofReal (abs ((1 / 2 : ℝ) ^ d)) * volume (P (d:=d) A) := by
  classical
  -- Volume scales by |r|^d under homothety (Haar measure fact).
  simp [halfCopy, finrank_euclideanSpace]
-- Turn (subset + disjoint interiors + volume scaling) into card ≤ 2^d
theorem card_le_pow_two_of_noObtuse_of_span
  (A : Finset (E d)) (hNo : NoObtuse (d:=d) A)
  (hspan : affineSpan ℝ (A : Set (E d)) = ⊤) :
  A.card ≤ 2^d := by
  classical
  -- Structure:
  -- 1) P := conv(A)
  -- 2) For each a∈A, halfCopy a ⊆ P
  -- 3) Interiors are pairwise disjoint
  -- 4) Each halfCopy has volume vol(P)/2^d
  -- 5) Additivity: ∑ vol(halfCopy a) ≤ vol(P)
  -- 6) Simplify to |A| ≤ 2^d
  --
  -- In Lean, step (5) uses "pairwise disjoint measurable sets ⇒ measure of union = sum"
  -- (or a finite sum over `A.attach`).
  --
  -- Below is the volume-counting proof.
  have hconvP : Convex ℝ (P (d:=d) A) := by
    simpa [P] using (convex_convexHull ℝ (A : Set (E d)))
  have hPint : (interior (P (d:=d) A)).Nonempty := by
    have hspan' : affineSpan ℝ (P (d:=d) A) = ⊤ := by
      simpa [P, affineSpan_convexHull] using hspan
    simpa [hspan'] using (hconvP.interior_nonempty_iff_affineSpan_eq_top)
  have hvol_pos : 0 < volume (P (d:=d) A) := by
    have hpos : 0 < volume (interior (P (d:=d) A)) := by
      simpa using (isOpen_interior.measure_pos (μ:=volume) hPint)
    exact hpos.trans_le (measure_mono interior_subset)
  have hvol_ne_top : volume (P (d:=d) A) ≠ ⊤ := by
    have hcompact : IsCompact (P (d:=d) A) := by
      simpa [P] using (A.finite_toSet.isCompact_convexHull ℝ)
    exact (ne_of_lt hcompact.measure_lt_top)
  let c : ENNReal := ENNReal.ofReal (abs ((1 / 2 : ℝ) ^ d))
  have hsum_le : Finset.sum A (fun a => volume (halfCopy (d:=d) A a)) ≤ volume (P (d:=d) A) := by
    -- Use disjoint interiors and null frontier of convex sets.
    have hpair :
        Set.Pairwise (A : Set (E d))
          (fun a b =>
            Disjoint (interior (halfCopy (d:=d) A a)) (interior (halfCopy (d:=d) A b))) := by
      intro a ha b hb hne
      refine Set.disjoint_iff_inter_eq_empty.mpr ?_
      exact interiors_disjoint_of_noObtuse (d:=d) A hNo ha hb hne
    have hmeas : ∀ a ∈ A, MeasurableSet (interior (halfCopy (d:=d) A a)) := by
      intro a ha
      simpa using (isOpen_interior.measurableSet)
    have hunion :
        volume (⋃ a ∈ (A : Set (E d)), interior (halfCopy (d:=d) A a)) =
          Finset.sum A (fun a => volume (interior (halfCopy (d:=d) A a))) := by
      simpa using
        (measure_biUnion_finset (μ:=volume) (s:=A) (f:=fun a => interior (halfCopy (d:=d) A a))
          hpair hmeas)
    have hsubset :
        (⋃ a ∈ (A : Set (E d)), interior (halfCopy (d:=d) A a)) ⊆ P (d:=d) A := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨a, hx⟩
      rcases Set.mem_iUnion.1 hx with ⟨ha, hx⟩
      have hx' : x ∈ halfCopy (d:=d) A a := interior_subset hx
      exact (halfCopy_subset_P (d:=d) A ha) hx'
    have hle : volume (⋃ a ∈ (A : Set (E d)), interior (halfCopy (d:=d) A a))
        ≤ volume (P (d:=d) A) := by
      exact measure_mono hsubset
    -- Replace interior volumes by full volumes using null frontier of convex sets.
    have hsum_eq :
        Finset.sum A (fun a => volume (interior (halfCopy (d:=d) A a))) =
          Finset.sum A (fun a => volume (halfCopy (d:=d) A a)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hconv : Convex ℝ (halfCopy (d:=d) A a) := by
        simpa [halfCopy] using (hconvP.affine_image (AffineMap.homothety a (1 / 2 : ℝ)))
      have hfront : volume (frontier (halfCopy (d:=d) A a)) = 0 := by
        simpa using (Convex.addHaar_frontier (μ:=volume) (s:=halfCopy (d:=d) A a) hconv)
      have hvol :
          volume (interior (halfCopy (d:=d) A a)) = volume (halfCopy (d:=d) A a) := by
        have := measure_diff_null (μ:=volume) (s:=halfCopy (d:=d) A a)
          (t:=frontier (halfCopy (d:=d) A a)) hfront
        simpa [self_diff_frontier] using this
      simp [hvol]
    have : volume (⋃ a ∈ (A : Set (E d)), interior (halfCopy (d:=d) A a))
        = Finset.sum A (fun a => volume (halfCopy (d:=d) A a)) := by
      simpa [hsum_eq] using hunion
    exact this ▸ hle
  -- Convert the volume inequality to a cardinality bound.
  have hsum_eval :
      Finset.sum A (fun a => volume (halfCopy (d:=d) A a)) =
        (A.card : ENNReal) * (c * volume (P (d:=d) A)) := by
    have hconst : ∀ a ∈ A, volume (halfCopy (d:=d) A a) = c * volume (P (d:=d) A) := by
      intro a ha
      simpa [c, mul_comm, mul_left_comm, mul_assoc] using
        (volume_halfCopy (d:=d) A a)
    calc
      Finset.sum A (fun a => volume (halfCopy (d:=d) A a))
          = Finset.sum A (fun a => c * volume (P (d:=d) A)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              exact hconst a ha
      _ = (A.card : ENNReal) * (c * volume (P (d:=d) A)) := by
              simp [Finset.sum_const, nsmul_eq_mul, mul_left_comm]
  have hle : (A.card : ENNReal) * (c * volume (P (d:=d) A)) ≤ volume (P (d:=d) A) := by
    simpa [hsum_eval] using hsum_le
  -- Move to ℝ and cancel volume(P).
  have hle_real : (A.card : ℝ) * (ENNReal.toReal c) * ENNReal.toReal (volume (P (d:=d) A))
      ≤ ENNReal.toReal (volume (P (d:=d) A)) := by
    have hcard : (A.card : ENNReal) ≠ ⊤ := by simp
    have hc : c ≠ ⊤ := by simp [c]
    have hcv : c * volume (P (d:=d) A) ≠ ⊤ := ENNReal.mul_ne_top hc hvol_ne_top
    have hfin : (A.card : ENNReal) * (c * volume (P (d:=d) A)) ≠ ⊤ :=
      ENNReal.mul_ne_top hcard hcv
    have hfin' : volume (P (d:=d) A) ≠ ⊤ := hvol_ne_top
    have h := (ENNReal.toReal_le_toReal hfin hfin').2 hle
    simpa [ENNReal.toReal_mul, hvol_ne_top, hfin', mul_assoc] using h
  have hVpos : 0 < ENNReal.toReal (volume (P (d:=d) A)) := by
    exact ENNReal.toReal_pos (ne_of_gt hvol_pos) hvol_ne_top
  have hle_real' : (A.card : ℝ) * (ENNReal.toReal c) ≤ 1 := by
    have h :
        ENNReal.toReal (volume (P (d:=d) A)) * ((A.card : ℝ) * ENNReal.toReal c) ≤
          ENNReal.toReal (volume (P (d:=d) A)) * 1 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hle_real
    exact (mul_le_mul_iff_right₀ hVpos).1 h
  have hc : ENNReal.toReal c = (1 / 2 : ℝ) ^ d := by
    have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
    simp [c]
  have hcard_real : (A.card : ℝ) ≤ (2 : ℝ) ^ d := by
    have hcpos : 0 < (1 / 2 : ℝ) ^ d := by positivity
    have hcpos' : 0 < ENNReal.toReal c := by
      simp [hc]
    have hle' : (A.card : ℝ) * ((1 / 2 : ℝ) ^ d) ≤ 1 := by
      simpa [hc] using hle_real'
    have hle'' : (A.card : ℝ) ≤ 1 / ((1 / 2 : ℝ) ^ d) := by
      exact (le_div_iff₀ hcpos).2 hle'
    have hdiv : (1 : ℝ) / ((1 / 2 : ℝ) ^ d) = (2 : ℝ) ^ d := by
      simp [one_div, inv_pow]
    simpa [hdiv] using hle''
  exact_mod_cast hcard_real

-- Reduce to the full-span case by working inside the affine span.
theorem card_le_pow_two_of_noObtuse
  (A : Finset (E d)) (hNo : NoObtuse (d:=d) A) :
  A.card ≤ 2^d := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨a0, ha0⟩ := hA
    let S : AffineSubspace ℝ (E d) := affineSpan ℝ (A : Set (E d))
    have hAset : (A : Set (E d)).Nonempty := by
      exact ⟨a0, ha0⟩
    letI : Nonempty (A : Set (E d)) := ⟨⟨a0, ha0⟩⟩
    letI : Nonempty S := ⟨⟨a0, subset_affineSpan ℝ (A : Set (E d)) ha0⟩⟩
    let AsetS : Set S := ((↑) : S → E d) ⁻¹' (A : Set (E d))
    have hspanS : affineSpan ℝ AsetS = ⊤ := by
      simp [AsetS, S]
    -- Embed A into its affine span, then map into E k via an affine isometry.
    let emb : {x // x ∈ A} ↪ S :=
      ⟨fun x => ⟨x.1, subset_affineSpan ℝ (A : Set (E d)) x.2⟩,
        by
          intro x y h
          apply Subtype.ext
          exact congrArg (fun s : S => (s : E d)) h⟩
    let A' : Finset S := A.attach.map emb
    have hsubsetA' : AsetS ⊆ (A' : Set S) := by
      intro x hx
      refine (Finset.mem_map).2 ?_
      have hxA : (x : E d) ∈ A := hx
      refine ⟨⟨(x : E d), hxA⟩, ?_, ?_⟩
      · simp
      · apply Subtype.ext
        rfl
    have hspanA' : affineSpan ℝ ((A' : Finset S) : Set S) = ⊤ := by
      apply top_unique
      have hspan_le := affineSpan_mono (k:=ℝ) hsubsetA'
      simpa [hspanS] using hspan_le
    let k : ℕ := Module.finrank ℝ S.direction
    have hk : k ≤ d := by
      simpa [k, finrank_euclideanSpace] using (Submodule.finrank_le S.direction)
    let p : S := ⟨a0, subset_affineSpan ℝ (A : Set (E d)) ha0⟩
    let f1 : S ≃ᵃⁱ[ℝ] S.direction := AffineIsometryEquiv.constVSub ℝ p
    let bS := stdOrthonormalBasis ℝ S.direction
    let bE := stdOrthonormalBasis ℝ (E k)
    have hcard :
        Fintype.card (Fin (Module.finrank ℝ S.direction)) =
          Fintype.card (Fin (Module.finrank ℝ (E k))) := by
      simp [k, finrank_euclideanSpace]
    let e :
        (Fin (Module.finrank ℝ S.direction)) ≃ (Fin (Module.finrank ℝ (E k))) :=
      Fintype.equivOfCardEq hcard
    let f2 : S.direction ≃ᵃⁱ[ℝ] E k :=
      (OrthonormalBasis.equiv bS bE e).toAffineIsometryEquiv
    let f : S ≃ᵃⁱ[ℝ] E k := f1.trans f2
    let A'' : Finset (E k) := A'.image f
    have hspanA'' : affineSpan ℝ ((A'' : Finset (E k)) : Set (E k)) = ⊤ := by
      have hspanA''set :
          affineSpan ℝ (f '' ((A' : Finset S) : Set S)) = ⊤ := by
        simpa using
          (AffineMap.span_eq_top_of_surjective (f:=f.toAffineMap) (s:=((A' : Finset S) : Set S))
            f.surjective hspanA')
      simpa [A'', Finset.coe_image] using hspanA''set
    -- NoObtuse is preserved under affine isometries (inner products are preserved).
    have hNo'' : NoObtuse (d:=k) A'' := by
      intro x y z hx hy hz hxy hxz hyz
      rcases Finset.mem_image.1 hx with ⟨xS, hxS, rfl⟩
      rcases Finset.mem_image.1 hy with ⟨yS, hyS, rfl⟩
      rcases Finset.mem_image.1 hz with ⟨zS, hzS, rfl⟩
      rcases (Finset.mem_map.1 hxS) with ⟨xA, hxA, rfl⟩
      rcases (Finset.mem_map.1 hyS) with ⟨yA, hyA, rfl⟩
      rcases (Finset.mem_map.1 hzS) with ⟨zA, hzA, rfl⟩
      have hxA' : (xA : E d) ∈ A := xA.property
      have hyA' : (yA : E d) ∈ A := yA.property
      have hzA' : (zA : E d) ∈ A := zA.property
      have hxyS : (emb xA : S) ≠ (emb yA : S) := by
        intro h
        apply hxy
        simp [h]
      have hxzS : (emb xA : S) ≠ (emb zA : S) := by
        intro h
        apply hxz
        simp [h]
      have hyzS : (emb yA : S) ≠ (emb zA : S) := by
        intro h
        apply hyz
        simp [h]
      have hxyA : (xA : E d) ≠ (yA : E d) := by
        intro h
        apply hxyS
        apply Subtype.ext
        exact h
      have hxzA : (xA : E d) ≠ (zA : E d) := by
        intro h
        apply hxzS
        apply Subtype.ext
        exact h
      have hyzA : (yA : E d) ≠ (zA : E d) := by
        intro h
        apply hyzS
        apply Subtype.ext
        exact h
      have hNo_xyz :=
        hNo (x:=xA) (y:=yA) (z:=zA) hxA' hyA' hzA' hxyA hxzA hyzA
      have hinner :
          ⟪(f (emb yA) : E k) - (f (emb xA)), (f (emb zA)) - (f (emb xA))⟫ =
            ⟪(yA : E d) - (xA : E d), (zA : E d) - (xA : E d)⟫ := by
        have hinner' :
            ⟪f (emb yA) -ᵥ f (emb xA), f (emb zA) -ᵥ f (emb xA)⟫ =
              ⟪(emb yA : S) -ᵥ (emb xA : S), (emb zA : S) -ᵥ (emb xA : S)⟫ := by
          simpa [f.map_vsub] using
            (f.linearIsometryEquiv.inner_map_map ((emb yA : S) -ᵥ (emb xA : S))
              ((emb zA : S) -ᵥ (emb xA : S)))
        simpa [AffineSubspace.coe_vsub, vsub_eq_sub] using hinner'
      intro h
      apply hNo_xyz
      have h' :
          ⟪(yA : E d) - (xA : E d), (zA : E d) - (xA : E d)⟫ < 0 := by
        simpa [ObtuseAt, hinner] using h
      simpa [ObtuseAt] using h'
    have hcardA' : A'.card = A.card := by
      simp [A']
    have hcardA'' : A''.card = A.card := by
      have hcardA'' : A''.card = A'.card := by
        have hinj : Set.InjOn f (A' : Set S) := fun _ _ _ _ h => f.injective h
        simpa [A''] using (Finset.card_image_iff.mpr hinj)
      simpa [hcardA'] using hcardA''
    have hle' : A''.card ≤ 2^k :=
      card_le_pow_two_of_noObtuse_of_span (d:=k) A'' hNo'' hspanA''
    have hpow : 2^k ≤ 2^d := by
      exact Nat.pow_le_pow_right (by decide) hk
    have hle : A.card ≤ 2^d := by
      have : A.card ≤ 2^k := by
        simpa [hcardA''] using hle'
      exact this.trans hpow
    exact hle
  ·
    have hA' : A = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hA
    simp [hA']

-- Final existence result ("some three points give an obtuse angle")
theorem exists_obtuse_of_card_succ_pow_two
  (A : Finset (E d))
  (hcard : A.card = (2^d) + 1) :
  ∃ x y z : E d, x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ObtuseAt (d:=d) x y z := by
  classical
  -- Contrapositive: if no obtuse triple exists, then NoObtuse A
  have : ¬ NoObtuse (d:=d) A := by
    -- From card = 2^d + 1, conclude ¬NoObtuse via the key bound:
    --   NoObtuse A → A.card ≤ 2^d
    intro hNo
    have hle : A.card ≤ 2^d := card_le_pow_two_of_noObtuse (d:=d) A hNo
    -- Contradiction with hcard
    have hle' : (2^d + 1) ≤ 2^d := by
      have hle' := hle
      simp [hcard] at hle'
    exact Nat.not_succ_le_self (2^d) hle'
  -- Unfold ¬NoObtuse to get an obtuse triple
  have h' := this
  unfold NoObtuse at h'
  push Not at h'
  rcases h' with ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, h⟩
  exact ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, h⟩

#print axioms exists_obtuse_of_card_succ_pow_two
-- 'Erdos224.exists_obtuse_of_card_succ_pow_two' depends on axioms: [propext,
-- Classical.choice,
-- Quot.sound]

end

end Erdos224
