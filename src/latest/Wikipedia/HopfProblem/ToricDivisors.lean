import Wikipedia.HopfProblem.ToricStrata
import Mathlib.Data.Set.Card

/-!
# The central ray components

The lattice vertices labelling the vanishing chart coordinates are independent
of the chosen toric chart. They define the actual closed central components
`rayDivisor v`, whose affine equations are the corresponding coordinate
hyperplanes. The twisted lattice action translates their vertex labels.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

def vertex (s : Triangle) (j : Fin 3) : Fin 2 → ℤ := fun i => s.rays i.castSucc j

theorem vertex_eq_iff (s t : Triangle) (j k : Fin 3) :
    s.vertex j = t.vertex k ↔ ∀ i, s.rays i j = t.rays i k := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1
    · simp
  · intro h
    funext i
    exact h i.castSucc

theorem vertex_injective (s : Triangle) : Function.Injective s.vertex := by
  intro j k h
  exact equal_columns_of_left_inverse s.dual_rays ((vertex_eq_iff s s j k).mp h)

theorem transition_column_iff_vertex (s t : Triangle) (j k : Fin 3) :
    (∀ i, transition s t i j = if i = k then 1 else 0) ↔ s.vertex j = t.vertex k := by
  rw [vertex_eq_iff]
  constructor
  · intro h i
    have hc := congrFun (congrFun (transition_covariance s t) i) j
    simpa only [Matrix.mul_apply, h, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc.symm
  · intro h i
    have hc := congrFun (congrFun t.dual_rays i) k
    simpa only [transition, Matrix.mul_apply, h, Matrix.one_apply] using hc

@[simp] theorem vertex_shift (s : Triangle) (v : Fin 2 → ℤ) (j : Fin 3) :
    (s.shift v).vertex j = s.vertex j + v := by
  ext i
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    simp [vertex, shift, rays, hs] <;> ring

def chartBranches (s : Triangle) (z : CoordinateSpace 3) : Set (Fin 2 → ℤ) :=
  s.vertex '' {j | z j = 0}

theorem chartBranches_finite (s : Triangle) (z : CoordinateSpace 3) :
    (chartBranches s z).Finite := (Set.toFinite _).image _

theorem chartBranches_ncard (s : Triangle) (z : CoordinateSpace 3) :
    (chartBranches s z).ncard = zeroCount z := by
  rw [chartBranches, Set.ncard_image_of_injective _ (vertex_injective s)]
  rfl

theorem chartBranches_subset_change (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    chartBranches s z ⊆ chartBranches t (chartChange s t z) := by
  rintro v ⟨j, hj, rfl⟩
  obtain ⟨k, hk⟩ := column_single_of_zero (transition_heightOne s t)
    (by simpa only [chartChange_source] using hz) hj
  refine ⟨k, monomial_zero_of_column_single hj hk, ?_⟩
  exact ((transition_column_iff_vertex s t j k).mp hk).symm

theorem chartBranches_change (s t : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ (chartChange s t).source) :
    chartBranches t (chartChange s t z) = chartBranches s z := by
  apply subset_antisymm
  · have h := chartBranches_subset_change t s ((chartChange s t).map_source hz)
    have hi : chartChange t s (chartChange s t z) = z := (chartChange s t).left_inv hz
    rwa [hi] at h
  · exact chartBranches_subset_change s t hz

theorem chartBranches_mul (s : Triangle) (u z : CoordinateSpace 3) (hu : ∀ j, u j ≠ 0) :
    chartBranches s (u * z) = chartBranches s z := by
  unfold chartBranches
  congr 1
  ext j
  simp [hu]

theorem chartBranches_shift (s : Triangle) (v : Fin 2 → ℤ) (z : CoordinateSpace 3) :
    chartBranches (s.shift v) z = (fun w => w + v) '' chartBranches s z := by
  simp only [chartBranches, Set.image_image, vertex_shift]

end Wikipedia.HopfProblem.ToricFan.Triangle

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def branchVertices : Space → Set (Fin 2 → ℤ) := descend chartBranches

@[simp] theorem branchVertices_inclusion (s : Triangle) (z : CoordinateSpace 3) :
    branchVertices (inclusion s z) = chartBranches s z :=
  descend_inclusion chartBranches (fun s t _ hz => chartBranches_change s t hz) s z

theorem branchVertices_finite (x : Space) : (branchVertices x).Finite :=
  chartBranches_finite _ _

theorem branchVertices_ncard (x : Space) : (branchVertices x).ncard = branchCount x :=
  chartBranches_ncard _ _

theorem branchVertices_nonempty (x : Space) : (branchVertices x).Nonempty ↔ time x = 0 := by
  rw [← Set.ncard_pos (branchVertices_finite x), branchVertices_ncard, branchCount_pos_iff]

/-- The central component labelled by the height-one ray through `(v,1)`. -/
def rayDivisor (v : Fin 2 → ℤ) : Set Space := {x | v ∈ branchVertices x}

theorem mem_rayDivisor_inclusion (v : Fin 2 → ℤ) (s : Triangle) (z : CoordinateSpace 3) :
    inclusion s z ∈ rayDivisor v ↔ ∃ j, z j = 0 ∧ s.vertex j = v := by
  change v ∈ branchVertices (inclusion s z) ↔ _
  rw [branchVertices_inclusion]
  rfl

theorem mem_rayDivisor_vertex (s : Triangle) (j : Fin 3) (z : CoordinateSpace 3) :
    inclusion s z ∈ rayDivisor (s.vertex j) ↔ z j = 0 := by
  rw [mem_rayDivisor_inclusion]
  constructor
  · rintro ⟨k, hk, he⟩
    rwa [(vertex_injective s) he] at hk
  · intro hj
    exact ⟨j, hj, rfl⟩

theorem preimage_rayDivisor (v : Fin 2 → ℤ) (s : Triangle) :
    inclusion s ⁻¹' rayDivisor v = ⋃ j : Fin 3, {z | z j = 0 ∧ s.vertex j = v} := by
  ext z
  simp only [Set.mem_preimage, mem_rayDivisor_inclusion, Set.mem_iUnion, Set.mem_ofPred_eq]

theorem rayDivisor_isClosed (v : Fin 2 → ℤ) : IsClosed (rayDivisor v) := by
  rw [← isOpen_compl_iff, gluing.isOpen_iff]
  change ∀ s : Triangle, IsOpen (inclusion s ⁻¹' (rayDivisor v)ᶜ)
  intro s
  rw [Set.preimage_compl, isOpen_compl_iff, preimage_rayDivisor]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_eq (continuous_apply j) continuous_const).inter isClosed_const

theorem time_eq_zero_of_mem_rayDivisor {v : Fin 2 → ℤ} {x : Space}
    (hx : x ∈ rayDivisor v) : time x = 0 :=
  (branchVertices_nonempty x).mp ⟨v, hx⟩

theorem central_fibre_eq_rayDivisors : time ⁻¹' {0} = ⋃ v : Fin 2 → ℤ, rayDivisor v := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, rayDivisor,
    Set.mem_ofPred_eq, ← branchVertices_nonempty, Set.nonempty_def]

theorem branchVertices_translate (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (translate v x) = (fun w => w + v) '' branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [translate_inclusion, branchVertices_inclusion, branchVertices_inclusion, chartBranches_shift]

theorem branchVertices_torusAction (u : ActingTorus) (x : Space) :
    branchVertices (torusAction u x) = branchVertices x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  rw [torusAction_inclusion, branchVertices_inclusion, branchVertices_inclusion]
  exact chartBranches_mul s (factors s u) z (factors_nonzero s u)

theorem branchVertices_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    branchVertices (twistedTranslate C v x) =
      (fun w => w + cuspVector v) '' branchVertices x := by
  simp only [twistedTranslate, variableMultiplier, branchVertices_torusAction,
    branchVertices_translate]

theorem twistedTranslate_mem_rayDivisor (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (x : Space) :
    twistedTranslate C v x ∈ rayDivisor w ↔ x ∈ rayDivisor (w - cuspVector v) := by
  change w ∈ branchVertices (twistedTranslate C v x) ↔ _
  rw [branchVertices_twistedTranslate]
  constructor
  · rintro ⟨u, hu, he⟩
    have : u = w - cuspVector v := eq_sub_iff_add_eq.mpr he
    rwa [← this]
  · intro hx
    exact ⟨w - cuspVector v, hx, sub_add_cancel _ _⟩

end Wikipedia.HopfProblem.ToricSpace
