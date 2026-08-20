/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos909.EuclideanGeometry
import Mathlib.Topology.Baire.Lemmas

/-!
# Generic directions on a Euclidean sphere

For a nonzero real subspace `Q`, the points of a positive-radius sphere which
do not belong to `Qᗮ` form an open dense subset.  Finite intersections of
these sets are again open dense, and therefore contain a countable dense
subset of the sphere.
-/

open Filter Set Topology
open Metric

namespace Erdos909

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directions on the radius-`R` sphere which are not orthogonal to `Q`. -/
def goodSphereDirections (R : ℝ) (Q : Submodule ℝ E) :
    Set (sphere (0 : E) R) :=
  {x | (x : E) ∉ Qᗮ}

theorem isOpen_goodSphereDirections (R : ℝ) (Q : Submodule ℝ E) :
    IsOpen (goodSphereDirections R Q) := by
  change IsOpen (Subtype.val ⁻¹' (Qᗮ : Set E)ᶜ)
  exact Q.isClosed_orthogonal.isOpen_compl.preimage continuous_subtype_val

private def normalizedPerturbation (R t : ℝ) (x q : E) : E :=
  (R / ‖x + t • q‖) • (x + t • q)

private theorem add_smul_ne_zero_of_mem_orthogonal
    {R t : ℝ} (hR : 0 < R) {x : sphere (0 : E) R}
    {Q : Submodule ℝ E} {q : E} (hq : q ∈ Q) (hx : (x : E) ∈ Qᗮ) :
    (x : E) + t • q ≠ 0 := by
  intro hzero
  have hxnorm : ‖(x : E)‖ = R := by
    simpa only [mem_sphere_zero_iff_norm] using x.property
  have hinner : @inner ℝ E _ (x : E) (x : E) = 0 := by
    have horth : @inner ℝ E _ q (x : E) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hq hx
    have := congrArg (fun z : E => @inner ℝ E _ z (x : E)) hzero
    simpa only [inner_add_left, real_inner_smul_left, inner_zero_left, horth,
      mul_zero, zero_add, add_zero] using this
  have hxzero : (x : E) = 0 := inner_self_eq_zero.mp hinner
  rw [hxzero, norm_zero] at hxnorm
  linarith

private theorem normalizedPerturbation_mem_sphere
    {R t : ℝ} (hR : 0 < R) {x : sphere (0 : E) R}
    {Q : Submodule ℝ E} {q : E} (hq : q ∈ Q) (hx : (x : E) ∈ Qᗮ) :
    normalizedPerturbation R t (x : E) q ∈ sphere (0 : E) R := by
  have hz : (x : E) + t • q ≠ 0 :=
    add_smul_ne_zero_of_mem_orthogonal hR hq hx
  rw [mem_sphere_zero_iff_norm, normalizedPerturbation, norm_smul, Real.norm_eq_abs]
  have hn : 0 < ‖(x : E) + t • q‖ := norm_pos_iff.mpr hz
  rw [abs_of_pos (div_pos hR hn), div_mul_cancel₀ R hn.ne']

private theorem normalizedPerturbation_zero
    {R : ℝ} (hR : 0 < R) (x : sphere (0 : E) R) (q : E) :
    normalizedPerturbation R 0 (x : E) q = x := by
  have hxnorm : ‖(x : E)‖ = R := by
    simpa only [mem_sphere_zero_iff_norm] using x.property
  simp only [normalizedPerturbation, zero_smul, add_zero, hxnorm,
    div_self hR.ne', one_smul]

private theorem normalizedPerturbation_not_mem_orthogonal
    {R t : ℝ} (hR : 0 < R) (ht : t ≠ 0) {x : sphere (0 : E) R}
    {Q : Submodule ℝ E} {q : E} (hq : q ∈ Q) (hq0 : q ≠ 0)
    (hx : (x : E) ∈ Qᗮ) :
    normalizedPerturbation R t (x : E) q ∉ Qᗮ := by
  intro hmem
  have hzero : @inner ℝ E _ q (normalizedPerturbation R t (x : E) q) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hq hmem
  have hxq : @inner ℝ E _ q (x : E) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hq hx
  have hz : (x : E) + t • q ≠ 0 :=
    add_smul_ne_zero_of_mem_orthogonal hR hq hx
  have hscalar : R / ‖(x : E) + t • q‖ ≠ 0 :=
    div_ne_zero hR.ne' (norm_ne_zero_iff.mpr hz)
  have hqq : @inner ℝ E _ q q ≠ 0 := inner_self_ne_zero.mpr hq0
  rw [normalizedPerturbation, real_inner_smul_right, inner_add_right,
    real_inner_smul_right, hxq, zero_add] at hzero
  exact (mul_ne_zero hscalar (mul_ne_zero ht hqq)) hzero

theorem dense_goodSphereDirections {R : ℝ} (hR : 0 < R)
    {Q : Submodule ℝ E} (hQ : Q ≠ ⊥) :
    Dense (goodSphereDirections R Q) := by
  obtain ⟨q, hq, hq0⟩ := Q.ne_bot_iff.mp hQ
  rw [dense_iff_closure_eq]
  apply eq_univ_of_forall
  intro x
  by_cases hx : (x : E) ∈ Qᗮ
  · let f : ℝ → sphere (0 : E) R := fun t =>
      ⟨normalizedPerturbation R t (x : E) q,
        normalizedPerturbation_mem_sphere hR hq hx⟩
    have hf : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
      rw [tendsto_subtype_rng]
      have hz : ContinuousAt (fun t : ℝ => (x : E) + t • q) 0 :=
        continuousAt_const.add (continuousAt_id.smul_const q)
      have hx0 : (x : E) ≠ 0 := by
        intro hzero
        have hxnorm : ‖(x : E)‖ = R := by
          simpa only [mem_sphere_zero_iff_norm] using x.property
        rw [hzero, norm_zero] at hxnorm
        linarith
      have hn0 : ‖(x : E) + (0 : ℝ) • q‖ ≠ 0 := by
        simpa only [zero_smul, add_zero, norm_ne_zero_iff] using hx0
      have hcont : ContinuousAt (normalizedPerturbation R · (x : E) q) 0 :=
        (continuousAt_const.div hz.norm hn0).smul hz
      have hlim : Tendsto (normalizedPerturbation R · (x : E) q)
          (𝓝 (0 : ℝ)) (𝓝 (x : E)) := by
        change Tendsto (normalizedPerturbation R · (x : E) q) (𝓝 (0 : ℝ))
          (𝓝 (normalizedPerturbation R 0 (x : E) q)) at hcont
        rw [normalizedPerturbation_zero hR x q] at hcont
        exact hcont
      exact hlim.mono_left inf_le_left
    apply mem_closure_of_tendsto hf
    filter_upwards [self_mem_nhdsWithin] with t ht
    change normalizedPerturbation R t (x : E) q ∉ Qᗮ
    exact normalizedPerturbation_not_mem_orthogonal hR (by simpa using ht) hq hq0 hx
  · exact subset_closure hx

/-- Simultaneously good directions for a finite family of subspaces. -/
def goodSphereDirectionsFinset (R : ℝ) (F : Finset (Submodule ℝ E)) :
    Set (sphere (0 : E) R) :=
  ⋂ Q ∈ F, goodSphereDirections R Q

theorem isOpen_goodSphereDirectionsFinset (R : ℝ)
    (F : Finset (Submodule ℝ E)) :
    IsOpen (goodSphereDirectionsFinset R F) := by
  exact isOpen_biInter_finset fun Q _ => isOpen_goodSphereDirections R Q

theorem dense_goodSphereDirectionsFinset {R : ℝ} (hR : 0 < R)
    {F : Finset (Submodule ℝ E)} (hF : ∀ Q ∈ F, Q ≠ ⊥) :
    Dense (goodSphereDirectionsFinset R F) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [goodSphereDirectionsFinset]
  | @insert Q F hQF ih =>
      have heq : goodSphereDirectionsFinset R (insert Q F) =
          goodSphereDirections R Q ∩ goodSphereDirectionsFinset R F := by
        ext x
        simp [goodSphereDirectionsFinset]
      rw [heq]
      exact (dense_goodSphereDirections hR (hF Q (Finset.mem_insert_self Q F))).inter_of_isOpen_left
        (ih fun P hPF => hF P (Finset.mem_insert_of_mem hPF))
        (isOpen_goodSphereDirections R Q)

theorem exists_countable_dense_subset_goodSphereDirectionsFinset
    [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R)
    {F : Finset (Submodule ℝ E)} (hF : ∀ Q ∈ F, Q ≠ ⊥) :
    ∃ D : Set (sphere (0 : E) R),
      D ⊆ goodSphereDirectionsFinset R F ∧ D.Countable ∧ Dense D := by
  exact (dense_goodSphereDirectionsFinset hR hF).exists_countable_dense_subset

end

end Erdos909
