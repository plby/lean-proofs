import ErdosProblems.Erdos587.NVDevelopment
import ErdosProblems.Erdos587.ReserveHomogeneity

/-! # An inner lattice-basis box in a proper convex progression -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

noncomputable def deltaBasisBox (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ) :
    GeneralizedAP where
  rank := X.rank
  base := X.base - X.eval ((latticeCoordinates b).symm (fun i => (R i : ℤ)))
  step i := X.eval (b i)
  length i := 2 * R i

lemma deltaBasisBox_eval (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    (x : (deltaBasisBox X b R).Param) :
    (deltaBasisBox X b R).eval x = X.base + X.eval ((latticeCoordinates b).symm
      (fun i => (x i : ℤ) - R i)) := by
  change (X.base - X.eval ((latticeCoordinates b).symm (fun i => (R i : ℤ)))) +
    ∑ i : Fin X.rank, (x i : ℤ) * X.eval (b i) =
      X.base + X.eval ((latticeCoordinates b).symm
        ((fun i : Fin X.rank => (x i : ℤ)) - (fun i : Fin X.rank => (R i : ℤ))))
  rw [map_sub, map_sub, eval_latticeSynthesis, eval_latticeSynthesis]
  ring

lemma deltaBasisBox_coeff_bound (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    (x : (deltaBasisBox X b R).Param) (i : Fin X.rank) :
    |(x i : ℤ) - R i| ≤ (R i : ℤ) := by
  have hx := (x i).isLt
  change (x i : ℕ) < 2 * R i + 1 at hx
  rw [abs_le]
  constructor <;> omega

lemma deltaBasisBox_carrier_subset (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    (hmem : ∀ u : Fin X.rank → ℤ, (∀ i, |u i| ≤ (R i : ℤ)) →
      intCastVec ((latticeCoordinates b).symm u) ∈ X.body) :
    ((deltaBasisBox X b R).carrier : Set ℤ) ⊆ X.carrier := by
  intro z hz
  obtain ⟨x, rfl⟩ := (deltaBasisBox X b R).mem_carrier_iff.mp hz
  refine ⟨(latticeCoordinates b).symm (fun i => (x i : ℤ) - R i),
    hmem _ (deltaBasisBox_coeff_bound X b R x), ?_⟩
  exact (deltaBasisBox_eval X b R x).symm

lemma deltaBasisBox_proper (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    (hmem : ∀ u : Fin X.rank → ℤ, (∀ i, |u i| ≤ (R i : ℤ)) →
      intCastVec ((latticeCoordinates b).symm u) ∈ X.body)
    (hproper : X.SProper 1) : (deltaBasisBox X b R).Proper := by
  intro x y hxy
  rw [deltaBasisBox_eval, deltaBasisBox_eval] at hxy
  let ux : Fin X.rank → ℤ := fun i => (x i : ℤ) - R i
  let uy : Fin X.rank → ℤ := fun i => (y i : ℤ) - R i
  have hx := hmem ux (deltaBasisBox_coeff_bound X b R x)
  have hy := hmem uy (deltaBasisBox_coeff_bound X b R y)
  have heq : (latticeCoordinates b).symm ux = (latticeCoordinates b).symm uy :=
    hproper ⟨_, hx, by simp⟩ ⟨_, hy, by simp⟩ (add_left_cancel hxy)
  have hu : ux = uy := (latticeCoordinates b).symm.injective heq
  funext i
  apply Fin.ext
  have hi := congrFun hu i
  have hcast : (x i : ℤ) = (y i : ℤ) := by dsimp only [ux, uy] at hi; omega
  exact_mod_cast hcast

lemma deltaBasisBox_homogeneous (X : ConvexProgression)
    (b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ)) (R : Fin X.rank → ℕ)
    (hbase : ∃ c : Fin X.rank → ℤ, X.eval c = X.base) :
    (deltaBasisBox X b R).HasHomogeneousBase := by
  obtain ⟨c, hc⟩ := hbase
  intro k hk
  have hdiv (v : Fin X.rank → ℤ) : k ∣ X.eval v := by
    rw [← (latticeCoordinates b).symm_apply_apply v, eval_latticeSynthesis]
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (hk i) _
  change k ∣ X.base - X.eval ((latticeCoordinates b).symm (fun i => (R i : ℤ)))
  rw [← hc]
  exact dvd_sub (hdiv c) (hdiv _)

lemma delta_adapted_inner_box_mem (X : ConvexProgression) (D : MahlerBoxData X)
    (u : Fin X.rank → ℤ)
    (hu : ∀ i, |u i| ≤ (⌊D.bound i / D.scale⌋₊ : ℤ)) :
    intCastVec ((latticeCoordinates D.basis).symm u) ∈ X.body := by
  have hscale : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
  have hcoord (i : Fin X.rank) : |(u i : ℝ)| ≤ D.bound i / D.scale := by
    have hh : ((|u i| : ℤ) : ℝ) ≤ (⌊D.bound i / D.scale⌋₊ : ℝ) := by exact_mod_cast hu i
    rw [Int.cast_abs] at hh
    exact hh.trans (Nat.floor_le (div_nonneg (D.bound_nonneg i) hscale.le))
  have hgauge : gauge X.body (intCastVec ((latticeCoordinates D.basis).symm u)) ≤ 1 := by
    apply (D.gauge_synthesis_le u).trans
    calc
      _ ≤ ∑ i, (D.bound i / D.scale) * D.cost i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hcoord i) (D.cost_nonneg i)
      _ = (∑ i, D.bound i * D.cost i) / D.scale := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (∑ i, (D.bound i + 1) * D.cost i) / D.scale := by
        apply div_le_div_of_nonneg_right _ hscale.le
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (by linarith) (D.cost_nonneg i)
      _ ≤ (D.scale : ℝ) / D.scale := div_le_div_of_nonneg_right D.scale_bound hscale.le
      _ = 1 := div_self hscale.ne'
  obtain ⟨z, hz, heq⟩ := MahlerBoxData.mem_bodyDilate_of_gauge_le
    (show (0 : ℝ) < 1 by norm_num) hgauge
  have hzv : z = intCastVec ((latticeCoordinates D.basis).symm u) := by
    simpa only [one_smul] using heq
  exact hzv ▸ hz

theorem delta_adapted_inner_box (X : ConvexProgression) (D : MahlerBoxData X)
    (hproper : X.SProper 1) (hbase : ∃ c : Fin X.rank → ℤ, X.eval c = X.base) :
    let Q := deltaBasisBox X D.basis (fun i => ⌊D.bound i / D.scale⌋₊)
    Q.Proper ∧ Q.HasHomogeneousBase ∧ (Q.carrier : Set ℤ) ⊆ X.carrier := by
  exact ⟨deltaBasisBox_proper X D.basis _ (delta_adapted_inner_box_mem X D) hproper,
    deltaBasisBox_homogeneous X D.basis _ hbase,
    deltaBasisBox_carrier_subset X D.basis _ (delta_adapted_inner_box_mem X D)⟩

end Erdos587.GeneralizedAP
