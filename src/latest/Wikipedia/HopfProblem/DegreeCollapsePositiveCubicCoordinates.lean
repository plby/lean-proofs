import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationModel
import Wikipedia.HopfProblem.DegreeCollapsePositiveClock
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Global smooth height coordinates for the positive cubic

The positive scalar cubic has derivative bounded below by a positive
constant, hence is a smooth diffeomorphism of the entire real line. Adding
the transverse quadratic form is a triangular coordinate change. Thus the
regular positive cubic becomes the first linear coordinate globally,
including the whole compact support of a birth template.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_positive_scalar_cubic_diffeomorph {a : ℝ} (ha : 0 < a) :
    ∃ e : ℝ ≃ₘ[ℝ] ℝ, ∀ s, e s = s ^ 3 / 3 + a ^ 2 * s := by
  let g : ℝ → ℝ := fun s => s ^ 3 / 3 + a ^ 2 * s
  have hg : ContDiff ℝ ∞ g := by unfold g; fun_prop
  have hd (s : ℝ) : HasDerivAt g (s ^ 2 + a ^ 2) s := by
    convert! (((hasDerivAt_id s).pow 3).div_const 3).add
      ((hasDerivAt_id s).const_mul (a ^ 2)) using 1 <;> simp
  have hpos (s : ℝ) : 0 < s ^ 2 + a ^ 2 := add_pos_of_nonneg_of_pos
    (sq_nonneg s) (sq_pos_of_pos ha)
  have hmono : StrictMono g := strictMono_of_hasDerivAt_pos hd hpos
  have hbound {s t : ℝ} (hst : s ≤ t) : a ^ 2 * (t - s) ≤ g t - g s :=
    mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; exact le_add_of_nonneg_left (sq_nonneg x)) hst
  have hzero : g 0 = 0 := by simp [g]
  have hsurj : Surjective g := by
    intro y
    apply mem_range_of_exists_le_of_exists_ge hg.continuous
    · refine ⟨min 0 (y / a ^ 2), ?_⟩
      have hh := hbound (min_le_left 0 (y / a ^ 2))
      have hm : a ^ 2 * min 0 (y / a ^ 2) ≤ y := by
        calc
          a ^ 2 * min 0 (y / a ^ 2) ≤ a ^ 2 * (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg a)
          _ = y := by field_simp
      rw [hzero] at hh
      linarith
    · refine ⟨max 0 (y / a ^ 2), ?_⟩
      have hh := hbound (le_max_left 0 (y / a ^ 2))
      have hm : y ≤ a ^ 2 * max 0 (y / a ^ 2) := by
        calc
          y = a ^ 2 * (y / a ^ 2) := by field_simp
          _ ≤ a ^ 2 * max 0 (y / a ^ 2) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg a)
      rw [hzero] at hh
      linarith
  let c : ℝ ≃o ℝ := hmono.orderIsoOfSurjective g hsurj
  have hi : ContDiff ℝ ∞ c.toHomeomorph.symm :=
    c.toHomeomorph.contDiff_symm_deriv (fun s => (hpos s).ne') hd hg
  let e : ℝ ≃ₘ[ℝ] ℝ := {
    toEquiv := c.toEquiv
    contMDiff_toFun := hg.contMDiff
    contMDiff_invFun := hi.contMDiff }
  exact ⟨e, fun _ => rfl⟩

theorem exists_positive_cubic_height_diffeomorph {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∃ D : Model m ≃ₘ[ℝ] Model m, ∀ p, D p = (cubic σ (a ^ 2) p, p.2) := by
  obtain ⟨e, he⟩ := exists_positive_scalar_cubic_diffeomorph ha
  let Q : (Fin m → ℝ) → ℝ := fun z => ∑ i, σ i * z i ^ 2
  have hQ : ContDiff ℝ ∞ Q := by unfold Q; fun_prop
  have hec : ContDiff ℝ ∞ e := contMDiff_iff_contDiff.mp e.contMDiff
  have hei : ContDiff ℝ ∞ e.symm := contMDiff_iff_contDiff.mp e.symm.contMDiff
  let D : Model m ≃ₘ[ℝ] Model m := {
    toFun := fun p => (e p.1 + Q p.2, p.2)
    invFun := fun p => (e.symm (p.1 - Q p.2), p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp
    contMDiff_toFun := ((hec.comp contDiff_fst |>.add (hQ.comp contDiff_snd)).prodMk
      contDiff_snd).contMDiff
    contMDiff_invFun := ((hei.comp (contDiff_fst.sub (hQ.comp contDiff_snd))).prodMk
      contDiff_snd).contMDiff }
  refine ⟨D, ?_⟩
  intro p
  change (e p.1 + Q p.2, p.2) = _
  rw [he]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
