import StackExchange.Puzzling139335.CentralRotation.BoundaryCoordinates

/-! # Propagating actual boundary lifts through the orbit gap -/

open Set

namespace Puzzling139335.CentralRotation.BoundaryLifts

variable {M Γ N : Set Plane} {d : BoundaryCoordinates M Γ N}
variable {g h : Plane ≃ᵃⁱ[ℝ] Plane} (L : BoundaryLifts d g h)

/-- The first orbit arc has the reversed parameter inherited from the cut. -/
def firstParameter (t : ℝ) : ℝ := L.H (L.G.symm (1 - t))

theorem firstParameter_continuous : Continuous L.firstParameter :=
  L.H.continuous.comp L.inverse_cut_lift_continuous

theorem firstParameter_antitone : StrictAnti L.firstParameter := by
  intro s t hst
  exact L.H_increasing (L.inverse_cut_lift_antitone hst)

/-- The parameter of the `(n+1)`st orbit arc before the first overlap. -/
def iterateParameter (n : ℕ) (t : ℝ) : ℝ :=
  (L.stepParameter^[n]) (L.firstParameter t)

theorem iterateParameter_continuous (n : ℕ) : Continuous (L.iterateParameter n) :=
  (L.stepParameter_continuous.iterate n).comp L.firstParameter_continuous

theorem iterateParameter_antitone (n : ℕ) : StrictAnti (L.iterateParameter n) := by
  intro s t hst
  exact (L.stepParameter_increasing.iterate n) (L.firstParameter_antitone hst)

/-- At an outer point whose inverse image is also outer, the step has the
increasing parameter map `H ∘ G⁻¹`. -/
theorem step_agrees (F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hF : ∀ x, F x = h (g.symm x)) {t : ℝ}
    (htN : circleParam d.outerParam t ∈ N)
    (htM : g.symm (circleParam d.outerParam t) ∈ M) :
    F (circleParam d.outerParam t) = circleParam d.outerParam (L.stepParameter t) := by
  have hinverse : g.symm (circleParam d.outerParam t) =
      circleParam d.leftParam (L.G.symm t) := by
    rw [d.outer_eq_right_of_mem htN, L.inverse_to_left]
  have hmem : circleParam d.leftParam (L.G.symm t) ∈ M := hinverse ▸ htM
  calc
    F (circleParam d.outerParam t) = h (g.symm (circleParam d.outerParam t)) := hF _
    _ = h (circleParam d.leftParam (L.G.symm t)) := congrArg h hinverse
    _ = h (circleParam d.outerParam (L.G.symm t)) := congrArg h (d.left_eq_outer_of_mem hmem)
    _ = circleParam d.outerParam (L.stepParameter t) := (L.outer_to_outer _).symm

theorem step_agrees_on_gap (F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hF : ∀ x, F x = h (g.symm x)) {Jopen : Set Plane}
    (hpreimage : g.symm '' (N \ Jopen) ⊆ M) {t : ℝ}
    (ht : circleParam d.outerParam t ∈ N \ Jopen) :
    F (circleParam d.outerParam t) = circleParam d.outerParam (L.stepParameter t) :=
  L.step_agrees F hF ht.1 (hpreimage (mem_image_of_mem g.symm ht))

/-- The actual first image of the cut agrees with the reversed lift. -/
theorem first_agrees (F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hF : ∀ x, F x = h (g.symm x)) (hI : g.symm '' Γ ⊆ M)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    F (circleParam d.leftParam t) = circleParam d.outerParam (L.firstParameter t) := by
  have hcut : circleParam d.leftParam t ∈ Γ :=
    d.leftCutImage.subset (mem_image_of_mem (circleParam d.leftParam) ht)
  have hmem : circleParam d.leftParam (L.G.symm (1 - t)) ∈ M := by
    rw [← L.inverse_cut_agrees ht]
    exact hI (mem_image_of_mem g.symm hcut)
  calc
    F (circleParam d.leftParam t) = h (g.symm (circleParam d.leftParam t)) := hF _
    _ = h (circleParam d.leftParam (L.G.symm (1 - t))) := congrArg h (L.inverse_cut_agrees ht)
    _ = h (circleParam d.outerParam (L.G.symm (1 - t))) :=
      congrArg h (d.left_eq_outer_of_mem hmem)
    _ = circleParam d.outerParam (L.firstParameter t) := (L.outer_to_outer _).symm

/-- Every step before the first overlap preserves the direction of the
previous arc, so the actual `(n+1)`st image retains its reversed lift. -/
theorem iterate_agrees (F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hF : ∀ x, F x = h (g.symm x)) (hI : g.symm '' Γ ⊆ M)
    {Jopen : Set Plane} (hpreimage : g.symm '' (N \ Jopen) ⊆ M)
    (n : ℕ) (hbefore : ∀ k : ℕ, 1 ≤ k → k ≤ n → ((F : Plane → Plane)^[k]) '' Γ ⊆ N \ Jopen)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    ((F : Plane → Plane)^[n + 1]) (circleParam d.leftParam t) =
      circleParam d.outerParam (L.iterateParameter n t) := by
  induction n with
  | zero => simpa only [Nat.zero_add, iterateParameter, Function.iterate_zero_apply,
      Function.iterate_one] using L.first_agrees F hF hI ht
  | succ n ih =>
      have hprev := ih (fun k hk hkn => hbefore k hk (hkn.trans (Nat.le_succ n)))
      have hxcut : circleParam d.leftParam t ∈ Γ :=
        d.leftCutImage.subset (mem_image_of_mem (circleParam d.leftParam) ht)
      have hgap : circleParam d.outerParam (L.iterateParameter n t) ∈ N \ Jopen := by
        rw [← hprev]
        exact hbefore (n + 1) (by omega) le_rfl
          (mem_image_of_mem ((F : Plane → Plane)^[n + 1]) hxcut)
      simpa only [iterateParameter, Function.iterate_succ_apply'] using
        (congrArg F hprev).trans (L.step_agrees_on_gap F hF hpreimage hgap)

/-- The direct image of the cut has increasing outer-boundary parameters. -/
theorem image_cut_agrees (hJ : g '' Γ ⊆ N) {t : ℝ}
    (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    g (circleParam d.leftParam t) = circleParam d.outerParam (L.G t) := by
  have hcut : circleParam d.leftParam t ∈ Γ :=
    d.leftCutImage.subset (mem_image_of_mem (circleParam d.leftParam) ht)
  have hmem : circleParam d.rightParam (L.G t) ∈ N := by
    rw [L.left_to_right]
    exact hJ (mem_image_of_mem g hcut)
  exact (L.left_to_right t).symm.trans (d.right_eq_outer_of_mem hmem)

end Puzzling139335.CentralRotation.BoundaryLifts
