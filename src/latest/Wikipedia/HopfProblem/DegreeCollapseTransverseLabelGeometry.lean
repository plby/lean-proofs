import Wikipedia.HopfProblem.DegreeCollapseTransverseProjectedEquiv

/-!
# Actual transverse label sheets give relative-coordinate transversality

Apply the genuine incoming label chart inverse to both sheets. Its full
derivative transports transversality, and the actual relative diagram and
local inverse identity identify the two transformed sheet germs. Unique
intersection alone is not used to assert transversality.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem label_sheets_transverse_in_incoming_chart
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hQsrc : (0 : A × B) ∈ Q.source) (hPsrc : (0 : A × B) ∈ P.source)
    (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z)
      (fun x : A => Q (x, 0)) (fun y : B => P (0, y)) 0 0) :
    Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, A × B)
      (fun x : A => P.symm (Q (x, 0))) 0).coprod
      (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, A × B) (fun y : B => P.symm (P (0, y))) 0)) := by
  have hcross : P ((0 : A), (0 : B)) = Q (0, 0) := hP0.trans hQ0.symm
  have htarget : Q ((0 : A), (0 : B)) ∈ P.target := by
    change Q (0 : A × B) ∈ P.target
    rw [hQ0, ← hP0]
    exact P.map_source' hPsrc
  have hι : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, A × B)
      (fun x : A => (x, (0 : B))) 0 :=
    ((contDiff_id : ContDiff ℝ ∞ (fun x : A => x)).prodMk contDiff_const).contMDiff.mdifferentiableAt
      (by simp)
  have hκ : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun y : B => ((0 : A), y)) 0 :=
    (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun y : B => y))).contMDiff.mdifferentiableAt
      (by simp)
  have hqdiff : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, Z) (fun x : A => Q (x, 0)) 0 :=
    (Q.mdifferentiableAt (by simp) hQsrc).comp (f := fun x : A => (x, (0 : B))) 0 hι
  have hpdiff : MDifferentiableAt 𝓘(ℝ, B) 𝓘(ℝ, Z) (fun y : B => P (0, y)) 0 :=
    (P.mdifferentiableAt (by simp) hPsrc).comp (f := fun y : B => ((0 : A), y)) 0 hκ
  exact ChartMapPerturbation.transverse_in_chart P.symm hqdiff hpdiff
    hcross htarget (htrans hcross)

theorem relative_label_sheet_germs
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hPsrc : (0 : A × B) ∈ P.source)
    (hHt : H.target ⊆ P.source) (hdiagram : ∀ u ∈ H.source, P (H u) = Q u) :
    ((fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0] (fun x : A => H (x, 0))) ∧
    ((fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0] (fun y : B => (0, y))) := by
  have hnearH : ∀ᶠ x : A in 𝓝 0, (x, (0 : B)) ∈ H.source :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually (H.open_source.mem_nhds h0)
  have heqH : (fun x : A => P.symm (Q (x, (0 : B)))) =ᶠ[𝓝 0]
      (fun x : A => H (x, 0)) := by
    filter_upwards [hnearH] with x hx
    rw [← hdiagram (x, 0) hx]
    exact P.left_inv' (hHt (H.map_source' hx))
  have hnearP : ∀ᶠ y : B in 𝓝 0, ((0 : A), y) ∈ P.source :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (P.open_source.mem_nhds hPsrc)
  have heqP : (fun y : B => P.symm (P ((0 : A), y))) =ᶠ[𝓝 0]
      (fun y : B => (0, y)) := by
    filter_upwards [hnearP] with y hy
    exact P.left_inv' hy
  exact ⟨heqH, heqP⟩

theorem relative_transverse_of_label_sheets
    (Q P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (H : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ H.source) (hH0 : H 0 = 0)
    (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hHs : H.source ⊆ Q.source) (hHt : H.target ⊆ P.source)
    (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z)
      (fun x : A => Q (x, 0)) (fun y : B => P (0, y)) 0 0) :
    NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => H (x, 0)) (fun y : B => (0, y)) 0 0 := by
  have hPsrc : (0 : A × B) ∈ P.source := by
    have hh := hHt (H.map_source' h0)
    rwa [hH0] at hh
  have ht := label_sheets_transverse_in_incoming_chart Q P (hHs h0) hPsrc hQ0 hP0 htrans
  obtain ⟨heqH, heqP⟩ := relative_label_sheet_germs Q P H h0 hPsrc hHt hdiagram
  rw [heqH.mfderiv_eq, heqP.mfderiv_eq] at ht
  exact fun _ => ht

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
