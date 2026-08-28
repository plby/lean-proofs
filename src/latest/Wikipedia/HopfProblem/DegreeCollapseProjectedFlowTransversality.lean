import Wikipedia.HopfProblem.DegreeCollapseTransverseLabelGeometry

/-!
# Projecting transverse flow sheets to their actual transverse labels

In genuine flow coordinates a sheet's transverse label is independent
of its time parameter. Projecting the full tangent sum then proves
transversality of the actual label sheets. Only equality of germs is
needed; global coordinate formulas are not assumed.
-/

noncomputable section

open Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem derivative_first_of_time_independent_label
    {F : ℝ × A → Z × ℝ} {f : A → Z}
    (hF : DifferentiableAt ℝ F 0) (hf : DifferentiableAt ℝ f 0)
    (hlabel : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2)) :
    ∀ u : ℝ × A, (fderiv ℝ F 0 u).1 = fderiv ℝ f 0 u.2 := by
  have hsnd : HasFDerivAt (fun u : ℝ × A => u.2) (ContinuousLinearMap.snd ℝ ℝ A) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ A).hasFDerivAt
  have hd : HasFDerivAt (fun u : ℝ × A => f u.2)
      ((fderiv ℝ f 0).comp (ContinuousLinearMap.snd ℝ ℝ A)) 0 :=
    hf.hasFDerivAt.comp (f := fun u : ℝ × A => u.2) 0 hsnd
  have heq : fderiv ℝ (fun u : ℝ × A => (F u).1) 0 =
      fderiv ℝ (fun u : ℝ × A => f u.2) 0 := hlabel.fderiv_eq
  rw [hF.hasFDerivAt.fst.fderiv, hd.fderiv] at heq
  intro u
  exact congrArg (fun L : (ℝ × A) →L[ℝ] Z => L u) heq

theorem transverse_labels_of_time_independent_flow_sheets
    {F : ℝ × A → Z × ℝ} {G : ℝ × B → Z × ℝ} {f : A → Z} {g : B → Z}
    (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (G u).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Surjective ((fderiv ℝ F 0).coprod (fderiv ℝ G 0))) :
    Surjective ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) := by
  have hfirstF := derivative_first_of_time_independent_label hF hf hlabelF
  have hfirstG := derivative_first_of_time_independent_label hG hg hlabelG
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans (z, 0)
  refine ⟨(u.2, v.2), ?_⟩
  change fderiv ℝ f 0 u.2 + fderiv ℝ g 0 v.2 = z
  rw [← hfirstF u, ← hfirstG v]
  exact congrArg Prod.fst huv

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
