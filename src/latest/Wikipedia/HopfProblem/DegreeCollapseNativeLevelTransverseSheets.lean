import Wikipedia.HopfProblem.DegreeCollapseTimeLiftTransversality

/-!
# Native transverse flow sheets from transverse level maps

Adding the free time direction and postcomposing with the genuine native
cylinder transports level transversality to the actual manifold. The
result only needs the coordinate formulas as germs of the actual sheets.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z E HA HB HZ HE X Y N M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HA] [TopologicalSpace HB] [TopologicalSpace HZ] [TopologicalSpace HE]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  {J : ModelWithCorners ℝ Z HZ} {J' : ModelWithCorners ℝ E HE}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
  [TopologicalSpace N] [ChartedSpace HZ N] [TopologicalSpace M] [ChartedSpace HE M]

theorem native_transverse_sheets_of_level_maps
    (C : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) J' (N × ℝ) M ∞)
    {f : X → N} {g : Y → N} {v : X → ℝ} {w : Y → ℝ} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x)
    (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y)
    {s t : ℝ} (hphase : t + w y = s + v x) (hsource : (f x, s + v x) ∈ C.source) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) J'
      (fun p : X × ℝ => C (f p.1, p.2 + v p.1))
      (fun p : Y × ℝ => C (g p.1, p.2 + w p.1)) (x, s) (y, t) := by
  let F : X × ℝ → N × ℝ := fun p => (f p.1, p.2 + v p.1)
  let G : Y × ℝ → N × ℝ := fun p => (g p.1, p.2 + w p.1)
  have hF : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) F (x, s) :=
    (hf.comp (x, s) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hv.comp (x, s) mdifferentiableAt_fst))
  have hG : MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) G (y, t) :=
    (hg.comp (y, t) mdifferentiableAt_fst).prodMk
      (mdifferentiableAt_snd.add (hw.comp (y, t) mdifferentiableAt_fst))
  have hcross : G (y, t) = F (x, s) := Prod.ext hxy hphase
  exact (native_transversality_partial_diffeomorph_iff C hF hG hcross hsource).mp
    (native_transversality_time_lifts hf hg hv hw hxy htrans s t)

theorem native_transverse_sheet_germs_of_level_maps
    (C : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) J' (N × ℝ) M ∞)
    {f : X → N} {g : Y → N} {v : X → ℝ} {w : Y → ℝ} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x)
    (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y)
    {s t : ℝ} (hphase : t + w y = s + v x) (hsource : (f x, s + v x) ∈ C.source)
    {F : X × ℝ → M} {G : Y × ℝ → M}
    (hF : F =ᶠ[𝓝 (x, s)] (fun p : X × ℝ => C (f p.1, p.2 + v p.1)))
    (hG : G =ᶠ[𝓝 (y, t)] (fun p : Y × ℝ => C (g p.1, p.2 + w p.1))) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) J' F G (x, s) (y, t) := by
  have ht := native_transverse_sheets_of_level_maps C hf hg hv hw hxy htrans hphase hsource
  have hcross : C (g y, t + w y) = C (f x, s + v x) :=
    congrArg C (Prod.ext hxy hphase)
  have hFd : (mfderiv (I.prod 𝓘(ℝ, ℝ)) J' F (x, s) : (A × ℝ) →L[ℝ] E) =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) J'
        (fun p : X × ℝ => C (f p.1, p.2 + v p.1)) (x, s) := hF.mfderiv_eq
  have hGd : (mfderiv (I'.prod 𝓘(ℝ, ℝ)) J' G (y, t) : (B × ℝ) →L[ℝ] E) =
      mfderiv (I'.prod 𝓘(ℝ, ℝ)) J'
        (fun p : Y × ℝ => C (g p.1, p.2 + w p.1)) (y, t) := hG.mfderiv_eq
  intro _
  rw [hFd, hGd]
  exact ht hcross

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
