import Wikipedia.SmoothSixDPoincare.ManifoldRegularValues
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Transverse translations for native source manifolds

Equal-dimensional Sard applied to the difference map on the product gives
one translation parameter transverse at every intersection in the supplied
open domains. Both sheet differentials are native manifold differentials.
-/

noncomputable section

open Set Function MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z F H K X Y : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ Z K}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace K Y] [IsManifold J ∞ Y]

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F]
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold J ∞ Y] in
/-- The difference map has the expected actual native product differential. -/
theorem mfderiv_sheetDifference {f : X → F} {g : Y → F} {x : X} {y : Y}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y) :
        D × Z →L[ℝ] F) =
      (-(mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F)).coprod
        (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F) := by
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change (mfderiv (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd - f ∘ Prod.fst) (x, y) :
    D × Z →L[ℝ] F) = (-A).coprod B
  have hf' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (f ∘ Prod.fst) (x, y) :=
    hf.comp (x, y) mdifferentiableAt_fst
  have hg' : MDifferentiableAt (I.prod J) 𝓘(ℝ, F) (g ∘ Prod.snd) (x, y) :=
    hg.comp (x, y) mdifferentiableAt_snd
  rw [mfderiv_sub hg' hf', mfderiv_comp (x, y) hg mdifferentiableAt_snd,
    mfderiv_comp (x, y) hf mdifferentiableAt_fst, mfderiv_fst, mfderiv_snd]
  apply ContinuousLinearMap.ext
  intro v
  change B v.2 - A v.1 = -(A v.1) + B v.2
  abel

omit [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F]
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ X] [IsManifold J ∞ Y] in
/-- Surjectivity of the difference differential is exactly the spanning condition for the sheets. -/
theorem surjective_sheetDifference_iff {f : X → F} {g : Y → F} {x : X} {y : Y}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hg : MDifferentiableAt J 𝓘(ℝ, F) g y) :
    Surjective (mfderiv (I.prod J) 𝓘(ℝ, F) (fun z : X × Y => g z.2 - f z.1) (x, y)) ↔
      Surjective ((mfderiv I 𝓘(ℝ, F) f x : D →L[ℝ] F).coprod
        (mfderiv J 𝓘(ℝ, F) g y : Z →L[ℝ] F)) := by
  rw [mfderiv_sheetDifference hf hg]
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Surjective ((-A).coprod B) ↔ Surjective (A.coprod B)
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change A (-v.1) + B v.2 = w
    change -(A v.1) + B v.2 = w at hv
    simpa only [map_neg] using hv
  · intro h w
    obtain ⟨v, hv⟩ := h w
    refine ⟨(-v.1, v.2), ?_⟩
    change -(A (-v.1)) + B v.2 = w
    change A v.1 + B v.2 = w at hv
    simpa only [map_neg, neg_neg] using hv

variable [LindelofSpace (X × Y)]

/-- A Haar-null set contains all nontransverse translation parameters. -/
theorem exists_null_exceptional_native_translations [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [IsAddHaarMeasure μ]
    {f : X → F} {g : Y → F} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    ∃ T : Set F, μ T = 0 ∧ ∀ a ∉ T, ∀ x ∈ U, ∀ y ∈ V, g y = f x + a →
      Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y)) := by
  let B : X × Y → F := fun z => g z.2 - f z.1
  have hB : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ B (U ×ˢ V) := by
    intro z hz
    have hfx : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => f w.1) z :=
      (hf.contMDiffAt (hU.mem_nhds hz.1)).comp z contMDiffAt_fst
    have hgy : ContMDiffAt (I.prod J) 𝓘(ℝ, F) ∞ (fun w : X × Y => g w.2) z :=
      (hg.contMDiffAt (hV.mem_nhds hz.2)).comp z contMDiffAt_snd
    exact (hgy.sub hfx).contMDiffWithinAt
  obtain ⟨T, hT, hgood⟩ := RegularValues.exists_null_exceptional_values_manifold μ
    (hU.prod hV) hB (by simpa only [Module.finrank_prod] using hdim)
  refine ⟨T, hT, ?_⟩
  intro a ha x hx y hy hxy
  have hvalue : B (x, y) = a := by
    change g y - f x = a
    rw [hxy, add_sub_cancel_left]
  have hs := hgood (x, y) ⟨hx, hy⟩ (by rwa [hvalue])
  change Surjective (mfderiv (I.prod J) 𝓘(ℝ, F)
    (fun z : X × Y => g z.2 - f z.1) (x, y)) at hs
  rw [mfderiv_sheetDifference
    ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    ((hg.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp))] at hs
  let A : D →L[ℝ] F := mfderiv I 𝓘(ℝ, F) f x
  let B' : Z →L[ℝ] F := mfderiv J 𝓘(ℝ, F) g y
  change Surjective ((-A).coprod B') at hs
  change Surjective (A.coprod B')
  intro w
  obtain ⟨v, hv⟩ := hs w
  refine ⟨(-v.1, v.2), ?_⟩
  change A (-v.1) + B' v.2 = w
  change -(A v.1) + B' v.2 = w at hv
  simpa only [map_neg] using hv

/-- The good native translation parameters are dense, with no measure assumed as input. -/
theorem dense_native_translations {f : X → F} {g : Y → F} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) (hg : ContMDiffOn J 𝓘(ℝ, F) ∞ g V)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ F) :
    Dense {a : F | ∀ x ∈ U, ∀ y ∈ V, g y = f x + a →
      Surjective ((mfderiv I 𝓘(ℝ, F) f x).coprod (mfderiv J 𝓘(ℝ, F) g y))} := by
  let _ : MeasurableSpace F := borel F
  let _ : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := Measure.addHaar
  obtain ⟨T, hT, hgood⟩ := exists_null_exceptional_native_translations μ hU hV hf hg hdim
  have hdense : Dense Tᶜ := by
    apply μ.dense_of_ae
    rw [ae_iff]
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using hT
  exact hdense.mono hgood

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates
