import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Native immersion of the parameter-retaining track

The track (t,x) ↦ (t,F(t,x)) is immersive whenever the spatial derivative
of F is injective. The first coordinate detects time, and the remaining
kernel is exactly the kernel of the spatial derivative. The original
target manifold and its product atlas are used throughout.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.FamilyTrack

open Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

def track (F : ℝ × E → N) (q : ℝ × E) : ℝ × N := (q.1, F q)

theorem track_smooth {F : ℝ × E → N} (hF : ContMDiff 𝓘(ℝ, ℝ × E) J ∞ F) :
    ContMDiff 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod J) ∞ (track F) :=
  contDiff_fst.contMDiff.prodMk hF

theorem injective_mfderiv_track {F : ℝ × E → N}
    (hF : ContMDiff 𝓘(ℝ, ℝ × E) J ∞ F) (q : ℝ × E)
    (hinj : Injective (mfderiv 𝓘(ℝ, E) J (fun x => F (q.1, x)) q.2)) :
    Injective (mfderiv 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod J) (track F) q) := by
  have hdF := hF.mdifferentiableAt (x := q) (by simp)
  have htSmooth : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (Prod.fst : ℝ × E → ℝ) :=
    contDiff_fst.contMDiff
  have hdt := htSmooth.mdifferentiableAt (x := q) (by simp)
  have htrack : mfderiv 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod J) (track F) q =
      (ContinuousLinearMap.fst ℝ ℝ E).prod (mfderiv 𝓘(ℝ, ℝ × E) J F q) := by
    change mfderiv 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod J)
      (fun r : ℝ × E => (r.1, F r)) q = _
    rw [mfderiv_prodMk hdt hdF, mfderiv_eq_fderiv, fderiv_fst]
    rfl
  have hs : HasFDerivAt (fun x : E => (q.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hds : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) (fun x : E => (q.1, x)) q.2 :=
    hs.differentiableAt.mdifferentiableAt
  have hspatial : mfderiv 𝓘(ℝ, E) J (fun x => F (q.1, x)) q.2 =
      (mfderiv 𝓘(ℝ, ℝ × E) J F q).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    change mfderiv 𝓘(ℝ, E) J (F ∘ (fun x : E => (q.1, x))) q.2 = _
    rw [mfderiv_comp q.2 hdF hds, mfderiv_eq_fderiv, hs.fderiv]
    rfl
  rw [htrack]
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨t, v⟩ hv
  have ht : t = 0 := congrArg Prod.fst hv
  subst t
  have hv' : mfderiv 𝓘(ℝ, E) J (fun x => F (q.1, x)) q.2 v = 0 := by
    rw [hspatial]
    exact congrArg Prod.snd hv
  have hvzero := (injective_iff_map_eq_zero _).mp hinj v hv'
  exact Prod.ext rfl hvzero

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [J.Boundaryless] [IsManifold J ∞ N]

theorem exists_open_injOn_track {F : ℝ × E → N}
    (hF : ContMDiff 𝓘(ℝ, ℝ × E) J ∞ F) (q : ℝ × E)
    (hinj : Injective (mfderiv 𝓘(ℝ, E) J (fun x => F (q.1, x)) q.2)) :
    ∃ V : Set (ℝ × E), IsOpen V ∧ q ∈ V ∧ InjOn (track F) V :=
  exists_open_injOn_of_injective_nativeDerivative
    (track_smooth hF) (injective_mfderiv_track hF q hinj)

end Wikipedia.HopfProblem.OrbitPair.FamilyTrack
