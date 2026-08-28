import Wikipedia.HopfProblem.OrbitPairAmbientCoincidenceTransport
import Wikipedia.HopfProblem.OrbitPairSynchronizedPairs
import Wikipedia.HopfProblem.OrbitPairFamilyDoublePoints

/-!
# Common ambient changes of a native surface family

Postcomposing each slice with an ambient diffeomorphism preserves its exact
ordered collision set, spatial immersion, and synchronized transversality.
The forward ambient family is jointly smooth. No jointly smooth inverse
family is needed for these conclusions.

This is a transport theorem, not a construction of the ambient perturbation
that makes a prescribed projected corridor immersive.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]

def ambientFamily (F : ℝ × M → N) (A : ℝ × N → N) (p : ℝ × M) : N :=
  A (p.1, F p)

theorem ambientFamily_smooth {F : ℝ × M → N} {A : ℝ × N → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ (ambientFamily F A) :=
  hA.comp (contMDiff_fst.prodMk hF)

theorem doublePoints_ambientFamily (F : ℝ × M → N) (A : ℝ × N → N)
    (hi : ∀ t, Injective (fun y => A (t, y))) :
    FamilyDoublePoints.doublePoints (ambientFamily F A) =
      FamilyDoublePoints.doublePoints F := by
  ext p
  change (p.2.1 ≠ p.2.2 ∧ A (p.1, F (p.1, p.2.1)) =
      A (p.1, F (p.1, p.2.2))) ↔
    (p.2.1 ≠ p.2.2 ∧ F (p.1, p.2.1) = F (p.1, p.2.2))
  exact and_congr_right (fun _ => (hi p.1).eq_iff)

theorem ambientFamily_fixed_time (F : ℝ × M → N) (A : ℝ × N → N)
    {t : ℝ} (hA : ∀ y, A (t, y) = y) (x : M) :
    ambientFamily F A (t, x) = F (t, x) := hA _

theorem ambientFamily_injective_spatial {F : ℝ × M → N} {A : ℝ × N → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A)
    (hiF : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (hiA : ∀ t y, Injective (mfderiv J J (fun z => A (t, z)) y)) :
    ∀ t x, Injective (mfderiv I J (fun y => ambientFamily F A (t, y)) x) := by
  intro t x
  have hf : ContMDiff I J ∞ (fun y => F (t, y)) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id)
  have ha : ContMDiff J J ∞ (fun y => A (t, y)) :=
    hA.comp (contMDiff_const.prodMk contMDiff_id)
  let B : G →L[ℝ] G := mfderiv J J (fun y => A (t, y)) (F (t, x))
  let C : E →L[ℝ] G := mfderiv I J (fun y => F (t, y)) x
  let D : E →L[ℝ] G := mfderiv I J (fun y => ambientFamily F A (t, y)) x
  have hD : D = B.comp C := mfderiv_comp x
    (ha.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  change Injective D
  rw [hD]
  exact (hiA t (F (t, x))).comp (hiF t x)

theorem ambientFamily_regularOn_iff {F : ℝ × M → N} {A : ℝ × N → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A)
    (hiA : ∀ t, Injective (fun y => A (t, y)))
    (hbA : ∀ t y, Bijective (mfderiv J J (fun z => A (t, z)) y))
    (S : Set (ℝ × (M × M))) :
    SynchronizedPairs.RegularOn (I := I) (J := J) (ambientFamily F A) S ↔
      SynchronizedPairs.RegularOn (I := I) (J := J) F S := by
  have he (q : ℝ × (M × M))
      (hq : F (SynchronizedPairs.first q) = F (SynchronizedPairs.second q)) :
      Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
          (ambientFamily F A ∘ SynchronizedPairs.first)
          (ambientFamily F A ∘ SynchronizedPairs.second) q ↔
        Coincidence.TransverseAt (I := 𝓘(ℝ, ℝ).prod (I.prod I)) (J := J)
          (F ∘ SynchronizedPairs.first) (F ∘ SynchronizedPairs.second) q := by
    exact Coincidence.transverseAt_ambient_family_iff
      (τ := fun p : ℝ × (M × M) => p.1)
      (hA.mdifferentiableAt (by simp))
      ((contMDiff_fst (n := ∞)).mdifferentiableAt (by simp))
      ((hF.comp SynchronizedPairs.first_smooth).mdifferentiableAt (by simp))
      ((hF.comp SynchronizedPairs.second_smooth).mdifferentiableAt (by simp))
      hq.symm (hbA q.1 (F (SynchronizedPairs.first q)))
  constructor
  · intro hr q hq hc
    apply (he q hc).mp
    apply hr q hq
    exact congrArg (fun y => A (q.1, y)) hc
  · intro hr q hq hc
    have hold : F (SynchronizedPairs.first q) = F (SynchronizedPairs.second q) :=
      hiA q.1 hc
    exact (he q hold).mpr (hr q hq hold)

theorem ambient_slice_bijective_mfderiv {A : ℝ × N → N}
    (hA : ∀ t, ∃ D : Diffeomorph J J N N ∞, ∀ y, D y = A (t, y)) :
    ∀ t y, Bijective (mfderiv J J (fun z => A (t, z)) y) := by
  intro t y
  obtain ⟨D, hD⟩ := hA t
  have he : (fun z => A (t, z)) = D := funext (fun z => (hD z).symm)
  rw [he]
  exact PartialChart.bijective_mfderiv D.toPartialDiffeomorph (mem_univ y)

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
