import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardBaseIdealLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheaf

/-!
# Global identification of native base-bundle sections with the ideal

The actual two-chart identifications are glued on every original sphere
open set.  Both directions use the genuine sheaves and literal
restrictions.  Their local inverse identities prove that the global
maps are inverse; no global section identification is assumed.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal

open HolomorphicFunctionSheaf.SphereH1

/-- The original two affine chart opens restricted to an arbitrary open. -/
def chartCover (U : Opens RiemannSphere) (b : Bool) : Opens RiemannSphere :=
  U ⊓ NegativeOneFrames.frameChart b

theorem chartCover_le (U : Opens RiemannSphere) (b : Bool) : chartCover U b ≤ U :=
  inf_le_left

theorem chartCover_le_frame (U : Opens RiemannSphere) (b : Bool) :
    chartCover U b ≤ NegativeOneFrames.frameChart b := inf_le_right

theorem chartCover_covers (U : Opens RiemannSphere) : U ≤ iSup (chartCover U) := by
  intro p hp
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact Opens.mem_iSup.mpr ⟨b, hp, hb⟩

theorem bundleSection_eq_of_chartCover (U : Opens RiemannSphere) (s t : BundleSection U)
    (h : ∀ b, bundleRestrict (chartCover_le U b) s = bundleRestrict (chartCover_le U b) t) :
    s = t := by
  apply NativeBundleSections.Section.ext CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ)
  intro p
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact congrArg (fun r : BundleSection (chartCover U b) => r ⟨p, ⟨p.property, hb⟩⟩) (h b)

theorem idealSection_eq_of_chartCover (U : Opens RiemannSphere) (f g : NegativeOneSection U)
    (h : ∀ b, negativeOneRestriction (chartCover_le U b) f =
      negativeOneRestriction (chartCover_le U b) g) : f = g := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  obtain ⟨b, hb⟩ := NegativeOneFrames.frameChart_cover p
  exact congrArg (fun r : NegativeOneSection (chartCover U b) => r ⟨p, ⟨p.property, hb⟩⟩) (h b)

/-- The actual ideal section read in each original local frame. -/
def localImage (U : Opens RiemannSphere) (s : BundleSection U) (b : Bool) :
    NegativeOneSection (chartCover U b) :=
  localLinearEquiv b (chartCover U b) (chartCover_le_frame U b)
    (bundleRestrict (chartCover_le U b) s)

theorem localImage_compatible (U : Opens RiemannSphere) (s : BundleSection U) :
    TopCat.Presheaf.IsCompatible negativeOneSheaf.obj (chartCover U) (localImage U s) := by
  intro b c
  change negativeOneRestriction inf_le_left (localImage U s b) =
    negativeOneRestriction inf_le_right (localImage U s c)
  rw [localImage, localImage,
    localLinearEquiv_restrict_change_chart b c inf_le_left
      (chartCover_le_frame U b) (inf_le_right.trans (chartCover_le_frame U c)),
    localLinearEquiv_restrict c inf_le_right (chartCover_le_frame U c)]
  rfl

theorem existsUnique_toIdeal (U : Opens RiemannSphere) (s : BundleSection U) :
    ∃! f : NegativeOneSection U,
      ∀ b, negativeOneRestriction (chartCover_le U b) f = localImage U s b := by
  have h := negativeOneSheaf.existsUnique_gluing' (chartCover U) U
    (fun b => homOfLE (chartCover_le U b)) (chartCover_covers U)
    (localImage U s) (localImage_compatible U s)
  exact h

/-- The global actual ideal section, glued from the proved original charts. -/
def toIdeal (U : Opens RiemannSphere) (s : BundleSection U) : NegativeOneSection U :=
  (existsUnique_toIdeal U s).choose

theorem toIdeal_restrict_chartCover (U : Opens RiemannSphere) (s : BundleSection U)
    (b : Bool) :
    negativeOneRestriction (chartCover_le U b) (toIdeal U s) = localImage U s b :=
  (existsUnique_toIdeal U s).choose_spec.1 b

/-- On every chart subopen, not just the two selected cover members,
the global map is the already proved original local identification. -/
theorem toIdeal_restrict_chart (b : Bool) {U V : Opens RiemannSphere}
    (h : U ≤ V) (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection V) :
    negativeOneRestriction h (toIdeal V s) =
      localLinearEquiv b U hU (bundleRestrict h s) := by
  let h' : U ≤ chartCover V b := le_inf h hU
  calc
    _ = negativeOneRestriction h'
        (negativeOneRestriction (chartCover_le V b) (toIdeal V s)) := rfl
    _ = negativeOneRestriction h' (localImage V s b) :=
      congrArg (negativeOneRestriction h') (toIdeal_restrict_chartCover V s b)
    _ = localLinearEquiv b U hU (bundleRestrict h s) :=
      localLinearEquiv_restrict b h' (chartCover_le_frame V b)
        (bundleRestrict (chartCover_le V b) s)

/-- The inverse local maps reconstruct actual native bundle sections. -/
def localPreimage (U : Opens RiemannSphere) (f : NegativeOneSection U) (b : Bool) :
    BundleSection (chartCover U b) :=
  (localLinearEquiv b (chartCover U b) (chartCover_le_frame U b)).symm
    (negativeOneRestriction (chartCover_le U b) f)

theorem localPreimage_compatible (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    TopCat.Presheaf.IsCompatible
      (NativeBundleSections.sheaf CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ)).obj
      (chartCover U) (localPreimage U f) := by
  intro b c
  change bundleRestrict inf_le_left (localPreimage U f b) =
    bundleRestrict inf_le_right (localPreimage U f c)
  apply (localLinearEquiv b (chartCover U b ⊓ chartCover U c)
    (inf_le_left.trans (chartCover_le_frame U b))).injective
  rw [← localLinearEquiv_restrict b inf_le_left (chartCover_le_frame U b),
    ← localLinearEquiv_restrict_change_chart c b inf_le_right
      (chartCover_le_frame U c) (inf_le_left.trans (chartCover_le_frame U b))]
  simp only [localPreimage, LinearEquiv.apply_symm_apply]
  rfl

theorem existsUnique_fromIdeal (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    ∃! s : BundleSection U,
      ∀ b, bundleRestrict (chartCover_le U b) s = localPreimage U f b := by
  have h := (NativeBundleSections.sheaf
      CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ)).existsUnique_gluing'
    (chartCover U) U (fun b => homOfLE (chartCover_le U b)) (chartCover_covers U)
    (localPreimage U f) (localPreimage_compatible U f)
  exact h

/-- Actual inverse reconstruction in the original native total-space atlas. -/
def fromIdeal (U : Opens RiemannSphere) (f : NegativeOneSection U) : BundleSection U :=
  (existsUnique_fromIdeal U f).choose

theorem fromIdeal_restrict_chartCover (U : Opens RiemannSphere) (f : NegativeOneSection U)
    (b : Bool) :
    bundleRestrict (chartCover_le U b) (fromIdeal U f) = localPreimage U f b :=
  (existsUnique_fromIdeal U f).choose_spec.1 b

theorem fromIdeal_toIdeal (U : Opens RiemannSphere) (s : BundleSection U) :
    fromIdeal U (toIdeal U s) = s := by
  apply bundleSection_eq_of_chartCover U
  intro b
  rw [fromIdeal_restrict_chartCover, localPreimage, toIdeal_restrict_chartCover,
    localImage, LinearEquiv.symm_apply_apply]

theorem toIdeal_fromIdeal (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    toIdeal U (fromIdeal U f) = f := by
  apply idealSection_eq_of_chartCover U
  intro b
  rw [toIdeal_restrict_chartCover, localImage, fromIdeal_restrict_chartCover,
    localPreimage, LinearEquiv.apply_symm_apply]

/-- Forward naturality on every pair of original sphere opens. -/
theorem toIdeal_restrict {U V : Opens RiemannSphere} (h : U ≤ V) (s : BundleSection V) :
    negativeOneRestriction h (toIdeal V s) = toIdeal U (bundleRestrict h s) := by
  apply idealSection_eq_of_chartCover U
  intro b
  calc
    _ = negativeOneRestriction ((chartCover_le U b).trans h) (toIdeal V s) := rfl
    _ = localLinearEquiv b (chartCover U b) (chartCover_le_frame U b)
        (bundleRestrict ((chartCover_le U b).trans h) s) :=
      toIdeal_restrict_chart b ((chartCover_le U b).trans h) (chartCover_le_frame U b) s
    _ = negativeOneRestriction (chartCover_le U b) (toIdeal U (bundleRestrict h s)) :=
      (toIdeal_restrict_chartCover U (bundleRestrict h s) b).symm

/-- Inverse reconstruction also commutes with every literal restriction. -/
theorem fromIdeal_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : NegativeOneSection V) :
    fromIdeal U (negativeOneRestriction h f) = bundleRestrict h (fromIdeal V f) := by
  have he := toIdeal_restrict h (fromIdeal V f)
  rw [toIdeal_fromIdeal] at he
  apply (congrArg (fromIdeal U) he).trans
  exact fromIdeal_toIdeal U _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal
