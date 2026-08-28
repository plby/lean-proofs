import Wikipedia.NoExoticSixSphere.RegularSlabCoreHomologyNaturality
import Wikipedia.NoExoticSixSphere.RegularSlabInteriorCapDuality

/-!
# A relative fundamental class for the original regular slab

The genuine compact-supported fundamental class on an inner slab is
transported by the actual excision and boundary-collar homology maps.
Naturality and support restriction prove independence of every choice
of inner slab. Identifying its connecting image with the original
boundary fundamental class is a separate theorem, not assumed here.
-/

noncomputable section

open Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))
  (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)

def coreFundamentalClass : RelativeCoefficients.ModHomology 2
    (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ (n + 3) :=
  letI := d.interiorEuclideanAtlas n hd
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  CompactSupportedFundamentalClass.fundamentalClass (E := EuclideanSpace ℝ (Fin (n + 3))) n
    (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))
    (d.compactCore a b hsa hbt).isCompact

def relativeFundamentalClassOnCore :
    RelativeCoefficients.ModHomology 2 (BoundaryPush.ends d.map z s t) (n + 3) :=
  d.coreToBoundaryModEquiv a b hsa hab hbt hL hR 2 (by decide) (n + 3)
    (d.coreFundamentalClass n hd a b hsa hbt)

theorem relativeFundamentalClassOnCore_collar :
    d.boundaryToCollarModEquiv a b hsa hab hbt hL hR 2 (by decide) (n + 3)
        (d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR) =
      d.coreModHomologyEquiv a b hsa hbt 2 (by decide) (n + 3)
        (d.coreFundamentalClass n hd a b hsa hbt) :=
  d.coreToBoundaryModEquiv_collar a b hsa hab hbt hL hR 2 (by decide) (n + 3) _

variable (a' b' : ℝ) (hsa' : s < a') (hab' : a' ≤ b') (hbt' : b' < t)
  (hL' : Icc s a' ⊆ d.leftTimes) (hR' : Icc b' t ⊆ d.rightTimes)

theorem coreFundamentalClass_restrict (haa : a' ≤ a) (hbb : b ≤ b') :
    SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod 2))
        (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) (n + 3)
        (d.coreFundamentalClass n hd a' b' hsa' hbt') =
      d.coreFundamentalClass n hd a b hsa hbt := by
  let := d.interiorEuclideanAtlas n hd
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact CompactSupportedFundamentalClass.restrict_fundamentalClass
    (E := EuclideanSpace ℝ (Fin (n + 3))) n
    (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb)
    (d.compactCore a b hsa hbt).isCompact (d.compactCore a' b' hsa' hbt').isCompact

theorem relativeFundamentalClassOnCore_mono (haa : a' ≤ a) (hbb : b ≤ b') :
    d.relativeFundamentalClassOnCore n hd a' b' hsa' hab' hbt' hL' hR' =
      d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR := by
  unfold relativeFundamentalClassOnCore
  rw [d.coreToBoundaryModEquiv_natural a b hsa hab hbt hL hR
    a' b' hsa' hab' hbt' hL' hR' haa hbb 2 (by decide) (n + 3)]
  rw [d.coreFundamentalClass_restrict n hd a b hsa hbt a' b' hsa' hbt' haa hbb]

theorem relativeFundamentalClassOnCore_independent :
    d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR =
      d.relativeFundamentalClassOnCore n hd a' b' hsa' hab' hbt' hL' hR' := by
  let c := min a a'
  let e := max b b'
  have hsc : s < c := lt_min hsa hsa'
  have het : e < t := max_lt hbt hbt'
  have hce : c ≤ e := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  have hLc : Icc s c ⊆ d.leftTimes :=
    (Icc_subset_Icc le_rfl (min_le_left _ _)).trans hL
  have hRe : Icc e t ⊆ d.rightTimes :=
    (Icc_subset_Icc (le_max_left _ _) le_rfl).trans hR
  exact (d.relativeFundamentalClassOnCore_mono n hd a b hsa hab hbt hL hR
    c e hsc hce het hLc hRe (min_le_left _ _) (le_max_left _ _)).symm.trans
    (d.relativeFundamentalClassOnCore_mono n hd a' b' hsa' hab' hbt' hL' hR'
      c e hsc hce het hLc hRe (min_le_right _ _) (le_max_right _ _))

def relativeFundamentalClass :
    RelativeCoefficients.ModHomology 2 (BoundaryPush.ends d.map z s t) (n + 3) :=
  let l := d.exists_inner_times.choose
  let u := d.exists_inner_times.choose_spec.choose
  let h := d.exists_inner_times.choose_spec.choose_spec
  d.relativeFundamentalClassOnCore n hd l u h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem relativeFundamentalClass_eq_onCore :
    d.relativeFundamentalClass n hd =
      d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR := by
  unfold relativeFundamentalClass
  exact d.relativeFundamentalClassOnCore_independent n hd _ _ _ _ _ _ _
    a b hsa hab hbt hL hR

theorem relativeFundamentalClass_core :
    (d.coreToBoundaryModEquiv a b hsa hab hbt hL hR 2 (by decide) (n + 3)).symm
        (d.relativeFundamentalClass n hd) = d.coreFundamentalClass n hd a b hsa hbt := by
  rw [d.relativeFundamentalClass_eq_onCore n hd a b hsa hab hbt hL hR]
  exact LinearEquiv.symm_apply_apply _ _

end NoExoticSixSphere.RegularCollaredCylinder
