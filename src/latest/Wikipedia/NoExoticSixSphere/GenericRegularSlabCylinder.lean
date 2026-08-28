import Wikipedia.NoExoticSixSphere.AnnulusImmersiveBoundaryNeighborhoods
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointParity
import Wikipedia.NoExoticSixSphere.FourAnnulusSingularities
import Wikipedia.NoExoticSixSphere.FourAnnulusParityBallSystem
import Wikipedia.NoExoticSixSphere.GenericProperFourAnnulus
import Wikipedia.NoExoticSixSphere.RegularSlabAnnulusDoublePoints

/-!
# A generic cylinder with the original regular-fiber atlas and both end maps

Starting with the actual collared cylinder, relative smoothing and the
proved boundary immersion give protected immersive subcollars. The annular
perturbation retains these original collars, their injectivity and boundary
derivatives, and strict-time interior values. Its middle jets are generic
in a countable cover of the original target charts. Every interior
double-point equation is regular: distinct points in the protected
collars cannot have the same image. The actual double-point closure lies
in the open annulus product. Its proved compact unordered curve and
half-line boundary charts give a finite, even intrinsic singularity count.
The actual disjoint parity-one balls can all be retained in the active
middle annulus. No endpoint framing comparison is asserted.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)}
  (D : d.CollaredCylinderExtension 3 f₀ f₁) (b : NoExoticSixSphere.Sphere 3)

theorem exists_generic_with_original_ends (hd : m = n + 6)
    (hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁))
    (hi₀ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₀) q))
    (hi₁ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial f₁) q))
    (hinj₀ : Injective f₀) (hinj₁ : Injective f₁)
    (h₀ : ∀ q, (f₀ q).val.val.1 = s) (h₁ : ∀ q, (f₁ q).val.val.1 = t) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    let L := EuclideanProduct.coordinates (m + 1)
    ∃ g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
      ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
      (∀ x ∈ SphereAnnulus.domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
      (∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f₀ q).val) ∧
      (∀ q : NoExoticSixSphere.Sphere 3, g ((2 : ℝ) • q.val) = (f₁ q).val) ∧
      (∀ x : SphereAnnulus.domain 3, ‖x.val‖ ≤ r₀ ∨ r₁ ≤ ‖x.val‖ →
        g x.val = (D.map (SphereAnnulus.toCylinder b x)).val) ∧
      Set.InjOn g {x : Vector 4 | x ∈ SphereAnnulus.domain 3 ∧
        (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)} ∧
      (∀ x ∈ SphereAnnulus.domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
        Injective (fderiv ℝ (e.toFun ∘ g) x)) ∧
      (∀ q : NoExoticSixSphere.Sphere 3,
        fderiv ℝ (e.toFun ∘ g) q.val = fderiv ℝ (L ∘ leftCollar D b) q.val ∧
        fderiv ℝ (e.toFun ∘ g) ((2 : ℝ) • q.val) =
          fderiv ℝ (L ∘ rightCollar D b) ((2 : ℝ) • q.val)) ∧
      (∀ x : Vector 4, 1 < ‖x‖ → ‖x‖ < 2 → (g x).val.1 ∈ Ioo s t) ∧
      (SphereAnnulus.domain 3 ∩
        {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite ∧
      (closure (AnnulusDoublePoints.points g) ⊆
        SphereAnnulus.openDomain 3 ×ˢ SphereAnnulus.openDomain 3) ∧
      Even (AnnulusDoublePoints.singularSet g).ncard ∧
      (∃ P : GenericFourAnnulus.ParityBallSystem g,
        P.closedHoles ⊆ {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁}) ∧
      ∃ C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7)
          {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} (Vector 7) ∞),
        C.Countable ∧ (∀ y, ∃ c ∈ C, y ∈ c.source) ∧
        (∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ fderiv ℝ (c ∘ g) x)
          {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source}) ∧
        CompactRetractionAffineFamily.RegularDoublePointsOn g
          {x | 1 < ‖x‖ ∧ ‖x‖ < 2} {x | 1 < ‖x‖ ∧ ‖x‖ < 2} C := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
  let L := EuclideanProduct.coordinates (m + 1)
  obtain ⟨f, hfs, hfe₀, hfe₁, hfeq, hfV, hfi⟩ :=
    exists_smooth_with_immersive_boundary D b 6 hd hf₀ hf₁ hi₀ hi₁ h₀ h₁
  obtain ⟨r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hir⟩ :=
    SphereAnnulus.exists_immersive_boundary_annuli e f hfs hfi
  have hrr : r₀ < r₁ := by linarith
  let V : Set {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    {v | v.val.1 ∈ Ioo s t}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)
  obtain ⟨g, hgs, hgeq, hgderiv, hgV, hgeneric⟩ :=
    GenericFourAnnulus.exists_relative e f hfs r₀ r₁ hr₀ hr₁ hrr V hV hfV
  obtain ⟨C, hC, hcov, hgen, hdouble⟩ := hgeneric
  have hsmall (x : Vector 4) (hx : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) :
      ‖x‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x‖ :=
    hx.elim (fun h ↦ Or.inl (h.trans hr₀small.le))
      (fun h ↦ Or.inr (hr₁large.le.trans h))
  have hunit (q : NoExoticSixSphere.Sphere 3) :
      q.val ∈ SphereAnnulus.domain 3 ∧ ‖q.val‖ ≤ r₀ := by
    change (1 ≤ ‖q.val‖ ∧ ‖q.val‖ ≤ 2) ∧ ‖q.val‖ ≤ r₀
    rw [ClosedHemisphere.unit_norm]
    exact ⟨⟨le_rfl, by norm_num⟩, hr₀.le⟩
  have houter (q : NoExoticSixSphere.Sphere 3) :
      (2 : ℝ) • q.val ∈ SphereAnnulus.domain 3 ∧ r₁ ≤ ‖(2 : ℝ) • q.val‖ := by
    have hn : ‖(2 : ℝ) • q.val‖ = 2 := by
      rw [norm_smul, ClosedHemisphere.unit_norm]
      norm_num
    change (1 ≤ ‖(2 : ℝ) • q.val‖ ∧ ‖(2 : ℝ) • q.val‖ ≤ 2) ∧ _
    rw [hn]
    exact ⟨⟨by norm_num, le_rfl⟩, hr₁.le⟩
  have hginj : Set.InjOn g {x : Vector 4 | x ∈ SphereAnnulus.domain 3 ∧
      (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)} := by
    intro x hx y hy he
    apply injOn_original_annulus_collars D b h₀ h₁ hinj₀ hinj₁ f hfeq
      ⟨hx.1, hsmall x hx.2⟩ ⟨hy.1, hsmall y hy.2⟩
    exact (hgeq x hx.1 hx.2).symm.trans (he.trans (hgeq y hy.1 hy.2))
  have hgi : ∀ x ∈ SphereAnnulus.domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x) := by
    intro x hx hxends
    rw [hgderiv x hx hxends]
    exact hir x hx hxends
  have hfinite := GenericFourAnnulus.finite_singular_of_chart_jets
    e g hgs r₀ r₁ hr₀ hr₁ hgi C hcov hgen
  have hboundary₀ : ∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f₀ q).val := by
    intro q
    exact (hgeq q.val (hunit q).1 (Or.inl (hunit q).2)).trans (hfe₀ q)
  have hboundary₁ : ∀ q : NoExoticSixSphere.Sphere 3,
      g ((2 : ℝ) • q.val) = (f₁ q).val := by
    intro q
    exact (hgeq ((2 : ℝ) • q.val) (houter q).1 (Or.inr (houter q).2)).trans (hfe₁ q)
  have hcont : ContinuousOn g (SphereAnnulus.domain 3) :=
    fun x hx ↦ (hgs x hx).continuousAt.continuousWithinAt
  have hcl := doublePointClosure_subset_interior g hcont hboundary₀ hboundary₁ h₀ h₁
    r₀ r₁ hr₀ hr₁ hginj hgV
  have hfull : CompactRetractionAffineFamily.RegularDoublePointsOn g
      (SphereAnnulus.openDomain 3) (SphereAnnulus.openDomain 3) C := by
    apply hdouble.of_injOn_compl
    apply hginj.mono
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩,
      (not_and_or.mp hx.2).imp le_of_not_gt le_of_not_gt⟩
  have heven := (AnnulusDoublePoints.finite_even_singularSet
    e g hgs r₀ r₁ hr₀ hr₁ hgi C hcov hgen hcl hfull).2
  have hP := GenericFourAnnulus.exists_parityBallSystem
    e g hgs r₀ r₁ hr₀ hr₁ hgi C hcov hgen
  refine ⟨g, r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hgs, hboundary₀, hboundary₁, ?_,
    hginj, hgi, ?_, hgV, hfinite, hcl, heven, hP, C, hC, hcov, hgen, hfull⟩
  · intro x hx
    exact (hgeq x.val x.property hx).trans (hfeq x (hsmall x.val hx))
  · intro q
    constructor
    · exact (hgderiv q.val (hunit q).1 (Or.inl (hunit q).2)).trans
        (fderiv_left_of_original_collar D b 6 hd hf₀ h₀ f hfs hfeq q)
    · exact (hgderiv ((2 : ℝ) • q.val) (houter q).1 (Or.inr (houter q).2)).trans
        (fderiv_right_of_original_collar D b 6 hd hf₁ h₁ f hfs hfeq q)

end NoExoticSixSphere.RegularSlabCylinderCollar
