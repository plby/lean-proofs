import Wikipedia.NoExoticSixSphere.SmoothIntegralKernelDisk
import Wikipedia.NoExoticSixSphere.FourDiskSingularities
import Wikipedia.NoExoticSixSphere.RegularSlabDiskDoublePoints
import Wikipedia.NoExoticSixSphere.DiskDoublePointParity
import Wikipedia.NoExoticSixSphere.FourDiskPuncturedDomain

/-!
# Proper integral-kernel disks with finitely many actual singularities

An original integral boundary-kernel class in an actually two-connected
regular slab gives a smooth four-disk in its original seven-dimensional
regular fiber. The constructed perturbation fixes its boundary and a
possibly smaller outer collar, keeps every interior point in the strict-time
slab interior, and has a finite intrinsic singular set. The same map has
regular chart jets and active double points. If the original boundary map
is injective, its fixed collar is injective, and all off-diagonal interior
double points are regular. Their actual compact closure stays in the open
disk product, with finite diagonal orbits and unordered real curve charts
away from them. The proved half-line charts at the diagonal identify the
boundary with the original singular set, whose cardinality is therefore
even. Neither immersion nor a boundary-frame obstruction comparison is inferred.
The same disk also has a finite disjoint system of original parity-one
linking balls, with a compact regular punctured domain retaining its
original outer sphere and the actual linking spheres.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem exists_generic_disk_of_integral_kernel (hd : m = n + 6)
    (U : Set (slab d.map z s t)) (hU : U ⊆ BoundaryPush.ends d.map z s t)
    (f : C(NoExoticSixSphere.Sphere 3, U))
    (hker : singularHomologyMap (subtypeInclusion U) 3 (SmoothCube.integralSphereClass f) = 0)
    (hf : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial ((subtypeInclusion U).comp f)))
    (hi : ∀ q, Injective
      (mfderiv (𝓡 3) (𝓡 (m + 1)) (spatial ((subtypeInclusion U).comp f)) q)) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
    ∃ D : d.CollaredDiskExtension 3 ((subtypeInclusion U).comp f),
      ∃ ρ : ℝ, 3 / 4 < ρ ∧ ρ < 1 ∧
        ∃ g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z},
          (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
          (∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f q).val.val) ∧
          (∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val) ∧
          (∀ x ∈ ball 0 1, (g x).val.1 ∈ Ioo s t) ∧
          (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x)) ∧
          (closedBall (0 : Vector 4) 1 ∩
            {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite ∧
          ∃ C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7)
              {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} (Vector 7) ∞),
            C.Countable ∧ (∀ y, ∃ c ∈ C, y ∈ c.source) ∧
            (∀ c ∈ C, OperatorRank.RegularFourSevenOn
              (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source}) ∧
            Nonempty (GenericFourDisk.ParityBallSystem g) ∧
            CompactRetractionAffineFamily.RegularDoublePointsOn g (ball 0 1) (ball 0 ρ) C ∧
            (Injective f →
              CompactRetractionAffineFamily.RegularDoublePointsOn g (ball 0 1) (ball 0 1) C ∧
              closure (DiskDoublePoints.points g) ⊆ ball 0 1 ×ˢ ball 0 1 ∧
              (DiskDoublePoints.diagonalOrbits g).Finite ∧
              Even (DiskDoublePoints.singularSet g).ncard ∧
              ∀ q : DiskDoublePoints.Unordered g, q ∉ DiskDoublePoints.diagonalOrbits g →
                ∃ c : OpenPartialHomeomorph (DiskDoublePoints.Unordered g) ℝ,
                  q ∈ c.source ∧ Disjoint c.source (DiskDoublePoints.diagonalOrbits g)) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiber_isManifold d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let e := RegularCylinderFiber.embedding d.map d.smooth_map z d.regular_map 6 hd
  obtain ⟨D, g₀, hgs₀, hgb₀, hgc₀, hgV₀, hgi₀⟩ :=
    exists_smooth_disk_of_integral_kernel w hd U hU f hker hf hi
  let V : Set {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z} :=
    {v | v.val.1 ∈ Ioo s t}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)
  obtain ⟨ρ, hρ, hρ1, g, hgs, hgeq, -, hgV, hgi, hfinite, C, hC, hcov, hgen⟩ :=
    GenericFourDisk.exists_relative_finite_singularities e g₀ hgs₀ hgi₀ V hV hgV₀
  have hcollar : ∀ x : Disk (E := Vector 4), ρ ≤ ‖x.val‖ → g x.val = (D.map x).val := by
    intro x hx
    rw [hgeq x.val x.property hx]
    exact hgc₀ x (hρ.le.trans hx)
  have hboundary : ∀ q : NoExoticSixSphere.Sphere 3, g q.val = (f q).val.val := by
    intro q
    have hq : q.val ∈ closedBall (0 : Vector 4) 1 := sphere_subset_closedBall q.property
    rw [hgeq q.val hq (by rw [ClosedHemisphere.unit_norm]; exact hρ1.le)]
    exact hgb₀ q
  refine ⟨D, ρ, hρ, hρ1, g, hgs, hboundary, hcollar, hgV, hgi, hfinite,
    C, hC, hcov, hgen.1,
    GenericFourDisk.exists_parityBallSystem e g hgs ρ hρ1 hgi C hcov hgen.1, hgen.2, ?_⟩
  intro hfinj
  have hfi : Injective ((subtypeInclusion U).comp f) := Subtype.val_injective.comp hfinj
  have hend := boundarySphere_one_end ((subtypeInclusion U).comp f)
    (fun q ↦ hU (f q).property)
  have hcol := injOn_of_eq_outer_collar D (spherePole 3) hfi hend ρ (by linarith) g hcollar
  have hfull : CompactRetractionAffineFamily.RegularDoublePointsOn
      g (ball 0 1) (ball 0 1) C := by
    apply hgen.2.of_injOn_compl
    apply hcol.mono
    intro x hx
    refine ⟨ball_subset_closedBall hx.1, ?_⟩
    exact le_of_not_gt (fun hn ↦ hx.2 (mem_ball_zero_iff.mpr hn))
  have hcont : ContinuousOn g (closedBall 0 1) :=
    fun x hx ↦ (hgs x hx).continuousAt.continuousWithinAt
  have hcl := doublePointClosure_subset_interior D (spherePole 3) hfi hend ρ (by linarith)
    hρ1 g hcont hboundary hcollar hgV
  exact ⟨hfull, hcl, DiskDoublePoints.finite_diagonalOrbits e g hgs hfinite,
    (DiskDoublePoints.finite_even_singularSet e g hgs ρ hρ1 hgi C hcov hgen.1 hcl hfull).2,
    DiskDoublePoints.exists_unordered_chart_of_not_mem_diagonal g hgs hcl C hcov hfull⟩

end NoExoticSixSphere.RegularSlabDiskCollar
