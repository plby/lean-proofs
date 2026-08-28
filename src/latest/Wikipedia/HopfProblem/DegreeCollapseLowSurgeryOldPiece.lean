import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryClosedExterior

/-!

# The original closed surgery piece, cover and exact common-face incidence

The actual original tube at the constructed face radius is closed embedded.
Together with the common closed exterior it covers the original manifold.
Their intersection is exactly the sphere-product face, with the original
tube map and both original sphere coordinates retained.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

abbrev OldDomain (d : ℕ) := NoExoticSixSphere.Sphere d × UnitBall (Vector (7 - d))

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def oldPiece (p : OldDomain d) : M := A.tube (p.1, oldRadius A • p.2.val)

theorem oldPiece_vector_norm_le (p : OldDomain d) :
    ‖oldRadius A • p.2.val‖ ≤ oldRadius A := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left p.2.property (oldRadius_pos A).le

theorem oldPiece_vector_mem (p : OldDomain d) :
    oldRadius A • p.2.val ∈ ball (0 : Vector (7 - d)) A.radius := by
  rw [mem_ball, dist_zero_right]
  exact (oldPiece_vector_norm_le A p).trans_lt (oldRadius_lt A)

theorem continuous_oldPiece : Continuous (oldPiece A) := by
  have hparam : Continuous (fun p : OldDomain d ↦ (p.1, oldRadius A • p.2.val)) :=
    continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).const_smul (oldRadius A))
  apply continuous_iff_continuousAt.mpr
  intro p
  have ht := (A.tube_localDiffeomorph p.1 (oldRadius A • p.2.val)
    (ball_subset_closedBall (oldPiece_vector_mem A p))).contMDiffAt.continuousAt
  exact ht.comp (f := fun p : OldDomain d ↦ (p.1, oldRadius A • p.2.val))
    hparam.continuousAt

theorem oldPiece_injective : Injective (oldPiece A) := by
  intro p q h
  have hp : (p.1, oldRadius A • p.2.val) ∈ A.openTubeDomain :=
    ⟨mem_univ _, oldPiece_vector_mem A p⟩
  have hq : (q.1, oldRadius A • q.2.val) ∈ A.openTubeDomain :=
    ⟨mem_univ _, oldPiece_vector_mem A q⟩
  have he : (p.1, oldRadius A • p.2.val) = (q.1, oldRadius A • q.2.val) :=
    A.injOn_tube_openTubeDomain hp hq h
  apply Prod.ext
  · exact congrArg
      (Prod.fst : NoExoticSixSphere.Sphere d × Vector (7 - d) → NoExoticSixSphere.Sphere d) he
  · apply Subtype.ext
    have hv : oldRadius A • p.2.val = oldRadius A • q.2.val := congrArg Prod.snd he
    exact (smul_right_injective _ (oldRadius_pos A).ne') hv

theorem isClosedEmbedding_oldPiece : IsClosedEmbedding (oldPiece A) := by
  let := e.closedEmbedding.isEmbedding.t2Space
  let := compactSpace_unitBall (7 - d)
  exact (continuous_oldPiece A).isClosedEmbedding (oldPiece_injective A)

theorem oldPiece_mem_closedExterior_iff (p : OldDomain d) :
    oldPiece A p ∈ closedExterior A ↔ ‖p.2.val‖ = 1 := by
  rw [oldPiece, tube_mem_closedExterior_iff A p.1 (oldPiece_vector_mem A p),
    norm_smul, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A)]
  constructor
  · intro hp
    nlinarith [p.2.property, oldRadius_pos A]
  · intro hp
    rw [hp, mul_one]

theorem old_cover : range (oldExterior A) ∪ range (oldPiece A) = univ := by
  apply eq_univ_of_forall
  intro m
  by_cases hm : m ∈ closedExterior A
  · exact Or.inl ⟨⟨m, hm⟩, rfl⟩
  · have ht : m ∈ A.tube '' ((univ : Set (NoExoticSixSphere.Sphere d)) ×ˢ
        ball (0 : Vector (7 - d)) (oldRadius A)) := by
      simpa only [closedExterior, mem_compl_iff, not_not] using hm
    obtain ⟨⟨s, v⟩, hv, he⟩ := ht
    have hn : ‖v‖ < oldRadius A := by
      simpa only [mem_ball, dist_zero_right] using hv.2
    have hx : ‖(oldRadius A)⁻¹ • v‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A)]
      calc
        (oldRadius A)⁻¹ * ‖v‖ ≤ (oldRadius A)⁻¹ * oldRadius A :=
          mul_le_mul_of_nonneg_left hn.le (inv_pos.mpr (oldRadius_pos A)).le
        _ = 1 := inv_mul_cancel₀ (oldRadius_pos A).ne'
    refine Or.inr ⟨(s, ⟨(oldRadius A)⁻¹ • v, hx⟩), ?_⟩
    change A.tube (s, oldRadius A • ((oldRadius A)⁻¹ • v)) = m
    rw [smul_inv_smul₀ (oldRadius_pos A).ne']
    exact he

theorem old_overlap (r : closedExterior A) (p : OldDomain d) :
    oldExterior A r = oldPiece A p ↔
      ∃ q : NoExoticSixSphere.Sphere d × sphere (0 : Vector (7 - d)) 1,
        r = commonFace A q ∧ p = oldBoundary q := by
  constructor
  · intro h
    have hr : oldPiece A p ∈ closedExterior A := h ▸ r.property
    have hn := (oldPiece_mem_closedExterior_iff A p).mp hr
    let w : sphere (0 : Vector (7 - d)) 1 := ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hn⟩
    refine ⟨(p.1, w), ?_, rfl⟩
    exact Subtype.ext h
  · rintro ⟨q, rfl, rfl⟩
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
