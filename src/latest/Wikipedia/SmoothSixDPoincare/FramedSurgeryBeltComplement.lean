import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedNewEmbedding
import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothBoundary

/-!
# The old patch is exactly the complement of the actual belt sphere

This identifies the full core complement, not merely the complement of
the closed new face. Every nonzero new-patch point is in the radial
overlap; zero points have no old-patch representative.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def beltMap : C(UnitSphere F, Boundary A n) :=
  (newMap A n).comp
    ⟨fun v => ((⟨0, by simp [openUnitDisk]⟩ : openUnitDisk E), v),
      continuous_const.prodMk continuous_id⟩

omit [FiniteDimensional ℝ F] in
theorem beltMap_eq_closedNewMap (v : UnitSphere F) :
    beltMap A n v = closedNewMap A n (⟨0, by simp⟩, v) :=
  (closedNewMap_open A n ((⟨0, by simp [openUnitDisk]⟩ : openUnitDisk E), v)).symm

theorem beltMap_isClosedEmbedding : IsClosedEmbedding (beltMap A n) := by
  apply (beltMap A n).continuous.isClosedEmbedding
  intro v w h
  exact congrArg (fun p : NewPatch E F => p.2)
    ((newMap_isOpenEmbedding A n).injective h)

omit [FiniteDimensional ℝ F] in
theorem oldMap_ne_belt (x : oldPatch A) (v : UnitSphere F) :
    oldMap A n x ≠ beltMap A n v := by
  rw [beltMap_eq_closedNewMap]
  exact (closedNewMap_zero_ne_old A n v x).symm

omit [FiniteDimensional ℝ F] in
theorem newMap_nonzero_mem_old (y : NewPatch E F) (hy : y.1.val ≠ 0) :
    newMap A n y ∈ range (oldMap A n) := by
  let q : openPuncturedDisk E × UnitSphere F :=
    (⟨y.1.val, hy, mem_ball_zero_iff.mp y.1.property⟩, y.2)
  let z : Overlap E F := (openExchange m n).symm q
  have hz : newOverlap m n z = y := by
    have h := (openExchange m n).apply_symm_apply q
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun p : openPuncturedDisk E × UnitSphere F =>
        p.1.val) h)
    · exact congrArg (fun p : openPuncturedDisk E × UnitSphere F => p.2) h
  exact ⟨oldOverlap A z, (overlap_identification A n z).trans (congrArg (newMap A n) hz)⟩

omit [FiniteDimensional ℝ F] in
theorem oldMap_range : range (oldMap A n) = (range (beltMap A n))ᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ ⟨v, hv⟩
    exact oldMap_ne_belt A n x v hv.symm
  · intro hy
    rcases cover A n y with h | ⟨q, rfl⟩
    · exact h
    · apply newMap_nonzero_mem_old A n q
      intro hq
      apply hy
      exact ⟨q.2, congrArg (newMap A n) (Prod.ext (Subtype.ext hq.symm) rfl)⟩

def beltComplement : TopologicalSpace.Opens (Boundary A n) :=
  ⟨(range (beltMap A n))ᶜ, (beltMap_isClosedEmbedding A n).isClosed_range.isOpen_compl⟩

def oldBeltMap (x : oldPatch A) : beltComplement A n :=
  ⟨oldMap A n x, fun ⟨v, hv⟩ => oldMap_ne_belt A n x v hv.symm⟩

theorem oldBeltMap_bijective : Bijective (oldBeltMap A n) := by
  constructor
  · intro x y h
    exact (oldMap_isOpenEmbedding A n).injective (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ range (oldMap A n) := by
      rw [oldMap_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

namespace SmoothBoundaryData

variable {A n} (P : SmoothBoundaryData A n)

omit [FiniteDimensional ℝ F] in
theorem contMDiff_beltMap :
    letI := P.charted
    ContMDiff (𝓡 n) J ∞ (beltMap A n) := by
  let _ := P.charted
  have h : ContMDiff (𝓡 n) (𝓘(ℝ, E).prod (𝓡 n)) ∞
      (fun v : UnitSphere F => ((⟨0, by simp [openUnitDisk]⟩ : openUnitDisk E), v)) :=
    contMDiff_const.prodMk contMDiff_id
  exact (P.newPartial.contMDiffOn.comp_contMDiff h
    (fun _ => P.new_source ▸ mem_univ _)).congr (fun v => (P.new_point _).symm)

theorem oldPartial_target :
    letI := P.charted
    P.oldPartial.target = (beltComplement A n : Set (Boundary A n)) := by
  let _ := P.charted
  rw [← P.oldPartial.toPartialEquiv.image_source_eq_target, P.old_source,
    image_univ]
  have he : (P.oldPartial : oldPatch A → Boundary A n) = oldMap A n :=
    funext P.old_point
  rw [he]
  exact oldMap_range A n

theorem contMDiff_oldBeltMap :
    letI := P.charted
    ContMDiff J J ∞ (oldBeltMap A n) := by
  let _ := P.charted
  apply (ContMDiff.subtypeVal_comp_iff (beltComplement A n) _).mp
  exact (P.oldPartial.contMDiffOn.comp_contMDiff contMDiff_id
    (fun _ => P.old_source ▸ mem_univ _)).congr (fun x => (P.old_point x).symm)

def beltComplementDiffeomorph :
    letI := P.charted
    Diffeomorph J J (oldPatch A) (beltComplement A n) ∞ := by
  let _ := P.charted
  let e := Equiv.ofBijective (oldBeltMap A n) (oldBeltMap_bijective A n)
  refine {
    toEquiv := e
    contMDiff_toFun := P.contMDiff_oldBeltMap
    contMDiff_invFun := ?_ }
  have h : ContMDiff J J ∞ (fun y : beltComplement A n => P.oldPartial.symm y.val) :=
    P.oldPartial.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val
      (fun y => by
        change y.val ∈ P.oldPartial.target
        rw [P.oldPartial_target]
        exact y.property)
  apply h.congr
  intro y
  have he : P.oldPartial (e.symm y) = y.val :=
    (P.old_point _).trans (congrArg (fun z : beltComplement A n => z.val)
      (e.apply_symm_apply y))
  exact ((congrArg P.oldPartial.symm he).symm.trans
    (P.oldPartial.left_inv (P.old_source ▸ mem_univ _))).symm

theorem beltComplementDiffeomorph_apply (x : oldPatch A) :
    letI := P.charted
    (P.beltComplementDiffeomorph x).val = oldMap A n x := rfl

end SmoothBoundaryData
end Wikipedia.SmoothSixDPoincare.FramedSurgery
