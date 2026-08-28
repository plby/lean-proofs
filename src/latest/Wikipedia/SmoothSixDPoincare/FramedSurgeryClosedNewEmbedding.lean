import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedNewFace

/-! # The whole closed new face is genuinely embedded in the surgery boundary -/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

theorem oldClosedOverlap_injective : Injective (oldClosedOverlap A) := by
  intro p q h
  have h' := A.closedEmbedding.injective (congrArg Subtype.val h)
  exact Prod.ext
    (congrArg (fun z : UnitSphere E × MorseHandle.UnitDisk F => z.1) h')
    (Subtype.ext (congrArg (fun z : UnitSphere E × MorseHandle.UnitDisk F => z.2.val) h'))

theorem newOuterMap_injective : Injective (newOuterMap A n) :=
  (oldMap_isOpenEmbedding A n).injective.comp
    ((oldClosedOverlap_injective A).comp (exchange E F).symm.injective)

theorem closedNewMap_punctured (u : PuncturedBall E) (v : UnitSphere F) :
    closedNewMap A n (⟨u.val, mem_closedBall_zero_iff.mpr u.property.2⟩, v) =
      newOuterMap A n (u, v) := by
  by_cases h : ‖u.val‖ < 1
  · exact (closedNewMap_open A n (⟨u.val, mem_ball_zero_iff.mpr h⟩, v)).trans
      (newOuterMap_open A n ⟨u.val, u.property.1, h⟩ v).symm
  · let q : newFaceOuter E F :=
      ⟨(⟨u.val, mem_closedBall_zero_iff.mpr u.property.2⟩, v), by
        change (1 / 2 : ℝ) ≤ ‖u.val‖
        linarith⟩
    exact closedNewMap_outer A n q

theorem closedNewMap_zero_ne_old (v : UnitSphere F) (x : oldPatch A) :
    closedNewMap A n (⟨0, by simp⟩, v) ≠ oldMap A n x := by
  intro h
  have hzero := closedNewMap_open A n ((⟨0, by simp [openUnitDisk]⟩ : openUnitDisk E), v)
  have he : oldMap A n x = newMap A n ((⟨0, by simp [openUnitDisk]⟩ : openUnitDisk E), v) :=
    h.symm.trans hzero
  obtain ⟨z, -, hz⟩ := (old_eq_new_iff A n _ _).mp he
  apply (openExchange m n z).1.property.1
  exact congrArg (fun q : NewPatch E F => q.1.val) hz

theorem closedNewMap_nonzero_ne_zero (p : ClosedNewFace E F) (hp : p.1.val ≠ 0)
    (v : UnitSphere F) : closedNewMap A n p ≠ closedNewMap A n (⟨0, by simp⟩, v) := by
  let u : PuncturedBall E := ⟨p.1.val, hp, mem_closedBall_zero_iff.mp p.1.property⟩
  have he := closedNewMap_punctured A n u p.2
  intro h
  apply closedNewMap_zero_ne_old A n v
    (oldClosedOverlap A ((exchange E F).symm (u, p.2)))
  exact h.symm.trans he

theorem closedNewMap_injective : Injective (closedNewMap A n) := by
  intro p q h
  by_cases hp : p.1.val = 0
  · by_cases hq : q.1.val = 0
    · let a : NewPatch E F := (⟨p.1.val, by simp [openUnitDisk, hp]⟩, p.2)
      let b : NewPatch E F := (⟨q.1.val, by simp [openUnitDisk, hq]⟩, q.2)
      have he : newMap A n a = newMap A n b :=
        (closedNewMap_open A n a).symm.trans (h.trans (closedNewMap_open A n b))
      have hab := (newMap_isOpenEmbedding A n).injective he
      exact Prod.ext (Subtype.ext (hp.trans hq.symm))
        (congrArg (fun z : NewPatch E F => z.2) hab)
    · have hp' : p = (⟨0, by simp⟩, p.2) := Prod.ext (Subtype.ext hp) rfl
      exact False.elim (closedNewMap_nonzero_ne_zero A n q hq p.2
        (h.symm.trans (congrArg (closedNewMap A n) hp')))
  · by_cases hq : q.1.val = 0
    · have hq' : q = (⟨0, by simp⟩, q.2) := Prod.ext (Subtype.ext hq) rfl
      exact False.elim (closedNewMap_nonzero_ne_zero A n p hp q.2
        (h.trans (congrArg (closedNewMap A n) hq')))
    · let u : PuncturedBall E := ⟨p.1.val, hp, mem_closedBall_zero_iff.mp p.1.property⟩
      let v : PuncturedBall E := ⟨q.1.val, hq, mem_closedBall_zero_iff.mp q.1.property⟩
      have he := (closedNewMap_punctured A n u p.2).symm.trans
        (h.trans (closedNewMap_punctured A n v q.2))
      have huv := newOuterMap_injective A n he
      exact Prod.ext (Subtype.ext (congrArg
        (fun z : PuncturedBall E × UnitSphere F => z.1.val) huv))
        (congrArg (fun z : PuncturedBall E × UnitSphere F => z.2) huv)

theorem closedNewMap_isClosedEmbedding [FiniteDimensional ℝ F] :
    IsClosedEmbedding (closedNewMap A n) :=
  (closedNewMap A n).continuous.isClosedEmbedding (closedNewMap_injective A n)

end Wikipedia.SmoothSixDPoincare.FramedSurgery
