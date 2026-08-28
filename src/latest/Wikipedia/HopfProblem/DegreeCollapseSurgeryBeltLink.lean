import Wikipedia.SmoothSixDPoincare.FramedSurgeryBeltComplement
import Mathlib.Topology.Homotopy.Basic

/-!
# The actual old tube link contracts onto the canonical belt sphere

In the new surgery patch the radial exchange sends `(u,v)` to
`(norm v • u, normalize v)`. Contract its first coordinate linearly to
zero, retaining the entire normal direction. This gives a homotopy in
the actual surgery target, with the original old-patch map at time zero
and the literal belt map at time one.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def oldTube : C(Overlap E F, oldPatch A) :=
  ⟨oldOverlap A, (oldOverlap_isOpenEmbedding A).continuous⟩

def normalDirection : C(Overlap E F, UnitSphere F) :=
  ⟨fun z => (newOverlap m n z).2, (newOverlap_isOpenEmbedding m n).continuous.snd⟩

theorem normalDirection_coe (z : Overlap E F) :
    (normalDirection (E := E) (F := F) (m := m) n z).val = ‖z.2.val‖⁻¹ • z.2.val :=
  newOverlap_snd m n z

def tubeToBelt :
    Homotopy ((oldMap A n).comp (oldTube A))
      ((beltMap A n).comp (normalDirection (E := E) (m := m) n)) where
  toFun z := newMap A n
    (⟨(1 - (z.1 : ℝ)) • (newOverlap m n z.2).1.val, by
      change (1 - (z.1 : ℝ)) • (newOverlap m n z.2).1.val ∈ ball (0 : E) 1
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr z.1.property.2)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ z.1.property.1)).trans_lt
        (mem_ball_zero_iff.mp (newOverlap m n z.2).1.property)⟩,
      (newOverlap m n z.2).2)
  continuous_toFun := by
    apply (newMap A n).continuous.comp
    have hc : Continuous (fun z : unitInterval × Overlap E F => newOverlap m n z.2) :=
      (newOverlap_isOpenEmbedding (E := E) (F := F) m n).continuous.comp continuous_snd
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp hc.fst)).subtype_mk _).prodMk hc.snd
  map_zero_left z := by
    change newMap A n _ = oldMap A n (oldOverlap A z)
    rw [overlap_identification A n z]
    apply congrArg (newMap A n)
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (0 : ℝ)) • (newOverlap m n z).1.val = (newOverlap m n z).1.val
      simp only [sub_zero, one_smul]
    · rfl
  map_one_left z := by
    change newMap A n _ = newMap A n _
    apply congrArg (newMap A n)
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (1 : ℝ)) • (newOverlap m n z).1.val = 0
      simp only [sub_self, zero_smul]
    · rfl

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryLink
