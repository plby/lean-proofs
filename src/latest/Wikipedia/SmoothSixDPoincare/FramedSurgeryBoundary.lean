import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedGraph

/-!
# The actual Hausdorff boundary obtained by framed surgery

The quotient glues the original core complement to the new open disk times
the belt sphere. Its transition and all its fibers come from the original
face and the actual radial exchange. Hausdorffness is proved, not assumed.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

section Nonempty

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem nonempty_overlap (m n : ℕ) [Fact (Module.finrank ℝ E = m + 1)]
    [Fact (Module.finrank ℝ F = n + 1)] : Nonempty (Overlap E F) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = m + 1)]
    omega)
  let _ : Nontrivial F := Module.nontrivial_of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ F = n + 1)]
    omega)
  obtain ⟨u⟩ : Nonempty (UnitSphere E) :=
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  obtain ⟨w⟩ : Nonempty (UnitSphere F) :=
    (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  exact ⟨(u, openPoint w ⟨1 / 2, by norm_num, by norm_num⟩)⟩

end Nonempty

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def transition : OpenPartialHomeomorph (oldPatch A) (NewPatch E F) := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition (oldOverlap_isOpenEmbedding A) (newOverlap_isOpenEmbedding m n)

theorem transition_source : (transition A n).source = range (oldOverlap A) := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition_source _ _

theorem transition_target : (transition A n).target = range (newOverlap (E := E) (F := F) m n) := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition_target _ _

theorem transition_apply (z : Overlap E F) :
    transition A n (oldOverlap A z) = newOverlap m n z := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition_apply _ _ z

abbrev Boundary := OpenGluing.Space (transition A n)

instance boundaryT2Space [FiniteDimensional ℝ F] : T2Space (Boundary A n) := by
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition_t2Space (oldOverlap_isOpenEmbedding A)
    (newOverlap_isOpenEmbedding m n) (isClosed_overlap_graph A n)

instance boundarySecondCountable [FiniteDimensional ℝ F] [SecondCountableTopology X] :
    SecondCountableTopology (Boundary A n) := by
  infer_instance

def oldMap : C(oldPatch A, Boundary A n) := OpenGluing.left (transition A n)

def newMap : C(NewPatch E F, Boundary A n) := OpenGluing.right (transition A n)

theorem oldMap_isOpenEmbedding : IsOpenEmbedding (oldMap A n) :=
  OpenGluing.left_isOpenEmbedding (transition A n)

theorem newMap_isOpenEmbedding : IsOpenEmbedding (newMap A n) :=
  OpenGluing.right_isOpenEmbedding (transition A n)

theorem old_eq_new_iff (x : oldPatch A) (y : NewPatch E F) :
    oldMap A n x = newMap A n y ↔
      ∃ z : Overlap E F, oldOverlap A z = x ∧ newOverlap m n z = y := by
  change OpenGluing.left (transition A n) x = OpenGluing.right (transition A n) y ↔ _
  rw [OpenGluing.left_eq_right]
  let _ := nonempty_overlap (E := E) (F := F) m n
  exact OpenGluing.overlapTransition_graph _ _ x y

theorem overlap_identification (z : Overlap E F) :
    oldMap A n (oldOverlap A z) = newMap A n (newOverlap m n z) :=
  (old_eq_new_iff A n _ _).mpr ⟨z, rfl, rfl⟩

theorem cover (q : Boundary A n) : q ∈ range (oldMap A n) ∪ range (newMap A n) :=
  OpenGluing.cover (transition A n) q

end Wikipedia.SmoothSixDPoincare.FramedSurgery
