import Wikipedia.HopfProblem.DegreeCollapseFiniteCellType
import Wikipedia.HopfProblem.DegreeCollapseAttachmentMaps
import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension

/-!
# Relative disk lifting propagates through finite homotopy cell constructions

The disk lifting premise explicitly retains every boundary value and the
entire prescribed boundary homotopy. It is not asserted for the original
sphere map here. Once established, this theorem constructs lifts on the
whole finite homotopy cell type using genuine quotient maps and homotopies.
-/

noncomputable section

open Set Metric
open scoped unitInterval ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.FiniteCells

open Wikipedia.SmoothSixDPoincare DiskCylinder AttachmentMaps

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (F : C(X, Y))

/-- Exact relative lifting on all disks up to the stated real dimension. -/
def RelativeDiskLifting (d : ℕ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Module.finrank ℝ V ≤ d →
    ∀ (a : C(Sphere (E := V), X)) (u : C(Disk (E := V), Y))
      (H : C(I × Sphere (E := V), Y)),
      (∀ s, H (0, s) = F (a s)) →
      (∀ s, H (1, s) = u (boundaryToDisk s)) →
      ∃ (v : C(Disk (E := V), X)) (G : C(I × Disk (E := V), Y)),
        (∀ s, v (boundaryToDisk s) = a s) ∧
        (∀ z, G (0, z) = F (v z)) ∧
        (∀ z, G (1, z) = u z) ∧
        ∀ t s, G (t, boundaryToDisk s) = H (t, s)

/-- Actual lifts up to homotopy, for all maps with the specified domain. -/
def MapsLift (Z : Type) [TopologicalSpace Z] : Prop :=
  ∀ u : C(Z, Y), ∃ v : C(Z, X), (F.comp v).Homotopic u

theorem mapsLift_empty (Z : Type) [TopologicalSpace Z] [IsEmpty Z] : MapsLift F Z := by
  intro u
  let v : C(Z, X) := ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun z => isEmptyElim z)⟩
  refine ⟨v, ?_⟩
  have he : F.comp v = u := ContinuousMap.ext (fun z => isEmptyElim z)
  rw [he]

theorem mapsLift_equiv {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    (e : Z ≃ₕ W) (h : MapsLift F Z) : MapsLift F W := by
  intro u
  obtain ⟨v, hv⟩ := h (u.comp e.toFun)
  refine ⟨v.comp e.invFun, ?_⟩
  have h₁ := hv.comp (ContinuousMap.Homotopic.refl e.invFun)
  have h₂ := (ContinuousMap.Homotopic.refl u).comp e.right_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using h₁.trans h₂

variable {d : ℕ} (hF : RelativeDiskLifting F d)

include hF in
theorem mapsLift_attach {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace M]
    (A : Set M) (h : C(MorseHandle.UnitDisk V, M))
    (hb : ∀ z : MorseHandle.UnitDisk V, ‖(z : V)‖ = 1 → h z ∈ A)
    (hd : Module.finrank ℝ V ≤ d) (hA : MapsLift F A) :
    MapsLift F (ClosedAttachment.Space A {z : MorseHandle.UnitDisk V | ‖(z : V)‖ = 1} h) := by
  intro u
  let B : Set (MorseHandle.UnitDisk V) := {z | ‖(z : V)‖ = 1}
  let iA := oldInclusion A B h
  let iD := cellInclusion A B h
  obtain ⟨vA, ⟨HA⟩⟩ := hA (u.comp iA)
  let b : C(Sphere (E := V), A) :=
    ⟨fun s => ⟨h (boundaryToDisk s), hb (boundaryToDisk s)
      (mem_sphere_zero_iff_norm.mp s.property)⟩,
      (h.continuous.comp boundaryToDisk.continuous).subtype_mk _⟩
  let H : C(I × Sphere (E := V), Y) :=
    HA.toContinuousMap.comp ((ContinuousMap.id I).prodMap b)
  have h0 : ∀ s, H (0, s) = F ((vA.comp b) s) := fun s => HA.map_zero_left (b s)
  have h1 : ∀ s, H (1, s) = (u.comp iD) (boundaryToDisk s) := by
    intro s
    change HA (1, b s) = u (iD (boundaryToDisk s))
    exact (HA.map_one_left (b s)).trans (congrArg u
      (boundary_eq A B h (b s) (boundaryToDisk s)
        (mem_sphere_zero_iff_norm.mp s.property) rfl))
  obtain ⟨vD, GD, hvD, hGD0, hGD1, hGDside⟩ := hF V hd (vA.comp b) (u.comp iD) H h0 h1
  have hcompat : ∀ a z, z ∈ B → a.val = h z → vA a = vD z := by
    intro a z hz ha
    let s : Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg vA hab).trans (hvD s).symm
  let v := glue A B h vA vD hcompat
  have hhom : ∀ t a z, z ∈ B → a.val = h z → HA (t, a) = GD (t, z) := by
    intro t a z hz ha
    let s : Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg (fun a => HA (t, a)) hab).trans (hGDside t s).symm
  refine ⟨v, ⟨{
    toContinuousMap := glueFamily A B h HA.toContinuousMap GD hhom
    map_zero_left := ?_
    map_one_left := ?_
  }⟩⟩
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_zero_left a
      | inr z => exact hGD0 z
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_one_left a
      | inr z => exact hGD1 z

include hF in
/-- All cellwise lifts and their comparison homotopies assemble to a genuine global lift. -/
theorem mapsLift_of_built {Z : Type} [TopologicalSpace Z] (hZ : Built d Z) : MapsLift F Z := by
  induction hZ with
  | empty Z => exact mapsLift_empty F Z
  | equiv e _ ih => exact mapsLift_equiv F e ih
  | attach A h hb hd _ ih => exact mapsLift_attach F hF A h hb hd ih

end Wikipedia.HopfProblem.DegreeCollapse.FiniteCells
