import ErdosProblems.Erdos593.TripleSystem.Embedding
import ErdosProblems.Erdos593.TripleSystem.Isomorph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# One-point amalgamations

The vertex type is the quotient of a tagged disjoint union that identifies
exactly the two selected roots. Edge indices retain their factor tags, and
incidence is defined by the image of each factor edge under its quotient
inclusion. The final universal-property lemmas support reconstruction up to
triple-system isomorphism.
-/

namespace Erdos593

universe u₀ v₀ u₁ v₁

namespace TripleSystem.OnePointAmalgamation

variable {V₀ : Type u₀} {E₀ : Type v₀}
variable {V₁ : Type u₁} {E₁ : Type v₁}

/-- The equivalence relation on the tagged disjoint union which identifies only
the two selected roots. -/
def Rel (r₀ : V₀) (r₁ : V₁) : Sum V₀ V₁ → Sum V₀ V₁ → Prop
  | .inl x, .inl y => x = y
  | .inr x, .inr y => x = y
  | .inl x, .inr y => x = r₀ ∧ y = r₁
  | .inr y, .inl x => y = r₁ ∧ x = r₀

private theorem rel_refl (r₀ : V₀) (r₁ : V₁) (x : Sum V₀ V₁) :
    Rel r₀ r₁ x x := by
  cases x <;> simp [Rel]

private theorem rel_symm (r₀ : V₀) (r₁ : V₁) {x y : Sum V₀ V₁}
    (h : Rel r₀ r₁ x y) : Rel r₀ r₁ y x := by
  cases x <;> cases y <;> simp_all [Rel]

private theorem rel_trans (r₀ : V₀) (r₁ : V₁) {x y z : Sum V₀ V₁}
    (hxy : Rel r₀ r₁ x y) (hyz : Rel r₀ r₁ y z) : Rel r₀ r₁ x z := by
  cases x <;> cases y <;> cases z <;> simp_all [Rel]

/-- The setoid identifying the two selected roots and nothing else. -/
def vertexSetoid (r₀ : V₀) (r₁ : V₁) : Setoid (Sum V₀ V₁) where
  r := Rel r₀ r₁
  iseqv := ⟨
    fun x => rel_refl r₀ r₁ x,
    fun h => rel_symm r₀ r₁ h,
    fun hxy hyz => rel_trans r₀ r₁ hxy hyz⟩

/-- Vertex type of the binary one-point amalgamation. -/
abbrev Vertex (r₀ : V₀) (r₁ : V₁) := Quotient (vertexSetoid r₀ r₁)

/-- Inclusion of the left factor. -/
def left (r₀ : V₀) (r₁ : V₁) (x : V₀) : Vertex r₀ r₁ :=
  Quotient.mk (vertexSetoid r₀ r₁) (.inl x)

/-- Inclusion of the right factor. -/
def right (r₀ : V₀) (r₁ : V₁) (y : V₁) : Vertex r₀ r₁ :=
  Quotient.mk (vertexSetoid r₀ r₁) (.inr y)

@[simp]
theorem left_eq_left_iff (r₀ : V₀) (r₁ : V₁) (x y : V₀) :
    left r₀ r₁ x = left r₀ r₁ y ↔ x = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro rfl
    rfl

@[simp]
theorem right_eq_right_iff (r₀ : V₀) (r₁ : V₁) (x y : V₁) :
    right r₀ r₁ x = right r₀ r₁ y ↔ x = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro rfl
    rfl

@[simp]
theorem left_eq_right_iff (r₀ : V₀) (r₁ : V₁) (x : V₀) (y : V₁) :
    left r₀ r₁ x = right r₀ r₁ y ↔ x = r₀ ∧ y = r₁ := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro ⟨rfl, rfl⟩
    apply Quotient.sound
    exact ⟨rfl, rfl⟩

@[simp]
theorem right_eq_left_iff (r₀ : V₀) (r₁ : V₁) (y : V₁) (x : V₀) :
    right r₀ r₁ y = left r₀ r₁ x ↔ y = r₁ ∧ x = r₀ := by
  rw [eq_comm, left_eq_right_iff, and_comm]

theorem root_eq (r₀ : V₀) (r₁ : V₁) :
    left r₀ r₁ r₀ = right r₀ r₁ r₁ := by
  simp

theorem left_injective (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (left r₀ r₁) := by
  intro x y h
  exact (left_eq_left_iff r₀ r₁ x y).mp h

theorem right_injective (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (right r₀ r₁) := by
  intro x y h
  exact (right_eq_right_iff r₀ r₁ x y).mp h

/-- Recursor out of the amalgamated vertex type.  The only compatibility
condition is agreement at the selected roots. -/
def lift {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) :
    Vertex r₀ r₁ → X :=
  Quotient.lift (Sum.elim f₀ f₁) (by
    intro a b hab
    change Rel r₀ r₁ a b at hab
    cases a <;> cases b <;> simp_all [Rel])

@[simp]
theorem lift_left {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) (x : V₀) :
    lift r₀ r₁ f₀ f₁ hroot (left r₀ r₁ x) = f₀ x := rfl

@[simp]
theorem lift_right {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) (y : V₁) :
    lift r₀ r₁ f₀ f₁ hroot (right r₀ r₁ y) = f₁ y := rfl

/-- The universal map is injective when the two input maps are injective and
have exactly the selected root as their cross-factor collision. -/
theorem lift_injective {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁) :
    Function.Injective (lift r₀ r₁ f₀ f₁ hroot) := by
  intro q q' h
  induction q using Quotient.inductionOn with
  | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
          cases a with
          | inl x =>
              cases b with
              | inl y =>
                  apply Quotient.sound
                  exact h₀ h
              | inr y =>
                  apply Quotient.sound
                  exact (hcross x y).mp h
          | inr x =>
              cases b with
              | inl y =>
                  apply Quotient.sound
                  have hyx := (hcross y x).mp h.symm
                  exact ⟨hyx.2, hyx.1⟩
              | inr y =>
                  apply Quotient.sound
                  exact h₁ h

/-- Every amalgamated vertex comes from at least one factor. -/
theorem exists_left_or_right (r₀ : V₀) (r₁ : V₁) (q : Vertex r₀ r₁) :
    (∃ x, left r₀ r₁ x = q) ∨ (∃ y, right r₀ r₁ y = q) := by
  induction q using Quotient.inductionOn with
  | _ s =>
      cases s with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr ⟨y, rfl⟩

/-- Reconstruction-facing universal property: two injections whose images
cover the target and meet exactly at the selected roots induce an equivalence
from the canonical amalgamated vertex type. -/
noncomputable def vertexEquivOfMaps {W : Type*}
    (r₀ : V₀) (r₁ : V₁) (f₀ : V₀ → W) (f₁ : V₁ → W)
    (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁)
    (hcover : ∀ w, (∃ x, f₀ x = w) ∨ (∃ y, f₁ y = w)) :
    Vertex r₀ r₁ ≃ W :=
  Equiv.ofBijective (lift r₀ r₁ f₀ f₁ hroot) ⟨
    lift_injective r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross,
    by
      intro w
      rcases hcover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨left r₀ r₁ x, rfl⟩
      · exact ⟨right r₀ r₁ y, rfl⟩⟩

/-- Images of arbitrary subsets from opposite factors intersect in at most the
single amalgamation root. -/
theorem cross_image_inter_subsingleton (r₀ : V₀) (r₁ : V₁)
    (s : Set V₀) (t : Set V₁) :
    (left r₀ r₁ '' s ∩ right r₀ r₁ '' t).Subsingleton := by
  intro q hq q' hq'
  rcases hq.1 with ⟨x, hx, hxq⟩
  rcases hq.2 with ⟨y, hy, hyq⟩
  rcases hq'.1 with ⟨x', hx', hxq'⟩
  rcases hq'.2 with ⟨y', hy', hyq'⟩
  have hxy := (left_eq_right_iff r₀ r₁ x y).mp (hxq.trans hyq.symm)
  have hxy' := (left_eq_right_iff r₀ r₁ x' y').mp (hxq'.trans hyq'.symm)
  exact hxq.symm.trans ((congrArg (left r₀ r₁) (hxy.1.trans hxy'.1.symm)).trans hxq')

/-- Edge indices retain their factor tag. -/
abbrev Edge (E₀ : Type v₀) (E₁ : Type v₁) := E₀ ⊕ E₁

/-- Incidence in the amalgam is exactly the image of incidence in the relevant
factor; no new edge is introduced. -/
def Inc (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) : Vertex r₀ r₁ → Edge E₀ E₁ → Prop
  | q, .inl e => q ∈ left r₀ r₁ '' F₀.edgeSet e
  | q, .inr e => q ∈ right r₀ r₁ '' F₁.edgeSet e

@[simp]
theorem incidenceSet_left (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) (e : E₀) :
    {q | Inc F₀ F₁ r₀ r₁ q (.inl e)} =
      left r₀ r₁ '' F₀.edgeSet e := rfl

@[simp]
theorem incidenceSet_right (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) (e : E₁) :
    {q | Inc F₀ F₁ r₀ r₁ q (.inr e)} =
      right r₀ r₁ '' F₁.edgeSet e := rfl

@[simp]
theorem inc_left_left_iff (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (x : V₀) (e : E₀) :
    Inc F₀ F₁ r₀ r₁ (left r₀ r₁ x) (.inl e) ↔ F₀.Inc x e := by
  simp [Inc]

@[simp]
theorem inc_right_right_iff (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (y : V₁) (e : E₁) :
    Inc F₀ F₁ r₀ r₁ (right r₀ r₁ y) (.inr e) ↔ F₁.Inc y e := by
  simp [Inc]

/-- A left-factor point is incident with a right-factor edge exactly when it is
the amalgamation root and the selected right root lies on that edge. -/
@[simp]
theorem inc_left_right_iff (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (x : V₀) (e : E₁) :
    Inc F₀ F₁ r₀ r₁ (left r₀ r₁ x) (.inr e) ↔
      x = r₀ ∧ F₁.Inc r₁ e := by
  simp [Inc, and_comm]

/-- A right-factor point is incident with a left-factor edge exactly when it is
the amalgamation root and the selected left root lies on that edge. -/
@[simp]
theorem inc_right_left_iff (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (y : V₁) (e : E₀) :
    Inc F₀ F₁ r₀ r₁ (right r₀ r₁ y) (.inl e) ↔
      y = r₁ ∧ F₀.Inc r₀ e := by
  simp [Inc, and_comm]

theorem incidenceSet_ncard (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    ∀ e : Edge E₀ E₁,
      Set.ncard {q | Inc F₀ F₁ r₀ r₁ q e} = 3 := by
  rintro (e | e)
  · rw [incidenceSet_left,
      Set.ncard_image_of_injective _ (left_injective r₀ r₁)]
    exact F₀.edgeSet_ncard e
  · rw [incidenceSet_right,
      Set.ncard_image_of_injective _ (right_injective r₀ r₁)]
    exact F₁.edgeSet_ncard e

theorem cross_edgeSets_ne (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (e : E₀) (f : E₁) :
    left r₀ r₁ '' F₀.edgeSet e ≠ right r₀ r₁ '' F₁.edgeSet f := by
  intro hsets
  have hsub : F₀.edgeSet e ⊆ ({r₀} : Set V₀) := by
    intro x hx
    have hx' : left r₀ r₁ x ∈ left r₀ r₁ '' F₀.edgeSet e :=
      ⟨x, hx, rfl⟩
    rw [hsets] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    exact (left_eq_right_iff r₀ r₁ x y).mp hyx.symm |>.1
  have hcard := Set.ncard_le_ncard hsub (Set.finite_singleton r₀)
  rw [F₀.edgeSet_ncard, Set.ncard_singleton] at hcard
  omega

theorem incidenceSet_injective (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (fun e : Edge E₀ E₁ =>
      {q | Inc F₀ F₁ r₀ r₁ q e}) := by
  intro e f h
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          congr 1
          apply F₀.edgeSet_injective
          apply (Set.image_eq_image (left_injective r₀ r₁)).mp
          exact h
      | inr f =>
          exact False.elim (cross_edgeSets_ne F₀ F₁ r₀ r₁ e f h)
  | inr e =>
      cases f with
      | inl f =>
          exact False.elim (cross_edgeSets_ne F₀ F₁ r₀ r₁ f e h.symm)
      | inr f =>
          congr 1
          apply F₁.edgeSet_injective
          apply (Set.image_eq_image (right_injective r₀ r₁)).mp
          exact h

/-- Canonical edge-indexed one-point amalgamation. -/
def amalgam (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) : TripleSystem (Vertex r₀ r₁) (Edge E₀ E₁) where
  Inc := Inc F₀ F₁ r₀ r₁
  edge_ncard := incidenceSet_ncard F₀ F₁ r₀ r₁
  simple := incidenceSet_injective F₀ F₁ r₀ r₁

/-- Canonical non-induced embedding of the left factor into the amalgam. -/
def leftFactorEmbedding (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    F₀.Embedding (amalgam F₀ F₁ r₀ r₁) where
  vertex := ⟨left r₀ r₁, left_injective r₀ r₁⟩
  edge := Sum.inl
  map_edge := by
    intro e
    rfl

/-- Canonical non-induced embedding of the right factor into the amalgam. -/
def rightFactorEmbedding (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    F₁.Embedding (amalgam F₀ F₁ r₀ r₁) where
  vertex := ⟨right r₀ r₁, right_injective r₀ r₁⟩
  edge := Sum.inr
  map_edge := by
    intro e
    rfl

/-- If a target is covered by two pieces meeting only at their selected roots,
and its edge indices are exactly the tagged union with the expected edge-set
images, then it is isomorphic to the canonical one-point amalgamation. -/
noncomputable def isoOfMaps {W : Type*} {D : Type*}
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (K : TripleSystem W D) (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → W) (f₁ : V₁ → W)
    (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁)
    (hcover : ∀ w, (∃ x, f₀ x = w) ∨ (∃ y, f₁ y = w))
    (edgeEquiv : Edge E₀ E₁ ≃ D)
    (hmap₀ : ∀ e, f₀ '' F₀.edgeSet e = K.edgeSet (edgeEquiv (.inl e)))
    (hmap₁ : ∀ e, f₁ '' F₁.edgeSet e = K.edgeSet (edgeEquiv (.inr e))) :
    Iso (amalgam F₀ F₁ r₀ r₁) K where
  vertexEquiv := vertexEquivOfMaps r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross hcover
  edgeEquiv := edgeEquiv
  map_inc_iff := by
    intro q e
    let ve := vertexEquivOfMaps r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross hcover
    have hve_injective : Function.Injective ve := ve.injective
    have himage : ve '' (amalgam F₀ F₁ r₀ r₁).edgeSet e =
        K.edgeSet (edgeEquiv e) := by
      cases e with
      | inl e =>
          change ve '' (left r₀ r₁ '' F₀.edgeSet e) = _
          rw [Set.image_image]
          change f₀ '' F₀.edgeSet e = _
          exact hmap₀ e
      | inr e =>
          change ve '' (right r₀ r₁ '' F₁.edgeSet e) = _
          rw [Set.image_image]
          change f₁ '' F₁.edgeSet e = _
          exact hmap₁ e
    change q ∈ (amalgam F₀ F₁ r₀ r₁).edgeSet e ↔
      ve q ∈ K.edgeSet (edgeEquiv e)
    rw [← himage]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q', hq', hqq'⟩
      exact hqq' |> hve_injective |> fun h => h ▸ hq'

/-- A finite input pair gives a finite amalgamated vertex type; package this as
a named definition so callers can opt into the noncomputable `Fintype`. -/
@[reducible]
noncomputable def vertexFintype (r₀ : V₀) (r₁ : V₁)
    [Fintype V₀] [Fintype V₁] : Fintype (Vertex r₀ r₁) :=
  Fintype.ofFinite _

end TripleSystem.OnePointAmalgamation

end Erdos593
