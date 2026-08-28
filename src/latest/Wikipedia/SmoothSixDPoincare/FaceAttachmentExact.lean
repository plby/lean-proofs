import Wikipedia.SmoothSixDPoincare.FaceAttachmentMaps

/-!
# Exact fibers of a whole-piece attachment along an embedded face

An injective attaching map creates only the prescribed cross-piece
identifications. No old points or whole-handle points are identified with
each other. These are identities in the original `FaceAttachment.Space`.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

variable {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
  {B : Set K} (b : C(B, X))

def ExactRel : X ⊕ K → X ⊕ K → Prop
  | .inl x, .inl y => x = y
  | .inl x, .inr k => ∃ u : B, b u = x ∧ u.val = k
  | .inr k, .inl x => ∃ u : B, b u = x ∧ u.val = k
  | .inr k, .inr l => k = l

theorem exactRel_equivalence (hb : Injective b) : Equivalence (ExactRel b) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (x | k) <;> rfl
  · rintro (x | k) (y | l) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  · rintro (x | k) (y | l) (z | m) h₁ h₂
    · exact h₁.trans h₂
    · rcases h₁ with rfl
      exact h₂
    · obtain ⟨u, hu, hul⟩ := h₁
      obtain ⟨v, hv, hvl⟩ := h₂
      have huv : u = v := Subtype.ext (hul.trans hvl.symm)
      exact hu.symm.trans ((congrArg b huv).trans hv)
    · rcases h₂ with rfl
      exact h₁
    · rcases h₂ with rfl
      exact h₁
    · obtain ⟨u, hu, huk⟩ := h₁
      obtain ⟨v, hv, hvm⟩ := h₂
      have huv : u = v := hb (hu.trans hv.symm)
      exact huk.symm.trans ((congrArg Subtype.val huv).trans hvm)
    · rcases h₁ with rfl
      exact h₂
    · exact h₁.trans h₂

def exactSetoid (hb : Injective b) : Setoid (X ⊕ K) := ⟨ExactRel b, exactRel_equivalence b hb⟩

private def exactDetector (hb : Injective b) : Space b → Quotient (exactSetoid b hb) :=
  Quot.lift (Quotient.mk (exactSetoid b hb)) (by
    rintro (x | k) (y | l) h
    · exact h.elim
    · obtain ⟨hl, rfl⟩ := h
      exact Quotient.sound ⟨⟨l, hl⟩, rfl, rfl⟩
    · exact h.elim
    · exact h.elim)

theorem quotient_eq_iff (hb : Injective b) (p q : X ⊕ K) :
    Quot.mk (Rel b) p = Quot.mk (Rel b) q ↔ ExactRel b p q := by
  constructor
  · intro h
    exact Quotient.exact (congrArg (exactDetector b hb) h)
  · cases p with
    | inl x =>
      cases q with
      | inl y => intro h; exact congrArg (fun z => Quot.mk (Rel b) (.inl z)) h
      | inr k =>
        rintro ⟨u, rfl, rfl⟩
        exact face_identification b u
    | inr k =>
      cases q with
      | inl x =>
        rintro ⟨u, rfl, rfl⟩
        exact (face_identification b u).symm
      | inr l => intro h; exact congrArg (fun z => Quot.mk (Rel b) (.inr z)) h

theorem oldMap_eq_oldMap (hb : Injective b) (x y : X) :
    oldMap b x = oldMap b y ↔ x = y := quotient_eq_iff b hb _ _

theorem handleMap_eq_handleMap (hb : Injective b) (k l : K) :
    handleMap b k = handleMap b l ↔ k = l := quotient_eq_iff b hb _ _

theorem oldMap_eq_handleMap (hb : Injective b) (x : X) (k : K) :
    oldMap b x = handleMap b k ↔ ∃ u : B, b u = x ∧ u.val = k := quotient_eq_iff b hb _ _

theorem cover (z : Space b) : z ∈ range (oldMap b) ∪ range (handleMap b) :=
  induction_on b z (fun x => Or.inl ⟨x, rfl⟩) (fun k => Or.inr ⟨k, rfl⟩)

end Wikipedia.SmoothSixDPoincare.FaceAttachment
