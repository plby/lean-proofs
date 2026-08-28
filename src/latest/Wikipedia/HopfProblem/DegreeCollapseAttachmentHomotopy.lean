import Wikipedia.SmoothSixDPoincare.ClosedAttachment
import Mathlib.Topology.Homotopy.Basic

/-!
# Relative handle homotopies descend to the actual attached union

The lower subspace is fixed pointwise. The time-dependent quotient is a
genuine compact-to-Hausdorff quotient, so continuity is joint in time and
the attached-space point, including along the entire attaching face.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.Attachment

open Wikipedia.SmoothSixDPoincare

variable {K M : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace M] [T2Space M]
  (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))

abbrev Union := ↥(A ∪ range h)

def sumQuotient : C(A ⊕ K, Union A h) :=
  ⟨ClosedAttachment.sumMap A h, ClosedAttachment.continuous_sumMap A h⟩

omit [CompactSpace K] [T2Space M] [CompactSpace A] in
theorem sumQuotient_surjective : Function.Surjective (sumQuotient A h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨.inr k, rfl⟩

def cylinderQuotient : C(I × (A ⊕ K), I × Union A h) :=
  (ContinuousMap.id I).prodMap (sumQuotient A h)

omit [CompactSpace K] [T2Space M] [CompactSpace A] in
theorem cylinderQuotient_surjective : Function.Surjective (cylinderQuotient A h) := by
  rintro ⟨t, x⟩
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  exact ⟨(t, z), rfl⟩

theorem cylinderQuotient_isQuotientMap : IsQuotientMap (cylinderQuotient A h) :=
  .of_surjective_continuous (cylinderQuotient_surjective A h) (cylinderQuotient A h).continuous

variable {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B)

def familyOnSum : C(I × (A ⊕ K), Union A h) where
  toFun p := match p.2 with
    | .inl a => ⟨a.val, Or.inl a.property⟩
    | .inr k => ⟨h (H (p.1, k)), Or.inr ⟨H (p.1, k), rfl⟩⟩
  continuous_toFun := by
    have ha : Continuous (fun p : I × A => (⟨p.2.val, Or.inl p.2.property⟩ : Union A h)) :=
      (continuous_subtype_val.comp continuous_snd).subtype_mk _
    have hk : Continuous (fun p : I × K =>
        (⟨h (H p), Or.inr ⟨H p, rfl⟩⟩ : Union A h)) :=
      (h.continuous.comp H.continuous).subtype_mk _
    convert (ha.sumElim hk).comp
      (Homeomorph.prodSumDistrib : I × (A ⊕ K) ≃ₜ _).continuous using 1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

variable (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B)

include hinj hface in
omit [CompactSpace K] [T2Space M] [CompactSpace A] in
theorem familyOnSum_constant_on_fibres (p q : I × (A ⊕ K))
    (heq : cylinderQuotient A h p = cylinderQuotient A h q) :
    familyOnSum A B h H p = familyOnSum A B h H q := by
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  have ht : t = s := congrArg Prod.fst heq
  subst s
  have hab : sumQuotient A h a = sumQuotient A h b := congrArg Prod.snd heq
  have hv := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      exact Subtype.ext hv
    | inr k =>
      change a.val = h k at hv
      have hk : k ∈ B := (hface k).mp (hv ▸ a.property)
      apply Subtype.ext
      change a.val = h (H (t, k))
      rw [H.eq_fst t hk]
      exact hv
  | inr k =>
    cases b with
    | inl b =>
      change h k = b.val at hv
      have hk : k ∈ B := (hface k).mp (hv.symm ▸ b.property)
      apply Subtype.ext
      change h (H (t, k)) = b.val
      rw [H.eq_fst t hk]
      exact hv
    | inr l =>
      have hkl : k = l := hinj hv
      subst l
      rfl

/-- The actual jointly continuous family on the attached union. -/
def unionFamily : C(I × Union A h, Union A h) :=
  (cylinderQuotient_isQuotientMap A h).lift (familyOnSum A B h H)
    (familyOnSum_constant_on_fibres A B h H hinj hface)

@[simp] theorem unionFamily_apply (t : I) (z : A ⊕ K) :
    unionFamily A B h H hinj hface (t, sumQuotient A h z) = familyOnSum A B h H (t, z) :=
  ContinuousMap.congr_fun
    ((cylinderQuotient_isQuotientMap A h).lift_comp (familyOnSum A B h H)
      (familyOnSum_constant_on_fibres A B h H hinj hface)) (t, z)

theorem unionFamily_fixed_lower (t : I) (a : A) :
    unionFamily A B h H hinj hface (t, ⟨a.val, Or.inl a.property⟩) =
      ⟨a.val, Or.inl a.property⟩ :=
  unionFamily_apply A B h H hinj hface t (.inl a)

theorem unionFamily_on_handle (t : I) (k : K) :
    (unionFamily A B h H hinj hface (t, ⟨h k, Or.inr ⟨k, rfl⟩⟩)).val = h (H (t, k)) :=
  congrArg Subtype.val (unionFamily_apply A B h H hinj hface t (.inr k))

theorem unionFamily_zero (x : Union A h) : unionFamily A B h H hinj hface (0, x) = x := by
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  rw [unionFamily_apply]
  cases z with
  | inl a => rfl
  | inr k =>
    apply Subtype.ext
    exact congrArg h (H.apply_zero k)

end Wikipedia.HopfProblem.DegreeCollapse.Attachment
