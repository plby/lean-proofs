import ErdosProblems.Erdos1123.Coupling

/-! # A total coupling induces an isomorphism of the Boolean quotients -/

namespace Erdos1123

open Filter
open scoped Topology symmDiff

variable {α β : Type*} {W : WeightSequence α} {V : WeightSequence β}

namespace Coupling

variable (C : Coupling W V)

/-- Reverse the two sides of a coupling. -/
def symm : Coupling V W where
  algebra :=
    { carrier := {p | p.swap ∈ C.algebra}
      supClosed' := fun _ h₁ _ h₂ => C.algebra.sup_mem h₁ h₂
      infClosed' := fun _ h₁ _ h₂ => C.algebra.inf_mem h₁ h₂
      compl_mem' := fun h => C.algebra.compl_mem h
      bot_mem' := C.algebra.bot_mem }
  matching := by
    intro p hp
    simpa only [neg_sub, neg_zero, Prod.swap] using (C.matching p.swap hp).neg

instance symm_countable [Countable C.algebra] : Countable C.symm.algebra := by
  apply Function.Injective.countable
    (f := fun p : C.symm.algebra => (⟨p.val.swap, p.property⟩ : C.algebra))
  intro p q hpq
  apply Subtype.ext
  exact Prod.swap_injective (congrArg Subtype.val hpq)

theorem null_iff {p : Set α × Set β} (hp : p ∈ C.algebra) : W.IsNull p.1 ↔ V.IsNull p.2 := by
  have h := C.matching p hp
  constructor
  · intro hW
    simpa only [WeightSequence.IsNull, sub_sub_cancel, sub_zero] using hW.sub h
  · intro hV
    simpa only [WeightSequence.IsNull, sub_add_cancel, zero_add] using h.add hV

theorem symmDiff_mem {p q : Set α × Set β} (hp : p ∈ C.algebra) (hq : q ∈ C.algebra) :
    (p.1 ∆ q.1, p.2 ∆ q.2) ∈ C.algebra := by
  have h₁ := C.algebra.sdiff_mem hp hq
  have h₂ := C.algebra.sdiff_mem hq hp
  exact C.algebra.sup_mem h₁ h₂

theorem pair_quotient_eq_iff {p q : Set α × Set β} (hp : p ∈ C.algebra) (hq : q ∈ C.algebra) :
    W.quotientMap p.1 = W.quotientMap q.1 ↔ V.quotientMap p.2 = V.quotientMap q.2 := by
  exact (W.quotientMap_eq_iff p.1 q.1).trans
    ((C.null_iff (C.symmDiff_mem hp hq)).trans (V.quotientMap_eq_iff p.2 q.2).symm)

/-- A coupling containing a pair for every set on both sides yields an actual
Boolean-algebra isomorphism, not just a correspondence between representatives. -/
noncomputable def quotientIso
    (hDomain : ∀ A : Set α, ∃ B : Set β, (A, B) ∈ C.algebra)
    (hRange : ∀ B : Set β, ∃ A : Set α, (A, B) ∈ C.algebra) : W.Algebra ≃o V.Algebra := by
  classical
  choose partner hPartner using hDomain
  choose rep hRep using W.quotientMap_surjective
  let f : W.Algebra → V.Algebra := fun a => V.quotientMap (partner (rep a))
  have hf (p : Set α × Set β) (hp : p ∈ C.algebra) :
      f (W.quotientMap p.1) = V.quotientMap p.2 := by
    apply (C.pair_quotient_eq_iff (hPartner (rep (W.quotientMap p.1))) hp).mp
    exact hRep _
  have hInjective : Function.Injective f := by
    intro a b hab
    have h := (C.pair_quotient_eq_iff (hPartner (rep a)) (hPartner (rep b))).mpr hab
    simpa only [hRep] using h
  have hSurjective : Function.Surjective f := by
    intro b
    obtain ⟨B, rfl⟩ := V.quotientMap_surjective b
    obtain ⟨A, hA⟩ := hRange B
    exact ⟨W.quotientMap A, hf (A, B) hA⟩
  have hInf (a b : W.Algebra) : f (a ⊓ b) = f a ⊓ f b := by
    have hp := hPartner (rep a)
    have hq := hPartner (rep b)
    have h := hf ((rep a, partner (rep a)) ⊓ (rep b, partner (rep b)))
      (C.algebra.inf_mem hp hq)
    change f (W.quotientMap (rep a ∩ rep b)) =
      V.quotientMap (partner (rep a) ∩ partner (rep b)) at h
    have hw : W.quotientMap (rep a ∩ rep b) = a ⊓ b := by
      exact (map_inf W.quotientMap (rep a) (rep b)).trans (congrArg₂ (· ⊓ ·) (hRep a) (hRep b))
    have hv : V.quotientMap (partner (rep a) ∩ partner (rep b)) = f a ⊓ f b :=
      map_inf V.quotientMap _ _
    rwa [hw, hv] at h
  refine ⟨Equiv.ofBijective f ⟨hInjective, hSurjective⟩, ?_⟩
  intro a b
  change f a ≤ f b ↔ a ≤ b
  rw [← inf_eq_left, ← hInf, hInjective.eq_iff, inf_eq_left]

end Coupling
end Erdos1123
