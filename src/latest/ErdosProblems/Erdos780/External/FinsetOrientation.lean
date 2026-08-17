import Mathlib

open Function

namespace Finset

section ImageOrientation

variable {V W U R : Type*}

/-- Compare an equivalence of two `n`-element finsets with their increasing enumerations. -/
noncomputable def orientationPerm [LinearOrder V] [LinearOrder W] {n : ℕ}
    (s : Finset V) (t : Finset W) (hs : s.card = n) (ht : t.card = n)
    (e : s ≃ t) : Equiv.Perm (Fin n) :=
  (s.orderIsoOfFin hs).toEquiv |>.trans e |>.trans (t.orderIsoOfFin ht).symm.toEquiv

/-- The sign of an equivalence relative to the increasing orientations on its finsets. -/
noncomputable def orientationSign [LinearOrder V] [LinearOrder W] {n : ℕ}
    (s : Finset V) (t : Finset W) (hs : s.card = n) (ht : t.card = n)
    (e : s ≃ t) : ℤˣ :=
  Equiv.Perm.sign (orientationPerm s t hs ht e)

/-- The auxiliary common cardinal and its equality witnesses do not affect the sign. -/
theorem orientationSign_card_congr [LinearOrder V] [LinearOrder W] {n m : ℕ}
    (s : Finset V) (t : Finset W)
    (hsn : s.card = n) (htn : t.card = n) (hsm : s.card = m) (htm : t.card = m)
    (e : s ≃ t) :
    orientationSign s t hsn htn e = orientationSign s t hsm htm e := by
  subst n
  subst m
  rfl

theorem orientationPerm_trans [LinearOrder V] [LinearOrder W] [LinearOrder U] {n : ℕ}
    (s : Finset V) (t : Finset W) (u : Finset U)
    (hs : s.card = n) (ht : t.card = n) (hu : u.card = n)
    (e : s ≃ t) (d : t ≃ u) :
    orientationPerm s u hs hu (e.trans d) =
      (orientationPerm s t hs ht e).trans (orientationPerm t u ht hu d) := by
  ext i
  simp [orientationPerm]

/-- Orientation signs multiply under composition (the second map's sign is the left factor,
matching `Equiv.Perm.sign_trans`). -/
theorem orientationSign_trans [LinearOrder V] [LinearOrder W] [LinearOrder U] {n : ℕ}
    (s : Finset V) (t : Finset W) (u : Finset U)
    (hs : s.card = n) (ht : t.card = n) (hu : u.card = n)
    (e : s ≃ t) (d : t ≃ u) :
    orientationSign s u hs hu (e.trans d) =
      orientationSign t u ht hu d * orientationSign s t hs ht e := by
  rw [orientationSign, orientationPerm_trans, Equiv.Perm.sign_trans]
  rfl

/-- An injective map on a finset is an equivalence with its finset image. -/
noncomputable def imageEquiv [DecidableEq W] (s : Finset V) (f : V → W)
    (hf : Set.InjOn f s) : s ≃ s.image f :=
  Equiv.ofBijective
    (fun x : s ↦ ⟨f x, mem_image_of_mem f x.2⟩)
    ⟨fun x y h ↦ Subtype.ext (hf x.2 y.2 (Subtype.ext_iff.mp h)),
      fun y ↦ by
        rcases mem_image.mp y.2 with ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

@[simp] theorem coe_imageEquiv_apply [DecidableEq W] (s : Finset V) (f : V → W)
    (hf : Set.InjOn f s) (x : s) :
    ((imageEquiv s f hf x : s.image f) : W) = f x := rfl

/-- The permutation comparing the increasing enumeration of `s`, transported by `f`,
with the increasing enumeration of `s.image f`. -/
noncomputable def imagePerm [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) : Equiv.Perm (Fin s.card) :=
  orientationPerm s (s.image f) rfl (card_image_of_injOn hf) (imageEquiv s f hf)

@[simp] theorem imagePerm_apply [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) (i : Fin s.card) :
    imagePerm s f hf i =
      ((s.image f).orderIsoOfFin (card_image_of_injOn hf)).symm
        ⟨f (s.orderIsoOfFin rfl i), mem_image_of_mem f (s.orderIsoOfFin rfl i).2⟩ :=
  rfl

/-- Canonical orientation sign of an injective finite image. -/
noncomputable def imageSign [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) : ℤˣ :=
  Equiv.Perm.sign (imagePerm s f hf)

/-- Functoriality of image orientation before normalizing the iterated image with
`Finset.image_image`. This form avoids dependent casts and is often the easiest one to rewrite. -/
theorem imageSign_trans_nested [LinearOrder V] [LinearOrder W] [LinearOrder U]
    (s : Finset V) (f : V → W) (g : W → U)
    (hf : Set.InjOn f s) (hg : Set.InjOn g (s.image f)) :
    orientationSign s ((s.image f).image g) rfl
        ((card_image_of_injOn hg).trans (card_image_of_injOn hf))
        ((imageEquiv s f hf).trans (imageEquiv (s.image f) g hg)) =
      imageSign (s.image f) g hg * imageSign s f hf := by
  change _ =
    orientationSign (s.image f) ((s.image f).image g) rfl
        (card_image_of_injOn hg) (imageEquiv (s.image f) g hg) *
      orientationSign s (s.image f) rfl
        (card_image_of_injOn hf) (imageEquiv s f hf)
  rw [orientationSign_trans s (s.image f) ((s.image f).image g)
    rfl (card_image_of_injOn hf)
    ((card_image_of_injOn hg).trans (card_image_of_injOn hf))
    (imageEquiv s f hf) (imageEquiv (s.image f) g hg)]
  exact congrArg₂ (· * ·)
    (orientationSign_card_congr
      (s.image f) ((s.image f).image g)
      (card_image_of_injOn hf)
      ((card_image_of_injOn hg).trans (card_image_of_injOn hf))
      rfl (card_image_of_injOn hg)
      (imageEquiv (s.image f) g hg))
    rfl

/-- A map which preserves the strict order on `s` has positive image orientation. -/
@[simp] theorem imageSign_eq_one_of_strictMonoOn [LinearOrder V] [LinearOrder W]
    (s : Finset V) (f : V → W) (hf : StrictMonoOn f s) :
    imageSign s f hf.injOn = 1 := by
  suffices imagePerm s f hf.injOn = 1 by simp [imageSign, this]
  have hp : StrictMono (imagePerm s f hf.injOn) := by
    intro i j hij
    rw [imagePerm_apply, imagePerm_apply]
    apply ((s.image f).orderIsoOfFin (card_image_of_injOn hf.injOn)).symm.strictMono
    exact hf (s.orderIsoOfFin rfl i).2 (s.orderIsoOfFin rfl j).2
      ((s.orderIsoOfFin rfl).strictMono hij)
  apply Equiv.ext
  exact congrFun hp.eq_id

/-- The normalized coefficient for the image of an ordered finite set: it is its canonical
orientation sign if `f` is injective on `s`, and zero otherwise. -/
noncomputable def imageCoeff [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) : R :=
  if hf : Set.InjOn f s then (((imageSign s f hf : ℤˣ) : ℤ) : R) else 0

@[simp] theorem imageCoeff_of_injOn [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) (hf : Set.InjOn f s) :
    imageCoeff (R := R) s f = (((imageSign s f hf : ℤˣ) : ℤ) : R) := by
  simp [imageCoeff, hf]

@[simp] theorem imageCoeff_of_not_injOn [LinearOrder V] [LinearOrder W] [Ring R]
    (s : Finset V) (f : V → W) (hf : ¬ Set.InjOn f s) :
    imageCoeff (R := R) s f = 0 := by
  simp [imageCoeff, hf]

end ImageOrientation

end Finset
