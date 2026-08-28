import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic.Linarith

/-!
# The actual mapping torus of a homeomorphism

The mapping torus is the quotient of `ℝ × X` by the deck transformations
`(t,x) ↦ (t+n, f^(-n) x)`.  In particular `[t+1,x] = [t,f x]`.
The quotient map is continuous and open, and the real coordinate descends
to an actual continuous map to `AddCircle 1`.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.MappingTorus

variable {X : Type*} [TopologicalSpace X]

abbrev Circle := AddCircle (1 : ℝ)

/-- The integer deck transformation defining the mapping torus. -/
def deck (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) : ℝ × X :=
  (p.1 + (n : ℝ), (f ^ (-n)) p.2)

@[simp] theorem deck_zero (f : X ≃ₜ X) (p : ℝ × X) : deck f 0 p = p := by
  simp [deck]

theorem deck_add (f : X ≃ₜ X) (m n : ℤ) (p : ℝ × X) :
    deck f (m + n) p = deck f m (deck f n p) := by
  apply Prod.ext
  · simp only [deck, Int.cast_add]
    abel
  · simp only [deck, neg_add, zpow_add, Homeomorph.mul_apply]

theorem deck_continuous (f : X ≃ₜ X) (n : ℤ) : Continuous (deck f n) :=
  (continuous_fst.add continuous_const).prodMk
    ((f ^ (-n)).continuous.comp continuous_snd)

/-- Each deck transformation is an actual homeomorphism. -/
def deckHomeomorph (f : X ≃ₜ X) (n : ℤ) : (ℝ × X) ≃ₜ (ℝ × X) where
  toFun := deck f n
  invFun := deck f (-n)
  left_inv p := by rw [← deck_add, neg_add_cancel, deck_zero]
  right_inv p := by rw [← deck_add, add_neg_cancel, deck_zero]
  continuous_toFun := deck_continuous f n
  continuous_invFun := deck_continuous f (-n)

/-- Two points are equivalent exactly when an integer deck transformation
takes the first to the second. -/
def orbitSetoid (f : X ≃ₜ X) : Setoid (ℝ × X) where
  r p q := ∃ n : ℤ, deck f n p = q
  iseqv := {
    refl := fun p ↦ ⟨0, deck_zero f p⟩
    symm := by
      rintro p q ⟨n, rfl⟩
      exact ⟨-n, by rw [← deck_add, neg_add_cancel, deck_zero]⟩
    trans := by
      rintro p q r ⟨m, rfl⟩ ⟨n, rfl⟩
      exact ⟨n + m, deck_add f n m p⟩ }

/-- The mapping torus, with the quotient topology. -/
def Torus (f : X ≃ₜ X) := Quotient (orbitSetoid f)

instance (f : X ≃ₜ X) : TopologicalSpace (Torus f) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid f)))

/-- The actual quotient projection from the real cylinder. -/
def mk (f : X ≃ₜ X) (p : ℝ × X) : Torus f := Quotient.mk (orbitSetoid f) p

theorem mk_continuous (f : X ≃ₜ X) : Continuous (mk f) :=
  continuous_quotient_mk'

theorem mk_surjective (f : X ≃ₜ X) : Function.Surjective (mk f) :=
  Quotient.mk_surjective

theorem mk_eq_mk_iff (f : X ≃ₜ X) (p q : ℝ × X) :
    mk f p = mk f q ↔
      ∃ n : ℤ, q.1 = p.1 + (n : ℝ) ∧ q.2 = (f ^ (-n)) p.2 := by
  change (Quotient.mk (orbitSetoid f) p = Quotient.mk (orbitSetoid f) q) ↔ _
  rw [Quotient.eq]
  change (∃ n : ℤ, deck f n p = q) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg Prod.fst hn).symm, (congrArg Prod.snd hn).symm⟩
  · rintro ⟨n, ht, hx⟩
    exact ⟨n, Prod.ext ht.symm hx.symm⟩

@[simp] theorem mk_deck (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) :
    mk f (deck f n p) = mk f p :=
  (Quotient.sound (s := orbitSetoid f) ⟨n, rfl⟩).symm

/-- Moving a representative one period to the left applies the monodromy. -/
@[simp] theorem mk_sub_one (f : X ≃ₜ X) (t : ℝ) (x : X) :
    mk f (t - 1, f x) = mk f (t, x) := by
  simpa [deck, sub_eq_add_neg] using mk_deck f (-1) (t, x)

/-- The usual mapping-torus gluing convention. -/
theorem mk_add_one (f : X ≃ₜ X) (t : ℝ) (x : X) :
    mk f (t + 1, x) = mk f (t, f x) := by
  simpa using (mk_sub_one f (t + 1) x).symm

theorem mk_preimage_image (f : X ≃ₜ X) (s : Set (ℝ × X)) :
    mk f ⁻¹' (mk f '' s) = ⋃ n : ℤ, deck f n '' s := by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨n, hn⟩ := Quotient.exact he
    exact mem_iUnion.mpr ⟨n, q, hq, hn⟩
  · intro hp
    obtain ⟨n, q, hq, rfl⟩ := mem_iUnion.mp hp
    exact ⟨q, hq, (mk_deck f n q).symm⟩

/-- The quotient projection is open, because the saturation of an open set
is the union of its homeomorphic integer translates. -/
theorem mk_open (f : X ≃ₜ X) : IsOpenMap (mk f) := by
  intro s hs
  apply (isQuotientMap_quotient_mk' (s := orbitSetoid f)).isOpen_preimage.mp
  change IsOpen (mk f ⁻¹' (mk f '' s))
  rw [mk_preimage_image]
  exact isOpen_iUnion fun n ↦ (deckHomeomorph f n).isOpenMap s hs

@[simp] theorem circle_intCast (n : ℤ) : ((n : ℝ) : Circle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp⟩

/-- Equality in the base circle is exactly an integral change of time. -/
theorem circle_coe_eq_iff (t s : ℝ) :
    (t : Circle) = (s : Circle) ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  constructor
  · intro h
    have hs : ((s - t : ℝ) : Circle) = 0 := by
      rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hs
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · rintro ⟨n, rfl⟩
    simp

/-- The time coordinate descends to the actual additive circle. -/
def base (f : X ≃ₜ X) : C(Torus f, Circle) where
  toFun := Quotient.lift (fun p : ℝ × X ↦ (p.1 : Circle)) (by
    rintro p q ⟨n, rfl⟩
    simp [deck])
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst |>.quotient_lift _

@[simp] theorem base_mk (f : X ≃ₜ X) (p : ℝ × X) :
    base f (mk f p) = (p.1 : Circle) := rfl

end Wikipedia.HopfProblem.MappingTorus
