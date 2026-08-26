import ErdosProblems.Erdos117.Basic
import ErdosProblems.Erdos117.Symplectic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# An explicit family for the extraspecial lower bound

We use triples `(x,y,z)` with product
`(x,y,z)(x',y',z') = (x+x',y+y',z+z'+x·y')`.
-/

namespace Erdos117

open Matrix Module

@[ext]
structure Heisenberg (m : ℕ) where
  x : Fin m → ZMod 2
  y : Fin m → ZMod 2
  z : ZMod 2
  deriving DecidableEq, Fintype

namespace Heisenberg

variable {m : ℕ}

instance : Group (Heisenberg m) where
  mul a b := ⟨a.x + b.x, a.y + b.y, a.z + b.z + dotProduct a.x b.y⟩
  one := ⟨0, 0, 0⟩
  inv a := ⟨-a.x, -a.y, -a.z + dotProduct a.x a.y⟩
  mul_assoc a b c := by
    apply Heisenberg.ext
    · exact add_assoc a.x b.x c.x
    · exact add_assoc a.y b.y c.y
    · change a.z + b.z + dotProduct a.x b.y + c.z +
        dotProduct (a.x + b.x) c.y =
        a.z + (b.z + c.z + dotProduct b.x c.y) + dotProduct a.x (b.y + c.y)
      rw [add_dotProduct, dotProduct_add]
      ring
  one_mul a := by
    apply Heisenberg.ext
    · exact zero_add a.x
    · exact zero_add a.y
    · change 0 + a.z + dotProduct 0 a.y = a.z
      simp
  mul_one a := by
    apply Heisenberg.ext
    · exact add_zero a.x
    · exact add_zero a.y
    · change a.z + 0 + dotProduct a.x 0 = a.z
      simp
  inv_mul_cancel a := by
    apply Heisenberg.ext
    · exact neg_add_cancel a.x
    · exact neg_add_cancel a.y
    · change -a.z + dotProduct a.x a.y + a.z + dotProduct (-a.x) a.y = 0
      rw [neg_dotProduct]
      ring

@[simp] theorem mul_x (a b : Heisenberg m) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : Heisenberg m) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_z (a b : Heisenberg m) :
    (a * b).z = a.z + b.z + dotProduct a.x b.y := rfl

/-- The underlying symplectic vector space. -/
abbrev Space (m : ℕ) := (Fin m → ZMod 2) × (Fin m → ZMod 2)

/-- Projection that forgets the central coordinate. -/
def project (a : Heisenberg m) : Space m := (a.x, a.y)

/-- The standard alternating commutator form. -/
def form (m : ℕ) : LinearMap.BilinForm (ZMod 2) (Space m) where
  toFun a :=
    { toFun := fun b => dotProduct a.1 b.2 - dotProduct b.1 a.2
      map_add' := fun b c => by
        simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
        ring
      map_smul' := fun r b => by
        simp [dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub] }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change dotProduct (a + b).1 c.2 - dotProduct c.1 (a + b).2 =
      (dotProduct a.1 c.2 - dotProduct c.1 a.2) +
      (dotProduct b.1 c.2 - dotProduct c.1 b.2)
    simp only [Prod.fst_add, Prod.snd_add,
      dotProduct_add, add_dotProduct]
    ring
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    change dotProduct (r • a).1 b.2 - dotProduct b.1 (r • a).2 = _
    simp [dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]

@[simp] theorem form_apply (a b : Space m) :
    form m a b = dotProduct a.1 b.2 - dotProduct b.1 a.2 := rfl

theorem form_isAlt (m : ℕ) : (form m).IsAlt := by
  intro a
  simp

theorem form_nondegenerate (m : ℕ) : (form m).Nondegenerate := by
  apply (form_isAlt m).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro a ha
  apply Prod.ext
  · exact dotProduct_eq_zero a.1 (fun b => by simpa using ha (0, b))
  · exact dotProduct_eq_zero a.2 (fun b => by
      have hb := ha (b, 0)
      simpa [dotProduct_comm] using hb)

theorem commute_iff (a b : Heisenberg m) :
    Commute a b ↔ form m (project a) (project b) = 0 := by
  change a * b = b * a ↔ _
  simp only [form_apply, project, sub_eq_zero]
  constructor
  · intro h
    have hz := congrArg Heisenberg.z h
    simpa [add_comm b.z a.z] using hz
  · intro h
    ext <;> simp [h, add_comm]

theorem form_eq_one_of_not_commute {a b : Heisenberg m} (h : ¬ Commute a b) :
    form m (project a) (project b) = 1 := by
  have hn := mt (commute_iff a b).mpr h
  have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  exact (h01 _).resolve_left hn

theorem project_injOn_noncommuting (s : Finset (Heisenberg m))
    (hs : (s : Set (Heisenberg m)).Pairwise (fun a b => ¬ Commute a b)) :
    Set.InjOn project (s : Set (Heisenberg m)) := by
  intro a ha b hb hp
  by_contra hn
  apply hs ha hb hn
  rw [commute_iff, hp]
  exact form_isAlt m _

theorem noncommutingBound (m : ℕ) : NoncommutingBound (Heisenberg m) (2 * m + 1) := by
  classical
  intro s hs
  have hi := project_injOn_noncommuting s hs
  have hp : ((s.image project : Finset (Space m)) : Set (Space m)).Pairwise
      (fun a b => form m a b = 1) := by
    intro a ha b hb hab
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
    apply form_eq_one_of_not_commute
    exact hs ha' hb' (fun h => hab (congrArg project h))
  have hdim := card_le_finrank_add_one_of_pairing (form m) (form_isAlt m)
    (s.image project) hp
  rw [Finset.card_image_of_injOn hi] at hdim
  simpa [Space, Module.finrank_prod, Module.finrank_pi, two_mul] using hdim

/-- The image of a subgroup in the elementary abelian quotient is a subspace. -/
def projectedSubspace (A : Subgroup (Heisenberg m)) : Submodule (ZMod 2) (Space m) where
  carrier := {v | ∃ a ∈ A, project a = v}
  zero_mem' := ⟨1, A.one_mem, rfl⟩
  add_mem' := by
    rintro v w ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, rfl⟩
  smul_mem' := by
    intro r v hv
    have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
    rcases h01 r with rfl | rfl
    · exact ⟨1, A.one_mem, by rw [zero_smul]; rfl⟩
    · simpa using hv

theorem projectedSubspace_isotropic (A : Subgroup (Heisenberg m))
    [IsMulCommutative A] :
    ∀ v ∈ projectedSubspace A, ∀ w ∈ projectedSubspace A, form m v w = 0 := by
  rintro v ⟨a, ha, rfl⟩ w ⟨b, hb, rfl⟩
  apply (commute_iff a b).mp
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem projectedSubspace_finrank_le (A : Subgroup (Heisenberg m))
    [IsMulCommutative A] : finrank (ZMod 2) (projectedSubspace A) ≤ m := by
  have hdim := twice_finrank_le_of_isotropic (form m) (form_nondegenerate m)
    (projectedSubspace A) (projectedSubspace_isotropic A)
  change 2 * finrank (ZMod 2) (projectedSubspace A) ≤ finrank (ZMod 2) (Space m) at hdim
  have hspace : finrank (ZMod 2) (Space m) = 2 * m := by
    simp [Space, Module.finrank_prod, two_mul]
  rw [hspace] at hdim
  omega

/-- An abelian subgroup contains at most `2^(m+1)` elements. -/
theorem card_abelian_subgroup_le (A : Subgroup (Heisenberg m))
    [IsMulCommutative A] [Fintype A] : Fintype.card A ≤ 2 ^ (m + 1) := by
  classical
  let W := projectedSubspace A
  let : Fintype W := Fintype.ofFinite W
  let f : A → W × ZMod 2 := fun a => (⟨project a, a, a.2, rfl⟩, a.1.z)
  have hf : Function.Injective f := by
    intro a b hab
    have hxy := congrArg (fun t : W × ZMod 2 => t.1.val) hab
    have hz := congrArg Prod.snd hab
    apply Subtype.ext
    exact Heisenberg.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy) hz
  calc
    Fintype.card A ≤ Fintype.card (W × ZMod 2) := Fintype.card_le_of_injective f hf
    _ = 2 ^ finrank (ZMod 2) W * 2 := by
      rw [Fintype.card_prod, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ ≤ 2 ^ m * 2 := Nat.mul_le_mul_right 2
      (Nat.pow_le_pow_right (by decide) (projectedSubspace_finrank_le A))
    _ = 2 ^ (m + 1) := (pow_succ 2 m).symm

/-- The explicit group has order `2^(2m+1)`. -/
theorem card (m : ℕ) : Fintype.card (Heisenberg m) = 2 ^ (2 * m + 1) := by
  let e : Heisenberg m ≃ Space m × ZMod 2 :=
    { toFun := fun a => (project a, a.z)
      invFun := fun a => ⟨a.1.1, a.1.2, a.2⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  rw [Fintype.card_congr e]
  simp [Space, Fintype.card_prod, ZMod.card, pow_add, two_mul]

/-- The extraspecial examples force the sharp exponential lower-bound scale. -/
theorem pow_le_cover_size {k : ℕ} (h : HasAbelianCover (Heisenberg m) k) :
    2 ^ m ≤ k := by
  classical
  obtain ⟨A, hA, hcover⟩ := h
  let (i : Fin k) : Fintype (A i) := Fintype.ofFinite (A i)
  have hc := card_le_sum_card_of_cover A hcover
  have hb : ∑ i, Fintype.card (A i) ≤ k * 2 ^ (m + 1) := by
    calc
      ∑ i, Fintype.card (A i) ≤ ∑ _i : Fin k, 2 ^ (m + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have := hA i
        exact card_abelian_subgroup_le (A i)
      _ = k * 2 ^ (m + 1) := by simp
  rw [card] at hc
  have hp : 2 ^ m * 2 ^ (m + 1) ≤ k * 2 ^ (m + 1) := by
    rw [← pow_add, show m + (m + 1) = 2 * m + 1 by omega]
    exact hc.trans hb
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  nlinarith

end Heisenberg
end Erdos117
