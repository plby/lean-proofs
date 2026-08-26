import ErdosProblems.Erdos117.BilinearLength
import ErdosProblems.Erdos117.PGroupLength
import ErdosProblems.Erdos117.Compression
import Mathlib.GroupTheory.Abelianization.Finite

/-!
# The commutator map of a group of class at most two

Commutators give a bilinear map on the abelianization, with values in the
derived subgroup. This is the class-two application of the composition-length
argument.
-/

namespace Erdos117

open scoped commutatorElement

variable {G A : Type*} [Group G] [CommGroup A]

/-- A homomorphism in each variable descends to a bilinear map on the two
abelianizations. -/
def bihomBilinear (η : G →* (G →* A)) :
    Additive (Abelianization G) →ₗ[ℤ] Additive (Abelianization G) →ₗ[ℤ] Additive A :=
  ({ toFun := fun u =>
       (Abelianization.lift (Abelianization.lift η u.toMul)).toAdditive.toIntLinearMap
     map_zero' := by
       ext q
       induction q using QuotientGroup.induction_on with
       | H g =>
         change Additive.ofMul ((Abelianization.lift η) 1 g) = 0
         rw [map_one]
         rfl
     map_add' := by
       intro u v
       ext q
       induction q using QuotientGroup.induction_on with
       | H g =>
         change Additive.ofMul ((Abelianization.lift η) (u.toMul * v.toMul) g) =
           Additive.ofMul ((Abelianization.lift η) u.toMul g) +
             Additive.ofMul ((Abelianization.lift η) v.toMul g)
         rw [map_mul]
         rfl } : Additive (Abelianization G) →+
          (Additive (Abelianization G) →ₗ[ℤ] Additive A)).toIntLinearMap

theorem bihomBilinear_of (η : G →* (G →* A)) (x y : G) :
    bihomBilinear η (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = Additive.ofMul (η x y) := rfl

/-- Central commutators are multiplicative in both variables. -/
def classTwoCommutatorHom (hG : commutator G ≤ Subgroup.center G)
    (ρ : commutator G →* A) : G →* (G →* A) where
  toFun x :=
    { toFun := fun y => ρ (centralCommutator (commutator G) le_rfl x y)
      map_one' := by
        have h : centralCommutator (commutator G) le_rfl x 1 = 1 :=
          Subtype.ext (commutatorElement_one_right x)
        rw [h, map_one]
      map_mul' y z := by
        rw [centralCommutator_mul_right _ _ hG, map_mul] }
  map_one' := by
    ext y
    have h : centralCommutator (commutator G) le_rfl 1 y = 1 :=
      Subtype.ext (commutatorElement_one_left y)
    change ρ (centralCommutator (commutator G) le_rfl 1 y) = 1
    rw [h, map_one]
  map_mul' x y := by
    ext z
    change ρ (centralCommutator (commutator G) le_rfl (x * y) z) =
      ρ (centralCommutator (commutator G) le_rfl x z) *
        ρ (centralCommutator (commutator G) le_rfl y z)
    rw [centralCommutator_mul_left _ _ hG, map_mul]

/-- The quadratic derived-order bound for finite groups of class at most two
whose order is a power of `p`. The only numerical hypothesis is the stated
bound on conjugacy-class sizes. -/
theorem class_two_derived_card_le {p b : ℕ} [Fact p.Prime] [Finite G]
    (hP : IsPGroup p G) (hG : commutator G ≤ Subgroup.center G)
    (hb : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ p ^ b) :
    Nat.card (commutator G) ≤ p ^ (b * b) := by
  classical
  let D := commutator G
  let : CommGroup D := { (inferInstance : Group D) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hG y.property) x) }
  let q : G →* Abelianization G := Abelianization.of
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective (commutator G)
  have : Finite (Abelianization G) := Finite.of_surjective q hq
  let η := classTwoCommutatorHom hG (MonoidHom.id D)
  let β := bihomBilinear η
  have hβ (x y : G) : β (Additive.ofMul (q x)) (Additive.ofMul (q y)) =
      Additive.ofMul (centralCommutator D le_rfl x y) := rfl
  have hrows : ∀ u, moduleLength ℤ (LinearMap.range (β u)) ≤ b := by
    intro u
    obtain ⟨x, hx⟩ := hq u.toMul
    have hu : u = Additive.ofMul (q x) := congrArg Additive.ofMul hx.symm
    subst u
    have hsub : ∀ z ∈ LinearMap.range (β (Additive.ofMul (q x))), z.toMul ∈ (η x).range := by
      rintro z ⟨v, rfl⟩
      obtain ⟨y, hy⟩ := hq v.toMul
      have hv : v = Additive.ofMul (q y) := congrArg Additive.ofMul hy.symm
      subst v
      exact ⟨y, rfl⟩
    let f : LinearMap.range (β (Additive.ofMul (q x))) → (η x).range :=
      fun z => ⟨z.val.toMul, hsub z z.property⟩
    have hf : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have heq : z.val.toMul = w.val.toMul :=
        congrArg (fun t : (η x).range => (t : D)) h
      exact congrArg Additive.ofMul heq
    have hker : (η x).ker = Subgroup.centralizer ({x} : Set G) := by
      ext y
      change centralCommutator D le_rfl x y = 1 ↔ _
      rw [Subtype.ext_iff, Subgroup.mem_centralizer_singleton_iff]
      change ⁅x, y⁆ = 1 ↔ y * x = x * y
      rw [commutatorElement_eq_one_iff_mul_comm, eq_comm]
    have hcard : Nat.card (LinearMap.range (β (Additive.ofMul (q x)))) ≤ p ^ b := by
      calc
        _ ≤ Nat.card (η x).range := Nat.card_le_card_of_injective f hf
        _ = (η x).ker.index := (Subgroup.index_ker (η x)).symm
        _ ≤ p ^ b := by rw [hker]; exact hb x
    let ι : Multiplicative (LinearMap.range (β (Additive.ofMul (q x)))) →* G :=
      { toFun := fun z => z.toAdd.val.toMul.val
        map_one' := rfl
        map_mul' _ _ := rfl }
    have hι : Function.Injective ι := by
      intro z w h
      change z.toAdd = w.toAdd
      apply Subtype.ext
      change z.toAdd.val.toMul = w.toAdd.val.toMul
      exact Subtype.ext h
    exact moduleLength_int_le_of_card_le (hP.of_injective ι hι) hcard
  have hskew : ∀ u v, β u v = -(β v u) := by
    intro u v
    obtain ⟨x, hx⟩ := hq u.toMul
    obtain ⟨y, hy⟩ := hq v.toMul
    have hu : u = Additive.ofMul (q x) := congrArg Additive.ofMul hx.symm
    have hv : v = Additive.ofMul (q y) := congrArg Additive.ofMul hy.symm
    subst u v
    rw [hβ, hβ]
    change centralCommutator D le_rfl x y = (centralCommutator D le_rfl y x)⁻¹
    apply Subtype.ext
    exact (commutatorElement_inv y x).symm
  have hcols : ∀ v ∈ (Set.univ : Set (Additive (Abelianization G))),
      moduleLength ℤ (LinearMap.range (β.flip v)) ≤ b := by
    intro v _
    have heq : β.flip v = -(β v) := by
      apply LinearMap.ext
      intro u
      exact hskew u v
    rw [heq, LinearMap.range_neg]
    exact hrows v
  let I := bilinearImage β
  have hD : D ≤ I.toAddSubgroup.toSubgroup'.map D.subtype := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    refine ⟨centralCommutator D le_rfl x y, ?_, rfl⟩
    exact mem_bilinearImage β (Additive.ofMul (q x)) (Additive.ofMul (q y))
  have hI : I = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨w, hw, heq⟩ := hD z.toMul.property
    have hwz : w = z.toMul := Subtype.ext heq
    subst w
    exact hw
  have hlen := bilinearImage_length_le β le_rfl hrows Set.univ (by simp) hcols
  change moduleLength ℤ I ≤ b * b at hlen
  rw [hI, moduleLength_top] at hlen
  have hDP : IsPGroup p D := hP.of_injective D.subtype D.subtype_injective
  rw [card_eq_pow_moduleLength hDP]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hlen

/-- The same bound with an arbitrary conjugacy bound, expressed uniformly
in base two. Taking the floor logarithm at `p` avoids a loss for large primes. -/
theorem class_two_prime_derived_card_le_two_pow {p r : ℕ} [Fact p.Prime] [Finite G]
    (hP : IsPGroup p G) (hG : commutator G ≤ Subgroup.center G) (hr : 1 ≤ r)
    (hb : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ r) :
    Nat.card (commutator G) ≤ 2 ^ ((Nat.clog 2 r) ^ 2) := by
  let b := Nat.log p r
  let ell := Nat.clog 2 r
  have hp : p.Prime := Fact.out
  have hpow : ∀ x : G, (Subgroup.centralizer ({x} : Set G)).index ≤ p ^ b := by
    intro x
    obtain ⟨j, hj⟩ := hP.index (Subgroup.centralizer ({x} : Set G))
    rw [hj]
    apply Nat.pow_le_pow_right hp.pos
    apply Nat.le_log_of_pow_le hp.one_lt
    rw [← hj]
    exact hb x
  have hcard := class_two_derived_card_le hP hG hpow
  have hpb : p ^ b ≤ 2 ^ ell :=
    (Nat.pow_log_le_self p (by omega : r ≠ 0)).trans (Nat.le_pow_clog (by decide) r)
  have hbell : b ≤ ell :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      ((Nat.pow_le_pow_left hp.two_le b).trans hpb)
  calc
    Nat.card (commutator G) ≤ p ^ (b * b) := hcard
    _ = (p ^ b) ^ b := by rw [pow_mul]
    _ ≤ (2 ^ ell) ^ b := Nat.pow_le_pow_left hpb b
    _ ≤ (2 ^ ell) ^ ell := Nat.pow_le_pow_right (by positivity) hbell
    _ = 2 ^ (ell ^ 2) := by rw [pow_two, pow_mul]

/-- A finite class-two `p`-group with clique bound `n` has derived-subgroup
order at most `2 ^ ((clog 2 ((2*n)^2))^2)`. -/
theorem class_two_prime_derived_card_le_clique {p n : ℕ} [Fact p.Prime] [Finite G]
    (hP : IsPGroup p G) (hG : commutator G ≤ Subgroup.center G)
    (hn : NoncommutingBound G n) :
    Nat.card (commutator G) ≤ 2 ^ ((Nat.clog 2 ((2 * n) ^ 2)) ^ 2) := by
  have hn1 := one_le_of_noncommutingBound hn
  apply class_two_prime_derived_card_le_two_pow hP hG (by nlinarith)
  exact fun x => centralizerIndex_le hn x

end Erdos117
