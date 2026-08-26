/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: generic p-adic branch-map isometry

This module isolates equations (22)--(28) of the proposed positive-density
proof.  A branch map has a quadratic coefficient divisible by `p`, a linear
coefficient of the form `p*u+b`, and a residual coefficient `b` which is a
unit modulo `p`.  We prove the exact difference factorization, the resulting
isometry modulo every positive power `p^j`, and hence permutation of
`ZMod (p^j)`.

The last section records the finite combinatorics used after the permutation:
the preimage of an allowed set has the same cardinality, removal of one allowed
image removes exactly one residue, and the corresponding depth-`d` digit box
has cardinality `(H-1) * H^(d-1)`.
-/

namespace Erdos730

/-- Generic form of the four branch polynomials in equation (22). -/
def padicBranchMap {R : Type*} [CommRing R]
    (p q u b v k : R) : R :=
  p * q * k ^ 2 + (p * u + b) * k + v

/-- Exact difference factorization underlying equation (26). -/
theorem padicBranchMap_sub_factor {R : Type*} [CommRing R]
    (p q u b v x y : R) :
    padicBranchMap p q u b v x - padicBranchMap p q u b v y =
      (x - y) * (p * q * (x + y) + p * u + b) := by
  simp only [padicBranchMap]
  ring

/-- A multiple of `p` in `ZMod (p^j)` is nilpotent when `j>=1`. -/
theorem zmod_primeMultiple_isNilpotent {p j : ℕ} (z : ZMod (p ^ j)) :
    IsNilpotent ((p : ZMod (p ^ j)) * z) := by
  refine ⟨j, ?_⟩
  rw [mul_pow, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

/-- The second factor in the branch-map difference is a unit.  This is the
kernel form of the sentence following equation (25). -/
theorem padicBranchMap_differenceFactor_isUnit
    {p j : ℕ} {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u x y : ZMod (p ^ j)) :
    IsUnit ((p : ZMod (p ^ j)) * q * (x + y) + p * u + b) := by
  have hnil : IsNilpotent
      ((p : ZMod (p ^ j)) * (q * (x + y) + u)) :=
    zmod_primeMultiple_isNilpotent _
  rw [show (p : ZMod (p ^ j)) * q * (x + y) + p * u + b =
      p * (q * (x + y) + u) + b by ring]
  exact hnil.isUnit_add_right_of_commute hb (Commute.all _ _)

/-- Equality after applying the branch map is equivalent to equality before
applying it.  Equality in `ZMod (p^j)` is congruence modulo `p^j`. -/
theorem padicBranchMap_eq_iff
    {p j : ℕ} {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u v x y : ZMod (p ^ j)) :
    padicBranchMap (p : ZMod (p ^ j)) q u b v x =
        padicBranchMap (p : ZMod (p ^ j)) q u b v y ↔ x = y := by
  constructor
  · intro hxy
    have hunit := padicBranchMap_differenceFactor_isUnit hb q u x y
    have hzero :
        (x - y) * ((p : ZMod (p ^ j)) * q * (x + y) + p * u + b) = 0 := by
      rw [← padicBranchMap_sub_factor]
      rw [hxy, sub_self]
    have hsub : x - y = 0 := hunit.mul_left_injective (by simpa using hzero)
    exact sub_eq_zero.mp hsub
  · exact fun hxy ↦ congrArg (padicBranchMap (p : ZMod (p ^ j)) q u b v) hxy

/-- The branch polynomial permutes every `ZMod (p^j)`. -/
theorem padicBranchMap_bijective
    {p j : ℕ} (hp0 : 0 < p) {b : ZMod (p ^ j)} (hb : IsUnit b)
    (q u v : ZMod (p ^ j)) :
    Function.Bijective (padicBranchMap (p : ZMod (p ^ j)) q u b v) := by
  have hinj : Function.Injective
      (padicBranchMap (p : ZMod (p ^ j)) q u b v) := by
    intro x y hxy
    exact (padicBranchMap_eq_iff hb q u v x y).mp hxy
  letI : NeZero (p ^ j) := ⟨pow_ne_zero j (Nat.ne_of_gt hp0)⟩
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

/-- A natural number not divisible by the prime `p` remains a unit modulo
every power `p^j`. -/
theorem natCast_isUnit_zmod_primePow
    {p j b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b) :
    IsUnit (b : ZMod (p ^ j)) := by
  exact (ZMod.isUnit_iff_coprime b (p ^ j)).2
    (hp.coprime_pow_of_not_dvd hpb)

/-- Equation (26) stated as an integer congruence equivalence.  The
coefficients `q,u,v` may depend on the branch and on the chosen root. -/
theorem padicBranchMap_int_congr_iff
    {p j b : ℕ} (hp : p.Prime) (hpb : ¬p ∣ b)
    (q u v : ZMod (p ^ j)) (x y : ℤ) :
    padicBranchMap (p : ZMod (p ^ j)) q u b v x =
        padicBranchMap (p : ZMod (p ^ j)) q u b v y ↔
      x ≡ y [ZMOD p ^ j] := by
  rw [padicBranchMap_eq_iff (natCast_isUnit_zmod_primePow hp hpb) q u v]
  exact ZMod.intCast_eq_intCast_iff x y (p ^ j)

/-! ## Exact one-class removal and digit-box cardinality -/

/-- Under a permutation of a finite type, the preimage of a finite allowed
set has exactly the cardinality of that set. -/
theorem card_filter_preimage_of_bijective
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : α → α) (hG : Function.Bijective G) (A : Finset α) :
    (Finset.univ.filter fun x ↦ G x ∈ A).card = A.card := by
  exact Finset.card_bijective G hG (by intro x; simp)

/-- If one allowed image `G x0` is removed, exactly one domain residue is
removed.  This is the finite permutation content of the sentence before
equation (28). -/
theorem card_filter_preimage_erase_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : α → α) (hG : Function.Bijective G) (A : Finset α)
    (x0 : α) (hx0 : G x0 ∈ A) :
    (Finset.univ.filter fun x ↦ G x ∈ A.erase (G x0)).card = A.card - 1 := by
  rw [card_filter_preimage_of_bijective G hG]
  exact Finset.card_erase_of_mem hx0

/-- Abstract digit box: the first digit lies in `A` with one endpoint
removed, while each of the remaining `d-1` digits lies in `A`. -/
def RestrictedDigitBox {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d : ℕ) :=
  ↥(A.erase endpoint) × (Fin (d - 1) → ↥A)

instance restrictedDigitBoxFintype {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d : ℕ) :
    Fintype (RestrictedDigitBox A endpoint d) := by
  unfold RestrictedDigitBox
  infer_instance

/-- Equation (28) as an exact finite cardinality identity. -/
theorem restrictedDigitBox_card
    {α : Type*} [DecidableEq α]
    (A : Finset α) (endpoint : α) (d H : ℕ)
    (hendpoint : endpoint ∈ A) (hcard : A.card = H) :
    Fintype.card (RestrictedDigitBox A endpoint d) =
      (H - 1) * H ^ (d - 1) := by
  change Fintype.card (↥(A.erase endpoint) × (Fin (d - 1) → ↥A)) = _
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem hendpoint, hcard]

end Erdos730
