/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorFactorization

/-!
# The `P`/`Q` coset reduction

This file isolates the part of the Jackson--Mauldin selector argument which
does not depend on the construction of the good permutations.  The
denominator is written `P * Q`, where `P` is the product of the nontrivial
prime powers and `Q` is the complementary product.  A selector constructed at
denominator `p * P` is used separately on each of the `Q^2` cosets.

The only arithmetic input needed to rule out conflicts between distinct
cosets is `SquareNormRigid Q`.  It is deliberately stated over `ℤ`: this is
the right condition also at the prime `2`, where anisotropy over `ZMod 2` is
false.  `SelectorFactorization` is responsible for proving this condition for
the canonical trivial part.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The remainder, as an element of the finite coset-indexing type. -/
def remainderFin (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (i : Fin (Q * D)) : Fin Q :=
  ⟨remainderIndex Q i, remainderIndex_lt Q hQ i⟩

@[simp] lemma remainderFin_val (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (i : Fin (Q * D)) :
    (remainderFin Q hQ i : ℕ) = remainderIndex Q i := rfl

/-- Reassemble a `Q`-coset and a coordinate in its denominator-`D` copy. -/
def joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (a : Fin Q) (x : Fin D) :
    Fin (Q * D) :=
  ⟨Q * (x : ℕ) + (a : ℕ), by
    calc
      Q * (x : ℕ) + (a : ℕ) < Q * (x : ℕ) + Q :=
        Nat.add_lt_add_left a.isLt _
      _ = Q * ((x : ℕ) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ Q * D := Nat.mul_le_mul_left Q (Nat.succ_le_iff.mpr x.isLt)⟩

@[simp] lemma joinIndex_val (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    (joinIndex Q hQ a x : ℕ) = Q * (x : ℕ) + (a : ℕ) := rfl

@[simp] lemma remainderIndex_joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    remainderIndex Q (joinIndex Q hQ a x) = a := by
  simp only [remainderIndex, joinIndex_val, Nat.add_mod, Nat.mul_mod_right,
    zero_add, Nat.mod_eq_of_lt a.isLt]

@[simp] lemma quotientIndex_joinIndex (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (a : Fin Q) (x : Fin D) :
    quotientIndex Q (joinIndex Q hQ a x) = x := by
  apply Fin.ext
  simp only [quotientIndex, hQ, ↓reduceDIte, joinIndex_val]
  simp [Nat.add_div, Nat.mod_eq_of_lt a.isLt,
    Nat.div_eq_of_lt a.isLt, Nat.not_le_of_gt a.isLt, hQ]

/-- Restrict a full selector to one `Q²`-coset and translate that coset back
to the pure denominator `D`. -/
def restrictCoset (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (s : LiftData (Q * D))
    (a b : Fin Q) : LiftData D where
  k := fun x y ↦ s.k (joinIndex Q hQ a x) (joinIndex Q hQ b y)
  l := fun x y ↦ s.l (joinIndex Q hQ a x) (joinIndex Q hQ b y)

lemma sqDist_restrictCoset (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (s : LiftData (Q * D)) (a b : Fin Q) (x₁ y₁ x₂ y₂ : Fin D) :
    sqDist ((restrictCoset Q hQ s a b).point x₁ y₁)
        ((restrictCoset Q hQ s a b).point x₂ y₂) =
      sqDist (s.point (joinIndex Q hQ a x₁) (joinIndex Q hQ b y₁))
        (s.point (joinIndex Q hQ a x₂) (joinIndex Q hQ b y₂)) := by
  simp only [LiftData.point, restrictCoset, liftedPoint, sqDist, joinIndex_val]
  push_cast
  field_simp [Nat.ne_of_gt hQ, hD]
  ring

theorem restrictCoset_separated (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (s : LiftData (Q * D)) (hs : s.Separated) (a b : Fin Q) :
    (restrictCoset Q hQ s a b).Separated := by
  rw [LiftData.separated_iff_sqDist_not_int hD]
  intro x₁ y₁ x₂ y₂ hne hInt
  have hjoin :
      (joinIndex Q hQ a x₁, joinIndex Q hQ b y₁) ≠
        (joinIndex Q hQ a x₂, joinIndex Q hQ b y₂) := by
    intro h
    apply hne
    apply Prod.ext <;> apply Fin.ext
    · have hv := congrArg (fun z : Fin (Q * D) ↦ (z : ℕ)) (congrArg Prod.fst h)
      simp only [joinIndex_val] at hv
      exact Nat.mul_left_cancel hQ (Nat.add_right_cancel hv)
    · have hv := congrArg (fun z : Fin (Q * D) ↦ (z : ℕ)) (congrArg Prod.snd h)
      simp only [joinIndex_val] at hv
      exact Nat.mul_left_cancel hQ (Nat.add_right_cancel hv)
  have hfull := (LiftData.separated_iff_sqDist_not_int
      (Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD) s).mp hs
    (joinIndex Q hQ a x₁) (joinIndex Q hQ b y₁)
    (joinIndex Q hQ a x₂) (joinIndex Q hQ b y₂) hjoin
  apply hfull
  rw [← sqDist_restrictCoset Q hQ hD s a b x₁ y₁ x₂ y₂]
  exact hInt

/-- Assemble independently chosen denominator-`D` selectors on all `Q²`
cosets. -/
def assembleCosets (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (pieces : Fin Q → Fin Q → LiftData D) : LiftData (Q * D) where
  k := fun i j ↦
    (pieces (remainderFin Q hQ i) (remainderFin Q hQ j)).k
      (quotientIndex Q i) (quotientIndex Q j)
  l := fun i j ↦
    (pieces (remainderFin Q hQ i) (remainderFin Q hQ j)).l
      (quotientIndex Q i) (quotientIndex Q j)

/-- Translate the residue coordinates of a selector cyclically by `c,d`.
The quotient terms are the integral corrections at the wraparound. -/
def shiftLift {n : ℕ} (c d : Fin n) (s : LiftData n) : LiftData n where
  k := fun i j ↦
    s.k (i - c) (j - d) + (((i - c : Fin n) : ℕ) + (c : ℕ)) / n
  l := fun i j ↦
    s.l (i - c) (j - d) + (((j - d : Fin n) : ℕ) + (d : ℕ)) / n

lemma shiftLift_point {n : ℕ} (hn : n ≠ 0) (c d : Fin n) (s : LiftData n)
    (i j : Fin n) :
    (shiftLift c d s).point i j =
      ((s.point (i - c) (j - d)).1 + (c : ℕ) / (n : ℚ),
        (s.point (i - c) (j - d)).2 + (d : ℕ) / (n : ℚ)) := by
  let : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hxi : (((i - c : Fin n) : ℕ) + (c : ℕ)) % n = (i : ℕ) := by
    have h := congrArg (fun z : Fin n ↦ (z : ℕ)) (sub_add_cancel i c)
    simpa only [Fin.val_add, Nat.mod_eq_of_lt i.isLt] using h
  have hxdiv := Nat.mod_add_div (((i - c : Fin n) : ℕ) + (c : ℕ)) n
  have hxeq : (i : ℕ) + n * ((((i - c : Fin n) : ℕ) + (c : ℕ)) / n) =
      ((i - c : Fin n) : ℕ) + (c : ℕ) := by
    rw [← hxi]
    omega
  have hyi : (((j - d : Fin n) : ℕ) + (d : ℕ)) % n = (j : ℕ) := by
    have h := congrArg (fun z : Fin n ↦ (z : ℕ)) (sub_add_cancel j d)
    simpa only [Fin.val_add, Nat.mod_eq_of_lt j.isLt] using h
  have hydiv := Nat.mod_add_div (((j - d : Fin n) : ℕ) + (d : ℕ)) n
  have hyeq : (j : ℕ) + n * ((((j - d : Fin n) : ℕ) + (d : ℕ)) / n) =
      ((j - d : Fin n) : ℕ) + (d : ℕ) := by
    rw [← hyi]
    omega
  apply Prod.ext
  · simp only [LiftData.point, shiftLift, liftedPoint]
    push_cast
    field_simp [hn]
    norm_cast
    have hxeqZ : (i : ℤ) + (n : ℤ) *
        (((((i - c : Fin n) : ℕ) + (c : ℕ)) / n : ℕ) : ℤ) =
          ((i - c : Fin n) : ℕ) + (c : ℕ) := by
      exact_mod_cast hxeq
    rw [mul_add]
    linear_combination hxeqZ
  · simp only [LiftData.point, shiftLift, liftedPoint]
    push_cast
    field_simp [hn]
    norm_cast
    have hyeqZ : (j : ℤ) + (n : ℤ) *
        (((((j - d : Fin n) : ℕ) + (d : ℕ)) / n : ℕ) : ℤ) =
          ((j - d : Fin n) : ℕ) + (d : ℕ) := by
      exact_mod_cast hyeq
    rw [mul_add]
    linear_combination hyeqZ

lemma sqDist_shiftLift {n : ℕ} (hn : n ≠ 0) (c d : Fin n) (s : LiftData n)
    (i₁ j₁ i₂ j₂ : Fin n) :
    sqDist ((shiftLift c d s).point i₁ j₁) ((shiftLift c d s).point i₂ j₂) =
      sqDist (s.point (i₁ - c) (j₁ - d)) (s.point (i₂ - c) (j₂ - d)) := by
  rw [shiftLift_point hn, shiftLift_point hn]
  simp only [sqDist]
  ring

theorem shiftLift_separated {n : ℕ} (hn : n ≠ 0) (c d : Fin n)
    (s : LiftData n) (hs : s.Separated) : (shiftLift c d s).Separated := by
  let : NeZero n := ⟨hn⟩
  rw [LiftData.separated_iff_sqDist_not_int hn]
  intro i₁ j₁ i₂ j₂ hne
  have hne' : (i₁ - c, j₁ - d) ≠ (i₂ - c, j₂ - d) := by
    intro h
    apply hne
    apply Prod.ext
    · exact sub_left_injective (congrArg Prod.fst h)
    · exact sub_left_injective (congrArg Prod.snd h)
  have hsep := (LiftData.separated_iff_sqDist_not_int hn s).mp hs
    (i₁ - c) (j₁ - d) (i₂ - c) (j₂ - d) hne'
  rw [sqDist_shiftLift hn]
  exact hsep

/-- Multiplication by `p` on the finite set of `Q` cosets. -/
def mulCosetMap (p Q : ℕ) (hQ : 0 < Q) (a : Fin Q) : Fin Q :=
  ⟨(p * (a : ℕ)) % Q, Nat.mod_lt _ hQ⟩

lemma mulCosetMap_injective (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q) :
    Function.Injective (mulCosetMap p Q hQ) := by
  intro a b hab
  have hv := congrArg (fun z : Fin Q ↦ (z : ℕ)) hab
  have hm : p * (a : ℕ) ≡ p * (b : ℕ) [MOD Q] := by
    exact hv
  have habm : (a : ℕ) ≡ (b : ℕ) [MOD Q] :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm hm
  apply Fin.ext
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using habm

/-- The permutation of the `Q` cosets induced by multiplication by `p`. -/
noncomputable def mulCosetEquiv (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q) :
    Equiv.Perm (Fin Q) :=
  Equiv.ofBijective (mulCosetMap p Q hQ)
    ⟨mulCosetMap_injective p Q hQ hcop,
      (Finite.injective_iff_surjective).mp (mulCosetMap_injective p Q hQ hcop)⟩

@[simp] lemma mulCosetEquiv_apply (p Q : ℕ) (hQ : 0 < Q) (hcop : p.Coprime Q)
    (a : Fin Q) :
    mulCosetEquiv p Q hQ hcop a = mulCosetMap p Q hQ a := rfl

/-- The quotient carry in `p*a = Q*carry + (p*a mod Q)`. -/
def cosetCarry (p Q : ℕ) (a : Fin Q) : ℕ := p * (a : ℕ) / Q

lemma cosetCarry_lt (p Q : ℕ) (hp : 0 < p) (hQ : 0 < Q) (a : Fin Q) :
    cosetCarry p Q a < p := by
  rw [cosetCarry, Nat.div_lt_iff_lt_mul hQ]
  exact (Nat.mul_lt_mul_left hp).2 a.isLt

lemma mul_val_eq_coset (p Q : ℕ) (hQ : 0 < Q) (a : Fin Q) :
    p * (a : ℕ) = Q * cosetCarry p Q a + (mulCosetMap p Q hQ a : ℕ) := by
  simp only [cosetCarry, mulCosetMap]
  simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div (p * (a : ℕ)) Q).symm

/-- The quotient carry, regarded as a residue at the enlarged pure
denominator.  The inequality `carry < p ≤ p*P` is the reason for the
positivity hypothesis on `P`. -/
def cosetCarryIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P) (hQ : 0 < Q)
    (a : Fin Q) : Fin (p * P) :=
  ⟨cosetCarry p Q a, by
    have hc := cosetCarry_lt p Q hp hQ a
    have hpP : p ≤ p * P := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr hP)
    exact lt_of_lt_of_le hc hpP⟩

@[simp] lemma cosetCarryIndex_val (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) :
    (cosetCarryIndex p P Q hp hP hQ a : ℕ) = cosetCarry p Q a := rfl

/-- In the target copy belonging to the coset `p*a mod Q`, the old pure
residue `x` occurs at `p*x + carry(p,a)`. -/
def localOldIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P) (hQ : 0 < Q)
    (a : Fin Q) (x : Fin P) : Fin (p * P) :=
  ⟨p * (x : ℕ) + cosetCarry p Q a, by
    have hc := cosetCarry_lt p Q hp hQ a
    calc
      p * (x : ℕ) + cosetCarry p Q a < p * (x : ℕ) + p :=
        Nat.add_lt_add_left hc _
      _ = p * ((x : ℕ) + 1) := by ring
      _ ≤ p * P := Nat.mul_le_mul_left p (Nat.succ_le_iff.mpr x.isLt)⟩

@[simp] lemma localOldIndex_val (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) (x : Fin P) :
    (localOldIndex p P Q hp hP hQ a x : ℕ) =
      p * (x : ℕ) + cosetCarry p Q a := rfl

lemma localOldIndex_sub_carry (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a : Fin Q) (x : Fin P) :
    localOldIndex p P Q hp hP hQ a x -
        cosetCarryIndex p P Q hp hP hQ a = oldIndex p hp x := by
  apply Fin.ext
  simp only [Fin.val_sub, localOldIndex_val, cosetCarryIndex_val, oldIndex]
  have hc : cosetCarry p Q a ≤ p * P :=
    le_of_lt (cosetCarryIndex p P Q hp hP hQ a).isLt
  have hx : p * (x : ℕ) < p * P := (oldIndex p hp x).isLt
  rw [show p * P - cosetCarry p Q a +
      (p * (x : ℕ) + cosetCarry p Q a) = p * P + p * (x : ℕ) by omega]
  simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hx]

lemma shiftLift_at_localOldIndex (p P Q : ℕ) (hp : 0 < p) (hP : 0 < P)
    (hQ : 0 < Q) (a b : Fin Q) (u : LiftData (p * P)) (x y : Fin P) :
    (shiftLift (cosetCarryIndex p P Q hp hP hQ a)
        (cosetCarryIndex p P Q hp hP hQ b) u).k
          (localOldIndex p P Q hp hP hQ a x)
          (localOldIndex p P Q hp hP hQ b y) =
        u.k (oldIndex p hp x) (oldIndex p hp y) ∧
    (shiftLift (cosetCarryIndex p P Q hp hP hQ a)
        (cosetCarryIndex p P Q hp hP hQ b) u).l
          (localOldIndex p P Q hp hP hQ a x)
          (localOldIndex p P Q hp hP hQ b y) =
        u.l (oldIndex p hp x) (oldIndex p hp y) := by
  have hi := localOldIndex_sub_carry p P Q hp hP hQ a x
  have hj := localOldIndex_sub_carry p P Q hp hP hQ b y
  have hxi : p * (x : ℕ) + cosetCarry p Q a < p * P :=
    (localOldIndex p P Q hp hP hQ a x).isLt
  have hyi : p * (y : ℕ) + cosetCarry p Q b < p * P :=
    (localOldIndex p P Q hp hP hQ b y).isLt
  constructor
  · simp only [shiftLift, hi, hj, oldIndex, cosetCarryIndex_val]
    have hzero : ((((p * (x : ℕ) : ℕ) : ℤ) +
        ((cosetCarry p Q a : ℕ) : ℤ)) /
          (((p * P : ℕ) : ℤ))) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast hxi
    rw [hzero, add_zero]
  · simp only [shiftLift, hi, hj, oldIndex, cosetCarryIndex_val]
    have hzero : ((((p * (y : ℕ) : ℕ) : ℤ) +
        ((cosetCarry p Q b : ℕ) : ℤ)) /
          (((p * P : ℕ) : ℤ))) = 0 := by
      apply Int.ediv_eq_zero_of_lt
      · positivity
      · exact_mod_cast hyi
    rw [hzero, add_zero]

/-- Transport lift data across an equality of denominators.  This definition
is kept local to the coset module, so the coset reduction does not depend on
the later infinite-chain construction. -/
def LiftData.transport {d e : ℕ} (h : d = e) (s : LiftData d) : LiftData e :=
  h ▸ s

@[simp] lemma LiftData.transport_rfl {d : ℕ} (s : LiftData d) :
    s.transport rfl = s := rfl

lemma LiftData.separated_transport {d e : ℕ} (h : d = e) (s : LiftData d)
    (hs : s.Separated) : (s.transport h).Separated := by
  subst e
  exact hs

@[simp] lemma LiftData.transport_k {d e : ℕ} (h : d = e) (s : LiftData d)
    (i j : Fin e) :
    (s.transport h).k i j = s.k (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

@[simp] lemma LiftData.transport_l {d e : ℕ} (h : d = e) (s : LiftData d)
    (i j : Fin e) :
    (s.transport h).l i j = s.l (Fin.cast h.symm i) (Fin.cast h.symm j) := by
  subst e
  rfl

/-- The elementary reassociation which changes the coset-friendly target
denominator into the standard prime-extension denominator. -/
lemma pqTargetDenom_eq (p P Q : ℕ) :
    Q * (p * P) = p * (P * Q) := by
  ac_rfl

lemma joinIndex_remainderFin_quotientIndex (Q : ℕ) (hQ : 0 < Q)
    {D : ℕ} (i : Fin (Q * D)) :
    joinIndex Q hQ (remainderFin Q hQ i) (quotientIndex Q i) = i := by
  apply Fin.ext
  exact (val_eq_mul_quotient_add_remainder Q hQ i).symm

/-- The old selector, written in `Q`-coset coordinates. -/
def oldCosetPiece (P Q : ℕ) (hQ : 0 < Q) (s : LiftData (P * Q))
    (a b : Fin Q) : LiftData P :=
  restrictCoset Q hQ (s.transport (Nat.mul_comm P Q)) a b

theorem oldCosetPiece_separated (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (s : LiftData (P * Q)) (hs : s.Separated) (a b : Fin Q) :
    (oldCosetPiece P Q hQ s a b).Separated := by
  apply restrictCoset_separated Q hQ (Nat.ne_of_gt hP)
      (s.transport (Nat.mul_comm P Q))
  exact LiftData.separated_transport (Nat.mul_comm P Q) s hs

lemma oldCosetPiece_at_quotient (P Q : ℕ) (hQ : 0 < Q)
    (s : LiftData (P * Q)) (i j : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let j' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) j
    (oldCosetPiece P Q hQ s (remainderFin Q hQ i') (remainderFin Q hQ j')).k
        (quotientIndex Q i') (quotientIndex Q j') = s.k i j ∧
    (oldCosetPiece P Q hQ s (remainderFin Q hQ i') (remainderFin Q hQ j')).l
        (quotientIndex Q i') (quotientIndex Q j') = s.l i j := by
  dsimp only
  simp only [oldCosetPiece, restrictCoset]
  rw [joinIndex_remainderFin_quotientIndex Q hQ,
    joinIndex_remainderFin_quotientIndex Q hQ]
  simp

lemma remainderFin_target_oldIndex (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (hQ : 0 < Q) (hcop : p.Coprime Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    remainderFin Q hQ I =
      mulCosetEquiv p Q hQ hcop (remainderFin Q hQ i') := by
  dsimp only
  apply Fin.ext
  simp only [remainderFin_val, remainderIndex, Fin.val_cast, oldIndex,
    mulCosetEquiv_apply, mulCosetMap]
  simp [Nat.mul_mod]

lemma quotientIndex_target_oldIndex (p : ℕ) (hp : 0 < p)
    (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    quotientIndex Q I =
      localOldIndex p P Q hp hP hQ (remainderFin Q hQ i')
        (quotientIndex Q i') := by
  dsimp only
  let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
  let I : Fin (Q * (p * P)) :=
    Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
  let a : Fin Q := remainderFin Q hQ i'
  let x : Fin P := quotientIndex Q i'
  have hi := val_eq_mul_quotient_add_remainder Q hQ i'
  have hI := val_eq_mul_quotient_add_remainder Q hQ I
  have hspec : (I : ℕ) =
      Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
        (mulCosetMap p Q hQ a : ℕ) := by
    calc
      (I : ℕ) = p * (i : ℕ) := rfl
      _ = p * (i' : ℕ) := rfl
      _ = p * (Q * (x : ℕ) + (a : ℕ)) := by
        exact congrArg (fun z : ℕ ↦ p * z)
          (by simpa only [x, a, remainderFin_val] using hi)
      _ = Q * (p * (x : ℕ)) + p * (a : ℕ) := by ring
      _ = Q * (p * (x : ℕ)) +
          (Q * cosetCarry p Q a + (mulCosetMap p Q hQ a : ℕ)) := by
            rw [mul_val_eq_coset p Q hQ a]
      _ = Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
          (mulCosetMap p Q hQ a : ℕ) := by
            rw [localOldIndex_val]
            ring
  have hrem : remainderIndex Q I = (mulCosetMap p Q hQ a : ℕ) := by
    rw [remainderIndex, hspec]
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (mulCosetMap p Q hQ a).isLt
  apply Fin.ext
  have heq : Q * (quotientIndex Q I : ℕ) + remainderIndex Q I =
      Q * (localOldIndex p P Q hp hP hQ a x : ℕ) + remainderIndex Q I := by
    calc
      _ = (I : ℕ) := hI.symm
      _ = Q * (localOldIndex p P Q hp hP hQ a x : ℕ) +
          (mulCosetMap p Q hQ a : ℕ) := hspec
      _ = _ := by rw [hrem]
  exact Nat.mul_left_cancel hQ (Nat.add_right_cancel heq)

lemma sourceCoset_target_oldIndex (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (hQ : 0 < Q) (hcop : p.Coprime Q) (i : Fin (P * Q)) :
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    (mulCosetEquiv p Q hQ hcop).symm (remainderFin Q hQ I) =
      remainderFin Q hQ i' := by
  dsimp only
  rw [remainderFin_target_oldIndex p hp P Q hQ hcop]
  exact (mulCosetEquiv p Q hQ hcop).symm_apply_apply _

/-- If an integral squared distance occurs at denominator `Q*D`, then the two
coordinate numerators are divisible by `Q`.  Consequently the two residues
belong to the same `Q`-coset.  Notice that the lifts themselves are arbitrary. -/
theorem same_remainders_of_integral_sqDist
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (i₁ j₁ i₂ j₂ : Fin (Q * D))
    (hInt : ∃ z : ℤ, sqDist (t.point i₁ j₁) (t.point i₂ j₂) = z) :
    remainderIndex Q i₁ = remainderIndex Q i₂ ∧
      remainderIndex Q j₁ = remainderIndex Q j₂ := by
  let N : ℕ := Q * D
  have hN : N ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD
  have hconf : (N : ℤ) ^ 2 ∣
      conflictNumerator N i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) :=
    (sqDist_liftedPoint_isInt_iff N hN i₁ j₁ i₂ j₂
      (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)).mp hInt
  have hdist : (N : ℤ) ^ 2 ∣
      distanceNumerator N i₁ j₁ i₂ j₂
        (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) :=
    (distanceNumerator_dvd_iff N i₁ j₁ i₂ j₂
      (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂)).2 hconf
  have hQN : (Q : ℤ) ^ 2 ∣ (N : ℤ) ^ 2 := by
    refine ⟨(D : ℤ) ^ 2, ?_⟩
    simp only [N]
    push_cast
    ring
  have hQdist := dvd_trans hQN hdist
  let A : ℤ := (i₁ : ℕ) - (i₂ : ℕ) + (N : ℤ) * (t.k i₁ j₁ - t.k i₂ j₂)
  let B : ℤ := (j₁ : ℕ) - (j₂ : ℕ) + (N : ℤ) * (t.l i₁ j₁ - t.l i₂ j₂)
  have hAB : (Q : ℤ) ^ 2 ∣ A ^ 2 + B ^ 2 := by
    rcases hQdist with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc
      A ^ 2 + B ^ 2 = distanceNumerator N i₁ j₁ i₂ j₂
          (t.k i₁ j₁) (t.l i₁ j₁) (t.k i₂ j₂) (t.l i₂ j₂) := by
            dsimp [A, B, distanceNumerator, conflictNumerator]
            ring
      _ = (Q : ℤ) ^ 2 * c := hc
  obtain ⟨hA, hB⟩ := hRigid A B hAB
  have hQNk (k : ℤ) : (Q : ℤ) ∣ (N : ℤ) * k := by
    refine ⟨(D : ℤ) * k, ?_⟩
    simp only [N]
    push_cast
    ring
  have hiDiff : (Q : ℤ) ∣ ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ) := by
    rw [show ((i₁ : ℕ) : ℤ) - ((i₂ : ℕ) : ℤ) =
        A - (N : ℤ) * (t.k i₁ j₁ - t.k i₂ j₂) by
      dsimp [A]
      ring]
    exact dvd_sub hA (hQNk (t.k i₁ j₁ - t.k i₂ j₂))
  have hjDiff : (Q : ℤ) ∣ ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ) := by
    rw [show ((j₁ : ℕ) : ℤ) - ((j₂ : ℕ) : ℤ) =
        B - (N : ℤ) * (t.l i₁ j₁ - t.l i₂ j₂) by
      dsimp [B]
      ring]
    exact dvd_sub hB (hQNk (t.l i₁ j₁ - t.l i₂ j₂))
  let _ : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have residue_eq_of_dvd {a b : ℕ}
      (h : (Q : ℤ) ∣ (a : ℤ) - (b : ℤ)) : a % Q = b % Q := by
    rcases h with ⟨c, hc⟩
    have hz : (a : ZMod Q) - (b : ZMod Q) = 0 := by
      have hc' := congrArg (fun x : ℤ ↦ (x : ZMod Q)) hc
      push_cast at hc'
      simpa using hc'
    have heq : (a : ZMod Q) = (b : ZMod Q) := sub_eq_zero.mp hz
    have hv := congrArg ZMod.val heq
    simpa using hv
  exact ⟨residue_eq_of_dvd hiDiff, residue_eq_of_dvd hjDiff⟩

/-- Distinct `Q`-cosets can never contain a pair at integral squared
distance.  This is the cross-coset half of the `P`/`Q` reduction. -/
theorem cross_coset_sqDist_not_integral
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (i₁ j₁ i₂ j₂ : Fin (Q * D))
    (hcross : remainderIndex Q i₁ ≠ remainderIndex Q i₂ ∨
      remainderIndex Q j₁ ≠ remainderIndex Q j₂) :
    ¬∃ z : ℤ, sqDist (t.point i₁ j₁) (t.point i₂ j₂) = z := by
  intro hInt
  obtain ⟨hi, hj⟩ := same_remainders_of_integral_sqDist Q hQ hRigid hD t
    i₁ j₁ i₂ j₂ hInt
  exact hcross.elim (fun h ↦ h hi) (fun h ↦ h hj)

/-- Exact within-coset reduction.  For each of the `Q²` cosets, distances
are identified with distances in a local selector at denominator `D`. -/
def ModeledWithinCosets (Q : ℕ) (hQ : 0 < Q) {D : ℕ}
    (t : LiftData (Q * D)) (pieces : Fin Q → Fin Q → LiftData D) : Prop :=
  ∀ i₁ j₁ i₂ j₂,
    remainderIndex Q i₁ = remainderIndex Q i₂ →
    remainderIndex Q j₁ = remainderIndex Q j₂ →
    sqDist (t.point i₁ j₁) (t.point i₂ j₂) =
      sqDist
        ((pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁)).point
          (quotientIndex Q i₁) (quotientIndex Q j₁))
        ((pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁)).point
          (quotientIndex Q i₂) (quotientIndex Q j₂))

theorem assembleCosets_modeled (Q : ℕ) (hQ : 0 < Q) {D : ℕ} (hD : D ≠ 0)
    (pieces : Fin Q → Fin Q → LiftData D) :
    ModeledWithinCosets Q hQ (assembleCosets Q hQ pieces) pieces := by
  intro i₁ j₁ i₂ j₂ hi hj
  simp only [LiftData.point, assembleCosets, liftedPoint, sqDist]
  have hvi₁ := val_eq_mul_quotient_add_remainder Q hQ i₁
  have hvi₂ := val_eq_mul_quotient_add_remainder Q hQ i₂
  have hvj₁ := val_eq_mul_quotient_add_remainder Q hQ j₁
  have hvj₂ := val_eq_mul_quotient_add_remainder Q hQ j₂
  have hai : remainderFin Q hQ i₂ = remainderFin Q hQ i₁ := by
    apply Fin.ext
    exact hi.symm
  have haj : remainderFin Q hQ j₂ = remainderFin Q hQ j₁ := by
    apply Fin.ext
    exact hj.symm
  rw [hai, haj]
  push_cast
  field_simp [Nat.ne_of_gt hQ, hD]
  rw [hvi₁, hvi₂, hvj₁, hvj₂, hi, hj]
  push_cast
  ring

/-- Glue separated local selectors on the `Q²` cosets.  Same-coset pairs
reduce to a local selector; different-coset pairs are handled solely by the
integer norm condition. -/
theorem separated_of_coset_model
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (t : LiftData (Q * D))
    (pieces : Fin Q → Fin Q → LiftData D)
    (hpieces : ∀ a b, (pieces a b).Separated)
    (hmodel : ModeledWithinCosets Q hQ t pieces) : t.Separated := by
  rw [LiftData.separated_iff_sqDist_not_int (Nat.mul_ne_zero (Nat.ne_of_gt hQ) hD)]
  intro i₁ j₁ i₂ j₂ hne
  by_cases hi : remainderIndex Q i₁ = remainderIndex Q i₂
  · by_cases hj : remainderIndex Q j₁ = remainderIndex Q j₂
    · have hquot :
          (quotientIndex Q i₁, quotientIndex Q j₁) ≠
            (quotientIndex Q i₂, quotientIndex Q j₂) := by
        intro h
        apply hne
        apply Prod.ext <;> apply Fin.ext
        · have hq := congrArg (fun x : Fin D ↦ (x : ℕ)) (congrArg Prod.fst h)
          rw [val_eq_mul_quotient_add_remainder Q hQ i₁,
            val_eq_mul_quotient_add_remainder Q hQ i₂, hi, hq]
        · have hq := congrArg (fun x : Fin D ↦ (x : ℕ)) (congrArg Prod.snd h)
          rw [val_eq_mul_quotient_add_remainder Q hQ j₁,
            val_eq_mul_quotient_add_remainder Q hQ j₂, hj, hq]
      have hsep := (LiftData.separated_iff_sqDist_not_int hD
        (pieces (remainderFin Q hQ i₁) (remainderFin Q hQ j₁))).mp
          (hpieces _ _) (quotientIndex Q i₁) (quotientIndex Q j₁)
            (quotientIndex Q i₂) (quotientIndex Q j₂) hquot
      rw [hmodel i₁ j₁ i₂ j₂ hi hj]
      exact hsep
    · exact cross_coset_sqDist_not_integral Q hQ hRigid hD t i₁ j₁ i₂ j₂ (Or.inr hj)
  · exact cross_coset_sqDist_not_integral Q hQ hRigid hD t i₁ j₁ i₂ j₂ (Or.inl hi)

/-- Copying one selector onto every `Q`-coset works for every modulus with the
integer square-norm rigidity property.  This strictly generalizes the
anisotropic-prime `primeCopy_separated` theorem and includes powers of `2`. -/
theorem primeCopy_separated_of_squareNormRigid
    (Q : ℕ) (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    {D : ℕ} (hD : D ≠ 0) (s : LiftData D) (hs : s.Separated) :
    (primeCopyLift Q s).Separated := by
  apply separated_of_coset_model Q hQ hRigid hD (primeCopyLift Q s)
    (fun _ _ ↦ s) (fun _ _ ↦ hs)
  intro i₁ j₁ i₂ j₂ hi hj
  exact sqDist_primeCopy_of_same_remainders Q hQ hD s i₁ j₁ i₂ j₂ hi hj

/-- Literal extension into the coset-friendly target denominator.  The cast
in the arguments is just the equality `Q*(p*P)=p*(P*Q)` read backwards. -/
def PQRawPrimeExtends (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (s : LiftData (P * Q)) (t : LiftData (Q * (p * P))) : Prop :=
  ∀ i j,
    t.k (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i))
        (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)) = s.k i j ∧
    t.l (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i))
        (Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)) = s.l i j

/-- A family of literal pure extensions, one for each `Q²`-coset, together
with the exact gluing and literal-preservation facts.  The good-permutation
construction supplies `localExtends` and `localSeparated`; the coordinate
calculation supplies `modeled` and `literal`. -/
structure PQCosetExtension (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hQ : 0 < Q)
    (s : LiftData (P * Q)) where
  oldLocal : Fin Q → Fin Q → LiftData P
  pureLocal : Fin Q → Fin Q → LiftData (p * P)
  localExtends : ∀ a b, PrimeExtends p hp (oldLocal a b) (pureLocal a b)
  pureSeparated : ∀ a b, (pureLocal a b).Separated
  /-- The pure pieces after permuting the `Q`-cosets and applying the exact
  quotient-carry shifts. -/
  newLocal : Fin Q → Fin Q → LiftData (p * P)
  localSeparated : ∀ a b, (newLocal a b).Separated
  target : LiftData (Q * (p * P))
  modeled : ModeledWithinCosets Q hQ target newLocal
  literal : PQRawPrimeExtends p hp P Q s target

/-- Construct the full coset-gluing certificate from a separated old
selector and the pure `P → pP` extension theorem.

The inverse of `mulCosetEquiv` identifies which old `Q`-coset feeds a target
coset.  `shiftLift` by `cosetCarry` then places every old pure residue at the
actual quotient of the full old index.  Thus the final `literal` field is an
equality of integer lifts, rather than merely an equality of selected
rational points. -/
theorem exists_PQCosetExtension
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hcop : p.Coprime Q) (s : LiftData (P * Q)) (hs : s.Separated)
    (pureExtension : ∀ u : LiftData P, u.Separated →
      ∃ v : LiftData (p * P), PrimeExtends p hp u v ∧ v.Separated) :
    Nonempty (PQCosetExtension p hp P Q hQ s) := by
  let oldLocal : Fin Q → Fin Q → LiftData P :=
    fun a b ↦ oldCosetPiece P Q hQ s a b
  have oldSeparated : ∀ a b, (oldLocal a b).Separated := by
    intro a b
    exact oldCosetPiece_separated P Q hP hQ s hs a b
  choose pureLocal localExtends pureSeparated using
    fun a b ↦ pureExtension (oldLocal a b) (oldSeparated a b)
  let source : Fin Q → Fin Q := fun a ↦ (mulCosetEquiv p Q hQ hcop).symm a
  let newLocal : Fin Q → Fin Q → LiftData (p * P) := fun A B ↦
    shiftLift (cosetCarryIndex p P Q hp hP hQ (source A))
      (cosetCarryIndex p P Q hp hP hQ (source B))
      (pureLocal (source A) (source B))
  have newSeparated : ∀ A B, (newLocal A B).Separated := by
    intro A B
    exact shiftLift_separated (Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hP))
      (cosetCarryIndex p P Q hp hP hQ (source A))
      (cosetCarryIndex p P Q hp hP hQ (source B))
      (pureLocal (source A) (source B)) (pureSeparated (source A) (source B))
  let target : LiftData (Q * (p * P)) := assembleCosets Q hQ newLocal
  have modeled : ModeledWithinCosets Q hQ target newLocal :=
    assembleCosets_modeled Q hQ (Nat.mul_ne_zero (Nat.ne_of_gt hp) (Nat.ne_of_gt hP))
      newLocal
  have literal : PQRawPrimeExtends p hp P Q s target := by
    intro i j
    let i' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) i
    let j' : Fin (Q * P) := Fin.cast (Nat.mul_comm P Q) j
    let I : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp i)
    let J : Fin (Q * (p * P)) :=
      Fin.cast (pqTargetDenom_eq p P Q).symm (oldIndex p hp j)
    let a : Fin Q := remainderFin Q hQ i'
    let b : Fin Q := remainderFin Q hQ j'
    let A : Fin Q := remainderFin Q hQ I
    let B : Fin Q := remainderFin Q hQ J
    let x : Fin P := quotientIndex Q i'
    let y : Fin P := quotientIndex Q j'
    have hsourceA : source A = a := by
      simpa only [source, A, a, I, i'] using
        sourceCoset_target_oldIndex p hp P Q hQ hcop i
    have hsourceB : source B = b := by
      simpa only [source, B, b, J, j'] using
        sourceCoset_target_oldIndex p hp P Q hQ hcop j
    have hquotI : quotientIndex Q I =
        localOldIndex p P Q hp hP hQ a x := by
      simpa only [I, i', a, x] using
        quotientIndex_target_oldIndex p hp P Q hP hQ i
    have hquotJ : quotientIndex Q J =
        localOldIndex p P Q hp hP hQ b y := by
      simpa only [J, j', b, y] using
        quotientIndex_target_oldIndex p hp P Q hP hQ j
    have hshift :
        (newLocal A B).k (quotientIndex Q I) (quotientIndex Q J) =
            (pureLocal a b).k (oldIndex p hp x) (oldIndex p hp y) ∧
        (newLocal A B).l (quotientIndex Q I) (quotientIndex Q J) =
            (pureLocal a b).l (oldIndex p hp x) (oldIndex p hp y) := by
      simp only [newLocal, hsourceA, hsourceB, hquotI, hquotJ]
      exact shiftLift_at_localOldIndex p P Q hp hP hQ a b (pureLocal a b) x y
    have hext := localExtends a b x y
    have hold :
        (oldLocal a b).k x y = s.k i j ∧
        (oldLocal a b).l x y = s.l i j := by
      simpa only [oldLocal, a, b, x, y, i', j'] using
        oldCosetPiece_at_quotient P Q hQ s i j
    change target.k I J = s.k i j ∧ target.l I J = s.l i j
    change (newLocal A B).k (quotientIndex Q I) (quotientIndex Q J) = s.k i j ∧
      (newLocal A B).l (quotientIndex Q I) (quotientIndex Q J) = s.l i j
    exact ⟨hshift.1.trans (hext.1.trans hold.1),
      hshift.2.trans (hext.2.trans hold.2)⟩
  exact ⟨{
    oldLocal := oldLocal
    pureLocal := pureLocal
    localExtends := localExtends
    pureSeparated := pureSeparated
    newLocal := newLocal
    localSeparated := newSeparated
    target := target
    modeled := modeled
    literal := literal }⟩

lemma transported_raw_primeExtends
    (p : ℕ) (hp : 0 < p) (P Q : ℕ)
    (s : LiftData (P * Q)) (t : LiftData (Q * (p * P)))
    (h : PQRawPrimeExtends p hp P Q s t) :
    PrimeExtends p hp s (t.transport (pqTargetDenom_eq p P Q)) := by
  intro i j
  rw [LiftData.transport_k, LiftData.transport_l]
  exact h i j

/-- The complete abstract `P`/`Q` reduction.  Literal separated pure
extensions on all `Q²` cosets glue to a literal separated extension at the
full denominator. -/
theorem PQCosetExtension.toPrimeExtension
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : P ≠ 0)
    (hQ : 0 < Q) (hRigid : SquareNormRigid Q)
    (s : LiftData (P * Q)) (E : PQCosetExtension p hp P Q hQ s) :
    ∃ t : LiftData (p * (P * Q)), PrimeExtends p hp s t ∧ t.Separated := by
  let rawSeparated : E.target.Separated :=
    separated_of_coset_model Q hQ hRigid (Nat.mul_ne_zero (Nat.ne_of_gt hp) hP)
      E.target E.newLocal E.localSeparated E.modeled
  refine ⟨E.target.transport (pqTargetDenom_eq p P Q),
    transported_raw_primeExtends p hp P Q s E.target E.literal, ?_⟩
  exact LiftData.separated_transport (pqTargetDenom_eq p P Q) E.target rawSeparated

/-- The usable `P`/`Q` reduction: a pure extension theorem at `P` yields a
literal separated extension at `P*Q`. -/
theorem primeExtension_of_pure_cosets
    (p : ℕ) (hp : 0 < p) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hcop : p.Coprime Q) (hRigid : SquareNormRigid Q)
    (s : LiftData (P * Q)) (hs : s.Separated)
    (pureExtension : ∀ u : LiftData P, u.Separated →
      ∃ v : LiftData (p * P), PrimeExtends p hp u v ∧ v.Separated) :
    ∃ t : LiftData (p * (P * Q)), PrimeExtends p hp s t ∧ t.Separated := by
  obtain ⟨E⟩ := exists_PQCosetExtension p hp P Q hP hQ hcop s hs pureExtension
  exact PQCosetExtension.toPrimeExtension p hp P Q (Nat.ne_of_gt hP) hQ hRigid s E

end

end Erdos215.Selector
