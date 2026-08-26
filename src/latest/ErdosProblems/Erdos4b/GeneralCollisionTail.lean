/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionSupport
import BoundedGaps.Maynard.MaynardS2RestrictedStarredSummandBound

/-!
# Trivial and nontrivial parts of the cross-collision matrix

The auxiliary-matrix expansions used by the unseparated normalization and
the pinned main term both contain a distinguished all-one matrix.  This file
separates that matrix from the finite sum.  In the unpinned case the
nontrivial tail is exactly the cross-gcd amplification minus one.

Keeping this separation as an exact finite identity is useful for the
analytic step: the all-one term is the tensor-product Maynard main term,
whereas every term in the tail contains a rough cross-family collision
prime.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance erdos4GeneralCollisionTailPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Affine compatibility forces every diagonal auxiliary entry to be one:
on a diagonal the two affine constants differ by exactly one. -/
theorem crossAuxiliary_diagonal_eq_one_of_affineCompatible
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ}
    {a : CrossAuxiliaryDivisors H d e d' e'}
    (hcompat : CrossAuxiliaryAffineCompatible m q a) (h : H) :
    (a (h, h)).1 = 1 := by
  let x := m * (h.1 * q)
  have hmod : x + 1 ≡ x + 0 [MOD (a (h, h)).1] := by
    simpa [x] using hcompat (h, h)
  have honeZero : 1 ≡ 0 [MOD (a (h, h)).1] :=
    Nat.ModEq.add_left_cancel' x hmod
  exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp honeZero)

/-- Restrict an auxiliary matrix to the genuinely cross-coordinate entries.
The ordered-pair labels remain `(companion, first)`; the generic starred-tail
API only uses the incidence relation, which is invariant under this naming. -/
def crossAuxiliaryOffDiagonalTuple
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') :
    ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ :=
  fun ab _ ↦ (a ab).1

@[simp] theorem crossAuxiliaryOffDiagonalTuple_apply
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e')
    (ab : H × H) (hab : ab ∈ BoundedGaps.Maynard.offDiagonalPairs H) :
    crossAuxiliaryOffDiagonalTuple a ab hab = (a ab).1 := by
  rfl

/-- Once affine compatibility has killed the diagonal entries, a nontrivial
matrix remains nontrivial after restriction to the off-diagonal pairs. -/
theorem crossAuxiliaryOffDiagonalTuple_ne_one_of_ne_one
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    {a : CrossAuxiliaryDivisors H d e d' e'}
    (hcompat : CrossAuxiliaryAffineCompatible m q a)
    (ha : a ≠ oneCrossAuxiliaryDivisors hDpos hEpos) :
    crossAuxiliaryOffDiagonalTuple a ≠
      BoundedGaps.Maynard.oneCrossMoebiusTuple H := by
  intro hoff
  apply ha
  apply (crossAuxiliaryDivisors_eq_one_iff hDpos hEpos a).mpr
  intro ba
  rcases ba with ⟨b, c⟩
  by_cases hdiag : b = c
  · dsimp at ⊢
    subst c
    exact crossAuxiliary_diagonal_eq_one_of_affineCompatible hcompat b
  · let ab : H × H := (b, c)
    have hab : ab ∈ BoundedGaps.Maynard.offDiagonalPairs H := by
      rw [BoundedGaps.Maynard.offDiagonalPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ ab, hdiag⟩
    have hvalue := congrFun (congrFun hoff ab) hab
    simpa [crossAuxiliaryOffDiagonalTuple, ab,
      BoundedGaps.Maynard.oneCrossMoebiusTuple] using hvalue

/-- On the affine-compatible locus, the off-diagonal projection is
injective: compatibility has already determined every omitted diagonal
entry to be one. -/
theorem crossAuxiliaryOffDiagonalTuple_injOn_affineCompatible
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ} :
    Set.InjOn
      (crossAuxiliaryOffDiagonalTuple
        (H := H) (d := d) (e := e) (d' := d') (e' := e'))
      {a | CrossAuxiliaryAffineCompatible m q a} := by
  intro a ha b hb hab
  funext ba
  apply Subtype.ext
  by_cases hdiag : ba.1 = ba.2
  · rcases ba with ⟨x, y⟩
    dsimp at hdiag ⊢
    subst y
    rw [crossAuxiliary_diagonal_eq_one_of_affineCompatible ha,
      crossAuxiliary_diagonal_eq_one_of_affineCompatible hb]
  · have hoff : ba ∈ BoundedGaps.Maynard.offDiagonalPairs H := by
      rw [BoundedGaps.Maynard.offDiagonalPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ ba, hdiag⟩
    exact congrFun (congrFun hab ba) hoff

/-- For an affine-compatible matrix, deleting the forced diagonal ones does
not change its multiplicative totient weight. -/
theorem crossAuxiliaryTotientWeight_eq_offDiagonal
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e')
    (hcompat : CrossAuxiliaryAffineCompatible m q a) :
    crossAuxiliaryTotientWeight a =
      BoundedGaps.Maynard.crossTotientProduct H
        (crossAuxiliaryOffDiagonalTuple a) := by
  classical
  unfold crossAuxiliaryTotientWeight
    BoundedGaps.Maynard.crossTotientProduct
  push_cast
  let f : H × H → ℝ := fun ba ↦ (Nat.totient (a ba).1 : ℝ)
  have hoff :
      (∏ i ∈ (BoundedGaps.Maynard.offDiagonalPairs H).attach,
          (Nat.totient
            (crossAuxiliaryOffDiagonalTuple a i.1 i.2) : ℝ)) =
        ∏ ba ∈ BoundedGaps.Maynard.offDiagonalPairs H, f ba := by
    rw [← Finset.prod_attach
      (BoundedGaps.Maynard.offDiagonalPairs H) f]
    apply Finset.prod_congr rfl
    intro i hi
    rfl
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (H × H)) (fun ba ↦ ba.1 ≠ ba.2) f
  have hdiag :
      (∏ ba ∈ (Finset.univ : Finset (H × H)) with ¬ba.1 ≠ ba.2,
          f ba) = 1 := by
    apply Finset.prod_eq_one
    intro ba hba
    have heq : ba.1 = ba.2 := not_ne_iff.mp (Finset.mem_filter.mp hba).2
    rcases ba with ⟨b, c⟩
    dsimp at heq ⊢
    subst c
    dsimp [f]
    rw [crossAuxiliary_diagonal_eq_one_of_affineCompatible hcompat]
    norm_num
  change (∏ ba : H × H, f ba) =
    ∏ i ∈ (BoundedGaps.Maynard.offDiagonalPairs H).attach,
      (Nat.totient
        (crossAuxiliaryOffDiagonalTuple a i.1 i.2) : ℝ)
  rw [hoff]
  rw [BoundedGaps.Maynard.offDiagonalPairs]
  rw [← hsplit, hdiag, mul_one]

/-- The same diagonal deletion preserves the pinned `g(p)=p-2` weight. -/
theorem crossAuxiliaryS2GWeight_eq_offDiagonal
    {H : Finset ℕ} {d e d' e' : H → ℕ} {m q : ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e')
    (hcompat : CrossAuxiliaryAffineCompatible m q a) :
    crossAuxiliaryS2GWeight a =
      BoundedGaps.Maynard.crossS2GProduct H
        (crossAuxiliaryOffDiagonalTuple a) := by
  classical
  unfold crossAuxiliaryS2GWeight
    BoundedGaps.Maynard.crossS2GProduct
  push_cast
  let f : H × H → ℝ := fun ba ↦
    (BoundedGaps.Maynard.maynardS2G (a ba).1 : ℝ)
  have hoff :
      (∏ i ∈ (BoundedGaps.Maynard.offDiagonalPairs H).attach,
          (BoundedGaps.Maynard.maynardS2G
            (crossAuxiliaryOffDiagonalTuple a i.1 i.2) : ℝ)) =
        ∏ ba ∈ BoundedGaps.Maynard.offDiagonalPairs H, f ba := by
    rw [← Finset.prod_attach
      (BoundedGaps.Maynard.offDiagonalPairs H) f]
    apply Finset.prod_congr rfl
    intro i hi
    rfl
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (H × H)) (fun ba ↦ ba.1 ≠ ba.2) f
  have hdiag :
      (∏ ba ∈ (Finset.univ : Finset (H × H)) with ¬ba.1 ≠ ba.2,
          f ba) = 1 := by
    apply Finset.prod_eq_one
    intro ba hba
    have heq : ba.1 = ba.2 := not_ne_iff.mp (Finset.mem_filter.mp hba).2
    rcases ba with ⟨b, c⟩
    dsimp at heq ⊢
    subst c
    dsimp [f]
    rw [crossAuxiliary_diagonal_eq_one_of_affineCompatible hcompat]
    simp [BoundedGaps.Maynard.maynardS2G]
  change (∏ ba : H × H, f ba) =
    ∏ i ∈ (BoundedGaps.Maynard.offDiagonalPairs H).attach,
      (BoundedGaps.Maynard.maynardS2G
        (crossAuxiliaryOffDiagonalTuple a i.1 i.2) : ℝ)
  rw [hoff]
  rw [BoundedGaps.Maynard.offDiagonalPairs]
  rw [← hsplit, hdiag, mul_one]

/-- Every auxiliary matrix on standard first-family support restricts to a
rough squarefree cross tuple.  This is the precise type-level bridge to the
existing starred-tail API. -/
theorem crossAuxiliaryOffDiagonalTuple_mem_roughCrossTupleSupport
    {H : Finset ℕ} {RD w : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (a : CrossAuxiliaryDivisors H d e d' e') :
    crossAuxiliaryOffDiagonalTuple a ∈
      BoundedGaps.Maynard.roughCrossTupleSupport H w (RD ^ 2) := by
  rw [BoundedGaps.Maynard.roughCrossTupleSupport, Finset.mem_pi]
  intro ab hab
  let P := crossCoordinateGcdProduct H d e d' e'
  let n := (a ab).1
  change n ∈ BoundedGaps.Maynard.squarefreeRoughUnitSupport w (RD ^ 2)
  have hPdata := crossCoordinateGcdProduct_roughModulusData hd hd' hDD hEE
  have hnGcd : n ∣
      Nat.gcd (Nat.lcm (d ab.2) (d' ab.2))
        (Nat.lcm (e ab.1) (e' ab.1)) := by
    exact (Nat.mem_divisors.mp (a ab).2).1
  have hGcdInner :
      Nat.gcd (Nat.lcm (d ab.2) (d' ab.2))
          (Nat.lcm (e ab.1) (e' ab.1)) ∣
        ∏ c : H, Nat.gcd (Nat.lcm (d c) (d' c))
          (Nat.lcm (e ab.1) (e' ab.1)) := by
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ ab.2)
  have hInnerOuter :
      (∏ c : H, Nat.gcd (Nat.lcm (d c) (d' c))
          (Nat.lcm (e ab.1) (e' ab.1))) ∣ P := by
    unfold P crossCoordinateGcdProduct
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ ab.1)
  have hnP : n ∣ P := hnGcd.trans (hGcdInner.trans hInnerOuter)
  have hnPos : 0 < n := Nat.pos_of_mem_divisors (a ab).2
  have hnSq : Squarefree n := hPdata.2.1.squarefree_of_dvd hnP
  have hnLeP : n ≤ P := Nat.le_of_dvd hPdata.1 hnP
  rw [BoundedGaps.Maynard.squarefreeRoughUnitSupport, Finset.mem_insert]
  by_cases hnOne : n = 1
  · exact Or.inl hnOne
  · apply Or.inr
    rw [BoundedGaps.Maynard.squarefreeRoughSupport, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, hnLeP.trans (Nat.le_of_lt hPdata.2.2)⟩,
      hnSq, ?_⟩
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hwp : w < p :=
      cutoff_lt_prime_of_dvd_crossAuxiliary hd hd' a ab
        hpPrime hpn
    have hpLe : p ≤ RD ^ 2 :=
      (Nat.le_of_dvd hnPos hpn).trans
        (hnLeP.trans (Nat.le_of_lt hPdata.2.2))
    rw [BoundedGaps.Maynard.roughPrimeSupport, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLe⟩, hpPrime⟩

/-- The affine-compatible nontrivial auxiliary matrices inject into the
ordinary rough starred tail.  Consequently their reciprocal-totient-square
mass has the same inverse-cutoff bound, with no matrix multiplicity factor. -/
theorem sum_affineCompatible_inv_crossAuxiliaryTotientWeight_sq_le
    {H : Finset ℕ} {RD w m q : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a ∈
        ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
          (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
            (CrossAuxiliaryAffineCompatible m q),
        (1 : ℝ) / crossAuxiliaryTotientWeight a ^ 2) ≤
      BoundedGaps.Maynard.roughCrossTupleTotientSquareTail H w (RD ^ 2) := by
  classical
  let S :=
    ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
      (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
        (CrossAuxiliaryAffineCompatible m q)
  let projection := crossAuxiliaryOffDiagonalTuple
    (H := H) (d := d) (e := e) (d' := d') (e' := e')
  have hinj : Set.InjOn projection S := by
    apply (crossAuxiliaryOffDiagonalTuple_injOn_affineCompatible
      (H := H) (d := d) (e := e) (d' := d') (e' := e')
      (m := m) (q := q)).mono
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have himage : S.image projection ⊆
      (BoundedGaps.Maynard.roughCrossTupleSupport H w (RD ^ 2)).erase
        (BoundedGaps.Maynard.oneCrossMoebiusTuple H) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    have haData := Finset.mem_filter.mp ha
    have haNe := (Finset.mem_erase.mp haData.1).1
    exact Finset.mem_erase.mpr ⟨
      crossAuxiliaryOffDiagonalTuple_ne_one_of_ne_one hDpos hEpos
        haData.2 haNe,
      crossAuxiliaryOffDiagonalTuple_mem_roughCrossTupleSupport
        hd hd' hDD hEE a⟩
  change (∑ a ∈ S, (1 : ℝ) / crossAuxiliaryTotientWeight a ^ 2) ≤ _
  calc
    (∑ a ∈ S, (1 : ℝ) / crossAuxiliaryTotientWeight a ^ 2) =
        ∑ a ∈ S,
          BoundedGaps.Maynard.crossTotientSquareWeight H (projection a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcompat := (Finset.mem_filter.mp ha).2
      unfold BoundedGaps.Maynard.crossTotientSquareWeight
      rw [crossAuxiliaryTotientWeight_eq_offDiagonal a hcompat]
    _ = ∑ s ∈ S.image projection,
          BoundedGaps.Maynard.crossTotientSquareWeight H s := by
      exact (Finset.sum_image
        (f := BoundedGaps.Maynard.crossTotientSquareWeight H) hinj).symm
    _ ≤ ∑ s ∈
          (BoundedGaps.Maynard.roughCrossTupleSupport H w (RD ^ 2)).erase
            (BoundedGaps.Maynard.oneCrossMoebiusTuple H),
          BoundedGaps.Maynard.crossTotientSquareWeight H s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro s hs hsNot
      unfold BoundedGaps.Maynard.crossTotientSquareWeight
      positivity
    _ = _ := rfl

/-- Pinned analogue of the preceding transfer.  The projected matrix weight
is exactly Maynard's reciprocal-`g`-square starred weight. -/
theorem sum_affineCompatible_inv_crossAuxiliaryS2GWeight_sq_le
    {H : Finset ℕ} {RD w m q : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a ∈
        ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
          (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
            (CrossAuxiliaryAffineCompatible m q),
        (1 : ℝ) / crossAuxiliaryS2GWeight a ^ 2) ≤
      BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail
        H w (RD ^ 2) := by
  classical
  let S :=
    ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
      (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
        (CrossAuxiliaryAffineCompatible m q)
  let projection := crossAuxiliaryOffDiagonalTuple
    (H := H) (d := d) (e := e) (d' := d') (e' := e')
  have hinj : Set.InjOn projection S := by
    apply (crossAuxiliaryOffDiagonalTuple_injOn_affineCompatible
      (H := H) (d := d) (e := e) (d' := d') (e' := e')
      (m := m) (q := q)).mono
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have himage : S.image projection ⊆
      (BoundedGaps.Maynard.roughCrossTupleSupport H w (RD ^ 2)).erase
        (BoundedGaps.Maynard.oneCrossMoebiusTuple H) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    have haData := Finset.mem_filter.mp ha
    have haNe := (Finset.mem_erase.mp haData.1).1
    exact Finset.mem_erase.mpr ⟨
      crossAuxiliaryOffDiagonalTuple_ne_one_of_ne_one hDpos hEpos
        haData.2 haNe,
      crossAuxiliaryOffDiagonalTuple_mem_roughCrossTupleSupport
        hd hd' hDD hEE a⟩
  change (∑ a ∈ S, (1 : ℝ) / crossAuxiliaryS2GWeight a ^ 2) ≤ _
  calc
    (∑ a ∈ S, (1 : ℝ) / crossAuxiliaryS2GWeight a ^ 2) =
        ∑ a ∈ S,
          BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight
            H (projection a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hcompat := (Finset.mem_filter.mp ha).2
      have hsupport := crossAuxiliaryOffDiagonalTuple_mem_roughCrossTupleSupport
        hd hd' hDD hEE a
      rw [crossAuxiliaryS2GWeight_eq_offDiagonal a hcompat,
        BoundedGaps.Maynard.crossS2GProduct_inv_sq_eq,
        BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight_eq_inv_g_product
          hsupport]
    _ = ∑ s ∈ S.image projection,
          BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight H s := by
      exact (Finset.sum_image
        (f := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight H)
        hinj).symm
    _ ≤ ∑ s ∈
          (BoundedGaps.Maynard.roughCrossTupleSupport H w (RD ^ 2)).erase
            (BoundedGaps.Maynard.oneCrossMoebiusTuple H),
          BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight H s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro s hs hsNot
      unfold BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight
      exact Finset.prod_nonneg fun x hx ↦
        Finset.prod_nonneg fun p hp ↦
          BoundedGaps.Maynard.maynardS2CrossPrimeSquareWeight_nonneg p
    _ = _ := rfl

/-- Explicit inverse-cutoff form of the unpinned matrix-tail bound. -/
theorem sum_affineCompatible_inv_crossAuxiliaryTotientWeight_sq_le_explicit
    {H : Finset ℕ} {RD w m q : ℕ} {d e d' e' : H → ℕ}
    (hw : 0 < w)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a ∈
        ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
          (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
            (CrossAuxiliaryAffineCompatible m q),
        (1 : ℝ) / crossAuxiliaryTotientWeight a ^ 2) ≤
      (8 * Real.exp 8 / (w : ℝ)) *
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 8) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1) := by
  exact (sum_affineCompatible_inv_crossAuxiliaryTotientWeight_sq_le
    hd hd' hDD hEE hDpos hEpos).trans
      (BoundedGaps.Maynard.roughCrossTupleTotientSquareTail_le
        (Q := RD ^ 2) hw)

/-- Explicit inverse-cutoff form of the pinned matrix-tail bound. -/
theorem sum_affineCompatible_inv_crossAuxiliaryS2GWeight_sq_le_explicit
    {H : Finset ℕ} {RD w m q : ℕ} {d e d' e' : H → ℕ}
    (hw : 2 ≤ w)
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD (primorial w) d')
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b)))
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a ∈
        ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
          (oneCrossAuxiliaryDivisors hDpos hEpos)).filter
            (CrossAuxiliaryAffineCompatible m q),
        (1 : ℝ) / crossAuxiliaryS2GWeight a ^ 2) ≤
      (32 * Real.exp 32 / (w : ℝ)) *
        ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1) := by
  exact (sum_affineCompatible_inv_crossAuxiliaryS2GWeight_sq_le
    hd hd' hDD hEE hDpos hEpos).trans
      (BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail_le
        (Q := RD ^ 2) hw)

/-- The nontrivial part of the auxiliary totient matrix sum. -/
noncomputable def crossAuxiliaryTotientTail
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) : ℝ :=
  ∑ a ∈ ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
      (oneCrossAuxiliaryDivisors hDpos hEpos)),
    crossAuxiliaryTotientWeight a

/-- The nontrivial part of the pinned auxiliary `g(p)=p-2` matrix sum. -/
noncomputable def crossAuxiliaryS2GTail
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) : ℝ :=
  ∑ a ∈ ((Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).erase
      (oneCrossAuxiliaryDivisors hDpos hEpos)),
    crossAuxiliaryS2GWeight a

/-- The full auxiliary totient sum is its unit matrix plus the nontrivial
tail. -/
theorem sum_crossAuxiliaryTotientWeight_eq_one_add_tail
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryTotientWeight a) =
      1 + crossAuxiliaryTotientTail hDpos hEpos := by
  classical
  have hmem : oneCrossAuxiliaryDivisors hDpos hEpos ∈
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')) := by
    simp
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')))
    (f := crossAuxiliaryTotientWeight)
    hmem
  rw [crossAuxiliaryTotientWeight_one] at hsplit
  simpa [crossAuxiliaryTotientTail, add_comm] using hsplit.symm

/-- The full pinned auxiliary sum is its unit matrix plus the nontrivial
tail. -/
theorem sum_crossAuxiliaryS2GWeight_eq_one_add_tail
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    (∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryS2GWeight a) =
      1 + crossAuxiliaryS2GTail hDpos hEpos := by
  classical
  have hmem : oneCrossAuxiliaryDivisors hDpos hEpos ∈
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')) := by
    simp
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')))
    (f := crossAuxiliaryS2GWeight)
    hmem
  rw [crossAuxiliaryS2GWeight_one] at hsplit
  simpa [crossAuxiliaryS2GTail, add_comm] using hsplit.symm

/-- Every unpinned auxiliary weight is nonnegative. -/
theorem crossAuxiliaryTotientWeight_nonneg
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') :
    0 ≤ crossAuxiliaryTotientWeight a := by
  unfold crossAuxiliaryTotientWeight
  positivity

/-- Every pinned auxiliary weight is nonnegative. -/
theorem crossAuxiliaryS2GWeight_nonneg
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') :
    0 ≤ crossAuxiliaryS2GWeight a := by
  unfold crossAuxiliaryS2GWeight
  positivity

theorem crossAuxiliaryTotientTail_nonneg
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    0 ≤ crossAuxiliaryTotientTail hDpos hEpos := by
  unfold crossAuxiliaryTotientTail
  exact Finset.sum_nonneg fun a _ ↦ crossAuxiliaryTotientWeight_nonneg a

theorem crossAuxiliaryS2GTail_nonneg
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    0 ≤ crossAuxiliaryS2GTail hDpos hEpos := by
  unfold crossAuxiliaryS2GTail
  exact Finset.sum_nonneg fun a _ ↦ crossAuxiliaryS2GWeight_nonneg a

/-- Exact value of the nontrivial normalization tail. -/
theorem crossAuxiliaryTotientTail_eq_crossGcd_sub_one
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    crossAuxiliaryTotientTail hDpos hEpos =
      (crossCoordinateGcdProduct H d e d' e' : ℝ) - 1 := by
  have hsum := sum_crossAuxiliaryTotientWeight_eq_one_add_tail hDpos hEpos
  rw [← crossCoordinateTotientSumProduct_eq_auxiliarySum,
    crossCoordinateTotientSumProduct_eq_crossGcd] at hsum
  linarith

/-- In particular, a nontrivial normalization tail is bounded by the full
cross-gcd amplification. -/
theorem crossAuxiliaryTotientTail_le_crossGcd
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h)) :
    crossAuxiliaryTotientTail hDpos hEpos ≤
      (crossCoordinateGcdProduct H d e d' e' : ℝ) := by
  rw [crossAuxiliaryTotientTail_eq_crossGcd_sub_one hDpos hEpos]
  linarith

end

end Erdos4b
