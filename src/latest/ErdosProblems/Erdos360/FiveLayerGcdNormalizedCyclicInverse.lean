/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.GcdNormalizedCyclicInverse
import ErdosProblems.Erdos360.FiveLayerAffine

/-!
# Gcd-normalized cyclic inverse theorem for five layers

This is the five-point counterpart of the high-support theorem in
`GcdNormalizedCyclicInverse`.  It uses the sharp `12/5` core inequality and
the five-layer affine-coherence package.
-/

namespace Erdos360

open scoped Pointwise BigOperators

attribute [local instance] Classical.propDecidable

theorem gcd_normalized_affine_productCore_cyclicProgressionBound_five
    {m g : ℕ} [NeZero g] [NeZero (m * g)]
    {B C D : Finset (ZMod (m * g))}
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm : 0 < m) (hDzero : 0 ∈ D)
    (hAcard :
      (firstCoordinateSet (zmodQuotRemImage m g D)).card = 5)
    (hXsumD :
      (zmodQuotRemImage m g D + zmodQuotRemImage m g D).card =
        (D + D).card)
    (hXsmall : 5 *
        (zmodQuotRemImage m g D + zmodQuotRemImage m g D).card <
      12 * (zmodQuotRemImage m g D).card) :
    HasCyclicCosetProgressionBound B (48 * B.card) := by
  classical
  let X := zmodQuotRemImage m g D
  let A := firstCoordinateSet X
  let q := A.gcd (fun a : ℕ ↦ a)
  have hXzero : (0, 0) ∈ X := by
    exact Finset.mem_image.mpr
      ⟨0, hDzero, by simp [zmodQuotRemLift, X]⟩
  have hXne : X.Nonempty := ⟨(0, 0), hXzero⟩
  have hAzero : 0 ∈ A :=
    mem_firstCoordinateSet.mpr ⟨0, by simpa [A] using hXzero⟩
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hqzero
    have hallzero : ∀ a ∈ A, a = 0 :=
      Finset.gcd_eq_zero_iff.mp hqzero
    have hAsub : A ⊆ {0} := by
      intro a ha
      simpa [hallzero a ha]
    have hcard : A.card ≤ 1 := by
      simpa using Finset.card_le_card hAsub
    have : A.card = 5 := by simpa [A, X] using hAcard
    omega
  have hdiv : ∀ p ∈ X, q ∣ p.1 := by
    simpa [q, A] using gcd_dvd_firstCoordinate X
  let Y := normalizeFirstCoordinates q X
  have hYne : Y.Nonempty := by
    refine ⟨divideFirstCoordinate q (0, 0), ?_⟩
    exact Finset.mem_image.mpr ⟨(0, 0), hXzero, rfl⟩
  have hYfirst : (firstCoordinateSet Y).Nonempty := by
    obtain ⟨p, hp⟩ := hYne
    exact ⟨p.1, mem_firstCoordinateSet.mpr ⟨p.2, hp⟩⟩
  have hYzero : 0 ∈ firstCoordinateSet Y := by
    apply mem_firstCoordinateSet.mpr
    refine ⟨0, ?_⟩
    simpa [Y, normalizeFirstCoordinates, divideFirstCoordinate] using
      (Finset.mem_image.mpr ⟨(0, 0), hXzero, rfl⟩ :
        divideFirstCoordinate q (0, 0) ∈ normalizeFirstCoordinates q X)
  have hYcard : Y.card = X.card :=
    card_normalizeFirstCoordinates hqpos hdiv
  have hYsum : (Y + Y).card = (X + X).card :=
    card_normalizeFirstCoordinates_add hqpos hdiv hdiv
  have hYAcard : (firstCoordinateSet Y).card = 5 := by
    rw [card_firstCoordinateSet_normalizeFirstCoordinates hqpos hdiv]
    simpa [A, X] using hAcard
  have hYgcd :
      (firstCoordinateSet Y).gcd (fun a ↦ (a : ℤ)) = 1 := by
    simpa [Y, q, A] using
      intGcd_firstCoordinateSet_normalizeFirstCoordinates hXne hqpos
  have hYsmall : 5 * (Y + Y).card < 12 * Y.card := by
    rw [hYsum, hYcard]
    simpa [X] using hXsmall
  obtain ⟨base, hbase, H, u, v, _hbaseCos, _hHdense, hbaseMax,
      _hAll, hmass, haffine⟩ :=
    exists_common_dense_coset_with_mass_bound_and_affine_labels_five
      Y hYfirst hYzero hYAcard hYgcd hYsmall
  let S := firstCoordinateSet Y
  let L := S.max' hYfirst + 1
  have hspan : 2 * S.max' hYfirst < 3 * S.card := by
    exact fiber_span_lt_three_halves_five Y
      hYfirst hYzero hYAcard hYgcd hYsmall
  have hLle : L ≤ 2 * S.card := by
    dsimp only [L]
    omega
  have hLH : L * Nat.card H ≤
      8 * ((Y + Y).card - Y.card) := by
    calc
      L * Nat.card H ≤ (2 * S.card) * Nat.card H :=
        Nat.mul_le_mul_right (Nat.card H) hLle
      _ = 2 * (S.card * Nat.card H) := by ring
      _ ≤ 2 * (4 * ((Y + Y).card - Y.card)) :=
        Nat.mul_le_mul_left 2 (by simpa [S] using hmass)
      _ = 8 * ((Y + Y).card - Y.card) := by ring
  have hdiff : (Y + Y).card - Y.card ≤ 2 * Y.card := by
    omega
  have hXcard : X.card = C.card := by
    calc
      X.card = D.card := zmodQuotRemImage_card hm D
      _ = C.card := by
        rw [hDaff, zmodAffineImage_card w.isUnit]
  have hCleB : C.card ≤ B.card := Finset.card_le_card hCB
  have hLH_B : L * Nat.card H ≤ 16 * B.card := by
    calc
      L * Nat.card H ≤ 8 * ((Y + Y).card - Y.card) := hLH
      _ ≤ 8 * (2 * Y.card) := Nat.mul_le_mul_left 8 hdiff
      _ = 16 * X.card := by rw [hYcard]; ring
      _ = 16 * C.card := by rw [hXcard]
      _ ≤ 16 * B.card := Nat.mul_le_mul_left 16 hCleB
  have hcoreY : 3 * Y.card ≤ 2 * (Y + Y).card := by
    have hweighted := layerHall_weighted_fiber_lower Y
      hYfirst hYzero
      (by omega : 3 ≤ (firstCoordinateSet Y).card) hYgcd hbase
      (D := ∅) (by simp) (by simp) (by simp)
    have hYsumFib :
        Y.card = ∑ a ∈ S, (coordinateFiber Y a).card := by
      simpa [S] using card_eq_sum_card_coordinateFiber Y
    have hYle :
        Y.card ≤ S.card * (coordinateFiber Y base).card := by
      rw [hYsumFib]
      calc
        ∑ a ∈ S, (coordinateFiber Y a).card ≤
            ∑ _a ∈ S, (coordinateFiber Y base).card := by
          apply Finset.sum_le_sum
          intro a ha
          exact hbaseMax a (by simpa [S] using ha)
        _ = S.card * (coordinateFiber Y base).card := by simp
    have hcoeff : S.card ≤ 2 * (S.card - 2) := by
      have : S.card = 5 := by simpa [S] using hYAcard
      omega
    have hextra : Y.card ≤
        2 * ((S.card - 2) * (coordinateFiber Y base).card) := by
      calc
        Y.card ≤ S.card * (coordinateFiber Y base).card := hYle
        _ ≤ (2 * (S.card - 2)) * (coordinateFiber Y base).card :=
          Nat.mul_le_mul_right _ hcoeff
        _ = 2 * ((S.card - 2) *
            (coordinateFiber Y base).card) := by ring
    have hweighted' :
        (S.card - 2) * (coordinateFiber Y base).card + Y.card ≤
          (Y + Y).card := by
      simpa only [Finset.sum_empty, zero_add, add_zero] using
        (show ((firstCoordinateSet Y).card - 2) *
            (coordinateFiber Y base).card +
            ∑ a ∈ (∅ : Finset ℕ), (coordinateFiber Y a).card + Y.card ≤
              (Y + Y).card from hweighted)
    rw [show S = firstCoordinateSet Y by rfl] at hextra
    omega
  have hDsumC : (D + D).card = (C + C).card := by
    rw [hDaff]
    exact zmodAffineImage_add_card w.isUnit C
  have hYsumC : (Y + Y).card = (C + C).card := by
    exact hYsum.trans (hXsumD.trans hDsumC)
  have hYcardC : Y.card = C.card := hYcard.trans hXcard
  have hcoreC : 3 * C.card ≤ 2 * (C + C).card := by
    rw [← hYcardC, ← hYsumC]
    exact hcoreY
  let K := H.map (zmodQuotientEmbedding m g)
  have hDprog : D ⊆ cyclicCosetProgression K
      (zmodQuotientEmbedding m g v)
      ((q : ZMod (m * g)) + zmodQuotientEmbedding m g u) L := by
    apply zmodQuotRem_normalizedAffineFiber_subset_cyclicCosetProgression
      hqpos
    intro z hz
    have hzX : zmodQuotRemLift m g z ∈ X :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hqrem : q ∣ z.val % m := hdiv _ hzX
    have haX : z.val % m ∈ A :=
      mem_firstCoordinateSet.mpr ⟨(z.val / m : ZMod g), hzX⟩
    have haY : (z.val % m) / q ∈ S := by
      rw [show S = firstCoordinateSet Y by rfl,
        firstCoordinateSet_normalizeFirstCoordinates]
      exact Finset.mem_image.mpr
        ⟨z.val % m, by simpa [A] using haX, rfl⟩
    refine ⟨hqrem, ?_, ?_⟩
    · exact Nat.lt_add_one_iff.mpr (S.le_max' _ haY)
    · have hfiber : (z.val / m : ZMod g) ∈
          coordinateFiber Y ((z.val % m) / q) := by
        rw [coordinateFiber_normalizeFirstCoordinates hdiv haX]
        exact mem_coordinateFiber.mpr hzX
      exact haffine _ haY _ hfiber
  have hcardK : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  let e := unitMulAddEquiv w
  let K' := K.comap e.toAddMonoidHom
  have hCprog : C ⊆ cyclicCosetProgression K'
      (e.symm (zmodQuotientEmbedding m g v - c))
      (e.symm ((q : ZMod (m * g)) + zmodQuotientEmbedding m g u)) L := by
    apply zmodAffineImage_pullback_cyclicCosetProgression w c
      (zmodQuotientEmbedding m g v)
      ((q : ZMod (m * g)) + zmodQuotientEmbedding m g u) C K
    simpa [hDaff] using hDprog
  have hcardK' : Nat.card K' = Nat.card K :=
    natCard_comap_addEquiv e K
  have hmassK' : L * Nat.card K' ≤ 16 * B.card := by
    rw [hcardK', hcardK]
    exact hLH_B
  obtain ⟨a', hBprog, hmassB⟩ :=
    dense_core_cosetProgression_ternary_completion_mass
      (hC.mono hCB) hCB hdense hBsmall hcoreC hCprog hmassK'
  refine ⟨K', a',
    e.symm ((q : ZMod (m * g)) + zmodQuotientEmbedding m g u),
    3 * L, hBprog, ?_⟩
  exact hmassB.trans_eq (by ring)

end Erdos360

#print axioms Erdos360.gcd_normalized_affine_productCore_cyclicProgressionBound_five
