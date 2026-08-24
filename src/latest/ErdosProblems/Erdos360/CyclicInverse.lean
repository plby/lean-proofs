import ErdosProblems.Erdos360.FiberCoherence

open scoped Pointwise

namespace Erdos360

/-!
This scratch file records the part of the cyclic inverse theorem which is
already supported by the public `Erdos360` API.  The hypotheses isolate the
remaining quantitative affine-alignment statement: all quotient--remainder
fibres must lie in affine cosets of the *same controlled subgroup* which
contains a fibre of density greater than `2 / 3`.
-/

/-- The Fourier product core with the affine relation to the original dense
core retained.  The public `exists_dense_cyclic_smallProductCore` currently
drops this equality even though `exists_dense_cyclic_noCarryCore` already
proves it. -/
def castZModFinset {a b : ℕ} (h : a = b) (D : Finset (ZMod a)) :
    Finset (ZMod b) := h ▸ D

theorem exists_dense_cyclic_smallProductCore_affine
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ htg : t = m * g,
      ∃ w : (ZMod t)ˣ, ∃ c : ZMod t,
      ∃ C : Finset (ZMod t),
      ∃ D : Finset (ZMod t), ∃ X : Finset (ℕ × ZMod g),
        240 ≤ m ∧ C ⊆ B ∧
        33 * B.card ≤ 40 * C.card ∧
        D = zmodAffineImage c (w : ZMod t) C ∧ 0 ∈ D ∧
        D.card = C.card ∧
        X = zmodQuotRemImage m g (castZModFinset htg D) ∧
        X.card = D.card ∧ (X + X).card = (D + D).card ∧
        (0, 0) ∈ X ∧
        (∀ p ∈ X, p.1 < m) ∧
        2 * (X + X).card < 5 * X.card := by
  classical
  obtain ⟨m, g, w, c, C, D, htg, hm240, hCB, hCcard, hDaff,
      hDzero, hDcard, hDsum, hDhalf⟩ :=
    exists_dense_cyclic_noCarryCore B hB hsmall hsparse
  subst t
  have hm : 0 < m := by omega
  have hmg : 0 < m * g := NeZero.pos (m * g)
  have hg : 0 < g := Nat.pos_of_mul_pos_left hmg
  letI : NeZero g := ⟨hg.ne'⟩
  let X := zmodQuotRemImage m g D
  have hnowrap : ∀ x ∈ D, ∀ y ∈ D,
      x.val % m + y.val % m < m := by
    intro x hx y hy
    have hxx := hDhalf x hx
    have hyy := hDhalf y hy
    omega
  have hXcard : X.card = D.card := zmodQuotRemImage_card hm D
  have hXsum : (X + X).card = (D + D).card :=
    zmodQuotRemImage_add_card hm D hnowrap
  have hcoreSmall : 2 * (D + D).card < 5 * D.card := by
    have hCC : (C + C).card ≤ (B + B).card :=
      Finset.card_le_card (Finset.add_subset_add hCB hCB)
    have hsmall' : 25 * (C + C).card ≤ 51 * B.card :=
      (Nat.mul_le_mul_left 25 hCC).trans hsmall
    have h1 : 825 * (C + C).card ≤ 1683 * B.card := by
      nlinarith only [hsmall']
    have h2 : 1683 * B.card ≤ 2040 * C.card := by
      nlinarith only [hCcard]
    have hsumPos : 0 < (C + C).card := by
      have hCne : C.Nonempty := by
        apply Finset.card_pos.mp
        have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨0, hDzero⟩
        omega
      exact Finset.card_pos.mpr (hCne.add hCne)
    rw [hDsum, hDcard]
    by_contra hnot
    have h3 : 5 * C.card ≤ 2 * (C + C).card := Nat.le_of_not_gt hnot
    have h4 : 2040 * C.card ≤ 816 * (C + C).card := by
      nlinarith only [h3]
    omega
  refine ⟨m, g, rfl, w, c, C, D, X, hm240, hCB, hCcard, hDaff,
    hDzero, hDcard, rfl, hXcard, hXsum, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, hDzero, by simp [zmodQuotRemLift]⟩
  · intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mod_lt _ hm
  · rw [hXsum, hXcard]
    exact hcoreSmall

/-- Pull a cyclic progression of cosets through a unit-affine change of
coordinates.  This is the general-subgroup analogue of the existing
`zmodAffineImage_pullback_cyclic_bot`. -/
theorem zmodAffineImage_pullback_cyclicCosetProgression
    {t L : ℕ} [NeZero t] (w : (ZMod t)ˣ)
    (c a d : ZMod t) (B : Finset (ZMod t))
    (H : AddSubgroup (ZMod t))
    (hB : zmodAffineImage c (w : ZMod t) B ⊆
      cyclicCosetProgression H a d L) :
    let e := unitMulAddEquiv w
    let K := H.comap e.toAddMonoidHom
    B ⊆ cyclicCosetProgression K (e.symm (a - c)) (e.symm d) L := by
  classical
  dsimp only
  let e := unitMulAddEquiv w
  let K := H.comap e.toAddMonoidHom
  intro x hx
  have hxaff : c + (w : ZMod t) * x ∈
      zmodAffineImage c (w : ZMod t) B :=
    Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨i, hi, hxi⟩ :=
    mem_cyclicCosetProgression_iff.mp (hB hxaff)
  apply mem_cyclicCosetProgression_iff.mpr
  refine ⟨i, hi, ?_⟩
  change e (x - (e.symm (a - c) + i • e.symm d)) ∈ H
  simp only [map_sub, map_add, map_nsmul, AddEquiv.apply_symm_apply]
  change (w : ZMod t) * x - (a - c + i • d) ∈ H
  convert hxi using 1 <;> ring

/-- A subgroup and its inverse image under an additive equivalence have the
same finite cardinality. -/
lemma natCard_comap_addEquiv
    {G G' : Type*} [AddGroup G] [AddGroup G']
    (e : G ≃+ G') (H : AddSubgroup G') :
    Nat.card (H.comap e.toAddMonoidHom) = Nat.card H := by
  apply Nat.card_congr
  exact
    { toFun := fun x : H.comap e.toAddMonoidHom => ⟨e x, x.property⟩
      invFun := fun y : H => ⟨e.symm y, by
        change e (e.symm y) ∈ H
        simpa using y.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact e.symm_apply_apply x
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y }

/-- Pulling a structured affine image of a dense core back to the original
coordinates allows the existing two-translate completion lemma to cover the
whole cyclic set.  This deliberately records the current factor `48`; it is
the remaining quantitative loss in the small-subgroup branch. -/
theorem dense_affine_core_cosetProgression_longProgressionCover
    {t L : ℕ} [NeZero t]
    {B C D : Finset (ZMod t)} (w : (ZMod t)ˣ) (c : ZMod t)
    {H : AddSubgroup (ZMod t)} {a d : ZMod t}
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod t) C)
    (hDprog : D ⊆ cyclicCosetProgression H a d L)
    (hL : 0 < L) :
    HasLongProgressionCover (shiftedZmodValues B)
      (48 * (L * Nat.card H)) := by
  let e := unitMulAddEquiv w
  let K := H.comap e.toAddMonoidHom
  have hCprog : C ⊆
      cyclicCosetProgression K (e.symm (a - c)) (e.symm d) L := by
    apply zmodAffineImage_pullback_cyclicCosetProgression w c a d C H
    simpa [hDaff] using hDprog
  have hcover := dense_core_cosetProgression_longProgressionCover
    hC hCB hdense hsmall hCprog hL
  have hcardK : Nat.card K = Nat.card H := natCard_comap_addEquiv e H
  rwa [hcardK] at hcover

/-- End-to-end mechanical connector from affine product fibres to a cover of
the original cyclic set.  Thus, once controlled affine alignment is supplied,
the current public API reaches the original `B`; the resulting quantitative
constant is `48`. -/
theorem affine_productCore_to_original_longProgressionCover
    {m g : ℕ} [NeZero g] [NeZero (m * g)]
    {B C D : Finset (ZMod (m * g))}
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m g D)).Nonempty)
    (H : AddSubgroup (ZMod g)) (u v : ZMod g)
    (haffine : ∀ a ∈ firstCoordinateSet (zmodQuotRemImage m g D),
      ∀ y ∈ coordinateFiber (zmodQuotRemImage m g D) a,
        y - (a • u + v) ∈ H) :
    let L :=
      (firstCoordinateSet (zmodQuotRemImage m g D)).max' hA + 1
    HasLongProgressionCover (shiftedZmodValues B)
      (48 * (L * Nat.card H)) := by
  classical
  let A := firstCoordinateSet (zmodQuotRemImage m g D)
  let L := A.max' hA + 1
  let K := H.map (zmodQuotientEmbedding m g)
  have hrange : A ⊆ Finset.range L := by
    intro a ha
    exact Finset.mem_range.mpr (by
      have := A.le_max' a ha
      omega)
  have hDprog : D ⊆ cyclicCosetProgression K
      (zmodQuotientEmbedding m g v)
      ((1 : ZMod (m * g)) + zmodQuotientEmbedding m g u) L :=
    commonFiberCosets_pullback_cyclicCosetProgression D hrange haffine
  have hL : 0 < L := by simp [L]
  have hcover := dense_affine_core_cosetProgression_longProgressionCover
    w c hC hCB hdense hsmall hDaff hDprog hL
  have hcardK : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  rwa [hcardK] at hcover

/-- A controlled affine family of quotient--remainder fibres pulls back to
one cyclic coset progression.  It always has the currently available
constant-six long-progression cover.  In the large-subgroup branch the dense
fibre and Ruzsa covering give the sharp mass bound needed by CFP. -/
theorem affine_dense_productCore_cover
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m d D)).Nonempty)
    {base : ℕ} (hbase :
      base ∈ firstCoordinateSet (zmodQuotRemImage m d D))
    (H : AddSubgroup (ZMod d)) (u v : ZMod d)
    (hbaseCos : ContainedInAddCoset H
      (coordinateFiber (zmodQuotRemImage m d D) base))
    (hbaseDense : 2 * Nat.card H <
      3 * (coordinateFiber (zmodQuotRemImage m d D) base).card)
    (haffine : ∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
      ∀ y ∈ coordinateFiber (zmodQuotRemImage m d D) a,
        y - (a • u + v) ∈ H) :
    let L :=
      (firstCoordinateSet (zmodQuotRemImage m d D)).max' hA + 1
    let K := H.map (zmodQuotientEmbedding m d)
    D ⊆ cyclicCosetProgression K (zmodQuotientEmbedding m d v)
        ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) L ∧
      HasLongProgressionCover (shiftedZmodValues D)
        (6 * (L * Nat.card H)) ∧
      (D.card ≤ (Nat.card H) ^ 3 →
        ∃ mass : ℕ, 2 * mass < 3 * (D + D).card ∧
          HasLongProgressionCover (shiftedZmodValues D) mass) := by
  classical
  let A := firstCoordinateSet (zmodQuotRemImage m d D)
  let L := A.max' hA + 1
  let K := H.map (zmodQuotientEmbedding m d)
  have hrange : A ⊆ Finset.range L := by
    intro a ha
    exact Finset.mem_range.mpr (by
      have := A.le_max' a ha
      omega)
  have hDprog : D ⊆ cyclicCosetProgression K
      (zmodQuotientEmbedding m d v)
      ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u) L := by
    exact commonFiberCosets_pullback_cyclicCosetProgression D hrange haffine
  have hL : 0 < L := by simp [L]
  have hmg : 0 < m * d := NeZero.pos (m * d)
  have hb : 0 < m * d := hmg
  obtain ⟨q, hq, hqmd, hKdiv, hKmult⟩ := exists_generator_modulus hb K
  have hcoverP := cyclicCosetProgression_shifted_longProgressionCover_parametric
    hb hq hqmd hL K hKdiv hKmult (zmodQuotientEmbedding m d v)
      ((1 : ZMod (m * d)) + zmodQuotientEmbedding m d u)
  have hcardK : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  have hcoverD : HasLongProgressionCover (shiftedZmodValues D)
      (6 * (L * Nat.card H)) := by
    have hsub := shiftedZmodValues_mono hDprog
    have := hcoverP.mono_set hsub
    rwa [hcardK] at this
  refine ⟨hDprog, hcoverD, ?_⟩
  intro hlarge
  let C := cyclicRemainderFiber D base
  have hC : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcardZero :
        (coordinateFiber (zmodQuotRemImage m d D) base).card = 0 := by
      rw [← card_cyclicRemainderFiber hm D base]
      simpa [C] using congrArg Finset.card hEmpty
    exact (Finset.card_pos.mpr (coordinateFiber_nonempty_iff.mpr hbase)).ne'
      hcardZero
  have hCD : C ⊆ D := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hKcos : ContainedInAddCoset K C :=
    cyclicRemainderFiber_containedIn_map D base H hbaseCos
  have hKdense : 2 * Nat.card K < 3 * C.card := by
    rw [hcardK, card_cyclicRemainderFiber hm D base]
    exact hbaseDense
  have hKlarge : D.card ≤ (Nat.card K) ^ 3 := by
    rwa [hcardK]
  exact dense_coset_large_subgroup_cover hC hCD hKcos hKdense hKlarge

end Erdos360
