/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.CoarseCyclicInverse
import ErdosProblems.Erdos360.DenseCoreCompletion
import ErdosProblems.Erdos360.AlmostPeriod

/-!
# Retaining the cyclic progression in the coarse inverse theorem

`HasLongProgressionCover` is the correct interface for the final sieve, but
it forgets the common cyclic direction needed by dyadic contraction.  In the
large-core-sumset branch the ternary dense-core completion retains that
direction and gives a single cyclic coset progression for the original set.
-/

namespace Erdos360

open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- In the sub-`3/2` core-doubling branch, Kneser's theorem makes the core
difference set a subgroup.  Ruzsa covering then places the original set in
at most two cosets of that subgroup, hence in a length-two cyclic coset
progression. -/
theorem dense_core_smallSumset_cyclicProgressionBound
    {t : ℕ} [NeZero t] {B C : Finset (ZMod t)}
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 2 * (C + C).card < 3 * C.card) :
    HasCyclicCosetProgressionBound B (3 * B.card) := by
  classical
  have hright : (C + C).card < 2 * C.card := by
    have hCpos : 0 < C.card := Finset.card_pos.mpr hC
    omega
  obtain ⟨H, c, hsumcos, hHcard⟩ :=
    small_sumset_stabilizer_coset hC hC hcore hright
  have hCcos : ContainedInAddCoset H C :=
    (summands_subset_cosets_of_sumset_subset_coset hC hC hsumcos).1
  have hHdense : 2 * Nat.card H < 3 * C.card := by
    rw [hHcard]
    exact hcore
  have hCC : C - C = subgroupFinset H :=
    dense_coset_sub_eq_subgroup hCcos hHdense
  obtain ⟨F, hFB, hFcard, hcover⟩ :=
    exists_two_translate_difference_cover hC hCB hdense hBsmall
  rw [hCC] at hcover
  have hB : B.Nonempty := hC.mono hCB
  have hF : F.Nonempty := by
    obtain ⟨x, hxB⟩ := hB
    obtain ⟨f, hfF, h, hhH, _⟩ := Finset.mem_add.mp (hcover hxB)
    exact ⟨f, hfF⟩
  let f₀ := hF.choose
  have hf₀ : f₀ ∈ F := hF.choose_spec
  let E := F.erase f₀
  have hEcard : E.card ≤ 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hf₀]
    omega
  let f₁ := if hE : E.Nonempty then hE.choose else f₀
  have hf_cases : ∀ f ∈ F, f = f₀ ∨ f = f₁ := by
    intro f hf
    by_cases hff₀ : f = f₀
    · exact Or.inl hff₀
    · right
      have hfE : f ∈ E := by simpa [E, hff₀] using hf
      by_cases hE : E.Nonempty
      · have hf₁E : f₁ ∈ E := by simpa [f₁, hE] using hE.choose_spec
        exact Finset.card_le_one.mp hEcard f hfE f₁ hf₁E
      · exact False.elim (hE ⟨f, hfE⟩)
  let d := f₁ - f₀
  have hBprog : B ⊆ cyclicCosetProgression H f₀ d 2 := by
    intro x hxB
    obtain ⟨f, hfF, h, hhH, hfx⟩ := Finset.mem_add.mp (hcover hxB)
    rcases hf_cases f hfF with rfl | rfl
    · apply mem_cyclicCosetProgression_iff.mpr
      refine ⟨0, by omega, ?_⟩
      rw [← hfx]
      simpa using hhH
    · apply mem_cyclicCosetProgression_iff.mpr
      refine ⟨1, by omega, ?_⟩
      have hbase : f₀ + d = f₁ := by simp [d]
      rw [← hfx]
      simpa [one_nsmul, hbase] using hhH
  refine ⟨H, f₀, d, 2, hBprog, ?_⟩
  calc
    2 * Nat.card H = 2 * (C + C).card := by rw [hHcard]
    _ < 3 * C.card := hcore
    _ ≤ 3 * B.card := Nat.mul_le_mul_left 3 (Finset.card_le_card hCB)

/-- A normalized affine product core whose double sumset has cardinality at
least `3|C|/2` puts the original cyclic set in one cyclic coset progression
of parameter mass at most `48|B|`.

This is the contraction-ready strengthening of
`normalized_affine_productCore_linear_cover`.  The latter deliberately
forgets the common cyclic direction when it lifts to ordinary integer
progressions; this theorem retains it. -/
theorem normalized_affine_productCore_cyclicProgressionBound
    {m g : ℕ} [NeZero g] [NeZero (m * g)]
    {B C D : Finset (ZMod (m * g))}
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hcore : 3 * C.card ≤ 2 * (C + C).card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m g D)).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m g D))
    (hAcard : 6 ≤
      (firstCoordinateSet (zmodQuotRemImage m g D)).card)
    (hgcd : (firstCoordinateSet (zmodQuotRemImage m g D)).gcd
      (fun n => (n : ℤ)) = 1)
    (hXsmall : 2 *
        (zmodQuotRemImage m g D + zmodQuotRemImage m g D).card <
      5 * (zmodQuotRemImage m g D).card) :
    HasCyclicCosetProgressionBound B (48 * B.card) := by
  classical
  let X := zmodQuotRemImage m g D
  let A := firstCoordinateSet X
  obtain ⟨base, hbase, H, u, v, _hbaseCos, _hHdense, _hbaseMax,
      _hAll, hmass, haffine⟩ :=
    exists_common_dense_coset_with_mass_bound_and_affine_labels
      X (by simpa [X, A] using hA) (by simpa [X, A] using hzero)
      (by simpa [X, A] using hAcard) (by simpa [X, A] using hgcd)
      (by simpa [X] using hXsmall)
  let L := A.max' (by simpa [X, A] using hA) + 1
  have hspan : 2 * A.max' (by simpa [X, A] using hA) < 3 * A.card := by
    simpa [X, A] using fiber_span_lt_three_halves X
      (by simpa [X, A] using hA) (by simpa [X, A] using hzero)
      (by simpa [X, A] using hAcard) (by simpa [X, A] using hgcd)
      (by simpa [X] using hXsmall)
  have hLle : L ≤ 2 * A.card := by
    dsimp only [L]
    omega
  have hLH : L * Nat.card H ≤
      8 * ((X + X).card - X.card) := by
    calc
      L * Nat.card H ≤ (2 * A.card) * Nat.card H :=
        Nat.mul_le_mul_right (Nat.card H) hLle
      _ = 2 * (A.card * Nat.card H) := by ring
      _ ≤ 2 * (4 * ((X + X).card - X.card)) :=
        Nat.mul_le_mul_left 2 (by simpa [X, A] using hmass)
      _ = 8 * ((X + X).card - X.card) := by ring
  have hdiff : (X + X).card - X.card ≤ 2 * X.card := by
    have hs := hXsmall
    change 2 * (X + X).card < 5 * X.card at hs
    omega
  have hXcard : X.card = C.card := by
    calc
      X.card = D.card := zmodQuotRemImage_card hm D
      _ = C.card := by
        rw [hDaff, zmodAffineImage_card w.isUnit]
  have hCleB : C.card ≤ B.card := Finset.card_le_card hCB
  have hLH_B : L * Nat.card H ≤ 16 * B.card := by
    calc
      L * Nat.card H ≤ 8 * ((X + X).card - X.card) := hLH
      _ ≤ 8 * (2 * X.card) := Nat.mul_le_mul_left 8 hdiff
      _ = 16 * C.card := by rw [hXcard]; ring
      _ ≤ 16 * B.card := Nat.mul_le_mul_left 16 hCleB

  let K := H.map (zmodQuotientEmbedding m g)
  have hrange : A ⊆ Finset.range L := by
    intro a ha
    exact Finset.mem_range.mpr (by
      have := A.le_max' a ha
      omega)
  have hDprog : D ⊆ cyclicCosetProgression K
      (zmodQuotientEmbedding m g v)
      ((1 : ZMod (m * g)) + zmodQuotientEmbedding m g u) L := by
    exact commonFiberCosets_pullback_cyclicCosetProgression D hrange
      (by simpa [X, A] using haffine)
  let e := unitMulAddEquiv w
  let K' := K.comap e.toAddMonoidHom
  have hCprog : C ⊆ cyclicCosetProgression K'
      (e.symm (zmodQuotientEmbedding m g v - c))
      (e.symm ((1 : ZMod (m * g)) + zmodQuotientEmbedding m g u)) L := by
    apply zmodAffineImage_pullback_cyclicCosetProgression w c
      (zmodQuotientEmbedding m g v)
      ((1 : ZMod (m * g)) + zmodQuotientEmbedding m g u) C K
    simpa [hDaff] using hDprog
  have hcardK : Nat.card K = Nat.card H :=
    natCard_map_zmodQuotientEmbedding hm H
  have hcardK' : Nat.card K' = Nat.card K :=
    natCard_comap_addEquiv e K
  have hmassK' : L * Nat.card K' ≤ 16 * B.card := by
    rw [hcardK', hcardK]
    exact hLH_B
  obtain ⟨a', hBprog, hmassB⟩ :=
    dense_core_cosetProgression_ternary_completion_mass
      hC hCB hdense hBsmall hcore hCprog hmassK'
  refine ⟨K', a',
    e.symm ((1 : ZMod (m * g)) + zmodQuotientEmbedding m g u),
    3 * L, hBprog, ?_⟩
  exact hmassB.trans_eq (by ring)

/-- Unconditional normalized high-support connector.  The large core
sumset branch uses affine fibre alignment and ternary completion, while the
small core sumset branch is already a two-coset Kneser configuration. -/
theorem normalized_affine_productCore_cyclicProgressionBound_all
    {m g : ℕ} [NeZero g] [NeZero (m * g)]
    {B C D : Finset (ZMod (m * g))}
    (w : (ZMod (m * g))ˣ) (c : ZMod (m * g))
    (hC : C.Nonempty) (hCB : C ⊆ B)
    (hdense : 33 * B.card ≤ 40 * C.card)
    (hBsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hDaff : D = zmodAffineImage c (w : ZMod (m * g)) C)
    (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m g D)).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m g D))
    (hAcard : 6 ≤
      (firstCoordinateSet (zmodQuotRemImage m g D)).card)
    (hgcd : (firstCoordinateSet (zmodQuotRemImage m g D)).gcd
      (fun n => (n : ℤ)) = 1)
    (hXsmall : 2 *
        (zmodQuotRemImage m g D + zmodQuotRemImage m g D).card <
      5 * (zmodQuotRemImage m g D).card) :
    HasCyclicCosetProgressionBound B (48 * B.card) := by
  by_cases hcore : 3 * C.card ≤ 2 * (C + C).card
  · exact normalized_affine_productCore_cyclicProgressionBound
      w c hC hCB hdense hBsmall hcore hDaff hm hA hzero hAcard hgcd hXsmall
  · have hsmallCore : 2 * (C + C).card < 3 * C.card :=
      Nat.lt_of_not_ge hcore
    obtain ⟨H, a, d, L, hsub, hmass⟩ :=
      dense_core_smallSumset_cyclicProgressionBound
        hC hCB hdense hBsmall hsmallCore
    exact ⟨H, a, d, L, hsub, hmass.trans (by omega)⟩

end Erdos360

#print axioms Erdos360.normalized_affine_productCore_cyclicProgressionBound
#print axioms Erdos360.normalized_affine_productCore_cyclicProgressionBound_all
