/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnPositiveVolume
import ErdosProblems.Erdos186.DiscreteJohnSection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Completing the positive-radius directions in a full lattice section

For a full active lattice section, the certificate directions whose
shrunken radii are positive can be extended, inside the lattice points of
the body, to a real basis.  Scaling precisely the original directions by
their shrunken radii gives a full-dimensional integral crosspolytope.  Its
determinant controls the product of `max 1 q_i`, which is the missing
mixed-radius input in the continuous discrete-John volume estimate.
-/

namespace Erdos186
namespace DiscreteJohn

open scoped BigOperators ENNReal
open Module CFP.Bilu.Mahler CFP.Bilu.MinkowskiSecond
open RankReduction

variable {d factor : ℕ}

/-- Full intrinsic lattice rank means that the embedded displayed lattice
points span the ambient real coordinate space. -/
theorem span_integralEmbed_points_eq_top_of_sectionRank_eq
    (points : Finset (LatticePoint d))
    (hrank : sectionRank points = d) :
    Submodule.span ℝ
        (integralEmbed '' (points : Set (LatticePoint d))) = ⊤ := by
  let P : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ
      (integralEmbed '' (points : Set (LatticePoint d)))
  have hLI := sectionSteps_realLinearIndependent points
  have hcard : Fintype.card (Fin (sectionRank points)) =
      Module.finrank ℝ (Fin d → ℝ) := by
    simp [hrank]
  have hspanSteps : Submodule.span ℝ
      (Set.range (fun i ↦ integralEmbed (sectionSteps points i))) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' hcard
  apply top_unique
  rw [← hspanSteps]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact sectionStep_mem_realSpan_points points i

/-- If a shrunken radius is positive, the corresponding unscaled step is
already a point of the inner GAP. -/
theorem step_mem_points_of_shrunkenRadius_pos
    {points : Finset (LatticePoint d)}
    (C : Certificate points d factor) (i : Fin d)
    (hi : 0 < C.radii i / factor) : C.steps i ∈ points := by
  let radii := shrinkRadii factor C.radii
  let c : Fin d → ℤ := Pi.single i 1
  have hc : ∀ j, -(radii j : ℤ) ≤ c j ∧ c j ≤ (radii j : ℤ) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [c, Pi.single_eq_same]
      have hr : (1 : ℤ) ≤ (radii i : ℤ) := by
        exact_mod_cast hi
      omega
    · have hij : i ≠ j := Ne.symm hji
      simp only [c, Pi.single_apply, hij, if_false]
      have hr : (0 : ℤ) ≤ (radii j : ℤ) := Int.natCast_nonneg _
      omega
  have hmem : integerCombination C.steps c ∈ C.inner.carrier :=
    integerCombination_mem_symmetricGAP C.steps radii c hc
  have hpoint := C.inner_carrier_subset hmem
  have hcomb : integerCombination C.steps c = C.steps i := by
    funext k
    classical
    rw [show integerCombination C.steps c k =
      ∑ j, c j * C.steps j k by rfl]
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro j _hj hji
      simp [c, Ne.symm hji]
    · simp
  rwa [hcomb] at hpoint

/-- In full active rank, complete the positive shrunken-radius steps by
lattice points of the body.  The returned scale product is exactly the
product of `max 1 q_i`, including the zero-radius coordinates at unit cost. -/
theorem exists_mixedRadius_integralCrosspolytope
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hrank : sectionRank points = d) :
    ∃ (a : Fin d → ℝ) (v : Fin d → LatticePoint d),
      LinearIndependent ℝ (fun i ↦ integralEmbed (v i)) ∧
      (∀ i, a i • integralEmbed (v i) ∈ K) ∧
      (∏ i, (((max 1 (C.radii i / factor)) : ℕ) : ℝ)) =
        ∏ i, |a i| := by
  classical
  let q : Fin d → ℕ := fun i ↦ C.radii i / factor
  let Active := {i : Fin d // 0 < q i}
  let u : Active → (Fin d → ℝ) :=
    fun i ↦ integralEmbed (C.steps i.1)
  have hsteps := realLinearIndependent_of_integerIndependent C.steps C.independent
  have hu : LinearIndependent ℝ u := by
    exact hsteps.comp (fun i : Active ↦ i.1) Subtype.val_injective
  let s : Set (Fin d → ℝ) := Set.range u
  let t : Set (Fin d → ℝ) :=
    integralEmbed '' (points : Set (LatticePoint d))
  have hst : s ⊆ t := by
    rintro _ ⟨i, rfl⟩
    refine ⟨C.steps i.1, ?_, rfl⟩
    exact step_mem_points_of_shrunkenRadius_pos C i.1 i.2
  have hs : LinearIndepOn ℝ id s := hu.linearIndepOn_id
  obtain ⟨b, hbt, hsb, htb, hlib⟩ :=
    exists_linearIndepOn_id_extension hs hst
  have htspan : Submodule.span ℝ t = ⊤ := by
    exact span_integralEmbed_points_eq_top_of_sectionRank_eq points hrank
  have hbspan : Submodule.span ℝ b = ⊤ := by
    apply top_unique
    rw [← htspan]
    exact Submodule.span_le.mpr htb
  have hbLI : LinearIndependent ℝ ((↑) : b → (Fin d → ℝ)) :=
    hlib.linearIndependent
  let bBasis : Basis b ℝ (Fin d → ℝ) :=
    Basis.mk hbLI (by
      rw [show Set.range ((↑) : b → (Fin d → ℝ)) = b by
        ext x
        simp]
      exact hbspan.ge)
  let Comp := (b \ s : Set (Fin d → ℝ))
  let es : Active ≃ s := Equiv.ofInjective u hu.injective
  let eSum : Active ⊕ Comp ≃ b :=
    (Equiv.sumCongr es (Equiv.refl Comp)).trans
      (Equiv.Set.sumDiffSubset hsb)
  have hcompImage (x : Comp) : x.1 ∈ t := hbt x.2.1
  have hcompExists (x : Comp) :
      ∃ z : LatticePoint d, z ∈ points ∧ integralEmbed z = x.1 := by
    have hx := hcompImage x
    change x.1 ∈ integralEmbed '' (points : Set (LatticePoint d)) at hx
    rcases hx with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  let compPoint : Comp → LatticePoint d :=
    fun x ↦ Classical.choose (hcompExists x)
  have hcompPoint_mem (x : Comp) : compPoint x ∈ points :=
    (Classical.choose_spec (hcompExists x)).1
  have hcompPoint_embed (x : Comp) : integralEmbed (compPoint x) = x.1 :=
    (Classical.choose_spec (hcompExists x)).2
  let J := Active ⊕ Comp
  let vJ : J → LatticePoint d := Sum.elim
    (fun i : Active ↦ C.steps i.1) compPoint
  let aJ : J → ℝ := Sum.elim
    (fun i : Active ↦ (q i.1 : ℝ)) (fun _ : Comp ↦ 1)
  have heSum_inl (i : Active) : (eSum (Sum.inl i) : Fin d → ℝ) = u i := by
    change ((Equiv.Set.sumDiffSubset hsb) (Sum.inl (es i)) : b).1 = u i
    rw [Equiv.Set.sumDiffSubset_apply_inl]
    rfl
  have heSum_inr (x : Comp) : (eSum (Sum.inr x) : Fin d → ℝ) = x.1 := by
    change ((Equiv.Set.sumDiffSubset hsb) (Sum.inr x) : b).1 = x.1
    rw [Equiv.Set.sumDiffSubset_apply_inr]
  have hvJ : (fun j ↦ integralEmbed (vJ j)) =
      fun j ↦ (eSum j : Fin d → ℝ) := by
    funext j
    cases j with
    | inl i => simpa [vJ, u] using (heSum_inl i).symm
    | inr x => simpa [vJ, hcompPoint_embed] using (heSum_inr x).symm
  have hLIJ : LinearIndependent ℝ (fun j ↦ integralEmbed (vJ j)) := by
    rw [hvJ]
    exact hbLI.comp eSum eSum.injective
  have hgenJ : ∀ j, aJ j • integralEmbed (vJ j) ∈ K := by
    intro j
    cases j with
    | inl i =>
        simpa [aJ, vJ, q] using shrunkenStep_mem_body C hpoints i.1
    | inr x =>
        simpa [aJ, vJ] using (hpoints (compPoint x)).mp (hcompPoint_mem x)
  letI : Finite J := Module.Finite.finite_basis (bBasis.reindex eSum.symm)
  letI : Finite Comp :=
    Finite.of_injective (fun x : Comp ↦ (Sum.inr x : J)) Sum.inr_injective
  letI : Fintype Comp := Fintype.ofFinite Comp
  have hcardJ : Fintype.card J = d := by
    rw [← Module.finrank_eq_card_basis (bBasis.reindex eSum.symm)]
    simp
  let e : Fin d ≃ J := Fintype.equivOfCardEq (by simpa using hcardJ.symm)
  let v : Fin d → LatticePoint d := vJ ∘ e
  let a : Fin d → ℝ := aJ ∘ e
  refine ⟨a, v, hLIJ.comp e e.injective, fun i ↦ hgenJ (e i), ?_⟩
  have hprodJ : (∏ j : J, |aJ j|) = ∏ i : Active, (q i.1 : ℝ) := by
    dsimp only [J, aJ]
    rw [Fintype.prod_sum_type
      (fun j : Active ⊕ Comp ↦
        |Sum.elim (fun i : Active ↦ (q i.1 : ℝ))
          (fun _ : Comp ↦ 1) j|)]
    simp only [Sum.elim_inl, Sum.elim_inr, abs_one,
      Finset.prod_const_one, mul_one]
    apply Finset.prod_congr rfl
    intro i _hi
    exact abs_of_nonneg (Nat.cast_nonneg _)
  have hprodActive :
      (∏ i : Fin d, (((max 1 (q i)) : ℕ) : ℝ)) =
        ∏ i : Active, (q i.1 : ℝ) := by
    let A : Finset (Fin d) := Finset.univ.filter fun i ↦ 0 < q i
    calc
      (∏ i : Fin d, (((max 1 (q i)) : ℕ) : ℝ)) =
          ∏ i : Fin d, if 0 < q i then (q i : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : 0 < q i
        · rw [if_pos hi, Nat.max_eq_right (Nat.succ_le_iff.mpr hi)]
        · have hq : q i = 0 := Nat.eq_zero_of_not_pos hi
          simp [hi, hq]
      _ = ∏ i ∈ A, (q i : ℝ) := by
        simpa [A] using
          (Finset.prod_filter (s := Finset.univ)
            (fun i : Fin d ↦ 0 < q i) (fun i ↦ (q i : ℝ))).symm
      _ = ∏ i : Active, (q i.1 : ℝ) := by
        exact Finset.prod_subtype A (by simp [A, Active]) (fun i ↦ (q i : ℝ))
  calc
    (∏ i : Fin d, (((max 1 (C.radii i / factor)) : ℕ) : ℝ)) =
        ∏ i : Fin d, (((max 1 (q i)) : ℕ) : ℝ) := by rfl
    _ = ∏ j : J, |aJ j| := hprodActive.trans hprodJ.symm
    _ = ∏ i : Fin d, |a i| := by
      simpa [a] using (e.prod_comp fun j ↦ |aJ j|).symm

/-- The mixed-radius crosspolytope gives the exact lower volume bound needed
to control the discrete inner width product, with zero radii charged by one. -/
theorem mixedRadius_product_volume_le
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hrank : sectionRank points = d) (hd : 0 < d) :
    ENNReal.ofReal
        (∏ i, (((max 1 (C.radii i / factor)) : ℕ) : ℝ)) *
        ENNReal.ofReal ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
      MeasureTheory.volume K := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨a, v, hv, hgen, hprod⟩ :=
    exists_mixedRadius_integralCrosspolytope C hpoints hrank
  rw [hprod]
  have hlower := volume_image_l1UnitBall_scaledRealColumns_lower a v hv
  exact hlower.trans (MeasureTheory.measure_mono
    (scaledCrosspolytope_subset_balancedConvex a v
      hbalanced hconvex hgen hd))

/-- The inner symmetric progression has at most a factor `3^d` more
coefficient tuples than the product in which every zero shrunken radius is
charged by one. -/
theorem inner_volume_le_three_pow_mul_mixedProduct
    {points : Finset (LatticePoint d)}
    (C : Certificate points d factor) :
    C.inner.volume ≤ 3 ^ d *
      ∏ i, max 1 (C.radii i / factor) := by
  rw [Certificate.inner, symmetricGAP_volume]
  calc
    (∏ i, (2 * (C.radii i / factor) + 1)) ≤
        ∏ i, (3 * max 1 (C.radii i / factor)) := by
      apply Finset.prod_le_prod
      · exact fun _ _ ↦ Nat.zero_le _
      · intro i _
        by_cases hi : C.radii i / factor = 0
        · simp [hi]
        · have hpos : 0 < C.radii i / factor := Nat.pos_of_ne_zero hi
          rw [Nat.max_eq_right (Nat.succ_le_iff.mpr hpos)]
          omega
    _ = (∏ _i : Fin d, 3) *
        ∏ i, max 1 (C.radii i / factor) :=
      Finset.prod_mul_distrib
    _ = 3 ^ d * ∏ i, max 1 (C.radii i / factor) := by simp

/-- In effective full rank, the outer coefficient-box volume is controlled
by the real volume of the symmetric body.  Zero shrunken radii are handled
by completing their directions with integral body points, so this estimate
does not require every inner radius to be positive. -/
theorem outer_volume_le_factorBound_mul_volumeReal
    {points : Finset (LatticePoint d)} {K : Set (Fin d → ℝ)}
    (C : Certificate points d factor)
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hbounded : Bornology.IsVonNBounded ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hrank : sectionRank points = d) (hd : 0 < d)
    {factorBound : ℕ} (hfactor : factor ≤ factorBound) :
    (C.outer.volume : ℝ) ≤
      ((((2 * factorBound + 1) ^ d * 3 ^ d * d.factorial : ℕ) : ℝ)) *
        MeasureTheory.volume.real K := by
  let Q : ℕ := ∏ i, max 1 (C.radii i / factor)
  have hbase : 2 * factor + 1 ≤ 2 * factorBound + 1 := by omega
  have hpow : (2 * factor + 1) ^ d ≤
      (2 * factorBound + 1) ^ d := Nat.pow_le_pow_left hbase d
  have houterNat : C.outer.volume ≤
      ((2 * factorBound + 1) ^ d * 3 ^ d) * Q := by
    calc
      C.outer.volume ≤ (2 * factor + 1) ^ d * C.inner.volume :=
        C.outer_volume_le
      _ ≤ (2 * factor + 1) ^ d * (3 ^ d * Q) := by
        exact Nat.mul_le_mul_left _
          (by simpa [Q] using inner_volume_le_three_pow_mul_mixedProduct C)
      _ ≤ (2 * factorBound + 1) ^ d * (3 ^ d * Q) := by
        exact Nat.mul_le_mul_right _ hpow
      _ = ((2 * factorBound + 1) ^ d * 3 ^ d) * Q := by ring
  have houterReal : (C.outer.volume : ℝ) ≤
      ((((2 * factorBound + 1) ^ d * 3 ^ d : ℕ) : ℝ)) * (Q : ℝ) := by
    exact_mod_cast houterNat
  have hmix := mixedRadius_product_volume_le C hbalanced hconvex hpoints hrank hd
  have hcastQ : (Q : ℝ) =
      ∏ i, (((max 1 (C.radii i / factor)) : ℕ) : ℝ) := by
    simp only [Q, Nat.cast_prod]
  rw [← hcastQ] at hmix
  have hbody_ne_top : MeasureTheory.volume K ≠ ∞ :=
    ((NormedSpace.isVonNBounded_iff ℝ).mp hbounded).measure_lt_top.ne
  have hmixReal := ENNReal.toReal_mono hbody_ne_top hmix
  have hQnonneg : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hgeomNonneg : (0 : ℝ) ≤
      (2 : ℝ) ^ d / (d.factorial : ℝ) := by positivity
  have hmixReal' :
      (Q : ℝ) * ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
        MeasureTheory.volume.real K := by
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hQnonneg, ENNReal.toReal_ofReal hgeomNonneg,
      Nat.cast_prod] using hmixReal
  have hfac : (0 : ℝ) < d.factorial := by positivity
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hweak : (Q : ℝ) / (d.factorial : ℝ) ≤
      MeasureTheory.volume.real K := by
    calc
      (Q : ℝ) / (d.factorial : ℝ) =
          (Q : ℝ) * (1 / (d.factorial : ℝ)) := by ring
      _ ≤ (Q : ℝ) * ((2 : ℝ) ^ d / (d.factorial : ℝ)) := by
        gcongr
      _ ≤ MeasureTheory.volume.real K := hmixReal'
  have hQ : (Q : ℝ) ≤
      MeasureTheory.volume.real K * (d.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp hweak
  calc
    (C.outer.volume : ℝ) ≤
        ((((2 * factorBound + 1) ^ d * 3 ^ d : ℕ) : ℝ)) * (Q : ℝ) :=
      houterReal
    _ ≤ ((((2 * factorBound + 1) ^ d * 3 ^ d : ℕ) : ℝ)) *
        (MeasureTheory.volume.real K * (d.factorial : ℝ)) := by
      gcongr
    _ = ((((2 * factorBound + 1) ^ d * 3 ^ d * d.factorial : ℕ) : ℝ)) *
        MeasureTheory.volume.real K := by
      push_cast
      ring

end DiscreteJohn
end Erdos186
