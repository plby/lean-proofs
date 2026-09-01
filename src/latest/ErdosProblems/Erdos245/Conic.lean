import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos245Scratch

def nzSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) : Finset ι :=
  Finset.univ.filter fun i ↦ a i ≠ 0

@[simp] lemma mem_nzSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (i : ι) : i ∈ nzSupport a ↔ a i ≠ 0 := by
  simp [nzSupport]

/-- A finite nonnegative rational linear combination can be chosen with
linearly independent nonzero support. -/
theorem exists_nonnegative_linearIndependent_support
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℚ V]
    (w : ι → V) (a : ι → ℚ) (ha : ∀ i, 0 ≤ a i) :
    ∃ b : ι → ℚ,
      (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = ∑ i, a i • w i ∧
      LinearIndependent ℚ (fun i : ↥(nzSupport b) ↦ w i.1) := by
  classical
  let target : V := ∑ i, a i • w i
  let Good : ℕ → Prop := fun n ↦
    ∃ b : ι → ℚ, (∀ i, 0 ≤ b i) ∧
      (∑ i, b i • w i) = target ∧ (nzSupport b).card = n
  have hGood : ∃ n, Good n := by
    refine ⟨(nzSupport a).card, a, ha, rfl, rfl⟩
  let n := Nat.find hGood
  obtain ⟨b, hb, hbsum, hbcard⟩ := Nat.find_spec hGood
  refine ⟨b, hb, by simpa [target] using hbsum, ?_⟩
  by_contra hdependent
  obtain ⟨g, hg, i₀, hi₀⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  let g' : ↥(nzSupport b) → ℚ :=
    if 0 < g i₀ then g else -g
  have hg'sum : ∑ i, g' i • w i.1 = 0 := by
    by_cases hpos : 0 < g i₀
    · simpa [g', hpos] using hg
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simpa [g', hpos] using congrArg Neg.neg hg
  have hi₀pos : 0 < g' i₀ := by
    by_cases hpos : 0 < g i₀
    · simp [g', hpos]
    · have hneg : g i₀ < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi₀
      simp [g', hpos, hneg]
  let P : Finset ↥(nzSupport b) := Finset.univ.filter fun i ↦ 0 < g' i
  have hP : P.Nonempty := by
    refine ⟨i₀, ?_⟩
    simp [P, hi₀pos]
  let R : Finset ℚ := P.image fun i ↦ b i.1 / g' i
  have hR : R.Nonempty := hP.image _
  let t : ℚ := R.min' hR
  obtain ⟨iMin, hiMinP, htEq⟩ := Finset.mem_image.mp (R.min'_mem hR)
  have hiMinG : 0 < g' iMin := (Finset.mem_filter.mp hiMinP).2
  have hiMinB : 0 < b iMin.1 := by
    have hne : b iMin.1 ≠ 0 := (mem_nzSupport b iMin.1).mp iMin.2
    exact lt_of_le_of_ne (hb iMin.1) (Ne.symm hne)
  have htpos : 0 < t := by
    change 0 < R.min' hR
    rw [← htEq]
    exact div_pos hiMinB hiMinG
  let gFull : ι → ℚ := fun i ↦
    if hi : i ∈ nzSupport b then g' ⟨i, hi⟩ else 0
  have hgFull : ∑ i, gFull i • w i = 0 := by
    calc
      ∑ i, gFull i • w i = ∑ i ∈ nzSupport b, gFull i • w i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hi
        have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
        simp [gFull, hbi]
      _ = ∑ i : ↥(nzSupport b), g' i • w i.1 := by
        rw [← (nzSupport b).sum_attach]
        apply Finset.sum_congr rfl
        intro i hi
        have hbi : b i.1 ≠ 0 := (mem_nzSupport b i.1).mp i.2
        simp [gFull, hbi]
      _ = 0 := hg'sum
  let b' : ι → ℚ := fun i ↦ b i - t * gFull i
  have hb' : ∀ i, 0 ≤ b' i := by
    intro i
    by_cases hi : i ∈ nzSupport b
    · let ii : ↥(nzSupport b) := ⟨i, hi⟩
      have hbi0 : b i ≠ 0 := (mem_nzSupport b i).mp hi
      by_cases hgpos : 0 < g' ii
      · have hiP : ii ∈ P := by simp [P, hgpos]
        have hratio : t ≤ b i / g' ii := by
          apply Finset.min'_le R
          exact Finset.mem_image.mpr ⟨ii, hiP, rfl⟩
        have hmul : t * g' ii ≤ b i :=
          (le_div_iff₀ hgpos).mp hratio
        simpa [b', gFull, hi, hbi0, ii] using sub_nonneg.mpr hmul
      · have hgle : g' ii ≤ 0 := le_of_not_gt hgpos
        have htg : t * g' ii ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hgle
        have : 0 ≤ b i - t * g' ii := sub_nonneg.mpr (htg.trans (hb i))
        simpa [b', gFull, hi, hbi0, ii] using this
    · have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
      simp [b', gFull, hbi]
  have hb'sum : (∑ i, b' i • w i) = ∑ i, b i • w i := by
    simp only [b', sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hgFull, smul_zero, sub_zero]
  have hsupport : nzSupport b' ⊆ nzSupport b := by
    intro i hi'
    by_contra hi
    have hbi : b i = 0 := not_ne_iff.mp (mt (mem_nzSupport b i).mpr hi)
    have hzero : b' i = 0 := by simp [b', gFull, hbi]
    exact (mem_nzSupport b' i).mp hi' hzero
  have hiMinZero : b' iMin.1 = 0 := by
    have ht : t = b iMin.1 / g' iMin := htEq.symm
    simp only [b', gFull, iMin.2, dite_true, ht]
    rw [div_mul_cancel₀ _ hiMinG.ne']
    exact sub_self _
  have hproper : nzSupport b' ⊂ nzSupport b := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsupport, ?_⟩
    intro heq
    have : iMin.1 ∈ nzSupport b' := by
      rw [heq]
      exact iMin.2
    exact (mem_nzSupport b' iMin.1).mp this hiMinZero
  have hcardlt : (nzSupport b').card < (nzSupport b).card :=
    Finset.card_lt_card hproper
  have hminimal : n ≤ (nzSupport b').card := by
    apply Nat.find_min' hGood
    refine ⟨b', hb', ?_, rfl⟩
    exact hb'sum.trans hbsum
  rw [hbcard] at hcardlt
  omega

/-- Columnwise bounds give the elementary Leibniz bound for an integer
determinant. -/
theorem natAbs_det_le_factorial_mul_prod
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (B : n → ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B j) :
    A.det.natAbs ≤ (Fintype.card n).factorial * ∏ j, B j := by
  have natAbs_prod (f : n → ℤ) :
      (∏ i, f i).natAbs = ∏ i, (f i).natAbs := by
    induction (Finset.univ : Finset n) using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx, Int.natAbs_mul, ih]
  rw [Matrix.det_apply']
  calc
    (∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i)).natAbs
        ≤ ∑ σ : Equiv.Perm n,
          (((Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i).natAbs) :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, ∏ i, B i := by
      apply Finset.sum_le_sum
      intro σ _hσ
      rw [Int.natAbs_mul, natAbs_prod (fun i ↦ A (σ i) i)]
      have hsign : ((Equiv.Perm.sign σ : ℤ)).natAbs = 1 := by simp
      rw [hsign, one_mul]
      exact Finset.prod_le_prod' fun i _hi ↦ hA (σ i) i
    _ = (Fintype.card n).factorial * ∏ i, B i := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
      rfl

def castVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℚ :=
  fun i ↦ z i

lemma castVec_injective {d : ℕ} :
    Function.Injective (@castVec d) := by
  intro x y h
  ext j
  have hj := congrFun h j
  change (x j : ℚ) = (y j : ℚ) at hj
  exact_mod_cast hj

@[simp] lemma castVec_apply {d : ℕ} (z : Fin d → ℤ) (i : Fin d) :
    castVec z i = (z i : ℚ) := rfl

/-- Cramer's-rule bound in the form needed for the coefficient chain.  The
independent integer vectors are extended using only standard basis vectors,
so a columnwise integral bound is preserved. -/
theorem coefficient_le_of_integral_linearIndependent
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → Fin d → ℤ) (v : Fin d → ℤ) (a : ι → ℚ) (i₀ : ι)
    (hli : LinearIndependent ℚ (fun i ↦ castVec (w i)))
    (hrel : castVec v = ∑ i, a i • castVec (w i))
    (B : Fin d → ℕ) (hB : ∀ j, 1 ≤ B j)
    (hw : ∀ i j, (w i j).natAbs ≤ B j)
    (hv : ∀ j, (v j).natAbs ≤ B j) :
    a i₀ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by
  classical
  let f : ι → (Fin d → ℚ) := fun i ↦ castVec (w i)
  let s : Set (Fin d → ℚ) := Set.range f
  let stdZ : Fin d → Fin d → ℤ := fun j ↦ Pi.single j 1
  let stdQ : Fin d → Fin d → ℚ := fun j ↦ castVec (stdZ j)
  let t : Set (Fin d → ℚ) := s ∪ Set.range stdQ
  have hs : LinearIndepOn ℚ id s := by
    exact hli.linearIndepOn_id
  have hst : s ⊆ t := Set.subset_union_left
  have ht : (⊤ : Submodule ℚ (Fin d → ℚ)) ≤ Submodule.span ℚ t := by
    rw [← (Pi.basisFun ℚ (Fin d)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    apply Set.mem_union_right
    refine ⟨j, ?_⟩
    ext k
    by_cases hjk : j = k
    · subst k
      simp [stdQ, stdZ, Pi.basisFun_apply]
    · simp [stdQ, stdZ, Pi.basisFun_apply, hjk]
  let basis : Module.Basis (hs.extend hst) ℚ (Fin d → ℚ) :=
    Module.Basis.extendLe hs hst ht
  let I := hs.extend hst
  let : Fintype I := Fintype.ofFinite I
  have hIntegral (i : I) :
      ∃ z : Fin d → ℤ, castVec z = basis i := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨j, hj⟩ := hi
      exact ⟨w j, by simpa [f, s] using hj⟩
    · obtain ⟨j, hj⟩ := hi
      exact ⟨stdZ j, by simpa [stdQ] using hj⟩
  choose bz hbz using hIntegral
  have hcard : Fintype.card I = d := by
    rw [← Module.finrank_eq_card_basis basis]
    simp
  let e : I ≃ Fin d := Fintype.equivOfCardEq (by simpa using hcard)
  let A : Matrix I I ℤ := fun i j ↦ bz i (e j)
  let AQ : Matrix I I ℚ := fun i j ↦ basis i (e j)
  have hAmap : A.map (Int.castRingHom ℚ) = AQ := by
    ext i j
    exact congrFun (hbz i) (e j)
  let E : (Fin d → ℚ) ≃ₗ[ℚ] (I → ℚ) :=
    LinearEquiv.piCongrLeft' ℚ (fun _ : Fin d ↦ ℚ) e.symm
  have hAQli : LinearIndependent ℚ (fun i ↦ AQ i) := by
    have hmap := basis.linearIndependent.map' E.toLinearMap (by simp [E])
    have heq : (fun i ↦ AQ i) = E ∘ basis := by
      funext i j
      rfl
    rw [heq]
    exact hmap
  have hAdetQ : AQ.det ≠ 0 := by
    have hunitA : IsUnit AQ :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hAQli
    exact ((Matrix.isUnit_iff_isUnit_det AQ).mp hunitA).ne_zero
  have hcast : (A.det : ℚ) = AQ.det :=
    (Int.cast_det A).trans (congrArg Matrix.det hAmap)
  have hAdet : A.det ≠ 0 := by
    intro hzero
    apply hAdetQ
    rw [← hcast, hzero]
    simp
  let ii : ι → I := fun i ↦
    ⟨f i, hs.subset_extend hst (Set.mem_range_self i)⟩
  let ic : I := ii i₀
  have hbasis_ii (i : ι) : basis (ii i) = f i := by
    exact Module.Basis.extendLe_apply_self hs hst ht (ii i)
  have hii_injective : Function.Injective ii := by
    intro i j hij
    apply hli.injective
    have := congrArg Subtype.val hij
    simpa [ii] using this
  have hrepr_w (i : ι) :
      basis.repr (castVec (w i)) ic = if i = i₀ then 1 else 0 := by
    rw [show castVec (w i) = basis (ii i) by simpa [f] using (hbasis_ii i).symm]
    rw [basis.repr_self_apply]
    by_cases hi : i = i₀
    · subst i
      simp [ic]
    · have hne : ii i ≠ ic := by
        simpa [ic] using fun h ↦ hi (hii_injective h)
      simp [hne, hi]
  have hrepr : basis.repr (castVec v) ic = a i₀ := by
    calc
      basis.repr (castVec v) ic =
          basis.repr (∑ i, a i • castVec (w i)) ic := by rw [hrel]
      _ = ∑ i, a i * basis.repr (castVec (w i)) ic := by simp
      _ = a i₀ := by simp [hrepr_w]
  have hbzBound (i j : I) : (bz i (e j)).natAbs ≤ B (e j) := by
    have hi : basis i ∈ t := by
      apply Module.Basis.extendLe_subset hs hst ht
      exact Set.mem_range_self i
    rcases hi with hi | hi
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = w k (e j) := by
        have := castVec_injective ((hbz i).trans hk.symm)
        exact congrFun this (e j)
      rw [heq]
      exact hw k (e j)
    · obtain ⟨k, hk⟩ := hi
      have heq : bz i (e j) = stdZ k (e j) := by
        have := castVec_injective ((hbz i).trans hk.symm)
        exact congrFun this (e j)
      rw [heq]
      by_cases hkj : k = e j
      · subst k
        simpa [stdZ] using hB (e j)
      · simp [stdZ, hkj]
  let vRow : I → ℤ := fun j ↦ v (e j)
  let Av : Matrix I I ℤ := A.updateRow ic vRow
  have hAvBound (i j : I) : (Av i j).natAbs ≤ B (e j) := by
    by_cases hi : i = ic
    · subst i
      simpa [Av, vRow, Matrix.updateRow_self] using hv (e j)
    · change ((A.updateRow ic vRow) i j).natAbs ≤ B (e j)
      rw [Matrix.updateRow_apply, if_neg hi]
      exact hbzBound i j
  have hAvdet : Av.det.natAbs ≤ d.factorial * ∏ j, B j := by
    have h := natAbs_det_le_factorial_mul_prod Av (fun j ↦ B (e j)) hAvBound
    rw [hcard] at h
    simpa only [Equiv.prod_comp e] using h
  have hvrow : (fun j : I ↦ (v (e j) : ℚ)) =
      ∑ i, (basis.repr (castVec v) i) • AQ i := by
    funext j
    have hsum := congrFun (basis.sum_repr (castVec v)) (e j)
    simpa [AQ] using hsum.symm
  have hAvmap : Av.map (Int.castRingHom ℚ) =
      AQ.updateRow ic (fun j ↦ (v (e j) : ℚ)) := by
    ext i j
    by_cases hi : i = ic
    · subst i
      simp [Av, vRow, Matrix.updateRow_self]
    · change ((A.updateRow ic vRow i j : ℤ) : ℚ) =
          AQ.updateRow ic (fun j ↦ (v (e j) : ℚ)) i j
      rw [Matrix.updateRow_apply, Matrix.updateRow_apply, if_neg hi, if_neg hi]
      change (bz i (e j) : ℚ) = basis i (e j)
      exact congrFun (hbz i) (e j)
  have hdetrel : (Av.det : ℚ) = a i₀ * (A.det : ℚ) := by
    calc
      (Av.det : ℚ) = (Av.map (Int.castRingHom ℚ)).det := Int.cast_det Av
      _ = (AQ.updateRow ic (fun j ↦ (v (e j) : ℚ))).det := by rw [hAvmap]
      _ = (AQ.updateRow ic
          (∑ i, (basis.repr (castVec v) i) • AQ i)).det := by rw [hvrow]
      _ = basis.repr (castVec v) ic * AQ.det := by
        simpa only [smul_eq_mul] using
          Matrix.det_updateRow_sum AQ ic (fun i ↦ basis.repr (castVec v) i)
      _ = a i₀ * (A.det : ℚ) := by
        rw [hrepr, ← hcast]
  have habs : |a i₀| * (A.det.natAbs : ℚ) = (Av.det.natAbs : ℚ) := by
    have := congrArg abs hdetrel
    simpa [abs_mul, mul_comm] using this.symm
  have hdetOne : 1 ≤ A.det.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hAdet)
  calc
    a i₀ ≤ |a i₀| := le_abs_self _
    _ ≤ |a i₀| * (A.det.natAbs : ℚ) := by
      have : (1 : ℚ) ≤ A.det.natAbs := by exact_mod_cast hdetOne
      nlinarith [abs_nonneg (a i₀)]
    _ = (Av.det.natAbs : ℚ) := habs
    _ ≤ ((d.factorial * ∏ j, B j : ℕ) : ℚ) := by exact_mod_cast hAvdet

end Erdos245Scratch
