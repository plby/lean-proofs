/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredIdentification
import ErdosProblems.Erdos186.CFP.RandomPartition
import ErdosProblems.Erdos186.CFP.AdaptedHNF
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Polynomially many canonical random-partition obstacles

This file supplies the finite counting input in CFP Lemma 2.34.  The first
part codes every admissible weak-stability GAP by its rank, offset,
differences, and widths.  The hypotheses used by preprocessing make all of
these parameters finite: differences are bounded explicitly, widths are
bounded by the comparison-box volume, and the condition that zero belongs
to the GAP bounds its offset.
-/

namespace Erdos186.CFP.RandomPartition

open scoped BigOperators
open Stability
open Module

noncomputable section

/-- Integers in the symmetric interval `[-M,M]`, used as finite codes. -/
abbrev SymmetricIntCode (M : ℕ) :=
  {z : ℤ // z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)}

@[simp]
theorem card_symmetricIntCode (M : ℕ) :
    Fintype.card (SymmetricIntCode M) = 2 * M + 1 := by
  rw [Fintype.card_coe, Int.card_Icc]
  omega

/-- A fixed-rank envelope for all GAP presentations of rank at most `D`.
Inactive coordinates are padded by zero (and width one). -/
abbrev WeakGAPCode (D differenceBound volumeBound offsetBound : ℕ) :=
  Fin (D + 1) × SymmetricIntCode offsetBound ×
    (Fin D → SymmetricIntCode differenceBound) ×
      (Fin D → Fin volumeBound)

@[simp]
theorem card_weakGAPCode (D differenceBound volumeBound offsetBound : ℕ) :
    Fintype.card (WeakGAPCode D differenceBound volumeBound offsetBound) =
      (D + 1) * (2 * offsetBound + 1) *
        (2 * differenceBound + 1) ^ D * volumeBound ^ D := by
  simp only [WeakGAPCode, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, card_symmetricIntCode]
  ring

/-- Decode the fixed-rank envelope into a GAP.  The stored width is one less
than the actual positive width. -/
def decodeWeakGAPCode {D differenceBound volumeBound offsetBound : ℕ}
    (code : WeakGAPCode D differenceBound volumeBound offsetBound) :
    GAP 1 code.1.val where
  offset := fun _ ↦ code.2.1.1
  steps := fun i _ ↦
    code.2.2.1 (Fin.castLE (Nat.le_of_lt_succ code.1.isLt) i)
  widths := fun i ↦
    (code.2.2.2 (Fin.castLE (Nat.le_of_lt_succ code.1.isLt) i)).val + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

/-- In a positive finite product, each factor is at most the product. -/
theorem factor_le_fin_product {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) (i : Fin d) :
    w i ≤ ∏ j, w j := by
  classical
  exact Finset.single_le_prod' (fun j _ ↦ hw j) (Finset.mem_univ i)

/-- Every coefficient of a GAP coordinate is strictly below its displayed
volume. -/
theorem coord_val_lt_volume {d : ℕ} (P : GAP 1 d) (c : P.Coord)
    (i : Fin d) :
    (c i : ℕ) < P.volume := by
  have hwidth : P.widths i ≤ P.volume := by
    exact factor_le_fin_product P.width_pos i
  exact (c i).isLt.trans_le hwidth

/-- A zero-containing rank-`d` GAP with volume at most `V` and differences
at most `q` has offset bounded by `d * V * q`. -/
theorem abs_offset_le_rank_mul_volume_mul_differenceBound
    {d q V : ℕ} (P : GAP 1 d)
    (hsteps : HasDifferencesAtMost P q) (hvolume : P.volume ≤ V)
    (hzero : (0 : LatticePoint 1) ∈ P.carrier) :
    |P.offset 0| ≤ ((d * V * q : ℕ) : ℤ) := by
  obtain ⟨c, hc⟩ := GAP.mem_carrier_iff.mp hzero
  have hc0 := congrFun hc 0
  change P.offset 0 + ∑ i, ((c i : ℕ) : ℤ) * P.steps i 0 = 0 at hc0
  have hoffset : P.offset 0 = -∑ i, ((c i : ℕ) : ℤ) * P.steps i 0 := by
    linarith
  rw [hoffset, abs_neg]
  calc
    |∑ i, ((c i : ℕ) : ℤ) * P.steps i 0| ≤
        ∑ i, |((c i : ℕ) : ℤ) * P.steps i 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ((V : ℤ) * (q : ℤ)) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (c i : ℕ))]
      have hcV : ((c i : ℕ) : ℤ) ≤ (V : ℤ) := by
        exact_mod_cast (coord_val_lt_volume P c i).le.trans hvolume
      exact mul_le_mul hcV (hsteps i) (abs_nonneg _) (by positivity)
    _ = ((d * V * q : ℕ) : ℤ) := by simp [mul_assoc]

/-- Code an admissible presentation in the fixed-rank envelope. -/
def encodeWeakGAP {D d q V : ℕ} (hdD : d ≤ D) (P : GAP 1 d)
    (hsteps : HasDifferencesAtMost P q) (hvolume : P.volume ≤ V)
    (hzero : (0 : LatticePoint 1) ∈ P.carrier) (hV : 0 < V) :
    WeakGAPCode D q V (D * V * q) :=
  (⟨d, Nat.lt_succ_of_le hdD⟩,
    ⟨P.offset 0, by
      rw [Finset.mem_Icc]
      have h := abs_offset_le_rank_mul_volume_mul_differenceBound
        P hsteps hvolume hzero
      have hrank : d * V * q ≤ D * V * q := by
        exact Nat.mul_le_mul_right q (Nat.mul_le_mul_right V hdD)
      have hbound : |P.offset 0| ≤ ((D * V * q : ℕ) : ℤ) :=
        h.trans (by exact_mod_cast hrank)
      exact ⟨neg_le_of_abs_le hbound, le_of_abs_le hbound⟩⟩,
    (fun j ↦ if hj : j.val < d then
      ⟨P.steps ⟨j.val, hj⟩ 0, by
        rw [Finset.mem_Icc]
        have h := hsteps ⟨j.val, hj⟩
        exact ⟨neg_le_of_abs_le h, le_of_abs_le h⟩⟩
      else ⟨0, by simp⟩),
    (fun j ↦ if hj : j.val < d then
      ⟨P.widths ⟨j.val, hj⟩ - 1, by
        have hwV : P.widths ⟨j.val, hj⟩ ≤ V :=
          (factor_le_fin_product P.width_pos _).trans hvolume
        omega⟩
      else ⟨0, hV⟩))

/-- Decoding the code of an admissible GAP recovers its presentation. -/
theorem decode_encodeWeakGAP {D d q V : ℕ} (hdD : d ≤ D)
    (P : GAP 1 d) (hsteps : HasDifferencesAtMost P q)
    (hvolume : P.volume ≤ V) (hzero : (0 : LatticePoint 1) ∈ P.carrier)
    (hV : 0 < V) :
    decodeWeakGAPCode (encodeWeakGAP hdD P hsteps hvolume hzero hV) = P := by
  apply GAP.ext
  · funext j
    fin_cases j
    rfl
  · funext j i
    fin_cases i
    simp [decodeWeakGAPCode, encodeWeakGAP, Fin.castLE]
  · funext i
    simp [decodeWeakGAPCode, encodeWeakGAP, Fin.castLE]
    have := P.width_pos i
    omega

/-! ## The weak-trace count -/

/-- Rank chosen from the existential data stored in a canonical weak trace. -/
noncomputable def weakTraceRank {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {D q : ℕ} (w : WeakTraceIndex A box D q) : ℕ :=
  Classical.choose w.2

theorem weakTraceRank_pos {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {D q : ℕ} (w : WeakTraceIndex A box D q) :
    0 < weakTraceRank w :=
  (Classical.choose_spec w.2).1

theorem weakTraceRank_le {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {D q : ℕ} (w : WeakTraceIndex A box D q) :
    weakTraceRank w ≤ D :=
  (Classical.choose_spec w.2).2.1

/-- A representing GAP chosen for a canonical weak trace. -/
noncomputable def weakTraceGAP {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {D q : ℕ} (w : WeakTraceIndex A box D q) : GAP 1 (weakTraceRank w) :=
  Classical.choose (Classical.choose_spec w.2).2.2

theorem weakTraceGAP_spec {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d}
    {D q : ℕ} (w : WeakTraceIndex A box D q) :
    HasDifferencesAtMost (weakTraceGAP w) q ∧
      4 * (weakTraceGAP w).volume ≤
        3 * (box (weakTraceRank w)).volume ∧
      integerPoint 0 ∈ (weakTraceGAP w).carrier ∧
      w.1.1 = outsideGAP A (weakTraceGAP w) :=
  Classical.choose_spec (Classical.choose_spec w.2).2.2

/-- The displayed volume comparison bounds the representing GAP by any
uniform bound for the comparison boxes. -/
theorem weakTraceGAP_volume_le {A : Finset ℤ}
    {box : (d : ℕ) → GAP 1 d} {D q V : ℕ}
    (hbox : ∀ d, 0 < d → d ≤ D → (box d).volume ≤ V)
    (w : WeakTraceIndex A box D q) :
    (weakTraceGAP w).volume ≤ V := by
  have h := (weakTraceGAP_spec w).2.1.trans
    (Nat.mul_le_mul_left 3
      (hbox (weakTraceRank w) (weakTraceRank_pos w) (weakTraceRank_le w)))
  omega

theorem weakTraceGAP_zero_mem {A : Finset ℤ}
    {box : (d : ℕ) → GAP 1 d} {D q : ℕ}
    (w : WeakTraceIndex A box D q) :
    (0 : LatticePoint 1) ∈ (weakTraceGAP w).carrier := by
  have hzero : integerPoint 0 = (0 : LatticePoint 1) := by
    ext i
    simp [integerPoint, BoundingBox.intPoint]
  have hz := (weakTraceGAP_spec w).2.2.1
  rwa [hzero] at hz

/-- The bounded code canonically assigned to a weak trace. -/
noncomputable def codeOfWeakTrace {A : Finset ℤ}
    {box : (d : ℕ) → GAP 1 d} {D q V : ℕ}
    (hbox : ∀ d, 0 < d → d ≤ D → (box d).volume ≤ V)
    (hV : 0 < V) (w : WeakTraceIndex A box D q) :
    WeakGAPCode D q V (D * V * q) :=
  encodeWeakGAP (weakTraceRank_le w) (weakTraceGAP w)
    (weakTraceGAP_spec w).1 (weakTraceGAP_volume_le hbox w)
    (weakTraceGAP_zero_mem w) hV

theorem outsideGAP_decode_codeOfWeakTrace {A : Finset ℤ}
    {box : (d : ℕ) → GAP 1 d} {D q V : ℕ}
    (hbox : ∀ d, 0 < d → d ≤ D → (box d).volume ≤ V)
    (hV : 0 < V) (w : WeakTraceIndex A box D q) :
    outsideGAP A (decodeWeakGAPCode (codeOfWeakTrace hbox hV w)) = w.1.1 := by
  rw [codeOfWeakTrace, decode_encodeWeakGAP]
  exact (weakTraceGAP_spec w).2.2.2.symm

/-- Explicit finite bound for all admissible weak-box traces. -/
theorem card_weakTraceIndex_le_code
    {A : Finset ℤ} {box : (d : ℕ) → GAP 1 d} {D q V : ℕ}
    (hbox : ∀ d, 0 < d → d ≤ D → (box d).volume ≤ V)
    (hV : 0 < V) :
    Fintype.card (WeakTraceIndex A box D q) ≤
      (D + 1) * (2 * (D * V * q) + 1) *
        (2 * q + 1) ^ D * V ^ D := by
  let f : WeakTraceIndex A box D q → WeakGAPCode D q V (D * V * q) :=
    codeOfWeakTrace hbox hV
  have hf : Function.Injective f := by
    intro u v huv
    change codeOfWeakTrace hbox hV u = codeOfWeakTrace hbox hV v at huv
    apply Subtype.ext
    apply Subtype.ext
    rw [← outsideGAP_decode_codeOfWeakTrace hbox hV u,
      ← outsideGAP_decode_codeOfWeakTrace hbox hV v, huv]
  rw [← card_weakGAPCode]
  exact Fintype.card_le_of_injective f hf

/-! ## Full-rank subgroup codes -/

/-- A bounded square matrix.  It is the finite code used for the canonical
Hermite basis of a superlattice of `q ℤ^k`. -/
abbrev BoundedMatrixCode (k q : ℕ) := Fin k → Fin k → Fin (q + 1)

@[simp]
theorem card_boundedMatrixCode (k q : ℕ) :
    Fintype.card (BoundedMatrixCode k q) = (q + 1) ^ (k * k) := by
  simp only [BoundedMatrixCode, Fintype.card_fun, Fintype.card_fin]
  rw [pow_mul]

/-- Any lattice containing the constant rectangular lattice `q ℤ^k` is
spanned by an adapted basis whose entries lie in `[0,q]`. -/
noncomputable def constantAdaptedBasis {k q : ℕ} (hq : 0 < q)
    (Gamma : LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) :
    Basis (Fin k) ℤ Gamma.1 :=
  Classical.choose
    (AdaptedHNF.exists_adapted_basis (fun _ ↦ hq) Gamma.1 Gamma.2)

theorem constantAdaptedBasis_spec {k q : ℕ} (hq : 0 < q)
    (Gamma : LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) :
    AdaptedHNF.IsAdapted (v := fun _ : Fin k ↦ q)
      (constantAdaptedBasis hq Gamma) :=
  Classical.choose_spec
    (AdaptedHNF.exists_adapted_basis (fun _ ↦ hq) Gamma.1 Gamma.2)

/-- The bounded matrix of an adapted basis. -/
noncomputable def codeOfConstantSuperlattice {k q : ℕ} (hq : 0 < q)
    (Gamma : LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) :
    BoundedMatrixCode k q :=
  fun i j ↦
    ⟨Int.toNat
        ((((constantAdaptedBasis hq Gamma i : Gamma.1) : LatticePoint k)) j),
      by
        have hnonneg := (constantAdaptedBasis_spec hq Gamma i j).2.1
        have hle := (constantAdaptedBasis_spec hq Gamma i j).2.2
        rw [Int.toNat_lt hnonneg]
        exact_mod_cast (lt_of_le_of_lt hle (by omega : (q : ℤ) < q + 1))⟩

/-- A subgroup is contained in any subgroup containing the ambient vectors
of one of its integral bases. -/
theorem subgroup_le_of_basis_mem {k : ℕ}
    {Gamma Lambda : AddSubgroup (LatticePoint k)}
    (b : Basis (Fin k) ℤ Gamma)
    (hb : ∀ i, ((b i : Gamma) : LatticePoint k) ∈ Lambda) :
    Gamma ≤ Lambda := by
  intro x hx
  let xGamma : Gamma := ⟨x, hx⟩
  have hsum :
      (∑ i, LatticeBasis.basisCoeff b xGamma i •
        ((b i : Gamma) : LatticePoint k)) ∈ Lambda := by
    exact AddSubgroup.sum_mem Lambda fun i _ ↦
      Lambda.zsmul_mem (hb i) (LatticeBasis.basisCoeff b xGamma i)
  have hreconstruct := congrArg Subtype.val
    (LatticeBasis.sum_basisCoeff_smul b xGamma)
  have hcoe :
      (∑ i, LatticeBasis.basisCoeff b xGamma i •
        ((b i : Gamma) : LatticePoint k)) =
        ((↑(∑ i, LatticeBasis.basisCoeff b xGamma i • b i) :
          Gamma) : LatticePoint k) := by
    simp
  rw [hcoe, hreconstruct] at hsum
  exact hsum

/-- Equal bounded Hermite codes determine equal superlattices. -/
theorem codeOfConstantSuperlattice_injective {k q : ℕ} (hq : 0 < q) :
    Function.Injective (codeOfConstantSuperlattice (k := k) hq) := by
  intro Gamma Lambda hcode
  apply Subtype.ext
  apply le_antisymm
  · apply subgroup_le_of_basis_mem (constantAdaptedBasis hq Gamma)
    intro i
    have hvec :
        (((constantAdaptedBasis hq Gamma i : Gamma.1) : LatticePoint k)) =
          (((constantAdaptedBasis hq Lambda i : Lambda.1) : LatticePoint k)) := by
      funext j
      have hij := congrFun (congrFun hcode i) j
      have hGnonneg := (constantAdaptedBasis_spec hq Gamma i j).2.1
      have hLnonneg := (constantAdaptedBasis_spec hq Lambda i j).2.1
      have hnat := congrArg Fin.val hij
      calc
        (((constantAdaptedBasis hq Gamma i : Gamma.1) : LatticePoint k)) j =
            (Int.toNat
              ((((constantAdaptedBasis hq Gamma i : Gamma.1) :
                LatticePoint k)) j) : ℤ) :=
          (Int.toNat_of_nonneg hGnonneg).symm
        _ = (Int.toNat
              ((((constantAdaptedBasis hq Lambda i : Lambda.1) :
                LatticePoint k)) j) : ℤ) := by
          exact_mod_cast hnat
        _ = (((constantAdaptedBasis hq Lambda i : Lambda.1) :
                LatticePoint k)) j :=
          Int.toNat_of_nonneg hLnonneg
    rw [hvec]
    exact (constantAdaptedBasis hq Lambda i).property
  · apply subgroup_le_of_basis_mem (constantAdaptedBasis hq Lambda)
    intro i
    have hvec :
        (((constantAdaptedBasis hq Lambda i : Lambda.1) : LatticePoint k)) =
          (((constantAdaptedBasis hq Gamma i : Gamma.1) : LatticePoint k)) := by
      funext j
      have hij := congrFun (congrFun hcode i) j
      have hGnonneg := (constantAdaptedBasis_spec hq Gamma i j).2.1
      have hLnonneg := (constantAdaptedBasis_spec hq Lambda i j).2.1
      have hnat := congrArg Fin.val hij
      calc
        (((constantAdaptedBasis hq Lambda i : Lambda.1) : LatticePoint k)) j =
            (Int.toNat
              ((((constantAdaptedBasis hq Lambda i : Lambda.1) :
                LatticePoint k)) j) : ℤ) :=
          (Int.toNat_of_nonneg hLnonneg).symm
        _ = (Int.toNat
              ((((constantAdaptedBasis hq Gamma i : Gamma.1) :
                LatticePoint k)) j) : ℤ) := by
          exact_mod_cast hnat.symm
        _ = (((constantAdaptedBasis hq Gamma i : Gamma.1) :
                LatticePoint k)) j :=
          Int.toNat_of_nonneg hGnonneg
    rw [hvec]
    exact (constantAdaptedBasis hq Gamma i).property

/-- Polynomial count for full-rank sublattices containing `q ℤ^k`. -/
theorem card_constantSuperlattice_le {k q : ℕ} (hq : 0 < q) :
    Nat.card
        (LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) ≤
      (q + 1) ^ (k * k) := by
  have : Finite
      (LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) :=
    LatticeBasis.finite_superlattice (fun _ : Fin k ↦ hq)
  calc
    Nat.card (LatticeBasis.Superlattice (fun _ : Fin k ↦ q)) ≤
        Nat.card (BoundedMatrixCode k q) :=
      Nat.card_le_card_of_injective
        (codeOfConstantSuperlattice hq)
        (codeOfConstantSuperlattice_injective hq)
    _ = (q + 1) ^ (k * k) := by
      rw [Nat.card_eq_fintype_card, card_boundedMatrixCode]

/-- Full-rank subgroups of `ℤ^k` whose (finite) index is at most `K`. -/
abbrev IndexBoundedSublattice (k K : ℕ) :=
  {Gamma : LatticeBasis.Sublattice k //
    0 < Gamma.index ∧ Gamma.index ≤ K}

/-- A finite code for an index-bounded sublattice: its positive index, and
an adapted basis padded to the common entry bound `K`. -/
abbrev IndexBoundedSublatticeCode (k K : ℕ) :=
  Fin K × BoundedMatrixCode k K

@[simp]
theorem card_indexBoundedSublatticeCode (k K : ℕ) :
    Fintype.card (IndexBoundedSublatticeCode k K) =
      K * (K + 1) ^ (k * k) := by
  simp only [IndexBoundedSublatticeCode, BoundedMatrixCode,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [pow_mul]

/-- The index multiple of every ambient vector belongs to the subgroup. -/
theorem rectangular_index_le (k : ℕ) (Gamma : LatticeBasis.Sublattice k)
    (hindex : 0 < Gamma.index) :
    LatticeBasis.rectangularSubgroup (fun _ : Fin k ↦ Gamma.index) ≤
      Gamma := by
  intro x hx
  rw [LatticeBasis.mem_rectangularSubgroup_iff] at hx
  let y : LatticePoint k := fun i ↦ x i / (Gamma.index : ℤ)
  have hxy : Gamma.index • y = x := by
    funext i
    change (Gamma.index : ℤ) *
      (x i / (Gamma.index : ℤ)) = x i
    rw [mul_comm]
    exact Int.ediv_mul_cancel (hx i)
  rw [← hxy]
  exact Gamma.nsmul_index_mem y

/-- The adapted basis used to encode an index-bounded sublattice. -/
noncomputable def indexBoundedAdaptedBasis {k K : ℕ}
    (Gamma : IndexBoundedSublattice k K) :
    Basis (Fin k) ℤ Gamma.1 :=
  constantAdaptedBasis Gamma.2.1
    ⟨Gamma.1, rectangular_index_le k Gamma.1 Gamma.2.1⟩

theorem indexBoundedAdaptedBasis_spec {k K : ℕ}
    (Gamma : IndexBoundedSublattice k K) :
    AdaptedHNF.IsAdapted (v := fun _ : Fin k ↦ Gamma.1.index)
      (indexBoundedAdaptedBasis Gamma) :=
  constantAdaptedBasis_spec Gamma.2.1
    ⟨Gamma.1, rectangular_index_le k Gamma.1 Gamma.2.1⟩

/-- Encode an index-bounded sublattice by its positive index and its common
`K`-bounded adapted basis. -/
noncomputable def codeOfIndexBoundedSublattice {k K : ℕ}
    (Gamma : IndexBoundedSublattice k K) :
    IndexBoundedSublatticeCode k K :=
  (⟨Gamma.1.index - 1, by omega⟩,
    fun i j ↦
      ⟨Int.toNat
          ((((indexBoundedAdaptedBasis Gamma i : Gamma.1) :
            LatticePoint k)) j),
        by
          have hnonneg := (indexBoundedAdaptedBasis_spec Gamma i j).2.1
          have hle := (indexBoundedAdaptedBasis_spec Gamma i j).2.2
          rw [Int.toNat_lt hnonneg]
          exact hle.trans_lt (by
            exact_mod_cast Nat.lt_succ_of_le Gamma.2.2)⟩)

/-- The common bounded code is injective. -/
theorem codeOfIndexBoundedSublattice_injective {k K : ℕ} :
    Function.Injective (codeOfIndexBoundedSublattice (k := k) (K := K)) := by
  intro Gamma Lambda hcode
  have hfirst := congrArg Prod.fst hcode
  have hindex : Gamma.1.index = Lambda.1.index := by
    have hval := congrArg Fin.val hfirst
    dsimp [codeOfIndexBoundedSublattice] at hval
    omega
  have hmatrix := congrArg Prod.snd hcode
  apply Subtype.ext
  apply le_antisymm
  · apply subgroup_le_of_basis_mem (indexBoundedAdaptedBasis Gamma)
    intro i
    have hvec :
        (((indexBoundedAdaptedBasis Gamma i : Gamma.1) : LatticePoint k)) =
          (((indexBoundedAdaptedBasis Lambda i : Lambda.1) : LatticePoint k)) := by
      funext j
      have hij := congrFun (congrFun hmatrix i) j
      have hGnonneg := (indexBoundedAdaptedBasis_spec Gamma i j).2.1
      have hLnonneg := (indexBoundedAdaptedBasis_spec Lambda i j).2.1
      have hnat := congrArg Fin.val hij
      calc
        (((indexBoundedAdaptedBasis Gamma i : Gamma.1) : LatticePoint k)) j =
            (Int.toNat
              ((((indexBoundedAdaptedBasis Gamma i : Gamma.1) :
                LatticePoint k)) j) : ℤ) :=
          (Int.toNat_of_nonneg hGnonneg).symm
        _ = (Int.toNat
              ((((indexBoundedAdaptedBasis Lambda i : Lambda.1) :
                LatticePoint k)) j) : ℤ) := by
          exact_mod_cast hnat
        _ = (((indexBoundedAdaptedBasis Lambda i : Lambda.1) :
                LatticePoint k)) j :=
          Int.toNat_of_nonneg hLnonneg
    rw [hvec]
    exact (indexBoundedAdaptedBasis Lambda i).property
  · apply subgroup_le_of_basis_mem (indexBoundedAdaptedBasis Lambda)
    intro i
    have hvec :
        (((indexBoundedAdaptedBasis Lambda i : Lambda.1) : LatticePoint k)) =
          (((indexBoundedAdaptedBasis Gamma i : Gamma.1) : LatticePoint k)) := by
      funext j
      have hij := congrFun (congrFun hmatrix i) j
      have hGnonneg := (indexBoundedAdaptedBasis_spec Gamma i j).2.1
      have hLnonneg := (indexBoundedAdaptedBasis_spec Lambda i j).2.1
      have hnat := congrArg Fin.val hij
      calc
        (((indexBoundedAdaptedBasis Lambda i : Lambda.1) : LatticePoint k)) j =
            (Int.toNat
              ((((indexBoundedAdaptedBasis Lambda i : Lambda.1) :
                LatticePoint k)) j) : ℤ) :=
          (Int.toNat_of_nonneg hLnonneg).symm
        _ = (Int.toNat
              ((((indexBoundedAdaptedBasis Gamma i : Gamma.1) :
                LatticePoint k)) j) : ℤ) := by
          exact_mod_cast hnat.symm
        _ = (((indexBoundedAdaptedBasis Gamma i : Gamma.1) :
                LatticePoint k)) j :=
          Int.toNat_of_nonneg hGnonneg
    rw [hvec]
    exact (indexBoundedAdaptedBasis Gamma i).property

/-- Explicit polynomial bound for all full-rank sublattices of index at
most `K`. -/
theorem card_indexBoundedSublattice_le (k K : ℕ) :
    Nat.card (IndexBoundedSublattice k K) ≤
      K * (K + 1) ^ (k * k) := by
  calc
    Nat.card (IndexBoundedSublattice k K) ≤
        Nat.card (IndexBoundedSublatticeCode k K) :=
      Nat.card_le_card_of_injective codeOfIndexBoundedSublattice
        codeOfIndexBoundedSublattice_injective
    _ = K * (K + 1) ^ (k * k) := by
      rw [Nat.card_eq_fintype_card, card_indexBoundedSublatticeCode]

/-! ## Rational-span strata -/

/-- Rational subspaces generated by subsets of a fixed finite set. -/
abbrev GeneratedRationalSpanValue (d : ℕ)
    (Y : Finset (Fin d → ℚ)) :=
  {V : Submodule ℚ (Fin d → ℚ) //
    V ∈ Y.powerset.image (fun S : Finset (Fin d → ℚ) ↦
      Submodule.span ℚ (S : Set (Fin d → ℚ)))}

noncomputable instance generatedRationalSpanValueFintype (d : ℕ)
    (Y : Finset (Fin d → ℚ)) :
    Fintype (GeneratedRationalSpanValue d Y) :=
  Fintype.ofFinset
    (Y.powerset.image (fun S : Finset (Fin d → ℚ) ↦
      Submodule.span ℚ (S : Set (Fin d → ℚ))))
    (fun _ ↦ Iff.rfl)

/-- A generating subset chosen for one generated rational subspace. -/
noncomputable def spanGeneratingFinset {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    Finset (Fin d → ℚ) :=
  Classical.choose (Finset.mem_image.mp V.2)

theorem spanGeneratingFinset_spec {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    spanGeneratingFinset V ⊆ Y ∧
      Submodule.span ℚ (spanGeneratingFinset V : Set (Fin d → ℚ)) = V.1 := by
  have h := Classical.choose_spec (Finset.mem_image.mp V.2)
  exact ⟨Finset.mem_powerset.mp h.1, h.2⟩

/-- A linearly independent basis subset of the chosen generators. -/
noncomputable def spanBasisFinset {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    Finset (Fin d → ℚ) :=
  Classical.choose
    (Submodule.exists_finset_span_eq_linearIndepOn ℚ
      (spanGeneratingFinset V : Set (Fin d → ℚ)))

theorem spanBasisFinset_spec {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    (spanBasisFinset V : Set (Fin d → ℚ)) ⊆
        spanGeneratingFinset V ∧
      (spanBasisFinset V).card = Module.finrank ℚ V.1 ∧
      Submodule.span ℚ (spanBasisFinset V : Set (Fin d → ℚ)) = V.1 := by
  have h := Classical.choose_spec
    (Submodule.exists_finset_span_eq_linearIndepOn ℚ
      (spanGeneratingFinset V : Set (Fin d → ℚ)))
  refine ⟨h.1, ?_, ?_⟩
  · rw [← (spanGeneratingFinset_spec V).2]
    exact h.2.1
  · exact h.2.2.1.trans (spanGeneratingFinset_spec V).2

theorem spanBasisFinset_card_le {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    (spanBasisFinset V).card ≤ d := by
  rw [(spanBasisFinset_spec V).2.1]
  exact (Submodule.finrank_le V.1).trans_eq (Module.finrank_fin_fun ℚ)

/-- A basis-subset code, with the basis length explicitly bounded by `d`. -/
abbrev RationalSpanCode (d : ℕ) (Y : Finset (Fin d → ℚ)) :=
  Σ k : Fin (d + 1), Fin k.val → {y // y ∈ Y}

/-- Decode a basis-subset code by taking its rational span. -/
def decodeRationalSpanCode {d : ℕ} {Y : Finset (Fin d → ℚ)}
    (code : RationalSpanCode d Y) : Submodule ℚ (Fin d → ℚ) :=
  Submodule.span ℚ (Set.range fun i ↦ (code.2 i).1)

/-- The canonical code of a generated rational span. -/
noncomputable def codeOfGeneratedRationalSpan {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    RationalSpanCode d Y :=
  ⟨⟨(spanBasisFinset V).card, Nat.lt_succ_of_le (spanBasisFinset_card_le V)⟩,
    fun i ↦
      ⟨((spanBasisFinset V).equivFinOfCardEq rfl).symm i,
        (spanGeneratingFinset_spec V).1
          ((spanBasisFinset_spec V).1
            (((spanBasisFinset V).equivFinOfCardEq rfl).symm i).2)⟩⟩

theorem decode_codeOfGeneratedRationalSpan {d : ℕ}
    {Y : Finset (Fin d → ℚ)} (V : GeneratedRationalSpanValue d Y) :
    decodeRationalSpanCode (codeOfGeneratedRationalSpan V) = V.1 := by
  rw [decodeRationalSpanCode, codeOfGeneratedRationalSpan]
  change Submodule.span ℚ
    (Set.range (fun i ↦
      ↑(((spanBasisFinset V).equivFinOfCardEq rfl).symm i))) = V.1
  have hrange :
      Set.range (fun i ↦
        ↑(((spanBasisFinset V).equivFinOfCardEq rfl).symm i)) =
        (spanBasisFinset V : Set (Fin d → ℚ)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (((spanBasisFinset V).equivFinOfCardEq rfl).symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        ((spanBasisFinset V).equivFinOfCardEq rfl).symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [hrange]
  exact (spanBasisFinset_spec V).2.2

theorem codeOfGeneratedRationalSpan_injective {d : ℕ}
    {Y : Finset (Fin d → ℚ)} :
    Function.Injective (codeOfGeneratedRationalSpan (d := d) (Y := Y)) := by
  intro V W h
  apply Subtype.ext
  rw [← decode_codeOfGeneratedRationalSpan V,
    ← decode_codeOfGeneratedRationalSpan W, h]

/-- The basis-subset code has at most `(d+1)(|Y|+1)^d` values. -/
theorem card_rationalSpanCode_le (d : ℕ) (Y : Finset (Fin d → ℚ)) :
    Fintype.card (RationalSpanCode d Y) ≤
      (d + 1) * (Y.card + 1) ^ d := by
  rw [Fintype.card_sigma]
  calc
    (∑ k : Fin (d + 1), Fintype.card (Fin k.val → {y // y ∈ Y})) ≤
        ∑ _k : Fin (d + 1), (Y.card + 1) ^ d := by
      apply Finset.sum_le_sum
      intro k _hk
      simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
      change Y.card ^ k.val ≤ (Y.card + 1) ^ d
      exact (Nat.pow_le_pow_left (by omega : Y.card ≤ Y.card + 1) k.val).trans
        (Nat.pow_le_pow_right (by omega : 0 < Y.card + 1) (by omega))
    _ = (d + 1) * (Y.card + 1) ^ d := by simp [mul_comm]

/-- Polynomially many rational spans are generated by subsets of `Y`. -/
theorem card_generatedRationalSpanValue_le (d : ℕ)
    (Y : Finset (Fin d → ℚ)) :
    Fintype.card (GeneratedRationalSpanValue d Y) ≤
      (d + 1) * (Y.card + 1) ^ d := by
  exact (Fintype.card_le_of_injective codeOfGeneratedRationalSpan
    codeOfGeneratedRationalSpan_injective).trans
      (card_rationalSpanCode_le d Y)

/-! ## Integral points in a rational span -/

/-- Coordinatewise embedding of the integral lattice into the rational
coordinate space. -/
def rationalEmbedPoint (d : ℕ) : LatticePoint d →+ (Fin d → ℚ) where
  toFun x i := (x i : ℚ)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

@[simp]
theorem rationalEmbedPoint_apply {d : ℕ} (x : LatticePoint d) (i : Fin d) :
    rationalEmbedPoint d x i = (x i : ℚ) := rfl

@[simp]
theorem rationalEmbedPoint_zsmul {d : ℕ} (a : ℤ) (x : LatticePoint d) :
    rationalEmbedPoint d (a • x) = a • rationalEmbedPoint d x := by
  ext i
  simp [rationalEmbedPoint]

/-- Integral points in a rational coordinate subspace. -/
def integralLatticeOfRationalSpan {d : ℕ}
    (V : Submodule ℚ (Fin d → ℚ)) : AddSubgroup (LatticePoint d) :=
  V.toAddSubgroup.comap (rationalEmbedPoint d)

@[simp]
theorem mem_integralLatticeOfRationalSpan {d : ℕ}
    {V : Submodule ℚ (Fin d → ℚ)} {x : LatticePoint d} :
    x ∈ integralLatticeOfRationalSpan V ↔ rationalEmbedPoint d x ∈ V :=
  Iff.rfl

/-- Intersections of rational subspaces with the integral lattice are
saturated. -/
theorem integralLatticeOfRationalSpan_saturated {d : ℕ}
    (V : Submodule ℚ (Fin d → ℚ)) {a : ℤ} (ha : a ≠ 0)
    {x : LatticePoint d} (hx : a • x ∈ integralLatticeOfRationalSpan V) :
    x ∈ integralLatticeOfRationalSpan V := by
  rw [mem_integralLatticeOfRationalSpan,
    rationalEmbedPoint_zsmul] at hx
  rw [mem_integralLatticeOfRationalSpan]
  have hcast : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hinv := V.smul_mem (a : ℚ)⁻¹ hx
  have heq : (a : ℚ)⁻¹ •
      (a • rationalEmbedPoint d x) =
        rationalEmbedPoint d x := by
    ext i
    simp [smul_smul, hcast]
  rwa [heq] at hinv

/-- Reduce an integral point in a rational span modulo an integral rational
basis.  The representative lies in the coordinate box of radius `k*M`. -/
theorem exists_bounded_representative_mod_basis
    {d k M : ℕ} {V : Submodule ℚ (Fin d → ℚ)}
    (b : Basis (Fin k) ℚ V) (t : Fin k → LatticePoint d)
    (hbt : ∀ i, (b i : Fin d → ℚ) = rationalEmbedPoint d (t i))
    (htM : ∀ i j, |t i j| ≤ (M : ℤ))
    (x : LatticePoint d) (hx : x ∈ integralLatticeOfRationalSpan V) :
    ∃ y : LatticePoint d,
      y ∈ integralLatticeOfRationalSpan V ∧
      x - y ∈ AddSubgroup.closure (Set.range t) ∧
      ∀ j, |y j| ≤ ((k * M : ℕ) : ℤ) := by
  classical
  let xV : V := ⟨rationalEmbedPoint d x, hx⟩
  let coeff : Fin k → ℚ := fun i ↦ b.repr xV i
  let floorPart : LatticePoint d :=
    ∑ i, ⌊(coeff i)⌋ • t i
  let y : LatticePoint d := x - floorPart
  have hfloorSpan : floorPart ∈ AddSubgroup.closure (Set.range t) := by
    dsimp only [floorPart]
    exact AddSubgroup.sum_mem _ fun i _ ↦
      (AddSubgroup.closure (Set.range t)).zsmul_mem
        (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  have hembedFloor : rationalEmbedPoint d floorPart =
      ∑ i, (⌊coeff i⌋ : ℚ) • (b i : Fin d → ℚ) := by
    dsimp only [floorPart]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [rationalEmbedPoint_zsmul, hbt]
    rfl
  have hrepr : (xV : Fin d → ℚ) =
      ∑ i, coeff i • (b i : Fin d → ℚ) := by
    calc
      (xV : Fin d → ℚ) =
          (↑(∑ i, coeff i • b i) : Fin d → ℚ) := by
        exact congrArg Subtype.val (b.sum_repr xV).symm
      _ = ∑ i, coeff i • (b i : Fin d → ℚ) := by simp
  have hyrepr : rationalEmbedPoint d y =
      ∑ i, Int.fract (coeff i) • (b i : Fin d → ℚ) := by
    dsimp only [y]
    rw [map_sub, hembedFloor, show rationalEmbedPoint d x = xV from rfl,
      hrepr]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← sub_smul]
    rfl
  have hyV : y ∈ integralLatticeOfRationalSpan V := by
    rw [mem_integralLatticeOfRationalSpan, hyrepr]
    exact Submodule.sum_mem V fun i _ ↦ V.smul_mem _ (b i).property
  refine ⟨y, hyV, ?_, ?_⟩
  · have hxy : x - y = floorPart := by simp [y]
    rwa [hxy]
  · intro j
    have hyjQ := congrFun hyrepr j
    have habsQ : |(y j : ℚ)| ≤ (k * M : ℕ) := by
      change |rationalEmbedPoint d y j| ≤ ((k * M : ℕ) : ℚ)
      rw [hyjQ]
      simp only [Finset.sum_apply, Pi.smul_apply]
      calc
        |∑ i, Int.fract (coeff i) * (b i : Fin d → ℚ) j| ≤
            ∑ i, |Int.fract (coeff i) * (b i : Fin d → ℚ) j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin k, (M : ℚ) := by
          apply Finset.sum_le_sum
          intro i _hi
          rw [abs_mul, hbt, rationalEmbedPoint_apply]
          have hfract : |Int.fract (coeff i)| ≤ (1 : ℚ) := by
            rw [abs_of_nonneg (Int.fract_nonneg _)]
            exact (Int.fract_lt_one _).le
          have htMQ : |((t i j : ℤ) : ℚ)| ≤ M := by
            exact_mod_cast htM i j
          exact (mul_le_mul hfract htMQ (abs_nonneg _) (by positivity)).trans_eq
            (one_mul _)
        _ = (k * M : ℕ) := by simp
    exact_mod_cast habsQ

/-- The symmetric coordinate box used for finite quotient representatives. -/
abbrev SymmetricPointCode (d R : ℕ) := Fin d → SymmetricIntCode R

@[simp]
theorem card_symmetricPointCode (d R : ℕ) :
    Fintype.card (SymmetricPointCode d R) = (2 * R + 1) ^ d := by
  simp only [SymmetricPointCode, Fintype.card_fun, card_symmetricIntCode,
    Fintype.card_fin]

/-- An integral subgroup containing a bounded integral rational basis has
relative index at most the number of integral points in the resulting
fundamental coordinate box. -/
theorem relativeIndex_integralLattice_le_box
    {d k M : ℕ} {V : Submodule ℚ (Fin d → ℚ)}
    (b : Basis (Fin k) ℚ V) (t : Fin k → LatticePoint d)
    (hbt : ∀ i, (b i : Fin d → ℚ) = rationalEmbedPoint d (t i))
    (htM : ∀ i j, |t i j| ≤ (M : ℤ))
    (H : AddSubgroup (LatticePoint d))
    (htH : ∀ i, t i ∈ H)
    (hHL : H ≤ integralLatticeOfRationalSpan V) :
    H.relIndex (integralLatticeOfRationalSpan V) ≠ 0 ∧
      H.relIndex (integralLatticeOfRationalSpan V) ≤
        (2 * (k * M) + 1) ^ d := by
  classical
  let L := integralLatticeOfRationalSpan V
  let J : AddSubgroup L := H.addSubgroupOf L
  let Q := L ⧸ J
  let decode : SymmetricPointCode d (k * M) → LatticePoint d :=
    fun code j ↦ code j
  let f : SymmetricPointCode d (k * M) → Q := fun code ↦
    if hmem : decode code ∈ L then
      QuotientAddGroup.mk' J ⟨decode code, hmem⟩
    else 0
  have hclosure : AddSubgroup.closure (Set.range t) ≤ H := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact htH i
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective J q
    obtain ⟨y, hyL, hxy, hybound⟩ :=
      exists_bounded_representative_mod_basis b t hbt htM x.1 x.2
    let code : SymmetricPointCode d (k * M) := fun j ↦
      ⟨y j, by
        rw [Finset.mem_Icc]
        exact ⟨neg_le_of_abs_le (hybound j), le_of_abs_le (hybound j)⟩⟩
    have hdecode : decode code = y := by
      funext j
      rfl
    have hyL' : decode code ∈ L := by
      rw [hdecode]
      exact hyL
    refine ⟨code, ?_⟩
    change (if hmem : decode code ∈ L then
      QuotientAddGroup.mk' J ⟨decode code, hmem⟩ else 0) =
        QuotientAddGroup.mk' J x
    rw [dif_pos hyL']
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change decode code - x.1 ∈ H
    rw [hdecode]
    simpa [neg_sub] using H.neg_mem (hclosure hxy)
  have : Finite Q := Finite.of_surjective f hf
  have hcard : Nat.card Q ≤ (2 * (k * M) + 1) ^ d := by
    calc
      Nat.card Q ≤ Nat.card (SymmetricPointCode d (k * M)) :=
        Nat.card_le_card_of_surjective f hf
      _ = (2 * (k * M) + 1) ^ d := by
        rw [Nat.card_eq_fintype_card, card_symmetricPointCode]
  have hrel : H.relIndex L = Nat.card Q := by
    rfl
  rw [show integralLatticeOfRationalSpan V = L from rfl, hrel]
  exact ⟨Nat.card_pos.ne', hcard⟩

/-! ## Integral subgroup values generated by a finite coordinate set -/

/-- Coordinatewise rational images of a finite integral set. -/
def rationalImage (d : ℕ) (X : Finset (LatticePoint d)) :
    Finset (Fin d → ℚ) :=
  X.image (rationalEmbedPoint d)

/-- Integral subgroups generated by subsets of a fixed finite coordinate
set. -/
abbrev GeneratedIntegralSubgroupValue (d : ℕ)
    (X : Finset (LatticePoint d)) :=
  {H : AddSubgroup (LatticePoint d) //
    ∃ S : Finset (LatticePoint d), S ⊆ X ∧
      AddSubgroup.closure (S : Set (LatticePoint d)) = H}

noncomputable instance generatedIntegralSubgroupValueFintype (d : ℕ)
    (X : Finset (LatticePoint d)) :
    Fintype (GeneratedIntegralSubgroupValue d X) :=
  by
  classical
  exact Fintype.ofFinset
    (X.powerset.image (fun S : Finset (LatticePoint d) ↦
      AddSubgroup.closure (S : Set (LatticePoint d))))
    (fun H ↦ by
      constructor
      · intro hH
        obtain ⟨S, hSX, hS⟩ := Finset.mem_image.mp hH
        exact ⟨S, Finset.mem_powerset.mp hSX, hS⟩
      · rintro ⟨S, hSX, rfl⟩
        exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hSX, rfl⟩)

/-- A generating subset selected for a generated integral subgroup. -/
noncomputable def integralGeneratingFinset {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) : Finset (LatticePoint d) :=
  Classical.choose H.2

theorem integralGeneratingFinset_spec {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) :
    integralGeneratingFinset H ⊆ X ∧
      AddSubgroup.closure
        (integralGeneratingFinset H : Set (LatticePoint d)) = H.1 := by
  exact Classical.choose_spec H.2

/-- The rational span attached to a generated integral subgroup. -/
noncomputable def generatedIntegralRationalSpan {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) :
    GeneratedRationalSpanValue d (rationalImage d X) :=
  ⟨Submodule.span ℚ
      ((integralGeneratingFinset H).image (rationalEmbedPoint d) :
        Set (Fin d → ℚ)),
    by
      apply Finset.mem_image.mpr
      refine ⟨(integralGeneratingFinset H).image (rationalEmbedPoint d), ?_, rfl⟩
      rw [Finset.mem_powerset]
      exact Finset.image_mono _ (integralGeneratingFinset_spec H).1⟩

/-- The generating integral subgroup lies in the saturated integral lattice
of its rational span. -/
theorem generatedIntegralSubgroup_le_integralLattice {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) :
    H.1 ≤ integralLatticeOfRationalSpan
      (generatedIntegralRationalSpan H).1 := by
  have hclosure : AddSubgroup.closure
      (integralGeneratingFinset H : Set (LatticePoint d)) ≤
      integralLatticeOfRationalSpan
        (generatedIntegralRationalSpan H).1 := by
    rw [AddSubgroup.closure_le]
    intro x hx
    change rationalEmbedPoint d x ∈
      (generatedIntegralRationalSpan H).1
    apply Submodule.subset_span
    change rationalEmbedPoint d x ∈
      ((integralGeneratingFinset H).image (rationalEmbedPoint d) :
        Set (Fin d → ℚ))
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rwa [(integralGeneratingFinset_spec H).2] at hclosure

/-- A rational basis of the span can be selected among the integral
generators themselves.  This is the quantitative input needed by the
finite-quotient representative bound. -/
theorem exists_integral_basis_of_generatedSubgroup {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) :
    ∃ k : ℕ,
      k ≤ d ∧
      ∃ b : Basis (Fin k) ℚ (generatedIntegralRationalSpan H).1,
      ∃ t : Fin k → LatticePoint d,
        (∀ i, t i ∈ integralGeneratingFinset H) ∧
        (∀ i, (b i : Fin d → ℚ) = rationalEmbedPoint d (t i)) := by
  classical
  let S : Set (Fin d → ℚ) :=
    rationalEmbedPoint d ''
      (integralGeneratingFinset H : Set (LatticePoint d))
  obtain ⟨f, hfS, hfspan, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  let k := Module.finrank ℚ (Submodule.span ℚ S)
  have hk : k ≤ d := by
    exact (Submodule.finrank_le (Submodule.span ℚ S)).trans_eq
      (Module.finrank_fin_fun ℚ)
  choose t ht using hfS
  have htS : ∀ i, t i ∈ integralGeneratingFinset H := by
    intro i
    exact (ht i).1
  have hft : ∀ i, f i = rationalEmbedPoint d (t i) := by
    intro i
    exact (ht i).2.symm
  have hSV : Submodule.span ℚ S =
      (generatedIntegralRationalSpan H).1 := by
    simp only [S, generatedIntegralRationalSpan]
    congr 1
    ext y
    simp
  let b : Basis (Fin k) ℚ (generatedIntegralRationalSpan H).1 :=
    (Basis.span hfLI).map
      (LinearEquiv.ofEq _ _ (hfspan.trans hSV))
  refine ⟨k, hk, b, t, htS, ?_⟩
  intro i
  change ((b i : (generatedIntegralRationalSpan H).1) : Fin d → ℚ) = _
  rw [show ((b i : (generatedIntegralRationalSpan H).1) : Fin d → ℚ) =
      f i by simp [b]]
  exact hft i

/-- A uniform coordinate bound on `X` also bounds the selected integral
rational basis. -/
theorem exists_bounded_integral_basis_of_generatedSubgroup {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ))
    (H : GeneratedIntegralSubgroupValue d X) :
    ∃ k : ℕ,
      k ≤ d ∧
      ∃ b : Basis (Fin k) ℚ (generatedIntegralRationalSpan H).1,
      ∃ t : Fin k → LatticePoint d,
        (∀ i, t i ∈ H.1) ∧
        (∀ i, (b i : Fin d → ℚ) = rationalEmbedPoint d (t i)) ∧
        (∀ i j, |t i j| ≤ (M : ℤ)) := by
  obtain ⟨k, hk, b, t, htS, hbt⟩ :=
    exists_integral_basis_of_generatedSubgroup H
  refine ⟨k, hk, b, t, ?_, hbt, ?_⟩
  · intro i
    rw [← (integralGeneratingFinset_spec H).2]
    exact AddSubgroup.subset_closure (htS i)
  · intro i j
    exact hXM (t i)
      ((integralGeneratingFinset_spec H).1 (htS i)) j

/-- Uniform upper bound for the relative index of a generated subgroup in
the integral points of its rational span. -/
def generatedSubgroupIndexBound (d M : ℕ) : ℕ :=
  (2 * (d * M) + 1) ^ d

/-- The relative index is positive and bounded uniformly in terms of the
ambient dimension and the coordinate radius. -/
theorem generatedIntegralSubgroup_relativeIndex_pos_le {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ))
    (H : GeneratedIntegralSubgroupValue d X) :
    H.1.relIndex
          (integralLatticeOfRationalSpan
            (generatedIntegralRationalSpan H).1) ≠ 0 ∧
      H.1.relIndex
          (integralLatticeOfRationalSpan
            (generatedIntegralRationalSpan H).1) ≤
        generatedSubgroupIndexBound d M := by
  obtain ⟨k, hk, b, t, htH, hbt, htM⟩ :=
    exists_bounded_integral_basis_of_generatedSubgroup hXM H
  have h := relativeIndex_integralLattice_le_box b t hbt htM H.1 htH
    (generatedIntegralSubgroup_le_integralLattice H)
  refine ⟨h.1, h.2.trans ?_⟩
  exact Nat.pow_le_pow_left (by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right M hk)) 1) d

/-- Add the constant rectangular lattice at the relative-index scale.  The
result has full rank while retaining enough information to recover the
original subgroup after intersecting with its saturated rational lattice. -/
noncomputable def augmentedGeneratedIntegralSubgroup {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X) :
    LatticeBasis.Sublattice d :=
  H.1 ⊔ LatticeBasis.rectangularSubgroup (fun _ : Fin d ↦
    H.1.relIndex
      (integralLatticeOfRationalSpan
        (generatedIntegralRationalSpan H).1))

/-- Saturation gives exact recovery from the rational span and the
full-rank augmentation. -/
theorem generatedIntegralSubgroup_eq_augmented_inf {d : ℕ}
    {X : Finset (LatticePoint d)}
    (H : GeneratedIntegralSubgroupValue d X)
    (hq : H.1.relIndex
      (integralLatticeOfRationalSpan
        (generatedIntegralRationalSpan H).1) ≠ 0) :
    H.1 = augmentedGeneratedIntegralSubgroup H ⊓
      integralLatticeOfRationalSpan
        (generatedIntegralRationalSpan H).1 := by
  classical
  let L := integralLatticeOfRationalSpan
    (generatedIntegralRationalSpan H).1
  let q := H.1.relIndex L
  have hHL : H.1 ≤ L := generatedIntegralSubgroup_le_integralLattice H
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq
  change H.1 =
    (H.1 ⊔ LatticeBasis.rectangularSubgroup
      (fun _ : Fin d ↦ q)) ⊓ L
  apply le_antisymm
  · intro x hx
    exact ⟨(le_sup_left : H.1 ≤ H.1 ⊔
      LatticeBasis.rectangularSubgroup (fun _ : Fin d ↦ q)) hx, hHL hx⟩
  · intro x hx
    obtain ⟨h, hh, r, hr, hhr⟩ := AddSubgroup.mem_sup.mp hx.1
    have hrL : r ∈ L := by
      have hre : r = x - h := by
        rw [← hhr]
        simp
      rw [hre]
      exact L.sub_mem hx.2 (hHL hh)
    let y : LatticePoint d := fun i ↦ r i / (q : ℤ)
    have hqy : q • y = r := by
      funext i
      change (q : ℤ) * (r i / (q : ℤ)) = r i
      rw [mul_comm]
      exact Int.ediv_mul_cancel
        ((LatticeBasis.mem_rectangularSubgroup_iff.mp hr) i)
    have hyL : y ∈ L := by
      apply integralLatticeOfRationalSpan_saturated
        (generatedIntegralRationalSpan H).1 hqZ
      have hqyZ : (q : ℤ) • y = r := by
        simpa using hqy
      rw [hqyZ]
      exact hrL
    have hqyH : q • y ∈ H.1 := by
      let yL : L := ⟨y, hyL⟩
      have hyq := (H.1.addSubgroupOf L).nsmul_index_mem yL
      change q • y ∈ H.1 at hyq
      exact hyq
    rw [← hhr, ← hqy]
    exact H.1.add_mem hh hqyH

/-- The uniform full-rank index bound for the augmented subgroup. -/
def augmentedSubgroupIndexBound (d M : ℕ) : ℕ :=
  (generatedSubgroupIndexBound d M) ^ d

theorem augmentedGeneratedIntegralSubgroup_index_pos_le {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ))
    (H : GeneratedIntegralSubgroupValue d X) :
    0 < (augmentedGeneratedIntegralSubgroup H).index ∧
      (augmentedGeneratedIntegralSubgroup H).index ≤
        augmentedSubgroupIndexBound d M := by
  let L := integralLatticeOfRationalSpan
    (generatedIntegralRationalSpan H).1
  let q := H.1.relIndex L
  let Gamma := augmentedGeneratedIntegralSubgroup H
  have hqData := generatedIntegralSubgroup_relativeIndex_pos_le hXM H
  have hqPos : 0 < q := Nat.pos_of_ne_zero hqData.1
  have hrect : LatticeBasis.rectangularSubgroup
      (fun _ : Fin d ↦ q) ≤ Gamma := le_sup_right
  have hmul := AddSubgroup.relIndex_mul_index hrect
  have hrectIndex :
      (LatticeBasis.rectangularSubgroup
        (fun _ : Fin d ↦ q)).index = q ^ d := by
    rw [LatticeBasis.rectangularSubgroup_index]
    simp
  rw [hrectIndex] at hmul
  have hpowPos : 0 < q ^ d := pow_pos hqPos d
  have hGammaPos : 0 < Gamma.index := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, mul_zero] at hmul
    omega
  refine ⟨hGammaPos, ?_⟩
  have hGammaDvd : Gamma.index ∣ q ^ d := by
    refine ⟨(LatticeBasis.rectangularSubgroup
      (fun _ : Fin d ↦ q)).relIndex Gamma, ?_⟩
    rw [mul_comm]
    exact hmul.symm
  exact (Nat.le_of_dvd hpowPos hGammaDvd).trans
    (Nat.pow_le_pow_left hqData.2 d)

/-- The bounded full-rank code associated to a generated subgroup. -/
noncomputable def augmentedGeneratedIntegralSubgroupCode {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ))
    (H : GeneratedIntegralSubgroupValue d X) :
    IndexBoundedSublatticeCode d (augmentedSubgroupIndexBound d M) :=
  codeOfIndexBoundedSublattice
    ⟨augmentedGeneratedIntegralSubgroup H,
      augmentedGeneratedIntegralSubgroup_index_pos_le hXM H⟩

/-- The complete finite code: rational span plus a bounded full-rank
augmentation. -/
abbrev GeneratedIntegralSubgroupCode (d M : ℕ)
    (X : Finset (LatticePoint d)) :=
  RationalSpanCode d (rationalImage d X) ×
    IndexBoundedSublatticeCode d (augmentedSubgroupIndexBound d M)

noncomputable def codeOfGeneratedIntegralSubgroup {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ))
    (H : GeneratedIntegralSubgroupValue d X) :
    GeneratedIntegralSubgroupCode d M X :=
  (codeOfGeneratedRationalSpan (generatedIntegralRationalSpan H),
    augmentedGeneratedIntegralSubgroupCode hXM H)

/-- Equality of complete codes recovers the original generated subgroup. -/
theorem codeOfGeneratedIntegralSubgroup_injective {d M : ℕ}
    {X : Finset (LatticePoint d)}
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ)) :
    Function.Injective (codeOfGeneratedIntegralSubgroup hXM) := by
  intro H K hcode
  have hV : generatedIntegralRationalSpan H =
      generatedIntegralRationalSpan K :=
    codeOfGeneratedRationalSpan_injective (congrArg Prod.fst hcode)
  have hGammaSubtype :
      (⟨augmentedGeneratedIntegralSubgroup H,
        augmentedGeneratedIntegralSubgroup_index_pos_le hXM H⟩ :
          IndexBoundedSublattice d (augmentedSubgroupIndexBound d M)) =
      ⟨augmentedGeneratedIntegralSubgroup K,
        augmentedGeneratedIntegralSubgroup_index_pos_le hXM K⟩ := by
    apply codeOfIndexBoundedSublattice_injective
    exact congrArg Prod.snd hcode
  have hGamma : augmentedGeneratedIntegralSubgroup H =
      augmentedGeneratedIntegralSubgroup K :=
    congrArg (fun G : IndexBoundedSublattice d
      (augmentedSubgroupIndexBound d M) ↦ G.1) hGammaSubtype
  have hVval : (generatedIntegralRationalSpan H).1 =
      (generatedIntegralRationalSpan K).1 := congrArg Subtype.val hV
  apply Subtype.ext
  calc
    H.1 = augmentedGeneratedIntegralSubgroup H ⊓
        integralLatticeOfRationalSpan
          (generatedIntegralRationalSpan H).1 :=
      generatedIntegralSubgroup_eq_augmented_inf H
        (generatedIntegralSubgroup_relativeIndex_pos_le hXM H).1
    _ = augmentedGeneratedIntegralSubgroup K ⊓
        integralLatticeOfRationalSpan
          (generatedIntegralRationalSpan K).1 := by
      rw [hGamma, hVval]
    _ = K.1 :=
      (generatedIntegralSubgroup_eq_augmented_inf K
        (generatedIntegralSubgroup_relativeIndex_pos_le hXM K).1).symm

/-- Explicit finite bound for all subgroups generated by subsets of a
coordinate set in a fixed integer box. -/
theorem card_generatedIntegralSubgroupValue_le {d M : ℕ}
    (X : Finset (LatticePoint d))
    (hXM : ∀ x ∈ X, ∀ j, |x j| ≤ (M : ℤ)) :
    Fintype.card (GeneratedIntegralSubgroupValue d X) ≤
      ((d + 1) * (X.card + 1) ^ d) *
        (augmentedSubgroupIndexBound d M *
          (augmentedSubgroupIndexBound d M + 1) ^ (d * d)) := by
  let Y := rationalImage d X
  let K := augmentedSubgroupIndexBound d M
  calc
    Fintype.card (GeneratedIntegralSubgroupValue d X) ≤
        Fintype.card (GeneratedIntegralSubgroupCode d M X) :=
      Fintype.card_le_of_injective (codeOfGeneratedIntegralSubgroup hXM)
        (codeOfGeneratedIntegralSubgroup_injective hXM)
    _ = Fintype.card (RationalSpanCode d Y) *
        (K * (K + 1) ^ (d * d)) := by
      rw [Fintype.card_prod]
      change Fintype.card (RationalSpanCode d (rationalImage d X)) *
        Fintype.card (IndexBoundedSublatticeCode d
          (augmentedSubgroupIndexBound d M)) = _
      rw [card_indexBoundedSublatticeCode]
    _ ≤ ((d + 1) * (X.card + 1) ^ d) *
        (K * (K + 1) ^ (d * d)) := by
      apply Nat.mul_le_mul_right
      exact (card_rationalSpanCode_le d Y).trans
        (Nat.mul_le_mul_left (d + 1)
          (Nat.pow_le_pow_left (by
            dsimp only [Y, rationalImage]
            exact Nat.add_le_add_right (Finset.card_image_le) 1) d))

/-! ## The canonical distinct-span index -/

/-- Coordinate image of a finite source set in one dimension. -/
def finiteCoordinateImage {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (phi : (d : ℕ) → alpha → LatticePoint d)
    (d : ℕ) : Finset (LatticePoint d) :=
  A.attach.image (fun a ↦ phi d a.1)

theorem finiteCoordinateImage_card_le {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (phi : (d : ℕ) → alpha → LatticePoint d)
    (d : ℕ) :
    (finiteCoordinateImage A phi d).card ≤ A.card := by
  exact (Finset.card_image_le).trans_eq A.card_attach

/-- A source subset selected from the closure witness stored by a distinct
span value. -/
noncomputable def distinctSpanGeneratingFinset
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d)
    (w : FinsetDistinctSpanIndex A relevant phi) : Finset {a // a ∈ A} :=
  Classical.choose
    (exists_closure_eq_of_mem_generatedSubgroupValues
      (fun d : {d // d ∈ relevant} ↦ LatticePoint d.1)
      (fun d : {d // d ∈ relevant} ↦
        fun a : {a // a ∈ A} ↦ phi d.1 a.1)
      w.1 w.2.2.1)

theorem distinctSpanGeneratingFinset_spec
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d)
    (w : FinsetDistinctSpanIndex A relevant phi) :
    AddSubgroup.closure
        ((fun a : {a // a ∈ A} ↦ phi w.1.1 a.1) ''
          (distinctSpanGeneratingFinset A relevant phi w :
            Set {a // a ∈ A})) = w.2.1 :=
  Classical.choose_spec
    (exists_closure_eq_of_mem_generatedSubgroupValues
      (fun d : {d // d ∈ relevant} ↦ LatticePoint d.1)
      (fun d : {d // d ∈ relevant} ↦
        fun a : {a // a ∈ A} ↦ phi d.1 a.1)
      w.1 w.2.2.1)

/-- Forget the properness clause of a distinct span, retaining its subgroup
as one generated by a subset of the finite coordinate image. -/
noncomputable def generatedIntegralValueOfDistinctSpan
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d)
    (w : FinsetDistinctSpanIndex A relevant phi) :
    GeneratedIntegralSubgroupValue w.1.1
      (finiteCoordinateImage A phi w.1.1) :=
  ⟨w.2.1,
    (distinctSpanGeneratingFinset A relevant phi w).image
      (fun a ↦ phi w.1.1 a.1),
    by
      intro x hx
      obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩,
    by
      simpa only [Finset.coe_image] using
        distinctSpanGeneratingFinset_spec A relevant phi w⟩

@[simp]
theorem generatedIntegralValueOfDistinctSpan_val
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d)
    (w : FinsetDistinctSpanIndex A relevant phi) :
    (generatedIntegralValueOfDistinctSpan A relevant phi w).1 = w.2.1 :=
  rfl

/-- Canonical map from the repository's distinct-span index into the sigma
type of generated integral subgroup values. -/
noncomputable def codeOfFinsetDistinctSpan
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d) :
    FinsetDistinctSpanIndex A relevant phi →
      Sigma (fun d : {d // d ∈ relevant} ↦
        GeneratedIntegralSubgroupValue d.1
          (finiteCoordinateImage A phi d.1)) :=
  fun w ↦ ⟨w.1, generatedIntegralValueOfDistinctSpan A relevant phi w⟩

theorem codeOfFinsetDistinctSpan_injective
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d) :
    Function.Injective (codeOfFinsetDistinctSpan A relevant phi) := by
  intro u v huv
  cases u with
  | mk du Hu =>
      cases v with
      | mk dv Hv =>
          have hinj := Sigma.mk.inj_iff.mp huv
          cases hinj.1
          have hvalue :
              generatedIntegralValueOfDistinctSpan A relevant phi ⟨du, Hu⟩ =
                generatedIntegralValueOfDistinctSpan A relevant phi ⟨du, Hv⟩ :=
            eq_of_heq hinj.2
          have hgroup : Hu.1 = Hv.1 := by
            calc
              Hu.1 = (generatedIntegralValueOfDistinctSpan
                  A relevant phi ⟨du, Hu⟩).1 :=
                (generatedIntegralValueOfDistinctSpan_val
                  A relevant phi ⟨du, Hu⟩).symm
              _ = (generatedIntegralValueOfDistinctSpan
                  A relevant phi ⟨du, Hv⟩).1 :=
                congrArg Subtype.val hvalue
              _ = Hv.1 := generatedIntegralValueOfDistinctSpan_val
                A relevant phi ⟨du, Hv⟩
          apply Sigma.mk.inj_iff.mpr
          exact ⟨rfl, heq_of_eq (Subtype.ext hgroup)⟩

/-- Explicit sum bound for all distinct proper generated spans. -/
theorem card_finsetDistinctSpanIndex_le
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d) (M : ℕ)
    (hphi : ∀ d ∈ relevant, ∀ a ∈ A, ∀ j, |phi d a j| ≤ (M : ℤ)) :
    Fintype.card (FinsetDistinctSpanIndex A relevant phi) ≤
      ∑ d : {d // d ∈ relevant},
        ((d.1 + 1) * (A.card + 1) ^ d.1) *
          (augmentedSubgroupIndexBound d.1 M *
            (augmentedSubgroupIndexBound d.1 M + 1) ^ (d.1 * d.1)) := by
  classical
  calc
    Fintype.card (FinsetDistinctSpanIndex A relevant phi) ≤
        Fintype.card (Sigma (fun d : {d // d ∈ relevant} ↦
          GeneratedIntegralSubgroupValue d.1
            (finiteCoordinateImage A phi d.1))) :=
      Fintype.card_le_of_injective (codeOfFinsetDistinctSpan A relevant phi)
        (codeOfFinsetDistinctSpan_injective A relevant phi)
    _ = ∑ d : {d // d ∈ relevant},
        Fintype.card (GeneratedIntegralSubgroupValue d.1
          (finiteCoordinateImage A phi d.1)) := by
      rw [Fintype.card_sigma]
    _ ≤ ∑ d : {d // d ∈ relevant},
        ((d.1 + 1) * (A.card + 1) ^ d.1) *
          (augmentedSubgroupIndexBound d.1 M *
            (augmentedSubgroupIndexBound d.1 M + 1) ^ (d.1 * d.1)) := by
      apply Finset.sum_le_sum
      intro d _hd
      have hcoord : ∀ x ∈ finiteCoordinateImage A phi d.1,
          ∀ j, |x j| ≤ (M : ℤ) := by
        intro x hx j
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact hphi d.1 d.2 a.1 a.2 j
      exact (card_generatedIntegralSubgroupValue_le
        (finiteCoordinateImage A phi d.1) hcoord).trans
          (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left (d.1 + 1)
              (Nat.pow_le_pow_left (Nat.add_le_add_right
                (finiteCoordinateImage_card_le A phi d.1) 1) d.1)))

/-! ## Canonical centered-coordinate bounds -/

/-- Every relevant centered identification coordinate lies in the symmetric
integer box of radius equal to the bounding GAP volume. -/
theorem abs_centeredMinimalIdentificationFamily_le_volume
    {W : Finset ℤ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hzero : 0 ∈ W) {d : ℕ} (hd : d ∈ relevant)
    {z : ℤ} (hz : z ∈ W) (j : Fin d) :
    |Stability.centeredMinimalIdentificationFamily hproper d z j| ≤
      ((BoundingBox.dBoundingBox W d (hproper.positive hd)).progression.volume :
        ℤ) := by
  let P := BoundingBox.dBoundingBox W d (hproper.positive hd)
  rw [Stability.centeredMinimalIdentificationFamily,
    Stability.minimalIdentificationFamily_apply hproper hd hz,
    Stability.minimalIdentificationFamily_apply hproper hd hzero]
  change |P.identificationMap (hproper.proper hd) ⟨z, hz⟩ j -
    P.identificationMap (hproper.proper hd) ⟨0, hzero⟩ j| ≤
      (P.progression.volume : ℤ)
  rw [P.identificationMap_apply, P.identificationMap_apply]
  apply abs_sub_le_of_nonneg_of_le
  · positivity
  · exact_mod_cast
      ((P.progression.coordinateMap
        (hproper.proper hd) ⟨BoundingBox.intPoint z, P.bounds ⟨z, hz⟩⟩ j).isLt.le.trans
          (factor_le_fin_product P.progression.width_pos j))
  · positivity
  · exact_mod_cast
      ((P.progression.coordinateMap
        (hproper.proper hd) ⟨BoundingBox.intPoint 0, P.bounds ⟨0, hzero⟩⟩ j).isLt.le.trans
          (factor_le_fin_product P.progression.width_pos j))

/-- Under the preprocessing interval hypotheses, all centered coordinates
have absolute value at most `n`. -/
theorem abs_centeredMinimalIdentificationFamily_le
    {B W : Finset ℤ} {relevant : Finset ℕ} {n : ℕ}
    (hBW : B ⊆ W) (hzeroW : 0 ∈ W)
    (hW : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hproper : Stability.RelevantBoxesProper W relevant)
    {d : ℕ} (hd : d ∈ relevant) {z : ℤ} (hz : z ∈ B)
    (j : Fin d) :
    |Stability.centeredMinimalIdentificationFamily hproper d z j| ≤
      (n : ℤ) := by
  exact (abs_centeredMinimalIdentificationFamily_le_volume
    hproper hzeroW hd (hBW hz) j).trans (by
      exact_mod_cast BoundingBox.dBoundingBox_volume_le_of_mem_Ico
        W d n (hproper.positive hd) hzeroW hW)

/-- Every canonical minimal comparison box in a relevant dimension has
volume at most the ambient interval length. -/
theorem minimalBoxFamily_volume_le
    {W : Finset ℤ} {n : ℕ} (hzeroW : 0 ∈ W)
    (hW : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    {d : ℕ} (hd : 0 < d) :
    (Stability.minimalBoxFamily W d).volume ≤ n := by
  rw [Stability.minimalBoxFamily_eq_dBoundingBox W hd]
  exact BoundingBox.dBoundingBox_volume_le_of_mem_Ico W d n hd hzeroW hW

/-! ## Uniform polynomial absorption -/

theorem add_one_le_sq {a n : ℕ} (hn : 2 ≤ n) (ha : a ≤ n) :
    a + 1 ≤ n ^ 2 := by
  calc
    a + 1 ≤ n + 1 := by omega
    _ ≤ n * n := by nlinarith
    _ = n ^ 2 := by ring

theorem two_mul_add_one_le_cube {x : ℕ} (hx : 2 ≤ x) :
    2 * x + 1 ≤ x ^ 3 := by
  calc
    2 * x + 1 ≤ 3 * x := by omega
    _ ≤ x * x * x := by
      have h3 : 3 ≤ x * x := by nlinarith
      exact Nat.mul_le_mul_right x h3
    _ = x ^ 3 := by ring

/-- Adding one to a quantity already bounded by a power costs one further
power when the base is at least two. -/
theorem add_one_le_pow_succ {a n e : ℕ} (hn : 2 ≤ n)
    (ha : a ≤ n ^ e) :
    a + 1 ≤ n ^ (e + 1) := by
  calc
    a + 1 ≤ n ^ e + 1 := Nat.add_le_add_right ha 1
    _ ≤ 2 * n ^ e := by
      have hpow : 1 ≤ n ^ e := Nat.one_le_pow e n (by omega)
      omega
    _ ≤ n * n ^ e := Nat.mul_le_mul_right (n ^ e) hn
    _ = n ^ (e + 1) := by rw [pow_succ']

/-- Exponent used for one fixed-dimensional generated-span family. -/
def generatedSpanPolynomialExponent (d : ℕ) : ℕ :=
  2 + 2 * d + 6 * d * d + (6 * d * d + 1) * (d * d)

/-- The explicit generated-subgroup code is polynomial in `n`, uniformly
for coordinate dimension and source cardinal at most `n`. -/
theorem generatedIntegralSubgroupCodeBound_le_pow
    {d sourceCard n : ℕ} (hn : 2 ≤ n)
    (hd : d ≤ n) (hcard : sourceCard ≤ n) :
    ((d + 1) * (sourceCard + 1) ^ d) *
        (augmentedSubgroupIndexBound d n *
          (augmentedSubgroupIndexBound d n + 1) ^ (d * d)) ≤
      n ^ generatedSpanPolynomialExponent d := by
  by_cases hd0 : d = 0
  · subst d
    simp only [generatedSpanPolynomialExponent, augmentedSubgroupIndexBound,
      generatedSubgroupIndexBound, zero_mul, pow_zero, add_zero, one_mul,
      Nat.reduceAdd]
    exact Nat.one_le_pow 2 n (by omega)
  have hd1 : d + 1 ≤ n ^ 2 := add_one_le_sq hn hd
  have hc1 : sourceCard + 1 ≤ n ^ 2 := add_one_le_sq hn hcard
  have hdn : d * n ≤ n ^ 2 := by
    calc
      d * n ≤ n * n := Nat.mul_le_mul_right n hd
      _ = n ^ 2 := by ring
  have hdnPos : 2 ≤ d * n := by
    exact hn.trans (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hd0))
  have hbase : 2 * (d * n) + 1 ≤ n ^ 6 := by
    calc
      2 * (d * n) + 1 ≤ (d * n) ^ 3 :=
        two_mul_add_one_le_cube hdnPos
      _ ≤ (n ^ 2) ^ 3 := Nat.pow_le_pow_left hdn 3
      _ = n ^ 6 := by rw [← pow_mul]
  have hindex : generatedSubgroupIndexBound d n ≤ n ^ (6 * d) := by
    exact (Nat.pow_le_pow_left hbase d).trans_eq (by
      simp only [generatedSubgroupIndexBound, pow_mul])
  have haug : augmentedSubgroupIndexBound d n ≤
      n ^ (6 * d * d) := by
    exact (Nat.pow_le_pow_left hindex d).trans_eq (by
      simp only [augmentedSubgroupIndexBound, pow_mul])
  have haug1 : augmentedSubgroupIndexBound d n + 1 ≤
      n ^ (6 * d * d + 1) := add_one_le_pow_succ hn haug
  calc
    ((d + 1) * (sourceCard + 1) ^ d) *
        (augmentedSubgroupIndexBound d n *
          (augmentedSubgroupIndexBound d n + 1) ^ (d * d)) ≤
      ((n ^ 2) * (n ^ 2) ^ d) *
        (n ^ (6 * d * d) *
          (n ^ (6 * d * d + 1)) ^ (d * d)) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul hd1 (Nat.pow_le_pow_left hc1 d))
        (Nat.mul_le_mul haug (Nat.pow_le_pow_left haug1 (d * d)))
    _ = n ^ generatedSpanPolynomialExponent d := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      simp only [generatedSpanPolynomialExponent]
      omega

theorem generatedSpanPolynomialExponent_mono {d D : ℕ} (hdD : d ≤ D) :
    generatedSpanPolynomialExponent d ≤
      generatedSpanPolynomialExponent D := by
  have hsq : d * d ≤ D * D := Nat.mul_le_mul hdD hdD
  have hlin : 2 * d ≤ 2 * D := Nat.mul_le_mul_left 2 hdD
  have hsix : 6 * d * d ≤ 6 * D * D := by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 6 hsq
  have hlast : (6 * d * d + 1) * (d * d) ≤
      (6 * D * D + 1) * (D * D) :=
    Nat.mul_le_mul (Nat.add_le_add_right hsix 1) hsq
  unfold generatedSpanPolynomialExponent
  omega

/-- All distinct generated spans across the relevant dimensions retain a
single fixed-`D` polynomial bound. -/
theorem card_finsetDistinctSpanIndex_le_pow
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (relevant : Finset ℕ)
    (phi : (d : ℕ) → alpha → LatticePoint d)
    {D n : ℕ} (hn : 2 ≤ n) (hDn : D ≤ n)
    (hcard : A.card ≤ n)
    (hpositive : ∀ d ∈ relevant, 0 < d)
    (hrank : ∀ d ∈ relevant, d ≤ D)
    (hphi : ∀ d ∈ relevant, ∀ a ∈ A, ∀ j, |phi d a j| ≤ (n : ℤ)) :
    Fintype.card (FinsetDistinctSpanIndex A relevant phi) ≤
      n ^ (generatedSpanPolynomialExponent D + 1) := by
  classical
  have hcardRelevant : relevant.card ≤ D := by
    have hsubset : relevant ⊆ Finset.Icc 1 D := by
      intro d hd
      exact Finset.mem_Icc.mpr ⟨hpositive d hd, hrank d hd⟩
    exact (Finset.card_le_card hsubset).trans_eq (by
      simp)
  calc
    Fintype.card (FinsetDistinctSpanIndex A relevant phi) ≤
        ∑ d : {d // d ∈ relevant},
          ((d.1 + 1) * (A.card + 1) ^ d.1) *
            (augmentedSubgroupIndexBound d.1 n *
              (augmentedSubgroupIndexBound d.1 n + 1) ^
                (d.1 * d.1)) :=
      card_finsetDistinctSpanIndex_le A relevant phi n hphi
    _ ≤ ∑ _d : {d // d ∈ relevant},
        n ^ generatedSpanPolynomialExponent D := by
      apply Finset.sum_le_sum
      intro d _hd
      exact (generatedIntegralSubgroupCodeBound_le_pow hn
        ((hrank d.1 d.2).trans hDn) hcard).trans
          (Nat.pow_le_pow_right (by omega)
            (generatedSpanPolynomialExponent_mono (hrank d.1 d.2)))
    _ = relevant.card * n ^ generatedSpanPolynomialExponent D := by
      simp
    _ ≤ n * n ^ generatedSpanPolynomialExponent D := by
      exact Nat.mul_le_mul_right _ (hcardRelevant.trans hDn)
    _ = n ^ (generatedSpanPolynomialExponent D + 1) := by
      rw [pow_succ']

/-- Exponent for the one-dimensional weak-trace presentation code. -/
def weakTracePolynomialExponent (D : ℕ) : ℕ := 14 + 7 * D

theorem weakTraceCodeBound_le_pow {D n : ℕ}
    (hn : 2 ≤ n) (hDn : D ≤ n) :
    (D + 1) * (2 * (D * n * n ^ 2) + 1) *
        (2 * n ^ 2 + 1) ^ D * n ^ D ≤
      n ^ weakTracePolynomialExponent D := by
  by_cases hD0 : D = 0
  · subst D
    simp only [zero_add, zero_mul, one_mul, pow_zero, add_zero,
      weakTracePolynomialExponent, Nat.reduceAdd]
    exact Nat.one_le_pow 14 n (by omega)
  have hD1 : D + 1 ≤ n ^ 2 := add_one_le_sq hn hDn
  have hDn2 : D * n ≤ n ^ 2 := by
    calc
      D * n ≤ n * n := Nat.mul_le_mul_right n hDn
      _ = n ^ 2 := by ring
  have hx : D * n * n ^ 2 ≤ n ^ 4 := by
    calc
      D * n * n ^ 2 ≤ n ^ 2 * n ^ 2 :=
        Nat.mul_le_mul_right (n ^ 2) hDn2
      _ = n ^ 4 := by rw [← pow_add]
  have hxPos : 2 ≤ D * n * n ^ 2 := by
    have hDnPos : 2 ≤ D * n :=
      hn.trans (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hD0))
    exact hDnPos.trans (Nat.le_mul_of_pos_right (D * n) (by positivity))
  have hoffset : 2 * (D * n * n ^ 2) + 1 ≤ n ^ 12 := by
    calc
      2 * (D * n * n ^ 2) + 1 ≤ (D * n * n ^ 2) ^ 3 :=
        two_mul_add_one_le_cube hxPos
      _ ≤ (n ^ 4) ^ 3 := Nat.pow_le_pow_left hx 3
      _ = n ^ 12 := by rw [← pow_mul]
  have hdiff : 2 * n ^ 2 + 1 ≤ n ^ 6 := by
    calc
      2 * n ^ 2 + 1 ≤ (n ^ 2) ^ 3 :=
        two_mul_add_one_le_cube (by nlinarith)
      _ = n ^ 6 := by rw [← pow_mul]
  calc
    (D + 1) * (2 * (D * n * n ^ 2) + 1) *
        (2 * n ^ 2 + 1) ^ D * n ^ D ≤
      n ^ 2 * n ^ 12 * (n ^ 6) ^ D * n ^ D := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hD1 hoffset)
          (Nat.pow_le_pow_left hdiff D)) le_rfl
    _ = n ^ weakTracePolynomialExponent D := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      simp only [weakTracePolynomialExponent]
      omega

/-- A fixed dimension-dependent exponent bounding the union of weak and
generated-span obstacle families. -/
def obstaclePolynomialExponent (D : ℕ) : ℕ :=
  weakTracePolynomialExponent D + generatedSpanPolynomialExponent D + 2

/-- Source-facing polynomial obstacle count for centered canonical
preprocessing coordinates. -/
theorem canonicalObstaclePolynomialBound_centered
    {B W : Finset ℤ} {D n : ℕ} {relevant : Finset ℕ}
    (hn : 2 ≤ n) (hDn : D ≤ n)
    (hBW : B ⊆ W) (hzeroW : 0 ∈ W)
    (hW : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hrank : ∀ d ∈ relevant, d ≤ D) :
    CanonicalObstaclePolynomialBound B (Stability.minimalBoxFamily W)
      D (n ^ 2) relevant
      (Stability.centeredMinimalIdentificationFamily hproper)
      n (obstaclePolynomialExponent D) := by
  classical
  have hWsubset : W ⊆ Finset.Ico (0 : ℤ) n := by
    intro z hz
    exact Finset.mem_Ico.mpr (hW z hz)
  have hWcard : W.card ≤ n := by
    have h := Finset.card_le_card hWsubset
    simpa using h
  have hBcard : B.card ≤ n :=
    (Finset.card_le_card hBW).trans hWcard
  have hbox : ∀ d, 0 < d → d ≤ D →
      (Stability.minimalBoxFamily W d).volume ≤ n := by
    intro d hd _hdD
    exact minimalBoxFamily_volume_le hzeroW hW hd
  have hweak : Fintype.card
      (WeakTraceIndex B (Stability.minimalBoxFamily W) D (n ^ 2)) ≤
      n ^ weakTracePolynomialExponent D := by
    exact (card_weakTraceIndex_le_code hbox (by omega)).trans
      (weakTraceCodeBound_le_pow hn hDn)
  have hspan : Fintype.card
      (FinsetDistinctSpanIndex B relevant
        (Stability.centeredMinimalIdentificationFamily hproper)) ≤
      n ^ (generatedSpanPolynomialExponent D + 1) := by
    apply card_finsetDistinctSpanIndex_le_pow B relevant
      (Stability.centeredMinimalIdentificationFamily hproper)
      hn hDn hBcard (fun d hd ↦ hproper.positive hd) hrank
    intro d hd a ha j
    exact abs_centeredMinimalIdentificationFamily_le hBW hzeroW hW
      hproper hd ha j
  unfold CanonicalObstaclePolynomialBound
  rw [Fintype.card_sum]
  let E := weakTracePolynomialExponent D +
    generatedSpanPolynomialExponent D + 1
  have hweakE : n ^ weakTracePolynomialExponent D ≤ n ^ E :=
    Nat.pow_le_pow_right (by omega) (by
      dsimp only [E]
      omega)
  have hspanE : n ^ (generatedSpanPolynomialExponent D + 1) ≤ n ^ E :=
    Nat.pow_le_pow_right (by omega) (by
      dsimp only [E]
      omega)
  calc
    Fintype.card (WeakTraceIndex B (Stability.minimalBoxFamily W) D (n ^ 2)) +
        Fintype.card (FinsetDistinctSpanIndex B relevant
          (Stability.centeredMinimalIdentificationFamily hproper)) ≤
      n ^ E + n ^ E := Nat.add_le_add (hweak.trans hweakE)
        (hspan.trans hspanE)
    _ = 2 * n ^ E := by omega
    _ ≤ n * n ^ E := Nat.mul_le_mul_right (n ^ E) hn
    _ = n ^ obstaclePolynomialExponent D := by
      have hE : obstaclePolynomialExponent D = E + 1 := by
        simp only [obstaclePolynomialExponent, E]
      rw [hE]
      exact (pow_succ' n E).symm

end

end Erdos186.CFP.RandomPartition
