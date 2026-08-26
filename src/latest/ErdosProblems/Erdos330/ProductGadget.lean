/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.AffineSafePairs

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Product-coordinate CRT gadget pieces for Erdős Problem 330

This file defines the product-coordinate version of the finite CRT gadget and
proves the first structural inclusion: the constructed set `T` lies inside the
allowed box.
-/

namespace Erdos330

open scoped Pointwise

abbrev ProductSpace {ι : Type*} (p0 : ℕ) (p : ι → ℕ) :=
  ZMod p0 × (∀ i : ι, ZMod (p i))

def productAllowed {ι : Type*} (p0 : ℕ) (p : ι → ℕ)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i)) : Set (ProductSpace p0 p) :=
  {x | x.1 ≠ α ∧ x.2 ∈ shiftedNonzeroBox p β}

def productPrivateSlice {ι : Type*} (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) : Set (ProductSpace p0 p) :=
  {z | z.1 = h + h ∧ affineDoubleNormalize p β z.2 ∉ coordinateTarget p e}

def productBase {ι : Type*} (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (h : ZMod p0) (U : Finset (ZMod p0)) (β : ∀ i : ι, ZMod (p i)) :
    Set (ProductSpace p0 p) :=
  {x | x.1 ∈ shiftedQRDelete p0 h U ∧ x.2 ∈ shiftedNonzeroBox p β}

def productLeftCorrection {ι : Type*} [Fintype ι] (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u : ZMod p0) (ν : Bool) : Set (ProductSpace p0 p) :=
  {x | x.1 = h + u ∧ x.2 ∈ affineLeftSafeSet p β e data ν (safeLeftThreshold ι)}

def productRightCorrection {ι : Type*} [Fintype ι] (p0 : ℕ) (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u : ZMod p0) (ν : Bool) : Set (ProductSpace p0 p) :=
  {x | x.1 = h - u ∧ x.2 ∈ affineRightSafeSet p β e data ν (safeRightThreshold ι)}

def productT {ι : Type*} [Fintype ι] (p0 : ℕ) [NeZero p0]
    (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) : Set (ProductSpace p0 p) :=
  productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β ∪
    (productLeftCorrection p0 p β e data h u1 true ∪
      (productRightCorrection p0 p β e data h u1 true ∪
        (productLeftCorrection p0 p β e data h u2 false ∪
          productRightCorrection p0 p β e data h u2 false)))

noncomputable def productCRTAddEquiv {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ)
    (hcop0 : Nat.Coprime p0 (∏ i, p i))
    (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j)) :
    ZMod (p0 * ∏ i, p i) ≃+ ProductSpace p0 p :=
  (ZMod.chineseRemainder hcop0).toAddEquiv.trans
    (AddEquiv.prodCongr (AddEquiv.refl (ZMod p0))
      (zmodProdEquivPi p hcop).toAddEquiv)

theorem productCRTAddEquiv_fst_natCast {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ)
    (hcop0 : Nat.Coprime p0 (∏ i, p i))
    (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j))
    (a : ℕ) :
    ((productCRTAddEquiv p0 p hcop0 hcop) (a : ZMod (p0 * ∏ i, p i))).1 =
      (a : ZMod p0) := by
  simp [productCRTAddEquiv, AddEquiv.prodCongr]

theorem productCRTAddEquiv_snd_natCast {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ)
    (hcop0 : Nat.Coprime p0 (∏ i, p i))
    (hcop : Pairwise fun i j => Nat.Coprime (p i) (p j))
    (a : ℕ) (i : ι) :
    ((productCRTAddEquiv p0 p hcop0 hcop) (a : ZMod (p0 * ∏ i, p i))).2 i =
      (a : ZMod (p i)) := by
  simp [productCRTAddEquiv, AddEquiv.prodCongr, zmodProdEquivPi]

theorem productBase_subset_allowed {ι : Type*} (p0 : ℕ) [NeZero p0]
    (p : ι → ℕ) (α h : ZMod p0) (U : Finset (ZMod p0))
    (β : ∀ i : ι, ZMod (p i))
    (hQavoid : ∀ q ∈ shiftedQRDelete p0 h U, q ≠ α) :
    productBase p0 p h U β ⊆ productAllowed p0 p α β := by
  intro x hx
  exact ⟨hQavoid x.1 hx.1, hx.2⟩

lemma add_deleted_residue_ne_forbidden {p0 : ℕ} (α h u : ZMod p0)
    (hu : u ≠ α - h) : h + u ≠ α := by
  intro hhu
  apply hu
  linear_combination hhu

lemma sub_deleted_residue_ne_forbidden {p0 : ℕ} (α h u : ZMod p0)
    (hu : u ≠ -(α - h)) : h - u ≠ α := by
  intro hhu
  apply hu
  linear_combination -hhu

theorem productLeftCorrection_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ) (α h u : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ν : Bool) (hu : u ≠ α - h) :
    productLeftCorrection p0 p β e data h u ν ⊆ productAllowed p0 p α β := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hx.1]
    exact add_deleted_residue_ne_forbidden α h u hu
  · exact affineLeftSafeSet_subset_shiftedNonzeroBox p β e data ν (safeLeftThreshold ι) hx.2

theorem productRightCorrection_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ) (α h u : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ν : Bool) (hu : u ≠ -(α - h)) :
    productRightCorrection p0 p β e data h u ν ⊆ productAllowed p0 p α β := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [hx.1]
    exact sub_deleted_residue_ne_forbidden α h u hu
  · exact affineRightSafeSet_subset_shiftedNonzeroBox p β e data ν (safeRightThreshold ι) hx.2

theorem productT_subset_allowed {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ) (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (hu1_pos : u1 ≠ α - h) (hu2_pos : u2 ≠ α - h)
    (hu1_neg : u1 ≠ -(α - h)) (hu2_neg : u2 ≠ -(α - h))
    (hQavoid : ∀ q ∈ shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)), q ≠ α) :
    productT p0 p β e data h u1 u2 ⊆ productAllowed p0 p α β := by
  intro x hx
  rcases hx with hbase | hrest
  · exact productBase_subset_allowed p0 p α h ({u1, u2} : Finset (ZMod p0)) β hQavoid
      hbase
  rcases hrest with hleft1 | hrest
  · exact productLeftCorrection_subset_allowed p0 p α h u1 β e data true hu1_pos hleft1
  rcases hrest with hright1 | hrest
  · exact productRightCorrection_subset_allowed p0 p α h u1 β e data true hu1_neg hright1
  rcases hrest with hleft2 | hright2
  · exact productLeftCorrection_subset_allowed p0 p α h u2 β e data false hu2_pos hleft2
  · exact productRightCorrection_subset_allowed p0 p α h u2 β e data false hu2_neg hright2

theorem productBase_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inl hx

theorem productLeftCorrection_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productLeftCorrection p0 p β e data h u1 true ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inl hx)

theorem productRightCorrection_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productRightCorrection p0 p β e data h u1 true ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inl hx))

theorem productLeftCorrectionTwo_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productLeftCorrection p0 p β e data h u2 false ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inr (Or.inl hx)))

theorem productRightCorrectionTwo_subset_productT {ι : Type*} [Fintype ι]
    (p0 : ℕ) [NeZero p0] (p : ι → ℕ)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    productRightCorrection p0 p β e data h u2 false ⊆
      productT p0 p β e data h u1 u2 := by
  intro x hx
  exact Or.inr (Or.inr (Or.inr (Or.inr hx)))

theorem productAllowed_add_productBase_eq_univ {ι : Type*}
    [Fintype ι] (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (hp7 : ∀ i, 7 ≤ p i)
    (α h : ZMod p0) (U : Finset (ZMod p0)) (hUcard : U.card ≤ 2)
    (β : ∀ i : ι, ZMod (p i)) :
    ((productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productBase p0 p h U β : Set (ProductSpace p0 p))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hsel := allowed_add_shiftedQRDelete_eq_univ hp0_3 hp0_23 h α U hUcard
  have hsel_mem : z.1 ∈ (Set.univ \ ({α} : Set (ZMod p0))) +
      (shiftedQRDelete p0 h U : Set (ZMod p0)) := by
    rw [hsel]
    exact Set.mem_univ z.1
  have hrest := shiftedNonzeroBox_add_self_eq_univ p hp7 β
  have hrest_mem : z.2 ∈ (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
      (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) := by
    rw [hrest]
    exact Set.mem_univ z.2
  rcases hsel_mem with ⟨a0, ha0, t0, ht0, h0sum⟩
  rcases hrest_mem with ⟨a', ha', t', ht', hrestsum⟩
  refine ⟨(a0, a'), ?_, (t0, t'), ?_, ?_⟩
  · exact ⟨ha0.2, ha'⟩
  · exact ⟨ht0, ht'⟩
  · ext <;> simp [h0sum, hrestsum]

theorem productAllowed_add_self_eq_univ {ι : Type*} [Fintype ι]
    (p0 : ℕ) [Fact p0.Prime] (hp0_7 : 7 ≤ p0)
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i)) :
    ((productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productAllowed p0 p α β : Set (ProductSpace p0 p))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  let target0 : ZMod p0 := z.1 - (α + α)
  let pair0 := nonzeroAddPairZMod p0 hp0_7 target0
  have hrest : z.2 ∈
      (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
        (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) := by
    rw [shiftedNonzeroBox_add_self_eq_univ p hp7 β]
    exact Set.mem_univ z.2
  rcases hrest with ⟨x, hx, y, hy, hxy⟩
  refine ⟨(α + pair0.left, x), ?_, (α + pair0.right, y), ?_, ?_⟩
  · refine ⟨?_, hx⟩
    intro hbad
    exact pair0.left_ne_zero (by linear_combination hbad)
  · refine ⟨?_, hy⟩
    intro hbad
    exact pair0.right_ne_zero (by linear_combination hbad)
  · ext i <;> dsimp
    · have hsum := pair0.sum_eq
      dsimp [target0] at hsum
      linear_combination hsum
    · exact congrFun hxy i

theorem productAllowed_add_productT_eq_univ {ι : Type*}
    [Fintype ι] (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (hp7 : ∀ i, 7 ≤ p i)
    (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  have hbase_univ := productAllowed_add_productBase_eq_univ p p0 hp0_3 hp0_23 hp7 α h
    ({u1, u2} : Finset (ZMod p0)) (by exact Finset.card_le_two) β
  have hzbase : z ∈ (productAllowed p0 p α β : Set (ProductSpace p0 p)) +
      (productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β :
        Set (ProductSpace p0 p)) := by
    rw [hbase_univ]
    exact Set.mem_univ z
  rcases hzbase with ⟨a, ha, t, ht, hsum⟩
  refine ⟨a, ha, t, ?_, hsum⟩
  exact productBase_subset_productT p0 p β e data h u1 u2 ht

lemma shiftedQRDelete_add_leftCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huQR : u ∈ QR p0) (hx : x ∈ shiftedQRDelete p0 h U) :
    x + (h + u) ≠ h + h := by
  intro hsum
  have hx_eq : x = h - u := by linear_combination hsum
  exact notMem_shiftedQRDelete_sub_QR hp3 h u U huQR (by simpa [hx_eq] using hx)

lemma shiftedQRDelete_add_rightCorrection_ne_tau {p0 : ℕ} [NeZero p0]
    (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huU : u ∈ U) (hx : x ∈ shiftedQRDelete p0 h U) :
    x + (h - u) ≠ h + h := by
  intro hsum
  have hx_eq : x = h + u := by linear_combination hsum
  exact notMem_shiftedQRDelete_add_deleted h u U huU (by simpa [hx_eq] using hx)

lemma leftCorrection_add_shiftedQRDelete_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huQR : u ∈ QR p0) (hx : x ∈ shiftedQRDelete p0 h U) :
    (h + u) + x ≠ h + h := by
  intro hsum
  exact shiftedQRDelete_add_leftCorrection_ne_tau hp3 h u x U huQR hx
    (by simpa [add_comm] using hsum)

lemma rightCorrection_add_shiftedQRDelete_ne_tau {p0 : ℕ} [NeZero p0]
    (h u x : ZMod p0) (U : Finset (ZMod p0))
    (huU : u ∈ U) (hx : x ∈ shiftedQRDelete p0 h U) :
    (h - u) + x ≠ h + h := by
  intro hsum
  exact shiftedQRDelete_add_rightCorrection_ne_tau h u x U huU hx
    (by simpa [add_comm] using hsum)

lemma leftCorrection_add_leftCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u v : ZMod p0) (huQR : u ∈ QR p0) (hvQR : v ∈ QR p0) :
    (h + u) + (h + v) ≠ h + h := by
  intro hsum
  have huv : u + v = 0 := by linear_combination hsum
  exact QR_add_ne_zero hp3 huQR hvQR huv

lemma rightCorrection_add_rightCorrection_ne_tau {p0 : ℕ} [Fact p0.Prime] [NeZero p0]
    (hp3 : p0 % 4 = 3) (h u v : ZMod p0) (huQR : u ∈ QR p0) (hvQR : v ∈ QR p0) :
    (h - u) + (h - v) ≠ h + h := by
  intro hsum
  have huv : u + v = 0 := by linear_combination -hsum
  exact QR_add_ne_zero hp3 huQR hvQR huv

lemma leftCorrection_add_rightCorrection_ne_tau_of_ne {p0 : ℕ}
    (h u v : ZMod p0) (huv : u ≠ v) :
    (h + u) + (h - v) ≠ h + h := by
  intro hsum
  apply huv
  linear_combination hsum

lemma rightCorrection_add_leftCorrection_ne_tau_of_ne {p0 : ℕ}
    (h u v : ZMod p0) (huv : u ≠ v) :
    (h - u) + (h + v) ≠ h + h := by
  intro hsum
  apply huv
  linear_combination -hsum

theorem product_compl_private_subset_T_add_T {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (p0 : ℕ) [NeZero p0]
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0)
    (hbase_sum : ((shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) :
          Set (ZMod p0)) +
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0))) =
      Set.univ \ ({h + h} : Set (ZMod p0))) :
    Set.univ \ productPrivateSlice p0 p β e h ⊆
      (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) +
        (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) := by
  classical
  intro z hz
  by_cases hzsel : z.1 = h + h
  · have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e := by
      by_contra hnot
      exact hz.2 ⟨hzsel, hnot⟩
    have haff := affineSafePair_sum_union_eq_coordinateTarget_preimage p hp7 β e data
    have hz2mem : z.2 ∈
        ((affineLeftSafeSet p β e data true (safeLeftThreshold ι) +
            affineRightSafeSet p β e data true (safeRightThreshold ι)) ∪
          (affineLeftSafeSet p β e data false (safeLeftThreshold ι) +
            affineRightSafeSet p β e data false (safeRightThreshold ι))) := by
      rw [haff]
      exact hcoord
    rcases hz2mem with htrue | hfalse
    · rcases htrue with ⟨x, hx, y, hy, hxy⟩
      refine ⟨(h + u1, x), ?_, (h - u1, y), ?_, ?_⟩
      · exact productLeftCorrection_subset_productT p0 p β e data h u1 u2 ⟨rfl, hx⟩
      · exact productRightCorrection_subset_productT p0 p β e data h u1 u2 ⟨rfl, hy⟩
      · ext i
        · simp [hzsel]
        · exact congrFun hxy i
    · rcases hfalse with ⟨x, hx, y, hy, hxy⟩
      refine ⟨(h + u2, x), ?_, (h - u2, y), ?_, ?_⟩
      · exact productLeftCorrectionTwo_subset_productT p0 p β e data h u1 u2 ⟨rfl, hx⟩
      · exact productRightCorrectionTwo_subset_productT p0 p β e data h u1 u2 ⟨rfl, hy⟩
      · ext i
        · simp [hzsel]
        · exact congrFun hxy i
  · have hsel_mem : z.1 ∈
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) +
          (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) := by
      rw [hbase_sum]
      exact ⟨Set.mem_univ z.1, by simpa using hzsel⟩
    have hrest := shiftedNonzeroBox_add_self_eq_univ p hp7 β
    have hrest_mem : z.2 ∈ (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
        (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) := by
      rw [hrest]
      exact Set.mem_univ z.2
    rcases hsel_mem with ⟨x0, hx0, y0, hy0, hxy0⟩
    rcases hrest_mem with ⟨x', hx', y', hy', hxy'⟩
    refine ⟨(x0, x'), ?_, (y0, y'), ?_, ?_⟩
    · exact productBase_subset_productT p0 p β e data h u1 u2 ⟨hx0, hx'⟩
    · exact productBase_subset_productT p0 p β e data h u1 u2 ⟨hy0, hy'⟩
    · ext <;> simp [hxy0, hxy']

theorem product_T_add_T_subset_compl_private {ι : Type*}
    [Fintype ι]
    (p : ι → ℕ)
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0)
    (hu1QR : u1 ∈ QR p0) (hu2QR : u2 ∈ QR p0) (hu12 : u1 ≠ u2)
    (hbase_sum : ((shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) :
          Set (ZMod p0)) +
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0))) =
      Set.univ \ ({h + h} : Set (ZMod p0))) :
    (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) +
        (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) ⊆
      Set.univ \ productPrivateSlice p0 p β e h := by
  classical
  rintro z ⟨x, hx, y, hy, hxy⟩
  refine ⟨Set.mem_univ z, ?_⟩
  rintro ⟨hzsel, hznotcoord⟩
  have hselxy : x.1 + y.1 = h + h := by
    have := congrArg Prod.fst hxy
    simpa [hzsel] using this
  have hrestxy : x.2 + y.2 = z.2 := by
    have := congrArg Prod.snd hxy
    simpa using this
  have hu1U : u1 ∈ ({u1, u2} : Finset (ZMod p0)) := by simp
  have hu2U : u2 ∈ ({u1, u2} : Finset (ZMod p0)) := by simp
  have hu21 : u2 ≠ u1 := fun h21 => hu12 h21.symm
  have hBB
      (hxB : x ∈ productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β)
      (hyB : y ∈ productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β) : False := by
    have hmem : x.1 + y.1 ∈
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) +
          (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0)) :=
      ⟨x.1, hxB.1, y.1, hyB.1, rfl⟩
    rw [hbase_sum] at hmem
    exact hmem.2 (by simp [hselxy])
  have hLRtrue
      (hxL : x ∈ productLeftCorrection p0 p β e data h u1 true)
      (hyR : y ∈ productRightCorrection p0 p β e data h u1 true) : False := by
    have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e :=
      affineLeftRight_sum_subset_coordinateTarget p β e data true
        ⟨x.2, hxL.2, y.2, hyR.2, hrestxy⟩
    exact hznotcoord hcoord
  have hRLtrue
      (hxR : x ∈ productRightCorrection p0 p β e data h u1 true)
      (hyL : y ∈ productLeftCorrection p0 p β e data h u1 true) : False := by
    have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e :=
      affineRightLeft_sum_subset_coordinateTarget p β e data true
        ⟨x.2, hxR.2, y.2, hyL.2, hrestxy⟩
    exact hznotcoord hcoord
  have hLRfalse
      (hxL : x ∈ productLeftCorrection p0 p β e data h u2 false)
      (hyR : y ∈ productRightCorrection p0 p β e data h u2 false) : False := by
    have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e :=
      affineLeftRight_sum_subset_coordinateTarget p β e data false
        ⟨x.2, hxL.2, y.2, hyR.2, hrestxy⟩
    exact hznotcoord hcoord
  have hRLfalse
      (hxR : x ∈ productRightCorrection p0 p β e data h u2 false)
      (hyL : y ∈ productLeftCorrection p0 p β e data h u2 false) : False := by
    have hcoord : affineDoubleNormalize p β z.2 ∈ coordinateTarget p e :=
      affineRightLeft_sum_subset_coordinateTarget p β e data false
        ⟨x.2, hxR.2, y.2, hyL.2, hrestxy⟩
    exact hznotcoord hcoord
  rcases hx with hxB | hx
  · rcases hy with hyB | hy
    · exact hBB hxB hyB
    rcases hy with hyL1 | hy
    · exact shiftedQRDelete_add_leftCorrection_ne_tau hp0_3 h u1 x.1
        ({u1, u2} : Finset (ZMod p0)) hu1QR hxB.1
        (by simpa [hyL1.1] using hselxy)
    rcases hy with hyR1 | hy
    · exact shiftedQRDelete_add_rightCorrection_ne_tau h u1 x.1
        ({u1, u2} : Finset (ZMod p0)) hu1U hxB.1
        (by simpa [hyR1.1] using hselxy)
    rcases hy with hyL2 | hyR2
    · exact shiftedQRDelete_add_leftCorrection_ne_tau hp0_3 h u2 x.1
        ({u1, u2} : Finset (ZMod p0)) hu2QR hxB.1
        (by simpa [hyL2.1] using hselxy)
    · exact shiftedQRDelete_add_rightCorrection_ne_tau h u2 x.1
        ({u1, u2} : Finset (ZMod p0)) hu2U hxB.1
        (by simpa [hyR2.1] using hselxy)
  rcases hx with hxL1 | hx
  · rcases hy with hyB | hy
    · exact leftCorrection_add_shiftedQRDelete_ne_tau hp0_3 h u1 y.1
        ({u1, u2} : Finset (ZMod p0)) hu1QR hyB.1
        (by simpa [hxL1.1] using hselxy)
    rcases hy with hyL1 | hy
    · exact leftCorrection_add_leftCorrection_ne_tau hp0_3 h u1 u1 hu1QR hu1QR
        (by simpa [hxL1.1, hyL1.1] using hselxy)
    rcases hy with hyR1 | hy
    · exact hLRtrue hxL1 hyR1
    rcases hy with hyL2 | hyR2
    · exact leftCorrection_add_leftCorrection_ne_tau hp0_3 h u1 u2 hu1QR hu2QR
        (by simpa [hxL1.1, hyL2.1] using hselxy)
    · exact leftCorrection_add_rightCorrection_ne_tau_of_ne h u1 u2 hu12
        (by simpa [hxL1.1, hyR2.1] using hselxy)
  rcases hx with hxR1 | hx
  · rcases hy with hyB | hy
    · exact rightCorrection_add_shiftedQRDelete_ne_tau h u1 y.1
        ({u1, u2} : Finset (ZMod p0)) hu1U hyB.1
        (by simpa [hxR1.1] using hselxy)
    rcases hy with hyL1 | hy
    · exact hRLtrue hxR1 hyL1
    rcases hy with hyR1 | hy
    · exact rightCorrection_add_rightCorrection_ne_tau hp0_3 h u1 u1 hu1QR hu1QR
        (by simpa [hxR1.1, hyR1.1] using hselxy)
    rcases hy with hyL2 | hyR2
    · exact rightCorrection_add_leftCorrection_ne_tau_of_ne h u1 u2 hu12
        (by simpa [hxR1.1, hyL2.1] using hselxy)
    · exact rightCorrection_add_rightCorrection_ne_tau hp0_3 h u1 u2 hu1QR hu2QR
        (by simpa [hxR1.1, hyR2.1] using hselxy)
  rcases hx with hxL2 | hxR2
  · rcases hy with hyB | hy
    · exact leftCorrection_add_shiftedQRDelete_ne_tau hp0_3 h u2 y.1
        ({u1, u2} : Finset (ZMod p0)) hu2QR hyB.1
        (by simpa [hxL2.1] using hselxy)
    rcases hy with hyL1 | hy
    · exact leftCorrection_add_leftCorrection_ne_tau hp0_3 h u2 u1 hu2QR hu1QR
        (by simpa [hxL2.1, hyL1.1] using hselxy)
    rcases hy with hyR1 | hy
    · exact leftCorrection_add_rightCorrection_ne_tau_of_ne h u2 u1 hu21
        (by simpa [hxL2.1, hyR1.1] using hselxy)
    rcases hy with hyL2 | hyR2
    · exact leftCorrection_add_leftCorrection_ne_tau hp0_3 h u2 u2 hu2QR hu2QR
        (by simpa [hxL2.1, hyL2.1] using hselxy)
    · exact hLRfalse hxL2 hyR2
  · rcases hy with hyB | hy
    · exact rightCorrection_add_shiftedQRDelete_ne_tau h u2 y.1
        ({u1, u2} : Finset (ZMod p0)) hu2U hyB.1
        (by simpa [hxR2.1] using hselxy)
    rcases hy with hyL1 | hy
    · exact rightCorrection_add_leftCorrection_ne_tau_of_ne h u2 u1 hu21
        (by simpa [hxR2.1, hyL1.1] using hselxy)
    rcases hy with hyR1 | hy
    · exact rightCorrection_add_rightCorrection_ne_tau hp0_3 h u2 u1 hu2QR hu1QR
        (by simpa [hxR2.1, hyR1.1] using hselxy)
    rcases hy with hyL2 | hyR2
    · exact hRLfalse hxR2 hyL2
    · exact rightCorrection_add_rightCorrection_ne_tau hp0_3 h u2 u2 hu2QR hu2QR
        (by simpa [hxR2.1, hyR2.1] using hselxy)

theorem product_T_add_T_eq_compl_private {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (p0 : ℕ) [Fact p0.Prime] [NeZero p0]
    (hp0_3 : p0 % 4 = 3)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0)
    (hu1QR : u1 ∈ QR p0) (hu2QR : u2 ∈ QR p0) (hu12 : u1 ≠ u2)
    (hbase_sum : ((shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) :
          Set (ZMod p0)) +
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0))) =
      Set.univ \ ({h + h} : Set (ZMod p0))) :
    ((productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p)) +
        (productT p0 p β e data h u1 u2 : Set (ProductSpace p0 p))) =
      Set.univ \ productPrivateSlice p0 p β e h := by
  apply Set.Subset.antisymm
  · exact product_T_add_T_subset_compl_private p p0 hp0_3 β e data h u1 u2 hu1QR
      hu2QR hu12 hbase_sum
  · exact product_compl_private_subset_T_add_T p hp7 p0 β e data h u1 u2 hbase_sum

noncomputable def crtProductAllowedFinset {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i)) : Finset (ZMod M) :=
  addEquivPreimageFinset φ (productAllowed p0 p α β)

noncomputable def crtProductTFinset {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) : Finset (ZMod M) :=
  addEquivPreimageFinset φ (productT p0 p β e data h u1 u2)

noncomputable def crtProductTbaseFinset {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (β : ∀ i : ι, ZMod (p i)) (h u1 u2 : ZMod p0) : Finset (ZMod M) :=
  addEquivPreimageFinset φ (productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β)

noncomputable def crtProductPstarFinset {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) : Finset (ZMod M) :=
  addEquivTranslatePreimageFinset a φ (productPrivateSlice p0 p β e h)

theorem crtProductTbase_subset_T {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0) :
    crtProductTbaseFinset M p0 p φ β h u1 u2 ⊆
      crtProductTFinset M p0 p φ β e data h u1 u2 := by
  simpa [crtProductTbaseFinset, crtProductTFinset] using
    (addEquivPreimageFinset_subset (φ := φ)
      (productBase_subset_productT p0 p β e data h u1 u2))

theorem crtProductT_subset_allowed {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (hu1_pos : u1 ≠ α - h) (hu2_pos : u2 ≠ α - h)
    (hu1_neg : u1 ≠ -(α - h)) (hu2_neg : u2 ≠ -(α - h))
    (hQavoid : ∀ q ∈ shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)), q ≠ α) :
    crtProductTFinset M p0 p φ β e data h u1 u2 ⊆
      crtProductAllowedFinset M p0 p φ α β := by
  simpa [crtProductTFinset, crtProductAllowedFinset] using
    (addEquivPreimageFinset_subset (φ := φ)
      (productT_subset_allowed p0 p α h u1 u2 β e data hu1_pos hu2_pos
        hu1_neg hu2_neg hQavoid))

theorem crtProductPstar_subset_allowed_of_subset {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0)
    (hsubset : {x : ZMod M | φ (a + x) ∈ productPrivateSlice p0 p β e h} ⊆
      {x : ZMod M | φ x ∈ productAllowed p0 p α β}) :
    crtProductPstarFinset M p0 p φ a β e h ⊆
      crtProductAllowedFinset M p0 p φ α β := by
  intro x hx
  change x ∈ (crtProductPstarFinset M p0 p φ a β e h : Set (ZMod M)) at hx
  rw [crtProductPstarFinset, coe_addEquivTranslatePreimageFinset] at hx
  change x ∈ (crtProductAllowedFinset M p0 p φ α β : Set (ZMod M))
  rw [crtProductAllowedFinset, coe_addEquivPreimageFinset]
  exact hsubset hx

theorem productPrivateSlice_translate_subset_allowed {ι : Type*}
    (p0 : ℕ) (p : ι → ℕ)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0)
    (a : ProductSpace p0 p)
    (ha1 : a.1 = α) (he : e = affineNormalize p β a.2)
    (hτ_ne : h + h ≠ α + α) :
    {x : ProductSpace p0 p | a + x ∈ productPrivateSlice p0 p β e h} ⊆
      productAllowed p0 p α β := by
  intro x hx
  rcases hx with ⟨hxsel, hxnotcoord⟩
  refine ⟨?_, ?_⟩
  · intro hxα
    have hαα : α + α = h + h := by
      simpa [ha1, hxα] using hxsel
    exact hτ_ne hαα.symm
  · intro i hxi
    apply hxnotcoord
    refine ⟨i, ?_⟩
    rw [he]
    simp [affineDoubleNormalize, affineNormalize, hxi]

theorem crtProductPstar_subset_allowed {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0)
    (ha1 : (φ a).1 = α) (he : e = affineNormalize p β (φ a).2)
    (hτ_ne : h + h ≠ α + α) :
    crtProductPstarFinset M p0 p φ a β e h ⊆
      crtProductAllowedFinset M p0 p φ α β := by
  refine crtProductPstar_subset_allowed_of_subset M p0 p φ a α β e h ?_
  intro x hx
  exact productPrivateSlice_translate_subset_allowed p0 p α β e h (φ a) ha1 he hτ_ne
    (by simpa [φ.map_add] using hx)

theorem crtProductAllowed_selected_ne {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i))
    {x : ZMod M} (hx : x ∈ crtProductAllowedFinset M p0 p φ α β) :
    (φ x).1 ≠ α := by
  change x ∈ (crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) at hx
  rw [crtProductAllowedFinset, coe_addEquivPreimageFinset] at hx
  exact hx.1

theorem crtProductPstar_selected_eq {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] (p : ι → ℕ)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0)
    (ha1 : (φ a).1 = α)
    {r : ZMod M} (hr : r ∈ crtProductPstarFinset M p0 p φ a β e h) :
    (φ r).1 = h + h - α := by
  change r ∈ (crtProductPstarFinset M p0 p φ a β e h : Set (ZMod M)) at hr
  rw [crtProductPstarFinset, coe_addEquivTranslatePreimageFinset] at hr
  have hsum : (φ a).1 + (φ r).1 = h + h := by
    simpa [φ.map_add] using hr.1
  linear_combination hsum - ha1

theorem crtProduct_T_add_T_compl_private {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (h u1 u2 : ZMod p0)
    (hu1QR : u1 ∈ QR p0) (hu2QR : u2 ∈ QR p0) (hu12 : u1 ≠ u2)
    (hbase_sum : ((shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) :
          Set (ZMod p0)) +
        (shiftedQRDelete p0 h ({u1, u2} : Finset (ZMod p0)) : Set (ZMod p0))) =
      Set.univ \ ({h + h} : Set (ZMod p0))) :
    ((crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M)) +
        (crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M))) =
      Set.univ \ ((fun x : ZMod M => a + x) ''
        (crtProductPstarFinset M p0 p φ a β e h : Set (ZMod M))) := by
  simpa [crtProductTFinset, crtProductPstarFinset] using
    (addEquivPreimageFinset_add_eq_compl_translate_image φ a
      (productT p0 p β e data h u1 u2)
      (productT p0 p β e data h u1 u2)
      (productPrivateSlice p0 p β e h)
      (product_T_add_T_eq_compl_private p hp7 p0 hp0_3 β e data h u1 u2 hu1QR
        hu2QR hu12 hbase_sum))

theorem crtProduct_allowed_add_T_eq_univ {ι : Type*}
    [Fintype ι]
    (M p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α h u1 u2 : ZMod p0)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) +
        (crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M))) = Set.univ := by
  simpa [crtProductAllowedFinset, crtProductTFinset] using
    (addEquivPreimageFinset_add_eq_univ φ
      (productAllowed p0 p α β)
      (productT p0 p β e data h u1 u2)
      (productAllowed_add_productT_eq_univ p p0 hp0_3 hp0_23 hp7 α h u1 u2 β e data))

theorem crtProduct_allowed_add_Tbase_eq_univ {ι : Type*}
    [Fintype ι]
    (M p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α h u1 u2 : ZMod p0)
    (β : ∀ i : ι, ZMod (p i)) :
    ((crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) +
        (crtProductTbaseFinset M p0 p φ β h u1 u2 : Set (ZMod M))) = Set.univ := by
  simpa [crtProductAllowedFinset, crtProductTbaseFinset] using
    (addEquivPreimageFinset_add_eq_univ φ
      (productAllowed p0 p α β)
      (productBase p0 p h ({u1, u2} : Finset (ZMod p0)) β)
      (productAllowed_add_productBase_eq_univ p p0 hp0_3 hp0_23 hp7 α h
        ({u1, u2} : Finset (ZMod p0)) (by exact Finset.card_le_two) β))

theorem crtProduct_allowed_add_allowed_eq_univ {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [Fact p0.Prime]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp0_7 : 7 ≤ p0) (hp7 : ∀ i, 7 ≤ p i)
    (φ : ZMod M ≃+ ProductSpace p0 p)
    (α : ZMod p0) (β : ∀ i : ι, ZMod (p i)) :
    ((crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) +
      (crtProductAllowedFinset M p0 p φ α β : Set (ZMod M))) = Set.univ := by
  simpa [crtProductAllowedFinset] using
    (addEquivPreimageFinset_add_eq_univ (φ := φ)
      (A := productAllowed p0 p α β) (B := productAllowed p0 p α β)
      (productAllowed_add_self_eq_univ p0 hp0_7 p hp7 α β))

theorem productPrivateSlice_card_eq_nonselected {ι : Type*}
    (p0 : ℕ) [Fintype (ZMod p0)]
    (p : ι → ℕ) [Fintype (∀ i : ι, ZMod (p i))]
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) :
    (setFiniteFinset (productPrivateSlice p0 p β e h)).card =
      (setFiniteFinset ({y : ∀ i : ι, ZMod (p i) |
        affineDoubleNormalize p β y ∉ coordinateTarget p e})).card := by
  simpa [productPrivateSlice] using
    (setFiniteFinset_prod_singleton_card (α := ZMod p0)
      (β := ∀ i : ι, ZMod (p i)) (h + h)
      ({y : ∀ i : ι, ZMod (p i) | affineDoubleNormalize p β y ∉ coordinateTarget p e}))

theorem crtProductPstarFinset_card_eq_productPrivateSlice {ι : Type*} [Fintype ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0]
    (p : ι → ℕ) [Fintype (ProductSpace p0 p)]
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) :
    (crtProductPstarFinset M p0 p φ a β e h).card =
      (setFiniteFinset (productPrivateSlice p0 p β e h)).card := by
  rw [crtProductPstarFinset, addEquivTranslatePreimageFinset_card_eq_preimage,
    addEquivPreimageFinset_card_eq]

theorem affineDoubleNormalize_not_coordinateTarget_card_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [(i : ι) → Fintype (ZMod (p i))]
    (β e : ∀ i : ι, ZMod (p i)) :
    (setFiniteFinset ({y : ∀ i : ι, ZMod (p i) |
        affineDoubleNormalize p β y ∉ coordinateTarget p e})).card =
      (setFiniteFinset (Set.univ \ coordinateTarget p e)).card := by
  classical
  refine Finset.card_bij (fun y _ => affineDoubleNormalize p β y) ?_ ?_ ?_
  · intro y hy
    rw [mem_setFiniteFinset]
    rw [mem_setFiniteFinset] at hy
    exact ⟨Set.mem_univ _, hy⟩
  · intro x _ y _ hxy
    funext i
    have hi := congrFun hxy i
    dsimp [affineDoubleNormalize] at hi
    linear_combination hi
  · intro z hz
    refine ⟨fun i => z i + (β i + β i), ?_, ?_⟩
    · rw [mem_setFiniteFinset]
      rw [mem_setFiniteFinset] at hz
      intro hcoord
      apply hz.2
      rcases hcoord with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simpa [affineDoubleNormalize] using hi
    · funext i
      simp [affineDoubleNormalize]

theorem noncoordinate_card_eq_prod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [(i : ι) → Fintype (ZMod (p i))]
    (e : ∀ i : ι, ZMod (p i)) :
    (setFiniteFinset (Set.univ \ coordinateTarget p e)).card = ∏ i, (p i - 1) := by
  classical
  have hset : Set.univ \ coordinateTarget p e =
      {z : ∀ i : ι, ZMod (p i) | ∀ i, z i ≠ e i} := by
    ext z
    simp [coordinateTarget]
  rw [hset]
  have hfin : setFiniteFinset ({z : ∀ i : ι, ZMod (p i) | ∀ i, z i ≠ e i}) =
      Fintype.piFinset (fun i => (Finset.univ.erase (e i) : Finset (ZMod (p i)))) := by
    ext z
    rw [mem_setFiniteFinset, Fintype.mem_piFinset]
    simp
  rw [hfin, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [Finset.card_erase_of_mem]
  · rw [Finset.card_univ, ZMod.card]
  · exact Finset.mem_univ (e i)

theorem productPrivateSlice_card_eq_prod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p0 : ℕ) [Fintype (ZMod p0)]
    (p : ι → ℕ) [(i : ι) → Fintype (ZMod (p i))]
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) :
    (setFiniteFinset (productPrivateSlice p0 p β e h)).card = ∏ i, (p i - 1) := by
  calc
    (setFiniteFinset (productPrivateSlice p0 p β e h)).card =
        (setFiniteFinset ({y : ∀ i : ι, ZMod (p i) |
          affineDoubleNormalize p β y ∉ coordinateTarget p e})).card :=
      productPrivateSlice_card_eq_nonselected p0 p β e h
    _ = (setFiniteFinset (Set.univ \ coordinateTarget p e)).card :=
      affineDoubleNormalize_not_coordinateTarget_card_eq p β e
    _ = ∏ i, (p i - 1) := noncoordinate_card_eq_prod p e

theorem crtProductPstarFinset_card_eq_prod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] [Fintype (ZMod p0)]
    (p : ι → ℕ) [(i : ι) → Fintype (ZMod (p i))]
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0) :
    (crtProductPstarFinset M p0 p φ a β e h).card = ∏ i, (p i - 1) := by
  calc
    (crtProductPstarFinset M p0 p φ a β e h).card =
        (setFiniteFinset (productPrivateSlice p0 p β e h)).card :=
      crtProductPstarFinset_card_eq_productPrivateSlice M p0 p φ a β e h
    _ = ∏ i, (p i - 1) := productPrivateSlice_card_eq_prod p0 p β e h

theorem real_prod_density_formula {ι : Type*} [Fintype ι]
    (p0 : ℕ) (p : ι → ℕ) (M : ℕ)
    (hp0 : 0 < p0) (hp : ∀ i, 0 < p i)
    (hM : M = p0 * ∏ i, p i) :
    ((∏ i, (p i - 1) : ℕ) : ℝ) / (M : ℝ) =
      (1 : ℝ) / (p0 : ℝ) * ∏ i, (1 - (1 : ℝ) / (p i : ℝ)) := by
  classical
  have hp0r : (p0 : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpr : ∀ i, (p i : ℝ) ≠ 0 := by
    intro i
    exact_mod_cast (hp i).ne'
  have hprod_cast : ((∏ i, (p i - 1) : ℕ) : ℝ) = ∏ i, ((p i : ℝ) - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _hi
    simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ p i from hp i))
  have hden_cast : ((∏ i, p i : ℕ) : ℝ) = ∏ i, (p i : ℝ) := by
    rw [Nat.cast_prod]
  have hfactor : (∏ i, (1 - (1 : ℝ) / (p i : ℝ))) =
      ∏ i, (((p i : ℝ) - 1) / (p i : ℝ)) := by
    apply Finset.prod_congr rfl
    intro i _hi
    field_simp [hpr i]
  rw [hM, Nat.cast_mul, hprod_cast, hden_cast, hfactor, Finset.prod_div_distrib]
  field_simp [hp0r]

theorem crtProductPstarFinset_card_real_formula {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M p0 : ℕ) [NeZero M] [NeZero p0] [Fintype (ZMod p0)]
    (p : ι → ℕ) [(i : ι) → Fintype (ZMod (p i))]
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (β e : ∀ i : ι, ZMod (p i)) (h : ZMod p0)
    (hp0 : 0 < p0) (hp : ∀ i, 0 < p i)
    (hM : M = p0 * ∏ i, p i) :
    ((crtProductPstarFinset M p0 p φ a β e h).card : ℝ) / (M : ℝ) =
      (1 : ℝ) / (p0 : ℝ) * ∏ i, (1 - (1 : ℝ) / (p i : ℝ)) := by
  rw [crtProductPstarFinset_card_eq_prod]
  exact real_prod_density_formula p0 p M hp0 hp hM

theorem exists_crtProduct_gadget_core {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M p0 : ℕ) [NeZero M] [Fact p0.Prime] [NeZero p0]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (hp0_3 : p0 % 4 = 3) (hp0_23 : 23 ≤ p0)
    (φ : ZMod M ≃+ ProductSpace p0 p) (a : ZMod M)
    (α : ZMod p0) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i))
    (ha1 : (φ a).1 = α) (he : e = affineNormalize p β (φ a).2) :
    ∃ h u1 u2 : ZMod p0,
      crtProductTbaseFinset M p0 p φ β h u1 u2 ⊆
        crtProductTFinset M p0 p φ β e data h u1 u2 ∧
      crtProductTFinset M p0 p φ β e data h u1 u2 ⊆
        crtProductAllowedFinset M p0 p φ α β ∧
      crtProductPstarFinset M p0 p φ a β e h ⊆
        crtProductAllowedFinset M p0 p φ α β ∧
      h + h - α ≠ α ∧
      ((crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) +
          (crtProductTbaseFinset M p0 p φ β h u1 u2 : Set (ZMod M))) = Set.univ ∧
      ((crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M)) +
          (crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M))) =
        Set.univ \ ((fun x : ZMod M => a + x) ''
          (crtProductPstarFinset M p0 p φ a β e h : Set (ZMod M))) ∧
      ((crtProductAllowedFinset M p0 p φ α β : Set (ZMod M)) +
          (crtProductTFinset M p0 p φ β e data h u1 u2 : Set (ZMod M))) = Set.univ := by
  obtain ⟨h, u1, u2, hu1QR, hu2QR, hu12, hτ_ne, hu1_pos, hu2_pos, hu1_neg, hu2_neg,
    hbase_sum, _hselected_full, hQavoid⟩ :=
    exists_selected_coordinate_strong_pair_data p0 hp0_3 hp0_23 α
  refine ⟨h, u1, u2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact crtProductTbase_subset_T M p0 p φ β e data h u1 u2
  · exact crtProductT_subset_allowed M p0 p φ α h u1 u2 β e data hu1_pos hu2_pos
      hu1_neg hu2_neg hQavoid
  · exact crtProductPstar_subset_allowed M p0 p φ a α β e h ha1 he hτ_ne
  · intro hbad
    apply hτ_ne
    linear_combination hbad
  · exact crtProduct_allowed_add_Tbase_eq_univ M p0 p hp7 hp0_3 hp0_23 φ α h u1 u2 β
  · exact crtProduct_T_add_T_compl_private M p0 p hp7 hp0_3 φ a β e data h u1 u2
      hu1QR hu2QR hu12 hbase_sum
  · exact crtProduct_allowed_add_T_eq_univ M p0 p hp7 hp0_3 hp0_23 φ α h u1 u2 β e data

end Erdos330
