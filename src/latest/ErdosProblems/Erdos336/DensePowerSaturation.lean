import Mathlib.Combinatorics.Additive.VerySmallDoubling
import ErdosProblems.Erdos336.DyadicSmallDoubling

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A dense primitive power saturates after boundedly many doublings
-/

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma image_ofAdd_add (A : Finset G) :
    (A.image Multiplicative.ofAdd) * (A.image Multiplicative.ofAdd) =
      (A + A).image Multiplicative.ofAdd := by
  ext z
  constructor
  · intro hz
    simp only [Finset.mem_mul] at hz
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    simp only [Finset.mem_image] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    refine Finset.mem_image.2 ⟨x + y, ?_, ?_⟩
    · exact Finset.mem_add.2 ⟨x, hx, y, hy, rfl⟩
    · exact hxy
  · intro hz
    simp only [Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hw
    exact Finset.mem_mul.2 ⟨Multiplicative.ofAdd x,
      Finset.mem_image.2 ⟨x, hx, rfl⟩,
      Multiplicative.ofAdd y, Finset.mem_image.2 ⟨y, hy, rfl⟩, rfl⟩

private lemma card_image_ofAdd (A : Finset G) :
    (A.image Multiplicative.ofAdd).card = A.card := by
  rw [Finset.card_image_of_injective]
  exact Multiplicative.ofAdd.injective

/-- Additive form of the `<3/2` saturation consequence: a zero-containing
finite set which generates the group and has doubling below `3/2` already
has full double. -/
theorem add_self_eq_univ_of_three_mul_lt_two_mul
    (A : Finset G) (hzero : 0 ∈ A)
    (hgen : AddSubgroup.closure (A : Set G) = ⊤)
    (hdbl : 2 * (A + A).card < 3 * A.card) :
    A + A = Finset.univ := by
  let M : Finset (Multiplicative G) := A.image Multiplicative.ofAdd
  have hMM : M * M = (A + A).image Multiplicative.ofAdd := image_ofAdd_add A
  have hcardM : M.card = A.card := card_image_ofAdd A
  have hrat : (((M * M).card : ℕ) : ℚ) < (3 / 2 : ℚ) * M.card := by
    rw [hMM, Finset.card_image_of_injective _ Multiplicative.ofAdd.injective, hcardM]
    have hdblQ : (2 : ℚ) * (A + A).card < 3 * A.card := by
      exact_mod_cast hdbl
    linarith
  let H : Subgroup (Multiplicative G) := M.invMulSubgroup hrat
  have honeM : (1 : Multiplicative G) ∈ M := by
    exact Finset.mem_image.2 ⟨0, hzero, rfl⟩
  have hMsub : (M : Set (Multiplicative G)) ⊆ H := by
    intro x hx
    rw [Finset.invMulSubgroup_eq_inv_mul M hrat]
    exact ⟨1, by simpa using honeM, x, hx, by simp⟩
  let K : AddSubgroup G :=
    { carrier := {x | Multiplicative.ofAdd x ∈ H}
      zero_mem' := H.one_mem
      add_mem' := by
        intro x y hx hy
        exact H.mul_mem hx hy
      neg_mem' := by
        intro x hx
        exact H.inv_mem hx }
  have hAK : (A : Set G) ⊆ K := by
    intro x hx
    exact hMsub (Finset.mem_image.2 ⟨x, hx, rfl⟩)
  have hKtop : K = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen, AddSubgroup.closure_le]
    exact hAK
  have hHtop : H = ⊤ := by
    apply (Subgroup.eq_top_iff' H).2
    intro x
    obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective x
    change x ∈ K
    rw [hKtop]
    trivial
  have hinvfull : (M⁻¹ * M : Finset (Multiplicative G)) = Finset.univ := by
    apply Finset.coe_injective
    rw [Finset.coe_mul, ← Finset.invMulSubgroup_eq_inv_mul M hrat]
    change (H : Set (Multiplicative G)) = (Finset.univ : Finset (Multiplicative G))
    rw [hHtop]
    simp
  have hprod : M⁻¹ * M = M * M := by
    simpa using
      (Finset.smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves hrat honeM)
  have hMMfull : M * M = Finset.univ := by
    rw [← hprod, hinvfull]
  have himage : (A + A).image Multiplicative.ofAdd = Finset.univ := by
    rw [← hMM, hMMfull]
  apply Finset.eq_univ_iff_forall.2
  intro x
  have hxM : Multiplicative.ofAdd x ∈
      (A + A).image Multiplicative.ofAdd := by
    rw [himage]
    simp
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hxM
  have : y = x := Multiplicative.ofAdd.injective hyx
  simpa [this] using hy

/-- A positive exact power of a primitive zero-containing set still generates
its ambient group. -/
theorem closure_exactPower_eq_top
    {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {k : ℕ} (hk : 0 < k) :
    AddSubgroup.closure (ExactPower D k) = ⊤ := by
  have hDtop : AddSubgroup.closure D = ⊤ := by
    apply (AddSubgroup.eq_top_iff' (AddSubgroup.closure D)).2
    intro y
    obtain ⟨q, hq⟩ := hexact
    have hy : y ∈ ExactPower D q := by rw [hq]; trivial
    obtain ⟨xs, -, hxmem, hxsum⟩ := hy
    rw [← hxsum]
    have hsum : ∀ ys : List G, (∀ z ∈ ys, z ∈ D) →
        ys.sum ∈ AddSubgroup.closure D := by
      intro ys hys
      induction ys with
      | nil => exact (AddSubgroup.closure D).zero_mem
      | cons x ys ih =>
          apply (AddSubgroup.closure D).add_mem
          · exact AddSubgroup.subset_closure (hys x (by simp))
          · apply ih
            intro z hz
            exact hys z (by simp [hz])
    exact hsum xs hxmem
  apply le_antisymm le_top
  rw [← hDtop]
  apply AddSubgroup.closure_mono
  have hpowOne : ExactPower D 1 = D := by
    simpa [exactPower_eq_nsmul]
  have hmono := exactPower_mono_of_zero hzero
    (Nat.one_le_iff_ne_zero.mpr hk.ne')
  intro x hx
  exact hmono (hpowOne.symm ▸ hx)

/-- The finite-set model of an exact power in a finite ambient group. -/
noncomputable def exactPowerFinset (D : Set G) (k : ℕ) : Finset G :=
  (ExactPower D k).toFinite.toFinset

@[simp] theorem mem_exactPowerFinset {D : Set G} {k : ℕ} {x : G} :
    x ∈ exactPowerFinset D k ↔ x ∈ ExactPower D k := by
  exact (Set.toFinite (ExactPower D k)).mem_toFinset

@[simp] theorem coe_exactPowerFinset (D : Set G) (k : ℕ) :
    (exactPowerFinset D k : Set G) = ExactPower D k := by
  ext x
  simp

@[simp] theorem card_exactPowerFinset (D : Set G) (k : ℕ) :
    (exactPowerFinset D k).card = (ExactPower D k).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  rfl

private lemma exactPowerFinset_add (D : Set G) (k l : ℕ) :
    exactPowerFinset D k + exactPowerFinset D l =
      exactPowerFinset D (k + l) := by
  classical
  apply Finset.coe_injective
  rw [Finset.coe_add]
  simp only [coe_exactPowerFinset]
  exact exactPower_add D k l

private lemma three_pow_mul_le_two_pow_of_growth
    (f : ℕ → ℕ) (m : ℕ)
    (hgrowth : ∀ i : ℕ, i < m → 3 * f i ≤ 2 * f (i + 1)) :
    3 ^ m * f 0 ≤ 2 ^ m * f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ih' : 3 ^ m * f 0 ≤ 2 ^ m * f m :=
        ih (fun i hi => hgrowth i (by omega))
      have hm := hgrowth m (by omega)
      calc
        3 ^ (m + 1) * f 0 = 3 * (3 ^ m * f 0) := by ring
        _ ≤ 3 * (2 ^ m * f m) := Nat.mul_le_mul_left 3 ih'
        _ ≤ 2 ^ m * (2 * f (m + 1)) := by
          nlinarith [Nat.zero_le (2 ^ m)]
        _ = 2 ^ (m + 1) * f (m + 1) := by ring

lemma dense_saturation_numerical :
    2 ^ 26 * 30000 < 3 ^ 26 := by norm_num

/-- A primitive exact power of density greater than `1/30000` saturates after
at most `2^26` copies.  This is the uniform endgame for the dense alternative
in the cyclic small-doubling trichotomy. -/
theorem dense_highPower_saturates
    {D : Set G} (hzero : 0 ∈ D)
    (hexact : ∃ q : ℕ, ExactPower D q = Set.univ)
    {t : ℕ} (ht : 0 < t)
    (hdense : Fintype.card G < 30000 * (ExactPower D t).ncard) :
    ∃ u : ℕ, 0 < u ∧ u ≤ 2 ^ 26 ∧
      ExactPower D (u * t) = Set.univ := by
  let f : ℕ → ℕ := fun i => (ExactPower D (2 ^ i * t)).ncard
  have htop : ∀ i, f i ≤ Fintype.card G := by
    intro i
    dsimp [f]
    calc
      (ExactPower D (2 ^ i * t)).ncard ≤ (Set.univ : Set G).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Fintype.card G := by simp
  have fpos : 0 < f 0 := by
    rw [Set.ncard_pos]
    refine ⟨0, ?_⟩
    apply exactPower_mono_of_zero hzero (show 0 ≤ 2 ^ 0 * t by omega)
    exact ⟨[], rfl, by simp, by simp⟩
  by_contra hnot
  push_neg at hnot
  have hnolow : ∀ i : ℕ, i < 26 →
      3 * f i ≤ 2 * f (i + 1) := by
    intro i hi
    by_contra hbad
    push_neg at hbad
    let A : Finset G := exactPowerFinset D (2 ^ i * t)
    have hAadd : A + A =
        exactPowerFinset D (2 ^ (i + 1) * t) := by
      dsimp [A]
      rw [exactPowerFinset_add]
      congr 2
      ring
    have hzeroA : 0 ∈ A := by
      dsimp [A]
      rw [mem_exactPowerFinset]
      apply exactPower_mono_of_zero hzero (show 0 ≤ 2 ^ i * t by omega)
      exact ⟨[], rfl, by simp, by simp⟩
    have hgenA : AddSubgroup.closure (A : Set G) = ⊤ := by
      dsimp [A]
      rw [coe_exactPowerFinset]
      exact closure_exactPower_eq_top hzero hexact (by positivity)
    have hdblA : 2 * (A + A).card < 3 * A.card := by
      rw [hAadd]
      dsimp [A]
      simp only [card_exactPowerFinset]
      simpa [f] using hbad
    have hfullA := add_self_eq_univ_of_three_mul_lt_two_mul
      A hzeroA hgenA hdblA
    have hfull : ExactPower D (2 ^ (i + 1) * t) = Set.univ := by
      rw [hAadd] at hfullA
      ext x
      have hx := Finset.ext_iff.mp hfullA x
      simpa using hx
    have hu : 2 ^ (i + 1) ≤ 2 ^ 26 :=
      pow_le_pow_right₀ (by omega) (by omega)
    exact hnot (2 ^ (i + 1)) (by positivity) hu hfull
  have hgrow := three_pow_mul_le_two_pow_of_growth f 26 hnolow
  have hden : Fintype.card G < 30000 * f 0 := by simpa [f] using hdense
  have hbad : 3 ^ 26 * f 0 < 2 ^ 26 * 30000 * f 0 := by
    calc
      3 ^ 26 * f 0 ≤ 2 ^ 26 * f 26 := hgrow
      _ ≤ 2 ^ 26 * Fintype.card G := Nat.mul_le_mul_left _ (htop 26)
      _ < 2 ^ 26 * (30000 * f 0) :=
        (Nat.mul_lt_mul_left (by positivity)).2 hden
      _ = 2 ^ 26 * 30000 * f 0 := by ring
  have hnum := dense_saturation_numerical
  nlinarith

end Erdos336
