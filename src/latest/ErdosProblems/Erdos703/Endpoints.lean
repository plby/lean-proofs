import Mathlib
import ErdosProblems.Erdos703.McDiarmid

namespace Erdos703Endpoints

open Finset Real
open scoped BigOperators symmDiff

noncomputable section

abbrev Cube (n : ℕ) := Finset (Fin n)
abbrev Family (n : ℕ) := Finset (Cube n)
abbrev BoolCube (n : ℕ) := Fin n → Bool

def fairBias (n : ℕ) : Fin n → ℝ := fun _ ↦ 1 / 2

def fairWeight (n : ℕ) : Fin n → Bool → ℝ :=
  Erdos703McDiarmid.bernoulliWeight (fairBias n)

def boolSupport {n : ℕ} (x : BoolCube n) : Cube n :=
  Finset.univ.filter fun i ↦ x i = true

def boolIndicator {n : ℕ} (S : Cube n) : BoolCube n :=
  fun i ↦ decide (i ∈ S)

@[simp] lemma boolSupport_indicator {n : ℕ} (S : Cube n) :
    boolSupport (boolIndicator S) = S := by
  ext i
  simp [boolSupport, boolIndicator]

@[simp] lemma boolIndicator_support {n : ℕ} (x : BoolCube n) :
    boolIndicator (boolSupport x) = x := by
  funext i
  cases h : x i <;> simp [boolIndicator, boolSupport, h]

def boolFinsetEquiv (n : ℕ) : BoolCube n ≃ Cube n where
  toFun := boolSupport
  invFun := boolIndicator
  left_inv := boolIndicator_support
  right_inv := boolSupport_indicator

lemma fairWeight_apply {n : ℕ} (i : Fin n) (b : Bool) :
    fairWeight n i b = 1 / 2 := by
  cases b <;> norm_num [fairWeight, fairBias, Erdos703McDiarmid.bernoulliWeight]

lemma fair_productMass {n : ℕ} (x : BoolCube n) :
    Erdos703McDiarmid.productMass (fairWeight n) x = (1 / 2 : ℝ) ^ n := by
  simp [Erdos703McDiarmid.productMass, fairWeight_apply]

def density {n : ℕ} (A : Family n) : ℝ :=
  (A.card : ℝ) / (2 : ℝ) ^ n

def cubeMean {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ S ∈ (Finset.univ : Cube n).powerset, f S) / (2 : ℝ) ^ n

lemma fair_weightedMean_support {n : ℕ} (f : Cube n → ℝ) :
    Erdos703McDiarmid.weightedMean (fairWeight n) (fun x ↦ f (boolSupport x)) =
      cubeMean f := by
  unfold Erdos703McDiarmid.weightedMean cubeMean
  simp_rw [fair_productMass]
  have hsum : (∑ x : BoolCube n, (1 / 2 : ℝ) ^ n * f (boolSupport x)) =
      ∑ S : Cube n, (1 / 2 : ℝ) ^ n * f S := by
    simpa [boolFinsetEquiv] using
      (boolFinsetEquiv n).sum_comp (fun S ↦ (1 / 2 : ℝ) ^ n * f S)
  rw [hsum]
  have hpowerset : (Finset.univ : Cube n).powerset =
      (Finset.univ : Finset (Cube n)) := by
    ext S
    simp
  rw [hpowerset]
  simp only [one_div, inv_pow, mul_comm]
  rw [← Finset.sum_mul, div_eq_mul_inv]

lemma card_filter_support {n : ℕ} (E : Family n) :
    #((Finset.univ : Finset (BoolCube n)).filter fun x ↦ boolSupport x ∈ E) = #E := by
  classical
  apply Finset.card_bij (fun x _ ↦ boolSupport x)
  · intro x hx
    simpa using (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact (boolFinsetEquiv n).injective hxy
  · intro S hS
    refine ⟨boolIndicator S, ?_, ?_⟩
    · simp [hS]
    · exact boolSupport_indicator S

lemma fair_eventMass_support {n : ℕ} (E : Family n) :
    Erdos703McDiarmid.eventMass (fairWeight n) {x | boolSupport x ∈ E} = density E := by
  unfold Erdos703McDiarmid.eventMass density
  rw [Finset.sum_filter]
  simp_rw [fair_productMass]
  have hsum : (∑ x : BoolCube n,
      if x ∈ {x | boolSupport x ∈ E} then (1 / 2 : ℝ) ^ n else 0) =
      ∑ S : Cube n, if S ∈ E then (1 / 2 : ℝ) ^ n else 0 := by
    simpa [boolFinsetEquiv] using
      (boolFinsetEquiv n).sum_comp
        (fun S : Cube n ↦ if S ∈ E then (1 / 2 : ℝ) ^ n else 0)
  rw [hsum]
  simp [div_eq_mul_inv, inv_pow]

def hamming {n : ℕ} (S T : Cube n) : ℕ := #(S ∆ T)

def OneLipschitz {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ S T, |f S - f T| ≤ hamming S T

/-- The exact black-box form of the two one-sided cube McDiarmid estimates
used by the endpoint arguments. -/
structure CubeMcDiarmid (n : ℕ) : Prop where
  upper : ∀ (f : Cube n → ℝ), OneLipschitz f → ∀ a : ℝ, cubeMean f = a →
    ∀ u : ℝ, 0 ≤ u → ∀ E : Family n,
      (∀ S ∈ E, a + u ≤ f S) →
      density E ≤ Real.exp (-2 * u ^ 2 / n)
  lower : ∀ (f : Cube n → ℝ), OneLipschitz f → ∀ a : ℝ, cubeMean f = a →
    ∀ u : ℝ, 0 ≤ u → ∀ E : Family n,
      (∀ S ∈ E, f S ≤ a - u) →
      density E ≤ Real.exp (-2 * u ^ 2 / n)

lemma hamming_support_le_one_of_off_eq {n : ℕ} (i : Fin n) (x y : BoolCube n)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    hamming (boolSupport x) (boolSupport y) ≤ 1 := by
  unfold hamming
  calc
    #(boolSupport x ∆ boolSupport y) ≤ #({i} : Finset (Fin n)) := by
      apply card_le_card
      intro j hj
      have hji : j = i := by
        by_contra hne
        have heq := hxy j hne
        have hmem : (j ∈ boolSupport x ↔ j ∈ boolSupport y) := by
          simp [boolSupport, heq]
        rcases mem_symmDiff.mp hj with h | h
        · exact h.2 (hmem.mp h.1)
        · exact h.2 (hmem.mpr h.1)
      simp [hji]
    _ = 1 := card_singleton i

lemma fairWeight_nonneg {n : ℕ} : ∀ i : Fin n, ∀ b : Bool, 0 ≤ fairWeight n i b := by
  intro i b
  rw [fairWeight_apply]
  norm_num

lemma fairWeight_sum_one {n : ℕ} : ∀ i : Fin n, ∑ b : Bool, fairWeight n i b = 1 := by
  intro i
  simp [fairWeight_apply]

/-- McDiarmid on the fair Boolean cube, transported through the characteristic-function
equivalence between subsets of `Fin n` and Boolean words. -/
theorem fairCubeMcDiarmid (n : ℕ) : CubeMcDiarmid n where
  upper := by
    intro f hf a hmean u hu E hE
    let fb : BoolCube n → ℝ := fun x ↦ f (boolSupport x)
    have hbd : ∀ i (x y : BoolCube n),
        (∀ j, j ≠ i → x j = y j) → |fb x - fb y| ≤ (1 : ℝ) := by
      intro i x y hxy
      exact (hf (boolSupport x) (boolSupport y)).trans (by
        exact_mod_cast hamming_support_le_one_of_off_eq i x y hxy)
    have hm := Erdos703McDiarmid.mcdiarmid_upper_all n (fairWeight n) fb
      (fun _ ↦ (1 : ℝ)) fairWeight_nonneg fairWeight_sum_one (fun _ ↦ by norm_num)
      hbd u hu
    calc
      density E = Erdos703McDiarmid.eventMass (fairWeight n)
          {x | boolSupport x ∈ E} := (fair_eventMass_support E).symm
      _ ≤ Erdos703McDiarmid.eventMass (fairWeight n)
          {x | Erdos703McDiarmid.weightedMean (fairWeight n) fb + u ≤ fb x} := by
        apply Erdos703McDiarmid.eventMass_mono (fairWeight n) fairWeight_nonneg
        intro x hx
        change boolSupport x ∈ E at hx
        change Erdos703McDiarmid.weightedMean (fairWeight n) fb + u ≤ fb x
        rw [show Erdos703McDiarmid.weightedMean (fairWeight n) fb = cubeMean f by
          exact fair_weightedMean_support f, hmean]
        exact hE (boolSupport x) hx
      _ ≤ Real.exp (-2 * u ^ 2 / n) := by
        simpa using hm

  lower := by
    intro f hf a hmean u hu E hE
    let fb : BoolCube n → ℝ := fun x ↦ f (boolSupport x)
    have hbd : ∀ i (x y : BoolCube n),
        (∀ j, j ≠ i → x j = y j) → |fb x - fb y| ≤ (1 : ℝ) := by
      intro i x y hxy
      exact (hf (boolSupport x) (boolSupport y)).trans (by
        exact_mod_cast hamming_support_le_one_of_off_eq i x y hxy)
    have hm := Erdos703McDiarmid.mcdiarmid_lower_all n (fairWeight n) fb
      (fun _ ↦ (1 : ℝ)) fairWeight_nonneg fairWeight_sum_one (fun _ ↦ by norm_num)
      hbd u hu
    calc
      density E = Erdos703McDiarmid.eventMass (fairWeight n)
          {x | boolSupport x ∈ E} := (fair_eventMass_support E).symm
      _ ≤ Erdos703McDiarmid.eventMass (fairWeight n)
          {x | fb x ≤ Erdos703McDiarmid.weightedMean (fairWeight n) fb - u} := by
        apply Erdos703McDiarmid.eventMass_mono (fairWeight n) fairWeight_nonneg
        intro x hx
        change boolSupport x ∈ E at hx
        change fb x ≤ Erdos703McDiarmid.weightedMean (fairWeight n) fb - u
        rw [show Erdos703McDiarmid.weightedMean (fairWeight n) fb = cubeMean f by
          exact fair_weightedMean_support f, hmean]
        exact hE (boolSupport x) hx
      _ ≤ Real.exp (-2 * u ^ 2 / n) := by
        simpa using hm

/-- The mean of one coordinate indicator under a product of Bernoulli weights. -/
theorem weightedMean_bit_true {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    Erdos703McDiarmid.weightedMean (Erdos703McDiarmid.bernoulliWeight p)
      (fun x : BoolCube n ↦ if x i = true then 1 else 0) = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Erdos703McDiarmid.weightedMean_succ]
          have hsection :
              Erdos703McDiarmid.sectionAverage
                (Erdos703McDiarmid.bernoulliWeight p)
                (fun x : BoolCube (n + 1) ↦
                  if x 0 = true then (1 : ℝ) else 0) =
                fun _ : BoolCube n ↦ p 0 := by
            funext y
            simp [Erdos703McDiarmid.sectionAverage,
              Erdos703McDiarmid.bernoulliWeight]
          rw [hsection]
          simp only [Erdos703McDiarmid.weightedMean]
          rw [← Finset.sum_mul,
            Erdos703McDiarmid.sum_productMass_eq_one n
              (fun i z ↦ Erdos703McDiarmid.bernoulliWeight p i.succ z)
              (fun i ↦ Erdos703McDiarmid.bernoulliWeight_sum_one p i.succ)]
          simp
      | succ i =>
          rw [Erdos703McDiarmid.weightedMean_succ]
          have hsection :
              Erdos703McDiarmid.sectionAverage
                (Erdos703McDiarmid.bernoulliWeight p)
                (fun x : BoolCube (n + 1) ↦
                  if x i.succ = true then (1 : ℝ) else 0) =
                fun x : BoolCube n ↦ if x i = true then 1 else 0 := by
            funext y
            simp [Erdos703McDiarmid.sectionAverage,
              Erdos703McDiarmid.bernoulliWeight]
          rw [hsection]
          exact ih (fun q ↦ p q.succ) i

lemma card_boolSupport_eq_sum {n : ℕ} (x : BoolCube n) :
    (#(boolSupport x) : ℝ) = ∑ i : Fin n, if x i = true then 1 else 0 := by
  rw [show (#(boolSupport x) : ℝ) = ∑ _i ∈ boolSupport x, (1 : ℝ) by
    rw [Finset.sum_const, nsmul_eq_mul]
    norm_num]
  rw [boolSupport, Finset.sum_filter]

lemma fair_weightedMean_card_support (n : ℕ) :
    Erdos703McDiarmid.weightedMean (fairWeight n)
      (fun x : BoolCube n ↦ (#(boolSupport x) : ℝ)) = (n : ℝ) / 2 := by
  simp_rw [card_boolSupport_eq_sum]
  simp only [Erdos703McDiarmid.weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin n, ∑ x : BoolCube n,
        Erdos703McDiarmid.productMass (fairWeight n) x *
          (if x i = true then 1 else 0)) = ∑ i : Fin n, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hbit := weightedMean_bit_true (fairBias n) i
      change (∑ x : BoolCube n,
        Erdos703McDiarmid.productMass (fairWeight n) x *
          (if x i = true then 1 else 0)) = fairBias n i at hbit
      simpa only [fairBias] using hbit
    _ = (n : ℝ) / 2 := by
      simp only [one_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_eq_mul_inv]

lemma cubeMean_card (n : ℕ) :
    cubeMean (fun S : Cube n ↦ (#S : ℝ)) = (n : ℝ) / 2 := by
  rw [← fair_weightedMean_support]
  exact fair_weightedMean_card_support n

lemma density_nonneg {n : ℕ} (A : Family n) : 0 ≤ density A := by
  unfold density
  positivity

lemma density_le_one {n : ℕ} (A : Family n) : density A ≤ 1 := by
  unfold density
  rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
  norm_cast
  simpa using card_le_card (show A ⊆ (Finset.univ : Cube n).powerset by simp)

lemma hamming_comm {n : ℕ} (S T : Cube n) : hamming S T = hamming T S := by
  simp [hamming, symmDiff_comm]

lemma hamming_self {n : ℕ} (S : Cube n) : hamming S S = 0 := by
  simp [hamming]

lemma hamming_triangle {n : ℕ} (S T U : Cube n) :
    hamming S U ≤ hamming S T + hamming T U := by
  unfold hamming
  calc
    #(S ∆ U) ≤ #((S ∆ T) ∪ (T ∆ U)) :=
      card_le_card (show S ∆ U ⊆ (S ∆ T) ∪ (T ∆ U) from symmDiff_triangle S T U)
    _ ≤ #(S ∆ T) + #(T ∆ U) := card_union_le _ _

def familyDist {n : ℕ} (A : Family n) (hA : A.Nonempty) (S : Cube n) : ℕ :=
  A.inf' hA (fun T ↦ hamming S T)

lemma familyDist_eq_zero_of_mem {n : ℕ} {A : Family n} (hA : A.Nonempty)
    {S : Cube n} (hS : S ∈ A) : familyDist A hA S = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Finset.inf'_le _ hS).trans_eq (hamming_self S)

lemma familyDist_le_hamming {n : ℕ} {A : Family n} (hA : A.Nonempty)
    (S : Cube n) {T : Cube n} (hT : T ∈ A) : familyDist A hA S ≤ hamming S T :=
  Finset.inf'_le _ hT

lemma le_familyDist {n : ℕ} {A : Family n} (hA : A.Nonempty)
    (S : Cube n) {d : ℕ} (h : ∀ T ∈ A, d ≤ hamming S T) :
    d ≤ familyDist A hA S := by
  exact Finset.le_inf' hA _ h

lemma familyDist_triangle_right {n : ℕ} {A : Family n} (hA : A.Nonempty)
    (S T : Cube n) :
    familyDist A hA S ≤ hamming S T + familyDist A hA T := by
  obtain ⟨U, hU, hmin⟩ := Finset.exists_mem_eq_inf' hA (fun U ↦ hamming T U)
  unfold familyDist
  rw [hmin]
  exact (Finset.inf'_le _ hU).trans (hamming_triangle S T U)

lemma familyDist_lipschitz {n : ℕ} {A : Family n} (hA : A.Nonempty) :
    OneLipschitz (fun S ↦ (familyDist A hA S : ℝ)) := by
  intro S T
  rw [abs_le]
  constructor
  · have h := familyDist_triangle_right hA T S
    rw [hamming_comm T S] at h
    have hc : (familyDist A hA T : ℝ) ≤
        (hamming S T : ℝ) + familyDist A hA S := by exact_mod_cast h
    dsimp
    linarith
  · have h := familyDist_triangle_right hA S T
    have hc : (familyDist A hA S : ℝ) ≤
        (hamming S T : ℝ) + familyDist A hA T := by exact_mod_cast h
    dsimp
    linarith

lemma familyDist_mean_nonneg {n : ℕ} {A : Family n} (hA : A.Nonempty) :
    0 ≤ cubeMean (fun S ↦ (familyDist A hA S : ℝ)) := by
  unfold cubeMean
  positivity

/-- Finite-cube separated-families endpoint, conditional only on the generic
McDiarmid estimate above. -/
theorem separated_families {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (A B : Family n) (t : ℝ) (ht : 0 ≤ t)
    (hsep : ∀ S ∈ A, ∀ T ∈ B, t ≤ hamming S T) :
    density A * density B ≤ Real.exp (-t ^ 2 / n) := by
  by_cases hAe : A = ∅
  · simp [hAe, density, Real.exp_nonneg]
  by_cases hBe : B = ∅
  · simp [hBe, density, Real.exp_nonneg]
  have hA : A.Nonempty := nonempty_iff_ne_empty.mpr hAe
  have hB : B.Nonempty := nonempty_iff_ne_empty.mpr hBe
  let f : Cube n → ℝ := fun S ↦ (familyDist A hA S : ℝ)
  let a : ℝ := cubeMean f
  have ha0 : 0 ≤ a := familyDist_mean_nonneg hA
  have hf : OneLipschitz f := familyDist_lipschitz hA
  have hfA : ∀ S ∈ A, f S = 0 := by
    intro S hS
    simp [f, familyDist_eq_zero_of_mem hA hS]
  have hfB : ∀ S ∈ B, t ≤ f S := by
    intro S hS
    have hnat : ∀ T ∈ A, t ≤ (hamming S T : ℝ) := by
      intro T hT
      simpa [hamming_comm] using hsep T hT S hS
    obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' hA (fun T ↦ hamming S T)
    dsimp [f]
    unfold familyDist
    rw [hmin]
    exact hnat u hu
  by_cases hat : t ≤ a
  · have hlow : density A ≤ Real.exp (-2 * a ^ 2 / n) := by
      apply mc.lower f hf a rfl a ha0 A
      intro S hS
      rw [hfA S hS]
      linarith
    calc
      density A * density B ≤ density A * 1 :=
        mul_le_mul_of_nonneg_left (density_le_one B) (density_nonneg A)
      _ = density A := by ring
      _ ≤ Real.exp (-2 * a ^ 2 / n) := hlow
      _ ≤ Real.exp (-t ^ 2 / n) := by
        apply Real.exp_le_exp.mpr
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        apply (div_le_div_iff_of_pos_right hnR).mpr
        nlinarith [sq_nonneg a, sq_nonneg t]
  · have hat' : a < t := lt_of_not_ge hat
    have hu : 0 ≤ t - a := sub_nonneg.mpr hat'.le
    have hlow : density A ≤ Real.exp (-2 * a ^ 2 / n) := by
      apply mc.lower f hf a rfl a ha0 A
      intro S hS
      rw [hfA S hS]
      linarith
    have hupp : density B ≤ Real.exp (-2 * (t - a) ^ 2 / n) := by
      apply mc.upper f hf a rfl (t - a) hu B
      intro S hS
      simpa only [add_sub_cancel] using hfB S hS
    calc
      density A * density B ≤
          Real.exp (-2 * a ^ 2 / n) * Real.exp (-2 * (t - a) ^ 2 / n) :=
        mul_le_mul hlow hupp (density_nonneg B) (Real.exp_nonneg _)
      _ = Real.exp ((-2 * a ^ 2 / n) + (-2 * (t - a) ^ 2 / n)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (-t ^ 2 / n) := by
        apply Real.exp_le_exp.mpr
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right hnR).mpr
        nlinarith [sq_nonneg (2 * a - t)]

def cubeCompl {n : ℕ} (S : Cube n) : Cube n := Finset.univ \ S

lemma cubeCompl_involutive {n : ℕ} (S : Cube n) : cubeCompl (cubeCompl S) = S := by
  ext i
  simp [cubeCompl]

lemma cubeCompl_injective {n : ℕ} : Function.Injective (cubeCompl : Cube n → Cube n) := by
  intro S T h
  simpa only [cubeCompl_involutive] using congrArg cubeCompl h

def complementFamily {n : ℕ} (B : Family n) : Family n := B.image cubeCompl

lemma complementFamily_density {n : ℕ} (B : Family n) :
    density (complementFamily B) = density B := by
  unfold density complementFamily
  rw [card_image_of_injective _ cubeCompl_injective]

lemma inter_subset_symmDiff_compl {n : ℕ} (S T : Cube n) :
    S ∩ T ⊆ S ∆ cubeCompl T := by
  intro i hi
  rw [mem_symmDiff]
  exact Or.inl ⟨(mem_inter.mp hi).1, by simp [cubeCompl, (mem_inter.mp hi).2]⟩

/-- Large cross intersections reduce to separated families after complementing
the second family. -/
theorem cross_high {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (A B : Family n) (t : ℝ) (ht : 0 ≤ t)
    (hcross : ∀ S ∈ A, ∀ T ∈ B, t ≤ #(S ∩ T)) :
    density A * density B ≤ Real.exp (-t ^ 2 / n) := by
  have hsep : ∀ S ∈ A, ∀ U ∈ complementFamily B, t ≤ hamming S U := by
    intro S hS U hU
    rw [complementFamily, mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    exact (hcross S hS T hT).trans (by
      exact_mod_cast card_le_card (inter_subset_symmDiff_compl S T))
  rw [← complementFamily_density B]
  exact separated_families hn mc A (complementFamily B) t ht hsep

lemma card_oneLipschitz {n : ℕ} : OneLipschitz (fun S : Cube n ↦ (#S : ℝ)) := by
  intro S T
  have hST := hamming_triangle S T ∅
  have hTS := hamming_triangle T S ∅
  have hzero (U : Cube n) : hamming U ∅ = #U := by
    simp [hamming, symmDiff_def]
  have hST' : #S ≤ hamming S T + #T := by simpa [hzero] using hST
  have hTS' : #T ≤ hamming T S + #S := by simpa [hzero] using hTS
  rw [abs_le]
  constructor
  · have hc : (#T : ℝ) ≤ (hamming S T : ℝ) + #S := by
      rw [hamming_comm]
      exact_mod_cast hTS'
    linarith
  · have hc : (#S : ℝ) ≤ (hamming S T : ℝ) + #T := by exact_mod_cast hST'
    linarith

lemma density_filter_add_filter_not {n : ℕ} (A : Family n) (p : Cube n → Prop)
    [DecidablePred p] [∀ S, Decidable (¬p S)] :
    density (A.filter p) + density (A.filter fun S ↦ ¬p S) = density A := by
  unfold density
  rw [← add_div, ← Nat.cast_add, card_filter_add_card_filter_not]

/-- Small cross intersections endpoint.  `hcardMean` is the elementary
identity saying that a uniform random subset has expected cardinality `n/2`;
it is kept explicit so that the only analytic input is `CubeMcDiarmid`. -/
theorem cross_low {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (hcardMean : cubeMean (fun S : Cube n ↦ (#S : ℝ)) = (n : ℝ) / 2)
    (A B : Family n) (κ : ℝ) (hκ0 : 0 < κ)
    (hcross : ∀ S ∈ A, ∀ T ∈ B,
      (#(S ∩ T) : ℝ) < (1 / 2 - κ) * n) :
    density A * density B ≤
      max (2 * Real.exp (-(κ ^ 2 * n) / 2))
        (4 * Real.exp (-(κ ^ 2 * n) / 4)) := by
  let large : Cube n → Prop := fun S ↦ (1 / 2 - κ / 2) * n ≤ (#S : ℝ)
  let Astar : Family n := A.filter large
  let Bstar : Family n := B.filter large
  let Alow : Family n := A.filter fun S ↦ ¬ large S
  let Blow : Family n := B.filter fun S ↦ ¬ large S
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : 0 ≤ κ * n / 2 := by positivity
  have hAlow : density Alow ≤ Real.exp (-(κ ^ 2 * n) / 2) := by
    have h := mc.lower (fun S : Cube n ↦ (#S : ℝ)) card_oneLipschitz
      ((n : ℝ) / 2) hcardMean (κ * n / 2) hu Alow
    have hevent : ∀ S ∈ Alow, (#S : ℝ) ≤ (n : ℝ) / 2 - κ * n / 2 := by
      intro S hS
      have hs := (mem_filter.mp hS).2
      dsimp [large] at hs
      push Not at hs
      linarith
    have hh := h hevent
    calc
      density Alow ≤ Real.exp (-2 * (κ * n / 2) ^ 2 / n) := hh
      _ = Real.exp (-(κ ^ 2 * n) / 2) := by
        congr 1
        field_simp [ne_of_gt hnR]
  have hBlow : density Blow ≤ Real.exp (-(κ ^ 2 * n) / 2) := by
    have h := mc.lower (fun S : Cube n ↦ (#S : ℝ)) card_oneLipschitz
      ((n : ℝ) / 2) hcardMean (κ * n / 2) hu Blow
    have hevent : ∀ S ∈ Blow, (#S : ℝ) ≤ (n : ℝ) / 2 - κ * n / 2 := by
      intro S hS
      have hs := (mem_filter.mp hS).2
      dsimp [large] at hs
      push Not at hs
      linarith
    have hh := h hevent
    calc
      density Blow ≤ Real.exp (-2 * (κ * n / 2) ^ 2 / n) := hh
      _ = Real.exp (-(κ ^ 2 * n) / 2) := by
        congr 1
        field_simp [ne_of_gt hnR]
  have hApart : density Astar + density Alow = density A := by
    exact density_filter_add_filter_not A large
  have hBpart : density Bstar + density Blow = density B := by
    exact density_filter_add_filter_not B large
  by_cases hAdense : density A ≤ 2 * density Astar
  swap
  · have hAupper : density A ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := by
      have hstarlt : density Astar < density Alow := by
        rw [← hApart] at hAdense
        push Not at hAdense
        linarith
      rw [← hApart]
      linarith
    calc
      density A * density B ≤ density A * 1 :=
        mul_le_mul_of_nonneg_left (density_le_one B) (density_nonneg A)
      _ = density A := by ring
      _ ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := hAupper
      _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
          (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_left _ _
  by_cases hBdense : density B ≤ 2 * density Bstar
  swap
  · have hBupper : density B ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := by
      have hstarlt : density Bstar < density Blow := by
        rw [← hBpart] at hBdense
        push Not at hBdense
        linarith
      rw [← hBpart]
      linarith
    calc
      density A * density B ≤ 1 * density B :=
        mul_le_mul_of_nonneg_right (density_le_one A) (density_nonneg B)
      _ = density B := by ring
      _ ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := hBupper
      _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
          (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_left _ _
  have hstarCross : ∀ S ∈ Astar, ∀ U ∈ complementFamily Bstar,
      κ * n / 2 ≤ (#(S ∩ U) : ℝ) := by
    intro S hS U hU
    rw [complementFamily, mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    have hSA := (mem_filter.mp hS)
    have hTB := (mem_filter.mp hT)
    have hi := hcross S hSA.1 T hTB.1
    have hsLarge := hSA.2
    dsimp [large] at hsLarge
    have hcardDiff : #(S \ T) + #(S ∩ T) = #S := by
      exact card_sdiff_add_card_inter S T
    have hEq : S ∩ cubeCompl T = S \ T := by
      ext i
      simp [cubeCompl]
    rw [hEq]
    have hcardDiffR : (#(S \ T) : ℝ) + #(S ∩ T) = #S := by exact_mod_cast hcardDiff
    linarith
  have hhigh := cross_high hn mc Astar (complementFamily Bstar)
    (κ * n / 2) hu hstarCross
  rw [complementFamily_density] at hhigh
  have hprod : density A * density B ≤ 4 * (density Astar * density Bstar) := by
    calc
      density A * density B ≤
          (2 * density Astar) * (2 * density Bstar) :=
        mul_le_mul hAdense hBdense (density_nonneg B)
          (mul_nonneg (by norm_num) (density_nonneg Astar))
      _ = 4 * (density Astar * density Bstar) := by ring
  calc
    density A * density B ≤ 4 * (density Astar * density Bstar) := hprod
    _ ≤ 4 * Real.exp (-((κ * n / 2) ^ 2) / n) :=
      mul_le_mul_of_nonneg_left hhigh (by norm_num)
    _ = 4 * Real.exp (-(κ ^ 2 * n) / 4) := by
      congr 2
      field_simp
      ring
    _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
        (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_right _ _

end

end Erdos703Endpoints
