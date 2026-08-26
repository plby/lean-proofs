import ErdosProblems.Erdos67b.WeightedTransfer
import ErdosProblems.Erdos67b.BCCDecomposition

/-!
# The finite prefix consumer for the generalized BCC argument

This file connects the normalized good-residue estimate in Tao's equation
(17) to the exact `q`-power Fourier energy calculation in `BCC`.  It records
the exceptional-residue loss explicitly: after normalization by `q ^ k`, the
loss is at most `2 * H * omega(q) / 2 ^ k` times a pointwise energy bound.
-/

open scoped BigOperators ZMod
open Finset

namespace Erdos67b

noncomputable section

/-- Multiplying two spatial functions by fixed coefficients preserves a zero
cross inner product. -/
theorem sum_coeff_mul_star_eq_zero {N : ℕ} [NeZero N]
    (f g : ZMod N → ℂ) (c e : ℂ)
    (hfg : ∑ a : ZMod N, f a * (starRingEnd ℂ) (g a) = 0) :
    ∑ a : ZMod N,
        (c * f a) * (starRingEnd ℂ) (e * g a) = 0 := by
  simp_rw [map_mul]
  calc
    (∑ a : ZMod N,
        (c * f a) * ((starRingEnd ℂ) e * (starRingEnd ℂ) (g a))) =
        (c * (starRingEnd ℂ) e) *
          ∑ a : ZMod N, f a * (starRingEnd ℂ) (g a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = 0 := by rw [hfg, mul_zero]

/-- Pythagoras for coefficient-weighted scaled-character prefixes whose
Fourier layers are pairwise disjoint. -/
theorem coeff_scaledCharacterPrefix_family_energy
    {q N L : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hd : ∀ i ∈ s, NeZero (d i))
    (ht : ∀ i ∈ s, NeZero (t i))
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) N)
        (SmoothFrequencyLayer q (t j) N)) :
    (∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ s, coeff i * scaledCharacterPrefix χ (d i) L a)) =
      ∑ i ∈ s, ∑ a : ZMod N,
        Complex.normSq
          (coeff i * scaledCharacterPrefix χ (d i) L a) := by
  apply sum_normSq_finset_sum_of_orthogonal
  intro i hi j hj hij
  apply sum_coeff_mul_star_eq_zero
  apply sum_mul_star_eq_zero_of_supportedOn_disjoint (hsep i hi j hj hij)
  · letI : NeZero (d i) := hd i hi
    letI : NeZero (t i) := ht i hi
    exact scaledCharacterPrefix_fourierSupportedOn_of_eq hχ (hN i hi)
  · letI : NeZero (d j) := hd j hj
    letI : NeZero (t j) := ht j hj
    exact scaledCharacterPrefix_fourierSupportedOn_of_eq hχ (hN j hj)

/-- Unit-modulus coefficients disappear from the diagonal terms in the
preceding Pythagorean identity. -/
theorem coeff_scaledCharacterPrefix_family_energy_of_normSq_one
    {q N L : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ s, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ s, NeZero (d i))
    (ht : ∀ i ∈ s, NeZero (t i))
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) N)
        (SmoothFrequencyLayer q (t j) N)) :
    (∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ s, coeff i * scaledCharacterPrefix χ (d i) L a)) =
      ∑ i ∈ s, ∑ a : ZMod N,
        Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
  rw [coeff_scaledCharacterPrefix_family_energy s χ hχ coeff d t hd ht hN hsep]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Complex.normSq_mul, hc i hi, one_mul]

/-- In a pairwise orthogonal full family, the total prefix energy of a
selected subfamily is at most the energy of the full family. -/
theorem coeff_selected_prefix_energy_le_full
    {q N L : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (selected full : Finset ι)
    (hsub : selected ⊆ full)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ full, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ full, NeZero (d i))
    (ht : ∀ i ∈ full, NeZero (t i))
    (hN : ∀ i ∈ full, N = t i * (q * d i))
    (hsep : ∀ i ∈ full, ∀ j ∈ full, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) N)
        (SmoothFrequencyLayer q (t j) N)) :
    (∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ selected,
            coeff i * scaledCharacterPrefix χ (d i) L a)) ≤
      ∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a) := by
  have hselected :
      (∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ selected,
              coeff i * scaledCharacterPrefix χ (d i) L a)) =
        ∑ i ∈ selected, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
    exact coeff_scaledCharacterPrefix_family_energy_of_normSq_one
      selected χ hχ coeff d t
      (fun i hi ↦ hc i (hsub hi))
      (fun i hi ↦ hd i (hsub hi))
      (fun i hi ↦ ht i (hsub hi))
      (fun i hi ↦ hN i (hsub hi))
      (fun i hi j hj hij ↦ hsep i (hsub hi) j (hsub hj) hij)
  have hfull :
      (∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ full,
              coeff i * scaledCharacterPrefix χ (d i) L a)) =
        ∑ i ∈ full, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterPrefix χ (d i) L a) :=
    coeff_scaledCharacterPrefix_family_energy_of_normSq_one
      full χ hχ coeff d t hc hd ht hN hsep
  rw [hselected, hfull]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _hi _hnot ↦ Finset.sum_nonneg fun a _ha ↦ Complex.normSq_nonneg _)

/-- Prefix differences turn the medium-length energy of a coefficient-weighted
orthogonal family into the sum of its exact block energies. -/
theorem coeff_block_energy_le_medium_prefix_energy
    {q N H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ s, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ s, NeZero (d i))
    (ht : ∀ i ∈ s, NeZero (t i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) N)
        (SmoothFrequencyLayer q (t j) N)) :
    (H : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
      8 * ∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ s,
              coeff i * scaledCharacterPrefix χ (d i) L a) := by
  have hone (i : ι) (hi : i ∈ s) :
      (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) :=
    H_mul_block_energy_le_eight_mul_medium_prefix_energy χ (d i) H (hdH i hi)
  have hsum := Finset.sum_le_sum (fun i hi ↦ hone i hi)
  have hmedium :
      (∑ i ∈ s, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) =
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s,
                coeff i * scaledCharacterPrefix χ (d i) L a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro L _hL
    exact (coeff_scaledCharacterPrefix_family_energy_of_normSq_one
      s χ hχ coeff d t hc hd ht hN hsep).symm
  have hcombined :
      (H : ℝ) *
          (∑ i ∈ s, ∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s,
                coeff i * scaledCharacterPrefix χ (d i) L a) := by
    calc
      (H : ℝ) *
          (∑ i ∈ s, ∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) =
          ∑ i ∈ s, (H : ℝ) *
            (∑ a : ZMod N,
              Complex.normSq (scaledCharacterBlock χ (d i) a)) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := hsum
      _ = 8 * (∑ i ∈ s, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) := by
        rw [Finset.mul_sum]
      _ = 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s,
                coeff i * scaledCharacterPrefix χ (d i) L a) := by
        rw [hmedium]
  have henergy :
      (∑ i ∈ s, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ (d i) a)) =
        ∑ i ∈ s,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    letI : NeZero (d i) := hd i hi
    letI : NeZero (t i) := ht i hi
    exact scaledCharacterBlock_energy_of_eq χ (hN i hi)
  rw [henergy] at hcombined
  exact hcombined

/-- Normalized full-family consumer for an arbitrary chosen good set.  The
exceptional-set estimate is supplied in the scale-free form
`card (univ \ good) ≤ N * delta`; this makes the theorem reusable after a
translation of the good residue classes. -/
theorem bcc_full_family_normalized_diagonal_le_of_good
    {q N H : ℕ} [NeZero q] [NeZero N] (hH : 0 < H)
    {ι : Type*} [DecidableEq ι]
    (selected full : Finset ι) (hsub : selected ⊆ full)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ full, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ full, NeZero (d i))
    (ht : ∀ i ∈ full, NeZero (t i))
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (hN : ∀ i ∈ full, N = t i * (q * d i))
    (hsep : ∀ i ∈ full, ∀ j ∈ full, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) N)
        (SmoothFrequencyLayer q (t j) N))
    (good : Finset (ZMod N)) (B R delta : ℝ) (hR : 0 ≤ R)
    (hcard : (((Finset.univ \ good).card : ℕ) : ℝ) ≤ (N : ℝ) * delta)
    (hgood :
      (1 / ((N : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ full,
                  coeff i * scaledCharacterPrefix χ (d i) L a) ≤ B)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ good,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (1 / (N : ℝ)) *
        ∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) ≤
      8 * (B + delta * R) := by
  let D : ℝ :=
    ∑ i ∈ selected,
      (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))
  let S : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ selected,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  let F : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  let G : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a ∈ good,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hden : (0 : ℝ) < (N : ℝ) * H := mul_pos hNR hHR
  have hprefix : (H : ℝ) * D ≤ 8 * S := by
    exact coeff_block_energy_le_medium_prefix_energy
      selected χ hχ coeff d t
      (fun i hi ↦ hc i (hsub hi))
      (fun i hi ↦ hd i (hsub hi))
      (fun i hi ↦ ht i (hsub hi)) hdH
      (fun i hi ↦ hN i (hsub hi))
      (fun i hi j hj hij ↦ hsep i (hsub hi) j (hsub hj) hij)
  have hSF : S ≤ F := by
    apply Finset.sum_le_sum
    intro L hL
    exact coeff_selected_prefix_energy_le_full
      selected full hsub χ hχ coeff d t hc hd ht hN hsep
  have hrestore :
      F ≤ G + (H : ℝ) * ((((Finset.univ \ good).card : ℕ) : ℝ) * R) := by
    exact medium_full_energy_le_good_add_bad good
      (fun L a ↦ ∑ i ∈ full,
        coeff i * scaledCharacterPrefix χ (d i) L a) R hbad
  have hgood' : G ≤ B * ((N : ℝ) * H) := by
    change (1 / ((N : ℝ) * H)) * G ≤ B at hgood
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hden] at hgood
    exact hgood
  have hbadTerm :
      (H : ℝ) * ((((Finset.univ \ good).card : ℕ) : ℝ) * R) ≤
        (H : ℝ) * (((N : ℝ) * delta) * R) := by
    gcongr
  have hbridge :
      (H : ℝ) * D ≤
        8 * (B * ((N : ℝ) * H) +
          (H : ℝ) * (((N : ℝ) * delta) * R)) := by
    calc
      (H : ℝ) * D ≤ 8 * S := hprefix
      _ ≤ 8 * F := mul_le_mul_of_nonneg_left hSF (by norm_num)
      _ ≤ 8 *
          (G + (H : ℝ) * ((((Finset.univ \ good).card : ℕ) : ℝ) * R)) :=
        mul_le_mul_of_nonneg_left hrestore (by norm_num)
      _ ≤ 8 * (B * ((N : ℝ) * H) +
          (H : ℝ) * (((N : ℝ) * delta) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hgood' hbadTerm) (by norm_num)
  change (1 / (N : ℝ)) * D ≤ 8 * (B + delta * R)
  rw [one_div, inv_mul_eq_div]
  calc
    D / (N : ℝ) = ((H : ℝ) * D) / ((H : ℝ) * (N : ℝ)) := by
      field_simp
    _ ≤ (8 * (B * ((N : ℝ) * H) +
          (H : ℝ) * (((N : ℝ) * delta) * R))) /
          ((H : ℝ) * (N : ℝ)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hHR hNR)).2 hbridge
    _ = 8 * (B + delta * R) := by
      field_simp

/-- Full-family consumer form.  The normalized estimate is assumed for the
coefficient-weighted complete divisor family.  Exact Fourier orthogonality
projects that estimate onto `selected`; prefix differences then recover the
selected diagonal block energy.  Restoring the omitted cyclic residue classes
costs exactly the displayed `2 ^ (-k)` term. -/
theorem bcc_full_family_normalized_diagonal_le
    {q k H : ℕ} [NeZero q] (hH : 0 < H)
    {ι : Type*} [DecidableEq ι]
    (selected full : Finset ι) (hsub : selected ⊆ full)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ full, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ full, NeZero (d i))
    (ht : ∀ i ∈ full, NeZero (t i))
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (hN : ∀ i ∈ full, q ^ k = t i * (q * d i))
    (hsep : ∀ i ∈ full, ∀ j ∈ full, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (t i) (q ^ k))
        (SmoothFrequencyLayer q (t j) (q ^ k)))
    (B R : ℝ) (hR : 0 ≤ R)
    (hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ i ∈ full,
                  coeff i * scaledCharacterPrefix χ (d i) L a) ≤ B)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (1 / ((q ^ k : ℕ) : ℝ)) *
        ∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) ≤
      8 *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * R) := by
  letI : NeZero (q ^ k) := ⟨pow_ne_zero k (NeZero.ne q)⟩
  let D : ℝ :=
    ∑ i ∈ selected,
      (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))
  let S : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a : ZMod (q ^ k),
        Complex.normSq
          (∑ i ∈ selected,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  let F : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a : ZMod (q ^ k),
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  let G : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a ∈ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a)
  let delta : ℝ :=
    ((2 * H * q.primeFactors.card : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)
  have hqkR : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos q) k
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hden : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) * H := mul_pos hqkR hHR
  have hprefix : (H : ℝ) * D ≤ 8 * S := by
    exact coeff_block_energy_le_medium_prefix_energy
      selected χ hχ coeff d t
      (fun i hi ↦ hc i (hsub hi))
      (fun i hi ↦ hd i (hsub hi))
      (fun i hi ↦ ht i (hsub hi)) hdH
      (fun i hi ↦ hN i (hsub hi))
      (fun i hi j hj hij ↦ hsep i (hsub hi) j (hsub hj) hij)
  have hSF : S ≤ F := by
    apply Finset.sum_le_sum
    intro L hL
    exact coeff_selected_prefix_energy_le_full
      selected full hsub χ hχ coeff d t hc hd ht hN hsep
  have hrestore :
      F ≤ G + (H : ℝ) *
        ((((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) * R) := by
    exact medium_full_energy_le_good_add_bad
      (cyclicGoodResidues q k H)
      (fun L a ↦ ∑ i ∈ full,
        coeff i * scaledCharacterPrefix χ (d i) L a) R hbad
  have hgood' : G ≤ B * (((q ^ k : ℕ) : ℝ) * H) := by
    change (1 / (((q ^ k : ℕ) : ℝ) * H)) * G ≤ B at hgood
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hden] at hgood
    exact hgood
  have hcomplement :
      (Finset.univ \ cyclicGoodResidues q k H).card =
        (cyclicBadResidues q k H).card := by
    congr 1
    ext a
    simp [cyclicGoodResidues]
  have hbadNat := card_cyclicBadResidues_le_twoPow q k H
  have hbadCast :
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
        (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) := by
    exact_mod_cast hbadNat
  have hquot :
      (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hbadCard :
      (((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) * delta := by
    rw [hcomplement]
    calc
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) :=
        hbadCast
      _ = (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ)) := by norm_num
      _ ≤ (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))) := by
        gcongr
      _ = ((q ^ k : ℕ) : ℝ) * delta := by
        dsimp only [delta]
        ring
  have hbadTerm :
      (H : ℝ) *
          ((((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) * R) ≤
        (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R) := by
    gcongr
  have hbridge :
      (H : ℝ) * D ≤
        8 * (B * (((q ^ k : ℕ) : ℝ) * H) +
          (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R)) := by
    calc
      (H : ℝ) * D ≤ 8 * S := hprefix
      _ ≤ 8 * F := mul_le_mul_of_nonneg_left hSF (by norm_num)
      _ ≤ 8 *
          (G + (H : ℝ) *
            ((((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) * R)) :=
        mul_le_mul_of_nonneg_left hrestore (by norm_num)
      _ ≤ 8 * (B * (((q ^ k : ℕ) : ℝ) * H) +
          (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R)) :=
        mul_le_mul_of_nonneg_left (add_le_add hgood' hbadTerm) (by norm_num)
  change (1 / ((q ^ k : ℕ) : ℝ)) * D ≤ 8 * (B + delta * R)
  rw [one_div, inv_mul_eq_div]
  calc
    D / ((q ^ k : ℕ) : ℝ) =
        ((H : ℝ) * D) /
          ((H : ℝ) * ((q ^ k : ℕ) : ℝ)) := by
      field_simp
    _ ≤ (8 * (B * (((q ^ k : ℕ) : ℝ) * H) +
          (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R))) /
          ((H : ℝ) * ((q ^ k : ℕ) : ℝ)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hHR hqkR)).2 hbridge
    _ = 8 * (B + delta * R) := by
      field_simp

/-- Specialization of `bcc_full_family_normalized_diagonal_le` to a family
of distinct divisors of one power of `q`.  The arbitrary smooth-scale
disjointness theorem supplies all off-diagonal cancellations, including for
incomparable scales. -/
theorem bcc_smooth_full_family_normalized_diagonal_le
    {q k K H : ℕ} [NeZero q] (hH : 0 < H)
    {ι : Type*} [DecidableEq ι]
    (selected full : Finset ι) (hsub : selected ⊆ full)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (coeff : ι → ℂ) (d t : ι → ℕ)
    (hc : ∀ i ∈ full, Complex.normSq (coeff i) = 1)
    (hd : ∀ i ∈ full, NeZero (d i))
    (ht : ∀ i ∈ full, NeZero (t i))
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (hN : ∀ i ∈ full, q ^ k = t i * (q * d i))
    (hsmooth : ∀ i ∈ full, d i ∣ q ^ K)
    (hinj : Set.InjOn d full)
    (B R : ℝ) (hR : 0 ≤ R)
    (hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ i ∈ full,
                  coeff i * scaledCharacterPrefix χ (d i) L a) ≤ B)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ full,
            coeff i * scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (1 / ((q ^ k : ℕ) : ℝ)) *
        ∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) ≤
      8 *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * R) := by
  apply bcc_full_family_normalized_diagonal_le hH selected full hsub χ hχ
    coeff d t hc hd ht hdH hN
  · intro i hi j hj hij
    letI : NeZero (t i) := ht i hi
    letI : NeZero (t j) := ht j hj
    exact smoothFrequencyLayer_disjoint_of_smooth_complements
      (hN i hi) (hN j hj) (hsmooth i hi) (hsmooth j hj)
        (fun hdij ↦ hij (hinj hi hj hdij))
  · exact hR
  · exact hgood
  · exact hbad

/-- Each valid BCC layer has normalized diagonal mass `phi(q) / q`.  Hence a
normalized diagonal estimate bounds the number of retained layers uniformly
when `q` ranges over `q ≤ Q`. -/
theorem bcc_card_le_uniform_of_normalized_diagonal
    {q k Q : ℕ} [NeZero q]
    {ι : Type*} [DecidableEq ι] (selected : Finset ι)
    (d t : ι → ℕ) (hqQ : q ≤ Q)
    (hd : ∀ i ∈ selected, NeZero (d i))
    (ht : ∀ i ∈ selected, NeZero (t i))
    (hN : ∀ i ∈ selected, q ^ k = t i * (q * d i))
    (X : ℝ)
    (hdiag :
      (1 / ((q ^ k : ℕ) : ℝ)) *
          ∑ i ∈ selected,
            (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) ≤ 8 * X) :
    (selected.card : ℝ) ≤ 8 * (Q : ℝ) * X := by
  let E : ℝ :=
    (1 / ((q ^ k : ℕ) : ℝ)) *
      ∑ i ∈ selected,
        (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))
  have hEX : E ≤ 8 * X := hdiag
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hterm (i : ι) (hi : i ∈ selected) :
      (1 / ((q ^ k : ℕ) : ℝ)) *
          ((d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) =
        (q.totient : ℝ) / q := by
    have hNi :
        ((q ^ k : ℕ) : ℝ) =
          (t i : ℝ) * ((q : ℝ) * (d i : ℝ)) := by
      exact_mod_cast hN i hi
    have hdR : (d i : ℝ) ≠ 0 := by exact_mod_cast (hd i hi).out
    have htR : (t i : ℝ) ≠ 0 := by exact_mod_cast (ht i hi).out
    rw [one_div, inv_mul_eq_div, hNi]
    field_simp [hdR, htR]
  have hE : E = (selected.card : ℝ) * ((q.totient : ℝ) / q) := by
    dsimp only [E]
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ selected,
          (1 / ((q ^ k : ℕ) : ℝ)) *
            ((d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)))) =
          ∑ _i ∈ selected, (q.totient : ℝ) / q := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i hi
      _ = (selected.card : ℝ) * ((q.totient : ℝ) / q) := by
        simp [nsmul_eq_mul]
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  have hX0 : 0 ≤ X := by linarith
  have hcardPhi :
      (selected.card : ℝ) ≤
        (selected.card : ℝ) * (q.totient : ℝ) := by
    calc
      (selected.card : ℝ) = (selected.card : ℝ) * 1 := by ring
      _ ≤ (selected.card : ℝ) * (q.totient : ℝ) :=
        mul_le_mul_of_nonneg_left hphi (Nat.cast_nonneg selected.card)
  have hqE :
      (q : ℝ) * E =
        (selected.card : ℝ) * (q.totient : ℝ) := by
    rw [hE]
    field_simp
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  calc
    (selected.card : ℝ) ≤
        (selected.card : ℝ) * (q.totient : ℝ) := hcardPhi
    _ = (q : ℝ) * E := hqE.symm
    _ ≤ (Q : ℝ) * E := mul_le_mul_of_nonneg_right hqQR hE0
    _ ≤ (Q : ℝ) * (8 * X) :=
      mul_le_mul_of_nonneg_left hEX (Nat.cast_nonneg Q)
    _ = 8 * (Q : ℝ) * X := by ring

/-- The finite consumer bridge from a normalized good-residue prefix estimate
to the normalized diagonal BCC energy.  The ambient cyclic modulus is `q ^ k`.
The displayed error is the explicit `2 ^ (-k)` loss coming from restoring the
omitted residue classes. -/
theorem bcc_qpower_normalized_diagonal_le
    {q k H : ℕ} [NeZero q] (hH : 0 < H)
    (s : Finset ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, q ^ k = q ^ i * (q * d i))
    (B R : ℝ) (hR : 0 ≤ R)
    (hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ B)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (1 / ((q ^ k : ℕ) : ℝ)) *
        ∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ)) ≤
      8 *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * R) := by
  letI : NeZero (q ^ k) := ⟨pow_ne_zero k (NeZero.ne q)⟩
  have hqkR : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by positivity
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hden : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) * H := mul_pos hqkR hHR
  let D : ℝ :=
    ∑ i ∈ s,
      (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))
  let G : ℝ :=
    ∑ L ∈ Finset.Ioc H (2 * H),
      ∑ a ∈ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)
  let delta : ℝ :=
    ((2 * H * q.primeFactors.card : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)
  have hgood' : G ≤ B * (((q ^ k : ℕ) : ℝ) * H) := by
    change (1 / (((q ^ k : ℕ) : ℝ) * H)) * G ≤ B at hgood
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hden] at hgood
    exact hgood
  have hcomplement :
      (Finset.univ \ cyclicGoodResidues q k H).card =
        (cyclicBadResidues q k H).card := by
    congr 1
    ext a
    simp [cyclicGoodResidues]
  have hbadNat := card_cyclicBadResidues_le_twoPow q k H
  have hbadCast :
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
        (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) := by
    exact_mod_cast hbadNat
  have hquot :
      (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hbadCard :
      (((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) * delta := by
    rw [hcomplement]
    calc
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) :=
        hbadCast
      _ = (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ)) := by norm_num
      _ ≤ (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))) := by
        gcongr
      _ = ((q ^ k : ℕ) : ℝ) * delta := by
        dsimp only [delta]
        ring
  have hbridge :
      (H : ℝ) * D ≤ 8 *
        (G + (H : ℝ) *
          ((((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) * R)) := by
    exact qpower_block_energy_le_medium_good_prefix_energy
      s χ hχ d hq hd hdH hN (cyclicGoodResidues q k H) R hbad
  have hbadTerm :
      (H : ℝ) *
          ((((Finset.univ \ cyclicGoodResidues q k H).card : ℕ) : ℝ) * R) ≤
        (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R) := by
    gcongr
  have hbridge' :
      (H : ℝ) * D ≤
        8 * (B * (((q ^ k : ℕ) : ℝ) * H) +
          (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R)) := by
    exact hbridge.trans (mul_le_mul_of_nonneg_left
      (add_le_add hgood' hbadTerm) (by norm_num))
  change (1 / ((q ^ k : ℕ) : ℝ)) * D ≤ 8 * (B + delta * R)
  rw [one_div, inv_mul_eq_div]
  calc
    D / ((q ^ k : ℕ) : ℝ) =
        ((H : ℝ) * D) /
          ((H : ℝ) * ((q ^ k : ℕ) : ℝ)) := by
      field_simp
    _ ≤ (8 * (B * (((q ^ k : ℕ) : ℝ) * H) +
          (H : ℝ) * ((((q ^ k : ℕ) : ℝ) * delta) * R))) /
          ((H : ℝ) * ((q ^ k : ℕ) : ℝ)) := by
      exact (div_le_div_iff_of_pos_right (mul_pos hHR hqkR)).2 hbridge'
    _ = 8 * (B + delta * R) := by
      field_simp

/-- Uniform cardinality consequence of the finite BCC prefix bridge.  Every
selected `q`-power layer contributes the same normalized diagonal mass
`phi(q) / q`; using `phi(q) >= 1` and `q <= Q` makes the resulting bound
uniform over all conductors in the finite range `q <= Q`. -/
theorem bcc_qpower_card_le_uniform
    {q k H Q : ℕ} [NeZero q] (hH : 0 < H)
    (s : Finset ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q) (hqQ : q ≤ Q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, q ^ k = q ^ i * (q * d i))
    (B R : ℝ) (hR : 0 ≤ R)
    (hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ B)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H),
      ∀ a ∉ cyclicGoodResidues q k H,
        Complex.normSq
          (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (s.card : ℝ) ≤
      8 * (Q : ℝ) *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * R) := by
  letI : NeZero (q ^ k) := ⟨pow_ne_zero k (NeZero.ne q)⟩
  let X : ℝ :=
    B + (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
      ((2 ^ k : ℕ) : ℝ)) * R
  let E : ℝ :=
    (1 / ((q ^ k : ℕ) : ℝ)) *
      ∑ i ∈ s,
        (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))
  have hEX : E ≤ 8 * X := by
    exact bcc_qpower_normalized_diagonal_le hH s χ hχ d hq hd hdH hN B R hR
      hgood hbad
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hqkR : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by positivity
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hterm (i : ℕ) (hi : i ∈ s) :
      (1 / ((q ^ k : ℕ) : ℝ)) *
          ((d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) =
        (q.totient : ℝ) / q := by
    have hNi :
        ((q ^ k : ℕ) : ℝ) =
          ((q ^ i : ℕ) : ℝ) * ((q : ℝ) * (d i : ℝ)) := by
      exact_mod_cast hN i hi
    have hdR : (d i : ℝ) ≠ 0 := by
      exact_mod_cast (hd i hi).out
    rw [one_div, inv_mul_eq_div]
    rw [hNi]
    field_simp [hdR]
  have hE : E = (s.card : ℝ) * ((q.totient : ℝ) / q) := by
    dsimp only [E]
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ s,
          (1 / ((q ^ k : ℕ) : ℝ)) *
            ((d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ)))) =
          ∑ _i ∈ s, (q.totient : ℝ) / q := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i hi
      _ = (s.card : ℝ) * ((q.totient : ℝ) / q) := by
        simp [nsmul_eq_mul]
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  have hX0 : 0 ≤ X := by linarith
  have hcardPhi : (s.card : ℝ) ≤ (s.card : ℝ) * (q.totient : ℝ) := by
    calc
      (s.card : ℝ) = (s.card : ℝ) * 1 := by ring
      _ ≤ (s.card : ℝ) * (q.totient : ℝ) :=
        mul_le_mul_of_nonneg_left hphi (Nat.cast_nonneg s.card)
  have hqE : (q : ℝ) * E = (s.card : ℝ) * (q.totient : ℝ) := by
    rw [hE]
    field_simp
  have hqQR : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  calc
    (s.card : ℝ) ≤ (s.card : ℝ) * (q.totient : ℝ) := hcardPhi
    _ = (q : ℝ) * E := hqE.symm
    _ ≤ (Q : ℝ) * E := mul_le_mul_of_nonneg_right hqQR hE0
    _ ≤ (Q : ℝ) * (8 * X) := mul_le_mul_of_nonneg_left hEX (Nat.cast_nonneg Q)
    _ = 8 * (Q : ℝ) * X := by ring

private def addOneEmbedding {N : ℕ} [NeZero N] : ZMod N ↪ ZMod N :=
  (Equiv.addRight (1 : ZMod N)).toEmbedding

/-- Translate the cyclic good residue classes by one.  This is the exact
spatial shift needed because `scaledCharacterPrefix` starts at shift zero,
whereas the discrepancy prefix starts at shift one. -/
def shiftedCyclicGoodResidues (q k H : ℕ) [NeZero q] :
    Finset (ZMod (q ^ k)) :=
  (cyclicGoodResidues q k H).map addOneEmbedding

/-- The actual discrepancy prefix of the unit-circle-valued completely
multiplicative extension on a cyclic translate. -/
def cyclicPrimeExtensionIccPrefix (z : PrimeAssignment) {q k : ℕ} [NeZero q]
    (L : ℕ) (a : ZMod (q ^ k)) : ℂ :=
  ∑ m ∈ Finset.Icc 1 L,
    (primeExtension z (a + (m : ZMod (q ^ k))).val : ℂ)

/-- Translation preserves the number of exceptional cyclic residues. -/
theorem card_compl_shiftedCyclicGoodResidues (q k H : ℕ) [NeZero q] :
    (Finset.univ \ shiftedCyclicGoodResidues q k H).card =
      (Finset.univ \ cyclicGoodResidues q k H).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    shiftedCyclicGoodResidues, Finset.card_map]

/-- On the translated good set, the full coefficient-weighted divisor-family
energy is exactly the energy of the genuine discrepancy prefixes. -/
theorem sum_shifted_good_fullDivisor_normSq_eq_actual
    (z : PrimeAssignment) {q k H L : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) (hL : L ≤ 2 * H) :
    (∑ b ∈ shiftedCyclicGoodResidues q k H,
        Complex.normSq
          (∑ d ∈ (q ^ (k - 1)).divisors,
            (primeExtension z d : ℂ) * scaledCharacterPrefix χ d L b)) =
      ∑ a ∈ cyclicGoodResidues q k H,
        Complex.normSq (cyclicPrimeExtensionIccPrefix z L a) := by
  rw [shiftedCyclicGoodResidues, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  have hadd : addOneEmbedding a = a + 1 := rfl
  rw [hadd]
  simpa only [cyclicPrimeExtensionIccPrefix] using
    congrArg Complex.normSq
      (fullDivisorPrefix_eq_primeExtensionPrefix_Icc
        z χ hagree hq ha hL)

/-- Final uniform finite BCC consequence for the actual modified character.
Every divisor of `q ^ (k - 1)` is retained in the full family, with its genuine
unit coefficient `primeExtension z d`; Fourier orthogonality then projects to
the selected divisors.  The last summand is the explicit exceptional-residue
loss `2 ^ (-k)` times the sharp trivial prefix bound `(2H)^2`. -/
theorem modifiedCharacter_selected_card_le_uniform
    {q k H Q : ℕ} [NeZero q]
    (hk : 0 < k) (hH : 0 < H)
    (z : PrimeAssignment)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) (hqQ : q ≤ Q)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hactual :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq (cyclicPrimeExtensionIccPrefix z L a) ≤ B) :
    (selected.card : ℝ) ≤
      8 * (Q : ℝ) *
        (B +
          (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
              ((2 ^ k : ℕ) : ℝ)) * (((2 * H : ℕ) : ℝ) ^ 2)) := by
  letI : NeZero (q ^ k) := ⟨pow_ne_zero k (NeZero.ne q)⟩
  let all : Finset ℕ := (q ^ (k - 1)).divisors
  let coeff : ℕ → ℂ := fun d ↦ (primeExtension z d : ℂ)
  let scale : ℕ → ℕ := fun d ↦ d
  let complement : ℕ → ℕ := fun d ↦ q ^ k / (q * d)
  let good : Finset (ZMod (q ^ k)) := shiftedCyclicGoodResidues q k H
  let R : ℝ := (((2 * H : ℕ) : ℝ) ^ 2)
  let delta : ℝ :=
    ((2 * H * q.primeFactors.card : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ)
  have hdall : ∀ d ∈ all, NeZero (scale d) := by
    intro d hd
    have hddiv : d ∣ q ^ (k - 1) := by
      exact Nat.dvd_of_mem_divisors hd
    exact ⟨(Nat.pos_of_dvd_of_pos hddiv (pow_pos (NeZero.pos q) _)).ne'⟩
  have htall : ∀ d ∈ all, NeZero (complement d) := by
    intro d hd
    letI : NeZero d := hdall d hd
    exact neZero_pow_div_q_mul hk (Nat.dvd_of_mem_divisors hd)
  have hNall : ∀ d ∈ all,
      q ^ k = complement d * (q * scale d) := by
    intro d hd
    exact pow_eq_div_q_mul_mul_q_mul hk (Nat.dvd_of_mem_divisors hd)
  have hcoeff : ∀ d ∈ all, Complex.normSq (coeff d) = 1 := by
    intro d _hd
    exact normSq_primeExtension_coe z d
  have hsep : ∀ i ∈ all, ∀ j ∈ all, i ≠ j →
      Disjoint (SmoothFrequencyLayer q (complement i) (q ^ k))
        (SmoothFrequencyLayer q (complement j) (q ^ k)) := by
    intro i hi j hj hij
    letI : NeZero (complement i) := htall i hi
    letI : NeZero (complement j) := htall j hj
    exact smoothFrequencyLayer_disjoint_of_smooth_complements
      (hNall i hi) (hNall j hj)
      (Nat.dvd_of_mem_divisors hi) (Nat.dvd_of_mem_divisors hj) hij
  have hgood :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ d ∈ all,
                  coeff d * scaledCharacterPrefix χ (scale d) L a) ≤ B := by
    calc
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ d ∈ all,
                  coeff d * scaledCharacterPrefix χ (scale d) L a) =
        (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq (cyclicPrimeExtensionIccPrefix z L a) := by
        congr 1
        apply Finset.sum_congr rfl
        intro L hL
        simpa only [good, all, coeff, scale] using
          sum_shifted_good_fullDivisor_normSq_eq_actual
            z χ hagree hq (Finset.mem_Ioc.mp hL).2
      _ ≤ B := hactual
  have hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ d ∈ all,
          coeff d * scaledCharacterPrefix χ (scale d) L a) ≤ R := by
    intro L hL a _ha
    have hLtwo : (L : ℝ) ^ 2 ≤ (((2 * H : ℕ) : ℝ) ^ 2) := by
      have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hL).2
      have hLleR : (L : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hLle
      have hL0 : (0 : ℝ) ≤ L := by positivity
      have htwo0 : (0 : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by positivity
      nlinarith
    exact (normSq_fullDivisor_scaledCharacterPrefix_le z χ hq a).trans hLtwo
  have hcard : (((Finset.univ \ good).card : ℕ) : ℝ) ≤
      ((q ^ k : ℕ) : ℝ) * delta := by
    have hcomplement :
        (Finset.univ \ good).card =
          (cyclicBadResidues q k H).card := by
      rw [show good = shiftedCyclicGoodResidues q k H from rfl,
        card_compl_shiftedCyclicGoodResidues]
      congr 1
      ext a
      simp [cyclicGoodResidues]
    have hbadNat := card_cyclicBadResidues_le_twoPow q k H
    have hbadCast :
        (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) := by
      exact_mod_cast hbadNat
    have hquot :
        (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ) ≤
          ((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcomplement]
    calc
      (((cyclicBadResidues q k H).card : ℕ) : ℝ) ≤
          (((2 * H) * q.primeFactors.card * (q ^ k / 2 ^ k) : ℕ) : ℝ) :=
        hbadCast
      _ = (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k / 2 ^ k : ℕ) : ℕ) : ℝ)) := by norm_num
      _ ≤ (((2 * H * q.primeFactors.card : ℕ) : ℝ) *
            (((q ^ k : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ))) := by
        gcongr
      _ = ((q ^ k : ℕ) : ℝ) * delta := by
        dsimp only [delta]
        ring
  have hdiag := bcc_full_family_normalized_diagonal_le_of_good
    hH selected all hselected χ hχ coeff scale complement hcoeff hdall htall hdH
      hNall hsep good B R delta (by positivity) hcard hgood hbad
  exact bcc_card_le_uniform_of_normalized_diagonal selected scale complement hqQ
    (fun d hd ↦ hdall d (hselected hd))
    (fun d hd ↦ htall d (hselected hd))
    (fun d hd ↦ hNall d (hselected hd))
    (B + delta * R) hdiag

/-- Finite contradiction form of `modifiedCharacter_selected_card_le_uniform`.
It is the direct consumer endpoint for a selected divisor family whose size
exceeds the bound forced by the actual modified-character prefix energy. -/
theorem modifiedCharacter_selected_family_contradiction
    {q k H Q : ℕ} [NeZero q]
    (hk : 0 < k) (hH : 0 < H)
    (z : PrimeAssignment)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hagree : AgreesWithCharacterAway z χ)
    (hq : 1 < q) (hqQ : q ≤ Q)
    (selected : Finset ℕ)
    (hselected : selected ⊆ (q ^ (k - 1)).divisors)
    (hdH : ∀ d ∈ selected, 2 * d ≤ H)
    (B : ℝ)
    (hactual :
      (1 / (((q ^ k : ℕ) : ℝ) * H)) *
          ∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ cyclicGoodResidues q k H,
              Complex.normSq (cyclicPrimeExtensionIccPrefix z L a) ≤ B)
    (hlarge :
      8 * (Q : ℝ) *
          (B +
            (((2 * H * q.primeFactors.card : ℕ) : ℝ) /
                ((2 ^ k : ℕ) : ℝ)) * (((2 * H : ℕ) : ℝ) ^ 2)) <
        (selected.card : ℝ)) : False := by
  exact (not_lt_of_ge (modifiedCharacter_selected_card_le_uniform
    hk hH z χ hχ hagree hq hqQ selected hselected hdH B hactual)) hlarge

end

end Erdos67b
