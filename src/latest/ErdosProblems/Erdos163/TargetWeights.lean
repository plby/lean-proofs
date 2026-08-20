/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.TargetParts

/-!
# Geometric weights for the target layers

Lee assigns mass which is constant on blocks of target layers.  The two
elementary estimates below give both the finite total mass and the summable
ratio between a layer size and its assigned mass.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace TargetWeights

noncomputable section

def blockWeight (L i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i / L)

theorem blockWeight_nonneg (L i : ℕ) : 0 ≤ blockWeight L i := by
  exact pow_nonneg (by norm_num) _

theorem blockWeight_le_one (L i : ℕ) : blockWeight L i ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The block-constant geometric series has total mass at most `2L`. -/
theorem sum_range_blockWeight_le {L : ℕ} (hL : 0 < L) (m : ℕ) :
    ∑ i ∈ Finset.range m, blockWeight L i ≤ 2 * L := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m ≤ L
      · calc
          (∑ i ∈ Finset.range m, blockWeight L i) ≤
              ∑ _i ∈ Finset.range m, (1 : ℝ) := by
            exact Finset.sum_le_sum fun i hi => blockWeight_le_one L i
          _ = m := by simp
          _ ≤ 2 * L := by exact_mod_cast (hm.trans (by omega : L ≤ 2 * L))
      · have hLm : L < m := Nat.lt_of_not_ge hm
        let k := m - L
        have hk : k < m := by dsimp [k]; omega
        have hmEq : L + k = m := by dsimp [k]; omega
        have hshift : ∀ i,
            blockWeight L (L + i) = (1 / 2 : ℝ) * blockWeight L i := by
          intro i
          simp only [blockWeight, Nat.add_div_left i hL, pow_succ]
          ring
        rw [← hmEq, Finset.sum_range_add]
        simp_rw [hshift]
        rw [← Finset.mul_sum]
        have hfirst : (∑ i ∈ Finset.range L, blockWeight L i) ≤ L := by
          calc
            (∑ i ∈ Finset.range L, blockWeight L i) ≤
                ∑ _i ∈ Finset.range L, (1 : ℝ) := by
              exact Finset.sum_le_sum fun i hi => blockWeight_le_one L i
            _ = L := by simp
        have htail := ih k hk
        have hhalf : (1 / 2 : ℝ) *
            (∑ i ∈ Finset.range k, blockWeight L i) ≤ L := by
          calc
            (1 / 2 : ℝ) * (∑ i ∈ Finset.range k, blockWeight L i) ≤
                (1 / 2 : ℝ) * (2 * L) :=
              mul_le_mul_of_nonneg_left htail (by norm_num)
            _ = L := by ring
        exact (add_le_add hfirst hhalf).trans_eq (by ring)

theorem block_le_index {L i : ℕ} (hL : 0 < L) : i / L ≤ i := by
  exact Nat.div_le_self i L

theorem twice_block_le_index {L i : ℕ} (hL : 2 ≤ L) : 2 * (i / L) ≤ i := by
  have hmul := Nat.div_mul_le_self i L
  have : 2 * (i / L) ≤ L * (i / L) := Nat.mul_le_mul_right (i / L) hL
  exact this.trans (by simpa [Nat.mul_comm] using hmul)

theorem blockGrowth_div_pow_le {L i : ℕ} (hL : 2 ≤ L) :
    (2 : ℝ) ^ (i / L) / (2 : ℝ) ^ i ≤ blockWeight L i := by
  let b := i / L
  have hbi : b ≤ i := block_le_index (by omega : 0 < L)
  have htwice : 2 * b ≤ i := twice_block_le_index hL
  have hpow : (2 : ℝ) ^ i = 2 ^ b * 2 ^ (i - b) := by
    rw [← pow_add, Nat.add_sub_of_le hbi]
  have heq : (2 : ℝ) ^ b / (2 : ℝ) ^ i = (1 / 2 : ℝ) ^ (i - b) := by
    rw [hpow, one_div_pow]
    field_simp
  rw [heq]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem sum_range_blockGrowth_div_pow_le {L : ℕ} (hL : 2 ≤ L) (m : ℕ) :
    ∑ i ∈ Finset.range m, (2 : ℝ) ^ (i / L) / (2 : ℝ) ^ i ≤ 2 * L := by
  exact (Finset.sum_le_sum fun i hi => blockGrowth_div_pow_le hL).trans
    (sum_range_blockWeight_le (by omega) m)

def mass {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} (L Q : ℕ)
    (p : TargetParts.OccupiedPart layer c) : ℝ :=
  1 / ((Q : ℝ) * (2 : ℝ) ^ (TargetParts.layerOf p / L))

theorem mass_pos {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} {L Q : ℕ} (hQ : 0 < Q)
    (p : TargetParts.OccupiedPart layer c) : 0 < mass L Q p := by
  unfold mass
  positivity

/-- Passing from occupied pairs to all layer-colour pairs and summing the
block-geometric series gives the total-mass estimate. -/
theorem sum_mass_le {n d L Q : ℕ} (hL : 0 < L)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1)) :
    ∑ p : TargetParts.OccupiedPart layer c, mass L Q p ≤
      ((d + 1 : ℕ) : ℝ) * (2 * L : ℕ) / Q := by
  let f : TargetParts.PartKey n d → ℝ := fun p =>
    1 / ((Q : ℝ) * (2 : ℝ) ^ (p.1.1 / L))
  have hsub : ∑ p : TargetParts.OccupiedPart layer c, f p.1 ≤
      ∑ p : TargetParts.PartKey n d, f p := by
    rw [← Finset.sum_image]
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hnot
      dsimp [f]
      positivity
    · intro a ha b hb hab
      exact Subtype.ext hab
  calc
    (∑ p : TargetParts.OccupiedPart layer c, mass L Q p) =
        ∑ p : TargetParts.OccupiedPart layer c, f p.1 := by rfl
    _ ≤ ∑ p : TargetParts.PartKey n d, f p := hsub
    _ = ∑ l : Fin (n + 1), ∑ _j : Fin (d + 1),
        1 / ((Q : ℝ) * (2 : ℝ) ^ (l.1 / L)) := by
      rw [Fintype.sum_prod_type]
    _ = ((d + 1 : ℕ) : ℝ) *
        (∑ l : Fin (n + 1), blockWeight L l.1) / Q := by
      have hterm : ∀ l : Fin (n + 1),
          1 / ((Q : ℝ) * (2 : ℝ) ^ (l.1 / L)) = blockWeight L l.1 / Q := by
        intro l
        simp only [blockWeight]
        rw [one_div_pow]
        field_simp
      simp_rw [hterm]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      calc
        (∑ l : Fin (n + 1), ((d + 1 : ℕ) : ℝ) *
            (blockWeight L l.1 / Q)) =
            ((d + 1 : ℕ) : ℝ) *
              (∑ l : Fin (n + 1), blockWeight L l.1 / Q) := by
                rw [Finset.mul_sum]
        _ = ((d + 1 : ℕ) : ℝ) *
              (∑ l : Fin (n + 1), blockWeight L l.1) / Q := by
                norm_num [Nat.cast_add]
                rw [← Finset.sum_div]
                exact (mul_div_assoc _ _ _).symm
    _ = ((d + 1 : ℕ) : ℝ) *
        (∑ l ∈ Finset.range (n + 1), blockWeight L l) / Q := by
      rw [Fin.sum_univ_eq_sum_range]
    _ ≤ ((d + 1 : ℕ) : ℝ) * (2 * L : ℕ) / Q := by
      gcongr
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        sum_range_blockWeight_le hL (n + 1)

def threshold {n d : ℕ} {layer : Fin n → Fin (n + 1)}
    {c : Fin n → Fin (d + 1)} (L Q τ : ℕ)
    (p : TargetParts.OccupiedPart layer c) : ℕ :=
  ⌊mass L Q p * τ / 4⌋₊

theorem real_half_le_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hlt := Nat.lt_floor_add_one x
  have hfloor0 : (0 : ℝ) ≤ ⌊x⌋₊ := by positivity
  nlinarith

theorem blockPow_le_layerPow {L i : ℕ} (hL : 0 < L) :
    2 ^ (i / L) ≤ 2 ^ i := by
  exact Nat.pow_le_pow_right (by omega) (block_le_index hL)

/-- With a base host reserve at least `8Q` times the target order, the
integer threshold attached to a part is at least twice that part's size. -/
theorem twice_partVertices_le_threshold
    {n d L Q τ : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 0 < L) (hQ : 0 < Q) (hτ : 8 * Q * n ≤ τ)
    (x : Fin n) :
    2 * (RandomGreedy.partVertices (TargetParts.part layer c) x).card ≤
      threshold L Q τ (TargetParts.part layer c x) := by
  let b := 2 ^ ((layer x).1 / L)
  let z := (RandomGreedy.partVertices (TargetParts.part layer c) x).card
  have hb : b ≤ 2 ^ (layer x).1 := blockPow_le_layerPow hL
  have hz := TargetParts.pow_mul_partVertices_card_le
    H hd hdeg layer c hlayer x
  have hbz : b * z ≤ n := by
    exact (Nat.mul_le_mul_right z hb).trans hz
  have hnat : 2 * z * (4 * (Q * b)) ≤ τ := by
    calc
      2 * z * (4 * (Q * b)) = 8 * Q * (b * z) := by ring
      _ ≤ 8 * Q * n := Nat.mul_le_mul_left (8 * Q) hbz
      _ ≤ τ := hτ
  apply Nat.le_floor
  change ((2 * z : ℕ) : ℝ) ≤ mass L Q (TargetParts.part layer c x) * τ / 4
  have hden : (0 : ℝ) < 4 * ((Q : ℝ) * (b : ℝ)) := by positivity
  rw [mass]
  simp only [TargetParts.layerOf_part]
  have hbR : (2 : ℝ) ^ ((layer x).1 / L) = (b : ℝ) := by
    norm_num [b]
  rw [hbR]
  change ((2 * z : ℕ) : ℝ) ≤ (1 / ((Q : ℝ) * (b : ℝ))) * τ / 4
  rw [show (1 / ((Q : ℝ) * (b : ℝ))) * τ / 4 =
      (τ : ℝ) / (4 * ((Q : ℝ) * (b : ℝ))) by ring]
  apply (le_div_iff₀ hden).2
  exact_mod_cast hnat

theorem threshold_pos
    {n d L Q τ : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 0 < L) (hQ : 0 < Q) (hτ : 8 * Q * n ≤ τ)
    (p : TargetParts.OccupiedPart layer c) : 0 < threshold L Q τ p := by
  obtain ⟨x, hx⟩ := p.property
  have hpx : TargetParts.part layer c x = p := Subtype.ext hx
  rw [← hpx]
  have hnonempty : 0 <
      (RandomGreedy.partVertices (TargetParts.part layer c) x).card := by
    rw [Finset.card_pos]
    exact ⟨x, by simp [RandomGreedy.partVertices]⟩
  exact (by omega : 0 < 2 *
    (RandomGreedy.partVertices (TargetParts.part layer c) x).card).trans_le
      (twice_partVertices_le_threshold H hd hdeg layer c hlayer hL hQ hτ x)

theorem threshold_le_mass_mul
    {n d L Q τ : ℕ} (layer : Fin n → Fin (n + 1))
    (c : Fin n → Fin (d + 1)) (p : TargetParts.OccupiedPart layer c) :
    (threshold L Q τ p : ℝ) ≤ mass L Q p * τ / 4 := by
  apply Nat.floor_le
  unfold mass
  positivity

theorem mass_mul_div_eight_le_threshold
    {n d L Q τ : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 0 < L) (hQ : 0 < Q) (hτ : 8 * Q * n ≤ τ)
    (p : TargetParts.OccupiedPart layer c) :
    mass L Q p * τ / 8 ≤ (threshold L Q τ p : ℝ) := by
  have hx : (2 : ℝ) ≤ mass L Q p * τ / 4 := by
    obtain ⟨x, hp⟩ := p.property
    have hpx : TargetParts.part layer c x = p := Subtype.ext hp
    have hcard : 0 <
        (RandomGreedy.partVertices (TargetParts.part layer c) x).card := by
      rw [Finset.card_pos]
      exact ⟨x, by simp [RandomGreedy.partVertices]⟩
    have htwo : 2 ≤ threshold L Q τ (TargetParts.part layer c x) :=
      (by omega : 2 ≤ 2 *
        (RandomGreedy.partVertices (TargetParts.part layer c) x).card).trans
        (twice_partVertices_le_threshold H hd hdeg layer c hlayer hL hQ hτ x)
    rw [← hpx]
    exact (Nat.cast_le.2 htwo).trans
      (threshold_le_mass_mul layer c _)
  have := real_half_le_floor hx
  calc
    mass L Q p * τ / 8 = (mass L Q p * τ / 4) / 2 := by ring
    _ ≤ (threshold L Q τ p : ℝ) := by simpa [threshold] using this

/-- The target decomposition makes the reciprocal-mass contribution
summable: layer `i` has at most `n / 2^i` vertices, whereas its reciprocal
mass grows only like `2^(i/L)`. -/
theorem sum_blockPow_layer_le
    {n d L : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 2 ≤ L) :
    ∑ x : Fin n, (2 : ℝ) ^ ((layer x).1 / L) ≤ (2 * L : ℕ) * n := by
  rw [← Fintype.sum_fiberwise layer
    (fun x : Fin n => (2 : ℝ) ^ ((layer x).1 / L))]
  have hfiber : ∀ l : Fin (n + 1),
      Fintype.card {x : Fin n // layer x = l} ≤
        (Decomposition.levels H d l.1).card := by
    intro l
    let f := fun x : {x : Fin n // layer x = l} =>
      (⟨x.1, by
        have hx := Decomposition.mem_levels_layerIndex H hd hdeg x.1
        have hlval : (layer x.1).1 = l.1 := congrArg Fin.val x.property
        rw [← hlayer x.1, hlval] at hx
        exact hx⟩ : ↥(Decomposition.levels H d l.1))
    have hinj : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
    have hc := Fintype.card_le_of_injective f hinj
    simpa only [Fintype.card_coe] using hc
  have hterm : ∀ l : Fin (n + 1),
      (∑ x : {x : Fin n // layer x = l},
          (2 : ℝ) ^ ((layer x.1).1 / L)) ≤
        (n : ℝ) * blockWeight L l.1 := by
    intro l
    have hlevel := Decomposition.pow_mul_card_levels_le H hd hdeg l.1
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ l.1 := by positivity
    have hlevelR : ((Decomposition.levels H d l.1).card : ℝ) ≤
        (n : ℝ) / (2 : ℝ) ^ l.1 := by
      apply (le_div_iff₀ hpowpos).2
      have hlevel' : (Decomposition.levels H d l.1).card * 2 ^ l.1 ≤ n := by
        simpa [Nat.mul_comm] using hlevel
      exact_mod_cast hlevel'
    have hfiberR : (Fintype.card {x : Fin n // layer x = l} : ℝ) ≤
        ((Decomposition.levels H d l.1).card : ℝ) := by
      exact_mod_cast hfiber l
    have hratio := blockGrowth_div_pow_le hL (i := l.1)
    calc
      (∑ x : {x : Fin n // layer x = l},
          (2 : ℝ) ^ ((layer x.1).1 / L)) =
          (Fintype.card {x : Fin n // layer x = l} : ℝ) *
            (2 : ℝ) ^ (l.1 / L) := by
        simp only [show ∀ x : {x : Fin n // layer x = l},
          (layer x.1).1 = l.1 from fun x => congrArg Fin.val x.property,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((Decomposition.levels H d l.1).card : ℝ) *
            (2 : ℝ) ^ (l.1 / L) :=
        mul_le_mul_of_nonneg_right hfiberR (by positivity)
      _ ≤ ((n : ℝ) / (2 : ℝ) ^ l.1) *
            (2 : ℝ) ^ (l.1 / L) :=
        mul_le_mul_of_nonneg_right hlevelR (by positivity)
      _ = (n : ℝ) *
            ((2 : ℝ) ^ (l.1 / L) / (2 : ℝ) ^ l.1) := by ring
      _ ≤ (n : ℝ) * blockWeight L l.1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  calc
    (∑ l : Fin (n + 1),
        ∑ x : {x : Fin n // layer x = l},
          (2 : ℝ) ^ ((layer x.1).1 / L)) ≤
      ∑ l : Fin (n + 1), (n : ℝ) * blockWeight L l.1 :=
        Finset.sum_le_sum fun l hl => hterm l
    _ = (n : ℝ) *
        (∑ i ∈ Finset.range (n + 1), blockWeight L i) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
    _ ≤ (n : ℝ) * (2 * L : ℕ) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          sum_range_blockWeight_le (by omega : 0 < L) (n + 1)) (by positivity)
    _ = ((2 * L : ℕ) : ℝ) * n := by ring

theorem sum_two_div_threshold_le
    {n d L Q τ : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 2 ≤ L) (hQ : 0 < Q) (hτ : 8 * Q * n ≤ τ) :
    ∑ x : Fin n,
        2 / (threshold L Q τ (TargetParts.part layer c x) : ℝ) ≤
      (32 : ℝ) * Q * L * n / τ := by
  have hpoint : ∀ x : Fin n,
      2 / (threshold L Q τ (TargetParts.part layer c x) : ℝ) ≤
        (16 : ℝ) * Q * (2 : ℝ) ^ ((layer x).1 / L) / τ := by
    intro x
    have hlower := mass_mul_div_eight_le_threshold H hd hdeg layer c hlayer
      (by omega : 0 < L) hQ hτ (TargetParts.part layer c x)
    have hmass := mass_pos (L := L) hQ (TargetParts.part layer c x)
    have hτpos : (0 : ℝ) < τ := by
      have hn : 0 < n := x.pos
      exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 8 * Q * n) hτ)
    have hthresholdR : (0 : ℝ) < threshold L Q τ
        (TargetParts.part layer c x) := by
      exact_mod_cast threshold_pos H hd hdeg layer c hlayer
        (by omega : 0 < L) hQ hτ _
    apply (div_le_iff₀ hthresholdR).2
    have hden : (0 : ℝ) < (Q : ℝ) *
        (2 : ℝ) ^ ((layer x).1 / L) := by positivity
    rw [mass, TargetParts.layerOf_part] at hlower hmass
    have hrewrite : (16 : ℝ) * Q *
          (2 : ℝ) ^ ((layer x).1 / L) / τ *
          (mass L Q (TargetParts.part layer c x) * τ / 8) = 2 := by
      rw [mass, TargetParts.layerOf_part]
      field_simp
      ring
    calc
      (2 : ℝ) ≤ (16 : ℝ) * Q * (2 : ℝ) ^ ((layer x).1 / L) / τ *
          (mass L Q (TargetParts.part layer c x) * τ / 8) :=
        le_of_eq hrewrite.symm
      _ ≤ (16 : ℝ) * Q * (2 : ℝ) ^ ((layer x).1 / L) / τ *
          threshold L Q τ (TargetParts.part layer c x) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  calc
    (∑ x : Fin n,
        2 / (threshold L Q τ (TargetParts.part layer c x) : ℝ)) ≤
      ∑ x : Fin n,
        (16 : ℝ) * Q * (2 : ℝ) ^ ((layer x).1 / L) / τ :=
      Finset.sum_le_sum fun x hx => hpoint x
    _ = ((16 : ℝ) * Q / τ) *
        ∑ x : Fin n, (2 : ℝ) ^ ((layer x).1 / L) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ((16 : ℝ) * Q / τ) * ((2 * L : ℕ) * n) :=
      mul_le_mul_of_nonneg_left
        (sum_blockPow_layer_le H hd hdeg layer hlayer hL) (by positivity)
    _ = (32 : ℝ) * Q * L * n / τ := by
      push_cast
      ring

end
end TargetWeights
end Erdos163
