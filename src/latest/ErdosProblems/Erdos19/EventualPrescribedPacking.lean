import ErdosProblems.Erdos19.PrescribedPacking
import ErdosProblems.Erdos19.PackingParameters
import ErdosProblems.Erdos19.ReservoirGraph

/-! # Prescribed matching packing in sufficiently large dense graphs

Every matching covers its prescribed even set. The omitted vertices are sparse
both in each round and over the full sequence at each vertex.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_prescribed_matching_packing (k : ℕ) (hk : 8 ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∀ m : ℕ, k * m + 4 * n ≤ k * n → ∀ A : ℕ → Set (Fin n),
      (∀ i < m, Even (A i).ncard) →
      (∀ i < m, ((A i)ᶜ.ncard : ℝ) ≤ delta * n) →
      (∀ v, ((∑ i ∈ range m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤ delta * n) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = A i) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  classical
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  let K := 1000 * k * k
  let B := 10000 * k * k
  obtain ⟨epsilon, hepsilon, N₁, hN₁⟩ := eventually_packing_load_small k K B (by dsimp [B]; positivity)
  let alpha : ℝ := 1 / (100 * k)
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  obtain ⟨deltaR, hdeltaR, N₂, hN₂⟩ := eventually_exists_reservoir_graph k hkpos
    alpha (epsilon / 2) halpha (by positivity)
  let delta := min deltaR epsilon
  have hdelta : 0 < delta := lt_min hdeltaR hepsilon
  refine ⟨delta, hdelta, max (max N₁ N₂) B, ?_⟩
  intro n hn G hG m hm A heven hsmall habs
  have hn₁ : N₁ ≤ n := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hn₂ : N₂ ≤ n := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hnB : B ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le (by dsimp [B]; positivity) hnB
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmlen : m ≤ n := by
    have hmul : k * m ≤ k * n := by omega
    exact Nat.le_of_mul_le_mul_left hmul hkpos
  have hdeltaE : delta ≤ epsilon := min_le_right _ _
  have hdeltaR' : delta ≤ deltaR := min_le_left _ _
  have hdeltaEn := mul_le_mul_of_nonneg_right hdeltaE hnR.le
  have hdeltaRn := mul_le_mul_of_nonneg_right hdeltaR' hnR.le
  obtain ⟨R, hRG, hdegrees, hcuts⟩ := hN₂ n hn₂ G (fun v ↦ by
    have hv := hG v
    nlinarith only [hv, hdeltaRn])
  let a := ⌈epsilon * n⌉₊ + 1
  let r := n / k + 1
  let q := n / (100 * k) + 1
  let b := n / K
  let L := packingLoadBound n a k K m
  have halo : epsilon * n + 1 ≤ (a : ℝ) := by
    have h := Nat.le_ceil (epsilon * n)
    dsimp only [a]
    push_cast
    linarith only [h]
  have hahi : (a : ℝ) ≤ epsilon * n + 2 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hepsilon.le hnR.le)
    dsimp only [a]
    push_cast
    linarith only [h]
  obtain ⟨ha, hL⟩ := hN₁ n hn₁ a hahi m hmlen
  obtain ⟨hri, hsize, hbad, hb, hmargin, hcutmargin⟩ :=
    packing_parameter_margins n k m a L hk hnB hm ha hL
  have hrlo : (n : ℝ) / k ≤ r := by
    apply (div_le_iff₀ hkR).mpr
    have h := (Nat.lt_mul_div_succ n hkpos).le
    have h' : (n : ℝ) ≤ (k : ℝ) * r := by exact_mod_cast h
    nlinarith only [h']
  have hrhi : (r : ℝ) ≤ (n : ℝ) / k + 1 := by
    have h : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
    dsimp only [r]
    push_cast
    linarith only [h]
  have hqlo : alpha * n ≤ (q : ℝ) := by
    have h : (n : ℝ) ≤ (100 * k : ℝ) * q := by
      exact_mod_cast (Nat.lt_mul_div_succ n (show 0 < 100 * k by positivity)).le
    have h' : (n : ℝ) / (100 * k) ≤ q := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [h])
    calc
      alpha * n = (n : ℝ) / (100 * k) := by dsimp only [alpha]; ring
      _ ≤ q := h'
  have hsmallNat : ∀ i < m, (A i)ᶜ.ncard ≤ a := by
    intro i hi
    have h := (hsmall i hi).trans hdeltaEn
    have h' : ((A i)ᶜ.ncard : ℝ) ≤ a := by linarith only [h, halo]
    exact_mod_cast h'
  have habsNat : ∀ v, ∑ i ∈ range m, (if v ∈ A i then 0 else 1) ≤ a := by
    intro v
    have h := (habs v).trans hdeltaEn
    have h' : ((∑ i ∈ range m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤ a := by
      linarith only [h, halo]
    exact_mod_cast h'
  have hGnat : ∀ v, n ≤ (G.neighborSet v).ncard + a := by
    intro v
    have hv := hG v
    have h' : (n : ℝ) ≤ G.degree v + a := by nlinarith only [hv, halo, hdeltaEn]
    have h'' : n ≤ G.degree v + a := by exact_mod_cast h'
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using h''
  have hRlo : ∀ v, r ≤ (R.neighborSet v).ncard + a := by
    intro v
    have hv := (abs_lt.mp (hdegrees v)).1
    have h' : (r : ℝ) ≤ R.degree v + a := by
      nlinarith only [hv, hrhi, halo, mul_nonneg hepsilon.le hnR.le]
    have h'' : r ≤ R.degree v + a := by exact_mod_cast h'
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using h''
  have hRhi : ∀ v, (R.neighborSet v).ncard ≤ r + a := by
    intro v
    have hv := (abs_lt.mp (hdegrees v)).2
    have h' : (R.degree v : ℝ) ≤ r + a := by
      nlinarith only [hv, hrlo, halo, mul_nonneg hepsilon.le hnR.le]
    have h'' : R.degree v ≤ r + a := by exact_mod_cast h'
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using h''
  have hcut : ∀ X Y : Finset (Fin n), Disjoint X Y → X.card = q → Y.card = q →
      q * (L + 1) < (R.between (X : Set (Fin n)) (Y : Set (Fin n))).edgeSet.ncard := by
    intro X Y hXY hX hY
    have h := hcuts X Y hXY (by simpa only [hX] using hqlo) (by simpa only [hY] using hqlo)
    rw [hX, hY] at h
    have hmarginR : (2 * k : ℝ) * (L + 1) ≤ q := by exact_mod_cast hcutmargin
    have hprod := mul_le_mul_of_nonneg_left hmarginR (show (0 : ℝ) ≤ q by positivity)
    have hle : (q : ℝ) * (L + 1) ≤ (q : ℝ) * q / (2 * k) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hprod]
    exact_mod_cast hle.trans_lt h
  apply exists_prescribed_matching_packing G R hRG A m a r k q K b
    (by simpa only [Fintype.card_fin] using hnpos)
    (by simpa only [Fintype.card_fin] using hmlen) heven hsmallNat habsNat
    (by simpa only [Fintype.card_fin] using hri)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hbad)
    (by simpa only [Fintype.card_fin] using hb)
    (by simpa only [Fintype.card_fin] using hmargin)
    (by simpa only [Fintype.card_fin] using hGnat) hRlo hRhi
    (by simpa only [Fintype.card_fin] using hcut)

#print axioms eventually_prescribed_matching_packing

theorem eventually_prescribed_matching_packing_with_slack (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * n → ∀ A : ℕ → Set (Fin n),
      (∀ i < m, Even (A i).ncard) →
      (∀ i < m, ((A i)ᶜ.ncard : ℝ) ≤ delta * n) →
      (∀ v, ((∑ i ∈ range m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤ delta * n) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = A i) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 8 (4 / zeta))
  have hk8 : 8 ≤ k := by
    have h : (8 : ℝ) < k := (le_max_left _ _).trans_lt hk
    have h' : 8 < k := by exact_mod_cast h
    omega
  have hkz : (4 : ℝ) ≤ k * zeta := by
    apply (div_le_iff₀ hzeta).mp
    exact ((le_max_right _ _).trans_lt hk).le
  obtain ⟨delta, hd, N, hN⟩ := eventually_prescribed_matching_packing k hk8
  refine ⟨delta, hd, N, ?_⟩
  intro n hn G hG m hm A heven hsmall habs
  have hm' : k * m + 4 * n ≤ k * n := by
    have h₁ := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ k by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hkz (show (0 : ℝ) ≤ n by positivity)
    have h : (k : ℝ) * m + 4 * n ≤ (k : ℝ) * n := by nlinarith only [h₁, h₂]
    exact_mod_cast h
  exact hN n hn G hG m hm' A heven hsmall habs

#print axioms eventually_prescribed_matching_packing_with_slack

theorem eventually_prescribed_matching_packing_fin (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * n → ∀ A : Fin m → Set (Fin n),
      (∀ i, Even (A i).ncard) →
      (∀ i, ((A i)ᶜ.ncard : ℝ) ≤ delta * n) →
      (∀ v, ((∑ i : Fin m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤ delta * n) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = A i) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  obtain ⟨delta, hd, N, hN⟩ := eventually_prescribed_matching_packing_with_slack zeta hzeta
  refine ⟨delta, hd, N, ?_⟩
  intro n hn G hG m hm A heven hsmall habs
  let A' : ℕ → Set (Fin n) := fun i ↦ if hi : i < m then A ⟨i, hi⟩ else ∅
  have hA : ∀ i : Fin m, A' i = A i := fun i ↦ dif_pos i.isLt
  have hsum : ∀ v, (∑ i ∈ range m, (if v ∈ A' i then 0 else 1)) =
      ∑ i : Fin m, (if v ∈ A i then 0 else 1) := by
    intro v
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl (fun i _ ↦ by rw [hA])
  obtain ⟨M, hM, hp⟩ := hN n hn G hG m hm A'
    (fun i hi ↦ by simpa only [A', dif_pos hi] using heven ⟨i, hi⟩)
    (fun i hi ↦ by simpa only [A', dif_pos hi] using hsmall ⟨i, hi⟩)
    (fun v ↦ by rw [hsum]; exact habs v)
  exact ⟨M, fun i ↦ ⟨(hM i).1, (hM i).2.trans (hA i)⟩, hp⟩

#print axioms eventually_prescribed_matching_packing_fin

end Erdos19
