import Arxiv.Arxiv2411_18291.TypicalModularGenerators
import Arxiv.Arxiv2411_18291.CliqueMeanComparisons

/-!
# A finite criterion for small saturation and deletion losses

One numerical inequality controls both the fraction of saturated cliques
and the fraction of deleted edges. The construction retains accurate
unsaturated-clique counts and bounded modular generators.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem saturation_relative_losses {cap ε μ X H D S B k : ℝ}
    (hcap : 0 < cap) (hε : 0 < ε) (hε1 : ε ≤ 1) (hμ : 0 < μ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (hD : 0 ≤ D) (hk : 0 ≤ k)
    (hs : cap * S ≤ X * (H * μ)) (hb : (ε * μ / 2) * B ≤ k * S)
    (hmean : H * μ ≤ 2 * k * D) (hsmall : 2 * k * X ≤ cap * ε ^ 2) :
    S ≤ ε * D ∧ B ≤ ε * H := by
  constructor
  · apply (mul_le_mul_iff_right₀ hcap).mp
    have hεsq : ε ^ 2 ≤ ε := by nlinarith
    calc
      cap * S ≤ X * (H * μ) := hs
      _ ≤ X * (2 * k * D) := mul_le_mul_of_nonneg_left hmean hX
      _ = (2 * k * X) * D := by ring
      _ ≤ (cap * ε ^ 2) * D := mul_le_mul_of_nonneg_right hsmall hD
      _ = (cap * D) * ε ^ 2 := by ring
      _ ≤ (cap * D) * ε := mul_le_mul_of_nonneg_left hεsq (mul_nonneg hcap.le hD)
      _ = cap * (ε * D) := by ring
  · have ht : 0 < cap * (ε * μ / 2) := by positivity
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      (cap * (ε * μ / 2)) * B = cap * ((ε * μ / 2) * B) := by ring
      _ ≤ cap * (k * S) := mul_le_mul_of_nonneg_left hb hcap.le
      _ = k * (cap * S) := by ring
      _ ≤ k * (X * (H * μ)) := mul_le_mul_of_nonneg_left hs hk
      _ = (2 * k * X) * (H * μ / 2) := by ring
      _ ≤ (cap * ε ^ 2) * (H * μ / 2) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (cap * (ε * μ / 2)) * (ε * H) := by ring

variable {V : Type*} [Fintype V] [DecidableEq V] {q r h : ℕ}

theorem exists_good_modular_generating_data (N : ℕ) (hN : 0 < N)
    {K : Hypergraph V (r + 1)} {c η θ ε : ℝ}
    (hT : IsTypical K c h) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    (hn : 0 < Fintype.card V) (hp : 0 < density K)
    (hcη : c ≤ η) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density K ^ q.choose (r + 1)))
    (cap : ℕ) (hcap : 0 < cap) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herror : η * q * 2 ^ q ≤ ε / 2)
    (hθ : ((q - r : ℕ) : ℝ) * cap < θ * Fintype.card V)
    (hsmall : 4 * (q.choose (r + 1) : ℝ) * q.choose r * N * Fintype.card V * density K ≤
      cap * ε ^ 2) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators θ ∧ C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤ ε * (cliqueFamily K q).card ∧
      ((K \ C.good).card : ℝ) ≤ ε * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)| <
          ε * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1) := by
  let ζ : ℝ := η * q * 2 ^ q
  let μ := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)
  let L := 2 * Fintype.card V * density K * μ
  let X : ℝ := 2 * q.choose r * N * Fintype.card V * density K
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hμ : 0 < μ := cliqueMainTerm_pos hnR hp _ _ _
  have hζ : ζ ≤ 1 / 2 := by dsimp [ζ]; linarith
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hτ : 0 < ε * μ / 2 := by positivity
  have hcapR : (0 : ℝ) < cap := by exact_mod_cast hcap
  have hD : ∀ Q ∈ cliqueFamily K q, cliqueEdges (r + 1) Q ⊆ K :=
    fun _ hQ => (mem_filter.mp hQ).2
  have hface (S : Block V r) :
      (((cliqueFamily K q).filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L := by
    let m := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) r
    have hm : 0 ≤ m := cliqueMainTerm_nonneg hnR.le hp.le _ _ _
    have hc := (abs_le.mp (hT.cliqueFamily_small_root_relative hqh hcη hη hη1 hsize S
      (by omega) (Nat.lt_succ_self r))).2
    change _ ≤ ζ * m at hc
    have hbase : m ≤ Fintype.card V * density K * μ := cliqueMainTerm_face_le hnR.le hp.le hqr
    calc
      _ ≤ (1 + ζ) * m := by linarith
      _ ≤ 2 * m := mul_le_mul_of_nonneg_right (by linarith) hm
      _ ≤ 2 * (Fintype.card V * density K * μ) := mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = L := by dsimp [L]; ring
  have hedge (e : Block V (r + 1)) (he : e ∈ K) :
      |(((cliqueFamily K q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ζ * μ :=
    hT.cliqueFamily_edge_relative hqh hcη hη hη1 hsize hqr he
  obtain ⟨C, hload, hcard, hsat, hbad, hcount⟩ :=
    exists_modular_generating_data N hN K (cliqueFamily K q) hD cap hcap hL hτ hface hedge
  have hs : (cap : ℝ) * C.saturated.card ≤ X * (K.card * μ) := by
    have hs' := (le_div_iff₀ hcapR).mp hsat
    push_cast at hs'
    calc
      _ = (C.saturated.card : ℝ) * cap := mul_comm _ _
      _ ≤ _ := hs'
      _ = _ := by dsimp [X, L]; ring
  have hb : (ε * μ / 2) * (K \ C.good).card ≤ (q.choose (r + 1) : ℝ) * C.saturated.card := by
    simpa only [mul_comm] using (le_div_iff₀ hτ).mp hbad
  have hmean := host_clique_mean_le K (cliqueFamily K q) hD hμ.le hζ hedge
  have hsmall' : 2 * (q.choose (r + 1) : ℝ) * X ≤ (cap : ℝ) * ε ^ 2 := by
    convert hsmall using 1
    dsimp [X]
    ring
  obtain ⟨hS, hB⟩ := saturation_relative_losses hcapR hε hε1 hμ hX (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs hb hmean hsmall'
  refine ⟨C, cliqueFamilyBounded_of_face_load C.generators cap hload hθ, hcard, hS, hB, ?_⟩
  intro e he
  have he' := hcount e he
  have herr : ζ * μ ≤ (ε / 2) * μ := mul_le_mul_of_nonneg_right herror hμ.le
  exact he'.trans_le (by linarith)

end Arxiv2411_18291
