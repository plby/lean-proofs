/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.GeneratorAsymptotic
import ErdosProblems.Erdos722.LocalDecoderAsymptotic
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Quantitative random rotations for the sparse generator

The surviving pruned host is not itself typical at every lower face.  What
the rotation argument needs is weaker: an upper codimension-one degree and
a global lower edge count.  The lemmas below turn exactly those two bounds
into a uniform constant correlation estimate for every proper intersection
class of two `r`-edges.
-/

namespace Erdos722.RotationAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.IntegralGenerators
open Erdos722.Rotations
open Erdos722.GeneratorAsymptotic

noncomputable section

/-- A deliberately coarse constant that dominates all fixed binomial
losses in the edge-pair correlation estimate. -/
def rotationPairConstant (r : ℕ) : ℕ :=
  64 * r * 2 ^ (2 * r) * (Nat.factorial r) ^ 2

lemma rotationPairConstant_pos {r : ℕ} (hr : 0 < r) :
    0 < rotationPairConstant r := by
  exact mul_pos (mul_pos (mul_pos (by positivity) hr) (by positivity))
    (by positivity)

/-- The two fixed binomial lower bounds dominate the matching product of
powers.  This is the only place where the harmless constant in
`rotationPairConstant` is spent. -/
lemma pair_binomial_scale
    {n r j : ℕ} (hr : 0 < r) (hj : j < r) (hn : 4 * r ≤ n) :
    64 * r * n ^ (r - 1 - j) * n ^ r ≤
      rotationPairConstant r * Nat.choose n (r - 1) *
        Nat.choose (n - r) (r - j) := by
  have hn₁ : 2 * (0 + (r - 1)) ≤ n := by omega
  have hn₂ : 2 * (r + (r - j)) ≤ n := by omega
  have h₁ := Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
    n 0 (r - 1) hn₁
  have h₂ := Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
    n r (r - j) hn₂
  have h₁' : n ^ (r - 1) ≤
      2 ^ (r - 1) * Nat.factorial (r - 1) *
        Nat.choose n (r - 1) := by simpa using h₁
  have hpows : n ^ (r - 1 - j) * n ^ r =
      n ^ (r - 1) * n ^ (r - j) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [show 64 * r * n ^ (r - 1 - j) * n ^ r =
    64 * r * (n ^ (r - 1 - j) * n ^ r) by ring, hpows]
  calc
    64 * r * (n ^ (r - 1) * n ^ (r - j)) ≤
        64 * r *
          ((2 ^ (r - 1) * Nat.factorial (r - 1) *
              Nat.choose n (r - 1)) *
            (2 ^ (r - j) * Nat.factorial (r - j) *
              Nat.choose (n - r) (r - j))) := by
      gcongr
    _ ≤ rotationPairConstant r * Nat.choose n (r - 1) *
          Nat.choose (n - r) (r - j) := by
      have hpow : 2 ^ (r - 1) * 2 ^ (r - j) ≤ 2 ^ (2 * r) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hfac₁ : Nat.factorial (r - 1) ≤ Nat.factorial r :=
        Nat.factorial_le (by omega)
      have hfac₂ : Nat.factorial (r - j) ≤ Nat.factorial r :=
        Nat.factorial_le (by omega)
      have hcoeff :
          (2 ^ (r - 1) * 2 ^ (r - j)) *
              (Nat.factorial (r - 1) * Nat.factorial (r - j)) ≤
            2 ^ (2 * r) * (Nat.factorial r) ^ 2 := by
        exact Nat.mul_le_mul hpow (by
          simpa [pow_two] using Nat.mul_le_mul hfac₁ hfac₂)
      calc
        64 * r *
            ((2 ^ (r - 1) * Nat.factorial (r - 1) *
                Nat.choose n (r - 1)) *
              (2 ^ (r - j) * Nat.factorial (r - j) *
                Nat.choose (n - r) (r - j))) =
            64 * r * (2 ^ (r - 1) * 2 ^ (r - j)) *
              (Nat.factorial (r - 1) * Nat.factorial (r - j)) *
              (Nat.choose n (r - 1) *
                Nat.choose (n - r) (r - j)) := by ring
        _ = 64 * r *
              ((2 ^ (r - 1) * 2 ^ (r - j)) *
                (Nat.factorial (r - 1) * Nat.factorial (r - j))) *
              (Nat.choose n (r - 1) *
                Nat.choose (n - r) (r - j)) := by ring
        _ ≤ 64 * r *
              (2 ^ (2 * r) * (Nat.factorial r) ^ 2) *
              (Nat.choose n (r - 1) *
                Nat.choose (n - r) (r - j)) := by
          gcongr
        _ = 64 * r * 2 ^ (2 * r) *
              ((Nat.factorial r) ^ 2) *
              (Nat.choose n (r - 1) *
                Nat.choose (n - r) (r - j)) := by ring
        _ = rotationPairConstant r * Nat.choose n (r - 1) *
              Nat.choose (n - r) (r - j) := by
          simp [rotationPairConstant]
          ring

/-- Global mass and a codimension-one degree cap give a constant pair
correlation bound for every proper intersection class. -/
theorem orderedIntersectionPairs_ratio
    {n r L D : ℕ} (hr : 0 < r) (hn : 4 * r ≤ n)
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hdegree : ∀ I : Finset (Fin n), I.card = r - 1 →
      (K.filter fun e ↦ I ⊆ e).card ≤ D)
    (hDL : D ≤ 32 * L)
    (hmass : Nat.choose n (r - 1) * L ≤
      2 * K.card * Nat.choose r (r - 1))
    {j : ℕ} (hj : j < r) :
    (orderedIntersectionPairs K j).card * Nat.choose n r ^ 2 ≤
      rotationPairConstant r * K.card ^ 2 *
        (orderedIntersectionPairs (uniformEdges n r) j).card := by
  have hpair := card_orderedIntersectionPairs_le_of_codimOneDegree
    hr hK hdegree hj
  have hscale := pair_binomial_scale hr hj hn
  have hchoose : Nat.choose r (r - 1) = r := by
    rw [← Nat.choose_symm (by omega : r - 1 ≤ r)]
    simp [show r - (r - 1) = 1 by omega]
  have hbin :
      64 * r * Nat.choose (n - j) (r - 1 - j) * Nat.choose n r ≤
        rotationPairConstant r * Nat.choose n (r - 1) *
          Nat.choose (n - r) (r - j) := by
    calc
      64 * r * Nat.choose (n - j) (r - 1 - j) * Nat.choose n r ≤
          64 * r * n ^ (r - 1 - j) * n ^ r := by
        gcongr
        · exact (Nat.choose_le_pow (n - j) (r - 1 - j)).trans
            (Nat.pow_le_pow_left (Nat.sub_le n j) _)
        · exact Nat.choose_le_pow _ _
      _ ≤ _ := hscale
  calc
    (orderedIntersectionPairs K j).card * Nat.choose n r ^ 2 ≤
        (K.card *
          (Nat.choose r j *
            (Nat.choose (n - j) (r - 1 - j) * D))) *
              Nat.choose n r ^ 2 := Nat.mul_le_mul_right _ hpair
    _ ≤ (K.card *
          (Nat.choose r j *
            (Nat.choose (n - j) (r - 1 - j) * (32 * L)))) *
              Nat.choose n r ^ 2 := by gcongr
    _ ≤ rotationPairConstant r * K.card ^ 2 *
          (Nat.choose n r *
            (Nat.choose r j * Nat.choose (n - r) (r - j))) := by
      rw [hchoose] at hmass
      have hchoosePos : 0 < Nat.choose n (r - 1) :=
        Nat.choose_pos (by omega)
      refine Nat.le_of_mul_le_mul_right ?_ hchoosePos
      calc
        ((K.card *
              (Nat.choose r j *
                (Nat.choose (n - j) (r - 1 - j) * (32 * L)))) *
            Nat.choose n r ^ 2) * Nat.choose n (r - 1) =
            (32 * K.card * Nat.choose r j *
              Nat.choose (n - j) (r - 1 - j) * Nat.choose n r ^ 2) *
                (Nat.choose n (r - 1) * L) := by ring
        _ ≤ (32 * K.card * Nat.choose r j *
              Nat.choose (n - j) (r - 1 - j) * Nat.choose n r ^ 2) *
                (2 * K.card * r) := by gcongr
        _ = (K.card ^ 2 * Nat.choose r j * Nat.choose n r) *
              (64 * r * Nat.choose (n - j) (r - 1 - j) *
                Nat.choose n r) := by ring
        _ ≤ (K.card ^ 2 * Nat.choose r j * Nat.choose n r) *
              (rotationPairConstant r * Nat.choose n (r - 1) *
                Nat.choose (n - r) (r - j)) := by gcongr
        _ = (rotationPairConstant r * K.card ^ 2 *
              (Nat.choose n r *
                (Nat.choose r j * Nat.choose (n - r) (r - j)))) *
              Nat.choose n (r - 1) := by ring
    _ = rotationPairConstant r * K.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n r) j).card := by
      rw [card_orderedIntersectionPairs_uniform (n := n) hj.le]

/-- The quartered floor used for the lower sampled degree still retains a
fixed sixteenth of its real power scale. -/
theorem eventually_rpow_div_sixteen_le_generatorDegreeLower
    {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 ≤
        (generatorDegreeLower d n : ℝ) := by
  have hhalf := eventually_half_rpow_le_rationalPowerThreshold
    (show 0 < d - 1 by omega) (show 0 < d by omega)
  have htop := rationalPowerThreshold_tendsto_atTop
    (show 0 < d - 1 by omega) (show 0 < d by omega)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      8 ≤ rationalPowerThreshold (d - 1) d n :=
    htop.eventually (eventually_ge_atTop 8)
  filter_upwards [hhalf, hlarge] with n hhalf hlarge
  let T := rationalPowerThreshold (d - 1) d n
  have hdiv := half_div_le_natDiv T 4 (by omega) hlarge
  calc
    (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 =
        ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 2) / 8 := by ring
    _ ≤ (T : ℝ) / 8 := by gcongr
    _ ≤ (T / 4 : ℕ) := by
      convert hdiv using 1 <;> norm_num
    _ = (generatorDegreeLower d n : ℝ) := by
      rfl

/-- Upper singleton-root typicality, restricted to a pruned subhost, is at
most thirty-two times the declared lower sampled degree. -/
theorem pruned_degree_le_thirtyTwo_lower
    {N n q r d : ℕ} (hn : 0 < n) (hr : 0 < r) (hrq : r ≤ q)
    (hd : 1 < d)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (D : TwoCapPrunedData N n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      (generatorPruneThreshold q r d n)
      (generatorFaceCliqueCap q r d n)
      (generatorEdgeCliqueCap q r d n))
    (hDK : D.K = sampledEdges n r ω)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots hr
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn))
    (hlower :
      (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 ≤
        (generatorDegreeLower d n : ℝ)) :
    ∀ I : Finset (Fin n), I.card = r - 1 →
      (D.Kstar.filter fun e ↦ I ⊆ e).card ≤
        32 * generatorDegreeLower d n := by
  intro I hI
  have hsample :
      (rootEdges (sampledEdges n r ω) I).card ≤
        32 * generatorDegreeLower d n := by
    have hupp := typical_localDegree_upper (q := q) hr hrq
      (reserveProbabilityIcc n d hn) ω htyp I hI
    have hp := natCast_mul_reserveProbability_pow_eq_rpow
      hn (show 0 < d by omega) (show 1 ≤ d by omega)
    have hreal :
        ((rootEdges (sampledEdges n r ω) I).card : ℝ) <
          (32 * generatorDegreeLower d n : ℕ) := by
      calc
        ((rootEdges (sampledEdges n r ω) I).card : ℝ) <
            2 * n * (reserveProbabilityIcc n d hn : ℝ) := by
          simpa [rootEdges, Erdos722.Reserve.localDegree] using hupp
        _ = 2 * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) := by
          rw [← hp]
          ring
        _ ≤ (32 * generatorDegreeLower d n : ℕ) := by
          push_cast
          linarith
    exact_mod_cast hreal.le
  have hsub : D.Kstar.filter (fun e ↦ I ⊆ e) ⊆
      (sampledEdges n r ω).filter (fun e ↦ I ⊆ e) := by
    intro e he
    have hedata := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [← hDK] using D.Kstar_subset hedata.1, hedata.2⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa [rootEdges] using hsample)

/-- The output of `eventually_exists_prunedGeneratorSample` satisfies the
uniform proper-intersection correlation estimate needed by every rotation
application. -/
theorem eventually_prunedGenerator_pair_ratio
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ j < r,
        (orderedIntersectionPairs D.Kstar j).card * Nat.choose n r ^ 2 ≤
          rotationPairConstant r * D.Kstar.card ^ 2 *
            (orderedIntersectionPairs (uniformEdges n r) j).card := by
  have hd : 1 < d := by
    have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
    omega
  have hlower := eventually_rpow_div_sixteen_le_generatorDegreeLower hd
  filter_upwards [hlower, eventually_ge_atTop (4 * r)] with n hlower hnlarge
  intro hn ω D htyp hDK hmass j hj
  apply orderedIntersectionPairs_ratio (K := D.Kstar)
    (by omega : 0 < r) hnlarge
    (fun e he ↦ D.uniform e (D.Kstar_subset he))
  · exact pruned_degree_le_thirtyTwo_lower hn (by omega) hrq.le hd
      ω D hDK htyp hlower
  · exact le_rfl
  · simpa [uniformEdges] using hmass
  · exact hj

/-- Tensor the proper-intersection edge correlation estimate over all
independent colour coordinates of one rooted pattern. -/
theorem rootedRotationSuccess_inter_ratio
    {v n m r c : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hpair : ∀ j < r,
      (orderedIntersectionPairs K j).card * Nat.choose n r ^ 2 ≤
        c * K.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n r) j).card)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r)
    {φ ψ : Fin v ↪ Fin n}
    (hφ : Erdos722.RootedEmbedding.ExtendsRequest root request φ)
    (hψ : Erdos722.RootedEmbedding.ExtendsRequest root request ψ)
    (hdisj : RootedOutsideDisjoint root φ ψ) :
    Fintype.card (Fin m → Equiv.Perm (Fin n)) *
        (rootedRotationSuccess K edges φ ∩
          rootedRotationSuccess K edges ψ).card ≤
      c ^ m * (rootedRotationSuccess K edges φ).card *
        (rootedRotationSuccess K edges ψ).card := by
  apply card_rainbowHitSamples_inter_ratio_of_coordinate
  intro i
  apply card_pairHitPermutations_ratio_of_orderedPair_ratio hK
  · exact (Erdos722.RootedEmbedding.card_mapEdge φ (edges i)).trans
      (hedges i)
  · exact (Erdos722.RootedEmbedding.card_mapEdge ψ (edges i)).trans
      (hedges i)
  · have hinter := card_mapEdge_inter_mapEdge_of_rootedOutsideDisjoint
      (S := edges i) hφ hψ hdisj
    have hratio := hpair ((edges i ∩ root).card) (hproper i)
    simpa [rootedRotationSuccess, mappedTargets, hinter] using hratio

/-- A constant tensorized pair ratio plus domination of the exceptional
rooted partners gives the scaled Paley--Zygmund failure estimate. -/
theorem rootedRotationFailures_paley_of_correlation
    {v n m r c : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess K edges φ₀ ∩
            rootedRotationSuccess K edges φ₁).card ≤
        c ^ m * (rootedRotationSuccess K edges φ₀).card *
          (rootedRotationSuccess K edges φ₁).card)
    (hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess K edges φ₀).card) :
    let R := c ^ m + 1
    R * ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ = 0).card ≤
      (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let A := (rootedRotationSuccess K edges φ₀).card
  let G := (rootedRotationSuccess K edges φ₀ ∩
    rootedRotationSuccess K edges φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
  have hAeq : (rootedRotationSuccess K edges φ₁).card = A :=
    card_rootedRotationSuccess_eq hK hedges φ₁ φ₀
  have hcorr' : S * G ≤ c ^ m * A ^ 2 := by
    simpa [S, G, A, hAeq, pow_two, Nat.mul_assoc] using hcorr
  have hexception' : S * L ≤ candidates.card * A := by
    simpa [S, L, candidates, A] using hexception
  have hratio :
      S * (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        (c ^ m + 1) * (candidates.card * A) ^ 2 := by
    calc
      S * (candidates.card ^ 2 * G + candidates.card * L * A) =
          candidates.card ^ 2 * (S * G) +
            candidates.card * A * (S * L) := by ring
      _ ≤ candidates.card ^ 2 * (c ^ m * A ^ 2) +
            candidates.card * A * (candidates.card * A) := by gcongr
      _ = (c ^ m + 1) * (candidates.card * A) ^ 2 := by ring
  apply card_rootedRotationFailures_paley_scaled hK hedges
    hφ₀ hφ₁ hdisj hApos (by positivity)
  simpa [candidates, A, G, L, S] using hratio

/-- A denominator-cleared lower bound on the expected number of rooted
successes is exactly the exceptional-partner inequality used above. -/
theorem rootedRotation_exceptional_of_expected_lower
    {v n m r : ℕ} {root : Finset (Fin v)}
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    (φ : Fin v ↪ Fin n)
    (hexpected :
      ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n r ^ m ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          K.card ^ m) :
    Fintype.card (Fin m → Equiv.Perm (Fin n)) *
        ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
        (rootedRotationSuccess K edges φ).card := by
  let C := (Erdos722.RootedEmbedding.rootedEmbeddings root request).card
  let A := (rootedRotationSuccess K edges φ).card
  let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  let U := Nat.choose n r
  have htargets : ∀ i,
      (Erdos722.RootedEmbedding.mapEdge φ (edges i)).card = r := by
    intro i
    exact (Erdos722.RootedEmbedding.card_mapEdge φ (edges i)).trans
      (hedges i)
  have hsuccess : A * U ^ m = K.card ^ m * S := by
    simpa [A, U, S, rootedRotationSuccess, mappedTargets,
      Fintype.card_fun] using
      (card_rainbowHitSamples_mul_choose_pow hK htargets)
  have hUpow : 0 < U ^ m := by
    by_cases hm : m = 0
    · simp [hm]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let i : Fin m := ⟨0, hmpos⟩
      have hrn : r ≤ n := by
        calc
          r = (edges i).card := (hedges i).symm
          _ = (Erdos722.RootedEmbedding.mapEdge φ (edges i)).card :=
            (Erdos722.RootedEmbedding.card_mapEdge φ _).symm
          _ ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      exact pow_pos (Nat.choose_pos hrn) m
  refine Nat.le_of_mul_le_mul_right ?_ hUpow
  calc
    (S * L) * U ^ m = S * (L * U ^ m) := by ring
    _ ≤ S * (C * K.card ^ m) := by
      simpa [C, L, U] using Nat.mul_le_mul_left S hexpected
    _ = C * (K.card ^ m * S) := by ring
    _ = (C * A) * U ^ m := by rw [← hsuccess]; ring

/-- The expected rooted success count beats the one-power exceptional
partner loss whenever the number of independently constrained edges is
strictly smaller than the sampling denominator. -/
theorem eventually_rooted_expected_lower
    {v m r d : ℕ} (root : Finset (Fin v))
    (hroot : root.card < v) (hr : 0 < r) (hd : 1 < d) (hmd : m < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (K : Finset (Finset (Fin n))),
      (Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * K.card * Nat.choose r (r - 1)) →
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
            Nat.choose n r ^ m ≤
          (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
            K.card ^ m := by
  let s := v - root.card
  let a : ℝ := ((d - 1 : ℕ) : ℝ) / d
  let b : ℝ := (r - 1 : ℕ) + a
  let leftExp : ℝ := (s - 1 : ℕ) + r * m
  let rightExp : ℝ := s + b * m
  let Cchoose : ℕ := 2 ^ (r - 1) * Nat.factorial (r - 1)
  let Cedge : ℕ := 32 * r * Cchoose
  let Ctotal : ℝ :=
    (s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cedge : ℝ) ^ m
  have hs : 0 < s := by dsimp [s]; omega
  have hCchoose : 0 < Cchoose := by positivity
  have hCedge : 0 < Cedge := by
    dsimp [Cedge]
    positivity
  have hgap : leftExp < rightExp := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hmdR : (m : ℝ) < d := by exact_mod_cast hmd
    have hsone : 1 ≤ s := by omega
    dsimp [leftExp, rightExp, b, a]
    rw [Nat.cast_sub hsone]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
    field_simp
    nlinarith
  have hdom := eventually_const_mul_rpow_le_rpow hgap (by positivity :
    0 ≤ Ctotal)
  have hdegreeLower :=
    eventually_rpow_div_sixteen_le_generatorDegreeLower hd
  filter_upwards [hdom, hdegreeLower,
      eventually_ge_atTop (max (2 * v) (4 * r))] with
      n hdom hdegreeLower hnlarge
  intro K hmass request
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnFourR : 4 * r ≤ n := (le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hbaseline :=
    Erdos722.LocalDecoderAsymptotic.descFactorial_sub_cast_lower
      (n := n) (r := root.card) (s := s) (by
        have hrs : root.card + s = v := by dsimp [s]; omega
        simpa [hrs] using hnTwoV)
  have hcandidate : (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card :=
    hbaseline.trans (by
      exact_mod_cast
        (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
          root request))
  have hchooseNat :=
    Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
      n 0 (r - 1) (by omega : 2 * (0 + (r - 1)) ≤ n)
  have hchoose : (n : ℝ) ^ (r - 1) / Cchoose ≤
      Nat.choose n (r - 1) := by
    have hreal : (n : ℝ) ^ (r - 1) ≤
        (Cchoose : ℝ) * Nat.choose n (r - 1) := by
      exact_mod_cast (by simpa [Cchoose] using hchooseNat)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Cchoose)).2 (by
      simpa [mul_comm] using hreal)
  have hmassR :
      (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n ≤
        2 * (K.card : ℝ) * r := by
    have hchooseR : Nat.choose r (r - 1) = r := by
      rw [← Nat.choose_symm (by omega : r - 1 ≤ r)]
      simp [show r - (r - 1) = 1 by omega]
    rw [hchooseR] at hmass
    exact_mod_cast hmass
  have hedge : (n : ℝ) ^ b / Cedge ≤ K.card := by
    have hpow : (n : ℝ) ^ b =
        (n : ℝ) ^ (r - 1) * (n : ℝ) ^ a := by
      rw [show b = (r - 1 : ℕ) + a by rfl, Real.rpow_add hnR,
        Real.rpow_natCast]
    have hprod :
        ((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ a / 16) ≤
          (Nat.choose n (r - 1) : ℝ) *
            generatorDegreeLower d n := by gcongr
    calc
      (n : ℝ) ^ b / Cedge =
          (((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ a / 16)) / (2 * r) := by
        rw [hpow]
        dsimp [Cedge]
        push_cast
        field_simp
        <;> ring
      _ ≤ ((Nat.choose n (r - 1) : ℝ) *
            generatorDegreeLower d n) / (2 * r) := by gcongr
      _ ≤ K.card := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmassR
  have hleft :
      ((((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n r ^ m : ℕ) : ℝ) ≤
        (s ^ 2 : ℕ) * (n : ℝ) ^ leftExp := by
    push_cast
    have hvsub : v - (root.card + 1) = s - 1 := by dsimp [s]; omega
    rw [hvsub]
    change (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
        (Nat.choose n r : ℝ) ^ m ≤
      (s : ℝ) ^ 2 * (n : ℝ) ^ leftExp
    calc
      (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
          (Nat.choose n r : ℝ) ^ m ≤
        (s : ℝ) ^ 2 * (n : ℝ) ^ (s - 1) *
          ((n : ℝ) ^ r) ^ m := by
        gcongr
        exact_mod_cast Nat.choose_le_pow n r
      _ = (s : ℝ) ^ 2 * (n : ℝ) ^ leftExp := by
        have hexp : leftExp =
            ((((s - 1) + r * m : ℕ) : ℕ) : ℝ) := by
          push_cast
          simp [leftExp]
        rw [hexp, Real.rpow_natCast, pow_add, pow_mul]
        ring
  have hright :
      (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) ≤
        ((Erdos722.RootedEmbedding.rootedEmbeddings root request).card : ℝ) *
          (K.card : ℝ) ^ m := by
    calc
      (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) =
        ((n : ℝ) ^ s / (2 : ℝ) ^ s) *
          (((n : ℝ) ^ b / Cedge) ^ m) := by
        rw [show rightExp = (s : ℕ) + b * m by rfl,
          Real.rpow_add hnR, Real.rpow_natCast,
          Real.rpow_mul hnR.le]
        rw [Real.rpow_natCast]
        rw [div_pow]
        ring
      _ ≤ ((Erdos722.RootedEmbedding.rootedEmbeddings root request).card : ℝ) *
          (K.card : ℝ) ^ m := by gcongr
  have hmiddle :
      (s ^ 2 : ℕ) * (n : ℝ) ^ leftExp ≤
        (n : ℝ) ^ rightExp /
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) := by
    have hden : (0 : ℝ) < (2 : ℝ) ^ s * (Cedge : ℝ) ^ m := by
      positivity
    apply (le_div_iff₀ hden).2
    have hdom' :
        ((s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cedge : ℝ) ^ m) *
            (n : ℝ) ^ leftExp ≤ (n : ℝ) ^ rightExp := by
      simpa [Ctotal] using hdom
    calc
      ((s ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ leftExp *
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) =
        ((s ^ 2 : ℕ) * (2 ^ s : ℕ) * (Cedge : ℝ) ^ m) *
          (n : ℝ) ^ leftExp := by
        push_cast
        ring
      _ ≤ _ := hdom'
  exact_mod_cast hleft.trans (hmiddle.trans hright)

/-- Once the ground set is large, the one-power family of exceptional
partners of a rooted embedding is strictly smaller than the full family
of rooted embeddings.  This supplies the general-position pair used in
the second-moment argument. -/
theorem eventually_rootedExceptionalPartners_lt_rootedEmbeddings
    {v : ℕ} (root : Finset (Fin v)) (hroot : root.card < v) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (request : Erdos722.RootedEmbedding.RootRequest v n root)
        (φ : Fin v ↪ Fin n),
        (rootedExceptionalPartners root request φ).card <
          (Erdos722.RootedEmbedding.rootedEmbeddings root request).card := by
  let s := v - root.card
  let C : ℝ := 2 * (s ^ 2 : ℕ) * (2 : ℝ) ^ s
  have hs : 0 < s := by dsimp [s]; omega
  have hgap : ((s - 1 : ℕ) : ℝ) < s := by
    rw [Nat.cast_sub (by omega : 1 ≤ s)]
    norm_num
  have hdom := eventually_const_mul_rpow_le_rpow hgap
    (show 0 ≤ C by positivity)
  filter_upwards [hdom, eventually_ge_atTop (max (2 * v) 1)] with
      n hdom hnlarge
  intro request φ
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hbaseline :=
    Erdos722.LocalDecoderAsymptotic.descFactorial_sub_cast_lower
      (n := n) (r := root.card) (s := s) (by
        have hrs : root.card + s = v := by dsimp [s]; omega
        simpa [hrs] using hnTwoV)
  have hcandidates : (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card :=
    hbaseline.trans (by
      exact_mod_cast
        (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
          root request))
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  have hexception := card_rootedExceptionalPartners_le root request φ
  have hvsub : v - (root.card + 1) = s - 1 := by dsimp [s]; omega
  have htwoL : ((2 * L : ℕ) : ℝ) ≤
      (n : ℝ) ^ s / (2 : ℝ) ^ s := by
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    apply (le_div_iff₀ hpowpos).2
    have hdom' :
        (2 : ℝ) * (s ^ 2 : ℕ) * (2 : ℝ) ^ s *
            (n : ℝ) ^ (s - 1 : ℕ) ≤
          (n : ℝ) ^ s := by
      simpa [C, mul_assoc] using hdom
    push_cast
    dsimp [L]
    rw [hvsub]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdom'
  have htwoLNat : 2 * L ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card := by
    exact_mod_cast htwoL.trans hcandidates
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.mul_pos (by dsimp [s] at hs ⊢; positivity) (pow_pos hnpos _)
  calc
    (rootedExceptionalPartners root request φ).card ≤ L := hexception
    _ < 2 * L := by omega
    _ ≤ (Erdos722.RootedEmbedding.rootedEmbeddings root request).card :=
      htwoLNat

/-- A strict exceptional-family bound produces two root-respecting
embeddings whose outside images are disjoint. -/
theorem exists_rootedOutsideDisjoint_of_exceptional_lt
    {v n : ℕ} (root : Finset (Fin v))
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    (hcandidates : 0 <
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card)
    (hexception : ∀ φ : Fin v ↪ Fin n,
      (rootedExceptionalPartners root request φ).card <
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card) :
    ∃ φ₀ φ₁ : Fin v ↪ Fin n,
      Erdos722.RootedEmbedding.ExtendsRequest root request φ₀ ∧
      Erdos722.RootedEmbedding.ExtendsRequest root request φ₁ ∧
      RootedOutsideDisjoint root φ₀ φ₁ := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := Finset.card_pos.mp hcandidates
  obtain ⟨φ₁, hφ₁, hφ₁not⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (hexception φ₀)
  refine ⟨φ₀, φ₁,
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ₀,
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ₁, ?_⟩
  by_contra hdisj
  exact hφ₁not (by
    apply Finset.mem_filter.mpr
    exact ⟨hφ₁, hdisj⟩)

/-- If the sparse host is nonempty, every rooted rotation event has
positive cardinality.  This is extracted from the exact product identity,
so no division in `ℕ` is needed. -/
theorem rootedRotationSuccess_card_pos
    {v n m r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r) (hKpos : 0 < K.card)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r) (φ : Fin v ↪ Fin n) :
    0 < (rootedRotationSuccess K edges φ).card := by
  have htargets : ∀ i,
      (Erdos722.RootedEmbedding.mapEdge φ (edges i)).card = r := by
    intro i
    exact (Erdos722.RootedEmbedding.card_mapEdge φ (edges i)).trans
      (hedges i)
  have hsuccess :
      (rootedRotationSuccess K edges φ).card * Nat.choose n r ^ m =
        K.card ^ m * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
    simpa [rootedRotationSuccess, mappedTargets, Fintype.card_fun] using
      (card_rainbowHitSamples_mul_choose_pow hK htargets)
  have hright :
      0 < K.card ^ m * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
    exact Nat.mul_pos (pow_pos hKpos _) Fintype.card_pos
  rw [← hsuccess] at hright
  exact Nat.pos_of_mul_pos_right hright

/-- The pruned generator therefore has a uniform constant-factor failure
bound for every rooted request of every fixed proper-edge pattern with
fewer than `d` independently rotated edges. -/
theorem eventually_prunedGenerator_rootedRotation_failure
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        let R := rotationPairConstant r ^ m + 1
        R * ((rotationSamples n m).filter fun σ ↦
          Erdos722.Probability.finiteSuccessCount
            (Erdos722.RootedEmbedding.rootedEmbeddings root request)
            (rootedRotationSuccess D.Kstar edges) σ = 0).card ≤
          (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  have hd : 1 < d := by
    have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
    omega
  have hpair := eventually_prunedGenerator_pair_ratio N q r d hr hrq hqd
  have hexpected := eventually_rooted_expected_lower root hroot
    (by omega : 0 < r) hd hmd
  have hexceptional :=
    eventually_rootedExceptionalPartners_lt_rootedEmbeddings root hroot
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower hd
  filter_upwards [hpair, hexpected, hexceptional, hdegree,
      eventually_ge_atTop (max (2 * v) r)] with
      n hpair hexpected hexceptional hdegree hnlarge
  intro hn ω D htyp hDK hmass request
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnr : r ≤ n := (le_max_right _ _).trans hnlarge
  have hDuniform : ∀ e ∈ D.Kstar, e.card = r := by
    intro e he
    exact D.uniform e (D.Kstar_subset he)
  have hpairD : ∀ j < r,
      (orderedIntersectionPairs D.Kstar j).card * Nat.choose n r ^ 2 ≤
        rotationPairConstant r * D.Kstar.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n r) j).card :=
    hpair hn ω D htyp hDK hmass
  have hdegreePos : 0 < generatorDegreeLower d n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 := by
      positivity
    have : (0 : ℝ) < generatorDegreeLower d n :=
      hstrict.trans_le hdegree
    exact_mod_cast this
  have huniformPos : 0 < (uniformEdges n (r - 1)).card := by
    simpa [uniformEdges] using Nat.choose_pos (by omega : r - 1 ≤ n)
  have hKstarPos : 0 < D.Kstar.card := by
    have hleft : 0 <
        (uniformEdges n (r - 1)).card * generatorDegreeLower d n :=
      Nat.mul_pos huniformPos hdegreePos
    have hright : 0 < 2 * D.Kstar.card * Nat.choose r (r - 1) :=
      hleft.trans_le hmass
    have htwoK : 0 < 2 * D.Kstar.card :=
      Nat.pos_of_mul_pos_right hright
    exact Nat.pos_of_mul_pos_left htwoK
  have hcandidates : 0 <
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card := by
    have hdesc : 0 < (n - root.card).descFactorial
        (v - root.card) := Nat.descFactorial_pos.mpr (by omega)
    exact hdesc.trans_le
      (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
        root request)
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, hdisj⟩ :=
    exists_rootedOutsideDisjoint_of_exceptional_lt root request hcandidates
      (hexceptional request)
  have hApos : 0 < (rootedRotationSuccess D.Kstar edges φ₀).card :=
    rootedRotationSuccess_card_pos hDuniform hKstarPos hedges φ₀
  have hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess D.Kstar edges φ₀ ∩
            rootedRotationSuccess D.Kstar edges φ₁).card ≤
        rotationPairConstant r ^ m *
          (rootedRotationSuccess D.Kstar edges φ₀).card *
          (rootedRotationSuccess D.Kstar edges φ₁).card :=
    rootedRotationSuccess_inter_ratio hDuniform hpairD hedges hproper
      hφ₀ hφ₁ hdisj
  have hexpectedD :
      ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n r ^ m ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          D.Kstar.card ^ m := by
    apply hexpected D.Kstar
    simpa [uniformEdges] using hmass
  have hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess D.Kstar edges φ₀).card :=
    rootedRotation_exceptional_of_expected_lower request hDuniform hedges
      φ₀ hexpectedD
  simpa using rootedRotationFailures_paley_of_correlation hDuniform hedges
    hφ₀ hφ₁ hdisj hApos hcorr hexception

/-- Root requests are a subtype of all maps from the fixed pattern
vertices to the ground set, hence form only a polynomial-size task family. -/
theorem natCard_rootRequest_le_pow
    {v n : ℕ} (root : Finset (Fin v)) :
    Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) ≤ n ^ v := by
  let code : Erdos722.RootedEmbedding.RootRequest v n root →
      (Fin v → Fin n) := Erdos722.RootedEmbedding.RootRequest.map
  have hcode : Function.Injective code := by
    intro a b hab
    cases a with
    | mk amap ainj =>
      cases b with
      | mk bmap binj =>
        simp only [code, Erdos722.RootedEmbedding.RootRequest.map] at hab
        cases hab
        rfl
  simpa [Nat.card_fun] using Nat.card_le_card_of_injective code hcode

lemma generatorEdgeCap_le (d n : ℕ) (hd : 0 < d) :
    generatorEdgeCap d n ≤ n := by
  calc
    generatorEdgeCap d n ≤ generatorEdgeCap d n ^ (1000 * d) :=
      Nat.le_pow (by positivity)
    _ ≤ n ^ 1 := by
      simpa [generatorEdgeCap] using
        (Erdos722.Asymptotics.rationalPowerThreshold_pow_le
          1 (1000 * d) n (by positivity))
    _ = n := by simp

/-- Any polynomially bounded task family is dominated by amplification
through the growing edge-cap number of independent rotation groups. -/
theorem eventually_polynomial_rotation_amplification_union_bound
    (V d R : ℕ) (hd : 0 < d) (hR : 1 < R) :
    ∀ᶠ n : ℕ in atTop,
      n ^ V * (R - 1) ^ generatorEdgeCap d n <
        R ^ generatorEdgeCap d n := by
  let a : ℝ := 1 / (1000 * d : ℕ)
  let b : ℝ := 1 / (2 * R : ℕ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hdecay := Erdos722.Reserve.tendsto_pow_mul_exp_neg_rpow_atTop
    V ha hb
  have hnat := hdecay.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ V * Real.exp (-b * (n : ℝ) ^ a) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hcap := eventually_half_rpow_le_rationalPowerThreshold
    (show 0 < (1 : ℕ) by omega) (show 0 < 1000 * d by positivity)
  filter_upwards [hsmall, hcap] with n hsmall hcap
  let g := generatorEdgeCap d n
  have hcap' : (n : ℝ) ^ a / 2 ≤ (g : ℝ) := by
    simpa [a, g, generatorEdgeCap] using hcap
  have hbase :
      (((R - 1 : ℕ) : ℝ) / R) ≤ Real.exp (-(1 / (R : ℝ))) := by
    have hone := Real.one_sub_le_exp_neg (1 / (R : ℝ))
    have hcast : ((R - 1 : ℕ) : ℝ) = R - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ R))
    rw [hcast]
    convert hone using 1 <;> field_simp <;> ring
  have hratioNonneg : (0 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) / R := by
    positivity
  have hexpBound :
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
        Real.exp (-b * (n : ℝ) ^ a) := by
    calc
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
          (Real.exp (-(1 / (R : ℝ)))) ^ g :=
        pow_le_pow_left₀ hratioNonneg hbase g
      _ = Real.exp (-((g : ℝ) / R)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (-b * (n : ℝ) ^ a) := by
        apply Real.exp_le_exp.mpr
        have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
        have hscaled : b * (n : ℝ) ^ a ≤ (g : ℝ) / R := by
          calc
            b * (n : ℝ) ^ a = ((n : ℝ) ^ a / 2) / R := by
              dsimp [b]
              push_cast
              field_simp
              <;> ring
            _ ≤ (g : ℝ) / R :=
              div_le_div_of_nonneg_right hcap' hRpos.le
        simpa only [neg_mul] using neg_le_neg hscaled
  have hratioSmall :
      (n : ℝ) ^ V * ((((R - 1 : ℕ) : ℝ) / R) ^ g) < 1 := by
    exact (mul_le_mul_of_nonneg_left hexpBound (by positivity)).trans_lt hsmall
  have hRpowPos : (0 : ℝ) < (R : ℝ) ^ g := by positivity
  have hquot :
      (n : ℝ) ^ V * ((R - 1 : ℕ) : ℝ) ^ g / (R : ℝ) ^ g < 1 := by
    simpa [div_pow, mul_div_assoc] using hratioSmall
  have hcross :
      (n : ℝ) ^ V * ((R - 1 : ℕ) : ℝ) ^ g < (R : ℝ) ^ g := by
    have := (div_lt_iff₀ hRpowPos).mp hquot
    simpa using this
  exact_mod_cast hcross

/-- A polynomial number of rooted requests is dominated by amplification
through the growing edge-cap number of independent colour groups. -/
theorem eventually_rotation_amplification_union_bound
    (v d R : ℕ) (hd : 0 < d) (hR : 1 < R) :
    ∀ᶠ n : ℕ in atTop,
      ∀ root : Finset (Fin v),
        Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) *
            (R - 1) ^ generatorEdgeCap d n <
          R ^ generatorEdgeCap d n := by
  let a : ℝ := 1 / (1000 * d : ℕ)
  let b : ℝ := 1 / (2 * R : ℕ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hdecay := Erdos722.Reserve.tendsto_pow_mul_exp_neg_rpow_atTop
    v ha hb
  have hnat := hdecay.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ v * Real.exp (-b * (n : ℝ) ^ a) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hcap := eventually_half_rpow_le_rationalPowerThreshold
    (show 0 < (1 : ℕ) by omega) (show 0 < 1000 * d by positivity)
  filter_upwards [hsmall, hcap] with n hsmall hcap
  intro root
  let g := generatorEdgeCap d n
  have hcap' : (n : ℝ) ^ a / 2 ≤ (g : ℝ) := by
    simpa [a, g, generatorEdgeCap] using hcap
  have hbase :
      (((R - 1 : ℕ) : ℝ) / R) ≤ Real.exp (-(1 / (R : ℝ))) := by
    have hone := Real.one_sub_le_exp_neg (1 / (R : ℝ))
    have hcast : ((R - 1 : ℕ) : ℝ) = R - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ R))
    rw [hcast]
    convert hone using 1 <;> field_simp <;> ring
  have hratioNonneg : (0 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) / R := by
    positivity
  have hexpBound :
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
        Real.exp (-b * (n : ℝ) ^ a) := by
    calc
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
          (Real.exp (-(1 / (R : ℝ)))) ^ g :=
        pow_le_pow_left₀ hratioNonneg hbase g
      _ = Real.exp (-((g : ℝ) / R)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (-b * (n : ℝ) ^ a) := by
        apply Real.exp_le_exp.mpr
        have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
        have hscaled : b * (n : ℝ) ^ a ≤ (g : ℝ) / R := by
          calc
            b * (n : ℝ) ^ a = ((n : ℝ) ^ a / 2) / R := by
              dsimp [b]
              push_cast
              field_simp
              <;> ring
            _ ≤ (g : ℝ) / R :=
              div_le_div_of_nonneg_right hcap' hRpos.le
        simpa only [neg_mul] using neg_le_neg hscaled
  have hcard :
      (Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) : ℝ) ≤
        (n : ℝ) ^ v := by
    exact_mod_cast natCard_rootRequest_le_pow root
  have hratioSmall :
      (Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) : ℝ) *
          ((((R - 1 : ℕ) : ℝ) / R) ^ g) < 1 := by
    calc
      (Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) : ℝ) *
          ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
        (n : ℝ) ^ v * Real.exp (-b * (n : ℝ) ^ a) := by gcongr
      _ < 1 := hsmall
  have hRpowPos : (0 : ℝ) < (R : ℝ) ^ g := by positivity
  have hquot :
      (Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) : ℝ) *
          ((R - 1 : ℕ) : ℝ) ^ g / (R : ℝ) ^ g < 1 := by
    simpa [div_pow, mul_div_assoc] using hratioSmall
  have hcross :
      (Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) : ℝ) *
          ((R - 1 : ℕ) : ℝ) ^ g < (R : ℝ) ^ g := by
    have := (div_lt_iff₀ hRpowPos).mp hquot
    simpa using this
  exact_mod_cast hcross

/-- Amplified form: a single deterministic family of rotation groups
covers every request for the fixed rooted pattern. -/
theorem eventually_exists_prunedGenerator_rootedRotationCover
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (generatorEdgeCap d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
          ∃ t : Fin (generatorEdgeCap d n), ∃ φ : Fin v ↪ Fin n,
            Erdos722.RootedEmbedding.ExtendsRequest root request φ ∧
            ∀ i, rotateEdge (choice t i).symm
              (Erdos722.RootedEmbedding.mapEdge φ (edges i)) ∈ D.Kstar := by
  let R := rotationPairConstant r ^ m + 1
  have hR : 1 < R := by
    dsimp [R]
    have hc : 0 < rotationPairConstant r :=
      rotationPairConstant_pos (by omega)
    have : 0 < rotationPairConstant r ^ m := pow_pos hc _
    omega
  have hfailure := eventually_prunedGenerator_rootedRotation_failure
    N q r d hr hrq hqd root hroot hmd edges hedges hproper
  have hunion := eventually_rotation_amplification_union_bound v d R
    (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn ω D htyp hDK hmass
  apply exists_amplified_rootedRotationCover_of_scaled_bad
    (r := r) (R := R) (g := generatorEdgeCap d n)
    D.Kstar edges (by omega)
  · intro request
    have hf := hfailure hn ω D htyp hDK hmass request
    have hRsub : R - 1 = rotationPairConstant r ^ m := by
      dsimp [R]
    rw [hRsub]
    simpa [R, Fintype.card_fun] using hf
  · exact hunion root

end

end Erdos722.RotationAsymptotic
