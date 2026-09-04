/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Structures
import ErdosProblems.Erdos547b.Lemma74
import ErdosProblems.Erdos547b.TreePadding
import ErdosProblems.Erdos547b.Claim712
import Mathlib.Tactic

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoSparseAssembly

open Finset SimpleGraph

/- The large denominator separates all three scales in Section 7:
`cross density << classification scale << EC3 defect << sqrt(EC3 defect)`. -/
def scaleDenom : ℕ := 1000000000000

def sqrtDenom : ℕ := 100000

def microDenom : ℕ := (40 * scaleDenom) ^ 2

def densityDenom : ℕ := microDenom ^ 2

def sparseCap : ℚ := 1 / densityDenom

def heavyScale (m : ℕ) : ℕ := m / scaleDenom + 1

def defectScale (m : ℕ) : ℕ := 3 * heavyScale m

def rootScale (m : ℕ) : ℕ := m / sqrtDenom + 1

def largeThreshold : ℕ := 2 * microDenom

def microScale (m : ℕ) : ℕ := m / microDenom + 1

/- `Q` is the common reservoir size in Claim 7.12.  Its loss from half the
host side is one twentieth of the heavy scale, matching the
`2 * alpha^(1/4) m` term in the paper with integral slack. -/
def reservoirLoss (m : ℕ) : ℕ := heavyScale m / 20 + 1

def propositionLoss (m : ℕ) : ℕ := heavyScale m / 30 + 1

def reservoirScale (m : ℕ) : ℕ := m / 2 - reservoirLoss m

def naturalSubtreeParameter (m : ℕ) : ℕ := (heavyScale m + 2) / 2

lemma microScale_le_heavyScale (m : ℕ) : microScale m ≤ heavyScale m := by
  have hdenom : scaleDenom ≤ microDenom := by
    norm_num [microDenom, scaleDenom]
  have hdiv : m / microDenom ≤ m / scaleDenom :=
    Nat.div_le_div_left hdenom (by norm_num [scaleDenom])
  simpa [microScale, heavyScale] using Nat.add_le_add_right hdiv 1

lemma thousand_microScale_le_heavyScale (m : ℕ)
    (hm : largeThreshold ≤ m) :
    1000 * microScale m ≤ heavyScale m := by
  have hmicro : microDenom * microScale m ≤ 2 * m := by
    have hbase : microDenom * (m / microDenom) ≤ m := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m microDenom
    have hDle : microDenom ≤ m :=
      (by simp [largeThreshold] at hm; omega)
    simp only [microScale, Nat.mul_add]
    omega
  have hmHeavy : m < scaleDenom * heavyScale m := by
    have hdiv := Nat.mod_add_div m scaleDenom
    have hmod := Nat.mod_lt m (by norm_num [scaleDenom] : 0 < scaleDenom)
    calc
      m = m % scaleDenom + scaleDenom * (m / scaleDenom) := hdiv.symm
      _ < scaleDenom + scaleDenom * (m / scaleDenom) :=
        Nat.add_lt_add_right hmod _
      _ = scaleDenom * heavyScale m := by
        simp [heavyScale, Nat.mul_add, Nat.add_comm]
  have hdenom : 2000 * scaleDenom ≤ microDenom := by
    norm_num [microDenom, scaleDenom]
  nlinarith

lemma scaleDenom_pos : 0 < scaleDenom := by norm_num [scaleDenom]

lemma densityDenom_pos : 0 < densityDenom := by
  norm_num [densityDenom, microDenom, scaleDenom]

lemma sparseCap_pos : (0 : ℚ) < sparseCap := by
  norm_num [sparseCap, densityDenom, microDenom, scaleDenom]

lemma sparseCap_lt_one : sparseCap < (1 : ℚ) := by
  norm_num [sparseCap, densityDenom, microDenom, scaleDenom]

lemma sourceHierarchy (m : ℕ) (hm : scaleDenom ≤ m) :
    Erdos547b.ZhaoLemma74.SourceHierarchy
      m (defectScale m) (rootScale m) := by
  have hKpos : 0 < scaleDenom := scaleDenom_pos
  have hDpos : 0 < sqrtDenom := by norm_num [sqrtDenom]
  have hDleK : sqrtDenom ≤ scaleDenom := by
    norm_num [sqrtDenom, scaleDenom]
  have hquotK : 1 ≤ m / scaleDenom :=
    (Nat.one_le_div_iff hKpos).2 hm
  have hmulK : (m / scaleDenom) * scaleDenom ≤ m :=
    Nat.div_mul_le_self m scaleDenom
  have hqD : defectScale m * (sqrtDenom * sqrtDenom) ≤ m := by
    simp only [defectScale, heavyScale]
    norm_num [sqrtDenom, scaleDenom] at hquotK hmulK ⊢
    nlinarith
  have hmRoot : m < sqrtDenom * rootScale m := by
    have hdiv := Nat.mod_add_div m sqrtDenom
    have hmod := Nat.mod_lt m hDpos
    calc
      m = m % sqrtDenom + sqrtDenom * (m / sqrtDenom) := hdiv.symm
      _ < sqrtDenom + sqrtDenom * (m / sqrtDenom) :=
        Nat.add_lt_add_right hmod _
      _ = sqrtDenom * rootScale m := by
        simp [rootScale, Nat.mul_add, Nat.add_comm]
  have hqmD :
      defectScale m * m * (sqrtDenom * sqrtDenom) ≤ m * m := by
    nlinarith [Nat.mul_le_mul_right m hqD]
  have hmm :
      m * m < (sqrtDenom * rootScale m) *
        (sqrtDenom * rootScale m) := by
    exact Nat.mul_self_lt_mul_self hmRoot
  have hcancel :
      (sqrtDenom * sqrtDenom) * (defectScale m * m) <
        (sqrtDenom * sqrtDenom) * (rootScale m * rootScale m) := by
    nlinarith
  have hdefect : defectScale m * m ≤ rootScale m * rootScale m := by
    have hlt : defectScale m * m < rootScale m * rootScale m :=
      Nat.lt_of_mul_lt_mul_left hcancel
    omega
  have hquotD : 1 ≤ m / sqrtDenom :=
    (Nat.one_le_div_iff hDpos).2 (hDleK.trans hm)
  have hmulD : (m / sqrtDenom) * sqrtDenom ≤ m :=
    Nat.div_mul_le_self m sqrtDenom
  have htheta : 1782 * rootScale m ≤ m := by
    simp only [rootScale]
    norm_num [sqrtDenom] at hquotD hmulD ⊢
    nlinarith
  exact
    { defect_square := hdefect
      theta_zero_bound := htheta
      q_pos := by simp [defectScale, heavyScale]
      n_large := by
        norm_num [scaleDenom] at hm
        omega }

/- The final rounded form of Lemma 7.4 uses `s+q`, rather than only `s`,
in the source-scale separation.  Our two denominators leave ample room for
that stronger inequality. -/
lemma sourceFullSeparation (m : ℕ) (hm : scaleDenom ≤ m) :
    1782 * (rootScale m + defectScale m) ≤ m := by
  have hmulD : (m / sqrtDenom) * sqrtDenom ≤ m :=
    Nat.div_mul_le_self m sqrtDenom
  have hmulK : (m / scaleDenom) * scaleDenom ≤ m :=
    Nat.div_mul_le_self m scaleDenom
  simp only [rootScale, defectScale, heavyScale]
  norm_num [sqrtDenom, scaleDenom] at hmulD hmulK hm ⊢
  nlinarith

lemma sourceRadiusPos (m : ℕ) :
    0 < rootScale m + defectScale m := by
  simp [rootScale, defectScale, heavyScale]

lemma heavyScale_large (m : ℕ) (hm : largeThreshold ≤ m) :
    1001 ≤ heavyScale m := by
  have hthreshold : 1000 * scaleDenom ≤ largeThreshold := by
    norm_num [largeThreshold, microDenom, scaleDenom]
  have hquot : 1000 ≤ m / scaleDenom := by
    apply (Nat.le_div_iff_mul_le scaleDenom_pos).2
    exact hthreshold.trans hm
  simp only [heavyScale]
  omega

lemma reservoirScale_pos (m : ℕ) (hm : largeThreshold ≤ m) :
    0 < reservoirScale m := by
  have hh := heavyScale_large m hm
  have hm' : 1000 * scaleDenom ≤ m := by
    exact (by norm_num [largeThreshold, microDenom, scaleDenom] :
      1000 * scaleDenom ≤ largeThreshold).trans hm
  simp only [reservoirScale, reservoirLoss, heavyScale]
  norm_num [scaleDenom] at hm' hh ⊢
  omega

/- Uniformly for the order returned by Fact 7.9, the selected natural
subtree is large enough to absorb the four reservoir losses in the final
partition estimate of Claim 7.12. -/
lemma claim712_selected_order_estimate (m selected : ℕ)
    (hm : largeThreshold ≤ m)
    (hlower : (naturalSubtreeParameter m + 1) / 2 ≤ selected) :
    2 * m + 1 ≤ selected + 4 * reservoirScale m := by
  have hh := heavyScale_large m hm
  have hloss : reservoirLoss m ≤ m / 2 := by
    simp only [reservoirLoss, heavyScale]
    have hm' : 1000 * scaleDenom ≤ m := by
      exact (by norm_num [largeThreshold, microDenom, scaleDenom] :
        1000 * scaleDenom ≤ largeThreshold).trans hm
    norm_num [scaleDenom] at hm' ⊢
    omega
  have hmargin :
      4 * reservoirLoss m + 3 ≤
        (naturalSubtreeParameter m + 1) / 2 := by
    simp only [reservoirLoss, naturalSubtreeParameter]
    omega
  simp only [reservoirScale]
  omega

lemma naturalSubtreeParameter_bounds (m : ℕ) (hm : largeThreshold ≤ m) :
    2 ≤ naturalSubtreeParameter m ∧
      naturalSubtreeParameter m ≤ m + 1 ∧
      naturalSubtreeParameter m ≤ heavyScale m + 1 := by
  have hh := heavyScale_large m hm
  have hdiv : m / scaleDenom ≤ m := Nat.div_le_self _ _
  have hmpos : 1 ≤ m := by
    have : 1 ≤ largeThreshold := by
      norm_num [largeThreshold, microDenom, scaleDenom]
    omega
  simp only [heavyScale] at hh
  simp only [naturalSubtreeParameter, heavyScale]
  omega

/- The two rounded margins which turn a heavy degree into the smaller
Claim 7.12 reservoir supply, and a half-total degree into the larger one. -/
lemma claim712_supply_margins (m : ℕ) (hm : largeThreshold ≤ m) :
    2 * (propositionLoss m + 1) + 1 ≤
        (naturalSubtreeParameter m + 1) / 2 ∧
      naturalSubtreeParameter m + propositionLoss m ≤ heavyScale m + 1 := by
  have hh := heavyScale_large m hm
  simp only [propositionLoss, naturalSubtreeParameter]
  omega

/- Once Proposition 7.3 has discarded at most `propositionLoss+1` vertices
from each cut side (the extra one is the reserved heavy vertex), these are
exactly the two degree inequalities consumed by `claim712_core_contradiction`.
The first reservoir is oriented toward the side containing at least half of
the total neighbourhood of `v₀`; the second retains the bi-heavy supply. -/
lemma claim712_root_selected_supply
    (m dBig dSmall retainedBig retainedSmall : ℕ)
    (hm : largeThreshold ≤ m)
    (htotal : m ≤ dBig + dSmall)
    (horder : dSmall ≤ dBig)
    (hsmall : heavyScale m + 1 ≤ dSmall)
    (hBigRetained : dBig - (propositionLoss m + 1) ≤ retainedBig)
    (hSmallRetained : dSmall - (propositionLoss m + 1) ≤ retainedSmall) :
    m + 1 ≤ (naturalSubtreeParameter m + 1) / 2 + 2 * retainedBig ∧
      naturalSubtreeParameter m ≤ retainedSmall + 1 := by
  obtain ⟨hrootMargin, hselectedMargin⟩ := claim712_supply_margins m hm
  constructor <;> omega

lemma microScale_lt_heavyThreshold (m : ℕ) (hm : largeThreshold ≤ m) :
    microScale m < heavyScale m + 1 := by
  have h := microScale_le_heavyScale m
  omega

lemma degreeInto_univ_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Erdos547EC2.degreeInto G v Finset.univ = G.degree v := by
  unfold Erdos547EC2.degreeInto
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [and_comm]

/- A density at most `sparseCap` is far below the square of the integral
classification scale.  This form feeds the EC2 rebalancing lemma directly. -/
lemma interedges_lt_heavyScale_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (m : ℕ)
    (hX : X.card = m) (hY : Y.card = m) (hm : 1 ≤ m)
    (hdensity : G.edgeDensity X Y ≤ sparseCap) :
    (G.interedges X Y).card < (heavyScale m + 1) * (heavyScale m + 1) := by
  have hdenQ : (0 : ℚ) < (m : ℚ) * m := by positivity
  have hdensity' :
      ((G.interedges X Y).card : ℚ) / ((m : ℚ) * m) ≤
        1 / (densityDenom : ℚ) := by
    simpa [SimpleGraph.edgeDensity_def, hX, hY, sparseCap] using hdensity
  have hDq : (0 : ℚ) < densityDenom := by
    exact_mod_cast densityDenom_pos
  have hedgeQ :
      ((G.interedges X Y).card : ℚ) * densityDenom ≤ (m : ℚ) * m := by
    have h := (div_le_iff₀ hdenQ).mp hdensity'
    calc
      ((G.interedges X Y).card : ℚ) * densityDenom ≤
          (1 / (densityDenom : ℚ) * ((m : ℚ) * m)) * densityDenom :=
        mul_le_mul_of_nonneg_right h hDq.le
      _ = (m : ℚ) * m := by field_simp
  have hedgeN :
      (G.interedges X Y).card * densityDenom ≤ m * m := by
    exact_mod_cast hedgeQ
  have hmScale : m < scaleDenom * heavyScale m := by
    have hdiv := Nat.mod_add_div m scaleDenom
    have hmod := Nat.mod_lt m scaleDenom_pos
    calc
      m = m % scaleDenom + scaleDenom * (m / scaleDenom) := hdiv.symm
      _ < scaleDenom + scaleDenom * (m / scaleDenom) :=
        Nat.add_lt_add_right hmod _
      _ = scaleDenom * heavyScale m := by
        simp [heavyScale, Nat.mul_add, Nat.add_comm]
  have hcoeff : scaleDenom * scaleDenom < densityDenom := by
    norm_num [densityDenom, microDenom, scaleDenom]
  have hkpos : 0 < heavyScale m := by simp [heavyScale]
  nlinarith

/- The sharper `sqrt(alpha) * m` error scale used by Proposition 7.3 inside
Claim 7.12. -/
lemma interedges_lt_microScale_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (m : ℕ)
    (hX : X.card = m) (hY : Y.card = m) (hm : 1 ≤ m)
    (hdensity : G.edgeDensity X Y ≤ sparseCap) :
    (G.interedges X Y).card < (microScale m + 1) * (microScale m + 1) := by
  have hdenQ : (0 : ℚ) < (m : ℚ) * m := by positivity
  have hdensity' :
      ((G.interedges X Y).card : ℚ) / ((m : ℚ) * m) ≤
        1 / (densityDenom : ℚ) := by
    simpa [SimpleGraph.edgeDensity_def, hX, hY, sparseCap] using hdensity
  have hDq : (0 : ℚ) < densityDenom := by
    exact_mod_cast densityDenom_pos
  have hedgeQ :
      ((G.interedges X Y).card : ℚ) * densityDenom ≤ (m : ℚ) * m := by
    have h := (div_le_iff₀ hdenQ).mp hdensity'
    calc
      ((G.interedges X Y).card : ℚ) * densityDenom ≤
          (1 / (densityDenom : ℚ) * ((m : ℚ) * m)) * densityDenom :=
        mul_le_mul_of_nonneg_right h hDq.le
      _ = (m : ℚ) * m := by field_simp
  have hedgeN :
      (G.interedges X Y).card * densityDenom ≤ m * m := by
    exact_mod_cast hedgeQ
  have hmScale : m < microDenom * microScale m := by
    have hdiv := Nat.mod_add_div m microDenom
    have hmod : m % microDenom < microDenom := by
      exact Nat.mod_lt m (by norm_num [microDenom, scaleDenom])
    calc
      m = m % microDenom + microDenom * (m / microDenom) := hdiv.symm
      _ < microDenom + microDenom * (m / microDenom) :=
        Nat.add_lt_add_right hmod _
      _ = microDenom * microScale m := by
        simp [microScale, Nat.mul_add, Nat.add_comm]
  have hcoeff : microDenom * microDenom = densityDenom := by
    simp [densityDenom, pow_two]
  have hkpos : 0 < microScale m := by simp [microScale]
  nlinarith

/- The discrete hypothesis of Proposition 7.3: the micro error times the
side order is dominated by the square of the reservoir loss. -/
lemma microScale_mul_le_reservoirLoss_sq (m : ℕ)
    (hm : largeThreshold ≤ m) :
    microScale m * m ≤ reservoirLoss m * (reservoirLoss m + 1) := by
  have hDpos : 0 < microDenom := by
    norm_num [microDenom, scaleDenom]
  have hKpos : 0 < scaleDenom := scaleDenom_pos
  have hmicroMul : microDenom * microScale m ≤ 2 * m := by
    have hbase : microDenom * (m / microDenom) ≤ m := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m microDenom
    simp only [microScale, Nat.mul_add]
    have hadd := Nat.add_le_add hbase (by simpa [largeThreshold] using hm)
    omega
  have hmHeavy : m < scaleDenom * heavyScale m := by
    have hdiv := Nat.mod_add_div m scaleDenom
    have hmod := Nat.mod_lt m hKpos
    calc
      m = m % scaleDenom + scaleDenom * (m / scaleDenom) := hdiv.symm
      _ < scaleDenom + scaleDenom * (m / scaleDenom) :=
        Nat.add_lt_add_right hmod _
      _ = scaleDenom * heavyScale m := by
        simp [heavyScale, Nat.mul_add, Nat.add_comm]
  have hheavyLoss : heavyScale m ≤ 20 * reservoirLoss m := by
    simp only [reservoirLoss]
    omega
  have hmLoss : m ≤ 20 * scaleDenom * reservoirLoss m := by
    nlinarith
  have hDexact : microDenom = 1600 * scaleDenom * scaleDenom := by
    simp [microDenom, pow_two]
    ring
  have hposLoss : 0 < reservoirLoss m := by simp [reservoirLoss]
  have hmicroM :
      microDenom * (microScale m * m) ≤ 2 * m * m := by
    nlinarith [Nat.mul_le_mul_right m hmicroMul]
  have hsq : m * m ≤
      (20 * scaleDenom * reservoirLoss m) *
        (20 * scaleDenom * reservoirLoss m) :=
    Nat.mul_le_mul hmLoss hmLoss
  have hcompare :
      2 * m * m ≤ microDenom *
        (reservoirLoss m * reservoirLoss m) := by
    rw [hDexact]
    nlinarith
  have hcancel :
      microDenom * (microScale m * m) ≤
        microDenom * (reservoirLoss m * reservoirLoss m) :=
    hmicroM.trans hcompare
  have hsqFinal :
      microScale m * m ≤ reservoirLoss m * reservoirLoss m :=
    Nat.le_of_mul_le_mul_left hcancel hDpos
  exact hsqFinal.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

lemma microScale_mul_le_propositionLoss_sq (m : ℕ)
    (hm : largeThreshold ≤ m) :
    microScale m * m ≤ propositionLoss m * (propositionLoss m + 1) := by
  have hDpos : 0 < microDenom := by
    norm_num [microDenom, scaleDenom]
  have hmicroTwice :
      2 * microDenom * microScale m ≤ 3 * m := by
    have hbase : microDenom * (m / microDenom) ≤ m := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m microDenom
    have htwoD : 2 * microDenom ≤ m := by
      simpa [largeThreshold] using hm
    simp only [microScale]
    nlinarith
  have hmHeavy : m < scaleDenom * heavyScale m := by
    have hdiv := Nat.mod_add_div m scaleDenom
    have hmod := Nat.mod_lt m scaleDenom_pos
    calc
      m = m % scaleDenom + scaleDenom * (m / scaleDenom) := hdiv.symm
      _ < scaleDenom + scaleDenom * (m / scaleDenom) :=
        Nat.add_lt_add_right hmod _
      _ = scaleDenom * heavyScale m := by
        simp [heavyScale, Nat.mul_add, Nat.add_comm]
  have hheavyLoss : heavyScale m ≤ 30 * propositionLoss m := by
    simp only [propositionLoss]
    omega
  have hmLoss : m ≤ 30 * scaleDenom * propositionLoss m := by
    nlinarith
  have hDexact : microDenom = 1600 * scaleDenom * scaleDenom := by
    simp [microDenom, pow_two]
    ring
  have hmicroM :
      2 * microDenom * (microScale m * m) ≤ 3 * m * m := by
    nlinarith [Nat.mul_le_mul_right m hmicroTwice]
  have hsq : m * m ≤
      (30 * scaleDenom * propositionLoss m) *
        (30 * scaleDenom * propositionLoss m) :=
    Nat.mul_le_mul hmLoss hmLoss
  have hcompare :
      3 * m * m ≤ 2 * microDenom *
        (propositionLoss m * propositionLoss m) := by
    rw [hDexact]
    nlinarith
  have hcancel :
      (2 * microDenom) * (microScale m * m) ≤
        (2 * microDenom) *
          (propositionLoss m * propositionLoss m) := by
    nlinarith
  have hsqFinal :
      microScale m * m ≤ propositionLoss m * propositionLoss m :=
    Nat.le_of_mul_le_mul_left hcancel (by positivity)
  exact hsqFinal.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

lemma claim712_loss_margin (m : ℕ) (hm : largeThreshold ≤ m) :
    3 * microScale m + propositionLoss m + 3 ≤ reservoirLoss m := by
  have hh := heavyScale_large m hm
  have hratio := thousand_microScale_le_heavyScale m hm
  simp only [propositionLoss, reservoirLoss]
  omega

/- The three capacity inequalities needed to build one Claim 7.12
reservoir.  They are a direct consequence of the two balanced high-vertex
counts and the micro-scale pruning loss. -/
lemma claim712_reservoir_card_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (Vᵢ Vⱼ L A : Finset V) (m : ℕ)
    (hdisj : Disjoint Vᵢ Vⱼ) (hcover : Vᵢ ∪ Vⱼ = Finset.univ)
    (hVᵢcard : Vᵢ.card = m) (hLcard : L.card = m)
    (hbalᵢ : (Vᵢ ∩ L).card < (m + 1) / 2 + microScale m)
    (hbalⱼ : (Vⱼ ∩ L).card < (m + 1) / 2 + microScale m)
    (hAsub : A ⊆ Vᵢ ∩ L)
    (hpruned : (Vᵢ ∩ L).card ≤ A.card + microScale m)
    (hm : largeThreshold ≤ m) :
    reservoirScale m + 1 + microScale m ≤ A.card ∧
      reservoirScale m + 1 + propositionLoss m ≤ A.card ∧
      reservoirScale m + 1 + microScale m + propositionLoss m ≤
        (Vᵢ \ A).card := by
  have hsplitDisj : Disjoint (Vᵢ ∩ L) (Vⱼ ∩ L) := by
    rw [Finset.disjoint_left]
    intro v hvi hvj
    exact (Finset.disjoint_left.mp hdisj
      (Finset.mem_inter.mp hvi).1 (Finset.mem_inter.mp hvj).1)
  have hsplitUnion : (Vᵢ ∩ L) ∪ (Vⱼ ∩ L) = L := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvi | hvj
      · exact (Finset.mem_inter.mp hvi).2
      · exact (Finset.mem_inter.mp hvj).2
    · intro hvL
      have hvU : v ∈ Vᵢ ∪ Vⱼ := by simpa [hcover]
      rcases Finset.mem_union.mp hvU with hvi | hvj
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvi, hvL⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvj, hvL⟩)
  have hsum : (Vᵢ ∩ L).card + (Vⱼ ∩ L).card = m := by
    rw [← Finset.card_union_of_disjoint hsplitDisj, hsplitUnion, hLcard]
  have hAupper : A.card ≤ (Vᵢ ∩ L).card := Finset.card_le_card hAsub
  have hAsubVi : A ⊆ Vᵢ := fun v hv => (Finset.mem_inter.mp (hAsub hv)).1
  have hcompl : (Vᵢ \ A).card + A.card = m := by
    rw [Finset.card_sdiff_of_subset hAsubVi, hVᵢcard]
    omega
  have hmargin := claim712_loss_margin m hm
  have hrespos := reservoirScale_pos m hm
  simp only [reservoirScale] at hmargin hrespos ⊢
  omega

/- The reservoir-free Claim 7.12 wrapper consumes the corresponding bounds
before the two pruning operations.  Balancedness of both intersections and
their exact sum give all six inequalities symmetrically. -/
lemma claim712_balanced_capacities
    (m x y : ℕ) (hm : largeThreshold ≤ m)
    (hsum : x + y = m)
    (hbalx : x < (m + 1) / 2 + microScale m)
    (hbaly : y < (m + 1) / 2 + microScale m) :
    (reservoirScale m + 1 + microScale m + microScale m ≤ x ∧
      reservoirScale m + 1 + propositionLoss m + microScale m ≤ x ∧
      reservoirScale m + 1 + microScale m + propositionLoss m + x ≤ m) ∧
    (reservoirScale m + 1 + microScale m + microScale m ≤ y ∧
      reservoirScale m + 1 + propositionLoss m + microScale m ≤ y ∧
      reservoirScale m + 1 + microScale m + propositionLoss m + y ≤ m) := by
  have hmargin := claim712_loss_margin m hm
  have hrespos := reservoirScale_pos m hm
  simp only [reservoirScale] at hmargin hrespos ⊢
  omega

/- All remaining scale-only side conditions of the sparse balanced wrapper
for Claim 7.12, in its argument order. -/
lemma claim712_wrapper_arithmetic (m : ℕ) (hm : largeThreshold ≤ m) :
    microScale m < heavyScale m + 1 ∧
      naturalSubtreeParameter m + propositionLoss m ≤ heavyScale m + 1 ∧
      2 ≤ naturalSubtreeParameter m ∧
      naturalSubtreeParameter m ≤ m + 1 ∧
      naturalSubtreeParameter m ≤ reservoirScale m + 1 ∧
      m + 1 + 2 * (propositionLoss m + 1) ≤
        (naturalSubtreeParameter m + 1) / 2 + 2 * ((m + 1) / 2) ∧
      2 * m + 1 ≤ (naturalSubtreeParameter m + 1) / 2 +
        4 * reservoirScale m := by
  have hmicro := microScale_lt_heavyThreshold m hm
  obtain ⟨hrootMargin, hselectedMargin⟩ := claim712_supply_margins m hm
  obtain ⟨hk2, hkT, _hkHeavy⟩ := naturalSubtreeParameter_bounds m hm
  have hqpos := reservoirScale_pos m hm
  have hqLarge : naturalSubtreeParameter m ≤ reservoirScale m + 1 := by
    have hh := heavyScale_large m hm
    have hm' : 1000 * scaleDenom ≤ m := by
      exact (by norm_num [largeThreshold, microDenom, scaleDenom] :
        1000 * scaleDenom ≤ largeThreshold).trans hm
    simp only [naturalSubtreeParameter, reservoirScale, reservoirLoss,
      heavyScale] at hqpos ⊢
    norm_num [scaleDenom] at hm' hh ⊢
    omega
  have hroot : m + 1 + 2 * (propositionLoss m + 1) ≤
      (naturalSubtreeParameter m + 1) / 2 + 2 * ((m + 1) / 2) := by
    have hmceil : m ≤ 2 * ((m + 1) / 2) := by omega
    omega
  have hfinal := claim712_selected_order_estimate m
    ((naturalSubtreeParameter m + 1) / 2) hm (by rfl)
  exact ⟨hmicro, hselectedMargin, hk2, hkT, hqLarge, hroot, hfinal⟩

/- Select exactly `m` high vertices, as Zhao does before classifying them. -/
lemma exists_exact_high_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ)
    (hlarge : m ≤ (Finset.univ.filter fun v => m ≤ G.degree v).card) :
    ∃ L : Finset V, L.card = m ∧ ∀ v ∈ L, m ≤ G.degree v := by
  obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq hlarge
  refine ⟨L, hLcard, ?_⟩
  intro v hv
  exact (Finset.mem_filter.mp (hLsub hv)).2

/- The exact EC2-to-EC3 conversion after Claim 7.12. -/
theorem ec2_to_dense_side_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {V₁ V₂ L : Finset V} {n k b : ℕ}
    (hV : Fintype.card V = 2 * n)
    (hV₁card : V₁.card = n)
    (hdisjV : Disjoint V₁ V₂) (hcover : V₁ ∪ V₂ = Finset.univ)
    (hLcard : L.card = n)
    (hlarge : ∀ v ∈ L,
      n ≤ Erdos547EC2.degreeInto G v Finset.univ)
    (hk : 2 * k < n)
    (hnoBoth : ∀ v ∈ L,
      ¬(k < Erdos547EC2.degreeInto G v V₁ ∧
        k < Erdos547EC2.degreeInto G v V₂))
    (hcross : (G.interedges V₁ V₂).card < (b + 1) * (k + 1)) :
    ∃ (A W : Finset V),
      W.card = n ∧ n ≤ 2 * A.card ∧ A ⊆ L ∧ A ⊆ W ∧
        ∀ v ∈ A, n - k - 2 * b ≤ Erdos547EC2.degreeInto G v W := by
  classical
  let L₁ := Erdos547EC2.classified G L V₁ k
  let L₂ := Erdos547EC2.classified G L V₂ k
  obtain ⟨hdisjL, _hunionL, hclasses⟩ :=
    Erdos547EC2.classified_partition_large
      G hdisjV hcover hLcard hlarge hk hnoBoth
  have hclassSum : L₁.card + L₂.card = n := by
    simpa [L₁, L₂] using hclasses
  have hV₂card : V₂.card = n := by
    have hcards := Finset.card_union_of_disjoint hdisjV
    rw [hcover, Finset.card_univ, hV, hV₁card] at hcards
    omega
  have hcross' :
      (G.interedges V₂ V₁).card < (b + 1) * (k + 1) := by
    let : Std.Symm G.Adj := G.symm
    rw [show (G.interedges V₂ V₁).card =
        (G.interedges V₁ V₂).card by
      exact Rel.card_interedges_comm V₂ V₁]
    exact hcross
  have hlarge₁ : ∀ v ∈ L₁,
      n ≤ Erdos547EC2.degreeInto G v Finset.univ := by
    intro v hv
    exact hlarge v (Erdos547EC2.classified_subset_left G L V₁ k hv)
  have hlarge₂ : ∀ v ∈ L₂,
      n ≤ Erdos547EC2.degreeInto G v Finset.univ := by
    intro v hv
    exact hlarge v (Erdos547EC2.classified_subset_left G L V₂ k hv)
  have hclass₁ : ∀ v ∈ L₁, k < Erdos547EC2.degreeInto G v V₁ := by
    intro v hv
    exact Erdos547EC2.classified_mem_degree G hv
  have hclass₂ : ∀ v ∈ L₂, k < Erdos547EC2.degreeInto G v V₂ := by
    intro v hv
    exact Erdos547EC2.classified_mem_degree G hv
  have hnot₂ : ∀ v ∈ L₁, Erdos547EC2.degreeInto G v V₂ ≤ k := by
    intro v hv
    apply Nat.le_of_not_gt
    intro hv₂
    exact hnoBoth v (Erdos547EC2.classified_subset_left G L V₁ k hv)
      ⟨hclass₁ v hv, hv₂⟩
  have hnot₁ : ∀ v ∈ L₂, Erdos547EC2.degreeInto G v V₁ ≤ k := by
    intro v hv
    apply Nat.le_of_not_gt
    intro hv₁
    exact hnoBoth v (Erdos547EC2.classified_subset_left G L V₂ k hv)
      ⟨hv₁, hclass₂ v hv⟩
  rcases le_total L₁.card L₂.card with h₁₂ | h₂₁
  · obtain ⟨W, hWcard, hL₂W, hdeg⟩ :=
      Erdos547EC2.exists_dense_balanced_side_of_classification
        G hV hV₂card hdisjV.symm
          (by simpa [Finset.union_comm] using hcover)
          hdisjL.symm (by omega) hlarge₂ hclass₂ hclass₁ hnot₁ hcross'
    refine ⟨L₂, W, hWcard, by omega, ?_, hL₂W, hdeg⟩
    exact Erdos547EC2.classified_subset_left G L V₂ k
  · obtain ⟨W, hWcard, hL₁W, hdeg⟩ :=
      Erdos547EC2.exists_dense_balanced_side_of_classification
        G hV hV₁card hdisjV hcover hdisjL hclassSum
          hlarge₁ hclass₁ hclass₂ hnot₂ hcross
    refine ⟨L₁, W, hWcard, by omega, ?_, hL₁W, hdeg⟩
    exact Erdos547EC2.classified_subset_left G L V₁ k

theorem exists_ec3Witness_of_sparseCut_of_noBoth
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y L : Finset V) (m : ℕ)
    (hcardV : Fintype.card V = 2 * m)
    (hX : X.card = m) (hY : Y.card = m)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hLcard : L.card = m)
    (hlarge : ∀ v ∈ L, m ≤ G.degree v)
    (hm : 4 ≤ m)
    (hdensity : G.edgeDensity X Y ≤ sparseCap)
    (hnoBoth : ∀ v ∈ L,
      ¬(heavyScale m < Erdos547EC2.degreeInto G v X ∧
        heavyScale m < Erdos547EC2.degreeInto G v Y)) :
    ∃ h : Erdos547b.ZhaoLemma74.RawEC3Witness G m (defectScale m), True := by
  let k := heavyScale m
  have hk : 2 * k < m := by
    dsimp [k, heavyScale, scaleDenom]
    omega
  have hcross :
      (G.interedges X Y).card < (k + 1) * (k + 1) := by
    exact interedges_lt_heavyScale_sq G X Y m hX hY (by omega) hdensity
  have hlarge' : ∀ v ∈ L,
      m ≤ Erdos547EC2.degreeInto G v Finset.univ := by
    intro v hv
    rw [degreeInto_univ_eq_degree]
    exact hlarge v hv
  obtain ⟨A, W, hWcard, hAcard, hAL, hAW, hdeg⟩ :=
    ec2_to_dense_side_high
      G hcardV hX hXY hcover hLcard hlarge' hk hnoBoth hcross
  have hhighA : ∀ v ∈ A, m ≤ G.degree v := by
    intro v hv
    exact hlarge v (hAL hv)
  have hWcomplCard : Wᶜ.card = m := by
    rw [Finset.card_compl, hcardV, hWcard]
    omega
  refine ⟨
    { V₁ := W
      V₂ := Wᶜ
      A := A
      cut_disjoint := by
        rw [Finset.disjoint_left]
        intro x hx hxc
        exact (Finset.mem_compl.mp hxc) hx
      cut_cover := Finset.union_compl W
      card_V₁ := hWcard
      card_V₂ := hWcomplCard
      A_subset := hAW
      card_A := by omega
      high_count := by
        have hLhigh : L ⊆ Erdos547b.ZhaoLemma74.highVertices G m := by
          intro v hv
          exact Erdos547b.ZhaoLemma74.mem_highVertices.mpr (hlarge v hv)
        have hc := Finset.card_le_card hLhigh
        rw [hLcard] at hc
        omega
      high_A := hhighA
      dense_A_V₁ := ?_ }, trivial⟩
  intro v hv
  have hd := hdeg v hv
  simp only [defectScale]
  dsimp [k] at hd
  omega

/- Before Claim 7.12, Zhao separates the case in which one half of the
sparse cut already contains at least `ceil(m/2)+b` selected high vertices.
Deleting the at most `b` vertices of large cross-degree leaves the EC3 high
set directly.  The complementary case is exactly the balance hypothesis
used inside Claim 7.12. -/
theorem exists_early_ec3_or_balanced_large
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y L : Finset V) (m : ℕ)
    (hX : X.card = m) (hY : Y.card = m)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hLcard : L.card = m)
    (hlarge : ∀ v ∈ L, m ≤ G.degree v)
    (hm : 2 ≤ m)
    (hdensity : G.edgeDensity X Y ≤ sparseCap) :
    (∃ h : Erdos547b.ZhaoLemma74.RawEC3Witness G m (defectScale m), True) ∨
      ((X ∩ L).card < (m + 1) / 2 + microScale m ∧
       (Y ∩ L).card < (m + 1) / 2 + microScale m) := by
  have hcross :
      (G.interedges X Y).card <
        (microScale m + 1) * (microScale m + 1) :=
    interedges_lt_microScale_sq G X Y m hX hY (by omega) hdensity
  have hlarge' : ∀ v ∈ L,
      m ≤ Erdos547EC2.degreeInto G v Finset.univ := by
    intro v hv
    rw [degreeInto_univ_eq_degree]
    exact hlarge v hv
  have hmicroHeavy : microScale m ≤ heavyScale m :=
    microScale_le_heavyScale m
  by_cases hbalX :
      (X ∩ L).card < (m + 1) / 2 + microScale m
  · by_cases hbalY :
        (Y ∩ L).card < (m + 1) / 2 + microScale m
    · exact Or.inr ⟨hbalX, hbalY⟩
    · left
      obtain ⟨A, hAYL, hcardA, _hcrossA, hdenseA⟩ :=
        Erdos547Claim712.exists_low_cross_large_side
          G hXY.symm (by simpa [Finset.union_comm] using hcover)
          hlarge' (by
            let : Std.Symm G.Adj := G.symm
            rw [show (G.interedges Y X).card =
                (G.interedges X Y).card by
              exact (@Rel.card_interedges_comm V G.Adj _ _ X Y).symm]
            exact hcross)
      have hceilA : (m + 1) / 2 ≤ A.card := by omega
      have hAY : A ⊆ Y := by
        intro v hv
        exact (Finset.mem_inter.mp (hAYL hv)).1
      have hAL : A ⊆ L := by
        intro v hv
        exact (Finset.mem_inter.mp (hAYL hv)).2
      refine ⟨{
        V₁ := Y
        V₂ := X
        A := A
        cut_disjoint := hXY.symm
        cut_cover := by simpa [Finset.union_comm] using hcover
        card_V₁ := hY
        card_V₂ := hX
        A_subset := hAY
        card_A := hceilA
        high_count := by
          have hLhigh : L ⊆ Erdos547b.ZhaoLemma74.highVertices G m := by
            intro v hv
            exact Erdos547b.ZhaoLemma74.mem_highVertices.mpr (hlarge v hv)
          have hc := Finset.card_le_card hLhigh
          rw [hLcard] at hc
          omega
        high_A := fun v hv => hlarge v (hAL hv)
        dense_A_V₁ := by
          intro v hv
          have hd := hdenseA v hv
          simp only [defectScale]
          omega }, trivial⟩
  · left
    obtain ⟨A, hAXL, hcardA, _hcrossA, hdenseA⟩ :=
      Erdos547Claim712.exists_low_cross_large_side
        G hXY hcover hlarge' hcross
    have hceilA : (m + 1) / 2 ≤ A.card := by omega
    have hAX : A ⊆ X := by
      intro v hv
      exact (Finset.mem_inter.mp (hAXL hv)).1
    have hAL : A ⊆ L := by
      intro v hv
      exact (Finset.mem_inter.mp (hAXL hv)).2
    refine ⟨{
      V₁ := X
      V₂ := Y
      A := A
      cut_disjoint := hXY
      cut_cover := hcover
      card_V₁ := hX
      card_V₂ := hY
      A_subset := hAX
      card_A := hceilA
      high_count := by
        have hLhigh : L ⊆ Erdos547b.ZhaoLemma74.highVertices G m := by
          intro v hv
          exact Erdos547b.ZhaoLemma74.mem_highVertices.mpr (hlarge v hv)
        have hc := Finset.card_le_card hLhigh
        rw [hLcard] at hc
        omega
      high_A := fun v hv => hlarge v (hAL hv)
      dense_A_V₁ := by
        intro v hv
        have hd := hdenseA v hv
        simp only [defectScale]
        omega }, trivial⟩

/- The structural conclusion of Section 7 before invoking Lemma 7.4:
an omitted exact-order tree forces the sparse balanced cut to normalize to
EC3.  The early unbalanced branch and Claim 7.12 are both internal here. -/
theorem exists_rawEC3_of_sparseCut_of_omitted_exact_tree
    {V A : Type*} [Fintype V] [Fintype A]
    [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) (T : SimpleGraph A)
    [DecidableRel G.Adj] [DecidableRel T.Adj]
    (X Y L : Finset V) (m : ℕ)
    (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (hcardT : Fintype.card A = m + 1)
    (hcardV : Fintype.card V = 2 * m)
    (hX : X.card = m) (hY : Y.card = m)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hLcard : L.card = m)
    (hlarge : ∀ v ∈ L, m ≤ G.degree v)
    (hm : largeThreshold ≤ m)
    (hdensity : G.edgeDensity X Y ≤ sparseCap) :
    ∃ h : Erdos547b.ZhaoLemma74.RawEC3Witness G m (defectScale m), True := by
  classical
  have hm2 : 2 ≤ m := by
    have : 2 ≤ largeThreshold := by
      norm_num [largeThreshold, microDenom, scaleDenom]
    omega
  rcases exists_early_ec3_or_balanced_large G X Y L m hX hY hXY hcover
      hLcard hlarge hm2 hdensity with hearly | hbalanced
  · exact hearly
  · obtain ⟨hbalX, hbalY⟩ := hbalanced
    have hsplitDisj : Disjoint (X ∩ L) (Y ∩ L) := by
      rw [Finset.disjoint_left]
      intro v hvX hvY
      exact Finset.disjoint_left.mp hXY
        (Finset.mem_inter.mp hvX).1 (Finset.mem_inter.mp hvY).1
    have hsplitUnion : (X ∩ L) ∪ (Y ∩ L) = L := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).2
        · exact (Finset.mem_inter.mp hv).2
      · intro hvL
        have hvU : v ∈ X ∪ Y := by simpa [hcover]
        rcases Finset.mem_union.mp hvU with hvX | hvY
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvX, hvL⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvY, hvL⟩)
    have hsum : (X ∩ L).card + (Y ∩ L).card = m := by
      rw [← Finset.card_union_of_disjoint hsplitDisj, hsplitUnion, hLcard]
    obtain ⟨hcapX, hcapY⟩ := claim712_balanced_capacities m
      (X ∩ L).card (Y ∩ L).card hm hsum hbalX hbalY
    obtain ⟨htHeavy, hkHeavy, hk2, hkT, hkq, hroot, hfinal⟩ :=
      claim712_wrapper_arithmetic m hm
    have hcross : (G.interedges X Y).card <
        (microScale m + 1) * (microScale m + 1) :=
      interedges_lt_microScale_sq G X Y m hX hY (by omega) hdensity
    have hscale : microScale m * m ≤
        propositionLoss m * (propositionLoss m + 1) :=
      microScale_mul_le_propositionLoss_sq m hm
    have hnoBoth := Erdos547Claim712.claim712_no_biheavy_of_sparse_balanced
      T G hT homit X Y L m (microScale m) (microScale m)
      (propositionLoss m) (reservoirScale m)
      (naturalSubtreeParameter m) (heavyScale m + 1)
      hcardT hX hY hXY hcover hlarge hcross hscale
      hcapX.1 hcapX.2.1 hcapX.2.2
      hcapY.1 hcapY.2.1 hcapY.2.2
      htHeavy hkHeavy hk2 (by simpa [hcardT] using hkT) hkq hroot hfinal
    apply exists_ec3Witness_of_sparseCut_of_noBoth G X Y L m hcardV hX hY
      hXY hcover hLcard hlarge (by omega) hdensity
    intro v hv
    simpa only [Nat.lt_iff_add_one_le] using hnoBoth v hv

/- The concrete sparse-cut embedding implication at the constants constructed
in this file.  Keeping this implication named avoids losing the explicit
witnesses when consumers unpack the existentially packaged property. -/
theorem zhaoSparseCutEmbeddingAtCap :
    ∀ (α : ℚ), 0 < α → α ≤ sparseCap →
      ∀ (n : ℕ), largeThreshold + 1 ≤ n →
        ∀ (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj],
          n - 1 ≤ (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card →
            Erdos547b.ZhaoExtremalCaseTwo α G →
              Erdos547b.ZhaoContainsAllTrees G := by
  classical
  intro α hα hαcap n hn G _hGdec hhigh hec2
  have hdec : _hGdec = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases hdec
  intro t T hT ht
  let m := n - 1
  have hm : largeThreshold ≤ m := by
    dsimp [m]
    omega
  have hnpos : 0 < n := by
    have : 0 < largeThreshold := by
      norm_num [largeThreshold, microDenom, scaleDenom]
    omega
  have htm : t ≤ m + 1 := by
    dsimp [m]
    have htpos : 0 < t := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_pos_iff.mpr hT.connected.nonempty)
    omega
  unfold Erdos547b.ZhaoExtremalCaseTwo at hec2
  obtain ⟨X, Y, hcut, hdensityα⟩ := hec2
  obtain ⟨hXY, hcover, hXn, hYn⟩ := hcut
  have hX : X.card = m := by simpa [m] using hXn
  have hY : Y.card = m := by simpa [m] using hYn
  have hdensity : G.edgeDensity X Y ≤ sparseCap := hdensityα.trans hαcap
  have hcardV : Fintype.card (Fin (2 * n - 2)) = 2 * m := by
    simp [m]
    omega
  obtain ⟨L, hLcard, hlarge⟩ := exists_exact_high_set G m (by
    simpa [m] using hhigh)
  apply Erdos547b.TreePadding.isContained_of_forall_fin_tree T G m
    (by simpa only [Fintype.card_fin] using htm) hT
  intro T' hT'
  by_contra homit
  obtain ⟨hraw, -⟩ := exists_rawEC3_of_sparseCut_of_omitted_exact_tree
    G T' X Y L m hT' homit (by simp) hcardV hX hY hXY hcover
      hLcard hlarge hm hdensity
  have hmscale : scaleDenom ≤ m := by
    have : scaleDenom ≤ largeThreshold := by
      norm_num [largeThreshold, microDenom, scaleDenom]
    omega
  have hscale : defectScale m * m ≤ rootScale m * (rootScale m + 1) := by
    have hsquare := (sourceHierarchy m hmscale).defect_square
    exact hsquare.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  exact homit (hraw.contains_every_exact_tree hscale
    (sourceFullSeparation m hmscale) (sourceRadiusPos m) T' hT' (by simp))

/- Zhao's sparse-cut embedding property (Theorem 3.2, sparse branch), with
the structural Section 7 reduction and Lemma 7.4 composed internally. -/
theorem zhaoSparseCutEmbeddingProperty :
    Erdos547b.ZhaoSparseCutEmbeddingProperty := by
  classical
  refine ⟨sparseCap, sparseCap_pos, sparseCap_lt_one,
    largeThreshold + 1, ?_⟩
  intro α hα hαcap n hn G hhigh hec2
  exact zhaoSparseCutEmbeddingAtCap α hα hαcap n hn G hhigh hec2

end Erdos547b.ZhaoSparseAssembly

#print axioms Erdos547b.ZhaoSparseAssembly.zhaoSparseCutEmbeddingProperty
