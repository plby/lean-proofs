/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import Util.Ramsey
import ErdosProblems.Erdos920.PrimeScale

/-!
# Numerical packaging of the Bradač construction for Erdős 920

This file gives a precise interface between the finite-geometric `D*`
construction and its analytic use.  A `DStarWitness t m q C` remembers an
actual finite directed graph, its `T_(t+1)`-freeness, its vertex lower bound,
and the bound on forward-independent ordered `m`-tuples.

The random-ordering and sampling/deletion arguments are represented by
`DStarWitness.HasAveragingSamplingConclusion`.  This is deliberately a
property of the concrete witness, rather than a global postulate.  The
projective/counting modules can prove that property once their
finite averaging development is available.  Everything after that interface
is proved here: first the lower bound `m q^(t-1)`, then the substitution of a
prime at scale `m / log(m)^2`, and finally the Bradač exponent.
-/

open Filter
open scoped BigOperators

namespace Erdos920.RamseyPackaging

noncomputable section

/-! ## The directed construction interface -/

/-- A directed graph.  Loops are allowed; the Bradač construction does not
need an irreflexivity assumption at this level. -/
structure Digraph (V : Type*) where
  arc : V → V → Prop

/-- A labelled copy of the transitive tournament `T_r`. -/
def Digraph.HasTransitiveTournament {V : Type*} (D : Digraph V) (r : ℕ) : Prop :=
  ∃ v : Fin r → V, Function.Injective v ∧
    ∀ i j : Fin r, i < j → D.arc (v i) (v j)

/-- An ordered tuple with no arc pointing from an earlier entry to a later
entry.  Repetitions are intentionally allowed. -/
def Digraph.IsForwardIndependent {V : Type*} (D : Digraph V) {m : ℕ}
    (v : Fin m → V) : Prop :=
  ∀ i j : Fin m, i < j → ¬ D.arc (v i) (v j)

/-- The number of forward-independent ordered tuples. -/
def Digraph.forwardIndependentTupleCount {V : Type*} [Fintype V]
    (D : Digraph V) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m → V)).filter
    (fun v => D.IsForwardIndependent v)).card

/-- The exact numerical information supplied by a `D*(t,q)` construction.
The exponent `t` is the projective parameter, so the forbidden transitive
tournament has `t+1` vertices. -/
structure DStarWitness (t m q : ℕ) (C : ℝ) where
  V : Type
  fintypeV : Fintype V
  D : Digraph V
  transitiveTournamentFree : ¬ D.HasTransitiveTournament (t + 1)
  vertex_lower : (q : ℝ) ^ (2 * t - 1) / 4 ≤ (@Fintype.card V fintypeV : ℝ)
  forward_bound :
    ((@Digraph.forwardIndependentTupleCount V fintypeV D m : ℕ) : ℝ) ≤
      (C * (q : ℝ) ^ t) ^ m

namespace DStarWitness

variable {t m q : ℕ} {C : ℝ}

/-- The retention probability used after the random-ordering argument. -/
def samplingDensity (_W : DStarWitness t m q C) : ℝ :=
  (m : ℝ) / (Real.exp 1 * C * (q : ℝ) ^ t)

/-- The conclusion of the two standard finite averaging steps.

The first step chooses a random ordering and turns a `T_(t+1)`-free digraph
into a `K_(t+1)`-free graph.  The factorial saving changes the tuple bound
`(C q^t)^m` into `(e C q^t / m)^m`.  Keeping vertices with probability
`m/(e C q^t)` and deleting one vertex from every surviving independent
`m`-set then gives precisely the strict Ramsey inequality below.

Keeping this conclusion as a named property permits the finite probability
or double-counting proof to live in a separate module without concealing any
numeric assumption used by the final argument. -/
def HasAveragingSamplingConclusion (W : DStarWitness t m q C) : Prop :=
  W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) - 1 <
    (Ramsey.ramseyNumber (t + 1) m : ℝ)

/-- The two standard side conditions for the sampling parameter. -/
def SamplingSideConditions (W : DStarWitness t m q C) : Prop :=
  0 < W.samplingDensity ∧ W.samplingDensity ≤ 1

end DStarWitness

/-! ## From one witness to a Ramsey lower bound -/

/-- A sampled `D*` witness gives the expected `m q^(t-1)` lower bound.

The harmless factor `8` absorbs the `-1` in the sampling/deletion estimate.
The hypothesis `8 e C ≤ m` is automatic eventually and only uses `q ≥ 1`.
-/
theorem ramsey_lower_of_dStarWitness {t m q : ℕ} {C : ℝ}
    (W : DStarWitness t m q C) (ht : 1 ≤ t) (hq : 1 ≤ q)
    (hC : 0 < C) (hm : 8 * Real.exp 1 * C ≤ (m : ℝ))
    (haverage : W.HasAveragingSamplingConclusion) :
    (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * Real.exp 1 * C) ≤
      (Ramsey.ramseyNumber (t + 1) m : ℝ) := by
  let E : ℝ := Real.exp 1
  have hE : 0 < E := Real.exp_pos 1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : 0 < (q : ℝ) ^ t := pow_pos hq0 _
  have hden : 0 < E * C * (q : ℝ) ^ t := mul_pos (mul_pos hE hC) hqpow
  have hcard := W.vertex_lower
  have htwo : 2 * t - 1 = t + (t - 1) := by omega
  have hscale_nonneg :
      0 ≤ (m : ℝ) / (E * C * (q : ℝ) ^ t) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hsample_lower :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) ≤
        W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) := by
    calc
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) =
          ((m : ℝ) / (E * C * (q : ℝ) ^ t)) *
            ((q : ℝ) ^ (2 * t - 1) / 4) := by
              rw [htwo, pow_add]
              field_simp
      _ ≤ ((m : ℝ) / (E * C * (q : ℝ) ^ t)) *
            (@Fintype.card W.V W.fintypeV : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hscale_nonneg
      _ = W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) := by
        rfl
  have hhalf_ge_one :
      1 ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C) := by
    have hqpow_one : (1 : ℝ) ≤ (q : ℝ) ^ (t - 1) := by
      exact one_le_pow₀ (by exact_mod_cast hq)
    have hm' : 8 * E * C ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) := by
      calc
        8 * E * C ≤ (m : ℝ) := hm
        _ ≤ (m : ℝ) * (q : ℝ) ^ (t - 1) := by
          exact le_mul_of_one_le_right (Nat.cast_nonneg _) hqpow_one
    exact (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hE) hC)).2 (by
      simpa [mul_assoc] using hm')
  have hsplit :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (4 * E * C) =
        2 * ((m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C)) := by
    field_simp
    ring
  have hminus_one :
      (m : ℝ) * (q : ℝ) ^ (t - 1) / (8 * E * C) ≤
        W.samplingDensity * (@Fintype.card W.V W.fintypeV : ℝ) - 1 := by
    rw [hsplit] at hsample_lower
    linarith
  exact hminus_one.trans haverage.le

/-! ## A prime at the logarithmic scale -/

/-- All inputs required at one value of the independent-set parameter.
The scale constant `κ` is allowed to depend on the fixed clique size. -/
def HasDStarAtScale (u m : ℕ) (C κ : ℝ) : Prop :=
  ∃ q : ℕ, q.Prime ∧
    κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
    ∃ W : DStarWitness (u + 1) m q C,
      W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion

/-- A useful expanded form of the power in the target Ramsey estimate. -/
lemma target_scale_eq (u m : ℕ) (κ C : ℝ) (hlog : Real.log (m : ℝ) ≠ 0)
    (hC : C ≠ 0) :
    κ ^ u / (8 * Real.exp 1 * C) * (m : ℝ) ^ (u + 1) /
        Real.log (m : ℝ) ^ (2 * u) =
      (m : ℝ) * (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u /
        (8 * Real.exp 1 * C) := by
  rw [pow_succ, mul_pow, div_pow, pow_mul]
  field_simp [hlog, hC]

/-- Substituting `q ≳ m/log²m` in the one-witness lower bound gives the
Bradač exponent `m^(u+1)/log(m)^(2u)`. -/
theorem ramsey_lower_of_hasDStarAtScale {u m : ℕ} {C κ : ℝ}
    (hC : 0 < C) (hκ : 0 ≤ κ) (hm2 : 2 ≤ m)
    (hlarge : 8 * Real.exp 1 * C ≤ (m : ℝ))
    (hstar : HasDStarAtScale u m C κ) :
    κ ^ u / (8 * Real.exp 1 * C) * (m : ℝ) ^ (u + 1) /
        Real.log (m : ℝ) ^ (2 * u) ≤
      (Ramsey.ramseyNumber (u + 2) m : ℝ) := by
  rcases hstar with ⟨q, hqprime, hqscale, W, _hside, haverage⟩
  have hq1 : 1 ≤ q := (Nat.Prime.one_lt hqprime).le
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  have hscale_nonneg : 0 ≤ κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2) :=
    mul_nonneg hκ (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hpow_scale :
      (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u ≤ (q : ℝ) ^ u :=
    pow_le_pow_left₀ hscale_nonneg hqscale _
  have hmul_scale :
      (m : ℝ) * (κ * ((m : ℝ) / Real.log (m : ℝ) ^ 2)) ^ u /
          (8 * Real.exp 1 * C) ≤
        (m : ℝ) * (q : ℝ) ^ u / (8 * Real.exp 1 * C) := by
    gcongr
  rw [target_scale_eq u m κ C hlogpos.ne' hC.ne']
  exact hmul_scale.trans
    (ramsey_lower_of_dStarWitness W (by omega) hq1 hC hlarge haverage)

/-! ## Eventual family packaging -/

/-- An abstract, completely explicit version of the `D*` construction
theorem.  It is the statement that the projective, marked-tree, prime-scale,
random-ordering, and sampling modules jointly need to supply. -/
structure DStarFamily (u : ℕ) where
  C : ℝ
  κ : ℝ
  C_pos : 0 < C
  κ_pos : 0 < κ
  exists_eventually : ∀ᶠ m : ℕ in atTop, HasDStarAtScale u m C κ

/-- A reusable construction-level interface.  Given every prime satisfying
the forward-tuple budget `C q log(q)^2 ≤ m`, it produces the finite `D*`
witness together with the random-ordering and sampling conclusion. -/
structure DStarConstruction (u : ℕ) where
  C : ℝ
  C_pos : 0 < C
  qThreshold : ℕ
  build : ∀ (m q : ℕ), q.Prime → qThreshold ≤ q → 2 ≤ q → q ≤ m →
    (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) →
    C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
      ∃ W : DStarWitness (u + 1) m q C,
        W.SamplingSideConditions ∧ W.HasAveragingSamplingConclusion

/-- Every fixed multiple of `log(m)^2` is eventually at most `m`. -/
private lemma eventually_mul_log_sq_le (K : ℝ) (hK : 0 < K) :
    ∀ᶠ m : ℕ in atTop, K * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
  have heps : 0 < K⁻¹ := inv_pos.mpr hK
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  calc
    K * Real.log (m : ℝ) ^ 2 ≤ K * (K⁻¹ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hK.le
    _ = (m : ℝ) := by field_simp

/-- The lower prime scale tends to infinity, so every fixed construction
threshold is eventually met. -/
private lemma eventually_qThreshold_le_scale (C : ℝ) (hC : 0 < C) (Q : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (Q : ℝ) ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) := by
  have hK : 0 < 8 * C * ((Q : ℝ) + 1) := by positivity
  filter_upwards [eventually_mul_log_sq_le
      (8 * C * ((Q : ℝ) + 1)) hK,
      eventually_ge_atTop (2 : ℕ)] with m hm hm2
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm2)
  rw [le_div_iff₀ (by positivity)]
  calc
    (Q : ℝ) * (8 * C * Real.log (m : ℝ) ^ 2) ≤
        (8 * C * ((Q : ℝ) + 1)) * Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ))]
    _ ≤ (m : ℝ) := hm

/-- Bertrand's postulate, as packaged in `PrimeScale`, turns a construction
valid under the tuple budget into an eventual family at scale
`m / log(m)^2`. -/
def DStarConstruction.toFamily {u : ℕ} (B : DStarConstruction u) :
    DStarFamily u where
  C := B.C
  κ := 1 / (8 * B.C)
  C_pos := B.C_pos
  κ_pos := div_pos (by norm_num) (mul_pos (by norm_num) B.C_pos)
  exists_eventually := by
    filter_upwards [PrimeScale.eventually_exists_prime_scale B.C B.C_pos,
      eventually_qThreshold_le_scale B.C B.C_pos B.qThreshold] with
      m hprime hthreshold
    rcases hprime with ⟨q, hqprime, hq2, hqm, hqscale, hbudget⟩
    have hqthreshold : B.qThreshold ≤ q := by
      exact_mod_cast hthreshold.trans hqscale
    refine ⟨q, hqprime, ?_,
      B.build m q hqprime hqthreshold hq2 hqm hqscale hbudget⟩
    have hm2 : 2 ≤ m := hq2.trans hqm
    have hlog : Real.log (m : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hm2)).ne'
    calc
      (1 / (8 * B.C)) * ((m : ℝ) / Real.log (m : ℝ) ^ 2) =
          (m : ℝ) / (8 * B.C * Real.log (m : ℝ) ^ 2) := by
            field_simp [B.C_pos.ne', hlog]
      _ ≤ (q : ℝ) := hqscale

/-- The final algebraic packaging theorem: an eventual `D*` family implies
the eventual Bradač Ramsey lower bound. -/
theorem bradac_ramsey_lower_bound_eventually_of_dStarFamily (u : ℕ)
    (F : DStarFamily u) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (u + 1) / Real.log (m : ℝ) ^ (2 * u) ≤
          (Ramsey.ramseyNumber (u + 2) m : ℝ) := by
  let A : ℝ := F.κ ^ u / (8 * Real.exp 1 * F.C)
  have hA : 0 < A := div_pos (pow_pos F.κ_pos _) <|
    mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) F.C_pos
  refine ⟨A, hA, ?_⟩
  filter_upwards [F.exists_eventually,
      (eventually_ge_atTop (2 : ℕ)),
      (tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (8 * Real.exp 1 * F.C)))] with m hstar hm2 hlarge
  exact ramsey_lower_of_hasDStarAtScale F.C_pos F.κ_pos.le hm2 hlarge hstar

/-- The same theorem indexed by the forbidden clique size `s`.  This is the
form consumed by the inversion argument in Erdős Problem 920. -/
theorem bradac_ramsey_lower_bound_eventually_of_package (s : ℕ) (hs : 3 ≤ s)
    (F : DStarFamily (s - 2)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (Ramsey.ramseyNumber s m : ℝ) := by
  obtain ⟨A, hA, hbound⟩ :=
    bradac_ramsey_lower_bound_eventually_of_dStarFamily (s - 2) F
  refine ⟨A, hA, ?_⟩
  have hsu : s - 2 + 2 = s := by omega
  have hspow : s - 2 + 1 = s - 1 := by omega
  have hslog : 2 * (s - 2) = 2 * s - 4 := by omega
  simpa [hsu, hspow, hslog] using hbound

/-- Construction-oriented version of the final result.  Supplying the
projective/marked-tree and finite averaging proof through `build` is enough;
prime selection and all exponent arithmetic are discharged here. -/
theorem bradac_ramsey_lower_bound_eventually_of_construction (s : ℕ)
    (hs : 3 ≤ s) (B : DStarConstruction (s - 2)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ᶠ m : ℕ in atTop,
        A * (m : ℝ) ^ (s - 1) / Real.log (m : ℝ) ^ (2 * s - 4) ≤
          (Ramsey.ramseyNumber s m : ℝ) :=
  bradac_ramsey_lower_bound_eventually_of_package s hs B.toFamily

end

end Erdos920.RamseyPackaging

#print axioms Erdos920.RamseyPackaging.bradac_ramsey_lower_bound_eventually_of_construction
