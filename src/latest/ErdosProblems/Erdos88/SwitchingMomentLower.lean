import ErdosProblems.Erdos88.SwitchingLower

open Classical
open scoped BigOperators

namespace Erdos88.Switching

universe u v

/-- Endpoint-distinct switching tuples with uniformly large private blocks. -/
noncomputable def richSwitchingTupleClass
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I]
    (T : Finset (V × V)) (G : SimpleGraph V) (S₀ : Finset V)
    (privateLower : ℝ) : Finset (I → V × V) := by
  classical
  exact Finset.univ.filter fun p ↦
    (∀ j, p j ∈ T) ∧ PairEndpointsDistinct p ∧
      ∀ i, privateLower ≤
        ((switchingPrivateNeighbors G p i S₀).card : ℝ)

@[simp] lemma mem_richSwitchingTupleClass
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I]
    {T : Finset (V × V)} {G : SimpleGraph V} {S₀ : Finset V}
    {privateLower : ℝ} {p : I → V × V} :
    p ∈ richSwitchingTupleClass T G S₀ privateLower ↔
      (∀ j, p j ∈ T) ∧ PairEndpointsDistinct p ∧
        ∀ i, privateLower ≤
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) := by
  classical
  simp [richSwitchingTupleClass]

/-- Generic form of the good-half conclusion of Lemma 13.10(a), expressed
through the named rich-tuple class. -/
lemma switchingTuple_good_half_richClass
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I]
    (G : SimpleGraph V) (S S₀ : Finset V) (delta rho : ℝ)
    (q b : ℕ) (default : V × V)
    (hrich : RichOn G S₀ delta rho (1 / 5)) (hSS₀ : S ⊆ S₀)
    (hrho : 0 ≤ rho)
    (hcommon : ∀ i (p : I → V × V), (∀ j, p j ∈ S ×ˢ S) →
      delta * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ b)
    (hsmallPrivate : 4 * (Fintype.card I *
      ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card * b)) ≤
      (switchingPairs G S S₀ q).card ^ Fintype.card I)
    (hsmallRepeat : 4 * ((2 * Fintype.card I) ^ 2 *
      ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
        S.card)) ≤
      (switchingPairs G S S₀ q).card ^ Fintype.card I) :
    (switchingPairs G S S₀ q).card ^ Fintype.card I ≤
      2 * (richSwitchingTupleClass (I := I)
        (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card)).card := by
  unfold richSwitchingTupleClass
  exact switchingTuple_good_half G S S₀ delta rho (1 / 5 : ℝ)
    q b default hrich hSS₀ hrho hcommon hbudget hsmallPrivate hsmallRepeat

/-- The good-half estimate with the zero-dimensional tuple case included. -/
lemma switchingTuple_good_half_richClass_or_empty
    {V : Type u} [Fintype V] [DecidableEq V]
    {I : Type v} [Fintype I]
    (G : SimpleGraph V) (S S₀ : Finset V) (delta rho : ℝ)
    (q b : ℕ) (default : V × V)
    (hrich : RichOn G S₀ delta rho (1 / 5)) (hSS₀ : S ⊆ S₀)
    (hrho : 0 ≤ rho)
    (hcommon : ∀ i (p : I → V × V), (∀ j, p j ∈ S ×ˢ S) →
      delta * S₀.card ≤
        ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ))
    (hbudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ b)
    (hsmall : 0 < Fintype.card I →
      4 * (Fintype.card I *
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
          S.card * b)) ≤
        (switchingPairs G S S₀ q).card ^ Fintype.card I ∧
      4 * ((2 * Fintype.card I) ^ 2 *
        ((switchingPairs G S S₀ q).card ^ (Fintype.card I - 1) *
          S.card)) ≤
        (switchingPairs G S S₀ q).card ^ Fintype.card I) :
    (switchingPairs G S S₀ q).card ^ Fintype.card I ≤
      2 * (richSwitchingTupleClass (I := I)
        (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card)).card := by
  classical
  by_cases hs0 : Fintype.card I = 0
  · haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp hs0
    have hp : (fun i : I ↦ isEmptyElim i : I → V × V) ∈
        richSwitchingTupleClass (I := I)
          (switchingPairs G S S₀ q) G S₀
            (rho * delta * S₀.card) := by
      rw [mem_richSwitchingTupleClass]
      refine ⟨fun i ↦ isEmptyElim i, ?_, fun i ↦ isEmptyElim i⟩
      intro i
      exact Sum.elim (fun j : I ↦ isEmptyElim j)
        (fun j : I ↦ isEmptyElim j) i
    have hcard : 1 ≤ (richSwitchingTupleClass (I := I)
        (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card)).card :=
      Finset.card_pos.mpr ⟨_, hp⟩
    rw [hs0, pow_zero]
    omega
  · have hspos : 0 < Fintype.card I := Nat.pos_of_ne_zero hs0
    exact switchingTuple_good_half_richClass
      (I := I) G S S₀ delta rho q b default hrich hSS₀ hrho
      hcommon hbudget (hsmall hspos).1 (hsmall hspos).2

/-- Raw-tuple-index specialization of the good-half estimate.  Keeping the
dependent sigma index behind this declaration makes later assembly cheap. -/
lemma rawTuple_richSwitchingTupleClass_half
    {n B D : ℕ} (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
    (delta rho : ℝ) (q b : ℕ) (a : ℤ → ℕ)
    (default : Fin n × Fin n)
    (hrich : RichOn G S₀ delta rho (1 / 5)) (hSS₀ : S ⊆ S₀)
    (hrho : 0 ≤ rho)
    (hcommon : HasLargeCommonNonneighbors G S S₀ delta D)
    (hID : 2 * Fintype.card (RawTupleIndex (switchingLabels B) a) ≤ D)
    (hbudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ b)
    (hsmall : 0 < Fintype.card (RawTupleIndex (switchingLabels B) a) →
      4 * (Fintype.card (RawTupleIndex (switchingLabels B) a) *
        ((switchingPairs G S S₀ q).card ^
            (Fintype.card (RawTupleIndex (switchingLabels B) a) - 1) *
          S.card * b)) ≤
        (switchingPairs G S S₀ q).card ^
          Fintype.card (RawTupleIndex (switchingLabels B) a) ∧
      4 * ((2 * Fintype.card (RawTupleIndex (switchingLabels B) a)) ^ 2 *
        ((switchingPairs G S S₀ q).card ^
            (Fintype.card (RawTupleIndex (switchingLabels B) a) - 1) *
          S.card)) ≤
        (switchingPairs G S S₀ q).card ^
          Fintype.card (RawTupleIndex (switchingLabels B) a)) :
    (switchingPairs G S S₀ q).card ^
        Fintype.card (RawTupleIndex (switchingLabels B) a) ≤
      2 * (richSwitchingTupleClass
        (I := RawTupleIndex (switchingLabels B) a)
        (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card)).card := by
  let I := RawTupleIndex (switchingLabels B) a
  classical
  letI : DecidableEq I := Classical.decEq _
  have hcommon' : ∀ i (p : I → Fin n × Fin n),
      (∀ j, p j ∈ S ×ˢ S) →
        delta * S₀.card ≤
          ((nonneighborsOf G (switchingOtherEndpoints p i) S₀).card : ℝ) :=
    fun i p hp ↦ hcommon.on_switchingOtherEndpoints hID p hp i
  have hmain := switchingTuple_good_half_richClass_or_empty
    (I := I) G S S₀ delta rho q b default
    hrich hSS₀ hrho hcommon' hbudget (fun hspos ↦ by
      simpa only [I] using hsmall (by simpa only [I] using hspos))
  simpa only [I] using hmain

/-- Apply the eventual numerical smallness estimate directly to a raw tuple
index, without exposing its dependent cardinality in the caller. -/
lemma rawTuple_richSwitchingTupleClass_half_of_smallness
    {n B D q : ℕ} (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
    (delta rho : ℝ) (a : ℤ → ℕ) (default : Fin n × Fin n)
    (hrich : RichOn G S₀ delta rho (1 / 5)) (hSS₀ : S ⊆ S₀)
    (hrho : 0 ≤ rho)
    (hcommon : HasLargeCommonNonneighbors G S S₀ delta D)
    (hID : 2 * Fintype.card (RawTupleIndex (switchingLabels B) a) ≤ D)
    (hbudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
      ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊)
    (hlarge : (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
      ((switchingPairs G S S₀ q).card : ℝ))
    (hsmallData : ∀ (s SCard TCard : ℕ),
      0 < s → s ≤ D →
      (SCard : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤ TCard →
      let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
      4 * (s * (TCard ^ (s - 1) * SCard * b)) ≤ TCard ^ s ∧
      4 * ((2 * s) ^ 2 * (TCard ^ (s - 1) * SCard)) ≤ TCard ^ s) :
    (switchingPairs G S S₀ q).card ^
        Fintype.card (RawTupleIndex (switchingLabels B) a) ≤
      2 * (richSwitchingTupleClass
        (I := RawTupleIndex (switchingLabels B) a)
        (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card)).card := by
  apply rawTuple_richSwitchingTupleClass_half
    (B := B) (D := D) G S S₀ delta rho q
    ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ a default
    hrich hSS₀ hrho hcommon hID hbudget
  intro hspos
  exact hsmallData _ S.card (switchingPairs G S S₀ q).card hspos
    (by omega) hlarge

/-- Lower half of the raw-moment comparison required by KSSS Lemma 13.4. -/
def KSSSUnbiasedSwitchingLowerMoments : Prop :=
  ∀ (C A : ℝ), 0 < C → 0 < A →
    ∃ (B : ℕ) (lower : ℝ),
      0 < lower ∧ ∃ N : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
          ∀ x : ℕ,
            |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
              ∃ T : Finset (Fin n × Fin n),
                IsSymmetric T ∧ 0 < (T.card : ℝ) / Real.sqrt n ∧
                  ∀ a : ℤ → ℕ,
                    (∀ i ∈ switchingLabels B, a i ≤ 2) →
                      lower * ((T.card : ℝ) / Real.sqrt n) ^
                          (∑ i ∈ switchingLabels B, a i) /
                          (n : ℝ) ^ (3 / 2 : ℝ) ≤
                        rawMomentExpectation
                          (Finset.univ : Finset (Finset (Fin n)))
                          (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
                          (fun ell U ↦
                            (switchingCount T (edgeScore G) ell U : ℝ))
                          a (switchingLabels B)

/-- Algebraic normalization of a raw-moment count on the Boolean cube. -/
lemma rawMomentExpectation_lower_of_rawMoment
    {n d : ℕ} (hn : 1 ≤ n) (t : ℕ)
    (window : Finset (Fin n) → Prop) (Y : ℤ → Finset (Fin n) → ℝ)
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (c z : ℝ) (hc : 0 ≤ c) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hsd : Fintype.card (RawTupleIndex labels a) ≤ d)
    (hraw :
      (((t : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2) *
        (c * ((2 : ℝ) ^ n *
          (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)))) ≤
        rawMoment (Finset.univ : Finset (Finset (Fin n)))
          window Y a labels)) :
    (c / 2 * z ^ d) *
          ((t : ℝ) / Real.sqrt n) ^
            Fintype.card (RawTupleIndex labels a) /
          (n : ℝ) ^ (3 / 2 : ℝ) ≤
      rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
        window Y a labels := by
  let s := Fintype.card (RawTupleIndex labels a)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hzpow : z ^ d ≤ z ^ s := pow_le_pow_of_le_one hz0 hz1 hsd
  have htwo : 0 < (2 : ℝ) ^ n := by positivity
  rw [rawMomentExpectation]
  have hcard : ((Finset.univ : Finset (Finset (Fin n))).card : ℝ) =
      (2 : ℝ) ^ n := by
    norm_num [Nat.cast_pow]
  rw [hcard]
  apply (le_div_iff₀ htwo).2
  calc
    (c / 2 * z ^ d) * ((t : ℝ) / Real.sqrt n) ^ s /
          (n : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ n ≤
        (c / 2 * z ^ s) * ((t : ℝ) / Real.sqrt n) ^ s /
          (n : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ n := by
      gcongr
    _ = (((t : ℝ) ^ s / 2) *
        (c * ((2 : ℝ) ^ n * (z / Real.sqrt n) ^ s *
          (n : ℝ) ^ (-(3 / 2 : ℝ))))) := by
      simp only [div_pow]
      rw [Real.rpow_neg hnpos.le]
      have hnRpow : (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnpos _)
      field_simp
    _ ≤ _ := by simpa only [s] using hraw

/-- Convert a sufficiently large tuple class with a uniform state count into
the corresponding unnormalised raw-moment lower bound. -/
lemma rawMoment_ge_of_tupleClass
    {n : ℕ} (states : Finset (Finset (Fin n)))
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (tuples : Finset (RawTupleIndex labels a → Fin n × Fin n))
    (stateLower : ℝ) (hstateLower : 0 ≤ stateLower)
    (hgood : T.card ^ Fintype.card (RawTupleIndex labels a) ≤
      2 * tuples.card)
    (hstate : ∀ p ∈ tuples,
      stateLower ≤
        (((states.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ))) :
    ((T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2) *
        stateLower ≤
      rawMoment states window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
        a labels := by
  have hgoodReal :
      (T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2 ≤
        (tuples.card : ℝ) := by
    have hcast :
        ((T.card ^ Fintype.card (RawTupleIndex labels a) : ℕ) : ℝ) ≤
          ((2 * tuples.card : ℕ) : ℝ) := by
      exact_mod_cast hgood
    push_cast at hcast
    linarith
  calc
    ((T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2) *
        stateLower ≤ (tuples.card : ℝ) * stateLower :=
      mul_le_mul_of_nonneg_right hgoodReal hstateLower
    _ ≤ _ := card_tupleClass_mul_stateLower_le_rawMoment
      states window T G labels a tuples stateLower hstateLower hstate

/-- Combine tuple-class summation with Boolean-cube normalization. -/
lemma rawMomentExpectation_lower_of_tupleClass
    {n d : ℕ} (hn : 1 ≤ n)
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (tuples : Finset (RawTupleIndex labels a → Fin n × Fin n))
    (c z : ℝ) (hc : 0 ≤ c) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hsd : Fintype.card (RawTupleIndex labels a) ≤ d)
    (hgood : T.card ^ Fintype.card (RawTupleIndex labels a) ≤
      2 * tuples.card)
    (hstate : ∀ p ∈ tuples,
      c * ((2 : ℝ) ^ n *
          (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ))) :
    (c / 2 * z ^ d) * ((T.card : ℝ) / Real.sqrt n) ^
          Fintype.card (RawTupleIndex labels a) /
        (n : ℝ) ^ (3 / 2 : ℝ) ≤
      rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
        window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
        a labels := by
  have hnonneg : 0 ≤ c * ((2 : ℝ) ^ n *
      (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
      (n : ℝ) ^ (-(3 / 2 : ℝ))) := by positivity
  have hraw := rawMoment_ge_of_tupleClass
    (Finset.univ : Finset (Finset (Fin n))) window T G labels a tuples
    (c * ((2 : ℝ) ^ n *
      (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
      (n : ℝ) ^ (-(3 / 2 : ℝ)))) hnonneg hgood hstate
  exact rawMomentExpectation_lower_of_rawMoment hn T.card window
    (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
    labels a c z hc hz0 hz1 hsd hraw

/-- Version of `rawMomentExpectation_lower_of_tupleClass` that keeps the
uniform state lower bound abstract at the call site.  This avoids unfolding a
large dependent tuple type merely to pass the state-count hypothesis. -/
lemma rawMomentExpectation_lower_of_tupleClass_via_stateLower
    {n d : ℕ} (hn : 1 ≤ n)
    (window : Finset (Fin n) → Prop)
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (tuples : Finset (RawTupleIndex labels a → Fin n × Fin n))
    (stateLower c z : ℝ)
    (hstateLower : stateLower = c * ((2 : ℝ) ^ n *
      (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
      (n : ℝ) ^ (-(3 / 2 : ℝ))))
    (hc : 0 ≤ c) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hsd : Fintype.card (RawTupleIndex labels a) ≤ d)
    (hgood : T.card ^ Fintype.card (RawTupleIndex labels a) ≤
      2 * tuples.card)
    (hstate : ∀ p ∈ tuples, stateLower ≤
      ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ))) :
    (c / 2 * z ^ d) * ((T.card : ℝ) / Real.sqrt n) ^
          Fintype.card (RawTupleIndex labels a) /
        (n : ℝ) ^ (3 / 2 : ℝ) ≤
      rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
        window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
        a labels := by
  apply rawMomentExpectation_lower_of_tupleClass (d := d)
    hn window T G labels a tuples c z hc hz0 hz1 hsd hgood
  intro p hp
  rw [← hstateLower]
  exact hstate p hp

lemma delta_le_rho_of_lemma131_bound {rho delta : ℝ} {D : ℕ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdelta : delta < rho ^ 3 / (3 : ℝ) ^ (D + 1)) :
    delta ≤ rho := by
  have hden : (1 : ℝ) ≤ (3 : ℝ) ^ (D + 1) :=
    one_le_pow₀ (by norm_num)
  have hrho3 : rho ^ 3 ≤ rho := by
    nlinarith [sq_nonneg rho, mul_nonneg hrho.le (sq_nonneg rho)]
  exact hdelta.le.trans ((div_le_self (by positivity) hden).trans hrho3)

/-- Strengthen the uniform fixed-tuple state count so that it applies
directly to membership in the named rich switching-tuple class. -/
theorem exists_uniform_richTupleClass_state_lower_of_data
    (CRam : ℝ) (Bwin : ℕ)
    (hlower : ∀ H A : ℝ, 0 < H → 0 < A →
      ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N ≤ Fintype.card V → FiniteRamseyFree (2 * CRam) G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                  A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ Bwin))
    (delta base rho A : ℝ) (d : ℕ)
    (hCRam : 0 < CRam) (hdelta : 0 < delta) (hbase : 0 < base)
    (hrho : 0 < rho) (hA : 0 < A) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree CRam G →
      ∀ (a : ℤ → ℕ),
        Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤ d →
      ∀ (S S₀ : Finset (Fin n)) (q Dcommon : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta Dcommon →
        2 * Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤
          Dcommon →
        base * n ≤ (S₀.card : ℝ) →
        (∀ v ∈ S, ∀ w ∈ S,
          |(FiniteES.vertexDegree G v : ℝ) / 2 -
            (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) →
      ∀ p ∈ richSwitchingTupleClass
          (I := RawTupleIndex (switchingLabels Bwin) a)
          (switchingPairs G S S₀ q) G S₀
          (rho * delta * S₀.card),
        let etaPrivate := rho * delta * base
        let CPrivate := canonicalPrivateQuadraticConstant etaPrivate Bwin d
        (1 / 2 * canonicalFirstExposureRate d * kappa) *
            ((2 : ℝ) ^ n *
              (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^
                Fintype.card (RawTupleIndex (switchingLabels Bwin) a) *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
          (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
            p ∈ switchingTupleFinset (switchingPairs G S S₀ q)
              (edgeScore G) (switchingLabels Bwin) a U ∧
              |edgeScore G U - x| ≤ (Bwin : ℤ)).card : ℝ) := by
  let etaPrivate := rho * delta * base
  have hetaPrivate : 0 < etaPrivate := by
    dsimp only [etaPrivate]
    positivity
  obtain ⟨kappa, hkappa, N₀, hstate⟩ :=
    exists_uniform_canonical_goodTuple_state_lower_of_data
      CRam Bwin hlower delta base etaPrivate A d
      hCRam hdelta hbase hetaPrivate hA
  refine ⟨kappa, hkappa, N₀, ?_⟩
  intro n hn G hG a hsd S S₀ q Dcommon hcommon hID hS₀ hdegree
    x hx p hp
  let I := RawTupleIndex (switchingLabels Bwin) a
  let rawDecidableEq : DecidableEq I := inferInstance
  classical
  letI : DecidableEq I := Classical.decEq _
  have hp' : (∀ j, p j ∈ switchingPairs G S S₀ q) ∧
      PairEndpointsDistinct p ∧
      ∀ i, rho * delta * S₀.card ≤
        ((switchingPrivateNeighbors G p i S₀).card : ℝ) :=
    mem_richSwitchingTupleClass.mp hp
  have hpS : ∀ j, p j ∈ S ×ˢ S := by
    intro j
    have hj := (mem_switchingPairs_iff G S S₀ q
      (p j).1 (p j).2).mp (hp'.1 j)
    exact Finset.mem_product.mpr ⟨hj.1, hj.2.1⟩
  have hblock : ∀ i, etaPrivate * n ≤
      ((switchingPrivateNeighbors G p i S₀).card : ℝ) := by
    intro i
    calc
      etaPrivate * n = (rho * delta) * (base * n) := by
        dsimp only [etaPrivate]
        ring
      _ ≤ (rho * delta) * S₀.card := by
        exact mul_le_mul_of_nonneg_left hS₀
          (mul_nonneg hrho.le hdelta.le)
      _ ≤ _ := hp'.2.2 i
  have hblock' : ∀ i, etaPrivate * n ≤
      ((@switchingPrivateNeighbors (Fin n) inferInstance inferInstance
        I inferInstance rawDecidableEq G p i S₀).card : ℝ) := by
    intro i
    have hdec : (Classical.decEq I) = rawDecidableEq := Subsingleton.elim _ _
    rw [← hdec]
    exact hblock i
  dsimp only [etaPrivate]
  apply hstate n hn G hG a hsd S S₀ p Dcommon
  · exact hcommon
  · exact hID
  · exact hpS
  · exact hS₀
  · exact hdegree
  · exact hp'.1
  · exact hp'.2.1
  · exact hblock'
  · exact hx

/-- Convert the edge-polynomial centering used by the fixed-tuple estimate to
the quarter-edge-count centering used in the raw switching moment. -/
lemma rawTuple_stateLower_of_edgeCountCenter
    {n B d q : ℕ} (A delta base rho kappa : ℝ)
    (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
    (a : ℤ → ℕ)
    (hstate :
      (∀ v ∈ S, ∀ w ∈ S,
          |(FiniteES.vertexDegree G v : ℝ) / 2 -
            (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤
            A * (n : ℝ) ^ (3 / 2 : ℝ) →
        ∀ p ∈ richSwitchingTupleClass
            (I := RawTupleIndex (switchingLabels B) a)
            (switchingPairs G S S₀ q) G S₀
            (rho * delta * S₀.card),
          let etaPrivate := rho * delta * base
          let CPrivate :=
            canonicalPrivateQuadraticConstant etaPrivate B d
          (1 / 2 * canonicalFirstExposureRate d * kappa) *
              ((2 : ℝ) ^ n *
                (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^
                  Fintype.card (RawTupleIndex (switchingLabels B) a) *
                (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
            ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
              p ∈ switchingTupleFinset (switchingPairs G S S₀ q)
                  (edgeScore G) (switchingLabels B) a U ∧
                |edgeScore G U - x| ≤ (B : ℤ)).card : ℝ)))
    (hdegree : ∀ v ∈ S, ∀ w ∈ S,
      |(FiniteES.vertexDegree G v : ℝ) / 2 + ((0 : ℤ) : ℝ) -
        ((FiniteES.vertexDegree G w : ℝ) / 2 + ((0 : ℤ) : ℝ))| ≤
          Real.sqrt n)
    (x : ℕ)
    (hx : |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
      A * (n : ℝ) ^ (3 / 2 : ℝ)) :
    ∀ p ∈ richSwitchingTupleClass
        (I := RawTupleIndex (switchingLabels B) a)
        (switchingPairs G S S₀ q) G S₀
        (rho * delta * S₀.card),
      let etaPrivate := rho * delta * base
      let CPrivate := canonicalPrivateQuadraticConstant etaPrivate B d
      let c₀ := 1 / 2 * canonicalFirstExposureRate d * kappa
      let z := Real.exp (-8 * CPrivate) / 8
      c₀ * ((2 : ℝ) ^ n *
          (z / Real.sqrt n) ^
            Fintype.card (RawTupleIndex (switchingLabels B) a) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset (switchingPairs G S S₀ q)
              (edgeScore G) (switchingLabels B) a U ∧
            |edgeScore G U - (x : ℤ)| ≤ (B : ℤ)).card : ℝ)) := by
  have hdegree' : ∀ v ∈ S, ∀ w ∈ S,
      |(FiniteES.vertexDegree G v : ℝ) / 2 -
        (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n := by
    intro v hv w hw
    simpa only [Int.cast_zero, add_zero] using hdegree v hv w hw
  have hx' : |(((x : ℕ) : ℤ) : ℝ) -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G)| ≤
      A * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Probability.expectation_edgePolynomial (G := G)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    norm_num
    exact hx
  intro p hp
  simpa only [div_div] using
    hstate hdegree' (x : ℤ) hx' p hp

/-- Pointwise tuple/state bounds assembled uniformly over an abstract label
set.  This prevents repeated unfolding of the raw sigma index. -/
lemma rawMomentExpectation_lower_of_tupleFamily
    {n d : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n × Fin n)) (labels : Finset ℤ)
    (degree : (ℤ → ℕ) → ℕ) (admissible : (ℤ → ℕ) → Prop)
    (tuples : ∀ a : ℤ → ℕ,
      Finset (RawTupleIndex labels a → Fin n × Fin n))
    (c z : ℝ) (hn : 1 ≤ n)
    (hdegree : ∀ a, admissible a →
      degree a = Fintype.card (RawTupleIndex labels a))
    (hsd : ∀ a, admissible a →
      Fintype.card (RawTupleIndex labels a) ≤ d)
    (hgood : ∀ a, admissible a →
      T.card ^ Fintype.card (RawTupleIndex labels a) ≤
        2 * (tuples a).card)
    (window : Finset (Fin n) → Prop)
    (hstates : ∀ a, admissible a → ∀ p ∈ tuples a,
      c * ((2 : ℝ) ^ n *
          (z / Real.sqrt n) ^ Fintype.card (RawTupleIndex labels a) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ((((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            window U).card : ℝ)))
    (hc : 0 ≤ c) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∀ a, admissible a →
      (c / 2 * z ^ d) * ((T.card : ℝ) / Real.sqrt n) ^ degree a /
          (n : ℝ) ^ (3 / 2 : ℝ) ≤
        rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
          window
          (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
          a labels := by
  intro a ha
  rw [hdegree a ha]
  exact rawMomentExpectation_lower_of_tupleClass
    (n := n) (d := d) hn window T G labels a (tuples a) c z
    hc hz0 hz1 (hsd a ha) (hgood a ha) (hstates a ha)

/-- The lower half of KSSS Lemma 13.4 follows from the bounded-window
input, Lemma 13.1, and the finite switching-tuple argument. -/
theorem ksssUnbiasedSwitchingLowerMoments_of_boundedWindow
    (hBW : KSSSBoundedWindow) : KSSSUnbiasedSwitchingLowerMoments := by
  intro C A hC hA
  obtain ⟨B, hB, _hupperData, hlowerData⟩ :=
    hBW (2 * C) (mul_pos (by norm_num) hC)
  let d := 4 * B + 2
  let D := 2 * d
  have hD : 0 < D := by dsimp only [D, d]; omega
  obtain ⟨rho, delta, hrho, hrho1, hdelta, hdeltaBound,
      Nrich, hrichData⟩ :=
    ksssLemma131 C 1 hC (by norm_num) D hD
  have hdeltaRho : delta ≤ rho :=
    delta_le_rho_of_lemma131_bound hrho hrho1 hdeltaBound
  let base := delta ^ (1 / rho)
  let etaPrivate := rho * delta * base
  have hbase : 0 < base := by dsimp only [base]; positivity
  have hetaPrivate : 0 < etaPrivate := by
    dsimp only [etaPrivate]
    positivity
  obtain ⟨kappa, hkappa, Nstate, hstateData⟩ :=
    exists_uniform_richTupleClass_state_lower_of_data
      C B hlowerData delta base rho A d
      hC hdelta hbase hrho hA
  obtain ⟨Npair, hpairData⟩ := Filter.eventually_atTop.1
    eventually_switchingPairs_large_from_lemma131_sizes
  obtain ⟨Nsmall, hsmallData⟩ := Filter.eventually_atTop.1
    (eventually_switchingTuple_good_smallness D)
  let CPrivate := canonicalPrivateQuadraticConstant etaPrivate B d
  let c₀ := 1 / 2 * canonicalFirstExposureRate d * kappa
  let z := Real.exp (-8 * CPrivate) / 8
  let lower := c₀ / 2 * z ^ d
  have hCPrivate : 0 < CPrivate := by
    dsimp only [CPrivate]
    exact canonicalPrivateQuadraticConstant_pos hetaPrivate B d
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact mul_pos (mul_pos (by norm_num) (canonicalFirstExposureRate_pos d))
      hkappa
  have hz : 0 < z := by dsimp only [z]; positivity
  have hz1 : z ≤ 1 := by
    have hexp : Real.exp (-8 * CPrivate) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp only [z]
    linarith [Real.exp_pos (-8 * CPrivate)]
  have hlower : 0 < lower := by dsimp only [lower]; positivity
  refine ⟨B, lower, hlower,
    max 1 (max Nrich (max Nstate (max Npair Nsmall))), ?_⟩
  intro n G hn hG x hx
  have hnRich : Nrich ≤ n := by omega
  have hnState : Nstate ≤ n := by omega
  have hnPair : Npair ≤ n := by omega
  have hnSmall : Nsmall ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S, S₀, hSS₀, hS, hS₀, hrich, hcommon, hdegree⟩ :=
    hrichData n hnRich G hG (fun _ ↦ 0) (by
      intro v
      constructor
      · norm_num
      · norm_num)
  let q := switchingThreshold rho S₀
  let T := switchingPairs G S S₀ q
  have hTlarge : (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
      (T.card : ℝ) := by
    simpa only [T, q] using
      hpairData n hnPair G S S₀ delta rho hSS₀ hS hrich
        hrho hrho1.le hdeltaRho
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hSp : 0 < (S.card : ℝ) := by
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hS
  have hTp : 0 < (T.card : ℝ) := by
    have hleft : 0 < (S.card : ℝ) *
        (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by positivity
    exact hleft.trans_le hTlarge
  have hS₀n : (S₀.card : ℝ) ≤ n := by
    exact_mod_cast (show S₀.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S₀))
  have hbudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
      (⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℝ) := by
    calc
      (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
          (n : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hS₀n (by norm_num)
      _ ≤ (⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℝ) := by
        exact_mod_cast Nat.le_ceil _
  refine ⟨T, ?_, ?_, ?_⟩
  · exact switchingPairs_isSymmetric G S S₀ q
  · exact div_pos hTp (Real.sqrt_pos.2 hnpos)
  · dsimp only [lower]
    exact rawMomentExpectation_lower_of_tupleFamily
      (d := d) G T (switchingLabels B)
      (fun a ↦ ∑ i ∈ switchingLabels B, a i)
      (fun a ↦ ∀ i ∈ switchingLabels B, a i ≤ 2)
      (fun a ↦ richSwitchingTupleClass
        (I := RawTupleIndex (switchingLabels B) a)
        T G S₀ (rho * delta * S₀.card))
      c₀ z hn1
      (by
        intro a _ha
        simpa only [Nat.card_eq_fintype_card] using
          (card_rawTupleIndex (switchingLabels B) a).symm)
      (by
        intro a ha
        dsimp only [d]
        simpa only [Nat.card_eq_fintype_card] using
          switchingTuple_dimension_le a ha)
      (by
        intro a ha
        have hsd : Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ d := by
          dsimp only [d]
          simpa only [Nat.card_eq_fintype_card] using
            switchingTuple_dimension_le a ha
        have hID : 2 * Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ D := by
          dsimp only [D]
          omega
        simpa only [T] using
          rawTuple_richSwitchingTupleClass_half_of_smallness
            (B := B) (D := D) G S S₀ delta rho a
            (⟨⟨0, hn1⟩, ⟨0, hn1⟩⟩ : Fin n × Fin n)
            hrich hSS₀ hrho.le hcommon hID hbudget
            (by simpa only [T] using hTlarge)
            (fun s SCard TCard ↦ hsmallData n hnSmall s SCard TCard))
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (by
        intro a ha
        have hsd : Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ d := by
          dsimp only [d]
          simpa only [Nat.card_eq_fintype_card] using
            switchingTuple_dimension_le a ha
        have hID : 2 * Fintype.card
            (RawTupleIndex (switchingLabels B) a) ≤ D := by
          dsimp only [D]
          omega
        have hstateCore := hstateData n hnState G hG a hsd
          S S₀ q D hcommon hID (by simpa only [base] using hS₀)
        simpa only [c₀, z, CPrivate, etaPrivate, T] using
          rawTuple_stateLower_of_edgeCountCenter
            (B := B) (d := d) (q := q)
            A delta base rho kappa G S S₀ a
            hstateCore hdegree x hx)
      hc₀.le hz.le hz1

end Erdos88.Switching
