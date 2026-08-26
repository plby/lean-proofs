import ErdosProblems.Erdos489.FullCliqueCharging
import ErdosProblems.Erdos489.OccurrenceRayCapacity
import ErdosProblems.Erdos489.DisjointGapInjection
import ErdosProblems.Erdos489.CoprimePairSupply

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

noncomputable def rankPairPreimage
    (S : Finset ℕ) (rank : ℕ → ℕ) (z : ℕ × ℕ) : ℕ × ℕ := by
  classical
  let P := coprimeOrderedPairs S
  let f : ℕ × ℕ → ℕ × ℕ := fun w => (rank w.1, rank w.2)
  exact if h : z ∈ P.image f then Classical.choose (Finset.mem_image.mp h) else (0, 0)

theorem rankPairPreimage_spec
    (S : Finset ℕ) (rank : ℕ → ℕ) (z : ℕ × ℕ)
    (hz : z ∈ (coprimeOrderedPairs S).image
      (fun w => (rank w.1, rank w.2))) :
    rankPairPreimage S rank z ∈ coprimeOrderedPairs S ∧
      (rank (rankPairPreimage S rank z).1,
        rank (rankPairPreimage S rank z).2) = z := by
  classical
  unfold rankPairPreimage
  rw [dif_pos hz]
  exact Classical.choose_spec (Finset.mem_image.mp hz)

/-- Global actual-prefix charging architecture. Each gap pays its square with
coprime position pairs. Fixed rank pairs are then bounded by primitive-ray
capacity across disjoint successive gaps. -/
theorem global_gap_charge_le_rankKernel
    (I : Finset ℕ) (bseq gap : ℕ → ℕ) (T : ℕ → Finset ℕ)
    (rank a : ℕ → ℕ) (C X N : ℕ)
    (hC : 0 < C) (hX : 0 < X) (hb : StrictMono bseq)
    (hgap : ∀ i ∈ I, bseq (i + 1) = bseq i + gap i)
    (hint : ∀ i ∈ I, ∀ n ∈ T i,
      bseq i < n ∧ n < bseq (i + 1))
    (hrankinj : ∀ i ∈ I, Set.InjOn rank (T i : Set ℕ))
    (ha : ∀ r, 0 < a r)
    (hdiv : ∀ i ∈ I, ∀ n ∈ T i, a (rank n) ∣ n)
    (hcoordX : ∀ i ∈ I, ∀ n ∈ T i, n ≤ X)
    (hhigh : ∀ i ∈ I, ∀ n ∈ T i, gap i / C ≤ rank n)
    (hN : ∀ i ∈ I, N ≤ gap i / C)
    (hpay : ∀ i ∈ I,
      (gap i) ^ 2 ≤ 16 * C ^ 2 * (coprimeOrderedPairs (T i)).card) :
    ∃ J : Finset (ℕ × ℕ),
      ((∑ i ∈ I, (gap i) ^ 2 : ℕ) : ℝ) ≤
        ((16 * C ^ 2 : ℕ) : ℝ) *
          (4 * (X : ℝ) * (C : ℝ) *
              (∑ z ∈ J, rankPairKernel a z) + 2 * (J.card : ℝ)) ∧
      (∀ z ∈ J, N ≤ z.1 ∧ N ≤ z.2) ∧
      (∀ z ∈ J, a z.1 ≤ X ∧ a z.2 ≤ X) := by
  classical
  let pairRanks : ℕ → Finset (ℕ × ℕ) := fun i =>
    (coprimeOrderedPairs (T i)).image
      (fun w => (rank w.1, rank w.2))
  let J : Finset (ℕ × ℕ) := I.biUnion pairRanks
  let R : ℕ → ℕ × ℕ → Prop := fun i z => z ∈ pairRanks i
  let cap : ℕ × ℕ → ℕ := fun z => (I.filter fun i => R i z).card
  have hpairInj : ∀ i ∈ I,
      Set.InjOn (fun w : ℕ × ℕ => (rank w.1, rank w.2))
        (coprimeOrderedPairs (T i) : Set (ℕ × ℕ)) := by
    intro i hi w hw v hv heq
    have hwmem := Finset.mem_filter.mp hw
    have hvmem := Finset.mem_filter.mp hv
    have hwT := Finset.mem_offDiag.mp hwmem.1
    have hvT := Finset.mem_offDiag.mp hvmem.1
    apply Prod.ext
    · exact hrankinj i hi hwT.1 hvT.1 (congrArg Prod.fst heq)
    · exact hrankinj i hi hwT.2.1 hvT.2.1 (congrArg Prod.snd heq)
  have hpairCard : ∀ i ∈ I,
      (pairRanks i).card = (coprimeOrderedPairs (T i)).card := by
    intro i hi
    exact Finset.card_image_iff.mpr (hpairInj i hi)
  have hpairSub : ∀ i ∈ I, pairRanks i ⊆ J := by
    intro i hi z hz
    exact Finset.mem_biUnion.mpr ⟨i, hi, hz⟩
  have hw : ∀ i ∈ I,
      (gap i) ^ 2 ≤ 16 * C ^ 2 * (J.filter (R i)).card := by
    intro i hi
    have hfilter : J.filter (R i) = pairRanks i := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · exact fun hz => hz.2
      · intro hz
        exact ⟨hpairSub i hi hz, hz⟩
    rw [hfilter, hpairCard i hi]
    exact hpay i hi
  have hocc : ∀ z ∈ J,
      (I.filter fun i => R i z).card ≤ cap z := by
    intro z hz
    exact le_rfl
  have hcap : ∀ z ∈ J,
      a z.1 * a z.2 * cap z ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) := by
    intro z hz
    let Iz := I.filter fun i => R i z
    let w : ℕ → ℕ × ℕ := fun i => rankPairPreimage (T i) rank z
    let u : ℕ → ℕ := fun i => (w i).1
    let v : ℕ → ℕ := fun i => (w i).2
    have hiI : ∀ i ∈ Iz, i ∈ I := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    have hiR : ∀ i ∈ Iz, R i z := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hspec : ∀ i ∈ Iz,
        w i ∈ coprimeOrderedPairs (T i) ∧
          (rank (u i), rank (v i)) = z := by
      intro i hi
      exact rankPairPreimage_spec (T i) rank z (hiR i hi)
    have huT : ∀ i ∈ Iz, u i ∈ T i := by
      intro i hi
      exact (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).1
    have hvT : ∀ i ∈ Iz, v i ∈ T i := by
      intro i hi
      exact (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).2.1
    have hru : ∀ i ∈ Iz, rank (u i) = z.1 := by
      intro i hi
      exact congrArg Prod.fst (hspec i hi).2
    have hrv : ∀ i ∈ Iz, rank (v i) = z.2 := by
      intro i hi
      exact congrArg Prod.snd (hspec i hi).2
    have hdistGap : ∀ i ∈ Iz, Nat.dist (u i) (v i) ≤ gap i := by
      intro i hi
      have hi' := hiI i hi
      have huInt := hint i hi' (u i) (huT i hi)
      have hvInt := hint i hi' (v i) (hvT i hi)
      have hg := hgap i hi'
      rcases le_total (u i) (v i) with huv | hvu
      · rw [Nat.dist_eq_sub_of_le huv]
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hvu]
        omega
    have hgapD : ∀ i ∈ Iz,
        gap i ≤ C * min (z.1 + 1) (z.2 + 1) := by
      intro i hi
      have hi' := hiI i hi
      have hglt : gap i < C * (gap i / C + 1) := Nat.lt_mul_div_succ _ hC
      have hgu := hhigh i hi' (u i) (huT i hi)
      have hgv := hhigh i hi' (v i) (hvT i hi)
      rw [hru i hi] at hgu
      rw [hrv i hi] at hgv
      have hm : gap i / C + 1 ≤ min (z.1 + 1) (z.2 + 1) := by
        exact le_min (by omega) (by omega)
      exact (Nat.le_of_lt hglt).trans (Nat.mul_le_mul_left C hm)
    have haduIz : ∀ i ∈ Iz, a z.1 ∣ u i := by
      intro i hi
      have hd := hdiv i (hiI i hi) (u i) (huT i hi)
      simpa [hru i hi] using hd
    have hbdvIz : ∀ i ∈ Iz, a z.2 ∣ v i := by
      intro i hi
      have hd := hdiv i (hiI i hi) (v i) (hvT i hi)
      simpa [hrv i hi] using hd
    have hquotInj := quotient_pair_injOn_of_successive_intervals Iz
      bseq u v (a z.1) (a z.2) hb
      (fun i hi => hint i (hiI i hi) (u i) (huT i hi)) haduIz
    have hfixed := fixed_modulus_occurrence_capacity Iz u v
      (a z.1) (a z.2) X (C * min (z.1 + 1) (z.2 + 1))
      (ha z.1) (ha z.2) hX (Nat.mul_pos hC (by positivity))
      (fun i hi => lt_of_le_of_lt (Nat.zero_le _) (hint i (hiI i hi) (u i) (huT i hi)).1)
      (fun i hi => lt_of_le_of_lt (Nat.zero_le _) (hint i (hiI i hi) (v i) (hvT i hi)).1)
      haduIz hbdvIz
      (fun i hi => (Finset.mem_filter.mp (hspec i hi).1).2)
      (fun i hi => hcoordX i (hiI i hi) (u i) (huT i hi))
      (fun i hi => hcoordX i (hiI i hi) (v i) (hvT i hi))
      (fun i hi => (Finset.mem_offDiag.mp
        (Finset.mem_filter.mp (hspec i hi).1).1).2.2)
      (fun i hi => (hdistGap i hi).trans (hgapD i hi)) hquotInj
    have hfixed' : a z.1 * a z.2 * Iz.card ≤
        4 * X * C * min (z.1 + 1) (z.2 + 1) +
          2 * (a z.1 * a z.2) := by
      calc
        a z.1 * a z.2 * Iz.card ≤
            4 * X * (C * min (z.1 + 1) (z.2 + 1)) +
              2 * (a z.1 * a z.2) := hfixed
        _ = 4 * X * C * min (z.1 + 1) (z.2 + 1) +
              2 * (a z.1 * a z.2) := by ring
    simpa [cap, Iz] using hfixed'
  have hglobal := full_clique_charge_le_rankKernel I J gap cap R a
    (16 * C ^ 2) C X hw hocc ha hcap
  refine ⟨J, hglobal, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hzi⟩
    rcases Finset.mem_image.mp hzi with ⟨w, hw, rfl⟩
    have hwT := Finset.mem_offDiag.mp (Finset.mem_filter.mp hw).1
    exact ⟨(hN i hi).trans (hhigh i hi w.1 hwT.1),
      (hN i hi).trans (hhigh i hi w.2 hwT.2.1)⟩
  · intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, hi, hzi⟩
    rcases Finset.mem_image.mp hzi with ⟨w, hw, rfl⟩
    have hwT := Finset.mem_offDiag.mp (Finset.mem_filter.mp hw).1
    constructor
    · exact (Nat.le_of_dvd (by
        have := (hint i hi w.1 hwT.1).1
        omega) (hdiv i hi w.1 hwT.1)).trans (hcoordX i hi w.1 hwT.1)
    · exact (Nat.le_of_dvd (by
        have := (hint i hi w.2 hwT.2.1).1
        omega) (hdiv i hi w.2 hwT.2.1)).trans (hcoordX i hi w.2 hwT.2.1)

end Erdos489
