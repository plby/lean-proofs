import ErdosProblems.Erdos344.IntervalBridges
import ErdosProblems.Erdos1211.Erdos1211RoughShell
import ErdosProblems.Erdos1211.Erdos1211Theta

/-!
# A long monochromatic subset-sum interval in every dyadic shell

This file proves the finite input used in the lower-bound half of Erdős
Problem 1211.  It is a two-colour specialization of the local interval lemma
of Conlon--Fox--Pham.  The proof uses the fixed rough shell developed in
`Erdos1211RoughShell`, the modular-phase machinery in `Erdos344`, and
the interval-valued sum-tree bridge in `Erdos344.IntervalBridges`.
-/

namespace Erdos1211Local

open BigOperators Finset Set
open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PT

open Erdos344

/-- An exact equipartition of a finite set into `2^t` leaves of size `r`. -/
lemma exists_exact_tree {t r : ℕ} {S : Finset ℕ}
    (hcard : S.card = 2 ^ t * r) :
    ∃ T : PartitionTree ℕ t,
      T.carrier = S ∧ T.PairwiseDisjoint ∧
        T.AllLeaves (fun C ↦ C.card = r) := by
  induction t generalizing S with
  | zero =>
      refine ⟨PartitionTree.leaf S, rfl, trivial, ?_⟩
      change S.card = r
      simpa using hcard
  | succ t ih =>
      have hpow : 2 ^ (t + 1) * r = 2 * (2 ^ t * r) := by
        rw [pow_succ]
        ring
      have hhalf : 2 ^ t * r ≤ S.card := by
        rw [hcard, hpow]
        omega
      obtain ⟨L, hLS, hLcard⟩ := Finset.exists_subset_card_eq hhalf
      let R := S \ L
      have hRcard : R.card = 2 ^ t * r := by
        dsimp only [R]
        rw [Finset.card_sdiff_of_subset hLS, hcard, hpow, hLcard]
        omega
      obtain ⟨TL, hTLcarrier, hTLdisj, hTLleaves⟩ := ih hLcard
      obtain ⟨TR, hTRcarrier, hTRdisj, hTRleaves⟩ := ih hRcard
      refine ⟨PartitionTree.node TL TR, ?_, ?_, hTLleaves, hTRleaves⟩
      · simp only [PartitionTree.carrier, hTLcarrier, hTRcarrier, R]
        exact Finset.union_sdiff_of_subset hLS
      · refine ⟨hTLdisj, hTRdisj, ?_⟩
        simpa only [hTLcarrier, hTRcarrier, R] using
          (Finset.disjoint_sdiff : Disjoint L (S \ L))

lemma allLeaves_and {t : ℕ} {T : PartitionTree ℕ t}
    {P Q : Finset ℕ → Prop} (hP : T.AllLeaves P) (hQ : T.AllLeaves Q) :
    T.AllLeaves fun S ↦ P S ∧ Q S := by
  induction T with
  | leaf S => exact ⟨hP, hQ⟩
  | node left right ihl ihr =>
      exact ⟨ihl hP.1 hQ.1, ihr hP.2 hQ.2⟩

lemma allLeafPairs_mono {t : ℕ} {A B : PartitionTree ℕ t}
    {P Q : Finset ℕ → Finset ℕ → Prop}
    (hP : PartitionTree.AllLeafPairs P A B)
    (hPQ : ∀ C D, P C D → Q C D) :
    PartitionTree.AllLeafPairs Q A B := by
  induction A with
  | leaf C =>
      cases B with
      | leaf D => exact hPQ C D hP
  | node A₁ A₂ ih₁ ih₂ =>
      cases B with
      | node B₁ B₂ => exact ⟨ih₁ hP.1, ih₂ hP.2⟩

end PT

namespace Pivot

open Erdos344

noncomputable def natAddTranslate (b : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x ↦ x + b

lemma card_union_natAddTranslate (b : ℕ) (S : Finset ℕ) :
    (S ∪ natAddTranslate b S).card =
      S.card + (natAddTranslate b S \ S).card := by
  have h := Finset.card_sdiff_add_card (natAddTranslate b S) S
  rw [Finset.union_comm] at h
  omega

/-- Adjoining the modulus creates a new sum in each occupied residue class. -/
lemma card_add_modulus_growth {b : ℕ} [NeZero b] (hb : 0 < b)
    (S : Finset ℕ) :
    S.card + (S.image fun x : ℕ ↦ (x : ZMod b)).card ≤
      (S ∪ natAddTranslate b S).card := by
  classical
  let R : Finset (ZMod b) := S.image fun x : ℕ ↦ (x : ZMod b)
  let fiber : R → Finset ℕ := fun r ↦
    Finset.filter (fun x : ℕ ↦ (x : ZMod b) = r.1) S
  have hfiber (r : R) : (fiber r).Nonempty := by
    obtain ⟨x, hxS, hxr⟩ := Finset.mem_image.mp r.2
    refine ⟨x, Finset.mem_filter.mpr ⟨hxS, ?_⟩⟩
    exact hxr
  let pick (r : R) := (fiber r).max' (hfiber r)
  let f : R → ℕ := fun r ↦ pick r + b
  have hmaps : ∀ r ∈ R.attach, f r ∈ natAddTranslate b S \ S := by
    intro r hr
    have hpickFiber : pick r ∈ fiber r := (fiber r).max'_mem (hfiber r)
    have hpickS : pick r ∈ S := (Finset.mem_filter.mp hpickFiber).1
    have hpickCast : (pick r : ZMod b) = r.1 :=
      (Finset.mem_filter.mp hpickFiber).2
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_image.mpr ⟨pick r, hpickS, rfl⟩
    · intro hnewS
      have hcast : ((pick r + b : ℕ) : ZMod b) = r.1 := by
        push_cast
        simpa using hpickCast
      have hnewFiber : pick r + b ∈ fiber r :=
        Finset.mem_filter.mpr ⟨hnewS, hcast⟩
      have hle := (fiber r).le_max' (pick r + b) hnewFiber
      dsimp only [pick] at hle
      omega
  have hinj : Set.InjOn f R.attach := by
    intro r hr q hq heq
    apply Subtype.ext
    have hpickEq : pick r = pick q := by
      dsimp only [f] at heq
      omega
    have hrmem := (Finset.mem_filter.mp ((fiber r).max'_mem (hfiber r))).2
    have hqmem := (Finset.mem_filter.mp ((fiber q).max'_mem (hfiber q))).2
    change (pick r : ZMod b) = r.1 at hrmem
    change (pick q : ZMod b) = q.1 at hqmem
    change r.1 = q.1
    rw [← hrmem, ← hqmem, hpickEq]
  have hnew : R.card ≤ (natAddTranslate b S \ S).card := by
    rw [← Finset.card_attach]
    exact Finset.card_le_card_of_injOn f hmaps hinj
  rw [card_union_natAddTranslate]
  exact Nat.add_le_add_left hnew S.card

lemma subsetSum_insert_eq (P : Finset ℕ) (b : ℕ) (hbP : b ∉ P) :
    (insert b P).subsetSum =
      P.subsetSum ∪ natAddTranslate b P.subsetSum := by
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hQ, hQsum⟩ := Finset.mem_subsetSum_iff.mp hx
    rw [Finset.mem_union]
    by_cases hbQ : b ∈ Q
    · right
      rw [natAddTranslate, Finset.mem_image]
      refine ⟨∑ q ∈ Q.erase b, q, ?_, ?_⟩
      · apply Finset.mem_subsetSum_iff.mpr
        refine ⟨Q.erase b, fun q hq ↦ ?_, rfl⟩
        exact (Finset.mem_insert.mp (hQ (Finset.mem_of_mem_erase hq))).resolve_left
          (fun h ↦ (Finset.mem_erase.mp hq).1 h)
      · have hsum := Finset.sum_erase_add Q id hbQ
        simp only [id_eq] at hsum
        omega
    · left
      apply Finset.mem_subsetSum_iff.mpr
      exact ⟨Q, fun q hq ↦
        (Finset.mem_insert.mp (hQ hq)).resolve_left (fun h ↦ hbQ (h ▸ hq)), hQsum⟩
  · intro hx
    rw [Finset.mem_union] at hx
    apply Finset.mem_subsetSum_iff.mpr
    rcases hx with hx | hx
    · obtain ⟨Q, hQP, hQsum⟩ := Finset.mem_subsetSum_iff.mp hx
      exact ⟨Q, hQP.trans (Finset.subset_insert b P), hQsum⟩
    · rw [natAddTranslate, Finset.mem_image] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨Q, hQP, hQsum⟩ := Finset.mem_subsetSum_iff.mp hu
      have hbQ : b ∉ Q := fun hbQ ↦ hbP (hQP hbQ)
      refine ⟨insert b Q, Finset.insert_subset_insert b hQP, ?_⟩
      rw [Finset.sum_insert hbQ]
      omega

lemma pivotExtended_empty (S : Finset ℕ) : Erdos344.pivotExtended S ∅ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, z, hz, hsum⟩ := Finset.mem_add.mp hx
    obtain ⟨Q, hQ, hQsum⟩ := Finset.mem_subsetSum_iff.mp hz
    have hQempty : Q = ∅ := Finset.subset_empty.mp hQ
    have hz0 : z = 0 := by
      rw [hQempty] at hQsum
      simpa using hQsum.symm
    have hsx : s = x := by omega
    simpa [← hsx] using hs
  · intro hx
    exact Finset.add_mem_add hx Finset.zero_mem_subsetSum

lemma pivotExtended_insert (S P : Finset ℕ) (b : ℕ) (hbP : b ∉ P) :
    Erdos344.pivotExtended S (insert b P) =
      Erdos344.pivotExtended S P ∪
        natAddTranslate b (Erdos344.pivotExtended S P) := by
  rw [Erdos344.pivotExtended, subsetSum_insert_eq P b hbP, Finset.add_union]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, u, hu, hsu⟩ := Finset.mem_add.mp hx
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hu
    apply Finset.mem_image.mpr
    refine ⟨s + v, Finset.mem_add.mpr ⟨s, hs, v, hv, rfl⟩, ?_⟩
    omega
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨s, hs, v, hv, hsv⟩ := Finset.mem_add.mp hy
    apply Finset.mem_add.mpr
    refine ⟨s, hs, v + b, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    omega

/-- Repeatedly adjoining pivots adds at least their quarter-moduli. -/
lemma card_pivotExtended_lower
    (S P : Finset ℕ) (hPpos : ∀ b ∈ P, 0 < b)
    (hcover : ∀ b ∈ P,
      b ≤ 4 * (S.image fun x : ℕ ↦ (x : ZMod b)).card) :
    S.card + ∑ b ∈ P, b / 4 ≤ (Erdos344.pivotExtended S P).card := by
  classical
  induction P using Finset.induction with
  | empty => simp [pivotExtended_empty]
  | @insert b P hbP ih =>
      have hb : 0 < b := hPpos b (Finset.mem_insert_self _ _)
      let : NeZero b := ⟨hb.ne'⟩
      have hIH := ih
        (fun a ha ↦ hPpos a (Finset.mem_insert_of_mem ha))
        (fun a ha ↦ hcover a (Finset.mem_insert_of_mem ha))
      let T := Erdos344.pivotExtended S P
      have hSsubT : S ⊆ T := Erdos344.subset_pivotExtended_left S P
      have hres : (S.image fun x : ℕ ↦ (x : ZMod b)).card ≤
          (T.image fun x : ℕ ↦ (x : ZMod b)).card := by
        exact Finset.card_le_card (Finset.image_subset_image hSsubT)
      have hquarter : b / 4 ≤
          (T.image fun x : ℕ ↦ (x : ZMod b)).card := by
        have := hcover b (Finset.mem_insert_self _ _)
        omega
      have hgrowth := card_add_modulus_growth hb T
      rw [pivotExtended_insert S P b hbP, Finset.sum_insert hbP]
      dsimp only [T] at hgrowth hquarter
      omega

end Pivot

namespace Leaf

open Erdos344

/-- The rough pool in one shell is diverse for every pivot from that shell. -/
lemma phaseDiverse_of_rough_pool
    {Q N r p : ℕ} [NeZero p] (hp : 0 < p)
    (hpN : N ≤ p) (hp2N : p < 2 * N)
    {C : Finset ℕ} (hC : C ⊆ Finset.Ico N (2 * N))
    (hCcard : C.card = r)
    (hrough : ∀ c ∈ C, Erdos344.RoughUpTo Q c)
    (hQr : 4 * N ≤ Q * r) (hQle : Q ≤ r) :
    PhaseDiverse hp (C.image fun c : ℕ ↦ (c : ZMod p)) := by
  let R₀ := C.image fun c : ℕ ↦ (c : ZMod p)
  have hinj : Set.InjOn (fun c : ℕ ↦ (c : ZMod p)) C := by
    apply natCast_zmod_injOn_of_subset_Ico_width (b := p) (N := N)
    intro c hc
    have hcI := Finset.mem_Ico.mp (hC hc)
    exact Finset.mem_Ico.mpr ⟨hcI.1, by omega⟩
  have hRcard : R₀.card = r := by
    dsimp only [R₀]
    rw [Finset.card_image_iff.mpr hinj, hCcard]
  apply phaseDiverse_of_bounded hp R₀
  intro d hd hddiv hmass
  have hdltQ : d < Q := by
    by_contra hnot
    have hQd : Q ≤ d := Nat.le_of_not_gt hnot
    have hbad : 4 * N ≤ 2 * p := by
      calc
        4 * N ≤ Q * r := hQr
        _ ≤ d * r := Nat.mul_le_mul_right r hQd
        _ = d * R₀.card := by rw [hRcard]
        _ ≤ 2 * p := hmass
    omega
  have hfilter : R₀.filter (fun x ↦ ¬d ∣ x.val) = R₀ := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    intro hdval
    have hdp : d ∣ p := hddiv
    have hdc : d ∣ c := by
      have hdmod : d ∣ c % p := by
        simpa [ZMod.val_natCast] using hdval
      rw [← Nat.mod_add_div c p]
      exact Nat.dvd_add hdmod (dvd_mul_of_dvd_left hdp _)
    obtain ⟨q, hqprime, hqd⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp (by omega : d ≠ 1)
    have hqQ : q ≤ Q := by
      have hqdle : q ≤ d := Nat.le_of_dvd (by omega) hqd
      omega
    exact hrough c hc q hqprime hqQ (hqd.trans hdc)
  rw [hfilter, hRcard]
  omega

/-- One seed element followed by at most `k` pool elements is a bounded sum
of the disjoint union, using at most `k+1` terms. -/
lemma add_seed_bounded_subset
    {D C : Finset ℕ} (hDC : Disjoint D C) (k : ℕ) :
    D + boundedSubsetSum C k ⊆ boundedSubsetSum (D ∪ C) (k + 1) := by
  intro x hx
  obtain ⟨d, hd, s, hs, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨H, hHC, hHcard, rfl⟩ := mem_boundedSubsetSum_iff.mp hs
  have hdH : d ∉ H := by
    intro hdH
    exact Finset.disjoint_left.mp hDC hd (hHC hdH)
  apply mem_boundedSubsetSum_iff.mpr
  refine ⟨insert d H, ?_, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_insert] at hy
    exact hy.elim (fun h ↦ h ▸ Finset.mem_union_left C hd)
      (fun h ↦ Finset.mem_union_right D (hHC h))
  · rw [Finset.card_insert_of_notMem hdH]
    omega
  · rw [Finset.sum_insert hdH]

/-- The modular phase engine gives quarter-coverage for the full leaf base. -/
lemma boundedSubsetSum_quarter_modulus
    {Q N r k p : ℕ} [NeZero p] (hp : 0 < p)
    (hpN : N ≤ p) (hp2N : p < 2 * N)
    {D C : Finset ℕ} (hDC : Disjoint D C)
    (hD : D ⊆ Finset.Ico N (2 * N))
    (hC : C ⊆ Finset.Ico N (2 * N))
    (hDcard : D.card = r) (hCcard : C.card = r)
    (hroughC : ∀ c ∈ C, Erdos344.RoughUpTo Q c)
    (hrpos : 0 < r) (hhalf : 2 * k ≤ r)
    (hQr : 4 * N ≤ Q * r) (hQle : Q ≤ r)
    (hmass : 4 * p ≤ k * (r - k)) :
    p ≤ 4 * ((boundedSubsetSum (D ∪ C) (k + 1)).image
      (fun u : ℕ ↦ (u : ZMod p))).card := by
  let R₀ := C.image fun c : ℕ ↦ (c : ZMod p)
  let E := D.image fun d : ℕ ↦ (d : ZMod p)
  have hinjC : Set.InjOn (fun c : ℕ ↦ (c : ZMod p)) C := by
    apply natCast_zmod_injOn_of_subset_Ico_width (b := p) (N := N)
    intro c hc
    have hcI := Finset.mem_Ico.mp (hC hc)
    exact Finset.mem_Ico.mpr ⟨hcI.1, by omega⟩
  have hinjD : Set.InjOn (fun d : ℕ ↦ (d : ZMod p)) D := by
    apply natCast_zmod_injOn_of_subset_Ico_width (b := p) (N := N)
    intro d hd
    have hdI := Finset.mem_Ico.mp (hD hd)
    exact Finset.mem_Ico.mpr ⟨hdI.1, by omega⟩
  have hRcard : R₀.card = r := by
    dsimp only [R₀]
    rw [Finset.card_image_iff.mpr hinjC, hCcard]
  have hEcard : E.card = r := by
    dsimp only [E]
    rw [Finset.card_image_iff.mpr hinjD, hDcard]
  have hE : E.Nonempty := by
    apply Finset.card_pos.mp
    rw [hEcard]
    exact hrpos
  have hdiverse : PhaseDiverse hp R₀ := by
    simpa only [R₀] using phaseDiverse_of_rough_pool hp hpN hp2N hC hCcard
      hroughC hQr hQle
  have hclosure : ∀ i < k,
      closureModulus hp (modularRemainder hp R₀ E hE hdiverse i) = 1 := by
    intro i hi
    let R := modularRemainder hp R₀ E hE hdiverse i
    have hiR : i ≤ R₀.card := by rw [hRcard]; omega
    have hRcard : R.card = r - i := by
      simpa only [R, hRcard] using
        card_modularRemainder hp R₀ E hE hdiverse hiR
    have hrle : r ≤ 2 * R.card := by
      rw [hRcard]
      omega
    have hlarge : p < (Q + 1) * R.card := by
      have htwo : 2 * N ≤ Q * R.card := by
        have : 4 * N ≤ 2 * (Q * R.card) := by
          calc
            4 * N ≤ Q * r := hQr
            _ ≤ Q * (2 * R.card) := Nat.mul_le_mul_left Q hrle
            _ = 2 * (Q * R.card) := by ring
        omega
      have hposR : 0 < R.card := by rw [hRcard]; omega
      calc
        p < 2 * N := hp2N
        _ ≤ Q * R.card := htwo
        _ < (Q + 1) * R.card := by nlinarith
    apply closureModulus_eq_one_of_rough_image hp
      (C := C) hroughC R
    · simpa only [R₀, R] using
        (modularRemainder_subset_initial hp R₀ E hE hdiverse i)
    · exact hlarge
  have hseed : R₀.card < 4 * E.card := by rw [hRcard, hEcard]; omega
  have hquarter := seededBoundedSubsetSum_quarter_modulus_of_full_closure_seed
    hp D C hinjC R₀ E rfl rfl hE hdiverse
    (by rw [hRcard]; exact hhalf) hclosure hseed (by rw [hRcard]; exact hmass)
  exact hquarter.trans (Nat.mul_le_mul_left 4 (Finset.card_le_card
    (Finset.image_subset_image (add_seed_bounded_subset hDC k))))

lemma boundedSubsetSum_le_shell {N s : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Ico N (2 * N)) {x : ℕ}
    (hx : x ∈ boundedSubsetSum C s) : x ≤ 2 * N * s := by
  obtain ⟨H, hHC, hHcard, rfl⟩ := mem_boundedSubsetSum_iff.mp hx
  calc
    ∑ h ∈ H, h ≤ ∑ _h ∈ H, 2 * N := by
      apply Finset.sum_le_sum
      intro h hh
      exact (Finset.mem_Ico.mp (hC (hHC hh))).2.le
    _ = H.card * (2 * N) := by simp [mul_comm]
    _ ≤ s * (2 * N) := Nat.mul_le_mul_right _ hHcard
    _ = 2 * N * s := by ring

/-- Uniform box bound for a pivot-extended leaf inside one shell. -/
lemma pivotExtended_subset_box {N L : ℕ} {C P : Finset ℕ}
    (hC : C ⊆ Finset.Ico N (2 * N))
    (hP : P ⊆ Finset.Ico N (2 * N)) (hPcard : P.card = L) :
    pivotExtended (boundedSubsetSum C L) P ⊆ Finset.Icc 0 (4 * L * N) := by
  intro x hx
  obtain ⟨s, hs, q, hq, rfl⟩ := Finset.mem_add.mp hx
  have hsle := boundedSubsetSum_le_shell hC hs
  obtain ⟨H, hHP, rfl⟩ := Finset.mem_subsetSum_iff.mp hq
  have hqle : ∑ h ∈ H, h ≤ 2 * N * L := by
    calc
      ∑ h ∈ H, h ≤ ∑ _h ∈ H, 2 * N := by
        apply Finset.sum_le_sum
        intro h hh
        exact (Finset.mem_Ico.mp (hP (hHP hh))).2.le
      _ = H.card * (2 * N) := by simp [mul_comm]
      _ ≤ P.card * (2 * N) := Nat.mul_le_mul_right _ (Finset.card_le_card hHP)
      _ = 2 * N * L := by rw [hPcard]; ring
  rw [Finset.mem_Icc]
  constructor
  · omega
  · nlinarith

/-- Cardinality supplied by `L` pivots, each at least `N`. -/
lemma pivotExtended_card_ge {N L : ℕ} {S P : Finset ℕ}
    (hP : P ⊆ Finset.Ico N (2 * N)) (hPcard : P.card = L)
    (hcover : ∀ p ∈ P,
      p ≤ 4 * (S.image fun x : ℕ ↦ (x : ZMod p)).card) :
    L * (N / 4) ≤ (pivotExtended S P).card := by
  have hpos : ∀ p ∈ P, 0 < p := by
    intro p hp
    have hpI := Finset.mem_Ico.mp (hP hp)
    omega
  have hcard := Pivot.card_pivotExtended_lower S P hpos hcover
  have hsum : L * (N / 4) ≤ ∑ p ∈ P, p / 4 := by
    calc
      L * (N / 4) = ∑ _p ∈ P, N / 4 := by simp [hPcard]
      _ ≤ ∑ p ∈ P, p / 4 := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.div_le_div_right ((Finset.mem_Ico.mp (hP hp)).1)
  omega

end Leaf

namespace Tree

open Erdos344

/-- The paired sum-tree wrapper, retaining the upper bound on the starting
point of the interval before the disjoint reserve is absorbed. -/
theorem paired_interval_with_start_bound
    {t k ell m : ℕ} (A B : PartitionTree ℕ t)
    (hell : 2 ≤ ell)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier)
    (hcard : PartitionTree.AllLeafPairs
      (fun C P ↦ ell ≤ (pivotExtended (boundedSubsetSum C k) P).card) A B)
    (hbox : PartitionTree.AllLeafPairs
      (fun C P ↦ pivotExtended (boundedSubsetSum C k) P ⊆ Finset.Icc 0 m) A B)
    (haper : PartitionTree.AllLeafPairs
      (fun C P ↦ ¬ Erdos360.ContainedInNontrivialAP
        (pivotExtended (boundedSubsetSum C k) P)) A B)
    (hexceed : 2 ^ t * m + 1 < SumTree.growthLower ell t) :
    ∃ a : ℕ, a ≤ 2 ^ t * m ∧
      Finset.Icc a (a + (2 * ell - 2)) ⊆
        (A.carrier ∪ B.carrier).subsetSum := by
  let T := PartitionTree.pairedPivotSumTree k A B
  have hzero : T.AllLeaves fun S ↦ 0 ∈ S := by
    rw [PartitionTree.allLeaves_pairedPivotSumTree_iff]
    apply PartitionTree.allLeafPairs_of_allLeaves
      (PartitionTree.allLeaves_true A) (PartitionTree.allLeaves_true B)
    intro C P _ _
    exact zero_mem_pivotExtended (zero_mem_boundedSubsetSum C k)
  have hcardT : T.AllLeaves fun S ↦ ell ≤ S.card := by
    rwa [PartitionTree.allLeaves_pairedPivotSumTree_iff]
  have hboxT : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m := by
    rwa [PartitionTree.allLeaves_pairedPivotSumTree_iff]
  have haperT : T.AllLeaves fun S ↦
      ¬ Erdos360.ContainedInNontrivialAP S := by
    rwa [PartitionTree.allLeaves_pairedPivotSumTree_iff]
  obtain ⟨a, ha⟩ := SumTree.containsInterval_of_growth_exceeds_diameter
    hell hzero hcardT haperT hboxT hexceed
  have haT : a ∈ T.carrier := ha (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have habox := Finset.mem_Icc.mp (SumTree.carrier_subset_Icc hboxT haT)
  refine ⟨a, habox.2, ha.trans ?_⟩
  exact PartitionTree.carrier_pairedPivotSumTree_subset_subsetSum
    A B hA hB hAB

lemma depthSeven_exceeds {N L : ℕ} (hN : 200 ≤ N) (hL : 0 < L) :
    2 ^ 7 * (4 * L * N) + 1 <
      Erdos344.SumTree.growthLower (L * (N / 4)) 7 := by
  have hK : 2 ≤ L * (N / 4) := by
    have hdiv : 50 ≤ N / 4 := by omega
    nlinarith
  have hgrowth := Erdos344.growthLower_ge_pow_mul hK 7
  have hround : N ≤ 4 * (N / 4) + 3 := by omega
  have hdiv : 50 ≤ N / 4 := by omega
  have hmul : L * N ≤ L * (4 * (N / 4) + 3) :=
    Nat.mul_le_mul_left L hround
  have hsub : L * (N / 4) - 2 + 2 = L * (N / 4) := by omega
  have htarget :
      512 * L * N + 1 < 2187 * (L * (N / 4) - 2) + 2 := by
    nlinarith
  calc
    2 ^ 7 * (4 * L * N) + 1 = 512 * L * N + 1 := by norm_num; ring
    _ < 2187 * (L * (N / 4) - 2) + 2 := htarget
    _ ≤ Erdos344.SumTree.growthLower (L * (N / 4)) 7 := by
      norm_num at hgrowth
      exact hgrowth

lemma shell_interval_long_enough {N L : ℕ} (hN : 200 ≤ N)
    (hL : 8 ≤ L) :
    2 * N ≤ 2 * (L * (N / 4)) - 1 := by
  have hround : N ≤ 4 * (N / 4) + 3 := by omega
  have hdiv : 50 ≤ N / 4 := by omega
  have hLmul : 8 * (N / 4) ≤ L * (N / 4) :=
    Nat.mul_le_mul_right (N / 4) hL
  omega

end Tree

/-! ### Fixed constants and shell bookkeeping -/

def depth : ℕ := 7
def leafCount : ℕ := 2 ^ depth

/-- A fixed roughness modulus with enough reduced residue classes.  It is
chosen noncomputably from the explicit primorial construction in
`Erdos1211Theta`; this keeps the kernel from trying to evaluate a primorial
with a four-billion-sized cutoff during unrelated arithmetic. -/
structure ShellData where
  q : ℕ
  m : ℕ
  ph : ℕ
  m_eq : m = RoughShellCount.roughModulus q
  ph_eq : ph = m.totient
  m_pos : 0 < m
  theta : 256 * 128 * m ≤ q * ph

lemma exists_shellData : Nonempty ShellData := by
  have htheta := ThetaBound.finite_theta_lower_bound
  have hconst : ThetaBound.C0 = 256 * 128 := by
    norm_num [ThetaBound.C0, ThetaBound.J]
  rw [hconst] at htheta
  exact ⟨{
    q := ThetaBound.cutoffQ
    m := RoughShellCount.roughModulus ThetaBound.cutoffQ
    ph := (RoughShellCount.roughModulus ThetaBound.cutoffQ).totient
    m_eq := rfl
    ph_eq := rfl
    m_pos := RoughShellCount.roughModulus_pos _
    theta := htheta }⟩

noncomputable def shellData : ShellData := Classical.choice exists_shellData

noncomputable def roughness : ℕ := shellData.q
noncomputable def modulus : ℕ := shellData.m
noncomputable def phi : ℕ := shellData.ph
def phaseCount : ℕ := 1024 * leafCount * modulus
def pivotCount : ℕ := phaseCount + 1
def baseHalf (N : ℕ) : ℕ := N * phi / (63 * modulus * leafCount)
def reserveCount (N : ℕ) : ℕ := N * phi / (16 * modulus)
def lowerEndpoint (N : ℕ) : ℕ := 512 * pivotCount * N
def upperEndpoint (N : ℕ) : ℕ := N * reserveCount N

lemma leafCount_eq : leafCount = 128 := by norm_num [leafCount, depth]

lemma modulus_eq : modulus = RoughShellCount.roughModulus roughness := by
  exact shellData.m_eq

lemma phi_eq : phi = modulus.totient := by
  exact shellData.ph_eq

lemma modulus_pos : 0 < modulus := shellData.m_pos

lemma phi_pos : 0 < phi := by
  rw [phi_eq, Nat.totient_pos]
  exact modulus_pos

lemma theta_bound_expanded :
    256 * leafCount * modulus ≤ roughness * phi := by
  rw [leafCount_eq]
  exact shellData.theta

lemma phaseCount_eq : phaseCount = 1024 * leafCount * modulus := by
  unfold phaseCount
  rfl

lemma pivotCount_eq : pivotCount = phaseCount + 1 := by
  unfold pivotCount
  rfl

lemma phaseCount_pos : 0 < phaseCount := by
  rw [phaseCount_eq]
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by
    rw [leafCount_eq]
    norm_num)) modulus_pos

lemma pivotCount_pos : 0 < pivotCount := by
  rw [pivotCount_eq]
  omega

lemma pivotCount_ge_eight : 8 ≤ pivotCount := by
  have hleaf : 1 ≤ leafCount := by
    rw [leafCount_eq]
    norm_num
  have hmodulus : 1 ≤ modulus := modulus_pos
  have hphase : 1024 ≤ phaseCount := by
    rw [phaseCount_eq]
    calc
      1024 = 1024 * 1 * 1 := by norm_num
      _ ≤ 1024 * leafCount * modulus :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 1024 hleaf) hmodulus
  rw [pivotCount_eq]
  omega

/-- The elementary inequalities needed by the finite construction.  They
hold once `N` dominates the fixed constants; keeping the threshold explicit
makes all later extraction steps purely finite. -/
def LargeEnough (N : ℕ) : Prop :=
  modulus ≤ N ∧
  200 ≤ N ∧
  63 * roughness ≤ 4 * N ∧
  roughness ^ 2 ≤ 4 * N ∧
  63 ≤ baseHalf N ∧
  2 * phaseCount ≤ baseHalf N ∧
  8 * modulus * (leafCount * pivotCount) ≤ N * phi ∧
  4 * modulus *
      (2 * leafCount * baseHalf N + leafCount * pivotCount + reserveCount N)
      ≤ N * phi ∧
  lowerEndpoint N ≤ upperEndpoint N

lemma largeEnough_baseHalf_pos {N : ℕ} (hN : LargeEnough N) :
    0 < baseHalf N := by
  have hr : 63 ≤ baseHalf N := hN.2.2.2.2.1
  omega

lemma largeEnough_four_mul_le {N : ℕ} (hN : LargeEnough N) :
    4 * N ≤ roughness * baseHalf N := by
  have hdpos : 0 < 63 * modulus * leafCount := by
    have hleaf : 0 < leafCount := by rw [leafCount_eq]; norm_num
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) modulus_pos) hleaf
  have hupper : N * phi <
      (63 * modulus * leafCount) * (baseHalf N + 1) := by
    rw [baseHalf]
    exact Nat.lt_mul_div_succ (N * phi) hdpos
  have hr := hN.2.2.2.2.1
  have hleaf : 0 < leafCount := by rw [leafCount_eq]; norm_num
  have hupper' : N * phi ≤ 64 * modulus * leafCount * baseHalf N := by
    nlinarith [modulus_pos]
  have htheta := Nat.mul_le_mul_right N theta_bound_expanded
  have hchain : 256 * leafCount * modulus * N ≤
      64 * roughness * modulus * leafCount * baseHalf N := by
    calc
      256 * leafCount * modulus * N ≤ roughness * phi * N := htheta
      _ = roughness * (N * phi) := by ring
      _ ≤ roughness * (64 * modulus * leafCount * baseHalf N) :=
        Nat.mul_le_mul_left roughness hupper'
      _ = 64 * roughness * modulus * leafCount * baseHalf N := by ring
  nlinarith [modulus_pos, hleaf]

lemma largeEnough_roughness_le_baseHalf {N : ℕ} (hN : LargeEnough N) :
    roughness ≤ baseHalf N := by
  have hQ : roughness ^ 2 ≤ 4 * N := hN.2.2.2.1
  have hfour := largeEnough_four_mul_le hN
  by_cases hzero : roughness = 0
  · simp [hzero]
  · apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hzero)
    calc
      roughness * roughness = roughness ^ 2 := by ring
      _ ≤ 4 * N := hQ
      _ ≤ roughness * baseHalf N := hfour

lemma largeEnough_phase_mass {N : ℕ} (hN : LargeEnough N) :
    8 * N ≤ phaseCount * (baseHalf N - phaseCount) := by
  have hdpos : 0 < 63 * modulus * leafCount := by
    have hleaf : 0 < leafCount := by rw [leafCount_eq]; norm_num
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) modulus_pos) hleaf
  have hupper : N * phi <
      (63 * modulus * leafCount) * (baseHalf N + 1) := by
    rw [baseHalf]
    exact Nat.lt_mul_div_succ (N * phi) hdpos
  have hr : 63 ≤ baseHalf N := hN.2.2.2.2.1
  have hhalf : 2 * phaseCount ≤ baseHalf N := hN.2.2.2.2.2.1
  have hphi : 1 ≤ phi := phi_pos
  have hNphi : N ≤ N * phi := by nlinarith
  have hupper' : N * phi ≤
      64 * modulus * leafCount * baseHalf N := by
    nlinarith [modulus_pos]
  have hkr : 16 * N ≤ phaseCount * baseHalf N := by
    rw [phaseCount_eq]
    nlinarith
  have hrsub : baseHalf N ≤ 2 * (baseHalf N - phaseCount) := by omega
  have hmul := Nat.mul_le_mul_left phaseCount hrsub
  apply Nat.le_of_mul_le_mul_left _ (by norm_num : 0 < 2)
  calc
    2 * (8 * N) = 16 * N := by ring
    _ ≤ phaseCount * baseHalf N := hkr
    _ ≤ phaseCount * (2 * (baseHalf N - phaseCount)) := hmul
    _ = 2 * (phaseCount * (baseHalf N - phaseCount)) := by ring

lemma largeEnough_shell_card {N : ℕ} (hN : LargeEnough N) :
    N * phi ≤ 2 * modulus *
      (RoughShellCount.roughShell roughness N).card := by
  have h := RoughShellCount.twice_mul_card_roughShell_ge roughness N ?_
  · rw [← modulus_eq, ← phi_eq] at h
    exact h
  · rw [← modulus_eq]
    exact hN.1

lemma largeEnough_need_le_quarter {N : ℕ} (hN : LargeEnough N) :
    4 * modulus *
        (2 * leafCount * baseHalf N + leafCount * pivotCount + reserveCount N)
      ≤ N * phi := hN.2.2.2.2.2.2.2.1

def largeThreshold : ℕ :=
  modulus + 200 + 63 * roughness + roughness ^ 2 +
    63 * (63 * modulus * leafCount) +
    2 * phaseCount * (63 * modulus * leafCount) +
    16 * modulus * leafCount * pivotCount +
    512 * pivotCount * (16 * modulus)

lemma largeEnough_of_ge {N : ℕ} (hN : largeThreshold ≤ N) : LargeEnough N := by
  have hphi : 1 ≤ phi := phi_pos
  have hleaf : 0 < leafCount := by rw [leafCount_eq]; norm_num
  have hdpos : 0 < 63 * modulus * leafCount :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) modulus_pos) hleaf
  have h16pos : 0 < 16 * modulus := Nat.mul_pos (by norm_num) modulus_pos
  have hNphi : N ≤ N * phi := by nlinarith
  have hmod : modulus ≤ N := by
    unfold largeThreshold at hN
    omega
  have h200 : 200 ≤ N := by
    unfold largeThreshold at hN
    omega
  have hQlin : 63 * roughness ≤ 4 * N := by
    unfold largeThreshold at hN
    omega
  have hQsq : roughness ^ 2 ≤ 4 * N := by
    unfold largeThreshold at hN
    omega
  have hr : 63 ≤ baseHalf N := by
    rw [baseHalf]
    apply (Nat.le_div_iff_mul_le hdpos).2
    calc
      63 * (63 * modulus * leafCount) ≤ N := by
        unfold largeThreshold at hN
        omega
      _ ≤ N * phi := hNphi
  have hhalf : 2 * phaseCount ≤ baseHalf N := by
    rw [baseHalf]
    apply (Nat.le_div_iff_mul_le hdpos).2
    calc
      2 * phaseCount * (63 * modulus * leafCount) ≤ N := by
        unfold largeThreshold at hN
        omega
      _ ≤ N * phi := hNphi
  have hpivotStrong : 16 * modulus * (leafCount * pivotCount) ≤ N * phi := by
    calc
      16 * modulus * (leafCount * pivotCount) =
          16 * modulus * leafCount * pivotCount := by ring
      _ ≤ N := by
        unfold largeThreshold at hN
        omega
      _ ≤ N * phi := hNphi
  have hpivot : 8 * modulus * (leafCount * pivotCount) ≤ N * phi := by
    nlinarith
  have hbaseDiv : (63 * modulus * leafCount) * baseHalf N ≤ N * phi := by
    rw [baseHalf]
    exact Nat.mul_div_le _ _
  have hreserveDiv : (16 * modulus) * reserveCount N ≤ N * phi := by
    rw [reserveCount]
    exact Nat.mul_div_le _ _
  have hA : 4 * (8 * modulus * leafCount * baseHalf N) ≤ N * phi := by
    nlinarith
  have hB : 4 * (4 * modulus * leafCount * pivotCount) ≤ N * phi := by
    calc
      4 * (4 * modulus * leafCount * pivotCount) =
          16 * modulus * (leafCount * pivotCount) := by ring
      _ ≤ N * phi := hpivotStrong
  have hC : 4 * (4 * modulus * reserveCount N) ≤ N * phi := by
    calc
      4 * (4 * modulus * reserveCount N) =
          (16 * modulus) * reserveCount N := by ring
      _ ≤ N * phi := hreserveDiv
  have hneed : 4 * modulus *
      (2 * leafCount * baseHalf N + leafCount * pivotCount + reserveCount N) ≤
      N * phi := by
    have hsum : 4 *
        (8 * modulus * leafCount * baseHalf N +
          4 * modulus * leafCount * pivotCount +
          4 * modulus * reserveCount N) ≤ 3 * (N * phi) := by
      nlinarith
    have hthree : 3 * (N * phi) ≤ 4 * (N * phi) := by omega
    have hcancel :
        8 * modulus * leafCount * baseHalf N +
            4 * modulus * leafCount * pivotCount +
            4 * modulus * reserveCount N ≤ N * phi := by
      apply Nat.le_of_mul_le_mul_left (hsum.trans hthree) (by norm_num : 0 < 4)
    calc
      4 * modulus *
          (2 * leafCount * baseHalf N + leafCount * pivotCount + reserveCount N) =
        8 * modulus * leafCount * baseHalf N +
          4 * modulus * leafCount * pivotCount +
          4 * modulus * reserveCount N := by ring
      _ ≤ N * phi := hcancel
  have hreserveLarge : 512 * pivotCount ≤ reserveCount N := by
    rw [reserveCount]
    apply (Nat.le_div_iff_mul_le h16pos).2
    calc
      512 * pivotCount * (16 * modulus) ≤ N := by
        unfold largeThreshold at hN
        omega
      _ ≤ N * phi := hNphi
  have hend : lowerEndpoint N ≤ upperEndpoint N := by
    rw [lowerEndpoint, upperEndpoint]
    simpa [mul_comm] using Nat.mul_le_mul_right N hreserveLarge
  exact ⟨hmod, h200, hQlin, hQsq, hr, hhalf, hpivot, hneed, hend⟩

theorem eventually_largeEnough : ∀ᶠ N : ℕ in Filter.atTop, LargeEnough N := by
  exact Filter.eventually_atTop.2 ⟨largeThreshold, fun _ hN ↦ largeEnough_of_ge hN⟩

lemma roughShell_subset_Ico (N : ℕ) :
    RoughShellCount.roughShell roughness N ⊆ Finset.Ico N (2 * N) := by
  intro n hn
  exact (Finset.mem_filter.mp hn).1

lemma roughShell_rough (N n : ℕ)
    (hn : n ∈ RoughShellCount.roughShell roughness N) :
    Erdos344.RoughUpTo roughness n := by
  simpa [Erdos344.RoughUpTo, RoughShellCount.RoughUpTo] using
    RoughShellCount.mem_roughShell_rough roughness N n hn

/-- One of the two colours occupies at least half of the fixed rough shell. -/
lemma exists_dense_shell_color (χ : ℕ → Fin 2) {N : ℕ}
    (hN : LargeEnough N) :
    ∃ i : Fin 2, N * phi ≤ 4 * modulus *
      ((RoughShellCount.roughShell roughness N).filter fun n ↦ χ n = i).card := by
  let X := RoughShellCount.roughShell roughness N
  let X₀ := X.filter fun n ↦ χ n = 0
  let X₁ := X.filter fun n ↦ χ n = 1
  have hunion : X₀ ∪ X₁ = X := by
    ext n
    simp only [X₀, X₁, X, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
    · intro hn
      have hc : χ n = 0 ∨ χ n = 1 := by
        generalize heq : χ n = c
        fin_cases c <;> simp_all
      exact hc.elim (fun h ↦ Or.inl ⟨hn, h⟩) (fun h ↦ Or.inr ⟨hn, h⟩)
  have hdisj : Disjoint X₀ X₁ := by
    rw [Finset.disjoint_left]
    intro n hn0 hn1
    have h0 := (Finset.mem_filter.mp hn0).2
    have h1 := (Finset.mem_filter.mp hn1).2
    omega
  have hcard : X.card = X₀.card + X₁.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hshell := largeEnough_shell_card hN
  change N * phi ≤ 2 * modulus * X.card at hshell
  by_cases hle : X₀.card ≤ X₁.card
  · refine ⟨1, ?_⟩
    change N * phi ≤ 4 * modulus * X₁.card
    calc
      N * phi ≤ 2 * modulus * X.card := hshell
      _ ≤ 4 * modulus * X₁.card := by rw [hcard]; nlinarith
  · refine ⟨0, ?_⟩
    change N * phi ≤ 4 * modulus * X₀.card
    have hle' : X₁.card ≤ X₀.card := Nat.le_of_not_ge hle
    calc
      N * phi ≤ 2 * modulus * X.card := hshell
      _ ≤ 4 * modulus * X₀.card := by rw [hcard]; nlinarith

lemma exists_three_disjoint_exact {H : Finset ℕ} {a b c : ℕ}
    (hcard : a + b + c ≤ H.card) :
    ∃ A B C : Finset ℕ,
      A ⊆ H ∧ B ⊆ H ∧ C ⊆ H ∧
      A.card = a ∧ B.card = b ∧ C.card = c ∧
      Disjoint A B ∧ Disjoint (A ∪ B) C := by
  have ha : a ≤ H.card := by omega
  obtain ⟨A, hAH, hAcard⟩ := Finset.exists_subset_card_eq ha
  let R := H \ A
  have hRcard : R.card = H.card - a := by
    dsimp only [R]
    rw [Finset.card_sdiff_of_subset hAH, hAcard]
  have hb : b ≤ R.card := by rw [hRcard]; omega
  obtain ⟨B, hBR, hBcard⟩ := Finset.exists_subset_card_eq hb
  let T := R \ B
  have hTcard : T.card = R.card - b := by
    dsimp only [T]
    rw [Finset.card_sdiff_of_subset hBR, hBcard]
  have hc : c ≤ T.card := by rw [hTcard, hRcard]; omega
  obtain ⟨C, hCT, hCcard⟩ := Finset.exists_subset_card_eq hc
  have hBH : B ⊆ H := hBR.trans Finset.sdiff_subset
  have hCH : C ⊆ H :=
    (hCT.trans Finset.sdiff_subset).trans Finset.sdiff_subset
  have hAB : Disjoint A B := by
    exact (Finset.disjoint_sdiff : Disjoint A (H \ A)).mono_right hBR
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro x hx hxc
    have hxT := hCT hxc
    have hxR : x ∈ R := (Finset.mem_sdiff.mp hxT).1
    have hxnotB : x ∉ B := (Finset.mem_sdiff.mp hxT).2
    rw [Finset.mem_union] at hx
    exact hx.elim
      (fun hxA ↦ (Finset.mem_sdiff.mp hxR).2 hxA)
      (fun hxB ↦ hxnotB hxB)
  exact ⟨A, B, C, hAH, hBH, hCH, hAcard, hBcard, hCcard, hAB, hABC⟩

/-- The complete finite shell lemma: a sufficiently dense `Q`-rough
subcollection of `[N,2N)` has subset sums covering a fixed interval from
linear to quadratic scale. -/
theorem dense_shell_subsetSum_interval {N : ℕ} (hN : LargeEnough N)
    {H : Finset ℕ}
    (hH : H ⊆ RoughShellCount.roughShell roughness N)
    (hdense : N * phi ≤ 4 * modulus * H.card) :
    Finset.Icc (lowerEndpoint N) (upperEndpoint N) ⊆ H.subsetSum := by
  let r := baseHalf N
  let L := pivotCount
  let baseSize := 2 * leafCount * r
  let pivotSize := leafCount * L
  let reserveSize := reserveCount N
  have hfactor : 0 < 4 * modulus := Nat.mul_pos (by norm_num) modulus_pos
  have hneedMul := largeEnough_need_le_quarter hN
  have hneed : baseSize + pivotSize + reserveSize ≤ H.card := by
    apply Nat.le_of_mul_le_mul_left _ hfactor
    calc
      4 * modulus * (baseSize + pivotSize + reserveSize) =
          4 * modulus *
            (2 * leafCount * baseHalf N + leafCount * pivotCount +
              reserveCount N) := by
            simp only [baseSize, pivotSize, reserveSize, r, L]
      _ ≤ N * phi := hneedMul
      _ ≤ 4 * modulus * H.card := hdense
  obtain ⟨base, pivots, reserve, hbaseH, hpivotsH, hreserveH,
      hbasecard, hpivotscard, hreservecard, hbasePivots,
      hconstructionReserve⟩ :=
    exists_three_disjoint_exact (H := H) hneed
  have hbaseTreeCard : base.card = 2 ^ depth * (2 * r) := by
    rw [hbasecard]
    simp only [baseSize, leafCount]
    ring
  have hpivotTreeCard : pivots.card = 2 ^ depth * L := by
    rw [hpivotscard]
    simp only [pivotSize, leafCount]
  obtain ⟨A, hAcarrier, hAdisjoint, hAleavesCard⟩ :=
    PT.exists_exact_tree hbaseTreeCard
  obtain ⟨B, hBcarrier, hBdisjoint, hBleavesCard⟩ :=
    PT.exists_exact_tree hpivotTreeCard
  have hAleaves : A.AllLeaves fun C ↦ C.card = 2 * r ∧ C ⊆ A.carrier :=
    PT.allLeaves_and hAleavesCard (A.allLeaves_subset_carrier)
  have hBleaves : B.AllLeaves fun P ↦ P.card = L ∧ P ⊆ B.carrier :=
    PT.allLeaves_and hBleavesCard (B.allLeaves_subset_carrier)
  have hAB : Disjoint A.carrier B.carrier := by
    simpa only [hAcarrier, hBcarrier] using hbasePivots
  have hNpos : 0 < N := by
    have h200 : 200 ≤ N := hN.2.1
    omega
  have hrpos : 0 < r := by
    dsimp only [r]
    exact largeEnough_baseHalf_pos hN
  have hhalf : 2 * phaseCount ≤ r := by
    exact hN.2.2.2.2.2.1
  have hQr : 4 * N ≤ roughness * r := by
    exact largeEnough_four_mul_le hN
  have hQle : roughness ≤ r := by
    exact largeEnough_roughness_le_baseHalf hN
  have hmass : 8 * N ≤ phaseCount * (r - phaseCount) := by
    exact largeEnough_phase_mass hN
  have hbaseShell : base ⊆ RoughShellCount.roughShell roughness N :=
    hbaseH.trans hH
  have hpivotsShell : pivots ⊆ RoughShellCount.roughShell roughness N :=
    hpivotsH.trans hH
  have hleafFacts : ∀ C P : Finset ℕ,
      (C.card = 2 * r ∧ C ⊆ A.carrier) →
      (P.card = L ∧ P ⊆ B.carrier) →
      L * (N / 4) ≤
          (Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P).card ∧
        Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P ⊆
          Finset.Icc 0 (4 * L * N) ∧
        ¬ Erdos360.ContainedInNontrivialAP
          (Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P) := by
    intro C P hCdata hPdata
    have hCshell : C ⊆ RoughShellCount.roughShell roughness N := by
      intro c hc
      apply hbaseShell
      rw [← hAcarrier]
      exact hCdata.2 hc
    have hPshell : P ⊆ RoughShellCount.roughShell roughness N := by
      intro p hp
      apply hpivotsShell
      rw [← hBcarrier]
      exact hPdata.2 hp
    have hCIco : C ⊆ Finset.Ico N (2 * N) :=
      hCshell.trans (roughShell_subset_Ico N)
    have hPIco : P ⊆ Finset.Ico N (2 * N) :=
      hPshell.trans (roughShell_subset_Ico N)
    have hCrough : ∀ c ∈ C, Erdos344.RoughUpTo roughness c := by
      intro c hc
      exact roughShell_rough N c (hCshell hc)
    have hcover : ∀ p ∈ P,
        p ≤ 4 * ((Erdos344.boundedSubsetSum C L).image
          (fun u : ℕ ↦ (u : ZMod p))).card := by
      intro p hp
      have hpI := Finset.mem_Ico.mp (hPIco hp)
      let : NeZero p := ⟨by omega⟩
      have hrle : r ≤ C.card := by rw [hCdata.1]; omega
      obtain ⟨D, hDC, hDcard⟩ := Finset.exists_subset_card_eq hrle
      let E := C \ D
      have hEcard : E.card = r := by
        dsimp only [E]
        rw [Finset.card_sdiff_of_subset hDC, hCdata.1, hDcard]
        omega
      have hDE : Disjoint D E := by
        exact Finset.disjoint_sdiff
      have hDEunion : D ∪ E = C := by
        exact Finset.union_sdiff_of_subset hDC
      have hDIco : D ⊆ Finset.Ico N (2 * N) := hDC.trans hCIco
      have hEIco : E ⊆ Finset.Ico N (2 * N) :=
        Finset.sdiff_subset.trans hCIco
      have hErough : ∀ e ∈ E, Erdos344.RoughUpTo roughness e := by
        intro e he
        exact hCrough e (Finset.sdiff_subset he)
      have hpMass : 4 * p ≤ phaseCount * (r - phaseCount) := by
        nlinarith
      have hquarter := Leaf.boundedSubsetSum_quarter_modulus
        (Q := roughness) (N := N) (r := r) (k := phaseCount)
        (p := p) (by omega) hpI.1 hpI.2 hDE hDIco hEIco hDcard hEcard
        hErough hrpos hhalf hQr hQle hpMass
      simpa only [hDEunion, L, pivotCount_eq] using hquarter
    have hcardLeaf : L * (N / 4) ≤
        (Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P).card :=
      Leaf.pivotExtended_card_ge hPIco hPdata.1 hcover
    have hboxLeaf :
        Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P ⊆
          Finset.Icc 0 (4 * L * N) :=
      Leaf.pivotExtended_subset_box hCIco hPIco hPdata.1
    have haperLeaf :
        ¬ Erdos360.ContainedInNontrivialAP
          (Erdos344.pivotExtended (Erdos344.boundedSubsetSum C L) P) := by
      apply Erdos344.pivotExtended_notContained_of_rough hNpos hCIco hCrough
        (s := L) (P := P)
      · rw [hCdata.1]
        nlinarith
      · dsimp only [L]
        exact pivotCount_pos
    exact ⟨hcardLeaf, hboxLeaf, haperLeaf⟩
  have hpairs := Erdos344.PartitionTree.allLeafPairs_of_allLeaves
    hAleaves hBleaves hleafFacts
  have hpairsCard := PT.allLeafPairs_mono hpairs
    (fun _ _ h ↦ h.1)
  have hpairsBox := PT.allLeafPairs_mono hpairs
    (fun _ _ h ↦ h.2.1)
  have hpairsAper := PT.allLeafPairs_mono hpairs
    (fun _ _ h ↦ h.2.2)
  have hell : 2 ≤ L * (N / 4) := by
    have h200 : 200 ≤ N := hN.2.1
    have hdiv : 50 ≤ N / 4 := by omega
    have hL : 0 < L := by exact pivotCount_pos
    nlinarith
  have hexceed :
      2 ^ depth * (4 * L * N) + 1 <
        Erdos344.SumTree.growthLower (L * (N / 4)) depth := by
    simpa only [depth] using Tree.depthSeven_exceeds hN.2.1
      (show 0 < L from pivotCount_pos)
  obtain ⟨a, hastart, hinterval⟩ := Tree.paired_interval_with_start_bound
    A B hell hAdisjoint hBdisjoint hAB hpairsCard hpairsBox hpairsAper hexceed
  have hastart' : a ≤ lowerEndpoint N := by
    calc
      a ≤ 2 ^ depth * (4 * L * N) := hastart
      _ = lowerEndpoint N := by
        simp only [depth, L, lowerEndpoint]
        norm_num
        ring
  have hreserveIco : reserve ⊆ Finset.Ico N (2 * N) :=
    (hreserveH.trans hH).trans (roughShell_subset_Ico N)
  have hlong : 2 * N ≤ 2 * (L * (N / 4)) - 1 := by
    exact Tree.shell_interval_long_enough hN.2.1
      (show 8 ≤ L from pivotCount_ge_eight)
  have hreserveSmall : ∀ x ∈ reserve, x ≤ 2 * (L * (N / 4)) - 1 := by
    intro x hx
    have hxI := Finset.mem_Ico.mp (hreserveIco hx)
    omega
  have htreeReserve : Disjoint (A.carrier ∪ B.carrier) reserve := by
    simpa only [hAcarrier, hBcarrier] using hconstructionReserve
  have habsorb : Finset.Icc a
      (a + (2 * (L * (N / 4)) - 2) + ∑ x ∈ reserve, x) ⊆
      ((A.carrier ∪ B.carrier) ∪ reserve).subsetSum := by
    apply Erdos360.Icc_subset_subsetSum_union_of_le_length
      (show a ≤ a + (2 * (L * (N / 4)) - 2) by omega)
      htreeReserve hinterval
    intro x hx
    have hxle := hreserveSmall x hx
    omega
  have hreserveSum : upperEndpoint N ≤ ∑ x ∈ reserve, x := by
    have hreservecard' : reserve.card = reserveCount N := by
      simpa only [reserveSize] using hreservecard
    rw [upperEndpoint, ← hreservecard']
    calc
      N * reserve.card = ∑ _x ∈ reserve, N := by simp [mul_comm]
      _ ≤ ∑ x ∈ reserve, x := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_Ico.mp (hreserveIco hx)).1
  have hsupport : (A.carrier ∪ B.carrier) ∪ reserve ⊆ H := by
    simpa only [hAcarrier, hBcarrier] using
      Finset.union_subset (Finset.union_subset hbaseH hpivotsH) hreserveH
  intro x hx
  apply Finset.subsetSum_mono hsupport
  apply habsorb
  rw [Finset.mem_Icc] at hx ⊢
  constructor
  · exact hastart'.trans hx.1
  · exact hx.2.trans (hreserveSum.trans (by omega))

theorem twoColor_shell_interval (χ : ℕ → Fin 2) {N : ℕ}
    (hN : LargeEnough N) :
    ∃ i : Fin 2,
      Finset.Icc (lowerEndpoint N) (upperEndpoint N) ⊆
        ((RoughShellCount.roughShell roughness N).filter
          fun n ↦ χ n = i).subsetSum := by
  obtain ⟨i, hi⟩ := exists_dense_shell_color χ hN
  refine ⟨i, dense_shell_subsetSum_interval hN (Finset.filter_subset _ _) hi⟩

theorem eventually_twoColor_shell_interval (χ : ℕ → Fin 2) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ i : Fin 2,
        Finset.Icc (lowerEndpoint N) (upperEndpoint N) ⊆
          ((RoughShellCount.roughShell roughness N).filter
            fun n ↦ χ n = i).subsetSum := by
  filter_upwards [eventually_largeEnough] with N hN
  exact twoColor_shell_interval χ hN



end

end Erdos1211Local
