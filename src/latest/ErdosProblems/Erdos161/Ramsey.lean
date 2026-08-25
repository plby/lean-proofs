import Mathlib
import ErdosProblems.Erdos1098

open Filter Finset Fintype MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace Erdos161

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## A finite hypergraph Ramsey lemma -/

/-- A coloring is constant on all `t`-subsets of `S`. -/
def HomogeneousOn (t : ℕ) (c : Finset ℕ → Bool) (S : Set ℕ) : Prop :=
  ∃ b : Bool, ∀ e : Finset ℕ, e.card = t → (e : Set ℕ) ⊆ S → c e = b

/-- Infinite Ramsey's theorem, in the precise set-valued form needed for the
compactness argument below. -/
theorem infinite_ramsey_on (t : ℕ) (c : Finset ℕ → Bool)
    (S : Set ℕ) (hS : S.Infinite) :
    ∃ T : Set ℕ, T ⊆ S ∧ T.Infinite ∧ HomogeneousOn t c T := by
  induction t generalizing c S with
  | zero =>
      refine ⟨S, fun _ h ↦ h, hS, ?_⟩
      refine ⟨c ∅, ?_⟩
      intro e he _
      have : e = ∅ := Finset.card_eq_zero.mp he
      simpa [this]
  | succ t ih =>
      have hstep :
          ∀ R : Set ℕ, R.Infinite →
            ∃ x ∈ R, ∃ T ⊆ R, T.Infinite ∧
              (∀ y ∈ T, x < y) ∧
              ∃ b : Bool, ∀ e : Finset ℕ, e.card = t →
                (e : Set ℕ) ⊆ T → c (insert x e) = b := by
        intro R hR
        obtain ⟨x, hxR⟩ := hR.nonempty
        let R' := R ∩ {y | x < y}
        have hR' : R'.Infinite := by
          exact (hR.sdiff (Set.finite_le_nat x)).mono fun y hy ↦ by
            exact ⟨hy.1, by simpa using hy.2⟩
        obtain ⟨T, hTR', hTinf, b, hb⟩ :=
          ih (fun e ↦ c (insert x e)) R' hR'
        refine ⟨x, hxR, T, ?_, hTinf, ?_, b, hb⟩
        · exact hTR'.trans Set.inter_subset_left
        · intro y hy
          exact (hTR' hy).2
      choose! x hx T hT hTinf hlt b hb using hstep
      let R : ℕ → Set ℕ :=
        fun n ↦ Nat.recOn n S (fun _ U ↦ T U)
      have hRzero : R 0 = S := rfl
      have hRsucc : ∀ n, R (n + 1) = T (R n) := fun _ ↦ rfl
      have hRinf : ∀ n, (R n).Infinite := by
        intro n
        induction n with
        | zero => exact hS
        | succ n hn => exact hTinf (R n) hn
      have hRsub : ∀ n, R (n + 1) ⊆ R n := by
        intro n
        rw [hRsucc]
        exact hT (R n) (hRinf n)
      have hRanti : Antitone R := antitone_nat_of_succ_le hRsub
      let q₀ : ℕ → ℕ := fun n ↦ x (R n)
      have hq₀mem : ∀ n, q₀ n ∈ R n :=
        fun n ↦ hx (R n) (hRinf n)
      have hq₀lt : ∀ n, q₀ n < q₀ (n + 1) := by
        intro n
        exact hlt (R n) (hRinf n) _ (by
          rw [← hRsucc]
          exact hq₀mem (n + 1))
      have hq₀mono : StrictMono q₀ := strictMono_nat_of_lt_succ hq₀lt
      let b₀ : ℕ → Bool := fun n ↦ b (R n)
      obtain ⟨f, hfmono, B, hfB⟩ :=
        Erdos1098.exists_monochromatic_subsequence b₀
      let q : ℕ → ℕ := fun n ↦ q₀ (f n)
      have hqmono : StrictMono q := hq₀mono.comp hfmono
      have hqinj : Function.Injective q := hqmono.injective
      let H : Set ℕ := Set.range q
      have hHinf : H.Infinite := Set.infinite_range_of_injective hqinj
      have hHsub : H ⊆ S := by
        rintro y ⟨n, rfl⟩
        have hmem : q₀ (f n) ∈ R (f n) := hq₀mem _
        exact hRzero ▸ hRanti (Nat.zero_le _) hmem
      refine ⟨H, hHsub, hHinf, B, ?_⟩
      intro e hecard hesub
      let inv : ℕ → ℕ := Function.invFun q
      let I : Finset ℕ := e.image inv
      have hright : ∀ y ∈ e, q (inv y) = y := by
        intro y hy
        exact Function.invFun_eq (hesub hy)
      have hinv_inj : Set.InjOn inv (e : Set ℕ) := by
        intro y hy z hz hyz
        rw [← hright y hy, ← hright z hz, hyz]
      have hIcard : I.card = t + 1 := by
        rw [show I = e.image inv by rfl, Finset.card_image_iff.mpr hinv_inj,
          hecard]
      have hIimage : I.image q = e := by
        ext y
        constructor
        · intro hy
          obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨z, hze, hzj⟩ := Finset.mem_image.mp hjI
          subst j
          simpa [hright z hze]
        · intro hy
          apply Finset.mem_image.mpr
          refine ⟨inv y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
          exact hright y hy
      have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
      let i := I.min' hIne
      have hiI : i ∈ I := Finset.min'_mem I hIne
      let J := I.erase i
      have hJcard : J.card = t := by
        dsimp [J]
        rw [Finset.card_erase_of_mem hiI, hIcard]
        omega
      have hfuture :
          ((J.image q : Finset ℕ) : Set ℕ) ⊆ R (f i + 1) := by
        intro y hy
        obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hy
        have hjI : j ∈ I := (Finset.mem_erase.mp hjJ).2
        have hne : j ≠ i := (Finset.mem_erase.mp hjJ).1
        have hij : i < j := lt_of_le_of_ne (Finset.min'_le I j hjI) (Ne.symm hne)
        have hfij : f i + 1 ≤ f j := Nat.succ_le_of_lt (hfmono hij)
        exact hRanti hfij (hq₀mem (f j))
      have hstar :=
        hb (R (f i)) (hRinf (f i)) (J.image q)
          (by simpa [Finset.card_image_of_injective _ hqinj] using hJcard)
          (by simpa [hRsucc] using hfuture)
      have hstar' :
          c (insert (q i) (J.image q)) = B := by
        calc
          c (insert (q i) (J.image q)) =
              b (R (f i)) := by simpa [q, q₀] using hstar
          _ = B := hfB i
      calc
        c e = c (I.image q) := by rw [hIimage]
        _ = c (insert (q i) (J.image q)) := by
          congr 1
          rw [← Finset.image_insert, Finset.insert_erase hiI]
        _ = B := hstar'

/-- Colorings of the `t`-subsets of the natural numbers, equipped with the
product topology for the compactness proof. -/
abbrev InfiniteEdgeColoring (t : ℕ) :=
  {e : Finset ℕ // e.card = t} → Bool

def finNatEmbedding (d : ℕ) : Fin d ↪ ℕ :=
  ⟨fun i ↦ i, Fin.val_injective⟩

def liftFiniteEdge {d : ℕ} (e : Finset (Fin d)) : Finset ℕ :=
  e.map (finNatEmbedding d)

@[simp] lemma card_liftFiniteEdge {d : ℕ} (e : Finset (Fin d)) :
    (liftFiniteEdge e).card = e.card := by
  simp [liftFiniteEdge]

def finiteRamseyGood (t h d : ℕ) (C : InfiniteEdgeColoring t) : Prop :=
  ∃ H : Finset (Fin d), H.card = h ∧
    ∃ b : Bool, ∀ (e : Finset (Fin d)) (hecard : e.card = t),
      e ⊆ H →
      C ⟨liftFiniteEdge e, by simpa using hecard⟩ = b

lemma isOpen_finiteRamseyGood (t h d : ℕ) :
    IsOpen {C : InfiniteEdgeColoring t | finiteRamseyGood t h d C} := by
  rw [isOpen_iff_forall_mem_open]
  intro C hC
  obtain ⟨H, hHcard, b, hb⟩ := hC
  let V : Set (InfiniteEdgeColoring t) :=
    ⋂ e : Finset (Fin d),
      if he : e.card = t ∧ e ⊆ H then
        {C | C ⟨liftFiniteEdge e, by
          simpa using he.1⟩ = b}
      else Set.univ
  refine ⟨V, ?_, ?_, ?_⟩
  · intro C' hC'
    refine ⟨H, hHcard, b, ?_⟩
    intro e hecard hesub
    have hmem := Set.mem_iInter.mp hC' e
    simpa [V, hecard, hesub] using hmem
  · apply isOpen_iInter_of_finite
    intro e
    split_ifs
    · change IsOpen ((fun C : InfiniteEdgeColoring t =>
          C ⟨liftFiniteEdge e, by simpa using ‹e.card = t ∧ e ⊆ H›.1⟩) ⁻¹'
          ({b} : Set Bool))
      exact (continuous_apply _).isOpen_preimage _
        (isOpen_discrete ({b} : Set Bool))
    · exact isOpen_univ
  · apply Set.mem_iInter.mpr
    intro e
    split_ifs with he
    · simpa using hb e he.1 he.2
    · trivial

lemma finiteRamseyGood_mono {t h d : ℕ} {C : InfiniteEdgeColoring t}
    (hgood : finiteRamseyGood t h d C) :
    finiteRamseyGood t h (d + 1) C := by
  obtain ⟨H, hHcard, b, hb⟩ := hgood
  let emb : Fin d ↪ Fin (d + 1) := Fin.castLEEmb (Nat.le_succ d)
  let H' : Finset (Fin (d + 1)) := H.map emb
  refine ⟨H', by simp [H', hHcard], b, ?_⟩
  intro e hecard heH'
  have herange : ∀ y ∈ e, y ∈ Set.range emb := by
    intro y hy
    obtain ⟨x, hxH, rfl⟩ := Finset.mem_map.mp (heH' hy)
    exact ⟨x, rfl⟩
  let e₀ : Finset (Fin d) :=
    e.preimage emb emb.injective.injOn
  have himage : e₀.map emb = e := by
    rw [Finset.map_eq_image]
    rw [show e₀ = e.preimage emb
      emb.injective.injOn by rfl,
      Finset.image_preimage]
    exact Finset.filter_eq_self.mpr herange
  have he₀card : e₀.card = t := by
    have hcardmap : (e₀.map emb).card = e₀.card := by simp
    rw [himage] at hcardmap
    omega
  have he₀sub : e₀ ⊆ H := by
    intro x hx
    have hxmap : emb x ∈ e := by
      rw [← himage]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxH' := heH' hxmap
    obtain ⟨y, hyH, hyx⟩ := Finset.mem_map.mp hxH'
    exact emb.injective hyx ▸ hyH
  have hlift : liftFiniteEdge e₀ = liftFiniteEdge e := by
    rw [← himage]
    ext y
    simp [liftFiniteEdge, emb, finNatEmbedding]
  simpa [hlift] using hb e₀ he₀card he₀sub

lemma exists_finiteRamseyGood (t h : ℕ) (C : InfiniteEdgeColoring t) :
    ∃ d, finiteRamseyGood t h d C := by
  let c : Finset ℕ → Bool := fun e ↦
    if he : e.card = t then C ⟨e, he⟩ else false
  obtain ⟨T, -, hTinf, b, hb⟩ :=
    infinite_ramsey_on t c Set.univ Set.infinite_univ
  obtain ⟨K, hKT, hKcard⟩ := hTinf.exists_subset_card_eq h
  let d := K.sup id + 1
  have hbound : ∀ x : ↥K, x.1 < d := by
    intro x
    dsimp [d]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) x.property)
  let embFun : ↥K → Fin d := fun x ↦ Fin.mk x.1 (hbound x)
  have hembFun : Function.Injective embFun := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Fin.val hxy
  let emb : ↥K ↪ Fin d := ⟨embFun, hembFun⟩
  let H : Finset (Fin d) := K.attach.map emb
  refine ⟨d, H, by simp [H, hKcard], b, ?_⟩
  intro e hecard heH
  have hliftK : ((liftFiniteEdge e : Finset ℕ) : Set ℕ) ⊆ K := by
    intro y hy
    obtain ⟨i, hie, rfl⟩ := Finset.mem_map.mp hy
    have hiH := heH hie
    obtain ⟨z, hz, hzi⟩ := Finset.mem_map.mp hiH
    have hi_eq : (i : ℕ) = z.1 := by
      simpa [emb, embFun] using (congrArg Fin.val hzi).symm
    change (i : ℕ) ∈ K
    rw [hi_eq]
    exact z.property
  have hcolor := hb (liftFiniteEdge e) (by simpa using hecard)
    (hliftK.trans hKT)
  simpa [c, hecard] using hcolor

/-- The qualitative finite two-color hypergraph Ramsey theorem.  It is
obtained from the infinite theorem by compactness of the Boolean product
space; no Ramsey theorem is assumed as an axiom. -/
theorem finite_hypergraph_ramsey (t h : ℕ) :
    ∃ d, ∀ C : InfiniteEdgeColoring t, finiteRamseyGood t h d C := by
  by_contra hcontra
  push Not at hcontra
  let Bad : ℕ → Set (InfiniteEdgeColoring t) :=
    fun d ↦ {C | ¬finiteRamseyGood t h d C}
  have hbad_nonempty : ∀ d, (Bad d).Nonempty := by
    intro d
    obtain ⟨C, hC⟩ := hcontra d
    exact ⟨C, hC⟩
  have hbad_closed : ∀ d, IsClosed (Bad d) := by
    intro d
    exact (isOpen_finiteRamseyGood t h d).isClosed_compl
  have hbad_step : ∀ d, Bad (d + 1) ⊆ Bad d := by
    intro d C hC hgood
    exact hC (finiteRamseyGood_mono hgood)
  have hinter :
      (⋂ d, Bad d).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      Bad hbad_step hbad_nonempty (hbad_closed 0).isCompact hbad_closed
  obtain ⟨C, hC⟩ := hinter
  obtain ⟨d, hd⟩ := exists_finiteRamseyGood t h C
  exact (Set.mem_iInter.mp hC d) hd

end Erdos161

end
