import ErdosProblems.Erdos722.SpecialCliqueRotationAsymptotic

namespace Erdos722

open Finset
open Erdos722.RootedEmbedding
open Erdos722.ExchangePattern
open Erdos722.SpecialCliqueCandidates

noncomputable section

abbrev FocusingBaseCoord (g mE mA mX mR : ℕ) :=
  Unit ⊕ ((Fin g × Fin mE) ⊕
    ((Fin g × Fin mA) ⊕ ((Fin g × Fin mX) ⊕ (Fin g × Fin mR))))

abbrev FocusingColor (g mE mA mX mR mFresh : ℕ) :=
  (FocusingBaseCoord g mE mA mX mR ⊕
    FocusingBaseCoord g mE mA mX mR) ⊕ (Fin g × Fin mFresh)

def identityBaseCoord {g mE mA mX mR : ℕ} :
    FocusingBaseCoord g mE mA mX mR := Sum.inl ()

def exchangeBaseCoord {g mE mA mX mR : ℕ}
    (t : Fin g) (i : Fin mE) : FocusingBaseCoord g mE mA mX mR :=
  Sum.inr (Sum.inl (t, i))

def auxiliaryBaseCoord {g mE mA mX mR : ℕ}
    (t : Fin g) (i : Fin mA) : FocusingBaseCoord g mE mA mX mR :=
  Sum.inr (Sum.inr (Sum.inl (t, i)))

def eliminationBaseCoord {g mE mA mX mR : ℕ}
    (t : Fin g) (i : Fin mX) : FocusingBaseCoord g mE mA mX mR :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, i))))

def reserveBaseCoord {g mE mA mX mR : ℕ}
    (t : Fin g) (i : Fin mR) : FocusingBaseCoord g mE mA mX mR :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (t, i))))

def focusingBasePerm {n g mE mA mX mR : ℕ}
    (choiceE : Fin g → Fin mE → Equiv.Perm (Fin n))
    (choiceA : Fin g → Fin mA → Equiv.Perm (Fin n))
    (choiceX : Fin g → Fin mX → Equiv.Perm (Fin n))
    (choiceR : Fin g → Fin mR → Equiv.Perm (Fin n)) :
    FocusingBaseCoord g mE mA mX mR → Equiv.Perm (Fin n)
  | Sum.inl _ => Equiv.refl _
  | Sum.inr (Sum.inl z) => choiceE z.1 z.2
  | Sum.inr (Sum.inr (Sum.inl z)) => choiceA z.1 z.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl z))) => choiceX z.1 z.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr z))) => choiceR z.1 z.2

def focusingRootSupport {g mE mA mX mR mFresh : ℕ} :
    FocusingColor g mE mA mX mR mFresh →
      FocusingBaseCoord g mE mA mX mR
  | Sum.inl (Sum.inl c) => c
  | Sum.inl (Sum.inr c) => c
  | Sum.inr _ => identityBaseCoord

def rootAliasColor {g mE mA mX mR mFresh : ℕ}
    (c : FocusingBaseCoord g mE mA mX mR) :
    FocusingColor g mE mA mX mR mFresh := Sum.inl (Sum.inl c)

def freeAliasColor {g mE mA mX mR mFresh : ℕ}
    (c : FocusingBaseCoord g mE mA mX mR) :
    FocusingColor g mE mA mX mR mFresh := Sum.inl (Sum.inr c)

def freshGeneratorColor {g mE mA mX mR mFresh : ℕ}
    (t : Fin g) (i : Fin mFresh) :
    FocusingColor g mE mA mX mR mFresh := Sum.inr (t, i)

def focusingGeneratorPerm {n g mE mA mX mR mFresh : ℕ}
    (basePerm : FocusingBaseCoord g mE mA mX mR → Equiv.Perm (Fin n))
    (fresh : Fin g → Fin mFresh → Equiv.Perm (Fin n)) :
    FocusingColor g mE mA mX mR mFresh → Equiv.Perm (Fin n)
  | Sum.inl (Sum.inl c) => basePerm c
  | Sum.inl (Sum.inr c) => basePerm c
  | Sum.inr z => fresh z.1 z.2

def focusingRootPerm {n g mE mA mX mR mFresh : ℕ}
    (basePerm : FocusingBaseCoord g mE mA mX mR → Equiv.Perm (Fin n)) :
    FocusingColor g mE mA mX mR mFresh → Equiv.Perm (Fin n) :=
  fun c ↦ basePerm (focusingRootSupport c)

/-- A block is rainbow for a family of coloured edge hosts if its
`r`-edges admit pairwise distinct colours and every edge belongs to the
host of its assigned colour. -/
noncomputable def rainbowBlocks (u n q r : ℕ)
    (K : Fin u → Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powersetCard q).filter fun Q ↦
    ∃ color : Finset (Fin n) → Fin u,
      Set.InjOn color (↑(Q.powersetCard r) : Set (Finset (Fin n))) ∧
      ∀ e ∈ Q.powersetCard r, e ∈ K (color e)

@[simp] lemma mem_rainbowBlocks
    {u n q r : ℕ} {K : Fin u → Finset (Finset (Fin n))}
    {Q : Finset (Fin n)} :
    Q ∈ rainbowBlocks u n q r K ↔
      Q.card = q ∧
      ∃ color : Finset (Fin n) → Fin u,
        Set.InjOn color (↑(Q.powersetCard r) : Set (Finset (Fin n))) ∧
        ∀ e ∈ Q.powersetCard r, e ∈ K (color e) := by
  classical
  simp [rainbowBlocks]

theorem mappedRemaining_mem_rainbowBlocks
    {u n q r : ℕ} [Nonempty (Fin u)]
    (E : RelabeledFullExchange q r)
    (phi : Fin E.v ↪ Fin n)
    (Kstar : Fin u → Finset (Finset (Fin n)))
    (freeColor : ↑E.pattern.freeEdges → Fin u)
    (hfreeColor : Function.Injective freeColor)
    (hfreeMem : ∀ a : ↑E.pattern.freeEdges,
      mapEdge phi a.1 ∈ Kstar (freeColor a))
    {B : Finset (Fin E.v)} (hB : B ∈ remainingBlocks E) :
    mapEdge phi B ∈ rainbowBlocks u n q r Kstar := by
  classical
  let Q := mapEdge phi B
  have hBcard : B.card = q := remainingBlocks_uniform E hB
  have hQcard : Q.card = q := (card_mapEdge phi B).trans hBcard
  have hBedge : B.powersetCard r ⊆ E.pattern.edges := by
    rcases Finset.mem_union.mp hB with hpos | hneg
    · exact E.positive_decomp.2.1 B (Finset.mem_erase.mp hpos).2
    · exact E.negative_decomp.2.1 B (Finset.mem_sdiff.mp hneg).1
  have htrace : (B ∩ E.pattern.root).card < r :=
    remainingBlocks_inter_root_card_lt E hB
  have hexists : ∀ g ∈ Q.powersetCard r,
      ∃ a ∈ B.powersetCard r, mapEdge phi a = g := by
    intro g hg
    have hg' : g ∈ Finset.map (Finset.mapEmbedding phi).toEmbedding
        (B.powersetCard r) := by
      rw [← Finset.powersetCard_map]
      exact hg
    obtain ⟨a, ha, hag⟩ := Finset.mem_map.mp hg'
    exact ⟨a, ha, hag⟩
  let pre (g : Finset (Fin n)) : Finset (Fin E.v) :=
    if hg : g ∈ Q.powersetCard r then Classical.choose (hexists g hg)
    else ∅
  have hpre_mem (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r) :
      pre g ∈ B.powersetCard r := by
    simp only [pre, dif_pos hg]
    exact (Classical.choose_spec (hexists g hg)).1
  have hpre_map (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r) :
      mapEdge phi (pre g) = g := by
    simp only [pre, dif_pos hg]
    exact (Classical.choose_spec (hexists g hg)).2
  have hpre_free (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r) :
      pre g ∈ E.pattern.freeEdges := by
    have hmem := hpre_mem g hg
    have hedge : pre g ∈ E.pattern.edges := hBedge hmem
    apply Finset.mem_filter.mpr
    refine ⟨hedge, ?_⟩
    intro hsub
    have hinterSub : pre g ⊆ B ∩ E.pattern.root := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp hmem).1 hx, hsub hx⟩
    have hcardLe := Finset.card_le_card hinterSub
    rw [(Finset.mem_powersetCard.mp hmem).2] at hcardLe
    omega
  let fallback : Fin u := Classical.choice inferInstance
  let color : Finset (Fin n) → Fin u := fun g ↦
    if hg : g ∈ Q.powersetCard r then
      freeColor ⟨pre g, hpre_free g hg⟩
    else fallback
  apply mem_rainbowBlocks.mpr
  refine ⟨hQcard, color, ?_, ?_⟩
  · intro g hg h hg' heq
    have hgm : g ∈ Q.powersetCard r := hg
    have hhm : h ∈ Q.powersetCard r := hg'
    have hpreEq : pre g = pre h := by
      exact congrArg Subtype.val (hfreeColor (by
        simpa only [color, dif_pos hgm, dif_pos hhm] using heq))
    rw [← hpre_map g hgm, ← hpre_map h hhm, hpreEq]
  · intro g hg
    have hgm : g ∈ Q.powersetCard r := hg
    simpa only [color, dif_pos hgm, hpre_map g hgm] using
      hfreeMem ⟨pre g, hpre_free g hgm⟩

theorem mappedSpecial_mem_rainbowBlocks
    {u n q r : ℕ} [Nonempty (Fin u)]
    (E : RelabeledFullExchange q r)
    (phi : Fin E.v ↪ Fin n)
    (Kstar : Fin u → Finset (Finset (Fin n)))
    (rootColor : Erdos722.Exchange.RootEdge q r → Fin u)
    (freeColor : ↑E.pattern.freeEdges → Fin u)
    (hfreeColor : Function.Injective freeColor)
    (hcolorsDisjoint : ∀ e a, rootColor e ≠ freeColor a)
    (hrootMem : ∀ e, mapEdge phi
      (Erdos722.Exchange.mappedRootEdge E.rootEmbedding e.1) ∈
        Kstar (rootColor e))
    (hfreeMem : ∀ a : ↑E.pattern.freeEdges,
      mapEdge phi a.1 ∈ Kstar (freeColor a))
    (e : Erdos722.Exchange.RootEdge q r) :
    mapEdge phi (E.special e) ∈ rainbowBlocks u n q r Kstar := by
  classical
  let B := E.special e
  let rootEdge := Erdos722.Exchange.mappedRootEdge E.rootEmbedding e.1
  let Q := mapEdge phi B
  have hBcard : B.card = q := E.negative_decomp.1 B (E.special_mem e)
  have hQcard : Q.card = q := (card_mapEdge phi B).trans hBcard
  have hBedge : B.powersetCard r ⊆ E.pattern.edges :=
    E.negative_decomp.2.1 B (E.special_mem e)
  have hrootEdgeCard : rootEdge.card = r := by
    simpa [rootEdge] using Erdos722.Exchange.card_mappedRootEdge
      E.rootEmbedding e.1
  have hinter : B ∩ E.pattern.root = rootEdge := by
    simpa [B, rootEdge, E.root_eq] using E.special_inter_root e
  have hexists : ∀ g ∈ Q.powersetCard r,
      ∃ a ∈ B.powersetCard r, mapEdge phi a = g := by
    intro g hg
    have hg' : g ∈ Finset.map (Finset.mapEmbedding phi).toEmbedding
        (B.powersetCard r) := by
      rw [← Finset.powersetCard_map]
      exact hg
    obtain ⟨a, ha, hag⟩ := Finset.mem_map.mp hg'
    exact ⟨a, ha, hag⟩
  let pre (g : Finset (Fin n)) : Finset (Fin E.v) :=
    if hg : g ∈ Q.powersetCard r then Classical.choose (hexists g hg)
    else ∅
  have hpre_mem (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r) :
      pre g ∈ B.powersetCard r := by
    simp only [pre, dif_pos hg]
    exact (Classical.choose_spec (hexists g hg)).1
  have hpre_map (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r) :
      mapEdge phi (pre g) = g := by
    simp only [pre, dif_pos hg]
    exact (Classical.choose_spec (hexists g hg)).2
  have hpre_root (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r)
      (hsub : pre g ⊆ E.pattern.root) : pre g = rootEdge := by
    have hmem := hpre_mem g hg
    have hsubInter : pre g ⊆ B ∩ E.pattern.root := by
      intro x hx
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp hmem).1 hx, hsub hx⟩
    rw [hinter] at hsubInter
    apply Finset.eq_of_subset_of_card_le hsubInter
    rw [(Finset.mem_powersetCard.mp hmem).2, hrootEdgeCard]
  have hpre_free (g : Finset (Fin n)) (hg : g ∈ Q.powersetCard r)
      (hnot : ¬pre g ⊆ E.pattern.root) : pre g ∈ E.pattern.freeEdges := by
    apply Finset.mem_filter.mpr
    exact ⟨hBedge (hpre_mem g hg), hnot⟩
  let fallback : Fin u := Classical.choice inferInstance
  let color : Finset (Fin n) → Fin u := fun g ↦
    if hg : g ∈ Q.powersetCard r then
      if hroot : pre g ⊆ E.pattern.root then rootColor e
      else freeColor ⟨pre g, hpre_free g hg hroot⟩
    else fallback
  apply mem_rainbowBlocks.mpr
  refine ⟨hQcard, color, ?_, ?_⟩
  · intro g hg h hg' heq
    have hgm : g ∈ Q.powersetCard r := hg
    have hhm : h ∈ Q.powersetCard r := hg'
    by_cases hgroot : pre g ⊆ E.pattern.root
    · by_cases hhroot : pre h ⊆ E.pattern.root
      · rw [← hpre_map g hgm, ← hpre_map h hhm,
          hpre_root g hgm hgroot, hpre_root h hhm hhroot]
      · exfalso
        exact hcolorsDisjoint e ⟨pre h, hpre_free h hhm hhroot⟩ (by
          simpa only [color, dif_pos hgm, dif_pos hhm,
            dif_pos hgroot, dif_neg hhroot] using heq)
    · by_cases hhroot : pre h ⊆ E.pattern.root
      · exfalso
        exact hcolorsDisjoint e ⟨pre g, hpre_free g hgm hgroot⟩ (by
          simpa only [color, dif_pos hgm, dif_pos hhm,
            dif_neg hgroot, dif_pos hhroot] using heq.symm)
      · have hpreEq : pre g = pre h := by
          exact congrArg Subtype.val (hfreeColor (by
            simpa only [color, dif_pos hgm, dif_pos hhm,
              dif_neg hgroot, dif_neg hhroot] using heq))
        rw [← hpre_map g hgm, ← hpre_map h hhm, hpreEq]
  · intro g hg
    have hgm : g ∈ Q.powersetCard r := hg
    by_cases hroot : pre g ⊆ E.pattern.root
    · have hEq := hpre_root g hgm hroot
      rw [show color g = rootColor e by
        simp only [color, dif_pos hgm, dif_pos hroot]]
      rw [← hpre_map g hgm, hEq]
      exact hrootMem e
    · rw [show color g = freeColor ⟨pre g, hpre_free g hgm hroot⟩ by
        simp only [color, dif_pos hgm, dif_neg hroot]]
      simpa only [hpre_map g hgm] using
        hfreeMem ⟨pre g, hpre_free g hgm hroot⟩

/-- Polynomially many `(root request, rainbow root colouring)` tasks can be
covered by one edge-cap-sized bank of fresh rotations. -/
theorem eventually_exists_prunedGenerator_specialCandidateRotationCover
    (N q r d Uexp : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (E : RelabeledFullExchange q r)
    (hbudget : Nat.choose q r *
      (Nat.choose q r - 1 + (remainingBlocks E).card) < d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : 0 < n)
        (omegaSample : {e // e ∈ Erdos722.Typicality.uniformEdges n r} → Bool)
        (D : Erdos722.Rotations.TwoCapPrunedData N n q r
          (Erdos722.GeneratorAsymptotic.generatorFaceCap d n)
          (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n)
          (Erdos722.GeneratorAsymptotic.generatorPruneThreshold q r d n)
          (Erdos722.GeneratorAsymptotic.generatorFaceCliqueCap q r d n)
          (Erdos722.GeneratorAsymptotic.generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ Erdos722.Typicality.rootFamilies n r
          (Nat.choose q r),
        Erdos722.Typicality.commonMean n roots
              (Erdos722.Reserve.reserveProbabilityIcc n d hn) / 2 <
            Erdos722.Probability.finiteRandomSum
              (fun x ↦ Erdos722.Typicality.commonNeighborIndicator n r roots
                (by omega)
                (Erdos722.Typicality.root_card_of_mem_rootFamilies hroots) x)
              omegaSample ∧
        Erdos722.Probability.finiteRandomSum
              (fun x ↦ Erdos722.Typicality.commonNeighborIndicator n r roots
                (by omega)
                (Erdos722.Typicality.root_card_of_mem_rootFamilies hroots) x)
              omegaSample <
            2 * Erdos722.Typicality.commonMean n roots
              (Erdos722.Reserve.reserveProbabilityIcc n d hn)) →
      D.K = Erdos722.Typicality.sampledEdges n r omegaSample →
      (Erdos722.Typicality.uniformEdges n (r - 1)).card *
          Erdos722.GeneratorAsymptotic.generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ (u : ℕ) (sigma : Fin u → Equiv.Perm (Fin n)),
      u ≤ n ^ Uexp →
      ∃ fresh : Fin (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n) →
          Fin (remainingBlocks E).card → Equiv.Perm (Fin n),
        ∀ (request : RootRequest E.v n E.pattern.root)
          (color : Erdos722.Exchange.RootEdge q r → Fin u),
        (∀ e, requestedRootEdge E request e ∈
          D.rotatedKstar sigma (color e)) →
        ∃ (t : Fin (Erdos722.GeneratorAsymptotic.generatorEdgeCap d n))
          (phi : Fin E.v ↪ Fin n),
          phi ∈ specialGoodEmbeddings E request
            (Erdos722.SpecialCliqueRotationAsymptotic.specialCliqueFamily
              D sigma color) ∧
          ∀ i, Erdos722.Rotations.rotateEdge (fresh t i).symm
              (mapEdge phi ((remainingBlocks E).equivFin.symm i).1) ∈
            Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D := by
  let m := (remainingBlocks E).card
  let blocks : Fin m → Finset (Fin E.v) := fun i ↦
    ((remainingBlocks E).equivFin.symm i).1
  let R := Erdos722.CliqueRotationAsymptotic.cliqueRotationPairConstant
    q r ^ m + 2
  let V := E.v + Uexp * Nat.choose q r
  have hR : 1 < R := by
    dsimp [R]
    omega
  have hfailure :=
    Erdos722.SpecialCliqueRotationAsymptotic.eventually_prunedGenerator_specialCandidateRotation_failure
      N q r d hr hrq hqd E hbudget
  have hunion :=
    Erdos722.RotationAsymptotic.eventually_polynomial_rotation_amplification_union_bound
      V d R (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn omegaSample D htyp hDK hmass u sigma hu
  let Request := RootRequest E.v n E.pattern.root
  letI : Fintype Request := Fintype.ofInjective RootRequest.map (by
    intro a b hab
    cases a with
    | mk amap ainj =>
      cases b with
      | mk bmap binj =>
        simp only [Request, RootRequest.map] at hab
        cases hab
        rfl)
  let Task := Request × (Erdos722.Exchange.RootEdge q r → Fin u)
  letI : DecidableEq Task := Classical.decEq Task
  let good (task : Task) : Prop :=
    ∀ e, requestedRootEdge E task.1 e ∈
      D.rotatedKstar sigma (task.2 e)
  let tasks : Finset Task := (Finset.univ : Finset Task).filter good
  let embeddings (task : Task) : Finset (Fin E.v ↪ Fin n) :=
    specialGoodEmbeddings E task.1
      (Erdos722.SpecialCliqueRotationAsymptotic.specialCliqueFamily
        D sigma task.2)
  have htaskCard : tasks.card ≤ n ^ V := by
    calc
      tasks.card ≤ Fintype.card Task := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card Request * u ^ Nat.choose q r := by
        simp [Task, Fintype.card_prod, Fintype.card_fun, card_rootEdge]
      _ ≤ n ^ E.v * (n ^ Uexp) ^ Nat.choose q r := by
        exact Nat.mul_le_mul
          (by
            rw [← Nat.card_eq_fintype_card]
            exact Erdos722.RotationAsymptotic.natCard_rootRequest_le_pow
              E.pattern.root)
          (Nat.pow_le_pow_left hu _)
      _ = n ^ V := by
        simp [V, pow_mul, pow_add]
  have hscaled : ∀ task ∈ tasks,
      R * ((Erdos722.Rotations.rotationSamples n m).filter fun fresh ↦
        Erdos722.Probability.finiteSuccessCount (embeddings task)
          (Erdos722.Rotations.rootedRotationSuccess
            (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)
            blocks) fresh = 0).card ≤
        (R - 1) * Fintype.card
          (Fin m → Equiv.Perm (Fin n)) := by
    intro task htask
    have hgood : good task := (Finset.mem_filter.mp htask).2
    simpa [R, m, blocks, embeddings, good] using
      hfailure hn omegaSample D htyp hDK hmass u sigma task.1 task.2 hgood
  have htaskUnion : tasks.card * (R - 1) ^
      Erdos722.GeneratorAsymptotic.generatorEdgeCap d n <
      R ^ Erdos722.GeneratorAsymptotic.generatorEdgeCap d n :=
    (Nat.mul_le_mul_right
      ((R - 1) ^ Erdos722.GeneratorAsymptotic.generatorEdgeCap d n)
      htaskCard).trans_lt hunion
  obtain ⟨fresh, hfresh⟩ :=
    Erdos722.CandidateCliqueRotation.exists_amplified_candidateRotationCover_of_scaled_bad
      tasks embeddings
      (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)
      blocks (by omega : 0 < R) hscaled htaskUnion
  refine ⟨fresh, ?_⟩
  intro request color hcolor
  have htask : (request, color) ∈ tasks := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hcolor⟩
  obtain ⟨t, phi, hphi, hsuccess⟩ := hfresh (request, color) htask
  exact ⟨t, phi, hphi, hsuccess⟩

end

end Erdos722
