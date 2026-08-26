import ErdosProblems.Erdos538.FixedChildGlobalCount
import ErdosProblems.Erdos538.FiniteAveraging

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

noncomputable section

/-- Canonical equivalence between the normalized-child coordinates and a
`d+1` element finite type. -/
def optionFinEquiv (d : ℕ) : Option (Fin d) ≃ Fin (d + 1) where
  toFun
    | none => 0
    | some i => i.succ
  invFun := Fin.cases none (fun i => some i)
  left_inv x := by cases x <;> rfl
  right_inv x := Fin.cases rfl (fun _ => rfl) x

/-- The type of `(d+1)`-subsets of an `m`-point ground set. -/
abbrev UniformChildren (m d : ℕ) :=
  {S : Finset (Fin m) // S.card = d + 1}

/-- A deterministic ordering of one child. -/
def childEquiv {m d : ℕ} (S : UniformChildren m d) :
    Option (Fin d) ≃ S.1 :=
  (optionFinEquiv d).trans (Finset.equivFinOfCardEq S.2).symm

/-- A deterministic ordering of the complement of one child. -/
def outsideEquiv {m d : ℕ} (S : UniformChildren m d) :
    Fin (m - (d + 1)) ≃ {v : Fin m // v ∉ S.1} := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, Fintype.card_subtype_compl]
  simp [S.2]

/-- One row/coefficient label. -/
abbrev VertexLabel (K : Type*) (d : ℕ) := (Fin d → K) × K

/-- All labels on an `m`-point ground set. -/
abbrev GlobalSample (K : Type*) (m d : ℕ) := Fin m → VertexLabel K d

/-- Combine a child sample and its outside labels into a global assignment. -/
def assembleGlobal
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (a : ChildSample K d ×
      (Fin (m - (d + 1)) → VertexLabel K d)) :
    GlobalSample K m d := fun v =>
  if hv : v ∈ S.1 then
    let o := (childEquiv S).symm ⟨v, hv⟩
    (a.1.1 o, a.1.2 o)
  else
    a.2 ((outsideEquiv S).symm ⟨v, by simpa using hv⟩)

/-- Recover the child and outside parts of a global assignment. -/
def disassembleGlobal
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (ω : GlobalSample K m d) :
    ChildSample K d × (Fin (m - (d + 1)) → VertexLabel K d) :=
  ((fun o => (ω ((childEquiv S o).1)).1,
    fun o => (ω ((childEquiv S o).1)).2),
   fun i => ω ((outsideEquiv S i).1))

@[simp] theorem assembleGlobal_child
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (a : ChildSample K d ×
      (Fin (m - (d + 1)) → VertexLabel K d))
    (o : Option (Fin d)) :
    assembleGlobal S a (childEquiv S o).1 = (a.1.1 o, a.1.2 o) := by
  simp [assembleGlobal, (childEquiv S o).2]

@[simp] theorem assembleGlobal_outside
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (a : ChildSample K d ×
      (Fin (m - (d + 1)) → VertexLabel K d))
    (i : Fin (m - (d + 1))) :
    assembleGlobal S a (outsideEquiv S i).1 = a.2 i := by
  have hi : (outsideEquiv S i).1 ∉ S.1 := (outsideEquiv S i).2
  rw [assembleGlobal, dif_neg hi]
  congr
  have hx : (⟨(outsideEquiv S i).1, hi⟩ : {v : Fin m // v ∉ S.1}) =
      outsideEquiv S i := Subtype.ext (by rfl)
  rw [hx, (outsideEquiv S).symm_apply_apply]

@[simp] theorem disassemble_assembleGlobal
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (a : ChildSample K d ×
      (Fin (m - (d + 1)) → VertexLabel K d)) :
    disassembleGlobal S (assembleGlobal S a) = a := by
  apply Prod.ext
  · apply Prod.ext <;> funext o
    · exact congrArg Prod.fst (assembleGlobal_child S a o)
    · exact congrArg Prod.snd (assembleGlobal_child S a o)
  · funext i
    exact assembleGlobal_outside S a i

@[simp] theorem assemble_disassembleGlobal
    {K : Type*} {m d : ℕ} (S : UniformChildren m d)
    (ω : GlobalSample K m d) :
    assembleGlobal S (disassembleGlobal S ω) = ω := by
  funext v
  by_cases hv : v ∈ S.1
  · let x : S.1 := ⟨v, hv⟩
    let o := (childEquiv S).symm x
    have hvo : (childEquiv S o).1 = v := by
      exact congrArg Subtype.val ((childEquiv S).apply_symm_apply x)
    simp [assembleGlobal, disassembleGlobal, hv, o, hvo]
  · let x : {u : Fin m // u ∉ S.1} := ⟨v, hv⟩
    let i := (outsideEquiv S).symm x
    have hvi : (outsideEquiv S i).1 = v := by
      exact congrArg Subtype.val ((outsideEquiv S).apply_symm_apply x)
    simp [assembleGlobal, disassembleGlobal, hv, i, hvi]

/-- Child/outside decomposition is an actual equivalence, so no sample mass is
lost when the fixed-child count is transported to the common global space. -/
def globalDecompositionEquiv
    {K : Type*} {m d : ℕ} (S : UniformChildren m d) :
    (ChildSample K d ×
      (Fin (m - (d + 1)) → VertexLabel K d)) ≃
      GlobalSample K m d where
  toFun := assembleGlobal S
  invFun := disassembleGlobal S
  left_inv := disassemble_assembleGlobal S
  right_inv := assemble_disassembleGlobal S

/-- Embed the safe favorable fixed-child parameters into common global label
assignments. -/
def safeGlobalEmbedding
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (S : UniformChildren m d) :
    SafeGlobalParam K d (m - (d + 1)) ↪ GlobalSample K m d where
  toFun z := assembleGlobal S (safeGlobalParamToSample z)
  inj' := (globalDecompositionEquiv S).injective.comp
    safeGlobalParamToSample_injective

/-- Under the fixed-child density hypotheses, every child embeds at least a
`1/(16q)` share of the common global sample space. -/
theorem globalSample_le_sixteen_q_safeParams
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (S : UniformChildren m d) (hd : 0 < d)
    (hqsize : 2 * (d + 1) ≤ Fintype.card K)
    (houtside : 2 * (m - (d + 1)) ≤ (Nat.card K) ^ 2) :
    Nat.card (GlobalSample K m d) ≤
      16 * Fintype.card K *
        Nat.card (SafeGlobalParam K d (m - (d + 1))) := by
  rw [← Nat.card_congr (globalDecompositionEquiv S)]
  rw [Nat.card_prod, Nat.card_fun]
  simpa using sixteen_q_mul_safeGlobal_ge_all hd hqsize houtside

/-- Every safe outside subtype is finite by its injection into the finite
function space. -/
instance safeOutsideFinite
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d t : ℕ} (p : GoodParam K d) : Finite (SafeOutside p t) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance goodParamFintype
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ} :
    Fintype (GoodParam K d) := Fintype.ofFinite _

noncomputable instance safeOutsideFintype
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d t : ℕ} (p : GoodParam K d) : Fintype (SafeOutside p t) :=
  Fintype.ofFinite _

noncomputable instance safeGlobalParamFintype
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d t : ℕ} :
    Fintype (SafeGlobalParam K d t) := Fintype.ofFinite _

/-- Finite averaging supplies one global label assignment that lies in the
safe parameter range for at least a `1/(16q)` fraction of all children. -/
theorem exists_globalSample_many_safe_children
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} (hd : 0 < d)
    (hqsize : 2 * (d + 1) ≤ Fintype.card K)
    (houtside : 2 * (m - (d + 1)) ≤ (Nat.card K) ^ 2) :
    ∃ ω : GlobalSample K m d,
      Fintype.card (UniformChildren m d) ≤
        (16 * Fintype.card K) *
          (Finset.univ.filter fun S =>
            ω ∈ Set.range (safeGlobalEmbedding S)).card := by
  classical
  let Sel : GlobalSample K m d → UniformChildren m d → Prop :=
    fun ω S => ω ∈ Set.range (safeGlobalEmbedding S)
  apply exists_sample_many Sel (16 * Fintype.card K)
  intro S
  have hcard := globalSample_le_sixteen_q_safeParams S hd hqsize houtside
  let emb : SafeGlobalParam K d (m - (d + 1)) ↪ GlobalSample K m d :=
    safeGlobalEmbedding S
  let image : Finset (GlobalSample K m d) := Finset.univ.image emb
  have himage : image = Finset.univ.filter fun ω => Sel ω S := by
    ext ω
    simp only [image, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter, Sel, Set.mem_range]
    exact ⟨fun ⟨p, hp⟩ => ⟨p, by simpa [emb] using hp⟩,
      fun ⟨p, hp⟩ => ⟨p, by simpa [emb] using hp⟩⟩
  rw [← himage, Finset.card_image_of_injective Finset.univ emb.injective]
  simpa [Nat.card_eq_fintype_card] using hcard

end

end Erdos538.IsotropicKernel
