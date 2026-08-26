import ErdosProblems.Erdos118.Reused591.CounterexampleTransport

namespace Erdos118.Reused591

namespace Erdos591.Negative

/-- A numerical coordinate together with the information that it is a box
coordinate in the height-two good-sequence presentation. -/
structure TaggedCoord where
  value : ℕ
  box : Bool
  deriving DecidableEq

/-- Every numerical coordinate in `s` is below every numerical coordinate
in `t`. -/
def AllLT (s t : List TaggedCoord) : Prop :=
  ∀ a ∈ s, ∀ b ∈ t, a.value < b.value

theorem AllLT.mem {s t : List TaggedCoord} (h : AllLT s t)
    {a b : TaggedCoord} (ha : a ∈ s) (hb : b ∈ t) :
    a.value < b.value := h a ha b hb

theorem AllLT.trans {r s t : List TaggedCoord} (hrs : AllLT r s)
    (hst : AllLT s t) (hs : s ≠ []) : AllLT r t := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil s hs
  intro a ha c hc
  exact (hrs.mem ha hb).trans (hst.mem hb hc)

theorem AllLT.append_left {r s t : List TaggedCoord} :
    AllLT (r ++ s) t ↔ AllLT r t ∧ AllLT s t := by
  simp only [AllLT, List.mem_append, or_imp, forall_and]

theorem AllLT.append_right {r s t : List TaggedCoord} :
    AllLT r (s ++ t) ↔ AllLT r s ∧ AllLT r t := by
  constructor
  · intro h
    exact ⟨fun a ha b hb ↦ h a ha b (List.mem_append_left _ hb),
      fun a ha b hb ↦ h a ha b (List.mem_append_right _ hb)⟩
  · rintro ⟨hrs, hrt⟩ a ha b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hrs a ha b hb
    · exact hrt a ha b hb

def HasBox (s : List TaggedCoord) : Prop :=
  ∃ a ∈ s, a.box = true

def NoBox (s : List TaggedCoord) : Prop :=
  ∀ a ∈ s, a.box = false

theorem HasBox.not_noBox {s : List TaggedCoord} (h : HasBox s) :
    ¬ NoBox s := by
  rintro hn
  rcases h with ⟨a, ha, hbox⟩
  rw [hn a ha] at hbox
  simp at hbox

/-- A nonempty five-piece consecutive decomposition. -/
structure Split5 (s : List TaggedCoord) where
  p0 : List TaggedCoord
  p1 : List TaggedCoord
  p2 : List TaggedCoord
  p3 : List TaggedCoord
  p4 : List TaggedCoord
  eq_append : s = p0 ++ p1 ++ p2 ++ p3 ++ p4
  ne0 : p0 ≠ []
  ne1 : p1 ≠ []
  ne2 : p2 ≠ []
  ne3 : p3 ≠ []
  ne4 : p4 ≠ []

/-- A nonempty four-piece consecutive decomposition. -/
structure Split4 (s : List TaggedCoord) where
  p0 : List TaggedCoord
  p1 : List TaggedCoord
  p2 : List TaggedCoord
  p3 : List TaggedCoord
  eq_append : s = p0 ++ p1 ++ p2 ++ p3
  ne0 : p0 ≠ []
  ne1 : p1 ≠ []
  ne2 : p2 ≠ []
  ne3 : p3 ≠ []

theorem Split5.mem_cases {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (ha : a ∈ s) :
    a ∈ P.p0 ∨ a ∈ P.p1 ∨ a ∈ P.p2 ∨ a ∈ P.p3 ∨ a ∈ P.p4 := by
  rw [P.eq_append] at ha
  simp only [List.mem_append] at ha
  aesop

theorem Split4.mem_cases {s : List TaggedCoord} (P : Split4 s)
    {a : TaggedCoord} (ha : a ∈ s) :
    a ∈ P.p0 ∨ a ∈ P.p1 ∨ a ∈ P.p2 ∨ a ∈ P.p3 := by
  rw [P.eq_append] at ha
  simp only [List.mem_append] at ha
  aesop

theorem Split5.mem0 {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (h : a ∈ P.p0) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show (((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3) ∨
      a ∈ P.p4 from Or.inl (Or.inl (Or.inl (Or.inl h))))

theorem Split5.mem1 {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (h : a ∈ P.p1) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show (((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3) ∨
      a ∈ P.p4 from Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem Split5.mem2 {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (h : a ∈ P.p2) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show (((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3) ∨
      a ∈ P.p4 from Or.inl (Or.inl (Or.inr h)))

theorem Split5.mem3 {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (h : a ∈ P.p3) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show (((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3) ∨
      a ∈ P.p4 from Or.inl (Or.inr h))

theorem Split5.mem4 {s : List TaggedCoord} (P : Split5 s)
    {a : TaggedCoord} (h : a ∈ P.p4) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show (((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3) ∨
      a ∈ P.p4 from Or.inr h)

theorem Split4.mem0 {s : List TaggedCoord} (P : Split4 s)
    {a : TaggedCoord} (h : a ∈ P.p0) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show ((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3 from
      Or.inl (Or.inl (Or.inl h)))

theorem Split4.mem1 {s : List TaggedCoord} (P : Split4 s)
    {a : TaggedCoord} (h : a ∈ P.p1) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show ((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3 from
      Or.inl (Or.inl (Or.inr h)))

theorem Split4.mem2 {s : List TaggedCoord} (P : Split4 s)
    {a : TaggedCoord} (h : a ∈ P.p2) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show ((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3 from
      Or.inl (Or.inr h))

theorem Split4.mem3 {s : List TaggedCoord} (P : Split4 s)
    {a : TaggedCoord} (h : a ∈ P.p3) : a ∈ s := by
  simpa only [P.eq_append, List.mem_append] using
    (show ((a ∈ P.p0 ∨ a ∈ P.p1) ∨ a ∈ P.p2) ∨ a ∈ P.p3 from Or.inr h)

/-- The oriented nine-block interlacing pattern of Hajnal--Larson,
Definition 9.19.  `x` supplies five blocks and `y` four. -/
structure InterlacingWitness (x y : List TaggedCoord) where
  X : Split5 x
  Y : Split4 y
  x0_y0 : AllLT X.p0 Y.p0
  y0_x1 : AllLT Y.p0 X.p1
  x1_y1 : AllLT X.p1 Y.p1
  y1_x2 : AllLT Y.p1 X.p2
  x2_y2 : AllLT X.p2 Y.p2
  y2_x3 : AllLT Y.p2 X.p3
  x3_y3 : AllLT X.p3 Y.p3
  y3_x4 : AllLT Y.p3 X.p4
  box_x0 : HasBox X.p0
  box_x2 : HasBox X.p2
  box_x4 : HasBox X.p4
  box_y0 : HasBox Y.p0
  box_y3 : HasBox Y.p3
  noBox_x1 : NoBox X.p1
  noBox_x3 : NoBox X.p3
  noBox_y1 : NoBox Y.p1
  noBox_y2 : NoBox Y.p2

structure SegmentBlock where
  coords : List TaggedCoord
  nonempty : coords ≠ []

def BlockLT (a b : SegmentBlock) : Prop := AllLT a.coords b.coords

instance blockLTTrans : Trans BlockLT BlockLT BlockLT where
  trans := fun {a b c} h₁ h₂ ↦ h₁.trans h₂ b.nonempty

def InterlacingWitness.blockList {x y : List TaggedCoord}
    (w : InterlacingWitness x y) : List SegmentBlock :=
  [⟨w.X.p0, w.X.ne0⟩, ⟨w.Y.p0, w.Y.ne0⟩,
   ⟨w.X.p1, w.X.ne1⟩, ⟨w.Y.p1, w.Y.ne1⟩,
   ⟨w.X.p2, w.X.ne2⟩, ⟨w.Y.p2, w.Y.ne2⟩,
   ⟨w.X.p3, w.X.ne3⟩, ⟨w.Y.p3, w.Y.ne3⟩,
   ⟨w.X.p4, w.X.ne4⟩]

theorem InterlacingWitness.blockList_chain {x y : List TaggedCoord}
    (w : InterlacingWitness x y) :
    w.blockList.IsChain BlockLT := by
  simp [InterlacingWitness.blockList, BlockLT, w.x0_y0, w.y0_x1,
    w.x1_y1, w.y1_x2, w.x2_y2, w.y2_x3, w.x3_y3, w.y3_x4]

def InterlacingWitness.blockAt {x y : List TaggedCoord}
    (w : InterlacingWitness x y) (i : Fin 9) : SegmentBlock :=
  w.blockList.get ⟨i, by simpa [InterlacingWitness.blockList] using i.isLt⟩

def InterlacingWitness.InBlock {x y : List TaggedCoord}
    (w : InterlacingWitness x y) (a : TaggedCoord) (i : Fin 9) : Prop :=
  a ∈ (w.blockAt i).coords

theorem InterlacingWitness.blockAt_lt {x y : List TaggedCoord}
    (w : InterlacingWitness x y) {i j : Fin 9} (hij : i < j) :
    BlockLT (w.blockAt i) (w.blockAt j) := by
  let ii : Fin w.blockList.length :=
    ⟨i, by simpa [InterlacingWitness.blockList] using i.isLt⟩
  let jj : Fin w.blockList.length :=
    ⟨j, by simpa [InterlacingWitness.blockList] using j.isLt⟩
  have hij' : ii < jj := hij
  exact w.blockList_chain.pairwise.rel_get_of_lt hij'

theorem InterlacingWitness.index_lt_of_value_lt
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a b : TaggedCoord} {i j : Fin 9}
    (ha : w.InBlock a i) (hb : w.InBlock b j)
    (hab : a.value < b.value) (hij : i ≠ j) : i < j := by
  rcases lt_trichotomy i j with h | h | h
  · exact h
  · exact (hij h).elim
  · have hba := (w.blockAt_lt h).mem hb ha
    omega

theorem InterlacingWitness.first_mem_even_block
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a : TaggedCoord} (ha : a ∈ x) :
    ∃ i : Fin 9, i.val % 2 = 0 ∧ w.InBlock a i := by
  rcases w.X.mem_cases ha with h0 | h1 | h2 | h3 | h4
  · exact ⟨0, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h0⟩
  · exact ⟨2, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h1⟩
  · exact ⟨4, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h2⟩
  · exact ⟨6, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h3⟩
  · exact ⟨8, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h4⟩

theorem InterlacingWitness.second_mem_odd_block
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a : TaggedCoord} (ha : a ∈ y) :
    ∃ i : Fin 9, i.val % 2 = 1 ∧ w.InBlock a i := by
  rcases w.Y.mem_cases ha with h0 | h1 | h2 | h3
  · exact ⟨1, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h0⟩
  · exact ⟨3, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h1⟩
  · exact ⟨5, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h2⟩
  · exact ⟨7, by decide, by
      simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
        InterlacingWitness.blockList] using h3⟩

/-- There are only two blocks strictly between `X₂` and `Y₃`; hence
three alternating coordinates cannot fit there. -/
theorem InterlacingWitness.no_forward_three_alternations
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {e₀ e₁ e₂ f₀ f₁ f₂ : TaggedCoord}
    (he₀ : e₀ ∈ w.X.p2) (he₁ : e₁ ∈ x) (he₂ : e₂ ∈ x)
    (hf₀ : f₀ ∈ y) (hf₁ : f₁ ∈ y) (hf₂ : f₂ ∈ w.Y.p3)
    (h₀ : e₀.value < f₀.value) (h₁ : f₀.value < e₁.value)
    (h₂ : e₁.value < f₁.value) (h₃ : f₁.value < e₂.value)
    (h₄ : e₂.value < f₂.value) : False := by
  obtain ⟨ie₁, hie₁even, hie₁⟩ := w.first_mem_even_block he₁
  obtain ⟨ie₂, hie₂even, hie₂⟩ := w.first_mem_even_block he₂
  obtain ⟨if₀, hif₀odd, hif₀⟩ := w.second_mem_odd_block hf₀
  obtain ⟨if₁, hif₁odd, hif₁⟩ := w.second_mem_odd_block hf₁
  have he₀block : w.InBlock e₀ 4 := by
    simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
      InterlacingWitness.blockList] using he₀
  have hf₂block : w.InBlock f₂ 7 := by
    simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
      InterlacingWitness.blockList] using hf₂
  have hi₀ : (4 : Fin 9) < if₀ :=
    w.index_lt_of_value_lt he₀block hif₀ h₀ (by intro h; subst if₀; omega)
  have hi₁ : if₀ < ie₁ :=
    w.index_lt_of_value_lt hif₀ hie₁ h₁ (by intro h; subst ie₁; omega)
  have hi₂ : ie₁ < if₁ :=
    w.index_lt_of_value_lt hie₁ hif₁ h₂ (by intro h; subst if₁; omega)
  have hi₃ : if₁ < ie₂ :=
    w.index_lt_of_value_lt hif₁ hie₂ h₃ (by intro h; subst ie₂; omega)
  have hi₄ : ie₂ < (7 : Fin 9) :=
    w.index_lt_of_value_lt hie₂ hf₂block h₄ (by intro h; subst ie₂; omega)
  omega

/-- Dually, there are only two blocks strictly between `Y₀` and `X₂`. -/
theorem InterlacingWitness.no_backward_three_alternations
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {e₀ e₁ e₂ f₀ f₁ f₂ : TaggedCoord}
    (hf₀ : f₀ ∈ w.Y.p0) (hf₁ : f₁ ∈ y) (hf₂ : f₂ ∈ y)
    (he₀ : e₀ ∈ x) (he₁ : e₁ ∈ x) (he₂ : e₂ ∈ w.X.p2)
    (h₀ : f₀.value < e₀.value) (h₁ : e₀.value < f₁.value)
    (h₂ : f₁.value < e₁.value) (h₃ : e₁.value < f₂.value)
    (h₄ : f₂.value < e₂.value) : False := by
  obtain ⟨ie₀, hie₀even, hie₀⟩ := w.first_mem_even_block he₀
  obtain ⟨ie₁, hie₁even, hie₁⟩ := w.first_mem_even_block he₁
  obtain ⟨if₁, hif₁odd, hif₁⟩ := w.second_mem_odd_block hf₁
  obtain ⟨if₂, hif₂odd, hif₂⟩ := w.second_mem_odd_block hf₂
  have hf₀block : w.InBlock f₀ 1 := by
    simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
      InterlacingWitness.blockList] using hf₀
  have he₂block : w.InBlock e₂ 4 := by
    simpa [InterlacingWitness.InBlock, InterlacingWitness.blockAt,
      InterlacingWitness.blockList] using he₂
  have hi₀ : (1 : Fin 9) < ie₀ :=
    w.index_lt_of_value_lt hf₀block hie₀ h₀ (by intro h; subst ie₀; omega)
  have hi₁ : ie₀ < if₁ :=
    w.index_lt_of_value_lt hie₀ hif₁ h₁ (by intro h; subst if₁; omega)
  have hi₂ : if₁ < ie₁ :=
    w.index_lt_of_value_lt hif₁ hie₁ h₂ (by intro h; subst ie₁; omega)
  have hi₃ : ie₁ < if₂ :=
    w.index_lt_of_value_lt hie₁ hif₂ h₃ (by intro h; subst if₂; omega)
  have hi₄ : if₂ < (4 : Fin 9) :=
    w.index_lt_of_value_lt hif₂ he₂block h₄ (by intro h; subst if₂; omega)
  omega

def Interlaces (x y : List TaggedCoord) : Prop :=
  Nonempty (InterlacingWitness x y)

/-- Symmetrization and diagonal removal turn the oriented interlacing
pattern into a simple graph on any family of tagged sequences. -/
def interlacingGraph {V : Type*} (seq : V → List TaggedCoord) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ Interlaces (seq x) (seq y)

theorem interlacingGraph_adj {V : Type*} (seq : V → List TaggedCoord)
    (x y : V) :
    (interlacingGraph seq).Adj x y ↔
      x ≠ y ∧ (Interlaces (seq x) (seq y) ∨
        Interlaces (seq y) (seq x)) := by
  exact SimpleGraph.fromRel_adj _ _ _

/-- A tagged coordinate occurs in the sequence and is a box coordinate. -/
def IsBoxCoord (s : List TaggedCoord) (a : TaggedCoord) : Prop :=
  a ∈ s ∧ a.box = true

/-- A numerical value occurs strictly between two coordinates of `s`. -/
def Inside (s : List TaggedCoord) (q : TaggedCoord) : Prop :=
  ∃ lo ∈ s, ∃ hi ∈ s, lo.value < q.value ∧ q.value < hi.value

theorem InterlacingWitness.middle_box_inside
    {x y : List TaggedCoord} (w : InterlacingWitness x y) :
    ∃ q, IsBoxCoord x q ∧ Inside y q := by
  rcases w.box_x2 with ⟨q, hq, hqbox⟩
  obtain ⟨lo, hlo⟩ := List.exists_mem_of_ne_nil w.Y.p1 w.Y.ne1
  obtain ⟨hi, hhi⟩ := List.exists_mem_of_ne_nil w.Y.p2 w.Y.ne2
  refine ⟨q, ?_, lo, ?_, hi, ?_, ?_, ?_⟩
  · constructor
    · rw [w.X.eq_append]
      simp only [List.mem_append]
      aesop
    · exact hqbox
  · rw [w.Y.eq_append]
    simp only [List.mem_append]
    aesop
  · rw [w.Y.eq_append]
    simp only [List.mem_append]
    aesop
  · exact w.y1_x2.mem hlo hq
  · exact w.x2_y2.mem hq hhi

theorem InterlacingWitness.x0_before_y
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a b : TaggedCoord} (ha : a ∈ w.X.p0) (hb : b ∈ y) :
    a.value < b.value := by
  rcases w.Y.mem_cases hb with hb | hb | hb | hb
  · exact w.x0_y0.mem ha hb
  · exact (((w.x0_y0.trans w.y0_x1 w.Y.ne0).trans
      w.x1_y1 w.X.ne1).mem ha hb)
  · exact (((((w.x0_y0.trans w.y0_x1 w.Y.ne0).trans
      w.x1_y1 w.X.ne1).trans w.y1_x2 w.Y.ne1).trans
      w.x2_y2 w.X.ne2).mem ha hb)
  · exact (((((((w.x0_y0.trans w.y0_x1 w.Y.ne0).trans
      w.x1_y1 w.X.ne1).trans w.y1_x2 w.Y.ne1).trans
      w.x2_y2 w.X.ne2).trans w.y2_x3 w.Y.ne2).trans
      w.x3_y3 w.X.ne3).mem ha hb)

theorem InterlacingWitness.y_before_x4
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a b : TaggedCoord} (ha : a ∈ y) (hb : b ∈ w.X.p4) :
    a.value < b.value := by
  rcases w.Y.mem_cases ha with ha | ha | ha | ha
  · exact (((((((w.y0_x1.trans w.x1_y1 w.X.ne1).trans
      w.y1_x2 w.Y.ne1).trans w.x2_y2 w.X.ne2).trans
      w.y2_x3 w.Y.ne2).trans w.x3_y3 w.X.ne3).trans
      w.y3_x4 w.Y.ne3).mem ha hb)
  · exact (((((w.y1_x2.trans w.x2_y2 w.X.ne2).trans
      w.y2_x3 w.Y.ne2).trans w.x3_y3 w.X.ne3).trans
      w.y3_x4 w.Y.ne3).mem ha hb)
  · exact (((w.y2_x3.trans w.x3_y3 w.X.ne3).trans
      w.y3_x4 w.Y.ne3).mem ha hb)
  · exact w.y3_x4.mem ha hb

theorem InterlacingWitness.y0_before_x_tail
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a b : TaggedCoord} (ha : a ∈ w.Y.p0)
    (hb : b ∈ w.X.p1 ∨ b ∈ w.X.p2 ∨ b ∈ w.X.p3 ∨ b ∈ w.X.p4) :
    a.value < b.value := by
  rcases hb with hb | hb | hb | hb
  · exact w.y0_x1.mem ha hb
  · exact (((w.y0_x1.trans w.x1_y1 w.X.ne1).trans
      w.y1_x2 w.Y.ne1).mem ha hb)
  · exact (((((w.y0_x1.trans w.x1_y1 w.X.ne1).trans
      w.y1_x2 w.Y.ne1).trans w.x2_y2 w.X.ne2).trans
      w.y2_x3 w.Y.ne2).mem ha hb)
  · exact (((((((w.y0_x1.trans w.x1_y1 w.X.ne1).trans
      w.y1_x2 w.Y.ne1).trans w.x2_y2 w.X.ne2).trans
      w.y2_x3 w.Y.ne2).trans w.x3_y3 w.X.ne3).trans
      w.y3_x4 w.Y.ne3).mem ha hb)

theorem InterlacingWitness.x_head_before_y3
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {a b : TaggedCoord}
    (ha : a ∈ w.X.p0 ∨ a ∈ w.X.p1 ∨ a ∈ w.X.p2 ∨ a ∈ w.X.p3)
    (hb : b ∈ w.Y.p3) : a.value < b.value := by
  rcases ha with ha | ha | ha | ha
  · exact (((((((w.x0_y0.trans w.y0_x1 w.Y.ne0).trans
      w.x1_y1 w.X.ne1).trans w.y1_x2 w.Y.ne1).trans
      w.x2_y2 w.X.ne2).trans w.y2_x3 w.Y.ne2).trans
      w.x3_y3 w.X.ne3).mem ha hb)
  · exact (((((w.x1_y1.trans w.y1_x2 w.Y.ne1).trans
      w.x2_y2 w.X.ne2).trans w.y2_x3 w.Y.ne2).trans
      w.x3_y3 w.X.ne3).mem ha hb)
  · exact (((w.x2_y2.trans w.y2_x3 w.Y.ne2).trans
      w.x3_y3 w.X.ne3).mem ha hb)
  · exact w.x3_y3.mem ha hb

/-- Claim A(2): a box coordinate of the five-block sequence which lies
inside the numerical interval of the four-block sequence must lie in the
middle box block. -/
theorem InterlacingWitness.box_mem_middle_of_inside
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {q : TaggedCoord} (hq : IsBoxCoord x q) (hin : Inside y q) :
    q ∈ w.X.p2 := by
  rcases hq with ⟨hqx, hqbox⟩
  rcases hin with ⟨lo, hlo, hi, hhi, hloq, hqhi⟩
  rcases w.X.mem_cases hqx with h0 | h1 | h2 | h3 | h4
  · exact (Nat.not_lt_of_ge (w.x0_before_y h0 hlo).le hloq).elim
  · have := w.noBox_x1 q h1
    simp [hqbox] at this
  · exact h2
  · have := w.noBox_x3 q h3
    simp [hqbox] at this
  · exact (Nat.not_lt_of_ge (w.y_before_x4 hhi h4).le hqhi).elim

/-- Claim A(3), in a form avoiding explicit minima and maxima. -/
theorem InterlacingWitness.no_y_box_between_x_inside
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {p q r lo hi : TaggedCoord}
    (hp : p ∈ x) (hq : IsBoxCoord y q) (hr : r ∈ x)
    (hlo : lo ∈ y) (hhi : hi ∈ y)
    (hchain : lo.value < p.value ∧ p.value < q.value ∧
      q.value < r.value ∧ r.value < hi.value) : False := by
  rcases hq with ⟨hqy, hqbox⟩
  rcases w.Y.mem_cases hqy with hq0 | hq1 | hq2 | hq3
  · rcases w.X.mem_cases hp with hp0 | hp1 | hp2 | hp3 | hp4
    · exact (Nat.not_lt_of_ge (w.x0_before_y hp0 hlo).le hchain.1).elim
    · exact (Nat.not_lt_of_ge (w.y0_before_x_tail hq0 (Or.inl hp1)).le
        hchain.2.1).elim
    · exact (Nat.not_lt_of_ge (w.y0_before_x_tail hq0 (Or.inr (Or.inl hp2))).le
        hchain.2.1).elim
    · exact (Nat.not_lt_of_ge
        (w.y0_before_x_tail hq0 (Or.inr (Or.inr (Or.inl hp3)))).le
        hchain.2.1).elim
    · exact (Nat.not_lt_of_ge
        (w.y0_before_x_tail hq0 (Or.inr (Or.inr (Or.inr hp4)))).le
        hchain.2.1).elim
  · have := w.noBox_y1 q hq1
    simp [hqbox] at this
  · have := w.noBox_y2 q hq2
    simp [hqbox] at this
  · rcases w.X.mem_cases hr with hr0 | hr1 | hr2 | hr3 | hr4
    · exact (Nat.not_lt_of_ge
        (w.x_head_before_y3 (Or.inl hr0) hq3).le hchain.2.2.1).elim
    · exact (Nat.not_lt_of_ge
        (w.x_head_before_y3 (Or.inr (Or.inl hr1)) hq3).le hchain.2.2.1).elim
    · exact (Nat.not_lt_of_ge
        (w.x_head_before_y3 (Or.inr (Or.inr (Or.inl hr2))) hq3).le
        hchain.2.2.1).elim
    · exact (Nat.not_lt_of_ge
        (w.x_head_before_y3 (Or.inr (Or.inr (Or.inr hr3))) hq3).le
        hchain.2.2.1).elim
    · exact (Nat.not_lt_of_ge (w.y_before_x4 hhi hr4).le hchain.2.2.2).elim

/-- The numerical interval of the four-block sequence is nested inside the
interval of the five-block sequence. -/
theorem InterlacingWitness.inside_first_of_inside_second
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {q : TaggedCoord} (hq : Inside y q) : Inside x q := by
  rcases hq with ⟨lo, hlo, hi, hhi, hloq, hqhi⟩
  obtain ⟨xlo, hxlo⟩ := List.exists_mem_of_ne_nil w.X.p0 w.X.ne0
  obtain ⟨xhi, hxhi⟩ := List.exists_mem_of_ne_nil w.X.p4 w.X.ne4
  refine ⟨xlo, ?_, xhi, ?_, ?_, ?_⟩
  · rw [w.X.eq_append]
    simp only [List.mem_append]
    aesop
  · rw [w.X.eq_append]
    simp only [List.mem_append]
    aesop
  · exact (w.x0_before_y hxlo hlo).trans hloq
  · exact hqhi.trans (w.y_before_x4 hhi hxhi)

theorem InterlacingWitness.second_mem_inside_first
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {q : TaggedCoord} (hq : q ∈ y) : Inside x q := by
  obtain ⟨xlo, hxlo⟩ := List.exists_mem_of_ne_nil w.X.p0 w.X.ne0
  obtain ⟨xhi, hxhi⟩ := List.exists_mem_of_ne_nil w.X.p4 w.X.ne4
  refine ⟨xlo, ?_, xhi, ?_, w.x0_before_y hxlo hq,
    w.y_before_x4 hq hxhi⟩
  · rw [w.X.eq_append]
    simp only [List.mem_append]
    aesop
  · rw [w.X.eq_append]
    simp only [List.mem_append]
    aesop

theorem InterlacingWitness.x1_mem_inside_second
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {q : TaggedCoord} (hq : q ∈ w.X.p1) : Inside y q := by
  obtain ⟨lo, hlo⟩ := List.exists_mem_of_ne_nil w.Y.p0 w.Y.ne0
  obtain ⟨hi, hhi⟩ := List.exists_mem_of_ne_nil w.Y.p1 w.Y.ne1
  exact ⟨lo, w.Y.mem0 hlo, hi, w.Y.mem1 hhi,
    w.y0_x1.mem hlo hq, w.x1_y1.mem hq hhi⟩

theorem InterlacingWitness.x3_mem_inside_second
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {q : TaggedCoord} (hq : q ∈ w.X.p3) : Inside y q := by
  obtain ⟨lo, hlo⟩ := List.exists_mem_of_ne_nil w.Y.p2 w.Y.ne2
  obtain ⟨hi, hhi⟩ := List.exists_mem_of_ne_nil w.Y.p3 w.Y.ne3
  exact ⟨lo, w.Y.mem2 hlo, hi, w.Y.mem3 hhi,
    w.y2_x3.mem hlo hq, w.x3_y3.mem hq hhi⟩

theorem InterlacingWitness.box_second_mem_last_of_middle_lt
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {p q : TaggedCoord} (hp : p ∈ w.X.p2)
    (hq : IsBoxCoord y q) (hpq : p.value < q.value) :
    q ∈ w.Y.p3 := by
  rcases hq with ⟨hqy, hqbox⟩
  rcases w.Y.mem_cases hqy with hq0 | hq1 | hq2 | hq3
  · exact (Nat.not_lt_of_ge (w.y0_before_x_tail hq0 (Or.inr (Or.inl hp))).le hpq).elim
  · have := w.noBox_y1 q hq1
    simp [hqbox] at this
  · have := w.noBox_y2 q hq2
    simp [hqbox] at this
  · exact hq3

theorem InterlacingWitness.box_second_mem_first_of_lt_middle
    {x y : List TaggedCoord} (w : InterlacingWitness x y)
    {p q : TaggedCoord} (hp : p ∈ w.X.p2)
    (hq : IsBoxCoord y q) (hqp : q.value < p.value) :
    q ∈ w.Y.p0 := by
  rcases hq with ⟨hqy, hqbox⟩
  rcases w.Y.mem_cases hqy with hq0 | hq1 | hq2 | hq3
  · exact hq0
  · have := w.noBox_y1 q hq1
    simp [hqbox] at this
  · have := w.noBox_y2 q hq2
    simp [hqbox] at this
  · exact (Nat.not_lt_of_ge
      (w.x_head_before_y3 (Or.inr (Or.inr (Or.inl hp))) hq3).le hqp).elim

/-- Hajnal--Larson Claim B.  In an oriented interlacing triangle, a box
coordinate of the last sequence cannot lie strictly between chosen box
coordinates of the first two sequences, provided the latter lie inside the
last numerical interval. -/
theorem triangle_box_not_between
    {x y z : List TaggedCoord}
    (wxy : InterlacingWitness x y) (wxz : InterlacingWitness x z)
    (wyz : InterlacingWitness y z)
    {qx qy qz : TaggedCoord}
    (hqx : IsBoxCoord x qx) (hqy : IsBoxCoord y qy)
    (hqz : IsBoxCoord z qz)
    (hqxz : Inside z qx) (hqyz : Inside z qy) :
    ¬ (qx.value < qz.value ∧ qz.value < qy.value) ∧
      ¬ (qy.value < qz.value ∧ qz.value < qx.value) := by
  have hqxy : Inside y qx := wyz.inside_first_of_inside_second hqxz
  have hqxmid : qx ∈ wxy.X.p2 := wxy.box_mem_middle_of_inside hqx hqxy
  constructor
  · rintro ⟨hqxqz, hqzqy⟩
    have hqylast : qy ∈ wxy.Y.p3 :=
      wxy.box_second_mem_last_of_middle_lt hqxmid hqy (hqxqz.trans hqzqy)
    obtain ⟨xplus, hxplus⟩ := List.exists_mem_of_ne_nil wxy.X.p3 wxy.X.ne3
    obtain ⟨gamma, hgamma⟩ := List.exists_mem_of_ne_nil wxy.Y.p2 wxy.Y.ne2
    have hqxgamma : qx.value < gamma.value := wxy.x2_y2.mem hqxmid hgamma
    have hgammaxplus : gamma.value < xplus.value :=
      wxy.y2_x3.mem hgamma hxplus
    have hxplusqy : xplus.value < qy.value := wxy.x3_y3.mem hxplus hqylast
    rcases lt_or_ge qz.value xplus.value with hqzx | hxqz
    · rcases hqxz with ⟨lo, hlo, -, -, hloq, -⟩
      rcases hqyz with ⟨-, -, hi, hhi, -, qyhi⟩
      exact wxz.no_y_box_between_x_inside
        hqx.1 hqz (wxy.X.mem3 hxplus) hlo hhi
        ⟨hloq, hqxqz, hqzx, hxplusqy.trans qyhi⟩
    · rcases hqxz with ⟨lo, hlo, -, -, hloqx, -⟩
      rcases hqyz with ⟨-, -, hi, hhi, -, qyhi⟩
      exact wyz.no_y_box_between_x_inside
        (wxy.Y.mem2 hgamma) hqz hqy.1 hlo hhi
        ⟨hloqx.trans hqxgamma, hgammaxplus.trans_le hxqz,
          hqzqy, qyhi⟩
  · rintro ⟨hqyqz, hqzqx⟩
    have hqyfirst : qy ∈ wxy.Y.p0 :=
      wxy.box_second_mem_first_of_lt_middle hqxmid hqy (hqyqz.trans hqzqx)
    obtain ⟨xminus, hxminus⟩ := List.exists_mem_of_ne_nil wxy.X.p1 wxy.X.ne1
    obtain ⟨gamma, hgamma⟩ := List.exists_mem_of_ne_nil wxy.Y.p1 wxy.Y.ne1
    have hqyxminus : qy.value < xminus.value := wxy.y0_x1.mem hqyfirst hxminus
    have hxminusgamma : xminus.value < gamma.value := wxy.x1_y1.mem hxminus hgamma
    have hgammaqx : gamma.value < qx.value := wxy.y1_x2.mem hgamma hqxmid
    rcases lt_or_ge qz.value gamma.value with hqzg | hgz
    · rcases hqyz with ⟨lo, hlo, -, -, hloqy, -⟩
      rcases hqxz with ⟨-, -, hi, hhi, -, qxhi⟩
      exact wyz.no_y_box_between_x_inside
        hqy.1 hqz (wxy.Y.mem1 hgamma) hlo hhi
        ⟨hloqy, hqyqz, hqzg, hgammaqx.trans qxhi⟩
    · rcases hqyz with ⟨lo, hlo, -, -, hloqy, -⟩
      rcases hqxz with ⟨-, -, hi, hhi, -, qxhi⟩
      exact wxz.no_y_box_between_x_inside
        (wxy.X.mem1 hxminus) hqz hqx.1 hlo hhi
        ⟨hloqy.trans hqyxminus,
          hxminusgamma.trans_le hgz, hqzqx, qxhi⟩

/-- Hajnal--Larson Claim C: between box coordinates of the first two
vertices of an oriented interlacing triangle, both lying inside the final
vertex, there is a coordinate of the final vertex. -/
theorem triangle_exists_coord_between
    {x y z : List TaggedCoord}
    (wxy : InterlacingWitness x y) (wxz : InterlacingWitness x z)
    (wyz : InterlacingWitness y z)
    {qx qy : TaggedCoord}
    (hqx : IsBoxCoord x qx) (hqy : IsBoxCoord y qy)
    (hqxz : Inside z qx) (hqyz : Inside z qy) :
    ∃ qz ∈ z,
      (qx.value < qz.value ∧ qz.value < qy.value) ∨
      (qy.value < qz.value ∧ qz.value < qx.value) := by
  have hqxy : Inside y qx := wyz.inside_first_of_inside_second hqxz
  have hqxmid : qx ∈ wxy.X.p2 := wxy.box_mem_middle_of_inside hqx hqxy
  have hcompare : qx.value < qy.value ∨ qy.value < qx.value := by
    rcases hqy with ⟨hqymem, hqybox⟩
    rcases wxy.Y.mem_cases hqymem with h0 | h1 | h2 | h3
    · exact Or.inr (wxy.y0_before_x_tail h0 (Or.inr (Or.inl hqxmid)))
    · have := wxy.noBox_y1 qy h1
      simp [hqybox] at this
    · have := wxy.noBox_y2 qy h2
      simp [hqybox] at this
    · exact Or.inl
        (wxy.x_head_before_y3 (Or.inr (Or.inr (Or.inl hqxmid))) h3)
  rcases hcompare with hxy | hyx
  · have hqylast : qy ∈ wxy.Y.p3 :=
      wxy.box_second_mem_last_of_middle_lt hqxmid hqy hxy
    obtain ⟨qz, hqz⟩ := List.exists_mem_of_ne_nil wxz.Y.p2 wxz.Y.ne2
    obtain ⟨xplus, hxplus⟩ := List.exists_mem_of_ne_nil wxz.X.p3 wxz.X.ne3
    have hqxqz : qx.value < qz.value := by
      have hqxmidz := wxz.box_mem_middle_of_inside hqx hqxz
      exact wxz.x2_y2.mem hqxmidz hqz
    have hqzxplus : qz.value < xplus.value := wxz.y2_x3.mem hqz hxplus
    have hxplus_inside_z : Inside z xplus := wxz.x3_mem_inside_second hxplus
    have hxplus_inside_y : Inside y xplus :=
      wyz.inside_first_of_inside_second hxplus_inside_z
    have hxplusqy : xplus.value < qy.value := by
      have hxmem : xplus ∈ x := wxz.X.mem3 hxplus
      rcases wxy.X.mem_cases hxmem with h0 | h1 | h2 | h3 | h4
      · exact wxy.x0_before_y h0 hqy.1
      · exact (((((wxy.x1_y1.trans wxy.y1_x2 wxy.Y.ne1).trans
          wxy.x2_y2 wxy.X.ne2).trans wxy.y2_x3 wxy.Y.ne2).trans
          wxy.x3_y3 wxy.X.ne3).mem h1 hqylast)
      · exact (((wxy.x2_y2.trans wxy.y2_x3 wxy.Y.ne2).trans
          wxy.x3_y3 wxy.X.ne3).mem h2 hqylast)
      · exact wxy.x3_y3.mem h3 hqylast
      · rcases hqxy with ⟨lo, hlo, -, -, hloqx, -⟩
        rcases hxplus_inside_y with ⟨-, -, hi, hhi, -, hxhi⟩
        exfalso
        exact wxy.no_y_box_between_x_inside hqx.1 hqy hxmem hlo hhi
          ⟨hloqx, hxy, wxy.y3_x4.mem hqylast h4, hxhi⟩
    exact ⟨qz, wxz.Y.mem2 hqz, Or.inl
      ⟨hqxqz, hqzxplus.trans hxplusqy⟩⟩
  · have hqyfirst : qy ∈ wxy.Y.p0 :=
      wxy.box_second_mem_first_of_lt_middle hqxmid hqy hyx
    obtain ⟨qz, hqz⟩ := List.exists_mem_of_ne_nil wxz.Y.p1 wxz.Y.ne1
    obtain ⟨xminus, hxminus⟩ := List.exists_mem_of_ne_nil wxz.X.p1 wxz.X.ne1
    have hxminusqz : xminus.value < qz.value := wxz.x1_y1.mem hxminus hqz
    have hqzqx : qz.value < qx.value := by
      have hqxmidz := wxz.box_mem_middle_of_inside hqx hqxz
      exact wxz.y1_x2.mem hqz hqxmidz
    have hxminus_inside_z : Inside z xminus := wxz.x1_mem_inside_second hxminus
    have hxminus_inside_y : Inside y xminus :=
      wyz.inside_first_of_inside_second hxminus_inside_z
    have hqyxminus : qy.value < xminus.value := by
      have hxmem : xminus ∈ x := wxz.X.mem1 hxminus
      rcases wxy.X.mem_cases hxmem with h0 | h1 | h2 | h3 | h4
      · rcases hxminus_inside_y with ⟨lo, hlo, -, -, hlo_x, -⟩
        rcases hqxy with ⟨-, -, hi, hhi, -, qxhi⟩
        exfalso
        exact wxy.no_y_box_between_x_inside hxmem hqy hqx.1 hlo hhi
          ⟨hlo_x, wxy.x0_y0.mem h0 hqyfirst, hyx, qxhi⟩
      · exact wxy.y0_x1.mem hqyfirst h1
      · exact wxy.y0_before_x_tail hqyfirst (Or.inr (Or.inl h2))
      · exact wxy.y0_before_x_tail hqyfirst (Or.inr (Or.inr (Or.inl h3)))
      · exact wxy.y0_before_x_tail hqyfirst (Or.inr (Or.inr (Or.inr h4)))
    exact ⟨qz, wxz.Y.mem1 hqz, Or.inr
      ⟨hqyxminus.trans hxminusqz, hqzqx⟩⟩

end Erdos591.Negative

end Erdos118.Reused591
