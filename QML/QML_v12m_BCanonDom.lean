import QML.QML_v12m_BStaged

/-!
# QML v12m — B's canonical model: arrows, raw objects and denotations

`BData` is what the canonical model for B needs from the construction, abstracted from the
networks: worlds (`BWorld`), a symmetric accessibility `R`, and for each accessible pair an
**arrow**: an index map on variables (`img`), with, for each stage of the source, a stage of the
target where every source variable has its image (`stg`, `imgOk`); necessity transfer along it
(`tr`) and existence of arrows for failing necessities (`ex`).  Some arrows lead into the extent
of a witness `x` (`kd`), with content variable `cx`, `□_x` transfer (`trX`) and existence for true
`◇_x` formulas (`exX`).

* **Raw objects** (`RDom`) are as in the staged model: a necessary object has a value along each
  arrow, a possible object has an extent (a set of arrows) and a value along each.
* ⭐`rden`: the denotation of a term.  A necessary term `□t` denotes, along an arrow, the
  denotation at the target of `t` **translated** along the arrow (`arrowS`); a possible term
  `◇_x t` has the extent of `x`, and along each of its arrows the denotation of `t` translated by
  the witness arrow (`arrowXS`).  This is a recursion on the type.
* It does not depend on the stage (`rden_congr`) and commutes with weakening (`rden_mono`).

Under T (with 4 off) each world also has **its own arrow** (`RT`, the reflexive closure of the
network's `R`, which is irreflexive): along it a necessary term denotes its body collapsed, and a
witness the world realises (`BWorld.Realised`) has it in its extent, with the realised body as
content (`realTerm`) — as the tree's `rden` does at the world itself
(docs/v12-arrow-canonical.md §9).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-- A network that labels each arrow once, by its kind: its label map. -/
def lbOfKd {W : Type} (kd : W → W → Option (VarSymb × VarType)) (s t : W) (x : VarSymb) :
    Option VarType :=
  match kd s t with
  | some (y, X) => if y = x then some X else none
  | none => none

omit [ModalSys] in
theorem lbOfKd_eq {W : Type} {kd : W → W → Option (VarSymb × VarType)} {s t : W} {x : VarSymb}
    {X : VarType} : lbOfKd kd s t x = some X ↔ kd s t = some (x, X) := by
  cases hk : kd s t with
  | none => simp [lbOfKd, hk]
  | some p =>
      obtain ⟨y, Y⟩ := p
      by_cases hy : y = x
      · subst hy
        simp [lbOfKd, hk]
      · simp [lbOfKd, hk, hy]

omit [ModalSys] in
theorem lbOfKd_none {W : Type} {kd : W → W → Option (VarSymb × VarType)} {s t : W}
    (h : kd s t = none) (x : VarSymb) : lbOfKd kd s t x = none := by
  unfold lbOfKd
  rw [h]

omit [ModalSys] in
/-- One label per arrow separates witnesses: one labelling an arrow is the only label there. -/
theorem lbOfKd_sep {W : Type} {kd : W → W → Option (VarSymb × VarType)} {s k : W}
    {y y' : VarSymb} {Y : VarType} (hk : lbOfKd kd s k y = some Y)
    (h : ∀ t, (∃ X, lbOfKd kd s t y = some X) ↔ (∃ X, lbOfKd kd s t y' = some X)) : y = y' := by
  obtain ⟨X, hX⟩ := (h k).mp ⟨Y, hk⟩
  exact (Prod.mk.inj (Option.some.inj ((lbOfKd_eq.mp hk).symm.trans (lbOfKd_eq.mp hX)))).1

/-- ⭐The data of the canonical model for B. -/
structure BData [ModalSys.NoFour] (σ : Signature) where
  W : Type
  actual : W
  w : W → BWorld σ
  R : W → W → Prop
  symm : ∀ {s t}, R s t → R t s
  /-- The network has no loops, so a world's own arrow (under T) is not one of its arrows. -/
  irrefl : ∀ s, ¬ R s s
  img : W → W → ℕ → ℕ
  stg : W → W → ℕ → ℕ
  imgOk : ∀ {s t}, R s t → ∀ i, ImgOk ((w s).l i) ((w t).ctx (stg s t i)) (img s t)
  tr : ∀ {s t} (h : R s t) (i : ℕ) (ψ : WFF σ ((w s).ctx i).boxIn 0), .box ψ ∈ (w s).M i →
    WFF.subst (arrowIdx (img s t)) (arrowS σ _ (img s t)) (ok_arrowS (imgOk h i))
      (coh_arrowS (imgOk h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈ (w t).M (stg s t i)
  ex : ∀ (s : W) (i : ℕ) (ψ : WFF σ ((w s).ctx i).boxIn 0), .box ψ ∉ (w s).M i →
    ∃ (t : W) (h : R s t), (WFF.subst (arrowIdx (img s t)) (arrowS σ _ (img s t))
      (ok_arrowS (imgOk h i)) (coh_arrowS (imgOk h i)) Ctx.NoSlots.slots Ctx.NoSlots.slots
        ψ).neg ∈ (w t).M (stg s t i)
  /-- ⭐The arrows' **labels** (docs §11.23): `lb s t x = some X` when the arrow `s → t` lies in
      the extent of `x : ◇X`, its content there the root `cx s t x` of `t`.  Each arrow is
      labelled by its kind (`kd_lb`), and under row 3 by late labels too. -/
  lb : W → W → VarSymb → Option VarType
  cx : W → W → VarSymb → ℕ
  lbR : ∀ {s t x X}, lb s t x = some X → R s t
  lb_hcx : ∀ {s t x X}, lb s t x = some X → ∀ i,
    ((w t).ctx (stg s t i)).ref (.root (.free (cx s t x))) = some X
  lb_hxX : ∀ {s t x X}, lb s t x = some X → ∀ i X',
    ((w s).ctx i).ref x = some (.VTypeDia X') → X' = X
  lb_trX : ∀ {s t x X} (hk : lb s t x = some X) (i : ℕ)
    (hx : ((w s).ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ (((w s).ctx i).diaIn x) 0),
    WFF.boxx x ⟨X, hx⟩ ψ ∈ (w s).M i →
    WFF.subst (arrowXIdx (img s t) x (cx s t x)) (arrowXS σ _ (img s t) x (cx s t x))
      (ok_arrowXS (imgOk (lbR hk) i) hx (lb_hcx hk i))
      (coh_arrowXS (imgOk (lbR hk) i) hx (lb_hcx hk i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        (w t).M (stg s t i)
  /-- The arrow's **kind**: the witness it was made for (`exX`), one of its labels. -/
  kd : W → W → Option (VarSymb × VarType)
  kd_lb : ∀ {s t x X}, kd s t = some (x, X) → lb s t x = some X
  exX : ∀ (s : W) (i : ℕ) (x : VarSymb) (X : VarType)
    (hx : ((w s).ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ (((w s).ctx i).diaIn x) 0),
    WFF.dia x ⟨X, hx⟩ ψ ∈ (w s).M i →
    ∃ (t : W) (hk : kd s t = some (x, X)),
      WFF.subst (arrowXIdx (img s t) x (cx s t x)) (arrowXS σ _ (img s t) x (cx s t x))
        (ok_arrowXS (imgOk (lbR (kd_lb hk)) i) hx (lb_hcx (kd_lb hk) i))
        (coh_arrowXS (imgOk (lbR (kd_lb hk)) i) hx (lb_hcx (kd_lb hk) i)) Ctx.NoSlots.slots
          Ctx.NoSlots.slots ψ ∈ (w t).M (stg s t i)
  /-- ⭐Wherever there is an arrow out there is one **not labelled** `y`, for each `y` (docs §11.23,
      P2): a plain leg's arrows are never one witness's extent, which strong B's `back` case reads
      to tell the legs apart. -/
  unl : ∀ {s t} (y : VarSymb), R s t → ∃ t', R s t' ∧ lb s t' y = none
  /-- ⭐**Labels separate witnesses** (docs §11.23, P2): a witness labelling some arrow is
      determined by the arrows it labels. -/
  sep : ∀ {s k y y' Y}, lb s k y = some Y →
    (∀ t, (∃ X, lb s t y = some X) ↔ (∃ X, lb s t y' = some X)) → y = y'
  /-- ⭐Strong B, row 1: a `Back` atom's carrier, read out along an arrow and home again, is
      interchangeable with the atom's value (`Att.back`, from the network's invariants). -/
  backRel : ∀ (hS : ModalSys.BStrong = true) {s : W} {i : ℕ} {A : VarType} {a₀ : Ann A}
    (bd : Term σ ((w s).ctx i).boxIn.boxIn A a₀) {a : Ann A} (t : Term σ ((w s).ctx i) A a),
    WFF.back hS .nec (Term.boxtm (Term.boxtm bd)) t ∈ (w s).M i →
    ∀ {k : W} (h : R s k),
      Canon.DTerm.Rel (S := (w s).sys) (T := (w s).T)
        ⟨stg k s (stg s k i), _, Term.subst (arrowIdx (img k s)) (arrowS σ _ (img k s))
          (ok_arrowS (imgOk (symm h) (stg s k i))) (coh_arrowS (imgOk (symm h) (stg s k i)))
          (Term.subst (arrowIdx (img s k)) (arrowS σ _ (img s k)).box
            (Subst.ok_box (ok_arrowS (imgOk h i)))
            (Subst.coh_box (ok_arrowS (imgOk h i)) (coh_arrowS (imgOk h i))) bd)⟩
        ⟨i, a, t⟩
  /-- ⭐Strong B, row 2: the same along the arrows of the carrier's witness `y`. -/
  backRelX : ∀ (hS : ModalSys.BStrong = true) {s : W} {i : ℕ} {A : VarType} {a₀ : Ann A}
    {y : VarSymb} {Y : VarType} (hy : ((w s).ctx i).ref y = some (.VTypeDia Y))
    (bd : Term σ (((w s).ctx i).diaIn y).boxIn A a₀) {a : Ann A} (t : Term σ ((w s).ctx i) A a),
    WFF.back hS .pos (Term.diatm y ⟨Y, hy⟩ (Term.boxtm bd)) t ∈ (w s).M i →
    ∀ {k : W} (hk : lb s k y = some Y),
      Canon.DTerm.Rel (S := (w s).sys) (T := (w s).T)
        ⟨stg k s (stg s k i), _, Term.subst (arrowIdx (img k s)) (arrowS σ _ (img k s))
          (ok_arrowS (imgOk (symm (lbR hk)) (stg s k i)))
          (coh_arrowS (imgOk (symm (lbR hk)) (stg s k i)))
          (Term.subst (arrowXIdx (img s k) y (cx s k y)) (arrowXS σ _ (img s k) y (cx s k y)).box
            (Subst.ok_box (ok_arrowXS (imgOk (lbR hk) i) hy (lb_hcx hk i)))
            (Subst.coh_box (ok_arrowXS (imgOk (lbR hk) i) hy (lb_hcx hk i))
              (coh_arrowXS (imgOk (lbR hk) i) hy (lb_hcx hk i))) bd)⟩
        ⟨i, a, t⟩

namespace BData

variable [ModalSys.NoFour] (B : BData σ)

/-! ### The kind label -/

theorem kdR {s t : B.W} {x : VarSymb} {X : VarType} (hk : B.kd s t = some (x, X)) : B.R s t :=
  B.lbR (B.kd_lb hk)

theorem hcx {s t : B.W} {x : VarSymb} {X : VarType} (hk : B.kd s t = some (x, X)) (i : ℕ) :
    ((B.w t).ctx (B.stg s t i)).ref (.root (.free (B.cx s t x))) = some X :=
  B.lb_hcx (B.kd_lb hk) i

theorem hxX {s t : B.W} {x : VarSymb} {X : VarType} (hk : B.kd s t = some (x, X)) (i : ℕ)
    (X' : VarType) (h : ((B.w s).ctx i).ref x = some (.VTypeDia X')) : X' = X :=
  B.lb_hxX (B.kd_lb hk) i X' h

theorem trX {s t : B.W} {x : VarSymb} {X : VarType} (hk : B.kd s t = some (x, X)) (i : ℕ)
    (hx : ((B.w s).ctx i).ref x = some (.VTypeDia X)) (ψ : WFF σ (((B.w s).ctx i).diaIn x) 0)
    (h : WFF.boxx x ⟨X, hx⟩ ψ ∈ (B.w s).M i) :
    WFF.subst (arrowXIdx (B.img s t) x (B.cx s t x)) (arrowXS σ _ (B.img s t) x (B.cx s t x))
      (ok_arrowXS (B.imgOk (B.kdR hk) i) hx (B.hcx hk i))
      (coh_arrowXS (B.imgOk (B.kdR hk) i) hx (B.hcx hk i)) Ctx.NoSlots.slots Ctx.NoSlots.slots ψ ∈
        (B.w t).M (B.stg s t i) :=
  B.lb_trX (B.kd_lb hk) i hx ψ h

/-- ⭐The canonical accessibility: the network's arrows and, under T, each world's own. -/
def RT (s t : B.W) : Prop := B.R s t ∨ (ModalSys.T = true ∧ s = t)

/-- The arrows out of a world. -/
abbrev Acc (s : B.W) : Type := Σ t : B.W, PLift (B.RT s t)

variable {B} in
/-- An arrow that is not one of the network's is the world's own, under T. -/
theorem self_of_not_R {s : B.W} {a : B.Acc s} (h : ¬ B.R s a.1) :
    ModalSys.T = true ∧ s = a.1 :=
  a.2.down.resolve_left h

/-- One world's contexts are another's when the worlds are one. -/
theorem selfLe {s t : B.W} (h : s = t) (i : ℕ) : ((B.w s).ctx i).Le ((B.w t).ctx i) :=
  h ▸ Ctx.Le.refl _

/-- ⭐The extent of the witness `x` at `s`: the network's arrows into its extent, and the world's
    own arrow when its theory realises `x`. -/
def extent (s : B.W) (x : VarSymb) : Set (B.Acc s) :=
  {a | (∃ X, B.lb s a.1 x = some X) ∨ (¬ B.R s a.1 ∧ (B.w s).Realised x)}

variable {B} in
theorem mem_extent_self {s : B.W} {x : VarSymb} {a : B.Acc s} (h : a ∈ B.extent s x)
    (hk : ¬ ∃ X, B.lb s a.1 x = some X) : ¬ B.R s a.1 ∧ (B.w s).Realised x :=
  h.resolve_left hk

variable {B} in
/-- Equal extents label the same network arrows. -/
theorem lb_iff_of_extent_eq {s : B.W} {y y' : VarSymb} (h : B.extent s y = B.extent s y')
    (t : B.W) : (∃ X, B.lb s t y = some X) ↔ (∃ X, B.lb s t y' = some X) := by
  by_cases hR : B.R s t
  · have e : (⟨t, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈ B.extent s y ↔
        (⟨t, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈ B.extent s y' := by rw [h]
    constructor
    · intro hl
      rcases e.mp (Or.inl hl) with h' | ⟨hn, -⟩
      · exact h'
      · exact absurd hR hn
    · intro hl
      rcases e.mpr (Or.inl hl) with h' | ⟨hn, -⟩
      · exact h'
      · exact absurd hR hn
  · constructor <;> rintro ⟨X, hX⟩ <;> exact absurd (B.lbR hX) hR

variable {B} in
/-- ⭐Two witnesses with one extent, labelling some arrow, are one (`sep`). -/
theorem eq_of_extent_eq {s k : B.W} {y y' : VarSymb} {Y : VarType}
    (hk : B.lb s k y = some Y) (h : B.extent s y = B.extent s y') : y = y' :=
  B.sep hk (lb_iff_of_extent_eq h)

/-- Under a world's own arrow, the content of a realised witness's possible object `⟨x; t⟩`: the
    body realised by the datum's content, at a stage above both (`Term.realiseAtA`) — the tree's
    `Canon.realisedTerm`. -/
noncomputable def realTerm {s : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {Γ : Ctx} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (t : Term σ (Γ.diaIn x) A a) :
    Σ b : Ann A, Term σ ((B.w s).ctx (max i hr.data.i₀)) A b :=
  ⟨_, Term.realiseAtA hr.data.hT x
    (hr.data.hdeclOf _ (hx.imp fun _ h => ((B.w s).le (le_max_left _ _)).ref (e.ref h)))
    (Term.mono ((B.w s).le (le_max_right _ _)) hr.data.t₀)
    (Term.mono ((e.trans ((B.w s).le (le_max_left _ _))).diaIn x) t)⟩

/-- The arrow's renaming is well typed at a stage. -/
theorem arOk {s t : B.W} (h : B.R s t) (i : ℕ) :
    Subst.Ok ((B.w s).ctx i).boxIn (arrowS σ ((B.w t).ctx (B.stg s t i)) (B.img s t)) :=
  ok_arrowS (B.imgOk h i)

theorem arCoh {s t : B.W} (h : B.R s t) (i : ℕ) :
    Subst.Coh (arrowIdx (B.img s t)) ((B.w s).ctx i).boxIn
      (arrowS σ ((B.w t).ctx (B.stg s t i)) (B.img s t)) :=
  coh_arrowS (B.imgOk h i)

/-- A witness arrow's renaming is well typed at a stage where the witness is visible. -/
theorem arXOk {s t : B.W} {x : VarSymb} (hm : ∃ X, B.lb s t x = some X) (i : ℕ)
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) :
    Subst.Ok (((B.w s).ctx i).diaIn x)
      (arrowXS σ ((B.w t).ctx (B.stg s t i)) (B.img s t) x (B.cx s t x)) := by
  obtain ⟨X, hk⟩ := hm
  obtain ⟨X', hX'⟩ := hx
  have e := B.lb_hxX hk i X' hX'
  subst e
  exact ok_arrowXS (B.imgOk (B.lbR hk) i) hX' (B.lb_hcx hk i)

theorem arXCoh {s t : B.W} {x : VarSymb} (hm : ∃ X, B.lb s t x = some X) (i : ℕ)
    (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X)) :
    Subst.Coh (arrowXIdx (B.img s t) x (B.cx s t x)) (((B.w s).ctx i).diaIn x)
      (arrowXS σ ((B.w t).ctx (B.stg s t i)) (B.img s t) x (B.cx s t x)) := by
  obtain ⟨X, hk⟩ := hm
  obtain ⟨X', hX'⟩ := hx
  have e := B.lb_hxX hk i X' hX'
  subst e
  exact coh_arrowXS (B.imgOk (B.lbR hk) i) hX' (B.lb_hcx hk i)

/-! ## Canonical shapes

As in the tree (`QML_v12m_CanonShape`): a root possibility is named by its address, and a `□`
address has, along each arrow, the shape of its contents' address there.  Along a network arrow
that address is the arrow's index map applied (`arrowIdx`, as `rden` translates); along a world's
own arrow it is collapsed (`succAddr`).  Only the frame's arrows differ from the tree's. -/

theorem noFour : ModalSys.Four = true → False := fun h => by
  rw [ModalSys.NoFour.noFour] at h
  cases h

/-- ⭐The network's arrows: its worlds with `RT`.  The frame is built on them, so a canonical shape
    is a shape of the model. -/
abbrev arrows : Arrows.{0, 0} σ where
  W := B.W
  R := B.RT
  refl := fun hT _ => Or.inr ⟨hT, rfl⟩
  trans := fun hF => (noFour hF).elim
  refl_trans := fun _ hF => (noFour hF).elim
  trans_refl := fun _ hF => (noFour hF).elim
  trans_assoc := fun hF => (noFour hF).elim

/-- Shapes on the network: a root possibility is named by its address. -/
abbrev CShape (s : B.W) (T : VarType) : Type := Model.Shape B.arrows (fun _ => VarSymb) s T

/-- Shape environments on the network. -/
abbrev CShEnv (Γ : Ctx) (s : B.W) : Type := Model.ShEnv B.arrows (fun _ => VarSymb) Γ s

open Classical in
/-- ⭐Where an address of the `□` view is read along an arrow: through the arrow's index map along a
    network arrow, collapsed along the world's own. -/
noncomputable def succAddr (s : B.W) (a : B.Acc s) (v : VarSymb) : VarSymb :=
  if B.R s a.1 then arrowIdx (B.img s a.1) v else v.collapse 0

variable {B} in
theorem succAddr_net {s : B.W} {a : B.Acc s} (h : B.R s a.1) (v : VarSymb) :
    B.succAddr s a v = arrowIdx (B.img s a.1) v := if_pos h

variable {B} in
theorem succAddr_self {s : B.W} {a : B.Acc s} (h : ¬ B.R s a.1) (v : VarSymb) :
    B.succAddr s a v = v.collapse 0 := if_neg h

/-- The shape of a root possibility's content at a path, as in the tree (`Canon.rootSh`). -/
def rootSh (s : B.W) (v : VarSymb) : List Step → (T : VarType) → B.CShape s T
  | _, .Var => .var
  | _, .VTypeOne => .one
  | π, .VTypeProd A C => .prod (rootSh s v (π ++ [.fst]) A) (rootSh s v (π ++ [.snd]) C)
  | π, .VTypeBox A => .box (rootSh s v (π ++ Step.innerPath) A)
  | π, .VTypeDia A => .dia (.root v π) (rootSh s v (π ++ [.dia]) A)

/-- ⭐The canonical shape of what an address names: a `◇` address is a root possibility, a `□`
    address has along each arrow the shape of its contents' address there. -/
noncomputable def canonSh : (s : B.W) → VarSymb → (T : VarType) → B.CShape s T
  | _, _, .Var => .var
  | _, _, .VTypeOne => .one
  | s, v, .VTypeProd A C => .prod (canonSh s (.step v .fst) A) (canonSh s (.step v .snd) C)
  | s, v, .VTypeBox A =>
      .box (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) fun a =>
        canonSh a.1 (B.succAddr s a v.inner) A)
  | s, v, .VTypeDia A => .dia (.root v []) (B.rootSh s v [.dia] A)

/-- A projection step moves a canonical shape to the projected address's. -/
theorem canonSh_proj (s : B.W) (v : VarSymb) {U T : VarType} {st : Step}
    (hs : st.isProj = true) (h : U.step st = some T) :
    GFunc.shp (GFunc.proj (σ := σ) hs h) 0 (B.canonSh s v U) = B.canonSh s (.step v st) T := by
  cases U <;> cases st <;> (try cases hs) <;> (try cases h)
  · rfl
  · rfl
  · obtain ⟨hT, rfl⟩ := VarType.step_here h
    change (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) fun a =>
        B.canonSh a.1 (B.succAddr s a v.inner) _).map (Arrows.Leaf.collapse hT 0) = _
    rw [Model.transpose_collapse_zero hT]
    change B.canonSh s (B.succAddr s ⟨s, ⟨Or.inr ⟨hT, rfl⟩⟩⟩ v.inner) _ = _
    rw [succAddr_self (B.irrefl s), VarSymb.inner_collapse_zero]

/-- The shape environment reading each address through an address map. -/
noncomputable def canonEnvF (Γ : Ctx) (s : B.W) (f : VarSymb → VarSymb) : B.CShEnv Γ s :=
  fun v T _ => B.canonSh s (f v) T

/-- ⭐The canonical shape environment. -/
noncomputable abbrev cEnv (Γ : Ctx) (s : B.W) : B.CShEnv Γ s := B.canonEnvF Γ s id

/-- Through a map commuting with projections on reachable addresses, every reachable address reads
    canonically. -/
theorem canonEnvF_ref (Γ : Ctx) (s : B.W) {f : VarSymb → VarSymb}
    (hf : ∀ v U st, Γ.ref v = some U → st.isProj = true → f (.step v st) = .step (f v) st) :
    ∀ (v : VarSymb) {T : VarType} (h : Γ.ref v = some T),
      (B.canonEnvF Γ s f).ref 0 v h = B.canonSh s (f v) T
  | .root _, _, _ => rfl
  | .step v st, T, h => by
      by_cases hs : st.isProj = true
      · obtain ⟨U, hU⟩ : ∃ U, Γ.ref v = some U := by
          rw [Ctx.ref_step_proj Γ v hs] at h
          cases hU : Γ.ref v with
          | none => rw [hU] at h; cases h
          | some U => exact ⟨U, rfl⟩
        rw [Model.ShEnv.ref_proj _ 0 hs hU h, canonEnvF_ref Γ s hf v hU, canonSh_proj,
          hf v U st hU hs]
      · rw [Model.ShEnv.ref_nonproj _ 0 hs h]
        rfl

theorem cEnv_ref (Γ : Ctx) (s : B.W) (v : VarSymb) {T : VarType} (h : Γ.ref v = some T) :
    (B.cEnv Γ s).ref 0 v h = B.canonSh s v T :=
  B.canonEnvF_ref Γ s (fun _ _ _ _ _ => rfl) v h

/-- ⭐Pushing the canonical environment into `□` gives, along each arrow, the target's environment
    read through `succAddr`. -/
theorem cEnv_boxPush (Γ : Ctx) (s : B.W) :
    ∀ v T (h : Γ.boxIn v = some T),
      (B.cEnv Γ s).boxPush 0 v T h =
        Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) fun a =>
          B.canonEnvF Γ.boxIn a.1 (B.succAddr s a) v T h
  | .step u .box, T, h => by
      obtain ⟨hk, _⟩ := Ctx.boxIn_box h
      change ((B.cEnv Γ s).ref 0 u (Ctx.boxIn_step_box h)).inner = _
      rw [cEnv_ref]
      change Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) (fun a =>
        B.canonSh a.1 (B.succAddr s a u.inner) T) = _
      rw [VarSymb.inner_box hk]
      rfl
  | .step u .keep, _, h => (noFour (Ctx.boxIn_keep h).1).elim
  | .root _, _, h => by cases h
  | .step _ .fst, _, h => by cases h
  | .step _ .snd, _, h => by cases h
  | .step _ .dia, _, h => by cases h
  | .step _ .here, _, h => by cases h

/-- Along a world's own arrow, a `□` body read through `succAddr` has the shape of its collapse. -/
theorem termShp_collapse_cEnv (hT : ModalSys.T = true) {Γ : Ctx} (s : B.W) {A : VarType}
    {a : Ann A} (t : Term σ Γ.boxIn A a) :
    Model.termShp (B.cEnv Γ s) 0 (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t) =
      Model.termShp (B.canonEnvF Γ.boxIn s fun v => v.collapse 0) 0 t := by
  refine Model.termShp_collapse ?_ t
  intro v T hv
  rw [B.canonEnvF_ref _ _ (fun v _ st _ hs => VarSymb.collapse_proj hs), cEnv_ref]

/-- ⭐Along a network arrow, a `□` body translated by the arrow has the shape of the body read
    through the arrow's index map. -/
theorem termShp_arrow_cEnv {Γ : Ctx} {s s' : B.W} (h : B.R s s') {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) {A : VarType} {a : Ann A} (b : Term σ Γ.boxIn A a) :
    Model.termShp (B.cEnv ((B.w s').ctx (B.stg s s' i)) s') 0
        (Term.subst (arrowIdx (B.img s s')) (arrowS σ _ (B.img s s'))
          ((B.arOk h i).restrict e.boxIn) ((B.arCoh h i).restrict e.boxIn) b) =
      Model.termShp (B.canonEnvF Γ.boxIn s' (arrowIdx (B.img s s'))) 0 b := by
  rw [Model.termShp_subst _ _ _ (Ctx.noProjLast_boxIn Γ)]
  congr 1
  funext v T hv
  obtain ⟨u, rfl, hu⟩ : ∃ u, v = .step u .box ∧ Γ.ref u = some (.VTypeBox T) := by
    match v, hv with
    | .step u .box, hv => exact ⟨u, rfl, (Ctx.boxIn_box hv).2⟩
    | .step u .keep, hv => exact (noFour (Ctx.boxIn_keep hv).1).elim
    | .root _, hv => cases hv
    | .step _ .fst, hv => cases hv
    | .step _ .snd, hv => cases hv
    | .step _ .dia, hv => cases hv
    | .step _ .here, hv => cases hv
  change (B.cEnv _ s').ref 0 (itemImg (B.img s s') u) _ =
    B.canonSh s' (arrowIdx (B.img s s') (.step u .box)) T
  rw [cEnv_ref, arrowIdx_item (reach_ppath (e.ref hu)).1]

/-- ⭐A raw possible object: an extent, a raw object along each of its arrows, and, under T, its
    shape, which the canonical model stores rather than computes — as in the tree (`Canon.RPos`).
    Without T, objects with one section are one object. -/
structure RPos (s : B.W) (A : VarType) (C : B.Acc s → Type) where
  E : Set (B.Acc s)
  c : (a : E) → C a.1
  tag : ModalSys.shaped = true → B.CShape s (.VTypeDia A)

variable {B} in
theorem RPos.congr_cont {s : B.W} {A : VarType} {C : B.Acc s → Type} {E : Set (B.Acc s)}
    {c c' : (a : E) → C a.1} {τ τ' : ModalSys.shaped = true → B.CShape s (.VTypeDia A)}
    (hc : c = c')
    (hτ : ∀ hT, τ hT = τ' hT) :
    (⟨E, c, τ⟩ : B.RPos s A C) = ⟨E, c', τ'⟩ := by
  subst hc
  obtain rfl : τ = τ' := funext hτ
  rfl

/-! ## Raw objects and denotations -/

/-- Raw objects of a type at a world. -/
def RDom : VarType → B.W → Type
  | .Var, s => (B.w s).D
  | .VTypeOne, _ => PUnit
  | .VTypeProd A C, s => RDom A s × RDom C s
  | .VTypeBox A, s => (a : B.Acc s) → RDom A a.1
  | .VTypeDia A, s => B.RPos s A fun a => RDom A a.1

/-- ⭐Under T or strong B (`shaped`), the shape of a raw object: the stored shapes of its possible
    objects, arranged as its type arranges them — `Frame.domShape` for raw objects. -/
def rawShape (hSh : ModalSys.shaped = true) : {A : VarType} → {s : B.W} → B.RDom A s → B.CShape s A
  | .Var, _, _ => .var
  | .VTypeOne, _, _ => .one
  | .VTypeProd _ _, _, o => .prod (rawShape hSh o.1) (rawShape hSh o.2)
  | .VTypeBox _, _, o =>
      .box (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) fun a =>
        rawShape hSh (o a))
  | .VTypeDia _, _, o => o.3 hSh

open Classical in
/-- ⭐The denotation of a term at a world, computed at a stage containing its context. -/
noncomputable def rden : {A : VarType} → {a : Ann A} → {Γ : Ctx} → (s : B.W) → (i : ℕ) →
    Γ.Le ((B.w s).ctx i) → Term σ Γ A a → B.RDom A s
  | _, _, _, s, i, e, .var v hv => (B.w s).cls i (.var v (e.ref hv))
  | _, _, _, s, i, e, .func f => (B.w s).cls i (Term.mono e (.func f))
  | _, _, _, _, _, _, .unit => PUnit.unit
  | _, _, _, s, i, e, .pair t u => (rden s i e t, rden s i e u)
  | _, _, Γ, s, i, e, .boxtm t => fun a =>
      if h : B.R s a.1 then
        rden a.1 (B.stg s a.1 i) (Ctx.Le.refl _)
          (Term.subst (arrowIdx (B.img s a.1)) (arrowS σ _ (B.img s a.1))
            ((B.arOk h i).restrict e.boxIn) ((B.arCoh h i).restrict e.boxIn) t)
      else
        rden a.1 i (e.trans (B.selfLe (self_of_not_R h).2 i))
          (Term.collapse (Ctx.collapses_boxIn_self (self_of_not_R h).1 Γ) t)
  | _, _, Γ, s, i, e, .diatm x hx t =>
      ⟨B.extent s x, fun a =>
        if hk : ∃ X, B.lb s a.1.1 x = some X then
          rden a.1.1 (B.stg s a.1.1 i) (Ctx.Le.refl _)
            (Term.subst (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1 x))
              (arrowXS σ _ (B.img s a.1.1) x (B.cx s a.1.1 x))
              ((B.arXOk hk i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x))
              ((B.arXCoh hk i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x)) t)
        else
          rden a.1.1 _ (B.selfLe (self_of_not_R (mem_extent_self a.2 hk).1).2 _)
            (B.realTerm (mem_extent_self a.2 hk).2 e hx t).2,
        fun _ => Model.termShp (B.cEnv Γ s) 0 (.diatm x hx t)⟩
  termination_by structural A => A

variable {B}

theorem rden_sigma {A : VarType} {Γ : Ctx} {s : B.W} {i : ℕ} (e : Γ.Le ((B.w s).ctx i))
    {p q : Σ b : Ann A, Term σ Γ A b} (h : p = q) : B.rden s i e p.2 = B.rden s i e q.2 := by
  subst h
  rfl

/-- Along a network arrow a necessary term denotes its body translated. -/
theorem rden_boxtm_net {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (t : Term σ Γ.boxIn A a) (a' : B.Acc s) (h : B.R s a'.1) :
    B.rden s i e (.boxtm t) a' = B.rden a'.1 (B.stg s a'.1 i) (Ctx.Le.refl _)
      (Term.subst (arrowIdx (B.img s a'.1)) (arrowS σ _ (B.img s a'.1))
        ((B.arOk h i).restrict e.boxIn) ((B.arCoh h i).restrict e.boxIn) t) := by
  simp only [rden, dif_pos h]

/-- Along the world's own arrow a necessary term denotes its body collapsed. -/
theorem rden_boxtm_self {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (t : Term σ Γ.boxIn A a) (a' : B.Acc s) (h : ¬ B.R s a'.1) :
    B.rden s i e (.boxtm t) a' = B.rden a'.1 i (e.trans (B.selfLe (self_of_not_R h).2 i))
      (Term.collapse (Ctx.collapses_boxIn_self (self_of_not_R h).1 Γ) t) := by
  simp only [rden, dif_neg h]

/-- Along a witness arrow a possible term's content is its body translated. -/
theorem rden_diatm_net {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ} {x : VarSymb}
    (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (a' : B.extent s x) (hk : ∃ X, B.lb s a'.1.1 x = some X) :
    (B.rden s i e (.diatm x hx t)).2 a' = B.rden a'.1.1 (B.stg s a'.1.1 i) (Ctx.Le.refl _)
      (Term.subst (arrowXIdx (B.img s a'.1.1) x (B.cx s a'.1.1 x))
        (arrowXS σ _ (B.img s a'.1.1) x (B.cx s a'.1.1 x))
        ((B.arXOk hk i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x))
        ((B.arXCoh hk i (hx.imp fun _ h => e.ref h)).restrict (e.diaIn x)) t) := by
  simp only [rden, dif_pos hk]

/-- Along the world's own arrow a possible term's content is its body realised. -/
theorem rden_diatm_self {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ} {x : VarSymb}
    (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (t : Term σ (Γ.diaIn x) A a) (a' : B.extent s x) (hk : ¬ ∃ X, B.lb s a'.1.1 x = some X) :
    (B.rden s i e (.diatm x hx t)).2 a' =
      B.rden a'.1.1 _ (B.selfLe (self_of_not_R (mem_extent_self a'.2 hk).1).2 _)
        (B.realTerm (mem_extent_self a'.2 hk).2 e hx t).2 := by
  simp only [rden, dif_neg hk]

/-- The denotation commutes with weakening. -/
theorem rden_mono : ∀ {A : VarType} {a : Ann A} {Γ Γ' : Ctx} (h : Γ.Le Γ') (t : Term σ Γ A a)
    (s : B.W) (i : ℕ) (e : Γ'.Le ((B.w s).ctx i)),
    B.rden s i e (Term.mono h t) = B.rden s i (h.trans e) t
  | _, _, _, _, _, .var _ _, _, _, _ => rfl
  | _, _, _, _, h, .func f, s, i, e => by
      change (B.w s).cls i (Term.mono e (Term.mono h (.func f))) =
        (B.w s).cls i (Term.mono (h.trans e) (.func f))
      rw [Term.mono_mono]
  | _, _, _, _, _, .unit, _, _, _ => rfl
  | _, _, _, _, h, .pair t u, s, i, e => Prod.ext (rden_mono h t s i e) (rden_mono h u s i e)
  | _, _, Γ, Γ', h, .boxtm t, s, i, e => funext fun a => by
      change B.rden s i e (.boxtm (Term.mono h.boxIn t)) a = B.rden s i (h.trans e) (.boxtm t) a
      by_cases hR : B.R s a.1
      · simp only [rden, dif_pos hR]
        rw [Term.subst_mono]
      · simp only [rden, dif_neg hR]
        rw [Term.collapse_mono (Ctx.collapses_boxIn_self (self_of_not_R hR).1 Γ)
          (Ctx.collapses_boxIn_self (self_of_not_R hR).1 Γ') h.boxIn h, rden_mono h _ a.1 i]
  | _, _, Γ, Γ', h, .diatm x hx t, s, i, e => by
      change B.rden s i e (.diatm x _ (Term.mono (h.diaIn x) t)) = _
      simp only [rden]
      refine RPos.congr_cont (funext fun a => ?_) fun _ =>
        Model.termShp_mono (h := h) (ρ := B.cEnv Γ s) (ρ' := B.cEnv Γ' s) (fun _ _ _ => rfl) 0
          (.diatm x hx t)
      by_cases hk : ∃ X, B.lb s a.1.1 x = some X
      · simp only [dif_pos hk, Term.subst_mono]
      · simp only [dif_neg hk, realTerm, Term.mono_mono]
  termination_by structural A => A

/-- Substituting along an arrow into a later stage of the target is weakening. -/
theorem subst_arrow_mono {s t : B.W} {Γ : Ctx} (i : ℕ) (j : ℕ) (hij : B.stg s t i ≤ j)
    (e : Γ.Le ((B.w s).ctx i).boxIn) (hθ : Subst.Ok Γ (arrowS σ ((B.w t).ctx j) (B.img s t)))
    (hc : Subst.Coh (arrowIdx (B.img s t)) Γ (arrowS σ ((B.w t).ctx j) (B.img s t)))
    (h : B.R s t) {A : VarType} {a : Ann A} (u : Term σ Γ A a) :
    Term.mono ((B.w t).le hij) (Term.subst (arrowIdx (B.img s t)) (arrowS σ _ (B.img s t))
        ((B.arOk h i).restrict e) ((B.arCoh h i).restrict e) u) =
      Term.subst (arrowIdx (B.img s t)) (arrowS σ ((B.w t).ctx j) (B.img s t)) hθ hc u := by
  rw [Term.mono_subst]
  exact eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ (fun v T hv => by
    rw [arrowS_mono]; exact .refl _) u)).2

/-- Substituting along a witness arrow into a later stage of the target is weakening. -/
theorem subst_arrowX_mono {s t : B.W} {Γ : Ctx} {x : VarSymb} (i : ℕ) (j : ℕ)
    (hij : B.stg s t i ≤ j) (e : Γ.Le (((B.w s).ctx i).diaIn x))
    (hθ : Subst.Ok Γ (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t x)))
    (hc : Subst.Coh (arrowXIdx (B.img s t) x (B.cx s t x)) Γ
      (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t x)))
    (hm : ∃ X, B.lb s t x = some X) (hx : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X))
    {A : VarType} {a : Ann A} (u : Term σ Γ A a) :
    Term.mono ((B.w t).le hij) (Term.subst (arrowXIdx (B.img s t) x (B.cx s t x))
        (arrowXS σ _ (B.img s t) x (B.cx s t x))
        ((B.arXOk hm i hx).restrict e) ((B.arXCoh hm i hx).restrict e) u) =
      Term.subst (arrowXIdx (B.img s t) x (B.cx s t x))
        (arrowXS σ ((B.w t).ctx j) (B.img s t) x (B.cx s t x)) hθ hc u := by
  rw [Term.mono_subst]
  exact eq_of_heq (Sigma.mk.inj (Term.subst_congr _ _ _ _ _ _ (fun v T hv => by
    rw [arrowXS_mono]; exact .refl _) u)).2

/-- The denotation does not depend on the stage it is computed at. -/
theorem rden_congr : ∀ {A : VarType} {a : Ann A} {Γ : Ctx} (t : Term σ Γ A a) (s : B.W)
    (i j : ℕ) (e : Γ.Le ((B.w s).ctx i)) (e' : Γ.Le ((B.w s).ctx j)),
    B.rden s i e t = B.rden s j e' t
  | _, _, _, .var _ _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := B.w s) (le_max_left i j)
        (le_max_right i j) rfl)
  | _, _, _, .func _, s, i, j, _, _ =>
      Quotient.sound (BWorld.TEq_of_lift_eq (w := B.w s) (le_max_left i j)
        (le_max_right i j) ((Term.mono_mono _ _ _).trans (Term.mono_mono _ _ _).symm))
  | _, _, _, .unit, _, _, _, _, _ => rfl
  | _, _, _, .pair t u, s, i, j, e, e' =>
      Prod.ext (rden_congr t s i j e e') (rden_congr u s i j e e')
  | _, _, _, .boxtm t, s, i, j, e, e' => funext fun a => by
      by_cases hR : B.R s a.1
      swap
      · simp only [rden, dif_neg hR]
        exact rden_congr _ a.1 i j _ _
      simp only [rden, dif_pos hR]
      set K := max (B.stg s a.1 i) (B.stg s a.1 j)
      have hθ : Subst.Ok _ (arrowS σ ((B.w a.1).ctx K) (B.img s a.1)) :=
        (ok_arrowS ((B.imgOk hR i).mono ((B.w a.1).le (le_max_left _ _)))).restrict
          e.boxIn
      have hc : Subst.Coh (arrowIdx (B.img s a.1)) _
          (arrowS σ ((B.w a.1).ctx K) (B.img s a.1)) :=
        (coh_arrowS ((B.imgOk hR i).mono ((B.w a.1).le (le_max_left _ _)))).restrict
          e.boxIn
      have h₁ := (rden_congr _ a.1 (B.stg s a.1 i) K (Ctx.Le.refl _)
        ((B.w a.1).le (le_max_left _ _))).trans
        ((rden_mono ((B.w a.1).le (le_max_left _ _)) _ a.1 K (Ctx.Le.refl _)).symm.trans
          (congrArg (B.rden a.1 K (Ctx.Le.refl _))
            (subst_arrow_mono i K (le_max_left _ _) e.boxIn hθ hc hR t)))
      have h₂ := (rden_congr _ a.1 (B.stg s a.1 j) K (Ctx.Le.refl _)
        ((B.w a.1).le (le_max_right _ _))).trans
        ((rden_mono ((B.w a.1).le (le_max_right _ _)) _ a.1 K (Ctx.Le.refl _)).symm.trans
          (congrArg (B.rden a.1 K (Ctx.Le.refl _))
            (subst_arrow_mono j K (le_max_right _ _) e'.boxIn hθ hc hR t)))
      exact h₁.trans h₂.symm
  | _, _, Γ, .diatm x hx t, s, i, j, e, e' =>
      RPos.congr_cont (funext fun a => by
        by_cases hk : ∃ X, B.lb s a.1.1 x = some X
        swap
        · simp only [dif_neg hk]
          obtain ⟨hnR, hr⟩ := mem_extent_self a.2 hk
          set K₁ := max i hr.data.i₀
          set K₂ := max j hr.data.i₀
          have h₁ : ((B.w s).ctx K₁).Le ((B.w s).ctx (max K₁ K₂)) := (B.w s).le (le_max_left _ _)
          have h₂ : ((B.w s).ctx K₂).Le ((B.w s).ctx (max K₁ K₂)) :=
            (B.w s).le (le_max_right _ _)
          have hK : i ≤ max K₁ K₂ := (le_max_left _ _).trans (le_max_left _ _)
          have key : Term.mono h₁ (B.realTerm hr e hx t).2 =
              Term.mono h₂ (B.realTerm hr e' hx t).2 := by
            simp only [realTerm]
            rw [Term.mono_realiseAtA hr.data.hT _
                (hcA' := hr.data.hdeclOf _ (hx.imp fun _ h => ((B.w s).le hK).ref (e.ref h))),
              Term.mono_realiseAtA hr.data.hT _
                (hcA' := hr.data.hdeclOf _ (hx.imp fun _ h => ((B.w s).le hK).ref (e.ref h))),
              Term.mono_mono, Term.mono_mono, Term.mono_mono, Term.mono_mono]
          have hl := B.selfLe (self_of_not_R hnR).2 (max K₁ K₂)
          calc B.rden a.1.1 K₁ _ (B.realTerm hr e hx t).2
              = B.rden a.1.1 (max K₁ K₂) (h₁.trans hl) (B.realTerm hr e hx t).2 :=
                rden_congr _ _ _ _ _ _
            _ = B.rden a.1.1 _ hl (Term.mono h₁ (B.realTerm hr e hx t).2) :=
                (rden_mono h₁ _ _ _ _).symm
            _ = B.rden a.1.1 _ hl (Term.mono h₂ (B.realTerm hr e' hx t).2) := by rw [key]
            _ = B.rden a.1.1 _ (h₂.trans hl) (B.realTerm hr e' hx t).2 := rden_mono h₂ _ _ _ _
            _ = B.rden a.1.1 K₂ _ (B.realTerm hr e' hx t).2 := rden_congr _ _ _ _ _ _
        simp only [dif_pos hk]
        set K := max (B.stg s a.1.1 i) (B.stg s a.1.1 j)
        have hxi : ∃ X, ((B.w s).ctx i).ref x = some (.VTypeDia X) := hx.imp fun _ h => e.ref h
        have hθ : Subst.Ok (Γ.diaIn x)
            (arrowXS σ ((B.w a.1.1).ctx K) (B.img s a.1.1) x (B.cx s a.1.1 x)) := by
          obtain ⟨X, hk⟩ := hk
          obtain ⟨X', hX'⟩ := hxi
          have ee := B.lb_hxX hk i X' hX'
          subst ee
          exact (ok_arrowXS ((B.imgOk (B.lbR hk) i).mono ((B.w a.1.1).le (le_max_left _ _))) hX'
            (((B.w a.1.1).le (le_max_left _ _)).ref (B.lb_hcx hk i))).restrict (e.diaIn x)
        have hc : Subst.Coh (arrowXIdx (B.img s a.1.1) x (B.cx s a.1.1 x)) (Γ.diaIn x)
            (arrowXS σ ((B.w a.1.1).ctx K) (B.img s a.1.1) x (B.cx s a.1.1 x)) := by
          obtain ⟨X, hk⟩ := hk
          obtain ⟨X', hX'⟩ := hxi
          have ee := B.lb_hxX hk i X' hX'
          subst ee
          exact (coh_arrowXS ((B.imgOk (B.lbR hk) i).mono ((B.w a.1.1).le (le_max_left _ _)))
            hX' (((B.w a.1.1).le (le_max_left _ _)).ref (B.lb_hcx hk i))).restrict (e.diaIn x)
        have h₁ := (rden_congr _ a.1.1 (B.stg s a.1.1 i) K (Ctx.Le.refl _)
          ((B.w a.1.1).le (le_max_left _ _))).trans
          ((rden_mono ((B.w a.1.1).le (le_max_left _ _)) _ a.1.1 K (Ctx.Le.refl _)).symm.trans
            (congrArg (B.rden a.1.1 K (Ctx.Le.refl _))
              (subst_arrowX_mono i K (le_max_left _ _) (e.diaIn x) hθ hc hk hxi t)))
        have h₂ := (rden_congr _ a.1.1 (B.stg s a.1.1 j) K (Ctx.Le.refl _)
          ((B.w a.1.1).le (le_max_right _ _))).trans
          ((rden_mono ((B.w a.1.1).le (le_max_right _ _)) _ a.1.1 K (Ctx.Le.refl _)).symm.trans
            (congrArg (B.rden a.1.1 K (Ctx.Le.refl _))
              (subst_arrowX_mono j K (le_max_right _ _) (e'.diaIn x) hθ hc hk
                (hx.imp fun _ h => e'.ref h) t)))
        exact h₁.trans h₂.symm) fun _ => rfl
  termination_by structural A => A

/-- ⭐**The stored shape is the symbolic one**: a term's denotation has the shape `termShp` computes
    for it in the canonical shape environment.  For a `◇` term this is `rden`'s definition.  A `□`
    term's values sit along the arrows, where the environment pushed into `□` is the target's own
    read through `succAddr` (`cEnv_boxPush`) — what translating the body (along a network arrow)
    and collapsing it (along the world's own) need. -/
theorem rawShape_rden (hSh : ModalSys.shaped = true) : ∀ {A : VarType} {a : Ann A} {Γ : Ctx}
    (s : B.W) (i : ℕ) (e : Γ.Le ((B.w s).ctx i)) (t : Term σ Γ A a),
    B.rawShape hSh (B.rden s i e t) = Model.termShp (B.cEnv Γ s) 0 t
  | _, _, _, _, _, _, .var _ _ => rfl
  | _, _, _, _, _, _, .func _ => rfl
  | _, _, _, _, _, _, .unit => rfl
  | _, _, _, s, i, e, .pair u v => by
      change Shp.prod (B.rawShape hSh (B.rden s i e u)) (B.rawShape hSh (B.rden s i e v)) = _
      rw [rawShape_rden hSh s i e u, rawShape_rden hSh s i e v]
      rfl
  | _, _, Γ, s, i, e, .boxtm t => by
      change Shp.box (Arrows.transposeShp (F := B.arrows) (Root := fun _ => VarSymb) fun a =>
          B.rawShape hSh (B.rden s i e (.boxtm t) a)) =
        Shp.box (Model.termShp ((B.cEnv Γ s).boxPush 0) (0 + 1) t)
      rw [Model.termShp_transpose ((B.cEnv Γ s).boxPush 0)
        (fun a => B.canonEnvF Γ.boxIn a.1 (B.succAddr s a)) 0 (B.cEnv_boxPush Γ s) t]
      refine congrArg Shp.box (congrArg _ (funext fun a => ?_))
      by_cases hR : B.R s a.1
      · rw [rden_boxtm_net e t a hR, rawShape_rden hSh, B.termShp_arrow_cEnv hR e t,
          show B.succAddr s a = arrowIdx (B.img s a.1) from funext (succAddr_net hR)]
      · rw [rden_boxtm_self e t a hR, rawShape_rden hSh,
          B.termShp_collapse_cEnv (self_of_not_R hR).1,
          show B.succAddr s a = fun v => v.collapse 0 from funext (succAddr_self hR)]
  | _, _, _, _, _, _, .diatm _ _ _ => rfl
  termination_by structural A => A

/-! ## Realised contents -/

/-- A realised pair's content is the pair of the realised components. -/
theorem rden_realTerm_pair {s t : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {Γ : Ctx} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A C : VarType}
    {a : Ann A} {c : Ann C} (u : Term σ (Γ.diaIn x) A a) (v : Term σ (Γ.diaIn x) C c)
    (hl : ((B.w s).ctx (max i hr.data.i₀)).Le ((B.w t).ctx (max i hr.data.i₀))) :
    B.rden t _ hl (B.realTerm hr e hx (Term.pair u v)).2 =
      ((B.rden t _ hl (B.realTerm hr e hx u).2, B.rden t _ hl (B.realTerm hr e hx v).2) :
        B.RDom (.VTypeProd A C) t) :=
  rfl

/-- ⭐The realised content of a term of the `□` view is what the term denotes here: realisation
    collapses it, so the witness plays no part. -/
theorem rden_realTerm_mono_boxIn {s t : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {Γ : Ctx}
    {i : ℕ} (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) {A : VarType}
    {a : Ann A} (b : Term σ Γ.boxIn A a)
    (hl : ((B.w s).ctx (max i hr.data.i₀)).Le ((B.w t).ctx (max i hr.data.i₀)))
    (hl' : Γ.Le ((B.w t).ctx i)) :
    B.rden t _ hl (B.realTerm hr e hx (Term.mono (Ctx.le_boxIn_diaIn Γ x) b)).2 =
      B.rden t i hl' (Term.collapse (Ctx.collapses_boxIn_self hr.T Γ) b) := by
  have hle : Γ.boxIn.Le ((B.w s).ctx (max i hr.data.i₀)).boxIn :=
    (e.trans ((B.w s).le (le_max_left _ _))).boxIn
  have hcomb : Term.mono ((e.trans ((B.w s).le (le_max_left _ _))).diaIn x)
      (Term.mono (Ctx.le_boxIn_diaIn Γ x) b) =
      Term.mono (Ctx.le_boxIn_diaIn ((B.w s).ctx (max i hr.data.i₀)) x) (Term.mono hle b) := by
    rw [Term.mono_mono, Term.mono_mono]
  simp only [realTerm]
  rw [hcomb, rden_sigma _ (Term.realiseAtA_mono_boxIn hr.data.hT x _ _ (Term.mono hle b)),
    Term.collapse_mono (Ctx.collapses_boxIn_self hr.T Γ)
      (Ctx.collapses_boxIn_self hr.data.hT ((B.w s).ctx (max i hr.data.i₀))) hle
      (e.trans ((B.w s).le (le_max_left _ _))) b,
    rden_mono]
  exact rden_congr _ _ _ _ _ _

/-- ⭐The realised content of the witness's own content address is the datum's content. -/
theorem rden_realTerm_eta {s t : B.W} {x : VarSymb} (hr : (B.w s).Realised x) {Γ : Ctx} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hdia : (Γ.diaIn x).ref (.step x .dia) = some hr.data.A)
    (hl : ((B.w s).ctx (max i hr.data.i₀)).Le ((B.w t).ctx (max i hr.data.i₀)))
    (hl' : ((B.w s).ctx hr.data.i₀).Le ((B.w t).ctx hr.data.i₀)) :
    B.rden t _ hl (B.realTerm hr e hx (Term.eta (.step x .dia) hr.data.A hdia)).2 =
      B.rden t hr.data.i₀ hl' hr.data.t₀ := by
  have hdecl : ((B.w s).ctx (max i hr.data.i₀)).ref x = some (.VTypeDia hr.data.A) :=
    hr.data.hdeclOf _ (hx.imp fun _ h => ((B.w s).le (le_max_left _ _)).ref (e.ref h))
  have hmono : (⟨_, Term.mono ((e.trans ((B.w s).le (le_max_left _ _))).diaIn x)
      (Term.eta (.step x .dia) hr.data.A hdia)⟩ : Σ z : Ann hr.data.A,
        Term σ (((B.w s).ctx (max i hr.data.i₀)).diaIn x) hr.data.A z) =
      ⟨_, Term.eta (.step x .dia) hr.data.A (Ctx.ref_diaIn_of hdecl)⟩ := by
    rw [Term.mono_eta]
  simp only [realTerm]
  rw [rden_sigma _ (Canon.Term.realiseAtA_sigma hr.data.hT x hdecl _ hmono),
    rden_sigma _ (Term.realiseAtA_eta hr.data.hT x hdecl
      (Term.mono ((B.w s).le (le_max_right _ _)) hr.data.t₀)),
    rden_mono]
  exact rden_congr _ _ _ _ _ _

/-! ## Definable objects -/

/-- ⭐The raw objects denoted by terms. -/
def Definable (A : VarType) (s : B.W) (o : B.RDom A s) : Prop :=
  ∃ (i : ℕ) (a : Ann A) (t : Term σ ((B.w s).ctx i) A a), B.rden s i (Ctx.Le.refl _) t = o

theorem definable_rden {A : VarType} {a : Ann A} {Γ : Ctx} {s : B.W} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (t : Term σ Γ A a) : Definable A s (B.rden s i e t) :=
  ⟨i, a, Term.mono e t, by rw [rden_mono]⟩

theorem rden_var_cls {s : B.W} {i : ℕ} :
    ∀ (t : Term σ ((B.w s).ctx i) .Var .var), B.rden s i (Ctx.Le.refl _) t = (B.w s).cls i t
  | .var _ _ => rfl
  | .func f => by
      change (B.w s).cls i (Term.mono (Ctx.Le.refl _) (.func f)) = _
      rw [Term.mono_refl]

theorem definable_var {s : B.W} (d : (B.w s).D) : Definable .Var s d :=
  Quotient.inductionOn d fun p => ⟨p.1, .var, p.2, rden_var_cls p.2⟩

theorem definable_unit {s : B.W} (o : B.RDom .VTypeOne s) : Definable .VTypeOne s o :=
  ⟨0, .one, .unit, rfl⟩

theorem definable_fst {A C : VarType} {s : B.W} {o : B.RDom (.VTypeProd A C) s}
    (h : Definable (.VTypeProd A C) s o) : Definable A s o.1 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair u _ => exact ⟨i, _, u, rfl⟩

theorem definable_snd {A C : VarType} {s : B.W} {o : B.RDom (.VTypeProd A C) s}
    (h : Definable (.VTypeProd A C) s o) : Definable C s o.2 := by
  obtain ⟨i, a, t, rfl⟩ := h
  cases t with
  | pair _ u => exact ⟨i, _, u, rfl⟩

theorem definable_pair {A C : VarType} {s : B.W} {o₁ : B.RDom A s} {o₂ : B.RDom C s}
    (h₁ : Definable A s o₁) (h₂ : Definable C s o₂) :
    Definable (.VTypeProd A C) s ((o₁, o₂) : B.RDom (.VTypeProd A C) s) := by
  obtain ⟨i₁, a₁, t₁, rfl⟩ := h₁
  obtain ⟨i₂, a₂, t₂, rfl⟩ := h₂
  refine ⟨max i₁ i₂, _, .pair ((B.w s).liftT (le_max_left _ _) t₁)
    ((B.w s).liftT (le_max_right _ _) t₂), Prod.ext ?_ ?_⟩
  · change B.rden s _ _ (Term.mono _ t₁) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _
  · change B.rden s _ _ (Term.mono _ t₂) = _
    rw [rden_mono]
    exact rden_congr _ _ _ _ _ _

theorem definable_box_apply {A : VarType} {s : B.W} {o : B.RDom (.VTypeBox A) s}
    (h : Definable (.VTypeBox A) s o) (a : B.Acc s) : Definable A a.1 (o a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | boxtm b =>
      simp only [rden]
      split <;> exact definable_rden _ _

theorem definable_dia_apply {A : VarType} {s : B.W} {o : B.RDom (.VTypeDia A) s}
    (h : Definable (.VTypeDia A) s o) (a : o.1) : Definable A a.1.1 (o.2 a) := by
  obtain ⟨i, _, t, rfl⟩ := h
  cases t with
  | diatm x hx b =>
      simp only [rden]
      split <;> exact definable_rden _ _

end BData

end BArrow

end V12M
