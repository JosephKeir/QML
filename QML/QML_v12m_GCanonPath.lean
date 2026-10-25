import QML.QML_v12m_GLimit

/-!
# QML v12m — the growing tree's canonical model: paths

Under 4 the canonical model's arrows are the tree's **paths**: a world `t` is accessible from `s`
when it is a descendant (`GR`), reached by a list of child indices, the first step first
(`nodeOf`); under T the empty path is the identity arrow, along which a view is collapsed.
The tree is a tree, so the path is unique (`nodeOf_inj`).

Along a path, the `□` view of a stage is translated **edge by edge, from the front**
(`docs/v12-modal-extensions.md` §3 4, "The canonical model on the growing tree: paper pass", 2):
* along one edge, by its committed entries (`fmapL`);
* along `c :: P`, the body is first **kept** (shifted one view in, `Term.shift`), translated along
  the first edge by the `□`-lift of its substitution (`Subst.box`), and the result translated
  along `P` (`pTr`).
A witness's view goes the same way (`pTrX`), along a path in its **extent** (`InExt`): the last
edge is made for the witness kept along the rest — the address the first edge's entry for
`x.keep` names (`wit`; for a lifted term, its witness).  The stage reached is `pstg`.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## Paths -/

/-- The node at the end of a path of child indices from `s`, the first step first. -/
def nodeOf : Node → List ℕ → Node
  | s, [] => s
  | s, c :: P => nodeOf (c :: s) P

omit [ModalSys] in
theorem nodeOf_eq : ∀ (s : Node) (P : List ℕ), nodeOf s P = P.reverse ++ s
  | _, [] => rfl
  | s, c :: P => by
      rw [nodeOf, nodeOf_eq (c :: s) P, List.reverse_cons, List.append_assoc]
      rfl

omit [ModalSys] in
theorem nodeOf_suffix (s : Node) (P : List ℕ) : s <:+ nodeOf s P := by
  rw [nodeOf_eq]
  exact List.suffix_append _ _

omit [ModalSys] in
/-- ⭐The path to a descendant is unique. -/
theorem nodeOf_inj {s : Node} {P Q : List ℕ} (h : nodeOf s P = nodeOf s Q) : P = Q := by
  rw [nodeOf_eq, nodeOf_eq] at h
  exact List.reverse_injective (List.append_cancel_right h)

omit [ModalSys] in
theorem nodeOf_append (s : Node) : ∀ (P Q : List ℕ), nodeOf s (P ++ Q) = nodeOf (nodeOf s P) Q
  | [], _ => rfl
  | c :: P, Q => nodeOf_append (c :: s) P Q

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem live_of_suffix {N : GNetSt σ} : ∀ {q k : Node}, N.Live (q ++ k) → N.Live k
  | [], _, h => h
  | _ :: q, _, h => live_of_suffix (q := q) h.1

theorem gborn_of_suffix {k k' : Node} (hk : GBorn hF M₀ k') (h : k <:+ k') : GBorn hF M₀ k := by
  obtain ⟨q, rfl⟩ := h
  obtain ⟨n, hn⟩ := hk
  exact ⟨n, live_of_suffix hn⟩

/-- A path that is an arrow: nonempty, or empty under T (the identity arrow). -/
abbrev PathOk (P : List ℕ) : Prop := P ≠ [] ∨ ModalSys.T = true

theorem PathOk.T_of_nil (h : PathOk []) : ModalSys.T = true := h.resolve_left fun e => e rfl

theorem pathOk_cons {c : ℕ} {P : List ℕ} : PathOk (c :: P) := Or.inl (List.cons_ne_nil _ _)

/-- ⭐Accessibility: a descendant along a path — a strict one, or, under T, the world itself. -/
def GR (s t : GW hF M₀) : Prop := ∃ P : List ℕ, PathOk P ∧ t.1 = nodeOf s.1 P

/-- Worlds with one node are one world. -/
theorem gw_eq {s t : GW hF M₀} (h : t.1 = s.1) : t = s := Subtype.ext h

/-- The empty path's end is its start, at every stage. -/
theorem glat_le_of_eq {s t : GW hF M₀} (h : t.1 = s.1) (i : ℕ) :
    (ctxOf (glat s i)).Le (ctxOf (glat t i)) := by
  rw [gw_eq h]
  exact Ctx.Le.refl _

/-- The world one step along a path. -/
def stepW (s : GW hF M₀) (c : ℕ) (hb : GBorn hF M₀ (c :: s.1)) : GW hF M₀ := ⟨c :: s.1, hb⟩

theorem born_step {s t : GW hF M₀} {c : ℕ} {P : List ℕ} (h : t.1 = nodeOf s.1 (c :: P)) :
    GBorn hF M₀ (c :: s.1) :=
  gborn_of_suffix t.2 (h ▸ nodeOf_suffix _ _)

/-! ## Stages along a path -/

/-- The stage of the path's end where stage `i` of its start is read. -/
noncomputable def pstg : (s t : GW hF M₀) → (P : List ℕ) → t.1 = nodeOf s.1 P → ℕ → ℕ
  | _, _, [], _, i => i
  | s, t, [_], _, i => glstg s t i
  | s, t, c :: c' :: P, h, i =>
      pstg (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)

/-! ## Translating along a path -/

/-- ⭐**A `□` view's term translated along a path**: along one edge by its entries; along
    `c :: P`, kept, translated by the first edge's `□`-lift, then along `P`. -/
noncomputable def pTr (hM₀ : Theory.IsMCS M₀) :
    (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → PathOk P → (i : ℕ) →
    {A : VarType} → {a : Ann A} → Term σ ((ctxOf (glat s i)).kView none) A a →
      Σ b : Ann A, Term σ (ctxOf (glat t (pstg s t P h i))) A b
  | s, _, [], h, hP, i, _, _, b =>
      ⟨_, Term.mono (glat_le_of_eq h i)
        (Term.collapse (Ctx.collapses_boxIn_self hP.T_of_nil (ctxOf (glat s i))) b)⟩
  | _, t, [c], h, _, i, _, _, b =>
      ⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) b⟩
  | s, t, c :: c' :: P, h, _, i, _, _, b =>
      pTr hM₀ (stepW s c (born_step h)) t (c' :: P) h pathOk_cons
        (glstg s (stepW s c (born_step h)) i)
        (Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          (eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).box
          (Subst.ok_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Subst.coh_box (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i)))
          (Term.shift (Ctx.shifts_boxIn_boxIn hF _) b))

/-! ## Witnesses along a path -/

/-- The witness an edge keeps `x` as: the address its entry for `x.keep` names (for a lifted
    term `⟨z; t⟩`, its witness `z`). -/
noncomputable def wit (w : GW hF M₀) (x : VarSymb) : VarSymb :=
  eIdx (fmapL hF M₀ w.1) (.step x .keep)

/-- ⭐**A path in a witness's extent**: its last edge is made for the witness kept along the rest. -/
def InExt : (s t : GW hF M₀) → (P : List ℕ) → t.1 = nodeOf s.1 P → VarSymb → Prop
  | _, _, [], _, _ => False
  | _, t, [_], _, x => lkd t = some x
  | s, t, c :: c' :: P, h, x =>
      InExt (stepW s c (born_step h)) t (c' :: P) h (wit (stepW s c (born_step h)) x)

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- What an entry of possible type names as its witness is declared, at a possible type. -/
theorem wit_decl {Δ : Ctx} {e : LEnt σ} {X : VarType} (he : (entOf Δ e).OkRef (.VTypeDia X)) :
    ∃ Z, Δ.ref (entIdx e []) = some (.VTypeDia Z) := by
  match e, he with
  | .inl w, he => exact ⟨X, he⟩
  | .inr ⟨l, U, a, t⟩, he =>
      have hl : (ctxOf l).Le Δ := by
        by_contra hn
        rw [show entOf Δ (.inr ⟨l, U, a, t⟩) = .hide from dif_neg hn] at he
        exact he
      rw [entOf_tm hl t] at he
      cases he
      match a, t with
      | .dia z _, .diatm _ hz _ => exact hz.imp fun _ h => hl.ref h

/-- The kept witness of a declared possible address is declared at the next world. -/
theorem wit_ref (hM₀ : Theory.IsMCS M₀) {s : GW hF M₀} {c : ℕ} (hb : GBorn hF M₀ (c :: s.1))
    (i : ℕ) {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ∃ Z, (ctxOf (glat (stepW s c hb) (glstg s (stepW s c hb) i))).ref (wit (stepW s c hb) x) =
      some (.VTypeDia Z) := by
  obtain ⟨X, hX⟩ := hx
  have hk := gentOk_box hM₀ (t := stepW s c hb) ⟨c, rfl⟩ i (.step x .keep) (.VTypeDia X) rfl
    (Ctx.boxIn_keep_of' hF hX rfl)
  rw [show wit (stepW s c hb) x = entIdx (fmapL hF M₀ (stepW s c hb).1 (.step x .keep)) [] from
    eIdx_item _ (reach_ppath hX).1 rfl []]
  exact wit_decl hk

/-- ⭐**A witness's view translated along a path in its extent**: along one edge made for it by
    the edge's entries; along `c :: P`, kept (`four_dia`'s shift), translated by the first edge's
    `◇`-lift at `x.keep`, then along `P` with the kept witness. -/
noncomputable def pTrX (hM₀ : Theory.IsMCS M₀) :
    (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → (i : ℕ) → (x : VarSymb) →
    (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) → InExt s t P h x →
    {A : VarType} → {a : Ann A} → Term σ ((ctxOf (glat s i)).kView (some x)) A a →
      Σ b : Ann A, Term σ (ctxOf (glat t (pstg s t P h i))) A b
  | _, _, [], _, _, _, _, hm, _, _, _ => hm.elim
  | _, t, [c], h, i, _, _, hm, _, _, u =>
      ⟨_, Term.subst (eIdx (fmapL hF M₀ t.1)) (eS σ _ (fmapL hF M₀ t.1))
        (ok_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) (coh_eS_kView (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) u⟩
  | s, t, c :: c' :: P, h, i, x, hx, hm, _, _, u =>
      pTrX hM₀ (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
        (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx) hm
        (Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          ((eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c (born_step h)) x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
              (.step x .keep) _
              (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx))
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) u))

/-! ## Witnesses kept along a path (T + 4) -/

/-- The kept witness of a declared possible address is declared at any child. -/
theorem wit_ref_ch (hM₀ : Theory.IsMCS M₀) {s t : GW hF M₀} (hc : GCh hF M₀ s t) (i : ℕ)
    {x : VarSymb} (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) :
    ∃ Z, (ctxOf (glat t (glstg s t i))).ref (wit t x) = some (.VTypeDia Z) := by
  obtain ⟨X, hX⟩ := hx
  have hk := gentOk_box hM₀ hc i (.step x .keep) (.VTypeDia X) rfl
    (Ctx.boxIn_keep_of' hF hX rfl)
  rw [show wit t x = entIdx (fmapL hF M₀ t.1 (.step x .keep)) [] from
    eIdx_item _ (reach_ppath hX).1 rfl []]
  exact wit_decl hk

/-- ⭐**The witness kept along a path**: itself along the empty path; along an edge, the edge's
    kept witness; along `c :: P`, the first edge's kept witness, kept along `P`.  Under T a path
    is in `x`'s extent when its end realises this witness (`docs/v12-modal-extensions.md` §3 4,
    "T + 4 on the growing tree"). -/
noncomputable def kw : (s t : GW hF M₀) → (P : List ℕ) → t.1 = nodeOf s.1 P → VarSymb → VarSymb
  | _, _, [], _, x => x
  | _, t, [_], _, x => wit t x
  | s, t, c :: c' :: P, h, x =>
      kw (stepW s c (born_step h)) t (c' :: P) h (wit (stepW s c (born_step h)) x)

/-- The kept witness is declared at a possible type at the end. -/
theorem kw_decl (hM₀ : Theory.IsMCS M₀) : ∀ (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) {x : VarSymb},
    (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) →
    ∃ Z, (ctxOf (glat t (pstg s t P h i))).ref (kw s t P h x) = some (.VTypeDia Z)
  | _, _, [], h, i, _, hx => hx.imp fun _ e => (glat_le_of_eq h i).ref e
  | _, _, [c], h, i, _, hx => wit_ref_ch hM₀ ⟨c, h⟩ i hx
  | s, t, c :: c' :: P, h, i, _, hx =>
      kw_decl hM₀ (stepW s c (born_step h)) t (c' :: P) h _ (wit_ref hM₀ (born_step h) i hx)

/-- ⭐**A witness's view translated along a path, the witness kept**: along the empty path,
    unchanged; along an edge, kept (`four_dia`'s shift) and translated by the edge's `◇`-lift at
    `x.keep`; along `c :: P`, the first edge's, then along `P` with the kept witness.  These are
    `pTrX`'s steps without reading the content off at the end. -/
noncomputable def pTrXK (hM₀ : Theory.IsMCS M₀) :
    (s t : GW hF M₀) → (P : List ℕ) → (h : t.1 = nodeOf s.1 P) → (i : ℕ) → (x : VarSymb) →
    (∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) →
    {A : VarType} → {a : Ann A} → Term σ ((ctxOf (glat s i)).kView (some x)) A a →
      Σ b : Ann A,
        Term σ ((ctxOf (glat t (pstg s t P h i))).kView (some (kw s t P h x))) A b
  | _, _, [], h, i, _, _, _, _, u => ⟨_, Term.mono ((glat_le_of_eq h i).kView _) u⟩
  | _, t, [c], h, i, x, hx, _, _, u =>
      ⟨_, Term.subst (eIdx (fmapL hF M₀ t.1))
        ((eS σ (ctxOf (glat t (glstg _ t i))) (fmapL hF M₀ t.1)).dia (.step x .keep) (wit t x))
        (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx)
          ((coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
            (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
        (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i))
          (coh_eS_kView (gentOk_box hM₀ ⟨c, h⟩ i)) (Ctx.exists_keep_dia hF hx))
        (Term.shift (Ctx.shifts_diaIn_keep hF _ x) u)⟩
  | s, t, c :: c' :: P, h, i, x, hx, _, _, u =>
      pTrXK hM₀ (stepW s c (born_step h)) t (c' :: P) h (glstg s (stepW s c (born_step h)) i)
        (wit (stepW s c (born_step h)) x) (wit_ref hM₀ (born_step h) i hx)
        (Term.subst (eIdx (fmapL hF M₀ (c :: s.1)))
          ((eS σ (ctxOf (glat (stepW s c (born_step h)) (glstg s (stepW s c (born_step h)) i)))
            (fmapL hF M₀ (c :: s.1))).dia (.step x .keep) (wit (stepW s c (born_step h)) x))
          (Subst.ok_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx)
            ((coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
              (.step x .keep) _ (Ctx.exists_keep_dia hF hx).choose_spec []))
          (Subst.coh_dia (ok_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (coh_eS_kView (gentOk_box hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ i))
            (Ctx.exists_keep_dia hF hx))
          (Term.shift (Ctx.shifts_diaIn_keep hF _ x) u))

/-! ## Later stages -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
/-- An edge's substitution, weakened, is the substitution into the larger context, at every
    address of the view. -/
theorem eS_mono_at {l : List VarType} {k : Option VarSymb} {Δ Δ' : Ctx} (h : Δ.Le Δ')
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView k) Δ g) :
    ∀ (u : VarSymb) {T : VarType}, ((ctxOf l).kView k).ref u = some T →
      ((eS σ Δ g).mono h).at u = (eS σ Δ' g).at u
  | .root r, T, hu => by
      obtain ⟨u, s, e, -⟩ := kView_item (show (ctxOf l).kView k (.root r) = some T from hu)
      cases e
  | .step u s, T, hu => by
      by_cases hs : s.isProj = true
      · rw [Subst.at_proj _ _ hs, Subst.at_proj _ _ hs]
        rw [Ctx.ref_step_proj _ _ hs] at hu
        cases hU : ((ctxOf l).kView k).ref u with
        | none => rw [hU] at hu; cases hu
        | some U => rw [eS_mono_at h hg u hU]
      · have hlp : (VarSymb.step u s).lastProj = false := Bool.eq_false_iff.mpr hs
        rw [Subst.at_nonproj _ hlp, Subst.at_nonproj _ hlp]
        rw [Ctx.ref_nonproj _ hlp] at hu
        change SubE.mono h (eS σ Δ g (.step u s)) = eS σ Δ' g (.step u s)
        rw [eS_item _ hlp, eS_item _ hlp, entOf_mono h (hg _ T hlp hu)]

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sim_box_eS_mono {l : List VarType} {Δ Δ' : Ctx} (h : Δ.Le Δ')
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView none) Δ g) :
    Subst.Sim ((ctxOf l).kView none).boxIn ((eS σ Δ g).box.mono h.boxIn) ((eS σ Δ' g).box) := by
  refine Subst.sim_of ?_
  intro v T _ hv
  match v with
  | .step u .box =>
      change SubE.Sim T (((eS σ Δ g).at u).unbox.mono h.boxIn) ((eS σ Δ' g).at u).unbox
      rw [← eS_mono_at h hg u (Ctx.boxIn_step_box hv), Subst.at_mono, SubE.unbox_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((eS σ Δ g).at u).keepE.mono h.boxIn) ((eS σ Δ' g).at u).keepE
      rw [← eS_mono_at h hg u (Ctx.boxIn_keep hv).2.1, Subst.at_mono, SubE.keepE_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .dia => cases hv
  | .step _ .here => cases hv

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem sim_dia_eS_mono {l : List VarType} {Δ Δ' : Ctx} (h : Δ.Le Δ')
    {g : VarSymb → LEnt σ} (hg : EntOk ((ctxOf l).kView none) Δ g) (x ιx : VarSymb)
    (hx : ∃ X, ((ctxOf l).kView none).ref x = some (.VTypeDia X)) :
    Subst.Sim (((ctxOf l).kView none).diaIn x) (((eS σ Δ g).dia x ιx).mono (h.diaIn ιx))
      ((eS σ Δ' g).dia x ιx) := by
  refine Subst.sim_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx)
          (if u = x then ((eS σ Δ g).at x).diaBody ιx else SubE.hide))
        (if u = x then ((eS σ Δ' g).at x).diaBody ιx else SubE.hide)
      by_cases hux : u = x
      · obtain ⟨X, hX⟩ := hx
        rw [if_pos hux, if_pos hux, ← eS_mono_at h hg x hX, Subst.at_mono, SubE.diaBody_mono]
        exact .refl _
      · rw [if_neg hux, if_neg hux]
        exact .refl _
  | .step u .box =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx)
          ((((eS σ Δ g).at u).unbox).mono (Ctx.le_boxIn_diaIn Δ ιx)))
        ((((eS σ Δ' g).at u).unbox).mono (Ctx.le_boxIn_diaIn Δ' ιx))
      rw [← eS_mono_at h hg u (Ctx.boxIn_step_box (show _ = some T from hv)), Subst.at_mono,
        SubE.unbox_mono, SubE.mono_mono, SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (SubE.mono (h.diaIn ιx)
          ((((eS σ Δ g).at u).keepE).mono (Ctx.le_boxIn_diaIn Δ ιx)))
        ((((eS σ Δ' g).at u).keepE).mono (Ctx.le_boxIn_diaIn Δ' ιx))
      rw [← eS_mono_at h hg u (Ctx.boxIn_keep (show _ = some T from hv)).2.1, Subst.at_mono,
        SubE.keepE_mono, SubE.mono_mono, SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- A stage's context grows into a later stage's. -/
theorem gle (hM₀ : Theory.IsMCS M₀) (s : GW hF M₀) {i i' : ℕ} (h : i ≤ i') :
    (ctxOf (glat s i)).Le (ctxOf (glat s i')) :=
  (gnodeWorld hF hM₀ s.1 s.2).le h

/-- A later stage of the start reaches a later stage of the end. -/
theorem pstg_monotone (hM₀ : Theory.IsMCS M₀) :
    ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) {i i' : ℕ}, i ≤ i' →
      pstg s t P h i ≤ pstg s t P h i'
  | _, _, [], _, _, _, hii => hii
  | _, _, [c], h, _, _, hii => glstg_monotone hM₀ ⟨c, h⟩ hii
  | s, t, c :: c' :: P, h, _, _, hii =>
      pstg_monotone hM₀ (stepW s c (born_step h)) t (c' :: P) h
        (glstg_monotone hM₀ (t := stepW s c (born_step h)) ⟨c, rfl⟩ hii)

theorem pTr_sigma (hM₀ : Theory.IsMCS M₀) (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (hP : PathOk P) (i : ℕ) {A : VarType} {a a' : Ann A}
    {u : Term σ ((ctxOf (glat s i)).kView none) A a}
    {u' : Term σ ((ctxOf (glat s i)).kView none) A a'}
    (e : (⟨a, u⟩ : Σ b : Ann A, Term σ ((ctxOf (glat s i)).kView none) A b) = ⟨a', u'⟩) :
    pTr hM₀ s t P h hP i u = pTr hM₀ s t P h hP i u' := by
  cases e
  rfl

/-- ⭐**Translating a later stage is weakening the translation**. -/
theorem pTr_mono (hM₀ : Theory.IsMCS M₀) :
    ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) (hP : PathOk P) {i i' : ℕ}
      (hii : i ≤ i') {A : VarType} {a : Ann A}
      (b : Term σ ((ctxOf (glat s i)).kView none) A a),
      (⟨_, Term.mono (gle hM₀ t (pstg_monotone hM₀ s t P h hii))
          (pTr hM₀ s t P h hP i b).2⟩ : Σ c, Term σ (ctxOf (glat t (pstg s t P h i'))) A c) =
        pTr hM₀ s t P h hP i' (Term.mono ((gle hM₀ s hii).kView none) b)
  | s, _, [], h, hP, i, i', hii, _, _, b => by
      have hT := hP.T_of_nil
      change (⟨_, Term.mono _ (Term.mono _ (Term.collapse _ b))⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.mono _ (Term.collapse _ (Term.mono _ b))⟩
      rw [Term.collapse_mono (Ctx.collapses_boxIn_self hT (ctxOf (glat s i)))
        (Ctx.collapses_boxIn_self hT (ctxOf (glat s i'))) (gle hM₀ s hii).boxIn (gle hM₀ s hii),
        Term.mono_mono, Term.mono_mono]
  | _, t, [c], h, _, i, i', hii, _, _, b => by
      change (⟨_, Term.mono _ (Term.subst _ _ _ _ b)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.subst _ _ _ _ (Term.mono _ b)⟩
      rw [Term.mono_subst, Term.subst_mono]
      exact Term.subst_congr _ _ _ _ _ _
        (sim_eS_mono _ (gentOk_box hM₀ ⟨c, h⟩ i)) b
  | s, t, c :: c' :: P, h, _, i, i', hii, _, _, b => by
      have hw := born_step h
      have hg := glstg_monotone hM₀ (t := stepW s c hw) ⟨c, rfl⟩ hii
      refine (pTr_mono hM₀ (stepW s c hw) t (c' :: P) h pathOk_cons hg _).trans ?_
      simp only [pTr]
      refine pTr_sigma hM₀ _ _ _ _ _ _ ?_
      rw [Term.mono_subst, Term.shift_mono (Ctx.shifts_boxIn_boxIn hF _)
        (Ctx.shifts_boxIn_boxIn hF _) ((gle hM₀ s hii).kView none) ((gle hM₀ s hii).boxIn.boxIn),
        Term.subst_mono]
      refine Term.subst_congr _ _ _ _ _ _ ?_ _
      exact sim_box_eS_mono (gle hM₀ (stepW s c hw) hg)
        (gentOk_box hM₀ (t := stepW s c hw) ⟨c, rfl⟩ i)

theorem pTrX_sigma (hM₀ : Theory.IsMCS M₀) (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X)) (hm : InExt s t P h x)
    {A : VarType} {a a' : Ann A} {u : Term σ ((ctxOf (glat s i)).kView (some x)) A a}
    {u' : Term σ ((ctxOf (glat s i)).kView (some x)) A a'}
    (e : (⟨a, u⟩ : Σ b : Ann A, Term σ ((ctxOf (glat s i)).kView (some x)) A b) = ⟨a', u'⟩) :
    pTrX hM₀ s t P h i x hx hm u = pTrX hM₀ s t P h i x hx hm u' := by
  cases e
  rfl

/-- ⭐**Translating a witness's view at a later stage is weakening the translation**. -/
theorem pTrX_mono (hM₀ : Theory.IsMCS M₀) :
    ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) {i i' : ℕ} (hii : i ≤ i')
      (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
      (hm : InExt s t P h x) {A : VarType} {a : Ann A}
      (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
      (⟨_, Term.mono (gle hM₀ t (pstg_monotone hM₀ s t P h hii))
          (pTrX hM₀ s t P h i x hx hm u).2⟩ : Σ c, Term σ (ctxOf (glat t (pstg s t P h i'))) A c) =
        pTrX hM₀ s t P h i' x (hx.imp fun _ e => (gle hM₀ s hii).ref e) hm
          (Term.mono ((gle hM₀ s hii).kView (some x)) u)
  | _, _, [], _, _, _, _, _, _, hm, _, _, _ => hm.elim
  | _, t, [c], h, i, i', hii, x, _, hm, _, _, u => by
      change (⟨_, Term.mono _ (Term.subst _ _ _ _ u)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.subst _ _ _ _ (Term.mono _ u)⟩
      rw [Term.mono_subst, Term.subst_mono]
      exact Term.subst_congr _ _ _ _ _ _
        (sim_eS_mono _ (hm ▸ gentOk hM₀ ⟨c, h⟩ i)) u
  | s, t, c :: c' :: P, h, i, i', hii, x, hx, hm, _, _, u => by
      have hw := born_step h
      have hg := glstg_monotone hM₀ (t := stepW s c hw) ⟨c, rfl⟩ hii
      refine (pTrX_mono hM₀ (stepW s c hw) t (c' :: P) h hg _ _ hm _).trans ?_
      simp only [pTrX]
      refine pTrX_sigma hM₀ (stepW s c hw) t (c' :: P) h _ _ _ hm ?_
      rw [Term.mono_subst, Term.shift_mono (Ctx.shifts_diaIn_keep hF _ x)
        (Ctx.shifts_diaIn_keep hF _ x) ((gle hM₀ s hii).kView (some x))
        ((gle hM₀ s hii).boxIn.diaIn _), Term.subst_mono]
      refine Term.subst_congr _ _ _ _ _ _ ?_ _
      exact sim_dia_eS_mono (gle hM₀ (stepW s c hw) hg)
        (gentOk_box hM₀ (t := stepW s c hw) ⟨c, rfl⟩ i) _ _
        (Ctx.exists_keep_dia hF hx)

theorem pTrXK_sigma (hM₀ : Theory.IsMCS M₀) (s t : GW hF M₀) (P : List ℕ)
    (h : t.1 = nodeOf s.1 P) (i : ℕ) (x : VarSymb)
    (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
    {A : VarType} {a a' : Ann A} {u : Term σ ((ctxOf (glat s i)).kView (some x)) A a}
    {u' : Term σ ((ctxOf (glat s i)).kView (some x)) A a'}
    (e : (⟨a, u⟩ : Σ b : Ann A, Term σ ((ctxOf (glat s i)).kView (some x)) A b) = ⟨a', u'⟩) :
    pTrXK hM₀ s t P h i x hx u = pTrXK hM₀ s t P h i x hx u' := by
  cases e
  rfl

/-- Keeping a witness's view along a path at a later stage is weakening the kept view. -/
theorem pTrXK_mono (hM₀ : Theory.IsMCS M₀) :
    ∀ (s t : GW hF M₀) (P : List ℕ) (h : t.1 = nodeOf s.1 P) {i i' : ℕ} (hii : i ≤ i')
      (x : VarSymb) (hx : ∃ X, (ctxOf (glat s i)).ref x = some (.VTypeDia X))
      {A : VarType} {a : Ann A} (u : Term σ ((ctxOf (glat s i)).kView (some x)) A a),
      (⟨_, Term.mono ((gle hM₀ t (pstg_monotone hM₀ s t P h hii)).kView _)
          (pTrXK hM₀ s t P h i x hx u).2⟩ :
          Σ c, Term σ ((ctxOf (glat t (pstg s t P h i'))).kView (some (kw s t P h x))) A c) =
        pTrXK hM₀ s t P h i' x (hx.imp fun _ e => (gle hM₀ s hii).ref e)
          (Term.mono ((gle hM₀ s hii).kView (some x)) u)
  | _, _, [], _, _, _, _, _, _, _, _, u => by
      change (⟨_, Term.mono _ (Term.mono _ u)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.mono _ (Term.mono _ u)⟩
      rw [Term.mono_mono, Term.mono_mono]
  | s, t, [c], h, i, i', hii, x, hx, _, _, u => by
      have hg := glstg_monotone hM₀ (t := t) ⟨c, h⟩ hii
      change (⟨_, Term.mono _ (Term.subst _ _ _ _ _)⟩ : Σ c, Term σ _ _ c) =
        ⟨_, Term.subst _ _ _ _ _⟩
      rw [Term.mono_subst, Term.shift_mono (Ctx.shifts_diaIn_keep hF _ x)
        (Ctx.shifts_diaIn_keep hF _ x) ((gle hM₀ s hii).kView (some x))
        ((gle hM₀ s hii).boxIn.diaIn _), Term.subst_mono]
      refine Term.subst_congr _ _ _ _ _ _ ?_ _
      exact sim_dia_eS_mono (gle hM₀ t hg) (gentOk_box hM₀ ⟨c, h⟩ i) _ _
        (Ctx.exists_keep_dia hF hx)
  | s, t, c :: c' :: P, h, i, i', hii, x, hx, _, _, u => by
      have hw := born_step h
      have hg := glstg_monotone hM₀ (t := stepW s c hw) ⟨c, rfl⟩ hii
      refine (pTrXK_mono hM₀ (stepW s c hw) t (c' :: P) h hg _ _ _).trans ?_
      simp only [pTrXK]
      refine pTrXK_sigma hM₀ (stepW s c hw) t (c' :: P) h _ _ _ ?_
      rw [Term.mono_subst, Term.shift_mono (Ctx.shifts_diaIn_keep hF _ x)
        (Ctx.shifts_diaIn_keep hF _ x) ((gle hM₀ s hii).kView (some x))
        ((gle hM₀ s hii).boxIn.diaIn _), Term.subst_mono]
      refine Term.subst_congr _ _ _ _ _ _ ?_ _
      exact sim_dia_eS_mono (gle hM₀ (stepW s c hw) hg)
        (gentOk_box hM₀ (t := stepW s c hw) ⟨c, rfl⟩ i) _ _
        (Ctx.exists_keep_dia hF hx)

/-! ## Arrows -/

open Classical in
/-- The path of an arrow. -/
noncomputable def pathOf {s t : GW hF M₀} (h : GR s t) : List ℕ := Classical.choose h

open Classical in
theorem pathOf_ok {s t : GW hF M₀} (h : GR s t) : PathOk (pathOf h) :=
  (Classical.choose_spec h).1

open Classical in
theorem pathOf_eq {s t : GW hF M₀} (h : GR s t) : t.1 = nodeOf s.1 (pathOf h) :=
  (Classical.choose_spec h).2

/-- The chosen path is any path. -/
theorem pathOf_of {s t : GW hF M₀} (hR : GR s t) {P : List ℕ} (h : t.1 = nodeOf s.1 P) :
    pathOf hR = P :=
  nodeOf_inj ((pathOf_eq hR).symm.trans h)

/-- ⭐The frame is transitive: paths compose. -/
theorem gtrans {s t u : GW hF M₀} (h₁ : GR s t) (h₂ : GR t u) : GR s u := by
  obtain ⟨P, hP, e₁⟩ := h₁
  obtain ⟨Q, -, e₂⟩ := h₂
  refine ⟨P ++ Q, hP.imp (fun hP h => hP (List.append_eq_nil_iff.mp h).1) id, ?_⟩
  rw [nodeOf_append, ← e₁]
  exact e₂

/-- Under T every world is its own successor, by the empty path. -/
theorem grefl (hT : ModalSys.T = true) (s : GW hF M₀) : GR s s := ⟨[], Or.inr hT, rfl⟩

theorem pathOf_trans {s t u : GW hF M₀} (h₁ : GR s t) (h₂ : GR t u) :
    pathOf (gtrans h₁ h₂) = pathOf h₁ ++ pathOf h₂ :=
  pathOf_of _ (by rw [nodeOf_append, ← pathOf_eq h₁]; exact pathOf_eq h₂)

theorem pathOf_refl (hT : ModalSys.T = true) (s : GW hF M₀) : pathOf (grefl hT s) = [] :=
  pathOf_of _ rfl

variable (hF M₀) in
/-- ⭐The growing tree's arrows: descendants, composed by appending paths; under T the empty path
    is the identity. -/
abbrev garrows : Arrows.{0, 0} σ where
  W := GW hF M₀
  R := GR
  refl := fun hT s => grefl hT s
  trans := fun _ {_ _ _} h₁ h₂ => gtrans h₁ h₂
  refl_trans := fun _ _ _ _ _ => rfl
  trans_refl := fun _ _ _ _ _ => rfl
  trans_assoc := fun _ _ _ _ _ _ _ _ => rfl

/-! ## The root action: keeping a witness along an arrow -/

theorem kw_path {s t : GW hF M₀} {P P' : List ℕ} (e : P = P') (h : t.1 = nodeOf s.1 P)
    (h' : t.1 = nodeOf s.1 P') (x : VarSymb) : kw s t P h x = kw s t P' h' x := by
  subst e
  rfl

/-- ⭐**Keeping along a composite is keeping twice.** -/
theorem kw_append : ∀ (P : List ℕ) {s t u : GW hF M₀} (Q : List ℕ) (h₁ : t.1 = nodeOf s.1 P)
    (h₂ : u.1 = nodeOf t.1 Q) (h : u.1 = nodeOf s.1 (P ++ Q)) (x : VarSymb),
    kw s u (P ++ Q) h x = kw t u Q h₂ (kw s t P h₁ x)
  | [], s, t, u, Q, h₁, h₂, h, x => by
      obtain rfl := gw_eq h₁
      rfl
  | [c], s, ⟨tn, tb⟩, u, [], h₁, h₂, h, x => by
      change tn = c :: s.1 at h₁
      subst h₁
      obtain rfl := gw_eq h₂
      rfl
  | [c], s, ⟨tn, tb⟩, u, c' :: Q, h₁, h₂, h, x => by
      change tn = c :: s.1 at h₁
      subst h₁
      rfl
  | c :: c' :: P, s, t, u, Q, h₁, h₂, h, x =>
      kw_append (c' :: P) (s := stepW s c (born_step h₁)) Q h₁ h₂ h _

/-- ⭐**The canonical root action**: a root possibility, named by its address, kept along an
    arrow is the witness kept along the arrow's path. -/
noncomputable def gRk (s : GW hF M₀) (r : VarSymb) (a : (garrows hF M₀).Acc s) : VarSymb :=
  kw s a.1 (pathOf a.2.down) (pathOf_eq a.2.down) r

/-- The canonical root action, on leaves: a root path stays a root path (`gRk`). -/
noncomputable instance instRootKeepG : Arrows.RootKeep (garrows hF M₀) (fun _ => VarSymb) :=
  Arrows.RootKeep.ofRoot fun _ {s} r a => gRk s r a

/-- Its laws: keeping along two arrows is keeping along their composite (`kw_append`), and
    keeping along the identity is the identity. -/
instance instRootKeepLawsG : Arrows.RootKeepLaws (garrows hF M₀) (fun _ => VarSymb) :=
  Arrows.RootKeepLaws.ofRoot _
    (fun _ {s} r a b => by
      change kw a.1 b.1 (pathOf b.2.down) _ (kw s a.1 (pathOf a.2.down) _ r) =
        kw s b.1 (pathOf (gtrans a.2.down b.2.down)) _ r
      rw [kw_path (pathOf_trans a.2.down b.2.down) _
        (by rw [nodeOf_append, ← pathOf_eq a.2.down]; exact pathOf_eq b.2.down),
        kw_append _ _ (pathOf_eq a.2.down) (pathOf_eq b.2.down)])
    (fun hT _ {s} r => by
      change kw s s (pathOf (grefl hT s)) _ r = r
      rw [kw_path (pathOf_refl hT s) _ rfl]
      rfl)

end GArrow

end V12M
