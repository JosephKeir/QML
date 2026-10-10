import QML.QML_v12m_BLeaf

/-!
# QML v12m — B's canonical model: tags determine annotations without T

Under T a family leaf is read back along two arrows, the world's own and a network one
(`BData.leafOf_inj`).  Without T there is no own arrow, but none is needed: the box contents carry
no `here` component, so a network arrow reads a label cut at its first `box`, `r.p.box.q`, as
`(img r).(p ++ q)` (docs §11.20, "The T-free decoder").  Two facts recover the label from that:

* the arrow's images are **injective** on roots (`ImgInj`, a hypothesis here);
* the cut's position is fixed by **typing**: walking the path from the root's type
  (`VarType.walk`), a projection cannot step past a `□` without T (`cut_unique`).

Labels are typed by walking (`BData.LabelTy`), and the walk survives an arrow because box contents
commute with projections (`walk_bc`).  Every world reached along an arrow has one back (B), so
only the anchor needs an arrow out.

* ⭐`cut_unique`, ⭐`walk_bc`;
* ⭐⭐`BData.leafOf_inj_noT`.
-/

namespace V12M

variable [ModalSys]

/-! ## Walking a path through a type -/

/-- The type reached from `T` along a path, if every step applies. -/
def VarType.walk : VarType → List Step → Option VarType
  | T, [] => some T
  | T, s :: p => (T.step s).bind fun U => U.walk p

theorem VarType.walk_append (T : VarType) (p q : List Step) :
    T.walk (p ++ q) = (T.walk p).bind fun U => U.walk q := by
  induction p generalizing T with
  | nil => rfl
  | cons s p ih =>
      simp only [List.cons_append, VarType.walk]
      cases T.step s with
      | none => rfl
      | some U => exact ih U

/-- ⭐**The cut is where the type is a box**: without T a projection cannot step past a `□`, so two
    typed paths that differ only in where their first `box` sits are one path. -/
theorem cut_unique (hT : ModalSys.T = false) :
    ∀ {R : VarType} {p p' q q' : List Step}, PPath p → PPath p' →
      R.walk (p ++ .box :: q) ≠ none → R.walk (p' ++ .box :: q') ≠ none →
      p ++ q = p' ++ q' → p = p' ∧ q = q'
  | _, [], [], _, _, _, _, _, _, h => ⟨rfl, h⟩
  | R, [], s' :: p', q, q', _, hp', hw, hw', h => by
      exfalso
      have hs' : s'.isProj = true := hp' s' List.mem_cons_self
      cases R <;> cases s' <;> simp_all [VarType.walk, VarType.step, Step.isProj]
  | R, s :: p, [], q, q', hp, _, hw, hw', h => by
      exfalso
      have hs : s.isProj = true := hp s List.mem_cons_self
      cases R <;> cases s <;> simp_all [VarType.walk, VarType.step, Step.isProj]
  | R, s :: p, s' :: p', q, q', hp, hp', hw, hw', h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.cons_append, VarType.walk] at hw hw'
      cases hU : R.step s with
      | none => rw [hU] at hw; exact absurd rfl hw
      | some U =>
          rw [hU] at hw hw'
          obtain ⟨rfl, rfl⟩ := cut_unique hT (fun t ht => hp t (List.mem_cons_of_mem _ ht))
            (fun t ht => hp' t (List.mem_cons_of_mem _ ht)) hw hw' h
          exact ⟨rfl, rfl⟩

/-- ⭐**Box contents commute with projections**, without T: walking the box-contents type along a
    projection path and then on is walking the type along it, into its `□`, and on. -/
theorem walk_bc (hT : ModalSys.T = false) :
    ∀ (R : VarType) {p : List Step}, PPath p → ∀ (q : List Step),
      R.walk (p ++ .box :: q) ≠ none → R.bc.walk (p ++ q) = R.walk (p ++ .box :: q)
  | .VTypeBox A, [], _, q, _ => by
      simp only [List.nil_append, VarType.walk, VarType.step, Option.bind_some]
      rw [show (VarType.VTypeBox A).bc = A by simp [VarType.bc, VarType.bcB, hT]]
  | .Var, [], _, q, h => by simp [VarType.walk, VarType.step] at h
  | .VTypeOne, [], _, q, h => by simp [VarType.walk, VarType.step] at h
  | .VTypeProd _ _, [], _, q, h => by simp [VarType.walk, VarType.step] at h
  | .VTypeDia _, [], _, q, h => by simp [VarType.walk, VarType.step] at h
  | R, s :: p, hp, q, h => by
      have hs : s.isProj = true := hp s List.mem_cons_self
      have hp' : PPath p := fun t ht => hp t (List.mem_cons_of_mem _ ht)
      cases R with
      | VTypeProd A C =>
          cases s with
          | fst =>
              simp only [List.cons_append, VarType.walk, VarType.step, Option.bind_some] at h ⊢
              rw [show (VarType.VTypeProd A C).bc = .VTypeProd A.bc C.bc from rfl]
              exact walk_bc hT A hp' q h
          | snd =>
              simp only [List.cons_append, VarType.walk, VarType.step, Option.bind_some] at h ⊢
              rw [show (VarType.VTypeProd A C).bc = .VTypeProd A.bc C.bc from rfl]
              exact walk_bc hT C hp' q h
          | here => simp [VarType.walk, VarType.step] at h
          | _ => simp [Step.isProj] at hs
      | _ =>
          exfalso
          cases s <;> simp_all [VarType.walk, VarType.step, Step.isProj]


namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

variable (B) in
/-- ⭐A label **types** at a world: its path walks from its root's type at some stage. -/
def LabelTy (s : B.W) (y : VarSymb) : Prop :=
  ∃ i R, ((B.w s).ctx i).ref (.root y.rt) = some R ∧ R.walk y.path ≠ none

variable (B) in
/-- ⭐**Injective images**: each network arrow sends distinct roots to distinct roots. -/
def ImgInj : Prop :=
  ∀ {s t : B.W}, B.R s t → ∀ (i r r' : ℕ), r < ((B.w s).l i).length →
    r' < ((B.w s).l i).length → B.img s t r = B.img s t r' → r = r'

omit [ModalSys.NoFour] in
/-- A root of a world's language is a declared free root. -/
theorem root_of_ctxOf {l : List VarType} {r : Root} {R : VarType}
    (h : (ctxOf l).ref (.root r) = some R) : ∃ n, r = .free n ∧ n < l.length := by
  obtain ⟨n, hn⟩ := ctxOf_decl (v := .root r) h
  cases hn
  refine ⟨n, rfl, ?_⟩
  have h' : ctxOf l (.root (.free n)) = some R := h
  rw [ctxOf_root] at h'
  by_contra hlt
  rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hlt)] at h'
  cases h'

omit [ModalSys.NoFour] in
/-- Without T an arrow reads a label cut at a `box` by dropping the `box`. -/
theorem arrowIdx_cut_noT (hT : ModalSys.T = false) (img : ℕ → ℕ) {pre : VarSymb}
    (hpre : PPath pre.path) (rest : List Step) :
    arrowIdx img ((VarSymb.step pre .box).ext rest) =
      (VarSymb.root (imgRoot img pre.rt)).ext (pre.path ++ rest) := by
  rw [arrowIdx_boxExt img hpre, itemImg, itemAt, encPath_noT hT, itemTail_noT hT,
    List.append_nil, VarSymb.ext_append]

/-- ⭐A typed label read along an arrow, past its cut, is typed there: box contents commute with
    projections (`walk_bc`). -/
theorem labelTy_arrow (hT : ModalSys.T = false) {s t : B.W} (hR : B.R s t) {pre : VarSymb}
    {rest : List Step} (hpre : PPath pre.path)
    (h : B.LabelTy s ((VarSymb.step pre .box).ext rest)) :
    B.LabelTy t (arrowIdx (B.img s t) ((VarSymb.step pre .box).ext rest)) := by
  obtain ⟨i, R, hRef, hw⟩ := h
  rw [VarSymb.ext_rt] at hRef
  change ((B.w s).ctx i).ref (.root pre.rt) = some R at hRef
  obtain ⟨n, hn, hlt⟩ := root_of_ctxOf hRef
  have hRn : R = rootTy ((B.w s).l i) n := by
    rw [hn] at hRef
    exact Option.some.inj (hRef.symm.trans (ctxOf_root_lt hlt))
  rw [VarSymb.ext_path] at hw
  change R.walk (pre.path ++ [.box] ++ rest) ≠ none at hw
  rw [List.append_assoc, List.singleton_append] at hw
  refine ⟨B.stg s t i, R.bc, ?_, ?_⟩
  · rw [arrowIdx_cut_noT hT _ hpre, VarSymb.ext_rt, hn, hRn]
    exact B.imgOk hR i n hlt
  · rw [arrowIdx_cut_noT hT _ hpre, VarSymb.ext_path]
    change R.bc.walk (pre.path ++ rest) ≠ none
    rw [walk_bc hT R hpre rest hw]
    exact hw

/-- ⭐⭐**Canonical leaves determine labels, without T**, at a world with an arrow out: one network
    arrow reads a family back — its images are injective (`ImgInj`) and the cut is placed by the
    labels' types (`cut_unique`); the world at its end has an arrow back. -/
theorem leafOf_inj_noT (hT : ModalSys.T = false) (hInj : B.ImgInj) :
    ∀ (m : ℕ) (s : B.W) {y y' : VarSymb}, y.OK → y'.OK → y.lv = m → y'.lv = m →
      B.LabelTy s y → B.LabelTy s y' → (∃ t, B.R s t) →
        B.leafOf s m y = B.leafOf s m y' → y = y'
  | 0, s, y, y', _, _, _, _, _, _, _, h => by
      rw [leafOf_zero, leafOf_zero] at h
      injection h
  | m + 1, s, y, y', hok, hok', hlv, hlv', hty, hty', ⟨t₁, hR⟩, h => by
      obtain ⟨pre, t, rest, hc⟩ := Canon.splitAt_of_lv (show m < y.lv by omega)
      obtain ⟨pre', t', rest', hc'⟩ := Canon.splitAt_of_lv (show m < y'.lv by omega)
      by_cases ht : t = .dia <;> by_cases ht' : t' = .dia
      · subst ht ht'
        rw [leafOf_dia s hc, leafOf_dia s hc'] at h
        injection h with _ h₁ h₂
        rw [(VarSymb.splitAt_spec hc).1, (VarSymb.splitAt_spec hc').1, h₁, h₂]
      · subst ht
        rw [leafOf_dia s hc, leafOf_lvl s hc' ht'] at h
        cases h
      · subst ht'
        rw [leafOf_lvl s hc ht, leafOf_dia s hc'] at h
        cases h
      · obtain ⟨-, hpre, hy, hl⟩ := cut_first hok hlv hc ht
        obtain ⟨-, hpre', hy', hl'⟩ := cut_first hok' hlv' hc' ht'
        rw [leafOf_lvl s hc ht, leafOf_lvl s hc' ht'] at h
        have hf := Arrows.Leaf.fam.inj h
        have h₁ := congrFun hf ⟨t₁, ⟨Or.inl hR⟩⟩
        obtain ⟨hok₁, hlv₁, -⟩ := B.succAddrK_cut ⟨t₁, ⟨Or.inl hR⟩⟩ hok hpre hy hl
        obtain ⟨hok₁', hlv₁', -⟩ := B.succAddrK_cut ⟨t₁, ⟨Or.inl hR⟩⟩ hok' hpre' hy' hl'
        have hty₁ : B.LabelTy t₁ (B.succAddrK s ⟨t₁, ⟨Or.inl hR⟩⟩ m y) := by
          rw [succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR, hy]
          exact labelTy_arrow hT hR hpre (hy ▸ hty)
        have hty₁' : B.LabelTy t₁ (B.succAddrK s ⟨t₁, ⟨Or.inl hR⟩⟩ m y') := by
          rw [succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR, hy']
          exact labelTy_arrow hT hR hpre' (hy' ▸ hty')
        have e₁ := leafOf_inj_noT hT hInj m t₁ hok₁ hok₁' hlv₁ hlv₁' hty₁ hty₁'
          ⟨s, B.symm hR⟩ h₁
        rw [succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR,
          succAddrK_net (a := ⟨t₁, ⟨Or.inl hR⟩⟩) hR, hy, hy', arrowIdx_cut_noT hT _ hpre,
          arrowIdx_cut_noT hT _ hpre'] at e₁
        have hrt := congrArg VarSymb.rt e₁
        have hpath := congrArg VarSymb.path e₁
        simp only [VarSymb.ext_rt, VarSymb.ext_path, VarSymb.rt, VarSymb.path,
          List.nil_append] at hrt hpath
        -- the two roots, at one stage
        obtain ⟨i, R, hRef, hw⟩ := hty
        obtain ⟨i', R', hRef', hw'⟩ := hty'
        rw [hy, VarSymb.ext_rt] at hRef
        rw [hy', VarSymb.ext_rt] at hRef'
        change ((B.w s).ctx i).ref (.root pre.rt) = some R at hRef
        change ((B.w s).ctx i').ref (.root pre'.rt) = some R' at hRef'
        have hK : ((B.w s).ctx (max i i')).ref (.root pre.rt) = some R :=
          ((B.w s).le (le_max_left i i')).ref hRef
        have hK' : ((B.w s).ctx (max i i')).ref (.root pre'.rt) = some R' :=
          ((B.w s).le (le_max_right i i')).ref hRef'
        obtain ⟨n, hn, hlt⟩ := root_of_ctxOf hK
        obtain ⟨n', hn', hlt'⟩ := root_of_ctxOf hK'
        rw [hn, hn'] at hrt
        have hnn : n = n' := hInj hR (max i i') n n' hlt hlt' (Root.free.inj hrt)
        have hrt' : pre.rt = pre'.rt := by rw [hn, hn', hnn]
        rw [← hrt'] at hK'
        obtain rfl : R = R' := Option.some.inj (hK.symm.trans hK')
        -- the cut, by typing
        rw [hy, VarSymb.ext_path] at hw
        rw [hy', VarSymb.ext_path] at hw'
        change R.walk (pre.path ++ [.box] ++ rest) ≠ none at hw
        change R.walk (pre'.path ++ [.box] ++ rest') ≠ none at hw'
        rw [List.append_assoc, List.singleton_append] at hw hw'
        obtain ⟨hp, hr⟩ := cut_unique hT hpre hpre' hw hw' hpath
        have hpe : pre = pre' := by
          rw [VarSymb.eq_root_ext_path pre, VarSymb.eq_root_ext_path pre', hrt', hp]
        rw [hy, hy', hpe, hr]

end BData

end BArrow


/-! ## Typed contexts and annotations -/

/-- Every reachable address of `Δ` walks, from its root's type in `Γ₀`, to its type. -/
def Ctx.Walks (Γ₀ Δ : Ctx) : Prop :=
  ∀ y T, Δ.ref y = some T → ∃ R, Γ₀.ref (.root y.rt) = some R ∧ R.walk y.path = some T

/-- It suffices that the declared addresses walk: projections walk on by `VarType.step`. -/
theorem Ctx.Walks.of_decl {Γ₀ Δ : Ctx}
    (h : ∀ y T, Δ y = some T → ∃ R, Γ₀.ref (.root y.rt) = some R ∧ R.walk y.path = some T) :
    Γ₀.Walks Δ := by
  intro y
  induction y with
  | root r => intro T hy; exact h _ T hy
  | step v s ih =>
      intro T hy
      by_cases hs : s.isProj = true
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hy
        rw [if_pos hs] at hy
        cases hU : Δ.ref v with
        | none => rw [hU] at hy; cases hy
        | some U =>
            rw [hU] at hy
            obtain ⟨R, hR, hw⟩ := ih U hU
            refine ⟨R, hR, ?_⟩
            change R.walk (v.path ++ [s]) = some T
            rw [VarType.walk_append, hw]
            simpa [VarType.walk] using hy
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hy
        rw [if_neg hs] at hy
        exact h _ T hy

theorem Ctx.Walks.mono {Γ₀ Γ₁ Δ : Ctx} (h : Γ₀.Walks Δ) (hle : Γ₀.Le Γ₁) : Γ₁.Walks Δ :=
  fun y T hy => (h y T hy).elim fun R ⟨hR, hw⟩ => ⟨R, hle.ref hR, hw⟩

/-- A world language's addresses walk from its roots. -/
theorem walks_ctxOf (l : List VarType) : (BArrow.ctxOf l).Walks (BArrow.ctxOf l) := by
  refine Ctx.Walks.of_decl fun y T hy => ?_
  obtain ⟨n, rfl⟩ := BArrow.ctxOf_decl hy
  exact ⟨T, hy, rfl⟩

theorem Ctx.Walks.boxIn [ModalSys.NoFour] {Γ₀ Δ : Ctx} (h : Γ₀.Walks Δ) : Γ₀.Walks Δ.boxIn := by
  refine Ctx.Walks.of_decl fun y T hy => ?_
  match y, hy with
  | .step u .box, hy =>
      obtain ⟨R, hR, hw⟩ := h u _ (Ctx.boxIn_box hy).2
      refine ⟨R, hR, ?_⟩
      change R.walk (u.path ++ [.box]) = some T
      rw [VarType.walk_append, hw]
      rfl
  | .step u .keep, hy => exact absurd (Ctx.boxIn_keep hy).1 (by simp [ModalSys.NoFour.noFour])
  | .root _, hy => cases hy
  | .step _ .fst, hy => cases hy
  | .step _ .snd, hy => cases hy
  | .step _ .dia, hy => cases hy
  | .step _ .here, hy => cases hy

theorem Ctx.Walks.diaIn [ModalSys.NoFour] {Γ₀ Δ : Ctx} (h : Γ₀.Walks Δ) (x : VarSymb) :
    Γ₀.Walks (Δ.diaIn x) := by
  refine Ctx.Walks.of_decl fun y T hy => ?_
  match y, hy with
  | .step u .dia, hy =>
      change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hy
      split_ifs at hy with hux
      subst hux
      cases hx : Δ.ref u with
      | none => rw [hx] at hy; cases hy
      | some X =>
          rw [hx] at hy
          cases X with
          | VTypeDia X' =>
              obtain rfl : X' = T := Option.some.inj hy
              obtain ⟨R, hR, hw⟩ := h u _ hx
              refine ⟨R, hR, ?_⟩
              change R.walk (u.path ++ [.dia]) = some X'
              rw [VarType.walk_append, hw]
              rfl
          | _ => cases hy
  | .step u .box, hy => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hy)
  | .step u .keep, hy => exact h.boxIn _ _ ((Ctx.ref_nonproj _ rfl).trans hy)
  | .root _, hy => cases hy
  | .step _ .fst, hy => cases hy
  | .step _ .snd, hy => cases hy
  | .step _ .here, hy => cases hy

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

variable (B) in
/-- Every label of an annotation types at the world. -/
def AnnTy (s : B.W) : {A : VarType} → Ann A → Prop
  | _, .var => True
  | _, .one => True
  | _, .prod a b => AnnTy s a ∧ AnnTy s b
  | _, .box a => AnnTy s a
  | _, .dia x a => B.LabelTy s x ∧ AnnTy s a

/-- A term over a context whose addresses walk from a stage's roots has typed labels. -/
theorem Term.annTy {s : B.W} {i : ℕ} :
    ∀ {Δ : Ctx}, ((B.w s).ctx i).Walks Δ → ∀ {A : VarType} {a : Ann A}, Term σ Δ A a →
      B.AnnTy s a
  | _, _, _, _, .var _ _ => trivial
  | _, _, _, _, .func _ => trivial
  | _, _, _, _, .unit => trivial
  | _, hW, _, _, .pair u t => ⟨(Term.annTy hW u :), (Term.annTy hW t :)⟩
  | _, hW, _, _, .boxtm t => (Term.annTy hW.boxIn t :)
  | _, hW, _, _, .diatm x hx t => by
      obtain ⟨X, h⟩ := hx
      obtain ⟨R, hR, hw⟩ := hW x _ h
      exact ⟨⟨i, R, hR, by rw [hw]; exact Option.some_ne_none _⟩, (Term.annTy (hW.diaIn x) t :)⟩

/-- Reading typed annotations canonically is injective, without T, at a world with an arrow. -/
theorem annShp_injective_noT (hT : ModalSys.T = false) (hInj : B.ImgInj) (s : B.W)
    (harr : ∃ t, B.R s t) :
    ∀ {A : VarType} (j : ℕ) (a a' : Ann A), a.Exact j → a'.Exact j → B.AnnTy s a →
      B.AnnTy s a' → B.annShp s j a = B.annShp s j a' → a = a'
  | _, _, .var, .var, _, _, _, _, _ => rfl
  | _, _, .one, .one, _, _, _, _, _ => rfl
  | _, j, .prod a b, .prod a' b', hab, hab', hty, hty', h => by
      obtain ⟨ha, hb⟩ := hab
      obtain ⟨ha', hb'⟩ := hab'
      injection h with _ _ h₁ h₂
      rw [annShp_injective_noT hT hInj s harr j a a' ha ha' hty.1 hty'.1 h₁,
        annShp_injective_noT hT hInj s harr j b b' hb hb' hty.2 hty'.2 h₂]
  | _, j, .box a, .box a', ha, ha', hty, hty', h => by
      injection h with _ h₁
      rw [annShp_injective_noT hT hInj s harr (j + 1) a a' ha ha' hty hty' h₁]
  | _, j, .dia x a, .dia x' a', hxa, hxa', hty, hty', h => by
      obtain ⟨hx, hlx, ha⟩ := hxa
      obtain ⟨hx', hlx', ha'⟩ := hxa'
      injection h with _ h₁ h₂
      rw [leafOf_inj_noT hT hInj j s hx hx' hlx hlx' hty.1 hty'.1 harr h₁,
        annShp_injective_noT hT hInj s harr (j + 1) a a' ha ha' hty.2 hty'.2 h₂]

/-- ⭐⭐**Tags determine annotations, without T**, at a world with an arrow out: two terms with one
    denotation have one annotation.  With T, `ann_eq_of_rden`. -/
theorem ann_eq_of_rden_noT (hT : ModalSys.T = false) (hSh : ModalSys.shaped = true)
    (hInj : B.ImgInj) {Γ : Ctx} (hok : Γ.DeclOK) (hex : Γ.Exact 0) {s : B.W} {i : ℕ}
    (e : Γ.Le ((B.w s).ctx i)) (hW : ((B.w s).ctx i).Walks Γ) (harr : ∃ t, B.R s t)
    {A : VarType} {a a' : Ann A} (t : Term σ Γ A a) (t' : Term σ Γ A a')
    (h : B.rden s i e t = B.rden s i e t') : a = a' := by
  refine annShp_injective_noT hT hInj s harr 0 a a' (Term.ann_exact hok hex t)
    (Term.ann_exact hok hex t') (Term.annTy hW t) (Term.annTy hW t') ?_
  rw [← termShp_canonical hok hex (cEnv_canonical hex s) t,
    ← termShp_canonical hok hex (cEnv_canonical hex s) t', ← B.rawShape_rden hSh s i e t,
    ← B.rawShape_rden hSh s i e t', h]

/-- Tags determine annotations without T, for terms of a world's language. -/
theorem ann_eq_of_rden_ctx_noT (hT : ModalSys.T = false) (hSh : ModalSys.shaped = true)
    (hInj : B.ImgInj) {s : B.W} {i : ℕ} (harr : ∃ t, B.R s t) {A : VarType} {a a' : Ann A}
    (t : Term σ ((B.w s).ctx i) A a) (t' : Term σ ((B.w s).ctx i) A a')
    (h : B.rden s i (Ctx.Le.refl _) t = B.rden s i (Ctx.Le.refl _) t') : a = a' :=
  ann_eq_of_rden_noT hT hSh hInj (Ctx.Presented.declOK_of (.inr noFour') _) (exact_ctxOf _)
    _ (walks_ctxOf _) harr t t' h

end BData

end BArrow

end V12M
