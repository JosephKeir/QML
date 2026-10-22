import QML.QML_v12m_BTruth
import QML.QML_v12m_BDecode

/-!
# QML v12m — B's canonical model: `Back`, truth ⇒ membership (strong B)

The truth lemma's `back` case in the direction the canonical `Ret` does not give for free
(docs §11.20, "Step 5 begun").

* ⭐`BData.mem_back_of_sat_diaFree`: at a `◇`-free content a true `Back` atom is in the theory.
  Suppose not.  `back_ret` turns the failure into a failing universal — some value `c` of the
  carrier's object along the leg (`◇[e ↦ c] □(e.box = bd)`) is not `t` — and Henkin witnessing
  names it.  The induction hypothesis makes the instance false in the model: some arrow of the
  leg brings the carrier's object home as `c`.  But a true `Back` makes the round trip
  (`Ret_fwd`), so the same arrow brings it home as something `Ind` to `t`; at a `◇`-free type
  `Ind` is equality (`ind_eq_of_diaFree`, by interchange at an `eqRec` slot), and `c = t`.
* `WFF.openFree_bindFree`: opening a bound body at its own eigenvariable gives it back, which is
  how a universal of the theory reaches `back_ret`'s subproof (`Proof.back_of_all`).
-/

namespace V12M

variable [ModalSys]

section Open

variable {σ : Signature} {Γ : Ctx} {T : VarType}

/-- ⭐Opening a bound body at its own eigenvariable gives the body back (`bindFree_openFree`'s
    converse): renaming the variable to the slot and the slot back to the variable composes to the
    identity renaming. -/
theorem WFF.openFree_bindFree (u : ℕ) (hu : Γ.RootFresh (.free u)) (hs : Γ.SlotsFrom 0)
    (φ : WFF σ (Γ.insert (.free u) T) 0) :
    WFF.openFree u hu hs (WFF.bindFree u hu hs T φ) = φ := by
  unfold WFF.openFree WFF.bindFree WFF.renameRoot
  rw [WFF.subst_comp _ _ (Subst.idRen _) _ _ _ _ Subst.ok_idRen Subst.coh_idRen _ _ _ ?_ φ]
  · exact (WFF.subst_ren (Ctx.Le.refl _) _ _ _ _ _ (fun v _ _ => Subst.at_idRen v) φ).trans
      (WFF.mono_refl _ φ)
  refine Subst.sim_of ?_
  intro v U hlp hv
  by_cases hvr : v = .root (.free u)
  · subst hvr
    change SubE.Sim U (.ren _) ((Subst.single (σ := σ) (.free u) (.ren (.root (.bnd 0)))
      (.root (.free u))).comp _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (.ren (.root (.bnd 0)))
      (.root (.free u)) = .ren (.root (.bnd 0)) from if_pos rfl]
    change SubE.Sim U _ (((Subst.idRen Γ).toFree 0 u T hu.root) (.root (.bnd 0)))
    rw [show ((Subst.idRen (σ := σ) Γ).toFree 0 u T hu.root) (.root (.bnd 0)) =
      .ren (.root (.free u)) from if_pos rfl]
    exact .refl _
  · have hv' : Γ v = some U := by simpa [Ctx.insert, hvr] using hv
    have hvb : v ≠ .root (.bnd 0) := fun h => by
      rw [h, hs.root] at hv'
      cases hv'
    change SubE.Sim U (.ren _) ((Subst.single (σ := σ) (.free u) (.ren (.root (.bnd 0))) v).comp
      _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (.ren (.root (.bnd 0)))
      v = .ren v from if_neg hvr]
    change SubE.Sim U _ (((Subst.idRen Γ).toFree 0 u T hu.root).at v)
    rw [Subst.at_nonproj _ hlp,
      show (Subst.idRen (σ := σ) Γ).toFree 0 u T hu.root v =
        ((Subst.idRen Γ) v).mono (Ctx.le_insert hu.root T) from if_neg hvb]
    exact .refl _

end Open

/-! ## `back_ret` from a universal -/

section BackRet

variable {σ : Signature} {Γ : Ctx} [Γ.NoSlots]

/-- `back_ret`'s premise and conclusion over its fresh value `c`, as one implication: if the
    carrier's object comes back along the leg as `c`, then `c` is `t`. -/
def WFF.backRetImp (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ (Γ.insert (.free c) A) 0 :=
  .imp ((O.mono (Ctx.le_insert hc.root A)).ret hS
      (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (WFF.mono ((O.le_view_mono (Ctx.le_insert hc.root A)).insert (.bnd 0) _)
        (WFF.backRetBody (OutLeg.slotsFrom Ctx.NoSlots.slots O) hA bd)))
    (eqRec A (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
      (Term.castAnn hA (Term.weaken hc.root A t)))

/-- `back_ret`'s premise as a universal: every value the carrier's object comes back as along
    the leg is `t`. -/
def WFF.backRetAll (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) : WFF σ Γ 0 :=
  .all A (WFF.bindFree c hc Ctx.NoSlots.slots A (WFF.backRetImp hS O hA bd t c hc))

/-- ⭐`∀c (◇[e ↦ c] □(e.box = bd) → c = t), ◇⊤ ⊢ Back bd t`: `back_ret`, its subproof
    instantiating the universal at the fresh value (`WFF.openFree_bindFree`). -/
def Proof.back_of_all (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) :
    Proof σ Γ [WFF.backRetAll hS O hA bd t c hc, O.dia .top] (O.back hS bd t) := by
  refine Proof.back_ret hS hB O hA bd t c hc
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  refine Proof.imp_elim (Proof.conv ?_ (Proof.all_elim A
    (Term.eta (.root (.free c)) A (Ctx.ref_insert_root Γ (.free c) A))
    (φ := WFF.mono ((Ctx.le_insert hc.root A).insert (.bnd 0) A)
      (WFF.bindFree c hc Ctx.NoSlots.slots A (WFF.backRetImp hS O hA bd t c hc)))
    (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))))
    (Proof.lookup List.mem_cons_self)
  rw [WFF.instantiate_eta_openFree c hc Ctx.NoSlots.slots, WFF.openFree_bindFree]
  rfl

end BackRet

/-! ## Unpacking a weakened returning possibility -/

section Agree

variable {σ : Signature} {M : Model σ} {Γ Γ' : Ctx}

/-- A returning possibility along a leg, weakened to a larger context, read back in the smaller
    one: an arrow of the old leg, the body there, and the way home (`sat_ret_agree`'s converse). -/
theorem OutLeg.ret_of_sat_agree {h : Γ.Le Γ'} {w : M.frame.W} {env : M.Env Γ w}
    {env' : M.Env Γ' w} (hag : Model.Env.Agree h env env') (hS : ModalSys.BStrong = true)
    (O : OutLeg Γ) {A : VarType} {a : Ann A} (t' : Term σ Γ' A a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    (hs : M.sat env' ((O.mono h).ret hS t' (WFF.mono ((O.le_view_mono h).insert (.bnd 0) _) Φ))) :
    ∃ (i : O.Arr env) (e : M.frame.Dom (.VTypeBox A) (O.acc env i).1),
      M.sat ((O.push env i).extend (.bnd 0) e) Φ ∧
        ∃ r : M.frame.R (O.acc env i).1 w,
          M.Ind (M.necEval (e : M.frame.Nec A (O.acc env i).1) ⟨w, ⟨r⟩⟩)
            (Model.interp env' t') := by
  cases O with
  | nec =>
      obtain ⟨i, e, hΦ, r, hr⟩ := hs
      exact ⟨i, e, (Model.sat_mono (Model.Env.extend_agree (Model.Env.boxPush_agree hag i)
        (.bnd 0) e) Φ).mp hΦ, r, hr⟩
  | pos y hy =>
      obtain ⟨Y, hY, a, e, hΦ, r, hr⟩ := hs
      have hYc : Y = hy.choose := by
        have e' := hY.symm.trans (h.ref hy.choose_spec)
        simp only [Option.some.injEq, VarType.VTypeDia.injEq] at e'
        exact e'
      subst hYc
      have href := Model.Env.ref_agree hag y hy.choose_spec
      let w₁ : (M.posEval (env.ref y hy.choose_spec)).1 := ⟨a.1, by rw [href]; exact a.2⟩
      exact ⟨w₁, e, (Model.sat_mono (Model.Env.extend_agree
        (Model.Env.diaPush_agree hag hy.choose_spec w₁ a.2) (.bnd 0) e) Φ).mp hΦ, r, hr⟩

end Agree

/-! ## Reading annotations back along a witness arrow -/

section AnnInj

/-- Every label of an annotation satisfies `P`. -/
def Ann.All (P : VarSymb → Prop) : {A : VarType} → Ann A → Prop
  | _, .var => True
  | _, .one => True
  | _, .prod a b => Ann.All P a ∧ Ann.All P b
  | _, .box a => Ann.All P a
  | _, .dia x a => P x ∧ Ann.All P a

omit [ModalSys] in
theorem Ann.All.and {P Q : VarSymb → Prop} :
    ∀ {A : VarType} {a : Ann A}, a.All P → a.All Q → a.All fun x => P x ∧ Q x
  | _, .var, _, _ => trivial
  | _, .one, _, _ => trivial
  | _, .prod _ _, h, h' =>
      And.intro (Ann.All.and (And.left h) (And.left h')) (Ann.All.and (And.right h) (And.right h'))
  | _, .box a, h, h' => Ann.All.and (a := a) h h'
  | _, .dia _ _, h, h' =>
      And.intro (And.intro (And.left h) (And.left h')) (Ann.All.and (And.right h) (And.right h'))

omit [ModalSys] in
/-- ⭐Renaming labels is injective on annotations whose labels it renames injectively. -/
theorem Ann.mapIdx_inj {P : VarSymb → Prop} {f : VarSymb → VarSymb}
    (hf : ∀ x x', P x → P x' → f x = f x' → x = x') :
    ∀ {A : VarType} (a a' : Ann A), a.All P → a'.All P → a.mapIdx f = a'.mapIdx f → a = a'
  | _, .var, .var, _, _, _ => rfl
  | _, .one, .one, _, _, _ => rfl
  | _, .prod a b, .prod a' b', hab, hab', h => by
      simp only [Ann.mapIdx, Ann.prod.injEq] at h
      rw [Ann.mapIdx_inj hf a a' (And.left hab) (And.left hab') h.1,
        Ann.mapIdx_inj hf b b' (And.right hab) (And.right hab') h.2]
  | _, .box a, .box a', ha, ha', h => by
      simp only [Ann.mapIdx, Ann.box.injEq] at h
      rw [Ann.mapIdx_inj hf a a' ha ha' h]
  | _, .dia x a, .dia x' a', hxa, hxa', h => by
      simp only [Ann.mapIdx, Ann.dia.injEq] at h
      rw [hf x x' (And.left hxa) (And.left hxa') h.1,
        Ann.mapIdx_inj hf a a' (And.right hxa) (And.right hxa') h.2]

/-- A context whose addresses all satisfy `Q`. -/
def Ctx.Under (Q : VarSymb → Prop) (Δ : Ctx) : Prop := ∀ v T, Δ.ref v = some T → Q v

section Under

variable {Q : VarSymb → Prop} (hQ : ∀ v st, Q v → Q (.step v st))
include hQ

/-- It suffices that the declared addresses satisfy `Q`, when `Q` is closed under steps. -/
theorem Ctx.Under.of_decl {Δ : Ctx} (h : ∀ v T, Δ v = some T → Q v) : Δ.Under Q := by
  intro v
  induction v with
  | root r => intro T hv; exact h _ T hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isProj = true
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hv
        rw [if_pos hs] at hv
        cases hU : Δ.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => exact hQ v s (ih U hU)
      · change (if s.isProj then (Δ.ref v).bind (·.step s) else Δ (.step v s)) = some T at hv
        rw [if_neg hs] at hv
        exact h _ T hv

theorem Ctx.Under.boxIn [ModalSys.NoFour] {Δ : Ctx} (h : Δ.Under Q) : Δ.boxIn.Under Q := by
  refine Ctx.Under.of_decl hQ fun y T hy => ?_
  match y, hy with
  | .step u .box, hy => exact hQ u .box (h u _ (Ctx.boxIn_box hy).2)
  | .step u .keep, hy => exact absurd (Ctx.boxIn_keep hy).1 (by simp [ModalSys.NoFour.noFour])
  | .root _, hy => cases hy
  | .step _ .fst, hy => cases hy
  | .step _ .snd, hy => cases hy
  | .step _ .dia, hy => cases hy
  | .step _ .here, hy => cases hy

theorem Ctx.Under.diaIn [ModalSys.NoFour] {Δ : Ctx} (h : Δ.Under Q) (x : VarSymb) :
    (Δ.diaIn x).Under Q := by
  refine Ctx.Under.of_decl hQ fun y T hy => ?_
  match y, hy with
  | .step u .dia, hy =>
      change (if u = x then (match Δ.ref x with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hy
      split_ifs at hy with hux
      subst hux
      cases hx : Δ.ref u with
      | none => rw [hx] at hy; cases hy
      | some X => exact hQ u .dia (h u X hx)
  | .step u .box, hy => exact h.boxIn hQ _ _ ((Ctx.ref_nonproj _ rfl).trans hy)
  | .step u .keep, hy => exact h.boxIn hQ _ _ ((Ctx.ref_nonproj _ rfl).trans hy)
  | .root _, hy => cases hy
  | .step _ .fst, hy => cases hy
  | .step _ .snd, hy => cases hy
  | .step _ .here, hy => cases hy

/-- A term's labels are addresses of its contexts, so they satisfy `Q`. -/
theorem Term.annAll [ModalSys.NoFour] {σ : Signature} :
    ∀ {Δ : Ctx}, Δ.Under Q → ∀ {A : VarType} {a : Ann A}, Term σ Δ A a → a.All Q
  | _, _, _, _, .var _ _ => trivial
  | _, _, _, _, .func _ => trivial
  | _, _, _, _, .unit => trivial
  | _, hU, _, _, .pair u t => And.intro (Term.annAll hU u :) (Term.annAll hU t :)
  | _, hU, _, _, .boxtm t => (Term.annAll (hU.boxIn hQ) t :)
  | _, hU, _, _, .diatm x hx t => by
      obtain ⟨X, h⟩ := hx
      exact And.intro (hU x _ h) (Term.annAll (hU.diaIn hQ x) t :)

end Under

namespace BArrow

/-- An address of a world's language is a declared root and projections. -/
theorem ctxOf_addr {l : List VarType} :
    ∀ {u : VarSymb} {T : VarType}, (ctxOf l).ref u = some T →
      PPath u.path ∧ ∃ n R, u.rt = .free n ∧ n < l.length ∧
        (ctxOf l).ref (.root (.free n)) = some R
  | .root r, T, h => by
      obtain ⟨n, rfl, hn⟩ := BData.root_of_ctxOf h
      exact ⟨fun _ hs => by simp [VarSymb.path] at hs, n, T, rfl, hn, h⟩
  | .step v s, T, h => by
      by_cases hs : s.isProj = true
      · change (if s.isProj then ((ctxOf l).ref v).bind (·.step s) else
          ctxOf l (.step v s)) = some T at h
        rw [if_pos hs] at h
        cases hU : (ctxOf l).ref v with
        | none => rw [hU] at h; cases h
        | some U =>
            obtain ⟨hp, n, R, hrt, hn, hR⟩ := ctxOf_addr hU
            refine ⟨fun t ht => ?_, n, R, hrt, hn, hR⟩
            simp only [VarSymb.path, List.mem_append, List.mem_singleton] at ht
            rcases ht with ht | rfl
            · exact hp t ht
            · exact hs
      · change (if s.isProj then ((ctxOf l).ref v).bind (·.step s) else
          ctxOf l (.step v s)) = some T at h
        rw [if_neg hs] at h
        obtain ⟨r, hr⟩ := ctxOf_decl h
        cases hr

omit [ModalSys] in
/-- The first level step after a run of projections is where it is. -/
theorem ppath_split {p p' : List Step} {s s' : Step} {t t' : List Step} (hp : PPath p)
    (hp' : PPath p') (hs : s.isProj = false) (hs' : s'.isProj = false)
    (h : p ++ s :: t = p' ++ s' :: t') : p = p' ∧ s = s' ∧ t = t' := by
  induction p generalizing p' with
  | nil =>
      cases p' with
      | nil => simpa using h
      | cons a p' =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          have := hp' a List.mem_cons_self
          rw [← h.1] at this
          rw [this] at hs
          cases hs
  | cons a p ih =>
      cases p' with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          have := hp a List.mem_cons_self
          rw [h.1] at this
          rw [this] at hs'
          cases hs'
      | cons a' p' =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨rfl, rfl, rfl⟩ := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
            (fun x hx => hp' x (List.mem_cons_of_mem _ hx)) h
          exact ⟨rfl, rfl, rfl⟩

/-- The labels a term in `y`'s `◇` view can carry: through `y`'s content, or through a necessary
    variable's `□` view. -/
def ViewLabel (l : List VarType) (y : VarSymb) (ℓ : VarSymb) : Prop :=
  (∃ q, ℓ = (VarSymb.step y .dia).ext q) ∨
    ∃ (u : VarSymb) (q : List Step) (T : VarType),
      (ctxOf l).ref u = some (.VTypeBox T) ∧ ℓ = (VarSymb.step u .box).ext q

theorem ViewLabel.step {l : List VarType} {y : VarSymb} {ℓ : VarSymb} (st : Step)
    (h : ViewLabel l y ℓ) : ViewLabel l y (.step ℓ st) := by
  rcases h with ⟨q, rfl⟩ | ⟨u, q, T, hu, rfl⟩
  · exact Or.inl ⟨q ++ [st], by rw [VarSymb.ext_append]; rfl⟩
  · exact Or.inr ⟨u, q ++ [st], T, hu, by rw [VarSymb.ext_append]; rfl⟩

/-- `y`'s `◇` view has only such labels. -/
theorem under_diaIn [ModalSys.NoFour] (l : List VarType) (y : VarSymb) :
    ((ctxOf l).diaIn y).Under (ViewLabel l y) := by
  refine Ctx.Under.of_decl (fun _ st h => h.step st) fun v T hv => ?_
  rcases diaIn_item hv with ⟨u, rfl, hu⟩ | ⟨rfl, _⟩
  · exact Or.inr ⟨u, [], T, hu, rfl⟩
  · exact Or.inl ⟨[], rfl⟩

/-- ⭐**Along a witness arrow, labels of `y`'s `◇` view are read back injectively**, given
    injective images and a content variable outside them: a label through `y`'s content goes to
    the content variable, one through a `□` view to its root's image, cut at its `box`
    (`arrowIdx_boxExt`; `cut_unique` without T, `cut_unique_T` with it). -/
theorem arrowXIdx_inj {l : List VarType} {img : ℕ → ℕ} {cx : ℕ}
    {y : VarSymb} {Y : VarType} (hy : (ctxOf l).ref y = some (.VTypeDia Y))
    (hInj : ∀ r r', r < l.length → r' < l.length → img r = img r' → r = r')
    (hcx : ∀ r < l.length, img r ≠ cx) {ℓ ℓ' : VarSymb} (hℓ : ViewLabel l y ℓ)
    (hℓ' : ViewLabel l y ℓ')
    (hw : ∀ R, (ctxOf l).ref (.root ℓ.rt) = some R → R.walk ℓ.path ≠ none)
    (hw' : ∀ R, (ctxOf l).ref (.root ℓ'.rt) = some R → R.walk ℓ'.path ≠ none)
    (e : arrowXIdx img y cx ℓ = arrowXIdx img y cx ℓ') : ℓ = ℓ' := by
  obtain ⟨hpy, -⟩ := ctxOf_addr hy
  -- the two kinds of label, read along the arrow
  have hY : ∀ q, arrowXIdx img y cx ((VarSymb.step y .dia).ext q) =
      (VarSymb.root (.free cx)).ext q := by
    intro q
    unfold arrowXIdx
    rw [if_pos ⟨by rw [VarSymb.ext_rt]; rfl, by
      rw [VarSymb.ext_path]; exact List.prefix_append _ _⟩, VarSymb.ext_path]
    congr 1
    simp [VarSymb.path]
  have hBx : ∀ u q T, (ctxOf l).ref u = some (.VTypeBox T) →
      arrowXIdx img y cx ((VarSymb.step u .box).ext q) =
        (VarSymb.root (imgRoot img u.rt)).ext (encPath u.path ++ itemTail ++ q) := by
    intro u q T hu
    obtain ⟨hpu, -⟩ := ctxOf_addr hu
    unfold arrowXIdx
    rw [if_neg, arrowIdx_boxExt img hpu, itemImg, itemAt]
    · simp only [VarSymb.ext_append]
    rintro ⟨-, t, ht⟩
    rw [VarSymb.ext_path] at ht
    change y.path ++ [Step.dia] ++ t = u.path ++ [Step.box] ++ q at ht
    simp only [List.append_assoc, List.singleton_append] at ht
    exact absurd (ppath_split hpy hpu rfl rfl ht).2.1 (by decide)
  have hext : ∀ {a b : Root} {p p' : List Step},
      (VarSymb.root a).ext p = (VarSymb.root b).ext p' → a = b ∧ p = p' := by
    intro a b p p' h
    have h₁ := congrArg VarSymb.rt h
    have h₂ := congrArg VarSymb.path h
    rw [VarSymb.ext_rt, VarSymb.ext_rt] at h₁
    rw [VarSymb.ext_path, VarSymb.ext_path] at h₂
    exact ⟨h₁, by simpa [VarSymb.path] using h₂⟩
  rcases hℓ with ⟨q, rfl⟩ | ⟨u, q, T, hu, rfl⟩ <;>
    rcases hℓ' with ⟨q', rfl⟩ | ⟨u', q', T', hu', rfl⟩
  · rw [hY, hY] at e
    rw [(hext e).2]
  · rw [hY, hBx u' q' T' hu'] at e
    obtain ⟨hpu', n', R', hrt', hn', -⟩ := ctxOf_addr hu'
    rw [hrt'] at e
    exact absurd (Root.free.inj (hext e).1).symm (hcx n' hn')
  · rw [hBx u q T hu, hY] at e
    obtain ⟨hpu, n, R, hrt, hn, -⟩ := ctxOf_addr hu
    rw [hrt] at e
    exact absurd (Root.free.inj (hext e).1) (hcx n hn)
  · rw [hBx u q T hu, hBx u' q' T' hu'] at e
    obtain ⟨hpu, n, R, hrt, hn, hR⟩ := ctxOf_addr hu
    obtain ⟨hpu', n', R', hrt', hn', hR'⟩ := ctxOf_addr hu'
    rw [hrt, hrt'] at e
    obtain ⟨e₁, e₂⟩ := hext e
    obtain rfl := hInj n n' hn hn' (Root.free.inj e₁)
    obtain rfl : R = R' := Option.some.inj (hR.symm.trans hR')
    have hr₁ : (ctxOf l).ref (.root ((VarSymb.step u .box).ext q).rt) = some R := by
      rw [VarSymb.ext_rt]
      change (ctxOf l).ref (.root u.rt) = _
      rw [hrt]
      exact hR
    have hr₂ : (ctxOf l).ref (.root ((VarSymb.step u' .box).ext q').rt) = some R := by
      rw [VarSymb.ext_rt]
      change (ctxOf l).ref (.root u'.rt) = _
      rw [hrt']
      exact hR'
    have hw₁ := hw R hr₁
    have hw₂ := hw' R hr₂
    rw [VarSymb.ext_path] at hw₁ hw₂
    change R.walk (u.path ++ [Step.box] ++ q) ≠ none at hw₁
    change R.walk (u'.path ++ [Step.box] ++ q') ≠ none at hw₂
    simp only [List.append_assoc, List.singleton_append] at hw₁ hw₂
    have hcut : u.path = u'.path ∧ q = q' := by
      cases hT : ModalSys.T
      · rw [encPath_noT hT, encPath_noT hT, itemTail_noT hT, List.append_nil,
          List.append_nil] at e₂
        exact cut_unique hT hpu hpu' hw₁ hw₂ e₂
      · rw [show itemTail = [Step.fst] by simp [itemTail, hT], List.append_assoc,
          List.append_assoc, List.singleton_append, List.singleton_append] at e₂
        exact cut_unique_T hT hpu hpu' hw₁ hw₂ e₂
    obtain ⟨hp, rfl⟩ := hcut
    rw [VarSymb.eq_of_rt_path (hrt.trans hrt'.symm) hp]

end BArrow

end AnnInj

namespace BArrow

variable {σ : Signature}

namespace BData

variable [ModalSys.NoFour] {B : BData σ}

/-- ⭐**At a `◇`-free type canonical `Ind` is equality**: related representatives are
    interchangeable at the slot formula `z = u'`, whose `u'`-instance is provable; so the
    `u`-instance is in the theory, and true by the induction hypothesis at `eqRec`. -/
theorem ind_eq_of_diaFree {s : B.W} {A : VarType} (hA : A.diaFree = true)
    {o o' : B.model.frame.Dom A s}
    (IH : ∀ (K : ℕ) (u u' : Term σ ((B.w s).ctx K) A (Ann.eta (.root (.bnd 0)) A)),
      (eqRec A u u' : WFF σ _ 0) ∈ (B.w s).M K →
        B.model.sat (B.canonEnv s K) (eqRec A u u' : WFF σ _ 0))
    (h : B.Ind o o') : o = o' := by
  obtain ⟨⟨i, a, u⟩, ⟨i', a', u'⟩, hu, hu', hrel⟩ := h
  obtain rfl := Ann.eq_of_diaFree hA a (Ann.eta (.root (.bnd 0)) A)
  obtain rfl := Ann.eq_of_diaFree hA a' (Ann.eta (.root (.bnd 0)) A)
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have key := hrel _ hK hK' (eqRec A
    (Term.eta (.root (.bnd 0)) A (Ctx.ref_insert_root _ (.bnd 0) A))
    (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (B.w s).ctx (max i i'))).root A)
      (Term.mono ((B.w s).le hK') u')))
  rw [WFF.instantiate_eqRec_slot hA, WFF.instantiate_eqRec_slot hA] at key
  have h0 : (eqRec A (Term.mono ((B.w s).le hK') u') (Term.mono ((B.w s).le hK') u') :
      WFF σ _ 0) ∈ (B.w s).M (max i i') :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.eqRec_refl A _⟩
  have hsat := IH _ _ _ (BWorld.mem_T.mp (key.mpr (BWorld.mem_T.mpr h0)))
  rw [Model.sat_eqRec, interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon _ (Model.Env.Agree.refl' _)] at hsat
  have he := toDom_inj hsat
  change B.rden s _ _ (Term.mono ((B.w s).le hK) u) =
    B.rden s _ _ (Term.mono ((B.w s).le hK') u') at he
  rw [rden_lift hK u, rden_lift hK' u', hu, hu'] at he
  rw [← B.toDom_fromDom A s o, ← B.toDom_fromDom A s o']
  exact toDom_congr he _ _

omit [ModalSys.NoFour] in
/-- `Back`'s size dominates everything its `◇`-free case looks at. -/
theorem size_back_ge {Γ : Ctx} (hS : ModalSys.BStrong = true) (O : OutLeg Γ) {A : VarType}
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ Γ A a) :
    3 * A.eqRecSize + 5 ≤ (O.back hS bd t : WFF σ Γ 0).size := by
  cases O <;> simp only [OutLeg.back, WFF.size, BLeg.carrier, VarType.eqRecSize] <;> omega

omit [ModalSys.NoFour] in
theorem size_backRetImp {Γ : Ctx} [Γ.NoSlots] (hS : ModalSys.BStrong = true) (O : OutLeg Γ)
    {A : VarType} (hA : A.diaFree = true) {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀)
    {a : Ann A} (t : Term σ Γ A a) (c : ℕ) (hc : Γ.RootFresh (.free c)) :
    (WFF.backRetImp hS O hA bd t c hc).size = 3 * A.eqRecSize + 3 := by
  cases O <;>
  simp only [WFF.backRetImp, OutLeg.ret, OutLeg.retS, OutLeg.mono, WFF.size, WFF.size_mono,
    WFF.backRetBody, WFF.size_eqRec, RShape.flat, NShape.flat, VarType.compsFlat,
    VarType.eqRecSize] <;> omega

omit [ModalSys.NoFour] in
theorem size_dia_top {Γ : Ctx} (O : OutLeg Γ) : (O.dia (.top : WFF σ O.view 0)).size ≤ 3 := by
  cases O <;> simp [OutLeg.dia, WFF.neg, WFF.size]

/-- ⭐⭐**`Back`, truth ⇒ membership, at a `◇`-free content** (strong B; docs §11.20).  Were the
    atom not in the theory, `back_ret` (`Proof.back_of_all`) would make its universal fail, and
    Henkin witnessing gives a value `g` with `◇[e ↦ g] □(e.box = bd)` and `g ≠ t` at a later stage.
    By the induction hypothesis that is true: an arrow of the leg brings the carrier's object home
    as `g`.  The atom is true, so it makes the round trip (`sat_back_rt`): the same arrow brings it
    home as something `Ind` to `t`.  At a `◇`-free type `Ind` is equality
    (`ind_eq_of_diaFree`), so `g = t`.  The induction hypothesis is used below `Back`'s size only
    (`size_back_ge`). -/
theorem mem_back_of_sat_diaFree (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    {s : B.W} {i : ℕ} (O : OutLeg ((B.w s).ctx i)) {A : VarType} (hA : A.diaFree = true)
    {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ ((B.w s).ctx K) 0),
      φ.size < (O.back hS bd t : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s K) φ ↔ φ ∈ (B.w s).M K))
    (h : B.model.sat (B.canonEnv s i) (O.back hS bd t : WFF σ _ 0)) :
    (O.back hS bd t : WFF σ _ 0) ∈ (B.w s).M i := by
  have hsz := size_back_ge hS O bd t
  have hrt := OutLeg.sat_back_rt hS (B.canonEnv s i) O bd t h
  obtain ⟨⟨i₀⟩, hrt⟩ := hrt
  have hdia : O.dia (.top : WFF σ O.view 0) ∈ (B.w s).M i :=
    (IH i _ (by have := size_dia_top (σ := σ) O; omega)).mp
      ((OutLeg.sat_dia (B.canonEnv s i) O _).mpr ⟨i₀, trivial⟩)
  have hind : ∀ {x y : B.model.frame.Dom A s}, B.Ind x y → x = y := fun hxy =>
    ind_eq_of_diaFree hA (fun K u u' hm => (IH K _ (by rw [WFF.size_eqRec]; omega)).mpr hm) hxy
  by_contra hnot
  have hc : ((B.w s).ctx i).RootFresh (.free ((B.w s).l i).length) := ctxOf_fresh le_rfl
  have hall : WFF.backRetAll hS O hA bd t _ hc ∉ (B.w s).M i := fun hm =>
    hnot (BWorld.mem_of_provable (Δ := [_, _]) (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact hm
      · rw [List.mem_singleton.mp hψ]; exact hdia)
      ⟨Proof.back_of_all hS hB O hA bd t _ hc⟩)
  obtain ⟨j, hij, ag, g, hneg⟩ := (B.w s).allW (((B.w s).mcs i).neg_mem_iff.mpr hall)
  have hns := fun hs => ((B.w s).mcs j).neg_mem_iff.mp hneg ((IH j _ (by
    rw [WFF.size_instantiate, WFF.size_mono, WFF.bindFree, WFF.renameRoot, WFF.size_subst,
      size_backRetImp]
    omega)).mp hs)
  rw [Model.sat_instantiate _ (noProjLast s j) _ g,
    Model.sat_mono (Model.Env.extend_agree (canonEnv_le s hij) (.bnd 0) _),
    Model.sat_bindFree _ (noProjLast s i) _ hc] at hns
  refine hns fun hR => ?_
  set og := Model.interp (B.canonEnv s j) g
  obtain ⟨i₁, e, hΦ, r, hr⟩ := OutLeg.ret_of_sat_agree
    (Model.Env.agree_extend (B.canonEnv s i) hc.root og) hS O _ _ hR
  have hslot : ((B.canonEnv s i).extend (.free _) og).ref (.root (.free _))
      (Ctx.ref_insert_root _ (.free ((B.w s).l i).length) A) = og :=
    Model.Env.extend_root _ (.free _) og (Ctx.ref_insert_root _ _ A)
  -- the body: the object out there is the carrier's
  unfold WFF.backRetBody at hΦ
  have hslot0 : ((O.push (B.canonEnv s i) i₁).extend (.bnd 0) e).ref (.root (.bnd 0))
      (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A)) = e :=
    Model.Env.extend_root _ (.bnd 0) e (Ctx.ref_insert_root O.view (.bnd 0) (.VTypeBox A))
  rw [Model.sat_eqRec, Model.interp_castAnn,
    Model.interp_mono (Model.Env.agree_extend _ (OutLeg.slotsFrom Ctx.NoSlots.slots O).root _),
    Model.interp_eta, hslot0] at hΦ
  rw [hΦ, Model.box_beta] at hr
  obtain ⟨r', hr'⟩ := hrt i₁
  change B.Ind _ _ at hr hr'
  rw [Model.interp_eta, hslot] at hr
  have h₁ := hind hr
  have h₂ := hind hr'
  rw [Model.sat_eqRec, Model.interp_castAnn, Term.weaken,
    Model.interp_mono (Model.Env.agree_extend _ hc.root _), Model.interp_eta, hslot]
  exact h₁.symm.trans h₂

/-- ⭐**A plain leg is no witness's extent**: wherever there is an arrow there is an unlabelled
    one (`unl`), and a witness's extent holds only arrows labelled with it and (under T) the
    world's own. -/
theorem univ_ne_extent {s : B.W} (harr : ∃ k, B.R s k)
    (y : VarSymb) : (Set.univ : Set (B.frame.Acc s)) ≠ B.extent s y := by
  intro h
  obtain ⟨k, hk⟩ := harr
  obtain ⟨t₀, hR, hkd⟩ := B.unl y hk
  have hm : (⟨t₀, ⟨Or.inl hR⟩⟩ : B.Acc s) ∈ B.extent s y := h ▸ Set.mem_univ _
  rcases hm with ⟨X, hX⟩ | ⟨hnR, -⟩
  · rw [hkd] at hX
    cases hX
  · exact hnR hR

/-- A true atom's out leg has an arrow, so its world has a network one (under T by `T`). -/
theorem exists_R_of_arr {s : B.W} {i : ℕ} {O : OutLeg ((B.w s).ctx i)}
    (a : O.Arr (B.canonEnv s i)) : ∃ k, B.R s k := by
  rcases (O.acc (B.canonEnv s i) a).2.down with hR | ⟨hT, -⟩
  · exact ⟨_, hR⟩
  · exact exists_R_of_T hT s

/-- Two terms of a world's language with one denotation, lifted to a common stage, have one
    annotation there (the decoder: `ann_eq_of_rden_ctx` under T, `ann_eq_of_rden_ctx_noT` off). -/
theorem ann_eq_of_toDom (hS : ModalSys.BStrong = true) (hInj : B.ImgInj) {s : B.W}
    (harr : ∃ k, B.R s k) {A : VarType} {i i' : ℕ} {a a' : Ann A}
    (t : Term σ ((B.w s).ctx i) A a) (t' : Term σ ((B.w s).ctx i') A a')
    (h : B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) =
      B.toDom A s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _)) : a = a' := by
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have e : B.rden s (max i i') (Ctx.Le.refl _) (Term.mono ((B.w s).le hK) t) =
      B.rden s (max i i') (Ctx.Le.refl _) (Term.mono ((B.w s).le hK') t') := by
    rw [rden_lift hK t, rden_lift hK' t']
    exact toDom_inj h
  by_cases hT : ModalSys.T = true
  · exact ann_eq_of_rden_ctx hT _ _ e
  · exact ann_eq_of_rden_ctx_noT (Bool.eq_false_iff.mpr hT) (by simp [ModalSys.shaped, hS])
      hInj harr _ _ e

/-- Denotations equal at a common stage make the equation true there. -/
theorem sat_eqRec_lift {s : B.W} {A : VarType} {i i' K : ℕ} (hK : i ≤ K) (hK' : i' ≤ K)
    {a : Ann A} (t : Term σ ((B.w s).ctx i) A a) (t' : Term σ ((B.w s).ctx i') A a)
    (h : B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) =
      B.toDom A s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _)) :
    B.model.sat (B.canonEnv s K)
      (eqRec A (Term.mono ((B.w s).le hK) t) (Term.mono ((B.w s).le hK') t') : WFF σ _ 0) := by
  rw [Model.sat_eqRec, interp_canon _ (Model.Env.Agree.refl' _),
    interp_canon _ (Model.Env.Agree.refl' _)]
  exact toDom_congr ((rden_lift hK t).trans ((toDom_inj h).trans (rden_lift hK' t').symm)) _ _

/-- ⭐⭐**`Back`, truth ⇒ membership, row 1** (a plain leg, carrier `□□A`), at every content
    type (strong B, any T; docs §11.20).  At a `◇`-free content, `mem_back_of_sat_diaFree`.
    Otherwise the canonical `Ret` is an atom `Back ct' t'` of the theory with the same round-trip
    data and `den t' = den t`.  The data's leg is every arrow, which no witness's extent is
    (`univ_ne_extent`), so the atom is row 1 too, and its carrier's values one arrow on and home
    again are ours: `nec_inj` twice makes the carriers' denotations equal.  The decoder makes the
    annotations equal (`ann_eq_of_toDom`, at a world with an arrow), the induction hypothesis puts
    `eqRec` of the carriers and of the values in the theory, and `back_eqC`, `back_eq` move the
    atom to ours. -/
theorem mem_back_of_sat_nec (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hInj : B.ImgInj) {s : B.W} {i : ℕ} {A : VarType} {a₀ : Ann A}
    (bd : Term σ ((B.w s).ctx i).boxIn.boxIn A a₀) {a : Ann A} (t : Term σ ((B.w s).ctx i) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ ((B.w s).ctx K) 0),
      φ.size < ((OutLeg.nec : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s K) φ ↔ φ ∈ (B.w s).M K))
    (h : B.model.sat (B.canonEnv s i)
      ((OutLeg.nec : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0)) :
    ((OutLeg.nec : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0) ∈ (B.w s).M i := by
  by_cases hA : A.diaFree = true
  · exact mem_back_of_sat_diaFree hS hB .nec hA bd t IH h
  have hsz := size_back_ge hS .nec bd t
  obtain ⟨⟨i₀⟩, -⟩ := OutLeg.sat_back_rt hS (B.canonEnv s i) .nec bd t h
  have harr := exists_R_of_arr (O := .nec) i₀
  change B.Ret _ _ _ at h
  rcases h with ⟨hA', -⟩ | ⟨hS', i', L, c, ct, a', t', hmem, hdata, hval⟩
  · exact absurd hA' hA
  revert c ct hmem hdata
  cases L with
  | pos =>
      intro c ct
      cases ct with
      | diatm y hy u =>
          intro _ hdata
          have hfst := congrArg Sigma.fst hdata
          change B.extent s y = Set.univ at hfst
          exact (univ_ne_extent harr y hfst.symm).elim
  | nec =>
      intro c ct
      cases ct with
      | boxtm u =>
          cases u with
          | boxtm bd' =>
              intro hmem hdata
              obtain ⟨-, hval'⟩ := Sigma.mk.inj_iff.mp hdata
              have hfun := eq_of_heq hval'
              -- the carriers denote alike
              have hc : B.toDom _ s (B.rden s i' (Ctx.Le.refl _) (Term.boxtm (Term.boxtm bd')))
                    (definable_rden _ _) =
                  B.toDom _ s (B.rden s i (Ctx.Le.refl _) (Term.boxtm (Term.boxtm bd)))
                    (definable_rden _ _) := by
                rw [← interp_canon (Term.boxtm (Term.boxtm bd)) (Model.Env.Agree.refl' _)]
                exact B.model.nec_inj (funext fun a₁ => B.model.nec_inj (funext fun b =>
                  congrFun (congrFun hfun ⟨a₁, Set.mem_univ _⟩) b))
              have hv : B.toDom A s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _) =
                  B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) := by
                rw [hval, interp_canon t (Model.Env.Agree.refl' _)]
              obtain ⟨⟨⟩⟩ := ann_eq_of_toDom hS hInj harr _ _ hc
              obtain rfl := ann_eq_of_toDom hS hInj harr _ _ hv
              have hK : i ≤ max i i' := le_max_left _ _
              have hK' : i' ≤ max i i' := le_max_right _ _
              have hmc := (IH _ _ (by
                rw [WFF.size_eqRec]; simp only [VarType.eqRecSize] at hsz ⊢; omega)).mp
                (sat_eqRec_lift hK' hK _ _ hc)
              have hmv := (IH _ _ (by rw [WFF.size_eqRec]; omega)).mp
                (sat_eqRec_lift hK' hK _ _ hv)
              refine (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable (Δ := [_, _, _])
                (fun ψ hψ => by
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact (BWorld.mem_lift hK').mp hmem
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact hmc
                  · rw [List.mem_singleton.mp hψ]; exact hmv)
                ⟨Proof.back_eq hS .nec _ _ _ (Proof.back_eqC hS .nec _ _ _
                  (Proof.lookup List.mem_cons_self)
                  (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
                  (Proof.lookup (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self)))⟩)

variable (B) in
/-- ⭐**Fresh witness arrows**: a true `◇_y ⊤` at a stage has an arrow of `y`'s extent whose
    content variable is no image of that stage's variables.  The limit's witness children have it
    (`bdata_cxFresh`): a child made for the formula sees the stage's variables under the identity,
    its content variable past them. -/
def CxFresh : Prop :=
  ∀ {s : B.W} {i : ℕ} {y : VarSymb} {Y : VarType} (hy : ((B.w s).ctx i).ref y = some (.VTypeDia Y)),
    WFF.dia y ⟨Y, hy⟩ (.top : WFF σ _ 0) ∈ (B.w s).M i →
      ∃ k, B.kd s k = some (y, Y) ∧ ∀ r < ((B.w s).l i).length, B.img s k r ≠ B.cx s k y

omit [ModalSys] in
/-- Two equal dependent pairs over sets agree at a common member. -/
theorem sigma_snd_apply {α : Type*} {β : α → Type*} {D₁ D₂ : Σ S : Set α, (a : S) → β a.1}
    (h : D₁ = D₂) (a : α) (h₁ : a ∈ D₁.1) (h₂ : a ∈ D₂.1) : D₁.2 ⟨a, h₁⟩ = D₂.2 ⟨a, h₂⟩ := by
  subst h
  rfl

/-- Typed annotations have typed labels. -/
theorem annTy_all {s : B.W} : ∀ {A : VarType} {a : Ann A}, B.AnnTy s a → a.All (B.LabelTy s)
  | _, .var, _ => trivial
  | _, .one, _ => trivial
  | _, .prod _ _, h => And.intro (annTy_all h.1) (annTy_all h.2)
  | _, .box a, h => annTy_all (a := a) h
  | _, .dia _ _, h => And.intro h.1 (annTy_all h.2)

/-- A typed label walks from its root's type at any stage declaring the root. -/
theorem labelTy_walk {s : B.W} {ℓ : VarSymb} (h : B.LabelTy s ℓ) {K : ℕ} {R : VarType}
    (hR : ((B.w s).ctx K).ref (.root ℓ.rt) = some R) : R.walk ℓ.path ≠ none := by
  obtain ⟨j, R', hR', hw⟩ := h
  have e₁ := ((B.w s).le (le_max_left j K)).ref hR'
  have e₂ := ((B.w s).le (le_max_right j K)).ref hR
  obtain rfl : R' = R := Option.some.inj (e₁.symm.trans e₂)
  exact hw

/-- ⭐⭐**`Back`, truth ⇒ membership, row 2** (a witness's leg, carrier `◇_y□A`), at every content
    type (strong B, any T; docs §11.20).  At a `◇`-free content, `mem_back_of_sat_diaFree`.
    Otherwise the canonical `Ret` is an atom `Back ct' t'` of the theory with the same round-trip
    data and `den t' = den t`.  Its leg is no plain leg (`univ_ne_extent`) and shares an arrow
    with `y`'s extent, so it is `y`'s.  Its contents along every arrow of the extent are ours.  At
    a fresh witness arrow (`CxFresh`) the decoder there gives the two contents' images one
    annotation, and the arrow reads the annotations of `y`'s view back injectively
    (`arrowXIdx_inj`), so the carriers have one annotation; their shapes follow
    (`termShp_ann`), so one denotation.  The induction hypothesis at the two `eqRec`s,
    `back_eqC` and `back_eq` finish, as in row 1. -/
theorem mem_back_of_sat_pos (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hInj : B.ImgInj) (hCx : B.CxFresh) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {A : VarType} {a₀ : Ann A}
    (bd : Term σ (((B.w s).ctx i).diaIn y).boxIn A a₀) {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ ((B.w s).ctx K) 0),
      φ.size < ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s K) φ ↔ φ ∈ (B.w s).M K))
    (h : B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0)) :
    ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).back hS bd t : WFF σ _ 0) ∈ (B.w s).M i := by
  by_cases hA : A.diaFree = true
  · exact mem_back_of_sat_diaFree hS hB (.pos y hy) hA bd t IH h
  have hsz := size_back_ge hS (.pos y hy) bd t
  obtain ⟨⟨i₀⟩, -⟩ := OutLeg.sat_back_rt hS (B.canonEnv s i) (.pos y hy) bd t h
  have harr := exists_R_of_arr (O := .pos y hy) i₀
  have hdia : (OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).dia (.top : WFF σ _ 0) ∈ (B.w s).M i :=
    (IH i _ (by have := size_dia_top (σ := σ) (OutLeg.pos y hy); omega)).mp
      ((OutLeg.sat_dia (B.canonEnv s i) (.pos y hy) _).mpr ⟨i₀, trivial⟩)
  obtain ⟨Y, hY⟩ := hy
  change B.Ret _ _ _ at h
  rcases h with ⟨hA', -⟩ | ⟨hS', i', L, c, ct, a', t', hmem, hdata, hval⟩
  · exact absurd hA' hA
  have hK : i ≤ max i i' := le_max_left _ _
  have hK' : i' ≤ max i i' := le_max_right _ _
  have hyK : ((B.w s).ctx (max i i')).ref y = some (.VTypeDia Y) := ((B.w s).le hK).ref hY
  obtain ⟨k, hkk, hfresh⟩ := hCx hyK ((BWorld.mem_lift hK).mp hdia)
  have hkR := B.kdR hkk
  have hD : B.model.carrierData .pos
      (Model.interp (B.canonEnv s i) (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd))) =
      B.cData .pos (B.toDom _ s (B.rden s i (Ctx.Le.refl _) (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd)))
        (definable_rden _ _)) := by
    rw [interp_canon _ (Model.Env.Agree.refl' _)]
    rfl
  revert c ct hmem hdata
  cases L with
  | nec =>
      intro c ct
      cases ct with
      | boxtm u =>
          intro _ hdata
          have hfst := congrArg Sigma.fst (hdata.trans hD)
          change Set.univ = B.extent s y at hfst
          exact (univ_ne_extent harr y hfst).elim
  | pos =>
      intro c ct
      cases ct with
      | diatm y' hy' u =>
          cases u with
          | boxtm bd' =>
              intro hmem hdata
              have hdata' := hdata.trans hD
              have hfst := congrArg Sigma.fst hdata'
              change B.extent s y' = B.extent s y at hfst
              obtain rfl : y = y' := eq_of_extent_eq (B.kd_lb hkk) hfst.symm
              -- the contents agree along every arrow of the extent
              have hcont : ∀ (a₁ : B.Acc s) (m : a₁ ∈ B.extent s y),
                  (B.rden s i' (Ctx.Le.refl _) (Term.diatm y hy' (Term.boxtm bd'))).2 ⟨a₁, m⟩ =
                    (B.rden s i (Ctx.Le.refl _) (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd))).2
                      ⟨a₁, m⟩ := by
                intro a₁ m
                have e := sigma_snd_apply
                  (β := fun a₂ : B.frame.Acc s => (b : B.frame.Acc a₂.1) → B.frame.Dom A b.1)
                  hdata' a₁ m m
                exact toDom_inj (B.model.nec_inj e)
              -- one annotation, read back along the fresh witness arrow `s → k`
              have hm₀ : (⟨k, ⟨Or.inl hkR⟩⟩ : B.Acc s) ∈ B.extent s y :=
                Or.inl ⟨Y, B.kd_lb hkk⟩
              have hck := hcont _ hm₀
              rw [rden_diatm_net _ _ _ ⟨_, hm₀⟩ ⟨Y, B.kd_lb hkk⟩,
                rden_diatm_net _ _ _ ⟨_, hm₀⟩ ⟨Y, B.kd_lb hkk⟩] at hck
              have hann := ann_eq_of_toDom hS hInj ⟨s, B.symm hkR⟩ _ _ (toDom_congr hck _ _)
              have hQ : ∀ (j : ℕ) (hj : j ≤ max i i') {b : Ann (.VTypeBox A)}
                  (u : Term σ (((B.w s).ctx j).diaIn y) (.VTypeBox A) b),
                  b.All fun ℓ => ViewLabel ((B.w s).l (max i i')) y ℓ ∧ B.LabelTy s ℓ := by
                intro j hj b u
                exact (Term.annAll (fun _ st h => h.step st) (under_diaIn _ y)
                  (Term.mono (((B.w s).le hj).diaIn y) u)).and
                  (annTy_all (Term.annTy ((walks_ctxOf _).diaIn y)
                    (Term.mono (((B.w s).le hj).diaIn y) u)))
              have hb := Ann.mapIdx_inj (fun ℓ ℓ' hℓ hℓ' e => arrowXIdx_inj hyK
                (fun r r' hr hr' e => hInj hkR _ r r' hr hr' e) hfresh hℓ.1 hℓ'.1
                (fun _ hR => labelTy_walk hℓ.2 hR) (fun _ hR => labelTy_walk hℓ'.2 hR) e)
                _ _ (hQ i' hK' (Term.boxtm bd')) (hQ i hK (Term.boxtm bd)) hann
              obtain rfl := Ann.box.inj hb
              -- the carriers denote alike
              have hc : B.rden s i' (Ctx.Le.refl _) (Term.diatm y hy' (Term.boxtm bd')) =
                  B.rden s i (Ctx.Le.refl _) (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd)) := by
                refine RPos.congr_cont (funext fun a₁ => hcont a₁.1 a₁.2) fun hSh => ?_
                have e₁ := congrArg (fun x => x.3 hSh)
                  (rden_lift hK' (Term.diatm y hy' (Term.boxtm bd')))
                have e₂ := congrArg (fun x => x.3 hSh)
                  (rden_lift hK (Term.diatm y ⟨Y, hY⟩ (Term.boxtm bd)))
                exact e₁.symm.trans ((Model.termShp_ann _ 0 _ _).trans e₂)
              have hv : B.toDom A s (B.rden s i' (Ctx.Le.refl _) t') (definable_rden _ _) =
                  B.toDom A s (B.rden s i (Ctx.Le.refl _) t) (definable_rden _ _) := by
                rw [hval, interp_canon t (Model.Env.Agree.refl' _)]
              obtain rfl := ann_eq_of_toDom hS hInj harr _ _ hv
              have hmc := (IH _ _ (by
                rw [WFF.size_eqRec]; simp only [VarType.eqRecSize] at hsz ⊢; omega)).mp
                (sat_eqRec_lift hK' hK _ _ (toDom_congr hc _ _))
              have hmv := (IH _ _ (by rw [WFF.size_eqRec]; omega)).mp
                (sat_eqRec_lift hK' hK _ _ hv)
              refine (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable (Δ := [_, _, _])
                (fun ψ hψ => by
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact (BWorld.mem_lift hK').mp hmem
                  rcases List.mem_cons.mp hψ with rfl | hψ
                  · exact hmc
                  · rw [List.mem_singleton.mp hψ]; exact hmv)
                ⟨Proof.back_eq hS .pos _ _ _ (Proof.back_eqC hS .pos _ _ _
                  (Proof.lookup List.mem_cons_self)
                  (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self)))
                  (Proof.lookup (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self)))⟩)

/-- ⭐⭐**`Back`, truth ⇒ membership** (strong B, any T), along either leg and at every content
    type: the truth lemma's `back` case in the direction the canonical `Ret` does not give for
    free (`mem_back_of_sat_nec`, `mem_back_of_sat_pos`).  It asks injective images (`ImgInj`) and
    fresh witness arrows (`CxFresh`), which the limit of a chain has. -/
theorem mem_back_of_sat (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hInj : B.ImgInj) (hCx : B.CxFresh) {s : B.W} {i : ℕ} (O : OutLeg ((B.w s).ctx i))
    {A : VarType} {a₀ : Ann A} (bd : Term σ O.view.boxIn A a₀) {a : Ann A}
    (t : Term σ ((B.w s).ctx i) A a)
    (IH : ∀ (K : ℕ) (φ : WFF σ ((B.w s).ctx K) 0),
      φ.size < (O.back hS bd t : WFF σ _ 0).size →
        (B.model.sat (B.canonEnv s K) φ ↔ φ ∈ (B.w s).M K))
    (h : B.model.sat (B.canonEnv s i) (O.back hS bd t : WFF σ _ 0)) :
    (O.back hS bd t : WFF σ _ 0) ∈ (B.w s).M i := by
  cases O with
  | nec => exact mem_back_of_sat_nec hS hB hInj bd t IH h
  | pos y hy => exact mem_back_of_sat_pos hS hB hInj hCx hy bd t IH h

end BData

end BArrow

end V12M
