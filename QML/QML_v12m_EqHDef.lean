import QML.QML_v12m_SubstEta
import QML.QML_v12m_Presented
import QML.QML_v12m_BackSyntax
import QML.QML_v12m_LoopHat
import QML.QML_v12m_LinkSyntax

/-!
# QML v12m — heterogeneous equality `≡`: the formula

The definition of `eqH` (`t ≡ s`, docs §12.2, §12.20) and what is syntactic about it: weakening,
collapse and substitution commute with it.  It comes before the proof system, since strong T's
rule states its hypothesis with `≡` when `Opt` is on (`Proof.T_dia`, docs §12.32).  The derived
rules about `≡` are in `QML_v12m_EqH`.
-/

namespace V12M

variable [ModalSys]

/-- A `◇`-address is a witness of the `□` view, with `Opt` on. -/
theorem Ctx.boxIn_wit_of {Γ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : ∃ X, Γ.boxIn.wit x = some X :=
  hx.imp fun _ h => Ctx.boxIn_wit.mpr ⟨hO, h⟩

/-- The `◇_x` view sits inside the `□` view with `x` and then `x'` opened. -/
theorem Ctx.le_diaIn_optIn₂ {Γ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (x' : VarSymb) :
    (Γ.diaIn x).Le ((Γ.boxIn.optIn x).optIn x') :=
  (hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h).trans (Ctx.le_optIn _ x')

/-- The `◇_{x'}` view sits inside the `□` view with `x` and then `x'` opened. -/
theorem Ctx.le_diaIn_optIn₂' {Γ : Ctx} (hO : ModalSys.Opt = true) (x : VarSymb) {x' : VarSymb}
    (hx' : ∃ X, Γ.ref x' = some (.VTypeDia X)) :
    (Γ.diaIn x').Le ((Γ.boxIn.optIn x).optIn x') :=
  (hx'.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h).trans ((Ctx.le_optIn Γ.boxIn x).optIn x')

/-- The `◇_x` view inside the `□` view with `x` opened, for an `∃`-declared witness. -/
theorem Ctx.le_diaIn_boxIn_optIn' {Γ : Ctx} (hO : ModalSys.Opt = true) {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) : (Γ.diaIn x).Le (Γ.boxIn.optIn x) :=
  hx.elim fun _ h => Ctx.le_diaIn_boxIn_optIn hO h

/-- In the identity view of a possible object its content there is a visible address. -/
theorem Ctx.ref_optInT_content {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.witT y = some X) :
    (Γ.optInT y).ref (.step y .at) = some X :=
  (Ctx.ref_nonproj _ rfl).trans (Ctx.optInT_content hy)

/-- ⭐**Heterogeneous equality** `t ≡ s`: `=` at `Var`, `⊤` at `𝟙`, componentwise at `×`, `□ ≡`
    at `□A`, and at `◇A` the two witnesses present together with `≡` contents, along every
    arrow.  At one annotation it agrees with `eqRec` in what it says, but it is a different
    formula at `◇` types. -/
def eqH {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) : {Γ : Ctx} → (T : VarType) →
    {a b : Ann T} → Term σ Γ T a → Term σ Γ T b → WFF σ Γ d
  | _, .Var, .var, .var, t, s => .eq t s
  | _, .VTypeOne, _, _, _, _ => .top
  | _, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ =>
      .and (eqH hO A t₁ s₁) (eqH hO B t₂ s₂)
  | _, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => .box (eqH hO A t s)
  | _, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s =>
      .box (.imp (.or (.optx hO .arrow x (Ctx.boxIn_wit_of hO hx) .top)
          (.optx hO .arrow x' (Ctx.boxIn_wit_of hO hx') .top))
        (.optx hO .arrow x (Ctx.boxIn_wit_of hO hx) (.optx hO .arrow x' (Ctx.boxIn_wit_of hO hx')
          (eqH hO A (Term.mono (Ctx.le_optIn _ x') (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))
            (Term.mono ((Ctx.le_optIn _ x).optIn x')
              (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s))))))

/-- ⭐**Two witnesses are equal**: present together, with `≡` contents.  The `□`-view part of `≡`
    at `◇` types (`eqH_dia`), and what relates two witnesses' entries in Leibniz. -/
abbrev witEq {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) {Γ : Ctx} (X : VarType)
    {z z' : VarSymb} (hz : ∃ Z, Γ.wit z = some Z) (hz' : ∃ Z, Γ.wit z' = some Z) {a b : Ann X}
    (c : Term σ (Γ.optIn z) X a) (c' : Term σ (Γ.optIn z') X b) : WFF σ Γ d :=
  .imp (.or (.optx hO .arrow z hz .top) (.optx hO .arrow z' hz' .top))
    (.optx hO .arrow z hz (.optx hO .arrow z' hz' (eqH hO X (Term.mono (Ctx.le_optIn _ z') c)
      (Term.mono ((Ctx.le_optIn Γ z).optIn z') c'))))

/-- At `◇` types, `≡` is `□` of the witnesses' equality. -/
theorem eqH_dia {σ : Signature} {Γ : Ctx} {d : ℕ} (hO : ModalSys.Opt = true) {A : VarType}
    {x x' : VarSymb} {a b : Ann A} (hx : ∃ X, Γ.ref x = some (.VTypeDia X))
    (hx' : ∃ X, Γ.ref x' = some (.VTypeDia X)) (t : Term σ (Γ.diaIn x) A a)
    (s : Term σ (Γ.diaIn x') A b) :
    (eqH hO (.VTypeDia A) (Term.diatm x hx t) (Term.diatm x' hx' s) : WFF σ Γ d) =
      .box (witEq hO A (Ctx.boxIn_wit_of hO hx) (Ctx.boxIn_wit_of hO hx')
        (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t)
        (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s)) :=
  rfl

/-- At base type `≡` is the primitive equality. -/
theorem eqH_Var {σ : Signature} {Γ : Ctx} {d : ℕ} (hO : ModalSys.Opt = true)
    (t s : Term σ Γ .Var .var) : (eqH hO .Var t s : WFF σ Γ d) = .eq t s := by
  cases t <;> cases s <;> rfl

/-- Weakening commutes with `≡`. -/
theorem eqH_mono {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) : {Γ Γ' : Ctx} →
    (h : Γ.Le Γ') → (T : VarType) → {a b : Ann T} → (t : Term σ Γ T a) → (s : Term σ Γ T b) →
    WFF.mono h (eqH hO T t s : WFF σ Γ d) = eqH hO T (Term.mono h t) (Term.mono h s)
  | _, _, h, .Var, .var, .var, t, s =>
      (congrArg (WFF.mono h) (eqH_Var hO t s)).trans (eqH_Var hO _ _).symm
  | _, _, _, .VTypeOne, .one, .one, .unit, .unit => rfl
  | _, _, h, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.mono h (eqH hO A t₁ s₁)) (WFF.mono h (eqH hO B t₂ s₂)) = _
      rw [eqH_mono hO h A, eqH_mono hO h B]
      rfl
  | _, _, h, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.mono h.boxIn (eqH hO A t s)) = _
      rw [eqH_mono hO h.boxIn A]
      rfl
  | Γ, _, h, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s => by
      have e := eqH_mono (d := d) hO ((h.boxIn.optIn x).optIn x') A
        (Term.mono (Ctx.le_optIn _ x') (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))
        (Term.mono ((Ctx.le_optIn _ x).optIn x') (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s))
      change WFF.box (WFF.imp (WFF.or _ _) (WFF.optx _ .arrow _ _ (WFF.optx _ .arrow _ _
        (WFF.mono ((h.boxIn.optIn x).optIn x') (eqH hO A _ _))))) = _
      rw [e]
      change _ = WFF.box (WFF.imp (WFF.or _ _) (WFF.optx _ .arrow _ _ (WFF.optx _ .arrow _ _
        (eqH hO A (Term.mono _ (Term.mono _ (Term.mono (h.diaIn x) t)))
          (Term.mono _ (Term.mono _ (Term.mono (h.diaIn x') s)))))))
      simp only [Term.mono_mono]
      rfl

/-! ## Collapse -/

/-- ⭐**Collapsing commutes with `≡`** at every type: each clause is the corresponding clause of
    `WFF.collapse`.  At `◇` types the witnesses sit under `□`, one level further in, and collapse
    along the arrow there.  With `T_box` this reads a `□`-hypothesis `□ (t ≡ s)` at the world
    itself (Leibniz along `≡` with T on, docs §12.32). -/
theorem WFF.collapse_eqH {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) : {k : ℕ} →
    {Γ₁ Γ₂ : Ctx} → (h : Ctx.Collapses k Γ₁ Γ₂) → (hs : Γ₁.SlotsFrom d) → (T : VarType) →
    {a b : Ann T} → (t : Term σ Γ₁ T a) → (s : Term σ Γ₁ T b) →
    WFF.collapse h hs (eqH hO T t s : WFF σ Γ₁ d) =
      eqH hO T (Term.collapse h t) (Term.collapse h s)
  | _, _, _, h, hs, .Var, .var, .var, t, s =>
      (congrArg (WFF.collapse h hs) (eqH_Var hO t s)).trans (eqH_Var hO _ _).symm
  | _, _, _, _, _, .VTypeOne, _, _, .unit, .unit => rfl
  | _, _, _, h, hs, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change WFF.and (WFF.collapse h hs (eqH hO A t₁ s₁)) (WFF.collapse h hs (eqH hO B t₂ s₂)) = _
      rw [WFF.collapse_eqH hO h hs A, WFF.collapse_eqH hO h hs B]
      rfl
  | _, _, _, h, hs, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.collapse h.boxIn hs.boxIn (eqH hO A t s)) = _
      rw [WFF.collapse_eqH hO h.boxIn hs.boxIn A]
      rfl
  | k, Γ₁, Γ₂, h, hs, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t, .diatm _ hx' s => by
      obtain ⟨X, hX⟩ := Ctx.boxIn_wit_of hO hx
      obtain ⟨X', hX'⟩ := Ctx.boxIn_wit_of hO hx'
      have C : Ctx.Collapses (k + 1) ((Γ₁.boxIn.optIn x).optIn x')
          ((Γ₂.boxIn.optIn (x.collapse k)).optIn (x'.collapse k)) :=
        (h.boxIn.optIn_succ hX).optIn_succ ((Ctx.le_optIn _ x).wit _ _ hX')
      have hxc : ∃ Y, Γ₂.ref (x.collapse k) = some (.VTypeDia Y) := hx.imp fun _ hY => h x _ hY
      have hxc' : ∃ Y, Γ₂.ref (x'.collapse k) = some (.VTypeDia Y) :=
        hx'.imp fun _ hY => h x' _ hY
      have ht : Term.collapse C (Term.mono (Ctx.le_optIn _ x')
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t)) =
          Term.mono (Ctx.le_optIn _ (x'.collapse k))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hxc) (Term.collapse (h.diaIn x) t)) := by
        rw [Term.mono_mono, Term.mono_mono, Term.collapse_mono (h.diaIn x) C _
          ((Ctx.le_diaIn_boxIn_optIn' hO hxc).trans (Ctx.le_optIn _ _))]
      have hs' : Term.collapse C (Term.mono ((Ctx.le_optIn _ x).optIn x')
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s)) =
          Term.mono ((Ctx.le_optIn _ (x.collapse k)).optIn (x'.collapse k))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hxc') (Term.collapse (h.diaIn x') s)) := by
        rw [Term.mono_mono, Term.mono_mono, Term.collapse_mono (h.diaIn x') C _
          ((Ctx.le_diaIn_boxIn_optIn' hO hxc').trans ((Ctx.le_optIn _ _).optIn _))]
      change WFF.box (WFF.imp (WFF.or _ _) (WFF.optx hO .arrow _ _ (WFF.optx hO .arrow _ _
        (WFF.collapse C _ (eqH hO A _ _))))) = _
      rw [WFF.collapse_eqH hO C _ A, ht, hs']
      rfl

/-- ⭐**Two witnesses of one kind are equal**: present together, with `≡` contents.  `witEq` is
    the arrow kind; at the identity kind it is what `T_box` makes of `□ witEq`
    (`WFF.collapse_witEq`), the two-entry case of Leibniz in the identity view (§12.32). -/
abbrev witEqK {σ : Signature} {d : ℕ} (hO : ModalSys.Opt = true) (κ : WitKind) {Γ : Ctx}
    (X : VarType) {z z' : VarSymb} (hz : ∃ Z, Γ.witK κ z = some Z)
    (hz' : ∃ Z, Γ.witK κ z' = some Z) {a b : Ann X} (c : Term σ (Γ.optInK κ z) X a)
    (c' : Term σ (Γ.optInK κ z') X b) : WFF σ Γ d :=
  .imp (.or (.optx hO κ z hz .top) (.optx hO κ z' hz' .top))
    (.optx hO κ z hz (.optx hO κ z' (hz'.imp fun _ h => (Ctx.le_optInK Γ κ z).witK h)
      (eqH hO X (Term.mono (Ctx.le_optInK _ κ z') c)
        (Term.mono ((Ctx.le_optInK Γ κ z).optInK κ z') c'))))

/-- ⭐**At level 0 the witnesses' equality collapses to the identity witnesses'**: each `◇⁰` along
    the arrow becomes `◇⁰ᵀ`, and the contents collapse into the identity views. -/
theorem WFF.collapse_witEq {σ : Signature} (hO : ModalSys.Opt = true) {Γ₁ Γ₂ : Ctx}
    (h : Ctx.Collapses 0 Γ₁ Γ₂) (hs : Γ₁.SlotsFrom 0) (X : VarType) {z z' : VarSymb}
    {Z Z' : VarType} (hZ : Γ₁.wit z = some Z) (hZ' : Γ₁.wit z' = some Z') {a b : Ann X}
    (c : Term σ (Γ₁.optIn z) X a) (c' : Term σ (Γ₁.optIn z') X b) :
    WFF.collapse h hs (witEq hO X ⟨Z, hZ⟩ ⟨Z', hZ'⟩ c c' : WFF σ Γ₁ 0) =
      witEqK hO .ident X ⟨Z, (h.wit z Z hZ).1 rfl⟩ ⟨Z', (h.wit z' Z' hZ').1 rfl⟩
        (Term.collapse (h.optIn_zero hO hZ) c) (Term.collapse (h.optIn_zero hO hZ') c') := by
  have C : Ctx.Collapses 0 ((Γ₁.optIn z).optIn z') ((Γ₂.optInT z).optInT z') :=
    (h.optIn_zero hO hZ).optIn_zero hO ((Ctx.le_optIn _ z).wit _ _ hZ')
  change WFF.imp (WFF.or (WFF.optx hO .ident z _ .top) (WFF.optx hO .ident z' _ .top))
    (WFF.optx hO .ident z _ (WFF.optx hO .ident z' _
      (WFF.collapse C _ (eqH hO X (Term.mono (Ctx.le_optIn _ z') c)
        (Term.mono ((Ctx.le_optIn Γ₁ z).optIn z') c'))))) = _
  rw [WFF.collapse_eqH hO C _ X,
    Term.collapse_mono (h.optIn_zero hO hZ) C (Ctx.le_optIn _ z') (Ctx.le_optInT _ z') c,
    Term.collapse_mono (h.optIn_zero hO hZ') C ((Ctx.le_optIn Γ₁ z).optIn z')
      ((Ctx.le_optInT Γ₂ z).optInT z') c']

/-! ## The conjuncts of `≡`, with T's readings -/

/-- ⭐**What `t ≡ s` gives as atoms**: its conjuncts, split at products and boxed at `□`, and
    under T also the equality read at the world itself (`T_box`, `collapse_eqH`), recursively.  The
    relation Leibniz carries (`SubE.EqH`) is built from these: T's projection `u.here` of a
    necessary object reads the collapsed equality (docs §12.32). -/
def eqHSat {σ : Signature} (hO : ModalSys.Opt = true) : {Γ : Ctx} → (T : VarType) →
    {a b : Ann T} → Term σ Γ T a → Term σ Γ T b → List (WFF σ Γ 0)
  | _, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ =>
      eqHSat hO A t₁ s₁ ++ eqHSat hO B t₂ s₂
  | Γ, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s =>
      (eqHSat hO A t s).map (fun c => WFF.box (Γ := Γ) c) ++
        (if hT : ModalSys.T = true then
          eqHSat hO A (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t)
            (Term.collapse (Ctx.collapses_boxIn_self hT Γ) s)
        else [])
  | _, T, _, _, t, s => [eqH hO T t s]

/-- Weakening commutes with `eqHSat`. -/
theorem eqHSat_mono {σ : Signature} (hO : ModalSys.Opt = true) : {Γ Γ' : Ctx} → (h : Γ.Le Γ') →
    (T : VarType) → {a b : Ann T} → (t : Term σ Γ T a) → (s : Term σ Γ T b) →
    (eqHSat hO T t s).map (WFF.mono h) = eqHSat hO T (Term.mono h t) (Term.mono h s)
  | _, _, h, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂, .pair s₁ s₂ => by
      change (eqHSat hO A t₁ s₁ ++ eqHSat hO B t₂ s₂).map _ =
        eqHSat hO A (Term.mono h t₁) (Term.mono h s₁) ++
          eqHSat hO B (Term.mono h t₂) (Term.mono h s₂)
      rw [List.map_append, eqHSat_mono hO h A, eqHSat_mono hO h B]
  | Γ, Γ', h, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change ((eqHSat hO A t s).map (fun c => WFF.box (Γ := Γ) c) ++
          (if hT : ModalSys.T = true then
            eqHSat hO A (Term.collapse (Ctx.collapses_boxIn_self hT Γ) t)
              (Term.collapse (Ctx.collapses_boxIn_self hT Γ) s) else [])).map (WFF.mono h) =
        (eqHSat hO A (Term.mono h.boxIn t) (Term.mono h.boxIn s)).map
            (fun c => WFF.box (Γ := Γ') c) ++
          (if hT : ModalSys.T = true then
            eqHSat hO A (Term.collapse (Ctx.collapses_boxIn_self hT Γ') (Term.mono h.boxIn t))
              (Term.collapse (Ctx.collapses_boxIn_self hT Γ') (Term.mono h.boxIn s)) else [])
      rw [List.map_append, List.map_map, ← eqHSat_mono hO h.boxIn A, List.map_map]
      congr 1
      by_cases hT : ModalSys.T = true
      · rw [dif_pos hT, dif_pos hT, eqHSat_mono hO h A,
          Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ) (Ctx.collapses_boxIn_self hT Γ')
            h.boxIn h t,
          Term.collapse_mono (Ctx.collapses_boxIn_self hT Γ) (Ctx.collapses_boxIn_self hT Γ')
            h.boxIn h s]
      · rw [dif_neg hT, dif_neg hT]
        rfl
  | _, _, h, .Var, .var, .var, t, s => by
      change [WFF.mono h (eqH hO .Var t s)] = [eqH hO .Var (Term.mono h t) (Term.mono h s)]
      rw [eqH_mono]
  | _, _, h, .VTypeOne, _, _, t, s => by
      change [WFF.mono h (eqH hO .VTypeOne t s)] =
        [eqH hO .VTypeOne (Term.mono h t) (Term.mono h s)]
      rw [eqH_mono]
  | _, _, h, .VTypeDia A, _, _, t, s => by
      change [WFF.mono h (eqH hO (.VTypeDia A) t s)] =
        [eqH hO (.VTypeDia A) (Term.mono h t) (Term.mono h s)]
      rw [eqH_mono]

/-! ## Substitution -/

/-- On the `◇_z` view, the `□` view of `θ` with `z` and then `z'` opened is `θ.dia`, weakened: the
    content's entry is the body either way (`SubE.toWit_optBody`), re-opened when `z' = z`
    (`WitE.optBody_mono`). -/
theorem Subst.simT_optIn₂_dia {σ : Signature} {Γ Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ)
    (hO : ModalSys.Opt = true) (ι : VarSymb → VarSymb) {z z' : VarSymb} {Z Y : VarType}
    (hZ : Γ.ref z = some (.VTypeDia Z)) (hY : Δ.ref (ι z) = some (.VTypeDia Y))
    (L : (Δ.diaIn (ι z)).Le ((Δ.boxIn.optIn (ι z)).optIn (ι z'))) :
    Subst.SimT (Γ.diaIn z) ((θ.box.optIn z (ι z)).optIn z' (ι z')) ((θ.dia z (ι z)).mono L) := by
  refine Subst.simT_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = z then (match Γ.ref z with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huz
      subst huz
      rw [hZ] at hv
      cases hv
      change SubE.Sim Z (((θ.box.optIn u (ι u)).optIn z' (ι z')) (.step u .dia))
        (SubE.mono L (if u = u then (θ.at u).diaBody (ι u) else SubE.hide))
      rw [if_pos rfl]
      by_cases hzz : u = z'
      · subst hzz
        rw [Subst.optIn_content]
        change SubE.Sim Z (((θ.box.wit u).mono (Ctx.le_optIn Δ.boxIn (ι u))).optBody (ι u)) _
        rw [← WitE.optBody_mono]
        change SubE.Sim Z (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
        rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ) (Ctx.le_diaIn_boxIn_optIn hO hY),
          SubE.mono_mono]
        exact .refl _
      · rw [Subst.optIn_ne _ _ (fun h => hzz (by cases h; rfl)), Subst.optIn_content]
        change SubE.Sim Z (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
        rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ) (Ctx.le_diaIn_boxIn_optIn hO hY),
          SubE.mono_mono]
        exact .refl _
  | .step u .box =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .box))
        (SubE.mono L (((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ (ι z))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).unbox))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .keep))
        (SubE.mono L (((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ (ι z))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).keepE))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- On the `◇_{z'}` view, the same, with `z'` the witness opened last. -/
theorem Subst.simT_optIn₂_dia' {σ : Signature} {Γ Δ : Ctx} {θ : Subst σ Δ} (hθ : Subst.Ok Γ θ)
    (hO : ModalSys.Opt = true) (ι : VarSymb → VarSymb) (z : VarSymb) {z' : VarSymb}
    {Z' Y' : VarType} (hZ' : Γ.ref z' = some (.VTypeDia Z'))
    (hY' : Δ.ref (ι z') = some (.VTypeDia Y'))
    (L : (Δ.diaIn (ι z')).Le ((Δ.boxIn.optIn (ι z)).optIn (ι z'))) :
    Subst.SimT (Γ.diaIn z') ((θ.box.optIn z (ι z)).optIn z' (ι z')) ((θ.dia z' (ι z')).mono L) := by
  refine Subst.simT_of ?_
  intro v T _ hv
  match v with
  | .step u .dia =>
      change (if u = z' then (match Γ.ref z' with | some (.VTypeDia X) => some X | _ => none)
        else none) = some T at hv
      split_ifs at hv with huz
      subst huz
      rw [hZ'] at hv
      cases hv
      change SubE.Sim Z' (((θ.box.optIn z (ι z)).optIn u (ι u)) (.step u .dia))
        (SubE.mono L (if u = u then (θ.at u).diaBody (ι u) else SubE.hide))
      rw [if_pos rfl, Subst.optIn_content]
      change SubE.Sim Z' (((θ.box.wit u).mono (Ctx.le_optIn Δ.boxIn (ι z))).optBody (ι u)) _
      rw [← WitE.optBody_mono]
      change SubE.Sim Z' (SubE.mono _ (((θ.at u).toWit).optBody (ι u))) _
      rw [SubE.toWit_optBody hO (ι u) (Subst.okRef_at hθ hZ') (Ctx.le_diaIn_boxIn_optIn hO hY'),
        SubE.mono_mono]
      exact .refl _
  | .step u .box =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .box))
        (SubE.mono L (((θ.at u).unbox).mono (Ctx.le_boxIn_diaIn Δ (ι z'))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).unbox))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .step u .keep =>
      change SubE.Sim T (((θ.box.optIn z (ι z)).optIn z' (ι z')) (.step u .keep))
        (SubE.mono L (((θ.at u).keepE).mono (Ctx.le_boxIn_diaIn Δ (ι z'))))
      rw [Subst.optIn_ne _ _ (fun h => by cases h), Subst.optIn_ne _ _ (fun h => by cases h)]
      change SubE.Sim T (SubE.mono _ (SubE.mono _ ((θ.at u).keepE))) _
      simp only [SubE.mono_mono]
      exact .refl _
  | .root _ => cases hv
  | .step _ .fst => cases hv
  | .step _ .snd => cases hv
  | .step _ .here => cases hv

/-- ⭐**Substitution commutes with `≡`**: at `◇` types the contents are substituted in the view
    with both witnesses opened, which is each content's own `◇` view weakened
    (`Subst.simT_optIn₂_dia`, `Subst.simT_optIn₂_dia'`). -/
theorem WFF.subst_eqH {σ : Signature} {ι : VarSymb → VarSymb} (hO : ModalSys.Opt = true) :
    {Γ Δ : Ctx} → {d d' : ℕ} → (θ : Subst σ Δ) → (hθ : Subst.Ok Γ θ) → (hc : Subst.Coh ι Γ θ) →
    (hΓ : Γ.SlotsFrom d) → (hΔ : Δ.SlotsFrom d') → (T : VarType) → {a b : Ann T} →
    (t : Term σ Γ T a) → (s : Term σ Γ T b) →
    WFF.subst ι θ hθ hc hΓ hΔ (eqH hO T t s : WFF σ Γ d) =
      eqH hO T (Term.subst ι θ hθ hc t) (Term.subst ι θ hθ hc s)
  | _, _, _, _, _, _, _, _, _, .Var, .var, .var, t, s => by
      rw [eqH_Var, eqH_Var]
      rfl
  | _, _, _, _, _, _, _, _, _, .VTypeOne, .one, .one, .unit, .unit => rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeProd A B, .prod _ _, .prod _ _, .pair t₁ t₂,
      .pair s₁ s₂ => by
      change WFF.and (WFF.subst ι θ hθ hc hΓ hΔ (eqH hO A t₁ s₁))
        (WFF.subst ι θ hθ hc hΓ hΔ (eqH hO B t₂ s₂)) = _
      rw [WFF.subst_eqH hO θ hθ hc hΓ hΔ A t₁ s₁, WFF.subst_eqH hO θ hθ hc hΓ hΔ B t₂ s₂]
      rfl
  | _, _, _, _, θ, hθ, hc, hΓ, hΔ, .VTypeBox A, .box _, .box _, .boxtm t, .boxtm s => by
      change WFF.box (WFF.subst ι θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc)
        hΓ.boxIn hΔ.boxIn (eqH hO A t s)) = _
      rw [WFF.subst_eqH hO θ.box (Subst.ok_box hθ) (Subst.coh_box hθ hc) hΓ.boxIn hΔ.boxIn A t s]
      rfl
  | Γ, Δ, d, d', θ, hθ, hc, hΓ, hΔ, .VTypeDia A, .dia x _, .dia x' _, .diatm _ hx t,
      .diatm _ hx' s => by
      obtain ⟨X, hr⟩ := id hx
      obtain ⟨X', hr'⟩ := id hx'
      have hw : (θ.at x).idxAlong [] = ι x := hc x _ hr []
      have hw' : (θ.at x').idxAlong [] = ι x' := hc x' _ hr' []
      obtain ⟨Y, hY⟩ := SubE.ref_witness (Subst.okRef_at hθ hr) hw
      obtain ⟨Y', hY'⟩ := SubE.ref_witness (Subst.okRef_at hθ hr') hw'
      have hb : Γ.boxIn.wit x = some X := Ctx.boxIn_wit.mpr ⟨hO, hr⟩
      have hb' : (Γ.boxIn.optIn x).wit x' = some X' := Ctx.boxIn_wit.mpr ⟨hO, hr'⟩
      have hθ₁ := Subst.ok_optIn (Subst.ok_box hθ) hO hb ((Subst.coh_box hθ hc).wit hO x X hb [])
      have hc₁ := Subst.coh_optIn (Subst.ok_box hθ) (Subst.coh_box hθ hc) hO hb
      have hθ₂ := Subst.ok_optIn hθ₁ hO hb' (hc₁.wit hO x' X' hb' [])
      have hc₂ := Subst.coh_optIn hθ₁ hc₁ hO hb'
      have ih := WFF.subst_eqH (d := d) (d' := d') hO ((θ.box.optIn x (ι x)).optIn x' (ι x'))
        hθ₂ hc₂ ((hΓ.boxIn.optIn x).optIn x') ((hΔ.boxIn.optIn (ι x)).optIn (ι x')) A
        (Term.mono (Ctx.le_optIn _ x') (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx) t))
        (Term.mono ((Ctx.le_optIn _ x).optIn x') (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO hx') s))
      have L := Ctx.le_diaIn_optIn₂ hO ⟨Y, hY⟩ (ι x')
      have L' := Ctx.le_diaIn_optIn₂' hO (ι x) ⟨Y', hY'⟩
      rw [Term.subst_mono, Term.subst_mono, Term.subst_mono, Term.subst_mono,
        Term.subst_congr_eq _ _ _ (Subst.ok_mono (Subst.ok_dia hθ hx hw) L) _
          (Subst.coh_mono (Subst.coh_dia hθ hc hx) L) (Subst.simT_optIn₂_dia hθ hO ι hr hY L) t,
        Term.subst_congr_eq _ _ _ (Subst.ok_mono (Subst.ok_dia hθ hx' hw') L') _
          (Subst.coh_mono (Subst.coh_dia hθ hc hx') L')
          (Subst.simT_optIn₂_dia' hθ hO ι x hr' hY' L') s,
        ← Term.mono_subst L _ (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx),
        ← Term.mono_subst L' _ (Subst.ok_dia hθ hx' hw') (Subst.coh_dia hθ hc hx')] at ih
      rw [show Term.mono L (Term.subst ι (θ.dia x (ι x)) (Subst.ok_dia hθ hx hw)
            (Subst.coh_dia hθ hc hx) t) = Term.mono (Ctx.le_optIn _ (ι x'))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO ⟨Y, hY⟩) (Term.subst ι (θ.dia x (ι x))
              (Subst.ok_dia hθ hx hw) (Subst.coh_dia hθ hc hx) t)) from
          (Term.mono_mono _ _ _).symm,
        show Term.mono L' (Term.subst ι (θ.dia x' (ι x')) (Subst.ok_dia hθ hx' hw')
            (Subst.coh_dia hθ hc hx') s) = Term.mono ((Ctx.le_optIn _ (ι x)).optIn (ι x'))
            (Term.mono (Ctx.le_diaIn_boxIn_optIn' hO ⟨Y', hY'⟩) (Term.subst ι (θ.dia x' (ι x'))
              (Subst.ok_dia hθ hx' hw') (Subst.coh_dia hθ hc hx') s)) from
          (Term.mono_mono _ _ _).symm] at ih
      exact congrArg (fun χ => WFF.box (WFF.imp
        (WFF.or (WFF.optx hO .arrow (ι x) (Ctx.boxIn_wit_of hO ⟨Y, hY⟩) .top)
          (WFF.optx hO .arrow (ι x') (Ctx.boxIn_wit_of hO ⟨Y', hY'⟩) .top))
        (WFF.optx hO .arrow (ι x) (Ctx.boxIn_wit_of hO ⟨Y, hY⟩)
          (WFF.optx hO .arrow (ι x') (Ctx.boxIn_wit_of hO ⟨Y', hY'⟩) χ)))) ih

/-- `≡` of terms equal with their annotations. -/
theorem eqH_congr {σ : Signature} {Γ : Ctx} {d : ℕ} (hO : ModalSys.Opt = true) {T : VarType}
    {a a' b b' : Ann T} {t : Term σ Γ T a} {t' : Term σ Γ T a'} {s : Term σ Γ T b}
    {s' : Term σ Γ T b'} (ht : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩)
    (hs : (⟨b, s⟩ : Σ c, Term σ Γ T c) = ⟨b', s'⟩) :
    (eqH hO T t s : WFF σ Γ d) = eqH hO T t' s' := by
  cases ht
  cases hs
  rfl

/-- Substituting into `◇⁰_y` where the image of `y` is known to be `z`. -/
theorem WFF.subst_optx_eq {σ : Signature} {ι : VarSymb → VarSymb} {Γ Δ : Ctx} {d d' : ℕ}
    (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom d)
    (hΔ : Δ.SlotsFrom d') (hO : ModalSys.Opt = true) (y : VarSymb)
    (hy : ∃ X, Γ.wit y = some X) (φ : WFF σ (Γ.optIn y) d) {z : VarSymb} (hz : ι y = z)
    (hz' : ∃ X, Δ.wit z = some X) (hθz : Subst.Ok (Γ.optIn y) (θ.optIn y z))
    (hcz : Subst.Coh ι (Γ.optIn y) (θ.optIn y z)) :
    WFF.subst ι θ hθ hc hΓ hΔ (.optx hO .arrow y hy φ) =
      .optx hO .arrow z hz' (WFF.subst ι (θ.optIn y z) hθz hcz (hΓ.optIn y) (hΔ.optIn z) φ) := by
  subst hz
  rfl

/-- In the view of a witness its content is a visible address. -/
theorem Ctx.ref_optIn_content {Γ : Ctx} {y : VarSymb} {X : VarType} (hy : Γ.wit y = some X) :
    (Γ.optIn y).ref (.step y .dia) = some X :=
  (Ctx.ref_nonproj _ rfl).trans (Ctx.optIn_content hy)

/-- `◇⁰_y (y.dia ≡ e)`, `e` the slot: the witness `y` is present, with content `e`. -/
abbrev WFF.optName {σ : Signature} {Γ : Ctx} (hO : ModalSys.Opt = true) {y : VarSymb}
    {X : VarType} (hy : Γ.wit y = some X) : WFF σ (Γ.insert (.bnd 0) X) 1 :=
  WFF.optx hO .arrow y ⟨X, hy⟩ (eqH hO X
    (Term.eta (.step y .dia) X (Ctx.ref_optIn_content (Γ := Γ.insert (.bnd 0) X) hy))
    (Term.eta (.root (.bnd 0)) X
      ((Ctx.le_optIn _ y).ref (Ctx.ref_insert_root Γ (.bnd 0) X))))

end V12M
