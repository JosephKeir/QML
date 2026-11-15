import QML.QML_v12m_Collapse

/-!
# QML v12m — reading opened contents at names

A canonical model must sometimes read, at a world, a view whose extra addresses its language
cannot declare (docs §12.36): under T a possible object's content at the identity arrow (`x.at`);
for B and 5, contents along the way home or across.  Canonical domains are definable, so each such
content is denoted by a term of the world's language, fixed by the theory: a **name**.  Reading
the view at the names is a renaming of addresses, `x.at.p ↦ n.p`, but **not a substitution**: out
of `x`'s identity view a substitution must send `x.at` to the image's identity content
(`Subst.Coh.openedT`).  The renaming is meaning-preserving only when the names denote the contents,
so it is a dedicated recursion, as `Term.collapse` is.

* `VarSymb.readNames ν k`: `ν` names witnesses (`y ↦ n`, for `y.at`); the renamed content step is
  the `at` step with exactly `k` level steps after it (so a view never captures another world's
  content), as `VarSymb.collapse k` locates its level.
* `Ann.readNames`: annotations' indices, at their levels.
* `Ctx.ReadsNames ν k Γ₁ Γ₂`: everything `Γ₁` reaches, `Γ₂` reaches after renaming; witnesses one
  level out are read one level out; and at level 0 every named witness is a possible address of
  `Γ₁` whose name has the content type.  It passes into every view and binder.
-/

namespace V12M

variable [ModalSys]

namespace VarSymb

/-- ⭐**Rename the named identity contents**: the `at` step with exactly `k` level steps after it,
    at a named witness, becomes the name. -/
def readNames (ν : VarSymb → Option VarSymb) : ℕ → VarSymb → VarSymb
  | _, root r => root r
  | k, step v s =>
      if s.isProj then
        if k = 0 ∧ s = .at then (ν v).elim (step (readNames ν k v) s) id
        else step (readNames ν k v) s
      else match k with
        | 0 => step v s
        | k + 1 => step (readNames ν k v) s

/-- The witness map one level out: at level 0 nothing, at `k + 1` the renaming at `k`. -/
def readNamesW (ν : VarSymb → Option VarSymb) : ℕ → VarSymb → VarSymb
  | 0, y => y
  | k + 1, y => y.readNames ν k

variable {ν : VarSymb → Option VarSymb}

omit [ModalSys] in
theorem readNames_root {k : ℕ} {r : Root} : (root r).readNames ν k = root r := rfl

omit [ModalSys] in
theorem readNames_proj {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = true)
    (hne : ¬ (k = 0 ∧ s = .at)) : (step v s).readNames ν k = step (v.readNames ν k) s := by
  simp only [readNames, hs, if_true, if_neg hne]

omit [ModalSys] in
theorem readNames_at_named {v n : VarSymb} (h : ν v = some n) :
    (step v .at).readNames ν 0 = n := by
  simp only [readNames, Step.isProj, if_true, and_self, h, Option.elim_some, id]

omit [ModalSys] in
theorem readNames_at_unnamed {v : VarSymb} (h : ν v = none) :
    (step v .at).readNames ν 0 = step (v.readNames ν 0) .at := by
  simp only [readNames, Step.isProj, if_true, and_self, h, Option.elim_none]

omit [ModalSys] in
theorem readNames_at_succ {k : ℕ} {v : VarSymb} :
    (step v .at).readNames ν (k + 1) = step (v.readNames ν (k + 1)) .at :=
  readNames_proj rfl (by simp)

omit [ModalSys] in
theorem readNames_level_zero {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).readNames ν 0 = step v s := by
  simp only [readNames, hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
theorem readNames_level_succ {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isProj = false) :
    (step v s).readNames ν (k + 1) = step (v.readNames ν k) s := by
  simp only [readNames, hs, Bool.false_eq_true, if_false]

omit [ModalSys] in
/-- Structural steps commute with the renaming. -/
theorem readNames_struct {k : ℕ} {v : VarSymb} {s : Step} (hs : s.isStruct = true) :
    (step v s).readNames ν k = step (v.readNames ν k) s :=
  readNames_proj (Step.isProj_of_isStruct hs) (fun h => by rw [h.2] at hs; cases hs)

omit [ModalSys] in
theorem readNames_rt {k : ℕ} (hν : ∀ v n, ν v = some n → n.rt = v.rt) :
    ∀ v : VarSymb, (v.readNames ν k).rt = v.rt
  | root _ => rfl
  | step v s => by
      by_cases hs : s.isProj = true
      · by_cases hk : k = 0 ∧ s = .at
        · obtain ⟨rfl, rfl⟩ := hk
          cases hv : ν v with
          | none => rw [readNames_at_unnamed hv]; exact readNames_rt hν v
          | some n => rw [readNames_at_named hv, hν v n hv]; rfl
        · rw [readNames_proj hs hk]; exact readNames_rt hν v
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases k with
        | zero => rw [readNames_level_zero hs']
        | succ k => rw [readNames_level_succ hs']; exact readNames_rt (k := k) hν v

end VarSymb

/-- Rename the indices of an annotation found `k` levels below the named contents. -/
def Ann.readNames (ν : VarSymb → Option VarSymb) : ℕ → {T : VarType} → Ann T → Ann T
  | _, _, .var => .var
  | _, _, .one => .one
  | k, _, .prod a b => .prod (a.readNames ν k) (b.readNames ν k)
  | k, _, .box a => .box (a.readNames ν (k + 1))
  | k, _, .dia i a => .dia (i.readNames ν k) (a.readNames ν (k + 1))

namespace Ctx

/-- ⭐**Reading at names is well typed**: everything `Γ₁` reaches, `Γ₂` reaches after renaming;
    `Γ₁`'s witnesses, one level out, are read one level out; and at level 0 every named witness is
    a possible address of `Γ₁` whose name has the content type. -/
structure ReadsNames (ν : VarSymb → Option VarSymb) (k : ℕ) (Γ₁ Γ₂ : Ctx) : Prop where
  ty : ∀ v T, Γ₁.ref v = some T → Γ₂.ref (v.readNames ν k) = some T
  wit : ∀ y X, Γ₁.wit y = some X → Γ₂.wit (y.readNamesW ν k) = some X
  named : k = 0 → ∀ y n, ν y = some n → ∃ X, Γ₁.ref y = some (.VTypeDia X) ∧ Γ₂.ref n = some X

instance {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx} :
    CoeFun (ReadsNames ν k Γ₁ Γ₂)
      (fun _ => ∀ v T, Γ₁.ref v = some T → Γ₂.ref (v.readNames ν k) = some T) :=
  ⟨ReadsNames.ty⟩

variable {ν : VarSymb → Option VarSymb}

/-- It suffices to check the visible non-projection addresses. -/
theorem ReadsNames.of_raw {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : ∀ v T, v.lastProj = false → Γ₁ v = some T → Γ₂.ref (v.readNames ν k) = some T)
    (hwit : ∀ y X, Γ₁.wit y = some X → Γ₂.wit (y.readNamesW ν k) = some X)
    (hnamed : k = 0 → ∀ y n, ν y = some n →
      ∃ X, Γ₁.ref y = some (.VTypeDia X) ∧ Γ₂.ref n = some X) :
    ReadsNames ν k Γ₁ Γ₂ := by
  refine ⟨?_, hwit, hnamed⟩
  intro v
  induction v with
  | root r => intro T hv; exact h _ _ rfl hv
  | step v s ih =>
      intro T hv
      by_cases hs : s.isStruct = true
      · rw [Ctx.ref_step_proj _ _ hs] at hv
        rw [VarSymb.readNames_struct hs, Ctx.ref_step_proj _ _ hs]
        cases hU : Γ₁.ref v with
        | none => rw [hU] at hv; cases hv
        | some U => rw [hU] at hv; rw [ih U hU]; exact hv
      · exact h _ _ (show s.isStruct = false from Bool.eq_false_iff.mpr hs)
          (by rwa [Ctx.ref_step_nonproj _ _ hs] at hv)

theorem ReadsNames.boxIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : ReadsNames ν k Γ₁ Γ₂) :
    ReadsNames ν (k + 1) Γ₁.boxIn Γ₂.boxIn := by
  refine ReadsNames.of_raw ?_ (fun y X hy => ?_) (fun h0 => absurd h0 (by omega))
  · intro v T _ hv
    match v with
    | .step u .box =>
        obtain ⟨hk, hu⟩ := boxIn_box hv
        rw [VarSymb.readNames_level_succ rfl, Ctx.ref_nonproj _ rfl]
        exact boxIn_box_of hk (h u _ hu)
    | .step u .keep =>
        obtain ⟨hF, hu, hk⟩ := boxIn_keep hv
        rw [VarSymb.readNames_level_succ rfl, Ctx.ref_nonproj _ rfl]
        exact boxIn_keep_of' hF (h u _ hu) hk
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .dia => cases hv
    | .step _ .here => cases hv
    | .step _ .at => cases hv
  · obtain ⟨hO, hr⟩ := boxIn_wit.mp hy
    exact boxIn_wit.mpr ⟨hO, h y _ hr⟩

theorem ReadsNames.diaIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : ReadsNames ν k Γ₁ Γ₂) (x : VarSymb) :
    ReadsNames ν (k + 1) (Γ₁.diaIn x) (Γ₂.diaIn (x.readNames ν k)) := by
  refine ReadsNames.of_raw ?_ (fun y X hy => ?_) (fun h0 => absurd h0 (by omega))
  · intro v T _ hv
    match v with
    | .step u .dia =>
        change (if u = x then (match Γ₁.ref x with | some (.VTypeDia X) => some X | _ => none)
          else none) = some T at hv
        split_ifs at hv with hux
        subst hux
        cases hx : Γ₁.ref u with
        | none => rw [hx] at hv; cases hv
        | some U =>
            rw [hx] at hv
            rw [VarSymb.readNames_level_succ rfl, Ctx.ref_nonproj _ rfl]
            change (if u.readNames ν k = u.readNames ν k then
              (match Γ₂.ref (u.readNames ν k) with | some (.VTypeDia X) => some X | _ => none)
              else none) = some T
            rw [if_pos rfl, h u _ hx]
            exact hv
    | .step u .box =>
        obtain ⟨hk, hu⟩ := boxIn_box (Γ := Γ₁) hv
        rw [VarSymb.readNames_level_succ rfl, Ctx.ref_nonproj _ rfl]
        exact boxIn_box_of (Γ := Γ₂) hk (h u _ hu)
    | .step u .keep =>
        obtain ⟨hF, hu, hk⟩ := boxIn_keep (Γ := Γ₁) hv
        rw [VarSymb.readNames_level_succ rfl, Ctx.ref_nonproj _ rfl]
        exact boxIn_keep_of' hF (h u _ hu) hk
    | .root _ => cases hv
    | .step _ .fst => cases hv
    | .step _ .snd => cases hv
    | .step _ .here => cases hv
    | .step _ .at => cases hv
  · obtain ⟨hO, hr⟩ := (boxIn_wit (Γ := Γ₁)).mp hy
    exact (boxIn_wit (Γ := Γ₂)).mpr ⟨hO, h y _ hr⟩

omit [ModalSys] in
/-- The renaming leaves an address's root alone unless a name supplies it. -/
theorem _root_.V12M.VarSymb.readNames_rt_ne {r : Root} (hn : ∀ y n, ν y = some n → n.rt ≠ r) :
    ∀ {k : ℕ} (v : VarSymb), v.rt ≠ r → (v.readNames ν k).rt ≠ r
  | _, .root _, h => h
  | k, .step v s, h => by
      by_cases hs : s.isProj = true
      · by_cases hk : k = 0 ∧ s = .at
        · obtain ⟨rfl, rfl⟩ := hk
          cases hv : ν v with
          | none => rw [VarSymb.readNames_at_unnamed hv]; exact VarSymb.readNames_rt_ne hn v h
          | some n => rw [VarSymb.readNames_at_named hv]; exact hn v n hv
        · rw [VarSymb.readNames_proj hs hk]; exact VarSymb.readNames_rt_ne hn v h
      · have hs' : s.isProj = false := Bool.eq_false_iff.mpr hs
        cases k with
        | zero => rw [VarSymb.readNames_level_zero hs']; exact h
        | succ k => rw [VarSymb.readNames_level_succ hs']; exact VarSymb.readNames_rt_ne hn v h

omit [ModalSys] in
theorem _root_.V12M.VarSymb.readNamesW_rt_ne {r : Root} (hn : ∀ y n, ν y = some n → n.rt ≠ r) :
    ∀ {k : ℕ} (v : VarSymb), v.rt ≠ r → (v.readNamesW ν k).rt ≠ r
  | 0, _, h => h
  | _ + 1, v, h => VarSymb.readNames_rt_ne hn v h

/-- Into a binder: the fresh root stays, the names avoiding it. -/
theorem ReadsNames.insert {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : ReadsNames ν k Γ₁ Γ₂) {r : Root}
    (hr : Γ₁.RootFresh r) (hn : ∀ y n, ν y = some n → n.rt ≠ r) (T : VarType) :
    ReadsNames ν k (Γ₁.insert r T) (Γ₂.insert r T) := by
  refine ReadsNames.of_raw ?_ (fun y X hy => ?_) (fun h0 y n hyn => ?_)
  · intro v U hlp hv
    by_cases hvr : v = .root r
    · subst hvr
      have hTU : T = U := by simpa [Ctx.insert] using hv
      subst hTU
      exact ref_insert_root Γ₂ r T
    · have hv' : Γ₁ v = some U := Ctx.insert_ne_some hv hvr
      have hrt : v.rt ≠ r := fun he => by rw [hr v he] at hv'; cases hv'
      rw [ref_insert_ne T (VarSymb.readNames_rt_ne hn v hrt)]
      exact h v U ((Ctx.ref_nonproj Γ₁ hlp).trans hv')
  · change Γ₁.wit y = some X at hy
    have hrt : y.rt ≠ r := fun he => by rw [hr.wit y he] at hy; cases hy
    change Γ₂.wit _ = some X
    exact h.wit y X hy
  · obtain ⟨X, hX, hn'⟩ := h.named h0 y n hyn
    have hrt : y.rt ≠ r := fun he => by
      rw [Ctx.ref_none_of_rootFresh hr y he] at hX; cases hX
    exact ⟨X, by rw [ref_insert_ne T hrt]; exact hX,
      by rw [ref_insert_ne T (hn y n hyn)]; exact hn'⟩

/-- Into the view of a witness along the arrow: its content is renamed as the witness is. -/
theorem ReadsNames.optIn {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : ReadsNames ν k Γ₁ Γ₂) {y : VarSymb}
    {X : VarType} (hy : Γ₁.wit y = some X) :
    ReadsNames ν k (Γ₁.optIn y) (Γ₂.optIn (y.readNamesW ν k)) := by
  refine ReadsNames.of_raw ?_ (fun z Z hz => (le_optIn Γ₂ _).wit _ _ (h.wit z Z hz))
    (fun h0 z n hzn => ?_)
  · intro v T hlp hv
    by_cases hc : v = .step y .dia
    · subst hc
      rw [optIn_content hy] at hv
      cases hv
      have e : (VarSymb.step y .dia).readNames ν k = .step (y.readNamesW ν k) .dia := by
        cases k with
        | zero => exact VarSymb.readNames_level_zero rfl
        | succ k => exact VarSymb.readNames_level_succ rfl
      rw [e, Ctx.ref_nonproj _ rfl]
      exact optIn_content (h.wit y _ hy)
    · rw [optIn_ne hc] at hv
      exact (le_optIn Γ₂ _).ref (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))
  · obtain ⟨Z, hZ, hn⟩ := h.named h0 z n hzn
    exact ⟨Z, (le_optIn Γ₁ y).ref hZ, (le_optIn Γ₂ _).ref hn⟩

/-- ⭐Into a witness's identity view: its content is renamed to its name at level 0 when it has
    one, and otherwise to the renamed witness's content. -/
theorem ReadsNames.optInT {k : ℕ} {Γ₁ Γ₂ : Ctx} (h : ReadsNames ν k Γ₁ Γ₂) {y : VarSymb}
    {X : VarType} (hy : Γ₁.witT y = some X) :
    ReadsNames ν k (Γ₁.optInT y) (Γ₂.optInT (y.readNames ν k)) := by
  obtain ⟨hT, hO, hr⟩ := witT_spec hy
  refine ReadsNames.of_raw ?_ (fun z Z hz => (le_optInT Γ₂ _).wit _ _ (h.wit z Z hz))
    (fun h0 z n hzn => ?_)
  · intro v T hlp hv
    by_cases hc : v = .step y .at
    · subst hc
      rw [optInT_content hy] at hv
      cases hv
      by_cases hk : k = 0 ∧ (ν y).isSome
      · obtain ⟨rfl, hs⟩ := hk
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
        rw [VarSymb.readNames_at_named hn]
        obtain ⟨X', hX', hn'⟩ := h.named rfl y n hn
        rw [hr] at hX'
        cases hX'
        exact (le_optInT Γ₂ _).ref hn'
      · have e : (VarSymb.step y .at).readNames ν k = .step (y.readNames ν k) .at := by
          cases k with
          | zero =>
              have hnone : ν y = none := by
                cases hv : ν y with
                | none => rfl
                | some _ => exact absurd ⟨rfl, by rw [hv]; rfl⟩ hk
              exact VarSymb.readNames_at_unnamed hnone
          | succ k => exact VarSymb.readNames_at_succ
        rw [e, Ctx.ref_nonproj _ rfl]
        exact optInT_content (witT_of hT hO (h y _ hr))
    · rw [optInT_ne hc] at hv
      exact (le_optInT Γ₂ _).ref (h v T ((Ctx.ref_nonproj Γ₁ hlp).trans hv))
  · obtain ⟨Z, hZ, hn⟩ := h.named h0 z n hzn
    exact ⟨Z, (le_optInT Γ₁ y).ref hZ, (le_optInT Γ₂ _).ref hn⟩

end Ctx

/-! ## Reading terms and formulas at names -/

mutual
  def Func.readNames {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ} :
      {Γ₁ Γ₂ : Ctx} → Ctx.ReadsNames ν k Γ₁ Γ₂ → {n : ℕ} → Func σ Γ₁ n → Func σ Γ₂ n
    | _, _, _, _, .F f => .F f
    | _, _, h, _, .eval g t => .eval (Func.readNames h g) (Term.readNames h t)

  /-- ⭐A term read at the names. -/
  def Term.readNames {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ} :
      {Γ₁ Γ₂ : Ctx} → Ctx.ReadsNames ν k Γ₁ Γ₂ → {T : VarType} → {a : Ann T} →
      Term σ Γ₁ T a → Term σ Γ₂ T (a.readNames ν k)
    | _, _, h, _, _, .var v hv => .var (v.readNames ν k) (h v _ hv)
    | _, _, h, _, _, .func f => .func (Func.readNames h f)
    | _, _, _, _, _, .unit => .unit
    | _, _, h, _, _, .pair s t => .pair (Term.readNames h s) (Term.readNames h t)
    | _, _, h, _, _, .boxtm t => .boxtm (Term.readNames h.boxIn t)
    | _, _, h, _, _, .diatm x hx t =>
        .diatm (x.readNames ν k) (hx.imp fun _ hX => h x _ hX) (Term.readNames (h.diaIn x) t)
end

def Rel.readNames {σ : Signature} {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) : {n : ℕ} → Rel σ Γ₁ n → Rel σ Γ₂ n
  | _, .R r => .R r
  | _, .eval ρ t => .eval (Rel.readNames h ρ) (Term.readNames h t)

/-- Identity witnesses map along: they are read off the context. -/
theorem Ctx.ReadsNames.witT {ν : VarSymb → Option VarSymb} {k : ℕ} {Γ₁ Γ₂ : Ctx}
    (h : Ctx.ReadsNames ν k Γ₁ Γ₂) {y : VarSymb} {X : VarType} (hy : Γ₁.witT y = some X) :
    Γ₂.witT (y.readNames ν k) = some X := by
  obtain ⟨hT, hO, hr⟩ := Ctx.witT_spec hy
  exact Ctx.witT_of hT hO (h y _ hr)

/-- ⭐**A formula read at the names**, the names avoiding the slots. -/
def WFF.readNames {σ : Signature} {ν : VarSymb → Option VarSymb}
    (hν : ∀ y n, ν y = some n → ∀ e, n.rt ≠ .bnd e) : {k : ℕ} → {Γ₁ Γ₂ : Ctx} → {d : ℕ} →
    Ctx.ReadsNames ν k Γ₁ Γ₂ → Γ₁.SlotsFrom d → WFF σ Γ₁ d → WFF σ Γ₂ d
  | _, _, _, _, h, _, .atom ρ => .atom (Rel.readNames h ρ)
  | _, _, _, _, h, _, .eq t s => .eq (Term.readNames h t) (Term.readNames h s)
  | _, _, _, _, _, _, .top => .top
  | _, _, _, _, _, _, .bot => .bot
  | _, _, _, _, h, hs, .and φ ψ => .and (WFF.readNames hν h hs φ) (WFF.readNames hν h hs ψ)
  | _, _, _, _, h, hs, .or φ ψ => .or (WFF.readNames hν h hs φ) (WFF.readNames hν h hs ψ)
  | _, _, _, _, h, hs, .imp φ ψ => .imp (WFF.readNames hν h hs φ) (WFF.readNames hν h hs ψ)
  | _, _, _, d, h, hs, .all T φ =>
      .all T (WFF.readNames hν (h.insert (hs.rootFresh le_rfl) (fun y n hy => hν y n hy d) T)
        (hs.insert T) φ)
  | _, _, _, d, h, hs, .ex T φ =>
      .ex T (WFF.readNames hν (h.insert (hs.rootFresh le_rfl) (fun y n hy => hν y n hy d) T)
        (hs.insert T) φ)
  | _, _, _, _, h, hs, .box φ => .box (WFF.readNames hν h.boxIn hs.boxIn φ)
  | k, _, _, _, h, hs, .dia x hx φ =>
      .dia (x.readNames ν k) (hx.imp fun _ hX => h x _ hX)
        (WFF.readNames hν (h.diaIn x) (hs.diaIn x) φ)
  | _, _, _, _, h, _, .here hT s t hO => .here hT (Term.readNames h s) (Term.readNames h t)
  | _, _, _, _, h, _, .back hB L s t => .back hB L (Term.readNames h s) (Term.readNames h t)
  | _, _, _, d, h, hs, .retS hB S t Φ =>
      .retS hB S (Term.readNames h t)
        (WFF.readNames hν (h.boxIn.insert (hs.boxIn.rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) (hs.boxIn.insert _) Φ)
  | k, _, _, d, h, hs, .retxS hB y hy S t Φ =>
      .retxS hB (y.readNames ν k) (hy.imp fun _ hY => h y _ hY) S (Term.readNames h t)
        (WFF.readNames hν ((h.diaIn y).insert ((hs.diaIn y).rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) ((hs.diaIn y).insert _) Φ)
  | _, _, _, d, h, hs, .link hV hF t Φ =>
      .link hV hF (Term.readNames h t)
        (WFF.readNames hν (h.boxIn.insert (hs.boxIn.rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) (hs.boxIn.insert _) Φ)
  | k, _, _, d, h, hs, .linkx hV hF y hy t Φ =>
      .linkx hV hF (y.readNames ν k) (hy.imp fun _ hY => h y _ hY) (Term.readNames h t)
        (WFF.readNames hν ((h.diaIn y).insert ((hs.diaIn y).rootFresh le_rfl)
          (fun y n hy => hν y n hy d) _) ((hs.diaIn y).insert _) Φ)
  | k, _, _, _, h, hs, .optx hO .arrow y hy φ =>
      .optx hO .arrow (y.readNamesW ν k) (hy.imp fun _ hX => h.wit y _ hX)
        (WFF.readNames hν (hy.elim fun _ hX => h.optIn hX) (hs.optIn y) φ)
  | k, _, _, _, h, hs, .optx hO .ident y hy φ =>
      .optx hO .ident (y.readNames ν k) (hy.imp fun _ hX => h.witT hX)
        (WFF.readNames hν (hy.elim fun _ hX => h.optInT hX) (hs.optInT y) φ)

end V12M
