import QML.DiaIdxProto

/-!
# Prototype, phase 3 — semantics: extents attached to variables

A possible object of plain type `◇A` at `w` is a pair of
* an **extent** — a set `D` of accessible worlds (plus the inner type's extents there), and
* a **content** — at each `w' ∈ D`, exactly one object of type `A` (a total section over `D`).

Every type's meaning splits this way (`Ext` / `Val`, packed as `Obj`).  Extents are DATA ATTACHED TO
THE INTERPRETATION OF VARIABLES: an environment gives each variable an object, extent included.
A term's extent is read directly off the variables it uses — `◇_x t` takes `x`'s world set —
never off its type; that typing determines it is a theorem (`interp_ext_eq`).

Simplification: a FULL model (every extent/content pair is a possible object), so the evaluation
map is the identity.  The questions tested here — extents from variables, equality meaning
equality, substitution as an equation — do not depend on fullness.
-/

namespace DiaIdx

structure Frame where
  W : Type
  R : W → W → Prop
  D : W → Type

abbrev Frame.Acc (F : Frame) (w : F.W) : Type := {w' : F.W // F.R w w'}

/-- Extents: where things are realized. -/
def Frame.Ext (F : Frame) : Ty → F.W → Type
  | .base, _ => PUnit
  | .unit, _ => PUnit
  | .prod A B, w => F.Ext A w × F.Ext B w
  | .box A, w => (w' : F.Acc w) → F.Ext A w'.1
  | .dia A, w => Σ (D : Set (F.Acc w)), ((w' : D) → F.Ext A w'.1.1)

/-- Contents over an extent: exactly one object at each world the extent picks out. -/
def Frame.Val (F : Frame) : (T : Ty) → (w : F.W) → F.Ext T w → Type
  | .base, w, _ => F.D w
  | .unit, _, _ => PUnit
  | .prod A B, w, e => F.Val A w e.1 × F.Val B w e.2
  | .box A, w, e => (w' : F.Acc w) → F.Val A w'.1 (e w')
  | .dia A, w, e => (w' : e.1) → F.Val A w'.1.1 (e.2 w')

/-- An object: extent and content. -/
abbrev Frame.Obj (F : Frame) (T : Ty) (w : F.W) : Type := Σ e : F.Ext T w, F.Val T w e

/-- An environment gives every declared variable an object of its PLAIN type. -/
abbrev Frame.Env (F : Frame) (Γ : Ctx) (w : F.W) : Type := ∀ j T, Γ j = some T → F.Obj T w

namespace Frame

variable {F : Frame}

/-- Into a `□`: each box-typed variable read at the accessible world. -/
def Env.boxPush {Γ : Ctx} {w : F.W} (env : F.Env Γ w) (w' : F.Acc w) :
    F.Env (unboxCtx Γ) w'.1 :=
  fun j T h =>
    ⟨(env j (.box T) (unboxSlot_eq_some.mp h)).1 w', (env j (.box T) (unboxSlot_eq_some.mp h)).2 w'⟩

/-- Into a `◇_x`, at a world `w'` of the witness object `o`'s extent: the box shadow read at `w'`,
    and the witness revealed as its one object there.  The witness object is passed explicitly. -/
def Env.diaPush {Γ : Ctx} {w : F.W} (env : F.Env Γ w) (x : Nat) (X : Ty) (o : F.Obj (.dia X) w)
    (w' : o.1.1) : F.Env (diaCtx Γ x X) w'.1.1 :=
  fun j T h =>
    if hjx : j = x then
      have hXT : X = T := by
        subst hjx
        simpa [diaCtx] using h
      hXT ▸ (⟨o.1.2 w', o.2 w'⟩ : F.Obj X w'.1.1)
    else
      env.boxPush w'.1 j T (by rw [diaCtx, Function.update_of_ne hjx] at h; exact h)

/-- Under `pelim`: the two components of the product object `o`. -/
def Env.pelimPush {Γ : Ctx} {w : F.W} (env : F.Env Γ w) (A B : Ty) (o : F.Obj (.prod A B) w) :
    F.Env (cons2 (some B) (some A) Γ) w
  | 0, _, h => (Option.some.inj h) ▸ (⟨o.1.2, o.2.2⟩ : F.Obj B w)
  | 1, _, h => (Option.some.inj h) ▸ (⟨o.1.1, o.2.1⟩ : F.Obj A w)
  | j + 2, T, h => env j T h

/-- A `◇`-object built from a witness object and, at each world of its extent, an inner object:
    the extent is the WITNESS's world set. -/
def diaBuild {X A : Ty} {w : F.W} (o : F.Obj (.dia X) w) (k : (w' : o.1.1) → F.Obj A w'.1.1) :
    F.Obj (.dia A) w :=
  ⟨⟨o.1.1, fun w' => (k w').1⟩, fun w' => (k w').2⟩

end Frame

/-! ## Typing inversions used by the interpretation -/

section Inversions

variable {Γ : Ctx}

theorem wt_var {k : Nat} {T : Ty} (h : ∃ S : ITy T, HasTy Γ (.var k) T S) : Γ k = some T := by
  obtain ⟨S, hS⟩ := h; cases hS; assumption

theorem wt_pair {a b : Tm} {A B : Ty} (h : ∃ S : ITy (.prod A B), HasTy Γ (.pair a b) (.prod A B) S) :
    (∃ S : ITy A, HasTy Γ a A S) ∧ (∃ S : ITy B, HasTy Γ b B S) := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | pair ha hb => exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩

theorem wt_box {t : Tm} {A : Ty} (h : ∃ S : ITy (.box A), HasTy Γ (.boxtm t) (.box A) S) :
    ∃ S : ITy A, HasTy (unboxCtx Γ) t A S := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | boxtm ht => exact ⟨_, ht⟩

theorem wt_dia_ctx {x : Nat} {X : Ty} {t : Tm} {A : Ty}
    (h : ∃ S : ITy (.dia A), HasTy Γ (.diatm x X t) (.dia A) S) : Γ x = some (.dia X) := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | diatm hx _ => exact hx

theorem wt_dia {x : Nat} {X : Ty} {t : Tm} {A : Ty}
    (h : ∃ S : ITy (.dia A), HasTy Γ (.diatm x X t) (.dia A) S) :
    ∃ S : ITy A, HasTy (diaCtx Γ x X) t A S := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | diatm _ ht => exact ⟨_, ht⟩

theorem wt_pelim_ctx {p : Nat} {A B : Ty} {t : Tm} {T : Ty}
    (h : ∃ S : ITy T, HasTy Γ (.pelim p A B t) T S) : Γ p = some (.prod A B) := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | pelim hp _ => exact hp

theorem wt_pelim {p : Nat} {A B : Ty} {t : Tm} {T : Ty}
    (h : ∃ S : ITy T, HasTy Γ (.pelim p A B t) T S) :
    ∃ S : ITy T, HasTy (cons2 (some B) (some A) Γ) t T S := by
  obtain ⟨S, hS⟩ := h
  cases hS with
  | pelim _ ht => exact ⟨_, ht⟩

theorem wf_prim {a b : Tm} (h : WfWff Γ (.prim a b)) :
    (∃ S : ITy .base, HasTy Γ a .base S) ∧ (∃ S : ITy .base, HasTy Γ b .base S) := by
  cases h with
  | prim ha hb => exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩

theorem wf_conj {φ ψ : Wff} (h : WfWff Γ (.conj φ ψ)) : WfWff Γ φ ∧ WfWff Γ ψ := by
  cases h with
  | conj h1 h2 => exact ⟨h1, h2⟩

theorem wf_imp {φ ψ : Wff} (h : WfWff Γ (.imp φ ψ)) : WfWff Γ φ ∧ WfWff Γ ψ := by
  cases h with
  | imp h1 h2 => exact ⟨h1, h2⟩

theorem wf_box {φ : Wff} (h : WfWff Γ (.box φ)) : WfWff (unboxCtx Γ) φ := by
  cases h with
  | box h1 => exact h1

theorem wf_boxx_ctx {x : Nat} {X : Ty} {φ : Wff} (h : WfWff Γ (.boxx x X φ)) :
    Γ x = some (.dia X) := by
  cases h with
  | boxx hx _ => exact hx

theorem wf_boxx {x : Nat} {X : Ty} {φ : Wff} (h : WfWff Γ (.boxx x X φ)) :
    WfWff (diaCtx Γ x X) φ := by
  cases h with
  | boxx _ h1 => exact h1

end Inversions

/-! ## Interpretation -/

namespace Frame

variable (F : Frame)

/-- The interpretation of a well-typed term at its plain type.  A `◇_x t`'s extent is `x`'s own
    world set, read from the environment. -/
def interp : (t : Tm) → {Γ : Ctx} → {w : F.W} → F.Env Γ w → (T : Ty) →
    (∃ S : ITy T, HasTy Γ t T S) → F.Obj T w
  | .var k, _, _, env, T, h => env k T (wt_var h)
  | .unit, _, _, _, .unit, _ => ⟨PUnit.unit, PUnit.unit⟩
  | .pair a b, _, _, env, .prod A B, h =>
      ⟨((interp a env A (wt_pair h).1).1, (interp b env B (wt_pair h).2).1),
       ((interp a env A (wt_pair h).1).2, (interp b env B (wt_pair h).2).2)⟩
  | .boxtm t, _, _, env, .box A, h =>
      ⟨fun w' => (interp t (env.boxPush w') A (wt_box h)).1,
       fun w' => (interp t (env.boxPush w') A (wt_box h)).2⟩
  | .diatm x X t, _, _, env, .dia A, h =>
      diaBuild (env x (.dia X) (wt_dia_ctx h))
        (fun w' => interp t (env.diaPush x X (env x (.dia X) (wt_dia_ctx h)) w') A (wt_dia h))
  | .pelim p A B t, _, _, env, T, h =>
      interp t (env.pelimPush A B (env p (.prod A B) (wt_pelim_ctx h))) T (wt_pelim h)
  -- ill-typed combinations
  | .unit, _, _, _, .base, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .unit, _, _, _, .prod _ _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .unit, _, _, _, .box _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .unit, _, _, _, .dia _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .pair _ _, _, _, _, .base, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .pair _ _, _, _, _, .unit, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .pair _ _, _, _, _, .box _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .pair _ _, _, _, _, .dia _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .boxtm _, _, _, _, .base, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .boxtm _, _, _, _, .unit, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .boxtm _, _, _, _, .prod _ _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .boxtm _, _, _, _, .dia _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .diatm _ _ _, _, _, _, .base, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .diatm _ _ _, _, _, _, .unit, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .diatm _ _ _, _, _, _, .prod _ _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)
  | .diatm _ _ _, _, _, _, .box _, h => False.elim (by obtain ⟨_, hS⟩ := h; cases hS)

/-- Satisfaction.  `□_x φ` ranges over the worlds of `x`'s extent. -/
def sat : (φ : Wff) → {Γ : Ctx} → {w : F.W} → F.Env Γ w → WfWff Γ φ → Prop
  | .prim a b, _, w, env, h =>
      ((F.interp a env .base (wf_prim h).1).2 : F.D w) = (F.interp b env .base (wf_prim h).2).2
  | .top, _, _, _, _ => True
  | .conj φ ψ, _, _, env, h => sat φ env (wf_conj h).1 ∧ sat ψ env (wf_conj h).2
  | .imp φ ψ, _, _, env, h => sat φ env (wf_imp h).1 → sat ψ env (wf_imp h).2
  | .box φ, _, w, env, h => ∀ w' : F.Acc w, sat φ (env.boxPush w') (wf_box h)
  | .boxx x X φ, _, _, env, h =>
      ∀ w' : (env x (.dia X) (wf_boxx_ctx h)).1.1,
        sat φ (env.diaPush x X (env x (.dia X) (wf_boxx_ctx h)) w') (wf_boxx h)

end Frame

/-! ## Equality of objects, by type -/

namespace Frame

variable {F : Frame}

theorem obj_base_eq {w : F.W} {o₁ o₂ : F.Obj .base w} : o₁ = o₂ ↔ (o₁.2 : F.D w) = o₂.2 := by
  constructor
  · rintro rfl; rfl
  · obtain ⟨e₁, v₁⟩ := o₁
    obtain ⟨e₂, v₂⟩ := o₂
    intro h
    cases e₁; cases e₂
    simp only at h
    subst h
    rfl

theorem obj_unit_eq {w : F.W} (o₁ o₂ : F.Obj .unit w) : o₁ = o₂ := by
  obtain ⟨e₁, v₁⟩ := o₁
  obtain ⟨e₂, v₂⟩ := o₂
  cases e₁; cases e₂; cases v₁; cases v₂; rfl

theorem obj_pair_eq {A B : Ty} {w : F.W} (a₁ a₂ : F.Obj A w) (b₁ b₂ : F.Obj B w) :
    (⟨(a₁.1, b₁.1), (a₁.2, b₁.2)⟩ : F.Obj (.prod A B) w) = ⟨(a₂.1, b₂.1), (a₂.2, b₂.2)⟩
      ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h
    exact ⟨congrArg (fun o : F.Obj (.prod A B) w => (⟨o.1.1, o.2.1⟩ : F.Obj A w)) h,
      congrArg (fun o : F.Obj (.prod A B) w => (⟨o.1.2, o.2.2⟩ : F.Obj B w)) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem obj_box_eq {A : Ty} {w : F.W} (f g : (w' : F.Acc w) → F.Obj A w'.1) :
    (⟨fun w' => (f w').1, fun w' => (f w').2⟩ : F.Obj (.box A) w)
        = ⟨fun w' => (g w').1, fun w' => (g w').2⟩ ↔ f = g := by
  constructor
  · intro h
    exact congrArg (fun (o : F.Obj (.box A) w) (w' : F.Acc w) => (⟨o.1 w', o.2 w'⟩ : F.Obj A w'.1)) h
  · rintro rfl; rfl

/-- Two `◇`-objects over the SAME witness object are equal iff they agree at every world of its
    extent — `□_x(t ≐ s)`, exactly. -/
theorem diaBuild_eq {X A : Ty} {w : F.W} (o : F.Obj (.dia X) w)
    (k₁ k₂ : (w' : o.1.1) → F.Obj A w'.1.1) : diaBuild o k₁ = diaBuild o k₂ ↔ k₁ = k₂ := by
  constructor
  · intro h
    have h' := congrArg (fun p : F.Obj (.dia A) w =>
      (⟨p.1.1, fun w' => (⟨p.1.2 w', p.2 w'⟩ : F.Obj A w'.1.1)⟩ :
        Σ D : Set (F.Acc w), ((w' : D) → F.Obj A w'.1.1))) h
    exact eq_of_heq (Sigma.mk.inj h').2
  · rintro rfl; rfl

end Frame

/-! ## ⭐Typing determines the extent

Option 2: a term's extent is computed from the variables it uses; this theorem is the guarantee
that two terms of the same elaborated type get the same one. -/

namespace Frame

variable {F : Frame}

theorem interp_ext_eq {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S) :
    ∀ {w : F.W} (env : F.Env Γ w) {b : Tm} (hb : HasTy Γ b T S), a.PelimFree → b.PelimFree →
      (F.interp a env T ⟨S, ha⟩).1 = (F.interp b env T ⟨S, hb⟩).1 := by
  induction ha with
  | var => intro _ _ _ _ _ _; rfl
  | unit => intro _ _ _ _ _ _; rfl
  | pair h₁ h₂ iha ihb =>
      intro w env b hb hpa hpb
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      simp only [Frame.interp]
      rw [iha env hc hpa.1 hcpf, ihb env hd hpa.2 hdpf]
  | boxtm _ ih =>
      intro w env b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [Frame.interp]
      funext w'
      exact ih (env.boxPush w') hs hpa hspf
  | @diatm Γ x X t A S hx _ ih =>
      intro w env b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [Frame.interp, Frame.diaBuild]
      congr 1
      funext w'
      exact ih _ hs hpa hspf
  | pelim => intro _ _ _ _ hpa _; exact hpa.elim

/-! ## ⭐The defined equality means equality of objects -/

theorem sat_eqf {Γ : Ctx} {a : Tm} {T : Ty} {S : ITy T} (ha : HasTy Γ a T S) :
    ∀ {w : F.W} (env : F.Env Γ w) {b : Tm} (hb : HasTy Γ b T S) (hpa : a.PelimFree)
      (hpb : b.PelimFree),
      F.sat (eqf T a b) env (eqf_wf ha hb hpa hpb) ↔ F.interp a env T ⟨S, ha⟩ = F.interp b env T ⟨S, hb⟩ := by
  induction ha with
  | var =>
      intro w env b hb hpa hpb
      simp only [eqf, Frame.sat]
      exact obj_base_eq.symm
  | unit =>
      intro w env b hb hpa hpb
      simp only [eqf, Frame.sat, true_iff]
      exact obj_unit_eq _ _
  | pair h₁ h₂ iha ihb =>
      intro w env b hb hpa hpb
      obtain ⟨c, d, rfl, hc, hd, hcpf, hdpf⟩ := pair_same_inner hb hpb
      simp only [eqf, Frame.sat, Frame.interp]
      rw [obj_pair_eq, iha env hc hpa.1 hcpf, ihb env hd hpa.2 hdpf]
  | boxtm _ ih =>
      intro w env b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := box_same_inner hb hpb
      simp only [eqf, Frame.sat, Frame.interp]
      rw [obj_box_eq, funext_iff]
      exact forall_congr' fun w' => ih (env.boxPush w') hs hpa hspf
  | @diatm Γ x X t A S hx _ ih =>
      intro w env b hb hpa hpb
      obtain ⟨s, rfl, hs, hspf⟩ := dia_same_inner hx hb hpb
      simp only [eqf, Frame.sat, Frame.interp]
      rw [diaBuild_eq, funext_iff]
      exact forall_congr' fun w' => ih _ hs hpa hspf
  | pelim => intro _ _ _ _ hpa _; exact hpa.elim

end Frame

/-! ## Substitution as an equation

`interp (t.psubst σ) env' = interp t (substEnv σ env')`: the substituted variables are given the
objects the substitutes denote — for `z := ◇_x u` that object's extent is `x`'s world set, so
nothing is pulled back and there is nothing to compare across witnesses. -/

theorem Sub.cases_eq (e : Sub) : (∃ i, e = .ren i) ∨ ∃ s T S, e = .tm s T S := by
  cases e with
  | ren i => exact .inl ⟨i, rfl⟩
  | tm s T S => exact .inr ⟨s, T, S, rfl⟩

theorem SubOk.lift2 {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) (A B : Ty) :
    SubOk (liftSub2 σ) (cons2 (some B) (some A) Γ) (cons2 (some B) (some A) Δ) := by
  intro j T' hj
  rcases j with _ | _ | j
  · exact hj
  · exact hj
  · have hokj := hσ _ _ hj
    show (σ j).shift2.Ok (cons2 (some B) (some A) Δ) T'
    rcases Sub.cases_eq (σ j) with ⟨k, hsj⟩ | ⟨s, T'', S', hsj⟩
    · rw [hsj] at hokj ⊢; exact hokj
    · rw [hsj] at hokj ⊢
      simp only [Sub.Ok] at hokj
      obtain ⟨he, hs, hpf⟩ := hokj
      simp only [Sub.shift2, Sub.Ok]
      exact ⟨he, hs.rename (fun _ _ hk => hk), hpf.rename _⟩

theorem SubOk.pairSub' {σ : Nat → Sub} {Γ Δ : Ctx} (hσ : SubOk σ Γ Δ) {A B : Ty} {a b : Tm}
    {SA : ITy A} {SB : ITy B} (ha : HasTy Δ a A SA) (hb : HasTy Δ b B SB) (hapf : a.PelimFree)
    (hbpf : b.PelimFree) : SubOk (pairSub a A SA b B SB σ) (cons2 (some B) (some A) Γ) Δ := by
  intro j T'' hj
  rcases j with _ | _ | j
  · simp only [cons2, Option.some.injEq] at hj; subst hj; exact ⟨rfl, hb, hbpf⟩
  · simp only [cons2, Option.some.injEq] at hj; subst hj; exact ⟨rfl, ha, hapf⟩
  · exact hσ _ _ hj

theorem CtxLe.dia {Γ Δ : Ctx} (h : CtxLe Γ Δ) (x : Nat) (X : Ty) :
    CtxLe (diaCtx Γ x X) (diaCtx Δ x X) := by
  intro j T hj
  by_cases hjx : j = x
  · subst hjx; simpa [diaCtx] using hj
  · rw [diaCtx, Function.update_of_ne hjx] at hj ⊢
    exact h.unbox _ _ hj

theorem CtxLe.cons2 {Γ Δ : Ctx} (h : CtxLe Γ Δ) (B A : Option Ty) :
    CtxLe (cons2 B A Γ) (cons2 B A Δ) := by
  intro j T hj
  rcases j with _ | _ | j
  · exact hj
  · exact hj
  · exact h _ _ hj

namespace Frame

variable {F : Frame}

theorem interp_tm_eq {Γ : Ctx} {w : F.W} (env : F.Env Γ w) {t₁ t₂ : Tm} (h : t₁ = t₂) (T : Ty)
    (p₁ : ∃ S : ITy T, HasTy Γ t₁ T S) (p₂ : ∃ S : ITy T, HasTy Γ t₂ T S) :
    F.interp t₁ env T p₁ = F.interp t₂ env T p₂ := by
  subst h; rfl

theorem interp_env_eq {Γ : Ctx} {w : F.W} {env₁ env₂ : F.Env Γ w} (h : env₁ = env₂) (t : Tm)
    (T : Ty) (p : ∃ S : ITy T, HasTy Γ t T S) : F.interp t env₁ T p = F.interp t env₂ T p := by
  subst h; rfl

/-- Changing the witness object of a `◇`-build whose inner part depends on it. -/
theorem diaBuild_congr_left {X A : Ty} {w : F.W}
    (G : (o : F.Obj (.dia X) w) → (w' : o.1.1) → F.Obj A w'.1.1) {o₁ o₂ : F.Obj (.dia X) w}
    (ho : o₁ = o₂) : diaBuild o₁ (G o₁) = diaBuild o₂ (G o₂) := by
  subst ho; rfl

theorem diaBuild_diaBuild {X Y A : Ty} {w : F.W} (o : F.Obj (.dia Y) w)
    (ku : (w' : o.1.1) → F.Obj X w'.1.1) (k : (w' : o.1.1) → F.Obj A w'.1.1) :
    diaBuild (diaBuild o ku) k = diaBuild o k := rfl

/-! ### Interpretation respects weakening and renaming -/

theorem interp_agree {Γ₁ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (ht : HasTy Γ₁ t T S) :
    ∀ {Γ₂ : Ctx} {w : F.W} (hle : CtxLe Γ₁ Γ₂) (env₁ : F.Env Γ₁ w) (env₂ : F.Env Γ₂ w),
      (∀ j T' (h : Γ₁ j = some T'), env₁ j T' h = env₂ j T' (hle j T' h)) →
      F.interp t env₁ T ⟨S, ht⟩ = F.interp t env₂ T ⟨S, ht.mono hle⟩ := by
  induction ht with
  | var hk => intro Γ₂ w hle env₁ env₂ hag; exact hag _ _ _
  | unit => intro _ _ _ _ _ _; rfl
  | pair _ _ iha ihb =>
      intro Γ₂ w hle env₁ env₂ hag
      simp only [Frame.interp]
      rw [iha hle env₁ env₂ hag, ihb hle env₁ env₂ hag]
  | @boxtm Γ t A S _ ih =>
      intro Γ₂ w hle env₁ env₂ hag
      simp only [Frame.interp]
      rw [obj_box_eq]
      funext w'
      refine ih hle.unbox (env₁.boxPush w') (env₂.boxPush w') ?_
      intro j T' h
      exact congrArg (fun o : F.Obj (.box T') w => (⟨o.1 w', o.2 w'⟩ : F.Obj T' w'.1))
        (hag j (.box T') _)
  | @diatm Γ x X t A S hx ht ih =>
      intro Γ₂ w hle env₁ env₂ hag
      simp only [Frame.interp]
      have ho := hag x (.dia X) hx
      refine Eq.trans ((diaBuild_eq _ _ _).mpr (funext fun w' => ?_))
        (diaBuild_congr_left (fun o w' => F.interp t (env₂.diaPush x X o w') A
          ⟨S, ht.mono (hle.dia x X)⟩) ho)
      refine ih (hle.dia x X) _ _ ?_
      intro j T' h
      simp only [Frame.Env.diaPush]
      split_ifs with hjx
      · rfl
      · exact congrArg (fun o : F.Obj (.box T') w => (⟨o.1 w'.1, o.2 w'.1⟩ : F.Obj T' w'.1.1))
          (hag j (.box T') _)
  | @pelim Γ p A B t T S hp ht ih =>
      intro Γ₂ w hle env₁ env₂ hag
      simp only [Frame.interp]
      have ho := hag p (.prod A B) hp
      refine Eq.trans ?_ (congrArg (fun o => F.interp t (env₂.pelimPush A B o) T
        ⟨S, ht.mono (hle.cons2 _ _)⟩) ho)
      refine ih (hle.cons2 _ _) _ _ ?_
      intro j T' h
      rcases j with _ | _ | j
      · rfl
      · rfl
      · exact hag j T' h

theorem interp_rename {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (ht : HasTy Γ t T S) :
    ∀ {Δ : Ctx} {w : F.W} {ρ : Nat → Nat} (hρ : RenOk ρ Γ Δ) (envΓ : F.Env Γ w)
      (envΔ : F.Env Δ w),
      (∀ j T' (h : Γ j = some T'), envΔ (ρ j) T' (hρ j T' h) = envΓ j T' h) →
      F.interp (t.rename ρ) envΔ T ⟨_, ht.rename hρ⟩ = F.interp t envΓ T ⟨S, ht⟩ := by
  induction ht with
  | var hk => intro Δ w ρ hρ envΓ envΔ hag; exact hag _ _ _
  | unit => intro _ _ _ _ _ _ _; rfl
  | pair _ _ iha ihb =>
      intro Δ w ρ hρ envΓ envΔ hag
      dsimp only [Tm.rename]
      simp only [Frame.interp]
      rw [iha hρ envΓ envΔ hag, ihb hρ envΓ envΔ hag]
  | @boxtm Γ t A S _ ih =>
      intro Δ w ρ hρ envΓ envΔ hag
      dsimp only [Tm.rename]
      simp only [Frame.interp]
      rw [obj_box_eq]
      funext w'
      have hρ' : RenOk ρ (unboxCtx Γ) (unboxCtx Δ) := fun j T h =>
        unboxSlot_eq_some.mpr (hρ _ _ (unboxSlot_eq_some.mp h))
      refine ih hρ' (envΓ.boxPush w') (envΔ.boxPush w') ?_
      intro j T' h
      exact congrArg (fun o : F.Obj (.box T') w => (⟨o.1 w', o.2 w'⟩ : F.Obj T' w'.1))
        (hag j (.box T') _)
  | @diatm Γ x X t A S hx ht ih =>
      intro Δ w ρ hρ envΓ envΔ hag
      dsimp only [Tm.rename]
      simp only [Frame.interp]
      have hxΔ := hρ _ _ hx
      have ho := hag x (.dia X) hx
      have hρ' : RenOk ρ (diaCtx Γ x X) (diaCtx Δ (ρ x) X) := by
        intro j T h
        by_cases hjx : j = x
        · subst hjx; simpa [diaCtx] using h
        · rw [diaCtx, Function.update_of_ne hjx] at h
          have hjΔ := hρ _ _ (unboxSlot_eq_some.mp h)
          have hne : ρ j ≠ ρ x := fun he => by rw [he, hxΔ] at hjΔ; simp at hjΔ
          rw [diaCtx, Function.update_of_ne hne]
          exact unboxSlot_eq_some.mpr hjΔ
      refine Eq.trans (diaBuild_congr_left (fun o w' => F.interp (t.rename ρ)
          (envΔ.diaPush (ρ x) X o w') A ⟨_, ht.rename hρ'⟩) ho)
        ((diaBuild_eq _ _ _).mpr (funext fun w' => ?_))
      refine ih hρ' _ _ ?_
      intro j T' h
      by_cases hjx : j = x
      · subst hjx
        have hXT : X = T' := by simpa [diaCtx] using h
        subst hXT
        simp only [Frame.Env.diaPush, dif_pos]
      · have hjbox : Γ j = some (.box T') := by
          rw [diaCtx, Function.update_of_ne hjx] at h
          exact unboxSlot_eq_some.mp h
        have hjΔ := hρ _ _ hjbox
        have hne : ρ j ≠ ρ x := fun he => by rw [he, hxΔ] at hjΔ; simp at hjΔ
        simp only [Frame.Env.diaPush, dif_neg hne, dif_neg hjx]
        exact congrArg (fun o : F.Obj (.box T') w => (⟨o.1 w'.1, o.2 w'.1⟩ : F.Obj T' w'.1.1))
          (hag j (.box T') hjbox)
  | @pelim Γ p A B t T S hp ht ih =>
      intro Δ w ρ hρ envΓ envΔ hag
      dsimp only [Tm.rename]
      simp only [Frame.interp]
      have ho := hag p (.prod A B) hp
      have hρ' : RenOk (lift2 ρ) (cons2 (some B) (some A) Γ) (cons2 (some B) (some A) Δ) := by
        intro j T h
        rcases j with _ | _ | j
        · exact h
        · exact h
        · exact hρ _ _ h
      refine Eq.trans (congrArg (fun o => F.interp (t.rename (lift2 ρ)) (envΔ.pelimPush A B o) T
        ⟨_, ht.rename hρ'⟩) ho) ?_
      refine ih hρ' _ _ ?_
      intro j T' h
      rcases j with _ | _ | j
      · rfl
      · rfl
      · exact hag j T' h

/-! ### The substituted environment -/

/-- The object an entry denotes, at the slot's plain type. -/
def subEntry {Δ : Ctx} {w : F.W} (env' : F.Env Δ w) : (e : Sub) → (T : Ty) → e.Ok Δ T → F.Obj T w
  | .ren i, T, h => env' i T h
  | .tm s T' S', _, h => h.1 ▸ F.interp s env' T' ⟨S', h.2.1⟩

def substEnv {Γ Δ : Ctx} {w : F.W} (σ : Nat → Sub) (hσ : SubOk σ Γ Δ) (env' : F.Env Δ w) :
    F.Env Γ w :=
  fun j T h => subEntry env' (σ j) T (hσ j T h)

theorem subEntry_congr {Δ : Ctx} {w : F.W} (env' : F.Env Δ w) {T : Ty} (e₁ e₂ : Sub)
    (he : e₁ = e₂) (p₁ : e₁.Ok Δ T) (p₂ : e₂.Ok Δ T) :
    subEntry env' e₁ T p₁ = subEntry env' e₂ T p₂ := by
  subst he; rfl

theorem subEntry_ren {Δ : Ctx} {w : F.W} (env' : F.Env Δ w) {T : Ty} {i : Nat} (e : Sub)
    (p : e.Ok Δ T) (he : e = .ren i) : subEntry env' e T p = env' i T (by subst he; exact p) := by
  subst he; rfl

theorem subEntry_tm {Δ : Ctx} {w : F.W} (env' : F.Env Δ w) {T : Ty} {s : Tm} {S' : ITy T}
    (e : Sub) (p : e.Ok Δ T) (he : e = .tm s T S') :
    subEntry env' e T p = F.interp s env' T ⟨S', by subst he; exact p.2.1⟩ := by
  subst he; rfl

theorem substEnv_unbox {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ)
    (env' : F.Env Δ w) (w' : F.Acc w) :
    substEnv (unboxSub σ) hσ.unbox (env'.boxPush w') = (substEnv σ hσ env').boxPush w' := by
  funext j T h
  have hjbox : Γ j = some (.box T) := unboxSlot_eq_some.mp h
  have hokj := hσ j (.box T) hjbox
  show subEntry (env'.boxPush w') ((unboxSub σ) j) T _
    = ⟨(subEntry env' (σ j) (.box T) _).1 w', (subEntry env' (σ j) (.box T) _).2 w'⟩
  rcases Sub.cases_eq (σ j) with ⟨k, hsj⟩ | ⟨s, T', S', hsj⟩
  · have hu : (unboxSub σ) j = .ren k := by simp [unboxSub, hsj, Sub.unbox]
    rw [subEntry_ren _ _ _ hu, subEntry_ren _ _ _ hsj]
    rfl
  · rw [hsj] at hokj
    simp only [Sub.Ok] at hokj
    obtain ⟨rfl, hs, hpf⟩ := hokj
    obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf
    have hu' : (unboxSub σ) j = .tm u T ((U.mapIdx boxOut).mapIdx Idx.strip) := by
      simp [unboxSub, hsj, Sub.unbox]
    rw [subEntry_tm _ _ _ hu', subEntry_tm _ _ _ hsj]
    simp only [Frame.interp]

/-- A box slot, seen inside a `◇_y` of the target, gives the same object as through a plain
    `□`: the slot is not the witness, so the push reads it through the box shadow. -/
theorem subEntry_unbox_diaPush {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ)
    {y : Nat} {Y : Ty} (hy : Δ y = some (.dia Y)) (env' : F.Env Δ w)
    (o : F.Obj (.dia Y) w) (w' : o.1.1) {j : Nat} {T : Ty} (h' : unboxCtx Γ j = some T)
    (p : ((unboxSub σ) j).Ok (diaCtx Δ y Y) T) :
    subEntry (env'.diaPush y Y o w') ((unboxSub σ) j) T p
      = (substEnv σ hσ env').boxPush w'.1 j T h' := by
  have hjbox : Γ j = some (.box T) := unboxSlot_eq_some.mp h'
  have hokj := hσ j (.box T) hjbox
  have hleΔ : CtxLe (unboxCtx Δ) (diaCtx Δ y Y) := by
    intro k K hk
    have hky : k ≠ y := fun he => by rw [he] at hk; simp [unboxCtx, hy, unboxSlot] at hk
    rw [diaCtx, Function.update_of_ne hky]
    exact hk
  show _ = ⟨(subEntry env' (σ j) (.box T) _).1 w'.1, (subEntry env' (σ j) (.box T) _).2 w'.1⟩
  rcases Sub.cases_eq (σ j) with ⟨k, hsj⟩ | ⟨s, T', S', hsj⟩
  · have hk : Δ k = some (.box T) := by rw [hsj] at hokj; exact hokj
    have hky : k ≠ y := fun he => by rw [he, hy] at hk; simp at hk
    have hu : (unboxSub σ) j = .ren k := by simp [unboxSub, hsj, Sub.unbox]
    rw [subEntry_ren _ _ _ hu, subEntry_ren _ _ _ hsj]
    simp only [Frame.Env.diaPush, dif_neg hky]
    rfl
  · rw [hsj] at hokj
    simp only [Sub.Ok] at hokj
    obtain ⟨rfl, hs, hpf⟩ := hokj
    obtain ⟨u, U, rfl, rfl, hu, hupf⟩ := canon_box hs hpf
    have hu' : (unboxSub σ) j = .tm u T ((U.mapIdx boxOut).mapIdx Idx.strip) := by
      simp [unboxSub, hsj, Sub.unbox]
    rw [subEntry_tm _ _ _ hu', subEntry_tm _ _ _ hsj]
    simp only [Frame.interp]
    have hU : (U.mapIdx boxOut).mapIdx Idx.strip = U := by
      rw [ITy.mapIdx_mapIdx, strip_comp_boxOut, ITy.mapIdx_id]
    refine Eq.trans ?_ (interp_agree hu hleΔ (env'.boxPush w'.1) (env'.diaPush y Y o w') ?_).symm
    · rfl
    · intro k K hk
      have hky : k ≠ y := fun he => by rw [he] at hk; simp [unboxCtx, hy, unboxSlot] at hk
      simp only [Frame.Env.diaPush, dif_neg hky]

theorem substEnv_diaRen {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) {x : Nat}
    {X : Ty} {i : Nat} (hi : Δ i = some (.dia X)) (env' : F.Env Δ w)
    (w' : (env' i (.dia X) hi).1.1) :
    substEnv (Function.update (unboxSub σ) x (.ren i)) (hσ.diaRen hi)
        (env'.diaPush i X (env' i (.dia X) hi) w')
      = (substEnv σ hσ env').diaPush x X (env' i (.dia X) hi) w' := by
  funext j T h
  by_cases hjx : j = x
  · subst hjx
    have hXT : X = T := by simpa [diaCtx] using h
    subst hXT
    have p₂ : (Sub.ren i).Ok (diaCtx Δ i X) X := by simp [Sub.Ok, diaCtx]
    show subEntry _ (Function.update (unboxSub σ) j (.ren i) j) X _ = _
    rw [subEntry_congr _ _ _ (Function.update_self j (Sub.ren i) (unboxSub σ)) _ p₂]
    show (env'.diaPush i X (env' i (.dia X) hi) w') i X p₂ = _
    simp only [Frame.Env.diaPush, dif_pos]
  · have h' : unboxCtx Γ j = some T := by rw [diaCtx, Function.update_of_ne hjx] at h; exact h
    show subEntry _ (Function.update (unboxSub σ) x (.ren i) j) T _ = _
    rw [subEntry_congr _ _ _ (Function.update_of_ne hjx _ _) _ (boxSlot_diaCtx hσ hi hjx h).1]
    simp only [Frame.Env.diaPush, dif_neg hjx]
    exact subEntry_unbox_diaPush hσ hi env' _ w' h' _

theorem substEnv_diaTm {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) {x : Nat}
    {X : Ty} {y : Nat} {Y : Ty} {u : Tm} {U : ITy X} (hy : Δ y = some (.dia Y))
    (hu : HasTy (diaCtx Δ y Y) u X U) (hupf : u.PelimFree) (env' : F.Env Δ w)
    (w' : (env' y (.dia Y) hy).1.1) :
    substEnv (Function.update (unboxSub σ) x (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)))
        (hσ.diaTm hy hu hupf) (env'.diaPush y Y (env' y (.dia Y) hy) w')
      = (substEnv σ hσ env').diaPush x X
          (diaBuild (env' y (.dia Y) hy)
            (fun w'' => F.interp u (env'.diaPush y Y (env' y (.dia Y) hy) w'') X ⟨U, hu⟩)) w' := by
  funext j T h
  by_cases hjx : j = x
  · subst hjx
    have hXT : X = T := by simpa [diaCtx] using h
    subst hXT
    have hU : (U.mapIdx (diaOut y)).mapIdx Idx.strip = U := by
      rw [ITy.mapIdx_mapIdx, strip_comp_diaOut, ITy.mapIdx_id]
    have p₂ : (Sub.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)).Ok (diaCtx Δ y Y) X :=
      ⟨rfl, by rw [hU]; exact hu, hupf⟩
    show subEntry _ (Function.update _ j (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)) j) X _
      = _
    rw [subEntry_congr _ _ _ (Function.update_self _ _ _) _ p₂]
    simp only [Frame.Env.diaPush, dif_pos]
    rfl
  · have h' : unboxCtx Γ j = some T := by rw [diaCtx, Function.update_of_ne hjx] at h; exact h
    show subEntry _ (Function.update (unboxSub σ) x _ j) T _ = _
    rw [subEntry_congr _ _ _ (Function.update_of_ne hjx _ _) _ (boxSlot_diaCtx hσ hy hjx h).1]
    simp only [Frame.Env.diaPush, dif_neg hjx]
    exact subEntry_unbox_diaPush hσ hy env' _ w' h' _

theorem substEnv_lift2 {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) (A B : Ty)
    (env' : F.Env Δ w) (o : F.Obj (.prod A B) w) :
    substEnv (liftSub2 σ) (hσ.lift2 A B) (env'.pelimPush A B o)
      = (substEnv σ hσ env').pelimPush A B o := by
  funext j T h
  rcases j with _ | _ | j
  · rfl
  · rfl
  · have hokj := hσ j T h
    show subEntry (env'.pelimPush A B o) ((σ j).shift2) T _ = subEntry env' (σ j) T _
    rcases Sub.cases_eq (σ j) with ⟨k, hsj⟩ | ⟨s, T', S', hsj⟩
    · have hs2 : (σ j).shift2 = .ren (k + 2) := by rw [hsj]; rfl
      rw [subEntry_ren _ _ _ hs2, subEntry_ren _ _ _ hsj]
      rfl
    · rw [hsj] at hokj
      simp only [Sub.Ok] at hokj
      obtain ⟨rfl, hs, -⟩ := hokj
      have hs2 : (σ j).shift2 = .tm (s.rename (· + 2)) T (S'.mapIdx (Idx.ren (· + 2))) := by
        rw [hsj]; rfl
      rw [subEntry_tm _ _ _ hs2, subEntry_tm _ _ _ hsj]
      exact interp_rename hs (fun _ _ hk => hk) env' (env'.pelimPush A B o) (fun _ _ _ => rfl)

theorem substEnv_pairSub {Γ Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) {A B : Ty}
    {a b : Tm} {SA : ITy A} {SB : ITy B} (ha : HasTy Δ a A SA) (hb : HasTy Δ b B SB)
    (hapf : a.PelimFree) (hbpf : b.PelimFree) (env' : F.Env Δ w) :
    substEnv (pairSub a A SA b B SB σ) (hσ.pairSub' ha hb hapf hbpf) env'
      = (substEnv σ hσ env').pelimPush A B
          (F.interp (.pair a b) env' (.prod A B) ⟨_, .pair ha hb⟩) := by
  funext j T h
  rcases j with _ | _ | j
  · obtain rfl : B = T := Option.some.inj h
    rfl
  · obtain rfl : A = T := Option.some.inj h
    rfl
  · rfl

/-! ### ⭐The substitution lemma -/

theorem interp_psubst {Γ : Ctx} {t : Tm} {T : Ty} {S : ITy T} (ht : HasTy Γ t T S) :
    ∀ {Δ : Ctx} {w : F.W} {σ : Nat → Sub} (hσ : SubOk σ Γ Δ) (env' : F.Env Δ w),
      F.interp (t.psubst σ) env' T ⟨_, ht.psubst hσ⟩
        = F.interp t (substEnv σ hσ env') T ⟨S, ht⟩ := by
  induction ht with
  | @var Γ k hk =>
      intro Δ w σ hσ env'
      have hok := hσ k .base hk
      rcases Sub.cases_eq (σ k) with ⟨i, hsk⟩ | ⟨s, T', S', hsk⟩
      · have e : (Tm.var k).psubst σ = .var i := by simp only [Tm.psubst, hsk]
        refine (interp_tm_eq env' e _ _ (by rw [← e]; exact ⟨_, (HasTy.var hk).psubst hσ⟩)).trans ?_
        exact (subEntry_ren env' (σ k) _ hsk).symm
      · rw [hsk] at hok
        simp only [Sub.Ok] at hok
        obtain ⟨rfl, hs, -⟩ := hok
        cases S'
        have e : (Tm.var k).psubst σ = s := by simp only [Tm.psubst, hsk]
        refine (interp_tm_eq env' e _ _ ⟨_, hs⟩).trans ?_
        exact (subEntry_tm env' (σ k) _ hsk).symm
  | unit => intro Δ w σ hσ env'; exact obj_unit_eq _ _
  | pair _ _ iha ihb =>
      intro Δ w σ hσ env'
      dsimp only [Tm.psubst]
      simp only [Frame.interp]
      rw [iha hσ env', ihb hσ env']
  | @boxtm Γ t A S _ ih =>
      intro Δ w σ hσ env'
      dsimp only [Tm.psubst]
      simp only [Frame.interp]
      rw [obj_box_eq]
      funext w'
      rw [ih hσ.unbox (env'.boxPush w')]
      exact interp_env_eq (substEnv_unbox hσ env' w') t A _
  | @diatm Γ x X t A S hx ht ih =>
      intro Δ w σ hσ env'
      have hok := hσ x (.dia X) hx
      rcases Sub.cases_eq (σ x) with ⟨i, hsx⟩ | ⟨s, T', S', hsx⟩
      · -- the witness is renamed
        have hi : Δ i = some (.dia X) := by rw [hsx] at hok; exact hok
        have e : (Tm.diatm x X t).psubst σ
            = .diatm i X (t.psubst (Function.update (unboxSub σ) x (.ren i))) := by
          simp only [Tm.psubst, hsx]
        refine (interp_tm_eq env' e _ _
          (by rw [← e]; exact ⟨_, (HasTy.diatm hx ht).psubst hσ⟩)).trans ?_
        simp only [Frame.interp]
        have ho : env' i (.dia X) hi = substEnv σ hσ env' x (.dia X) hx :=
          (subEntry_ren env' (σ x) _ hsx).symm
        refine Eq.trans ((diaBuild_eq _ _ _).mpr (funext fun w' => ?_))
          (diaBuild_congr_left (fun o w' => F.interp t ((substEnv σ hσ env').diaPush x X o w') A
            ⟨S, ht⟩) ho)
        rw [ih (hσ.diaRen hi) (env'.diaPush i X (env' i (.dia X) hi) w')]
        exact interp_env_eq (substEnv_diaRen hσ hi env' w') t A _
      · -- modal β: the witness slot receives a `◇_y u`
        rw [hsx] at hok
        simp only [Sub.Ok] at hok
        obtain ⟨rfl, hs, hpf⟩ := hok
        obtain ⟨y, Y, u, U, rfl, rfl, hy, hu, hupf⟩ := canon_dia hs hpf
        have e : (Tm.diatm x X t).psubst σ
            = .diatm y Y (t.psubst (Function.update (unboxSub σ) x
                (.tm u X ((U.mapIdx (diaOut y)).mapIdx Idx.strip)))) := by
          simp only [Tm.psubst, hsx]
        refine (interp_tm_eq env' e _ _
          (by rw [← e]; exact ⟨_, (HasTy.diatm hx ht).psubst hσ⟩)).trans ?_
        simp only [Frame.interp]
        have ho : F.interp (.diatm y Y u) env' (.dia X) ⟨_, hs⟩
            = substEnv σ hσ env' x (.dia X) hx := (subEntry_tm env' (σ x) _ hsx).symm
        refine Eq.trans ?_ (diaBuild_congr_left (fun o w' => F.interp t
          ((substEnv σ hσ env').diaPush x X o w') A ⟨S, ht⟩) ho)
        simp only [Frame.interp]
        rw [diaBuild_diaBuild]
        refine (diaBuild_eq _ _ _).mpr (funext fun w' => ?_)
        rw [ih (hσ.diaTm hy hu hupf) (env'.diaPush y Y (env' y (.dia Y) hy) w')]
        exact interp_env_eq (substEnv_diaTm hσ hy hu hupf env' w') t A _
  | @pelim Γ p A B t T S hp ht ih =>
      intro Δ w σ hσ env'
      have hok := hσ p (.prod A B) hp
      rcases Sub.cases_eq (σ p) with ⟨i, hsp⟩ | ⟨s, T', S', hsp⟩
      · have hi : Δ i = some (.prod A B) := by rw [hsp] at hok; exact hok
        have e : (Tm.pelim p A B t).psubst σ = .pelim i A B (t.psubst (liftSub2 σ)) := by
          simp only [Tm.psubst, hsp]
        refine (interp_tm_eq env' e _ _
          (by rw [← e]; exact ⟨_, (HasTy.pelim hp ht).psubst hσ⟩)).trans ?_
        simp only [Frame.interp]
        have ho : env' i (.prod A B) hi = substEnv σ hσ env' p (.prod A B) hp :=
          (subEntry_ren env' (σ p) _ hsp).symm
        refine Eq.trans ?_ (congrArg (fun o => F.interp t ((substEnv σ hσ env').pelimPush A B o) T
          ⟨S, ht⟩) ho)
        rw [ih (hσ.lift2 A B) (env'.pelimPush A B (env' i (.prod A B) hi))]
        exact interp_env_eq (substEnv_lift2 hσ A B env' _) t T _
      · -- pair β
        rw [hsp] at hok
        simp only [Sub.Ok] at hok
        obtain ⟨rfl, hs, hpf⟩ := hok
        obtain ⟨a, b, SA, SB, rfl, rfl, ha, hb, hapf, hbpf⟩ := canon_prod hs hpf
        have e : (Tm.pelim p A B t).psubst σ = t.psubst (pairSub a A SA b B SB σ) := by
          simp only [Tm.psubst, hsp]
        refine (interp_tm_eq env' e _ _
          (by rw [← e]; exact ⟨_, (HasTy.pelim hp ht).psubst hσ⟩)).trans ?_
        rw [ih (hσ.pairSub' ha hb hapf hbpf) env']
        simp only [Frame.interp]
        have ho : F.interp (.pair a b) env' (.prod A B) ⟨_, .pair ha hb⟩
            = substEnv σ hσ env' p (.prod A B) hp := (subEntry_tm env' (σ p) _ hsp).symm
        refine Eq.trans ?_ (congrArg (fun o => F.interp t ((substEnv σ hσ env').pelimPush A B o) T
          ⟨S, ht⟩) ho)
        exact interp_env_eq (substEnv_pairSub hσ ha hb hapf hbpf env') t T _

end Frame

end DiaIdx

#print axioms DiaIdx.Frame.interp_ext_eq
#print axioms DiaIdx.Frame.sat_eqf
#print axioms DiaIdx.Frame.interp_psubst
