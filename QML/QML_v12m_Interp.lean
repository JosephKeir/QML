import QML.QML_v12m_Env
import QML.QML_v12m_WFF

/-!
# QML v12m — the interpretation

Terms are interpreted structurally, except at the modal term formers, whose values must be elements
of the carriers — and carriers are only closed under the function algebra.  So the body of a
`□`/`◇` term is COMPILED to a definable map (`Term.compile`) out of the tuple of the objects it
uses — its **support** (`Term.bases`: a finite list of visible addresses with their types) — and:

* `□t` is `necMap` of the compiled body, applied to the necessary tuple of the support
  (`Env.necBundle`, built with `necPair`);
* `◇_x t` is `posMap` of the compiled body, applied to the possible tuple obtained from the
  necessary part of the support and the witness `x` by the strength, re-ordered by `Supp.assemble`.

Support entries are BASE addresses (trailing product steps removed); product components are reached
by projection (`Supp.refGF`).  Satisfaction (`sat`) is then the usual clauses; `◇_x φ` ranges over
the extent of `x`, the quantifiers over the domain of their type.
-/

namespace V12M

variable [ModalSys]

/-! ## Base addresses -/

/-- The address with its trailing product steps removed. -/
def VarSymb.base : VarSymb → VarSymb
  | .root r => .root r
  | .step v s => if s.isProj then v.base else .step v s

/-- A reachable address's base is visible. -/
def Ctx.baseOf (Δ : Ctx) : (v : VarSymb) → {T : VarType} → Δ.ref v = some T →
    Σ' U : VarType, Δ v.base = some U
  | .root _, T, h => ⟨T, h⟩
  | .step v s, T, h =>
      if hs : s.isProj = true then
        match hU : Δ.ref v with
        | some _ =>
            have r := Ctx.baseOf Δ v hU
            ⟨r.1, by rw [show (VarSymb.step v s).base = v.base from if_pos hs]; exact r.2⟩
        | none => False.elim (by rw [Ctx.ref_step_proj Δ v hs, hU] at h; cases h)
      else
        ⟨T, by
          rw [show (VarSymb.step v s).base = .step v s from if_neg hs]
          rw [Ctx.ref_step_nonproj Δ v hs] at h
          exact h⟩

/-! ## Supports -/

/-- A finite list of visible addresses with their types. -/
abbrev Supp (Δ : Ctx) : Type := List (Σ' (v : VarSymb) (T : VarType), Δ v = some T)

/-- The type of the tuple of a support. -/
def Supp.ty {Δ : Ctx} : Supp Δ → VarType
  | [] => .VTypeOne
  | e :: L => .VTypeProd e.2.1 (Supp.ty L)

/-- Contents of `□`-view entries, as entries of the outer context. -/
def Supp.outerBox {Δ : Ctx} : Supp Δ.boxIn → Supp Δ
  | [] => []
  | ⟨.step u .box, _, h⟩ :: L =>
      ⟨u.base, (Ctx.baseOf Δ u (Ctx.boxIn_step_box h)).1,
        (Ctx.baseOf Δ u (Ctx.boxIn_step_box h)).2⟩ :: Supp.outerBox L
  | ⟨.step u .keep, _, h⟩ :: L =>
      ⟨u.base, (Ctx.baseOf Δ u (Ctx.boxIn_keep h).2.1).1,
        (Ctx.baseOf Δ u (Ctx.boxIn_keep h).2.1).2⟩ :: Supp.outerBox L
  | ⟨.root _, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .fst, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .snd, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .dia, _, h⟩ :: _ => False.elim (by cases h)

/-- The necessary part of a `◇_x`-view support. -/
def Supp.boxPart {Δ : Ctx} {x : VarSymb} : Supp (Δ.diaIn x) → Supp Δ.boxIn
  | [] => []
  | ⟨.step u .box, T, h⟩ :: L => ⟨.step u .box, T, h⟩ :: Supp.boxPart L
  | ⟨.step u .keep, T, h⟩ :: L => ⟨.step u .keep, T, h⟩ :: Supp.boxPart L
  | ⟨.step _ .dia, _, _⟩ :: L => Supp.boxPart L
  | ⟨.root _, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .fst, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .snd, _, h⟩ :: _ => False.elim (by cases h)

/-! ## Definable maps out of a support -/

def GFunc.ofEq {σ : Signature} : {A B : VarType} → A = B → GFunc σ A B
  | _, _, rfl => .id _

/-- The projection along a product step. -/
def GFunc.proj {σ : Signature} {U T : VarType} {s : Step} (hs : s.isProj = true)
    (h : U.step s = some T) : GFunc σ U T := by
  cases U <;> cases s <;> (try cases hs) <;> (try cases h)
  · exact .fst
  · exact .snd
  · exact (VarType.step_here h).2 ▸ GFunc.extract (VarType.step_here h).1

/-- The component of a support tuple at a listed address. -/
def Supp.lookup {σ : Signature} {Δ : Ctx} : (L : Supp Δ) → (v : VarSymb) → {T : VarType} →
    Δ v = some T → v ∈ List.map PSigma.fst L → GFunc σ (Supp.ty L) T
  | [], _, _, _, hm => absurd hm List.not_mem_nil
  | ⟨v', T', h'⟩ :: L, v, _, h, hm =>
      if hvv : v' = v then
        .comp (GFunc.ofEq (Option.some.inj (h'.symm.trans (by rw [hvv]; exact h)))) .fst
      else
        .comp (Supp.lookup L v h ((List.mem_cons.mp hm).resolve_left (fun e => hvv e.symm))) .snd

/-- The object at a reachable address whose base is listed. -/
def Supp.refGF {σ : Signature} {Δ : Ctx} (L : Supp Δ) : (v : VarSymb) → {T : VarType} →
    Δ.ref v = some T → v.base ∈ List.map PSigma.fst L → GFunc σ (Supp.ty L) T
  | .root r, _, h, hm => Supp.lookup L (.root r) h hm
  | .step v s, _, h, hm =>
      if hs : s.isProj = true then
        match hU : Δ.ref v with
        | some _ =>
            .comp (GFunc.proj hs (by rw [Ctx.ref_step_proj Δ v hs, hU] at h; exact h))
              (Supp.refGF L v hU
                (by rw [show (VarSymb.step v s).base = v.base from if_pos hs] at hm; exact hm))
        | none => False.elim (by rw [Ctx.ref_step_proj Δ v hs, hU] at h; cases h)
      else
        Supp.lookup L (.step v s) (by rw [Ctx.ref_step_nonproj Δ v hs] at h; exact h)
          (by rw [show (VarSymb.step v s).base = .step v s from if_neg hs] at hm; exact hm)

/-- The necessary tuple of a `□`-view support, out of an outer support tuple. -/
def Supp.gatherBox {σ : Signature} {Δ : Ctx} (L : Supp Δ) : (L' : Supp Δ.boxIn) →
    (∀ e ∈ Supp.outerBox L', e.1 ∈ List.map PSigma.fst L) →
    GFunc σ (Supp.ty L) (.VTypeBox (Supp.ty L'))
  | [], _ => .comp .boxUnit (.unit _)
  | ⟨.step u .box, T, h⟩ :: L', hL =>
      .comp (.boxPair T (Supp.ty L'))
        (.pair (Supp.refGF L u (Ctx.boxIn_step_box h) (hL _ List.mem_cons_self))
          (Supp.gatherBox L L' (fun e he => hL e (List.mem_cons_of_mem _ he))))
  | ⟨.step u .keep, T, h⟩ :: L', hL =>
      .comp (.boxPair T (Supp.ty L'))
        (.pair (.comp (GFunc.keep (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2)
            (Supp.refGF L u (Ctx.boxIn_keep h).2.1 (hL _ List.mem_cons_self)))
          (Supp.gatherBox L L' (fun e he => hL e (List.mem_cons_of_mem _ he))))
  | ⟨.root _, _, h⟩ :: _, _ => False.elim (by cases h)
  | ⟨.step _ .fst, _, h⟩ :: _, _ => False.elim (by cases h)
  | ⟨.step _ .snd, _, h⟩ :: _, _ => False.elim (by cases h)
  | ⟨.step _ .dia, _, h⟩ :: _, _ => False.elim (by cases h)

/-- Re-order (necessary part, witness) into the tuple of a `◇_x`-view support. -/
def Supp.assemble {σ : Signature} {Δ : Ctx} {x : VarSymb} {X : VarType}
    (hx : Δ.ref x = some (.VTypeDia X)) :
    (L : Supp (Δ.diaIn x)) → GFunc σ (.VTypeProd (Supp.ty (Supp.boxPart L)) X) (Supp.ty L)
  | [] => .unit _
  | ⟨.step _ .box, _, _⟩ :: L =>
      .pair (.comp .fst .fst) (.comp (Supp.assemble hx L) (.pair (.comp .snd .fst) .snd))
  | ⟨.step _ .keep, _, _⟩ :: L =>
      .pair (.comp .fst .fst) (.comp (Supp.assemble hx L) (.pair (.comp .snd .fst) .snd))
  | ⟨.step _ .dia, _, h⟩ :: L =>
      .pair (.comp (GFunc.ofEq (Ctx.diaIn_step_dia hx h)) .snd) (Supp.assemble hx L)
  | ⟨.root _, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .fst, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .snd, _, h⟩ :: _ => False.elim (by cases h)

/-! ## The support of a term, and its compilation -/

mutual
  def Func.bases {σ : Signature} : {Δ : Ctx} → {n : ℕ} → Func σ Δ n → Supp Δ
    | _, _, .F _ => []
    | _, _, .eval g t => Func.bases g ++ Term.bases t

  /-- The support of a term. -/
  def Term.bases {σ : Signature} : {Δ : Ctx} → {T : VarType} → {a : Ann T} →
      Term σ Δ T a → Supp Δ
    | Δ, _, _, .var v hv => [⟨v.base, (Ctx.baseOf Δ v hv).1, (Ctx.baseOf Δ v hv).2⟩]
    | _, _, _, .func f => Func.bases f
    | _, _, _, .unit => []
    | _, _, _, .pair s t => Term.bases s ++ Term.bases t
    | _, _, _, .boxtm t => Supp.outerBox (Term.bases t)
    | Δ, _, _, .diatm x hx t =>
        ⟨x.base, (Δ x.base).getD .VTypeOne, by
          obtain ⟨X, h⟩ := hx
          have hb := (Ctx.baseOf Δ x h).2
          simp [hb]⟩ :: Supp.outerBox (Supp.boxPart (Term.bases t))
end

omit [ModalSys] in
theorem Supp.mem_self {Δ : Ctx} (L : Supp Δ) : ∀ e ∈ L, e.1 ∈ List.map PSigma.fst L :=
  fun e he => List.mem_map.mpr ⟨e, he, rfl⟩

mutual
  def Func.compile {σ : Signature} : {Δ : Ctx} → {n : ℕ} → (L : Supp Δ) → (g : Func σ Δ n) →
      (∀ e ∈ Func.bases g, e.1 ∈ List.map PSigma.fst L) →
      (Fin n → GFunc σ (Supp.ty L) .Var) → GFunc σ (Supp.ty L) .Var
    | _, _, _, .F f, _, args => .func f.1 (fun i => args (Fin.cast f.2 i))
    | _, _, L, .eval g t, hL, args =>
        Func.compile L g (fun e he => hL e (List.mem_append_left _ he))
          (Fin.cons (Term.compile L t (fun e he => hL e (List.mem_append_right _ he))) args)

  /-- ⭐A term as a definable map out of the tuple of a support containing its own. -/
  def Term.compile {σ : Signature} : {Δ : Ctx} → {T : VarType} → {a : Ann T} →
      (L : Supp Δ) → (t : Term σ Δ T a) →
      (∀ e ∈ Term.bases t, e.1 ∈ List.map PSigma.fst L) → GFunc σ (Supp.ty L) T
    | _, _, _, L, .var v hv, hL => Supp.refGF L v hv (hL _ List.mem_cons_self)
    | _, _, _, L, .func f, hL => Func.compile L f hL Fin.elim0
    | _, _, _, _, .unit, _ => .unit _
    | _, _, _, L, .pair s t, hL =>
        .pair (Term.compile L s (fun e he => hL e (List.mem_append_left _ he)))
          (Term.compile L t (fun e he => hL e (List.mem_append_right _ he)))
    | _, _, _, L, .boxtm t, hL =>
        .comp (.boxMap (Term.compile (Term.bases t) t (Supp.mem_self _))) (Supp.gatherBox L _ hL)
    | Δ, _, _, L, .diatm x hx t, hL =>
        match hr : Δ.ref x with
        | some (.VTypeDia X) =>
            .comp (.diaMap (Term.compile (Term.bases t) t (Supp.mem_self _)))
              (.comp (.diaMap (Supp.assemble hr (Term.bases t)))
                (.comp (.strength _ X)
                  (.pair
                    (Supp.gatherBox L (Supp.boxPart (Term.bases t))
                      (fun e he => hL e (List.mem_cons_of_mem _ he)))
                    (Supp.refGF L x hr (hL _ List.mem_cons_self)))))
        | some .Var => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some .VTypeOne => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeProd _ _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeBox _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | none => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
end

/-! ## Interpretation and satisfaction -/

namespace Model

variable {σ : Signature} {M : Model.{u, v} σ}

/-- The tuple of a support. -/
def Env.bundle {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    (L : Supp Δ) → M.frame.Dom (Supp.ty L) w
  | [] => PUnit.unit
  | e :: L => (env e.1 e.2.1 e.2.2, Env.bundle env L)

/-- The necessary tuple of a `□`-view support. -/
def Env.necBundle {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    (L : Supp Δ.boxIn) → M.frame.Nec (Supp.ty L) w
  | [] => M.ops.necUnit
  | ⟨.step u .box, _, h⟩ :: L =>
      M.ops.necPair (env.ref u (Ctx.boxIn_step_box h)) (Env.necBundle env L)
  | ⟨.step u .keep, _, h⟩ :: L =>
      M.ops.necPair
        (GFunc.eval M.ops (GFunc.keep (σ := σ) (Ctx.boxIn_keep h).1 (Ctx.boxIn_keep h).2.2) w
          (env.ref u (Ctx.boxIn_keep h).2.1))
        (Env.necBundle env L)
  | ⟨.root _, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .fst, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .snd, _, h⟩ :: _ => False.elim (by cases h)
  | ⟨.step _ .dia, _, h⟩ :: _ => False.elim (by cases h)

mutual
  def interpFunc {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
      {n : ℕ} → Func σ Δ n → (Fin n → M.frame.D w) → M.frame.D w
    | _, .F f, args => M.frame.funcInterp f.1 w (fun i => args (Fin.cast f.2 i))
    | _, .eval g t, args => interpFunc env g (Fin.cons (interp env t) args)

  /-- ⭐The value of a term. -/
  def interp {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
      {T : VarType} → {a : Ann T} → Term σ Δ T a → M.frame.Dom T w
    | _, _, .var v hv => env.ref v hv
    | _, _, .func f => interpFunc env f Fin.elim0
    | _, _, .unit => PUnit.unit
    | _, _, .pair s t => (interp env s, interp env t)
    | _, _, .boxtm t =>
        M.ops.necMap (Term.compile (Term.bases t) t (Supp.mem_self _))
          (env.necBundle (Term.bases t))
    | _, _, .diatm x hx t =>
        match hr : Δ.ref x with
        | some (.VTypeDia _) =>
            M.ops.posMap (Term.compile (Term.bases t) t (Supp.mem_self _))
              (M.ops.posMap (Supp.assemble hr (Term.bases t))
                (M.ops.posStrength (env.necBundle (Supp.boxPart (Term.bases t))) (env.ref x hr)))
        | some .Var => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some .VTypeOne => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeProd _ _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | some (.VTypeBox _) => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
        | none => False.elim (hx.elim fun _ h => by rw [hr] at h; cases h)
end

def relSat {Δ : Ctx} {w : M.frame.W} (env : M.Env Δ w) :
    {n : ℕ} → Rel σ Δ n → (Fin n → M.frame.D w) → Prop
  | _, .R r, args => M.frame.relInterp r.1 w (fun i => args (Fin.cast r.2 i))
  | _, .eval ρ t, args => relSat env ρ (Fin.cons (interp env t) args)
/-- ⭐`p` is **realised here**, with value `o`: the identity arrow lies in `p`'s extent and `p`'s
    content there is **indistinguishable** from `o` (`Model.Ind`; docs §10.33).  At a `◇`-free type
    the model's invariance makes this equality.  Naming it keeps the dependent `∃` out of
    congruence proofs. -/
def Realised (hT : ModalSys.T = true) {A : VarType} {w : M.frame.W}
    (p : M.frame.Dom (.VTypeDia A) w) (o : M.frame.Dom A w) : Prop :=
  ∃ hm : M.frame.reflAcc hT w ∈ (M.posEval p).1,
    M.Ind ((M.posEval p).2 ⟨M.frame.reflAcc hT w, hm⟩) o

/-- ⭐`c` **comes back as** `o` (strong B, `Back`; docs §11.1): its out leg is nonempty, and from
    every arrow of it some way home returns a value indistinguishable from `o`.  Row 1 (`nec`): the
    out leg is every arrow out of `w`; row 2 (`pos`): the carrier's own extent. -/
def Backs : (L : BLeg) → {A : VarType} → {w : M.frame.W} → M.frame.Dom (L.carrier A) w →
    M.frame.Dom A w → Prop
  | .nec, A, w, c, o =>
      Nonempty (M.frame.Acc w) ∧ ∀ a : M.frame.Acc w, ∃ r : M.frame.R a.1 w,
        M.Ind (M.necEval (M.necEval (c : M.frame.Nec (.VTypeBox A) w) a) ⟨w, ⟨r⟩⟩) o
  | .pos, A, w, c, o =>
      Nonempty (M.posEval (c : M.frame.Pos (.VTypeBox A) w)).1 ∧
        ∀ a : (M.posEval (c : M.frame.Pos (.VTypeBox A) w)).1, ∃ r : M.frame.R a.1.1 w,
          M.Ind (M.necEval ((M.posEval (c : M.frame.Pos (.VTypeBox A) w)).2 a) ⟨w, ⟨r⟩⟩) o


/-- ⭐Satisfaction. -/
def sat : {Γ : Ctx} → {d : ℕ} → {w : M.frame.W} → M.Env Γ w → WFF σ Γ d → Prop
  | _, _, _, env, .atom ρ => relSat env ρ Fin.elim0
  | _, _, _, env, .eq t s => interp env t = interp env s
  | _, _, _, _, .top => True
  | _, _, _, _, .bot => False
  | _, _, _, env, .and φ ψ => sat env φ ∧ sat env ψ
  | _, _, _, env, .or φ ψ => sat env φ ∨ sat env ψ
  | _, _, _, env, .imp φ ψ => sat env φ → sat env ψ
  | _, d, w, env, .all T φ => ∀ o : M.frame.Dom T w, sat (env.extend (.bnd d) o) φ
  | _, d, w, env, .ex T φ => ∃ o : M.frame.Dom T w, sat (env.extend (.bnd d) o) φ
  | _, _, w, env, .box φ => ∀ w' : M.frame.Acc w, sat (env.boxPush w') φ
  | Γ, _, _, env, .dia x _ φ =>
      ∃ (X : VarType) (h : Γ.ref x = some (.VTypeDia X)) (w' : (M.posEval (env.ref x h)).1),
        sat (env.diaPush x h w') φ
  | _, _, _, env, .here hT s t => Realised hT (interp env s) (interp env t)
  | _, _, _, env, .back _ L s t => Backs L (interp env s) (interp env t)
  | _, d, w, env, @WFF.ret _ _ _ _ _ A _ t Φ =>
      ∃ (a : M.frame.Acc w) (e : M.frame.Dom (.VTypeBox A) a.1),
        sat ((env.boxPush a).extend (.bnd d) e) Φ ∧
          ∃ r : M.frame.R a.1 w, M.Ind (M.necEval (e : M.frame.Nec A a.1) ⟨w, ⟨r⟩⟩) (interp env t)
  | Γ, d, w, env, @WFF.retx _ _ _ _ _ y _ A _ t Φ =>
      ∃ (Y : VarType) (h : Γ.ref y = some (.VTypeDia Y)) (a : (M.posEval (env.ref y h)).1)
        (e : M.frame.Dom (.VTypeBox A) a.1.1),
        sat ((env.diaPush y h a).extend (.bnd d) e) Φ ∧
          ∃ r : M.frame.R a.1.1 w,
            M.Ind (M.necEval (e : M.frame.Nec A a.1.1) ⟨w, ⟨r⟩⟩) (interp env t)

end Model

end V12M
