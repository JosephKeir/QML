import QML.QML_v12m_CanonWorld

/-!
# QML v12m — the chain's realised witnesses (strong T)

The Henkin chain declares, at a strong T step, a witness `ρ n : ◇A` for the term it enumerated,
together with the `Here` atom saying that witness is realised by that term (`retSet`).  This file
turns the atom into a `Canon.RealDatum`: the evidence that makes the witness a **realised** one,
whose realisation readings at every later stage are now a *derivation*
(`Canon.RealDatum.spec`, from `Canon.spec_of_here`) rather than data the construction arranges.

* ⭐`hereAt_mem_retSet`, `step_mem`: the atom is in the step's theory, the transport done once;
* ⭐`hhere_of_isRet`, `hhere_of_isRet_at`: and in the finished one, at every later stage;
* ⭐`exists_retW`: every term at every stage is some step's, so the finished theory has a `Here`
  atom for it — `World.retW`.  The datum making the witness realised is read off that atom
  downstream (`Canon.realised_of_here`), so this file no longer builds one (§10.41).

*Nothing here names the world's realisations any more (2026-09-28).* A world realises whatever its
theory says (`Canon.World.real`, read off `T` by `Nonempty`), so the old `chainReal`,
`chainReal_ret` and `retDatum_fields` are gone; what the chain still has to provide is that every
term, of any type, is *some* step's content.

*Retired with the schema (2026-09-27):* `spec_of_retHyps` and the packing it needed — `laterList`
with its side conditions, and the files `QML_v12m_StageSkip`, `QML_v12m_RetUse`, `QML_v12m_Pack`.
All of it existed because a hole formula could mention the later stages' constants; the atom
mentions only the witness and the term, so lifting it is one `StageSys.IsMCS.mem_lift_iff`.
-/

namespace V12M

variable [ModalSys]

namespace Ctx

omit [ModalSys] in
theorem le_of_eq {Γ Γ' : Ctx} (E : Γ = Γ') : Γ.Le Γ' := fun _ _ h => E ▸ h

end Ctx

/-- ⭐The same for the `Here` atom the new `Proof.T_dia` hands over: the contexts and the name are
    variables, so the equalities can be `subst`ed away. -/
theorem WFF.hereAt_transport {σ : Signature} {Γ Γ' Δ : Ctx} (hT : ModalSys.T = true)
    {A : VarType} {a : Ann A} (t : Term σ Γ A a) {c c' : ℕ}
    (hΓ : Γ = Γ') (hcc : c = c')
    (hc : Γ.RootFresh (.free c)) (hc' : Γ'.RootFresh (.free c'))
    (ht : Term σ Γ' A a) (hteq : ht = Term.mono (Ctx.le_of_eq hΓ) t)
    (hΔ : Γ'.insert (.free c') (.VTypeDia A) = Δ)
    (hle : (Γ.insert (.free c) (.VTypeDia A)).Le Δ) :
    WFF.mono hle (WFF.hereAt hT (.root (.free c))
        (Ctx.ref_insert_root Γ (.free c) (.VTypeDia A))
        (Term.weaken hc.root (.VTypeDia A) t) : WFF σ (Γ.insert (.free c) (.VTypeDia A)) 0) =
      WFF.mono (Ctx.le_of_eq hΔ) (WFF.hereAt hT (.root (.free c'))
        (Ctx.ref_insert_root Γ' (.free c') (.VTypeDia A))
        (Term.weaken hc'.root (.VTypeDia A) ht)) := by
  subst hΓ
  subst hcc
  subst hΔ
  subst hteq
  simp only [Term.mono_refl, WFF.mono_refl]

/-! ## The witness's specification -/

namespace WorldLang

variable {σ : Signature} (F : WorldLang)

/-- The witness of stage `n`, as an address. -/
abbrev wit (n : ℕ) : VarSymb := .root (.free (F.ρ n))

variable {F}

/-- At a later stage the witness is declared at its own type. -/
theorem ref_wit {m j n : ℕ} (h : n < j) : (F.ctx (m, j)).ref (F.wit n) = some (F.τ n) :=
  Ctx.stage_ref_root F.ρ F.ρ_inj (F.fresh m) h

/-- Nothing else is written at the witness's root. -/
theorem fr_wit {m j n : ℕ} : ∀ v : VarSymb, v.rt = .free (F.ρ n) → v ≠ F.wit n →
    (F.ctx (m, j)) v = none :=
  Ctx.stage_only_root F.ρ F.ρ_inj (F.fresh m) j

theorem WFF.mono_imp {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} (φ ψ : WFF σ Γ d) :
    WFF.mono h (.imp φ ψ) = .imp (WFF.mono h φ) (WFF.mono h ψ) := rfl

theorem WFF.mono_dia {Γ Γ' : Ctx} (h : Γ.Le Γ') {d : ℕ} {x : VarSymb}
    (hx : ∃ X, Γ.ref x = some (.VTypeDia X)) (χ : WFF σ (Γ.diaIn x) d) :
    WFF.mono h (.dia x hx χ) =
      .dia x (hx.imp fun _ hX => h.ref hX) (WFF.mono (h.diaIn x) χ) := rfl

/-! ## The chain's hypotheses, in the finished language -/

section Chain

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms] (L : WorldLang)
  {S₀ : Set ((L.pre []).Sentence σ)}

/-- Step `n` of the chain declared a strong T witness: the formula it chose called for no witness of
    its own, and the term query it read lives in a context contained in the step's own — exactly
    the guard `retStep` tests. -/
def IsRet (S₀ : Set ((L.pre []).Sentence σ)) (n : ℕ) : Prop :=
  (∀ (A : VarType) (ψ : WFF σ ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A) 1),
      L.choice n (L.chain S₀ n) ≠ .ex A ψ) ∧
    (∀ (A : VarType) (ψ : WFF σ ((L.ctxL (decM n) (L.chain S₀ n).l).insert (.bnd 0) A) 1),
      L.choice n (L.chain S₀ n) ≠ .imp (.all A ψ) .bot) ∧
    (L.ctxL (decM n) (L.termQ (σ := σ) n).1).Le (L.ctxL (decM n) (L.chain S₀ n).l)

variable {L}

/-- ⭐The term the step is declared for: the query's term, in the step's own context. -/
noncomputable def retTerm {n : ℕ} (hret : IsRet L S₀ n) :
    Term σ (L.ctxL (decM n) (L.chain S₀ n).l) (L.termQ (σ := σ) n).2.1 (L.termQ (σ := σ) n).2.2.1 :=
  Term.mono hret.2.2 (L.termQ (σ := σ) n).2.2.2

/-- At such a step the declaration is the one `retStep` makes. -/
theorem witStep_eq_retStep {n : ℕ} (hret : IsRet L S₀ n) :
    L.witStep (decM n) (L.chain S₀ n).l (L.termQ (σ := σ) n) (L.choice n (L.chain S₀ n)) =
      L.retStep (decM n) (L.chain S₀ n).l (L.termQ (σ := σ) n) := by
  unfold WorldLang.witStep
  split
  · next A ψ h => exact absurd h (hret.1 A ψ)
  · next A ψ h => exact absurd h (hret.2.1 A ψ)
  · rfl

/-- At a strong T step the witness is declared at the `◇` of the address's type. -/
theorem finalτ_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) :
    L.finalτ S₀ n = .VTypeDia (L.termQ (σ := σ) n).2.1 := by
  unfold WorldLang.finalτ
  rw [witStep_eq_retStep hret,
    show L.retStep (decM n) (L.chain S₀ n).l (L.termQ (σ := σ) n) =
    ⟨.VTypeDia (L.termQ (σ := σ) n).2.1, L.retSet hT (L.chain S₀ n).l (decM n)
      (retTerm hret)⟩ from dif_pos ⟨hT, hTS, hret.2.2⟩]

/-- ⭐The `Here` atom the chain added for a strong T witness, as a sentence of the step's set. -/
theorem hereAt_mem_retSet (hT : ModalSys.T = true) {n : ℕ} (hret : IsRet L S₀ n) (m : ℕ)
    (hm : decM n ≤ m) :
    (⟨m, WFF.hereAt hT (.root (.free (L.ρ (L.chain S₀ n).l.length)))
        (Ctx.ref_insert_root (L.ctxL m (L.chain S₀ n).l)
          (.free (L.ρ (L.chain S₀ n).l.length))
          (.VTypeDia (L.termQ (σ := σ) n).2.1))
        (Term.weaken (L.ctxL_fresh (l := (L.chain S₀ n).l)
              (n := (L.chain S₀ n).l.length) le_rfl).root
          (.VTypeDia (L.termQ (σ := σ) n).2.1)
          (Term.mono (L.ctxL_base_le hm (L.chain S₀ n).l) (retTerm hret)))⟩ :
      (L.pre (.VTypeDia (L.termQ (σ := σ) n).2.1 :: (L.chain S₀ n).l)).Sentence σ) ∈
      L.retSet hT (L.chain S₀ n).l (decM n) (retTerm hret) :=
  ⟨m, hm, rfl⟩

/-- ⭐At a strong T step, whatever the chain adds for the address's η-expansion is in the step's
    theory.  Abstract in the sentence, so that the transport — the step's declaration left stuck, so
    that the match can be split — is done once. -/
theorem step_mem (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ)
    (φ : WFF σ ((L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
      (.VTypeDia (L.termQ (σ := σ) n).2.1)) 0)
    (hmem : (⟨m, φ⟩ :
        (L.pre (.VTypeDia (L.termQ (σ := σ) n).2.1 :: (L.chain S₀ n).l)).Sentence σ) ∈
      L.retSet hT (L.chain S₀ n).l (decM n) (retTerm hret))
    (hEq : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
        (.VTypeDia (L.termQ (σ := σ) n).2.1) =
      L.ctxL m (L.chain S₀ (n + 1)).l) :
    (⟨m, WFF.mono (Ctx.le_of_eq hEq) φ⟩ :
      (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈ (L.chain S₀ (n + 1)).S := by
  refine Set.mem_union_right _ ?_
  have base : ∀ hEq'' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
        (.VTypeDia (L.termQ (σ := σ) n).2.1) =
      L.ctxL m ((⟨.VTypeDia (L.termQ (σ := σ) n).2.1,
        L.retSet hT (L.chain S₀ n).l (decM n) (retTerm hret)⟩ :
          Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).1 :: (L.chain S₀ n).l),
      (⟨m, WFF.mono (Ctx.le_of_eq hEq'') φ⟩ :
        (L.pre ((⟨.VTypeDia (L.termQ (σ := σ) n).2.1,
          L.retSet hT (L.chain S₀ n).l (decM n) (retTerm hret)⟩ :
              Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).1 ::
                (L.chain S₀ n).l)).Sentence σ) ∈
        (⟨.VTypeDia (L.termQ (σ := σ) n).2.1,
          L.retSet hT (L.chain S₀ n).l (decM n) (retTerm hret)⟩ :
              Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ)).2 := by
    intro hEq''
    rw [WFF.mono_refl]
    exact hmem
  exact Eq.subst
    (motive := fun X : Σ A : VarType, Set ((L.pre (A :: (L.chain S₀ n).l)).Sentence σ) =>
      ∀ hEq'' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
          (.VTypeDia (L.termQ (σ := σ) n).2.1) =
        L.ctxL m (X.1 :: (L.chain S₀ n).l),
        (⟨m, WFF.mono (Ctx.le_of_eq hEq'') φ⟩ :
          (L.pre (X.1 :: (L.chain S₀ n).l)).Sentence σ) ∈ X.2)
    ((dif_pos ⟨hT, hTS, hret.2.2⟩ : L.retStep (decM n) (L.chain S₀ n).l
        (L.termQ (σ := σ) n) = ⟨_, _⟩).symm.trans (witStep_eq_retStep hret).symm) base hEq

theorem ctxL_eq_final (S₀ : Set ((L.pre []).Sentence σ)) (m j : ℕ) :
    L.ctxL m (L.chain S₀ j).l = (L.final S₀).ctx (m, j) := (L.final_ctx S₀ m j).symm

/-- At a strong T step the next stage declares the witness at the `◇` of the address's type. -/
theorem ctx_succ_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ) :
    ((L.final S₀).ctx (m, n)).insert (.free (L.ρ n))
        (.VTypeDia (L.termQ (σ := σ) n).2.1) = (L.final S₀).ctx (m, n + 1) := by
  rw [WorldLang.ctx_succ, show (L.final S₀).τ n =
    .VTypeDia (L.termQ (σ := σ) n).2.1 from finalτ_of_isRet hT hTS hret]
  rfl

/-- ⭐The chain's `Here` atom for a strong T witness, as a sentence of the finished theory: this is
    what `Canon.spec_of_here` asks for.  The transport is `WFF.hereAt_transport`, the step's own
    membership `hereAt_mem_retSet`, and `step_mem` carries it into the step's theory. -/
theorem hhere_of_isRet (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (m : ℕ) (hm : decM n ≤ m) :
    (⟨(m, n + 1), WFF.mono
        (Ctx.le_of_eq (ctx_succ_of_isRet hT hTS hret m))
        (WFF.hereAt hT (.root (.free (L.ρ n)))
          (Ctx.ref_insert_root ((L.final S₀).ctx (m, n)) (.free (L.ρ n))
            (.VTypeDia (L.termQ (σ := σ) n).2.1))
          (Term.weaken ((L.final S₀).fresh_ctx (m := m) (j := n) (n := n) le_rfl).root
            (.VTypeDia (L.termQ (σ := σ) n).2.1)
            (Term.mono ((L.final S₀).ctx_le (Prod.mk_le_mk.mpr ⟨hm, le_rfl⟩))
              (Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n))
                (retTerm hret)))))⟩ :
      (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  refine ⟨n + 1, le_rfl, ?_⟩
  have hlen : (L.chain S₀ n).l.length = n := length_chain S₀ n
  have hctx : (L.final S₀).ctx (m, n) = L.ctxL m (L.chain S₀ n).l := L.final_ctx S₀ m n
  have hname : L.ρ n = L.ρ (L.chain S₀ n).l.length := by rw [hlen]
  have hEq' : (L.ctxL m (L.chain S₀ n).l).insert (.free (L.ρ (L.chain S₀ n).l.length))
      (.VTypeDia (L.termQ (σ := σ) n).2.1) = L.ctxL m (L.chain S₀ (n + 1)).l := by
    rw [← hname, ← hctx]
    exact (ctx_succ_of_isRet hT hTS hret m).trans (L.final_ctx S₀ m (n + 1))
  refine Eq.mp (congrArg (fun φ => (⟨m, φ⟩ : (L.pre (L.chain S₀ (n + 1)).l).Sentence σ) ∈
    (L.chain S₀ (n + 1)).S) ?_) (step_mem hT hTS hret m _ (hereAt_mem_retSet hT hret m hm) hEq')
  rw [WFF.mono_mono]
  refine (WFF.hereAt_transport hT
    (Term.mono ((L.final S₀).ctx_le (Prod.mk_le_mk.mpr ⟨hm, le_rfl⟩))
      (Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n)) (retTerm hret)))
    hctx hname ((L.final S₀).fresh_ctx (m := m) (j := n) (n := n) le_rfl)
    (L.ctxL_fresh le_rfl) _ ?_ hEq' _).symm
  rw [Term.mono_mono, Term.mono_mono]


/-- ⭐The atom at **every** later stage, which is what `Canon.spec_of_here` asks for: the one at the
    step's own stage, lifted by maximal consistency (`StageSys.IsMCS.mem_lift_iff`) and read back
    through `WFF.mono_hereAt_of_le`. -/
theorem hhere_of_isRet_at (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (hS₀ : StageSys.Consistent S₀) (i : ℕ × ℕ) (hi : (decM n, n) ≤ i)
    (hlt : n < i.2)
    (hd : ((L.final S₀).ctx i).ref (.root (.free (L.ρ n))) =
      some (.VTypeDia (L.termQ (σ := σ) n).2.1)) :
    (⟨i, WFF.hereAt hT (.root (.free (L.ρ n))) hd
        (Term.mono ((L.final S₀).ctx_le hi)
          (Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n)) (retTerm hret)))⟩ :
      (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  obtain ⟨m, j⟩ := i
  have hlift : ((m, n + 1) : ℕ × ℕ) ≤ (m, j) := Prod.mk_le_mk.mpr ⟨le_rfl, hlt⟩
  refine Eq.mp (congrArg (fun φ => (⟨(m, j), φ⟩ : (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀) ?_)
    (((WorldLang.finalT_isMCS hS₀).mem_lift_iff hlift).mpr (hhere_of_isRet hT hTS hret m hi.1))
  rw [StageSys.lift, WFF.mono_mono,
    WFF.mono_hereAt_of_le hT _ _ _ hd]
  exact WFF.here_congr' hT rfl
    (by simp only [Term.weaken, Term.mono_mono])

/-! ## The realisation a strong T step provides -/

/-- The witness a strong T step declares is declared, at the `◇` of the step's type, from just past
    the step's own stage on. -/
theorem retDecl (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true) {n : ℕ}
    (hret : IsRet L S₀ n) (i : ℕ × ℕ) (hlt : n < i.2) :
    ((L.final S₀).ctx i).ref (.root (.free (L.ρ n))) =
      some (.VTypeDia (L.termQ (σ := σ) n).2.1) := by
  obtain ⟨m, j⟩ := i
  exact (finalτ_of_isRet hT hTS hret) ▸ ref_wit hlt



/-! ## Every term is realised -/

/-- A step whose formula is `⊤` and whose term query fits its context declares a strong T
    witness: neither `⊤` nor its negation calls for a witness of its own. -/
theorem isRet_of_top {n : ℕ}
    (htop : enumF (σ := σ) (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKF n) = .top)
    (hq : (L.ctxL (decM n) (L.termQ (σ := σ) n).1).Le (L.ctxL (decM n) (L.chain S₀ n).l)) :
    IsRet L S₀ n := by
  have hqt : L.query (σ := σ) n (L.chain S₀ n).l = .top := by
    rw [query_chain S₀ n (chain_le S₀ (decJ_le n) (decM n)), htop]
    rfl
  refine ⟨fun A ψ => ?_, fun A ψ => ?_, hq⟩ <;>
    rcases choice_cases (L := L) n (L.chain S₀ n) with hc | hc <;> rw [hc, hqt]
  · exact fun h => by cases h
  · exact fun h => by cases h
  · exact fun h => by cases h
  · intro h
    injection h
    rename_i h₁ h₂ h₃
    cases h₂


/-- ⭐At a strong T step, the finished theory has the `Here` atom for the query's term, read in the
    finished language at the first stage that declares the witness.  Stated for any query equal to
    the step's, so that the equation can be `subst`ed and the query's components compute. -/
theorem retW_of_step (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true)
    (hS₀ : StageSys.Consistent S₀) {n : ℕ} (q : L.RetQ σ (decM n)) (hq : L.termQ n = q)
    (htop : enumF (σ := σ) (L.ctxL (decM n) (L.chain S₀ (decJ n)).l) (decKF n) = .top)
    (hle : (L.ctxL (decM n) q.1).Le (L.ctxL (decM n) (L.chain S₀ n).l)) :
    ∃ hd : ((L.final S₀).ctx (decM n, n + 1)).ref (.root (.free (L.ρ n))) =
        some (.VTypeDia q.2.1),
      (⟨(decM n, n + 1), WFF.hereAt hT (.root (.free (L.ρ n))) hd
          (Term.mono ((L.final S₀).ctx_le (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ n⟩))
            (Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ (decM n) n)) (Term.mono hle q.2.2.2)))⟩ :
        (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  subst hq
  have hret : IsRet L S₀ n := isRet_of_top htop hle
  exact ⟨retDecl hT hTS hret (decM n, n + 1) (Nat.lt_succ_self n),
    hhere_of_isRet_at hT hTS hret hS₀ (decM n, n + 1)
      (Prod.mk_le_mk.mpr ⟨le_rfl, Nat.le_succ n⟩) (Nat.lt_succ_self n) _⟩

/-- ⭐**Every term, of any type, at every stage, is realised by the theory's word**: the step that
    enumerates it as its term query and reads `⊤` declares a witness with the `Here` atom for it.
    This is strong T on the construction side, with no naming (§10.41): the atom's content is the
    term itself, and the datum making the witness realised is read off the atom downstream. -/
theorem exists_retW (hT : ModalSys.T = true) (hTS : ModalSys.TStrong = true)
    (hS₀ : StageSys.Consistent S₀) (m j : ℕ) {A : VarType} {a : Ann A}
    (t : Term σ ((L.final S₀).ctx (m, j)) A a) :
    ∃ (i' : ℕ × ℕ) (hi : (m, j) ≤ i') (y : VarSymb)
      (hy : ((L.final S₀).ctx i').ref y = some (.VTypeDia A)),
      (⟨i', WFF.hereAt hT y hy (Term.mono ((L.final S₀).ctx_le hi) t)⟩ :
        (L.final S₀).sys.Sentence σ) ∈ L.finalT S₀ := by
  let t' : Term σ (L.ctxL m (L.chain S₀ j).l) A a :=
    Term.mono (Ctx.le_of_eq (ctxL_eq_final S₀ m j).symm) t
  obtain ⟨k', hk'⟩ := L.enumRQ_surjective (σ := σ) m ⟨(L.chain S₀ j).l, A, a, t'⟩
  obtain ⟨kt, hkt⟩ := enumF_surjective (σ := σ) (L.ctxL m (L.chain S₀ j).l) .top
  obtain ⟨n, hj, hm, hkf, hkT⟩ := exists_decFT m j kt k'
  subst hm
  subst hj
  have hq : L.termQ n = ⟨(L.chain S₀ (decJ n)).l, A, a, t'⟩ := by rw [termQ, hkT, hk']
  obtain ⟨hd, hmem⟩ := retW_of_step hT hTS hS₀ _ hq (by rw [hkf]; exact hkt)
    (chain_le S₀ (decJ_le n) (decM n))
  have hi : ((decM n, decJ n) : ℕ × ℕ) ≤ (decM n, n + 1) :=
    Prod.mk_le_mk.mpr ⟨le_rfl, (decJ_le n).trans (Nat.le_succ n)⟩
  refine ⟨(decM n, n + 1), hi, _, hd, ?_⟩
  refine Eq.mp (congrArg (fun φ => (⟨(decM n, n + 1), φ⟩ : (L.final S₀).sys.Sentence σ) ∈
    L.finalT S₀) ?_) hmem
  exact WFF.here_congr' hT rfl (by simp only [t', Term.mono_mono])


end Chain

end WorldLang

end V12M
