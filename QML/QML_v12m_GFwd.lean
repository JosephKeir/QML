import QML.QML_v12m_GLocal
import QML.QML_v12m_BNetStep

/-!
# QML v12m — the growing tree: an edge's data

What an edge commits, and that its transfer survives growth at either end: split from
`QML_v12m_GNet.lean`, so that a step along the root's self-edge (`QML_v12m_GLoopStep.lean`) can be
stated below the network.
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow

variable {σ : Signature}

/-! ## Transfers survive growth -/

/-- A growing target keeps the transfer. -/
theorem GTransfer.mono_tgt {Γ : Ctx} {M : Set (WFF σ Γ 0)} {ls : List VarType}
    {hle : (ctxOf ls).Le Γ} {k : Option VarSymb} {hk : KDecl (ctxOf ls) k} {lt lt' : List VarType}
    (h : (ctxOf lt).Le (ctxOf lt')) {N : Set (WFF σ (ctxOf lt) 0)}
    {N' : Set (WFF σ (ctxOf lt') 0)} (hN : ∀ φ ∈ N, WFF.mono h φ ∈ N')
    {f : VarSymb → LEnt σ} {hf : EntOk ((ctxOf ls).kView k) (ctxOf lt) f}
    (htr : GTransfer M ls hle k hk N f hf) : GTransfer M ls hle k hk N' f (hf.le h) := by
  intro ψ hψ
  have h' := hN _ (htr ψ hψ)
  rw [WFF.mono_subst] at h'
  rwa [WFF.subst_congr _ _ _ (ok_eS_kView (hf.le h)) _ (coh_eS_kView (hf.le h)) _ _
    (sim_eS_mono h hf) ψ] at h'

/-- A source growing conservatively keeps the transfer. -/
theorem GTransfer.mono_src {Γ Γ' : Ctx} (h : Γ.Le Γ') {M : Set (WFF σ Γ 0)}
    (hM : Theory.IsMCS M) {M' : Set (WFF σ Γ' 0)} (hM' : Theory.IsMCS M')
    (hsub : ∀ φ ∈ M, WFF.mono h φ ∈ M') {ls : List VarType} {hle : (ctxOf ls).Le Γ}
    {k : Option VarSymb} {hk : KDecl (ctxOf ls) k} {lt : List VarType}
    {N : Set (WFF σ (ctxOf lt) 0)} {f : VarSymb → LEnt σ}
    {hf : EntOk ((ctxOf ls).kView k) (ctxOf lt) f} (htr : GTransfer M ls hle k hk N f hf) :
    GTransfer M' ls (hle.trans h) k hk N f hf := by
  intro ψ hψ
  refine htr ψ (mem_of_mono_mem h hM hM' hsub ?_)
  rwa [WFF.mono_mono]

/-! ## Edges -/

/-- ⭐An edge from `tp` to `tk` of kind `k`: `tp`'s variables `cl` are committed by the item map
    `f`, with `□_k` transfer. -/
def FwdData (tp tk : NodeSt σ) (k : Option VarSymb) (cl : List VarType)
    (f : VarSymb → LEnt σ) : Prop :=
  ∃ (hsuf : cl <:+ tp.l) (hk : KDecl (ctxOf cl) k)
    (hf : EntOk ((ctxOf cl).kView k) (ctxOf tk.l) f),
    GTransfer tp.M cl (ctxOf_le_of_suffix hsuf) k hk tk.M f hf

theorem FwdData.grow_tgt {tp tk tk' : NodeSt σ} {k : Option VarSymb} {cl : List VarType}
    {f : VarSymb → LEnt σ} (h : FwdData tp tk k cl f) (hg : Grows tk tk') :
    FwdData tp tk' k cl f := by
  obtain ⟨hsuf, hk, hf, htr⟩ := h
  exact ⟨hsuf, hk, hf.le (ctxOf_le_of_suffix hg.suf), GTransfer.mono_tgt _ hg.sub htr⟩

theorem FwdData.grow_src {tp tp' tk : NodeSt σ} {k : Option VarSymb} {cl : List VarType}
    {f : VarSymb → LEnt σ} (hp : Theory.IsMCS tp.M) (hp' : Theory.IsMCS tp'.M)
    (h : FwdData tp tk k cl f) (hg : Grows tp tp') : FwdData tp' tk k cl f := by
  obtain ⟨hsuf, hk, hf, htr⟩ := h
  exact ⟨hsuf.trans hg.suf, hk, hf,
    GTransfer.mono_src (ctxOf_le_of_suffix hg.suf) hp hp' hg.sub htr⟩

end GArrow

end V12M
