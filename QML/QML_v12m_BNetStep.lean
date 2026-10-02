import QML.QML_v12m_BNetGrow

/-!
# QML v12m — B's arrow model: one realisation step

Realising the source's next variable along an arrow grows the target by one variable and commits
the variable (`realStep` for a `□` arrow, `realXStep` for a witness arrow).  ⭐`realStep_ok`,
⭐`realXStep_ok`: when the arrow's invariant holds, the grown target is maximal consistent, extends
the old one, and the arrow's invariant holds for one more variable.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature}

/-! ## The next variable -/

/-- The type of the variable after the suffix `ls` of `l`. -/
def nextTy (l ls : List VarType) : VarType := rootTy l ls.length

omit [ModalSys] in
theorem suffix_next {l ls : List VarType} (h : ls <:+ l) (hlt : ls.length < l.length) :
    (nextTy l ls :: ls) <:+ l := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨e', A, rfl⟩ : ∃ e' A, e = e' ++ [A] := by
    rcases List.eq_nil_or_concat e with he | ⟨e', A, he⟩
    · subst he
      simp at hlt
    · exact ⟨e', A, by rw [he, List.concat_eq_append]⟩
  have hA : nextTy (e' ++ [A] ++ ls) ls = A := by
    simp [nextTy, rootTy, List.getD_eq_getElem?_getD]
  rw [hA]
  exact ⟨e', by simp⟩

/-! ## A `□` arrow -/

/-- What a `□` arrow puts into the target when the source's next variable, of type `A`, is given
    an image. -/
def realSet [ModalSys.NoFour] (ts tt : NodeSt σ) (cl : List VarType) (img : ℕ → ℕ)
    (A : VarType) : Set (WFF σ (ctxOf (A.bc :: tt.l)) 0) :=
  {φ | ∃ (hle : (ctxOf (A :: cl)).Le (ctxOf ts.l)) (himg : ImgOk cl (ctxOf tt.l) img)
    (ψ : WFF σ (ctxOf (A :: cl)).boxIn 0), WFF.mono hle (.box ψ) ∈ ts.M ∧ φ = extArrow himg ψ}

/-- The target grown by the image of the source's next variable. -/
noncomputable def realStep [ModalSys.NoFour] (ts tt : NodeSt σ) (cl : List VarType)
    (img : ℕ → ℕ) : NodeSt σ :=
  ⟨(nextTy ts.l cl).bc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
    tt.M ∪ realSet ts tt cl img (nextTy ts.l cl))⟩

/-- ⭐One realisation step along a `□` arrow. -/
theorem realStep_ok [ModalSys.NoFour] {ts tt : NodeSt σ} {cl : List VarType} {img : ℕ → ℕ}
    (hs : Theory.IsMCS ts.M) (ht : Theory.IsMCS tt.M) (hsuf : cl <:+ ts.l)
    (himg : ImgOk cl (ctxOf tt.l) img)
    (htr : Transfer ts.M cl (ctxOf_le_of_suffix hsuf) tt.M img himg)
    (hlt : cl.length < ts.l.length) :
    Theory.IsMCS (realStep ts tt cl img).M ∧ Grows tt (realStep ts tt cl img) ∧
      ∃ (hsuf' : (nextTy ts.l cl :: cl) <:+ ts.l)
        (himg' : ImgOk (nextTy ts.l cl :: cl) (ctxOf (realStep ts tt cl img).l)
          (extImg img cl.length tt.l.length)),
        Transfer ts.M (nextTy ts.l cl :: cl) (ctxOf_le_of_suffix hsuf') (realStep ts tt cl img).M
          (extImg img cl.length tt.l.length) himg' := by
  have hsuf' := suffix_next hsuf hlt
  have hle := ctxOf_le_of_suffix hsuf'
  have hcons := realise_consistent hs hle ht himg htr
  have hsub : WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
      realSet ts tt cl img (nextTy ts.l cl) ⊆ WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l)
        '' tt.M ∪ {φ | ∃ ψ, WFF.mono hle (.box ψ) ∈ ts.M ∧ φ = extArrow himg ψ} := by
    rintro φ (h | ⟨_, _, ψ, h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ψ, h₁, h₂⟩
  obtain ⟨hS, hmcs⟩ := complete_spec (hcons.mono hsub)
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hS (Or.inl ⟨φ, hφ, rfl⟩)⟩, hsuf', imgOk_ext himg, ?_⟩
  intro ψ hψ
  exact hS (Or.inr ⟨hle, himg, ψ, hψ, rfl⟩)

/-! ## A witness arrow -/

/-- What a witness arrow puts into the target when the source's next variable is given an
    image. -/
def realXSet [ModalSys.NoFour] (ts tt : NodeSt σ) (x : VarSymb) (X : VarType) (cx : ℕ)
    (cl : List VarType) (img : ℕ → ℕ) (A : VarType) : Set (WFF σ (ctxOf (A.bc :: tt.l)) 0) :=
  {φ | ∃ (hle : (ctxOf (A :: cl)).Le (ctxOf ts.l)) (himg : ImgOk cl (ctxOf tt.l) img)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (ψ : WFF σ ((ctxOf (A :: cl)).diaIn x) 0),
    WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ) ∈ ts.M ∧ φ = extArrowX himg hx hcx ψ}

/-- The witness child grown by the image of the parent's next variable. -/
noncomputable def realXStep [ModalSys.NoFour] (ts tt : NodeSt σ) (x : VarSymb) (X : VarType)
    (cx : ℕ) (cl : List VarType) (img : ℕ → ℕ) : NodeSt σ :=
  ⟨(nextTy ts.l cl).bc :: tt.l, complete (WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) ''
    tt.M ∪ realXSet ts tt x X cx cl img (nextTy ts.l cl))⟩

/-- ⭐One realisation step along a witness arrow. -/
theorem realXStep_ok [ModalSys.NoFour] {ts tt : NodeSt σ} {x : VarSymb} {X : VarType} {cx : ℕ}
    {cl : List VarType} {img : ℕ → ℕ} (hs : Theory.IsMCS ts.M) (ht : Theory.IsMCS tt.M)
    (hsuf : cl <:+ ts.l) (himg : ImgOk cl (ctxOf tt.l) img)
    (hx : (ctxOf cl).ref x = some (.VTypeDia X))
    (hcx : (ctxOf tt.l).ref (.root (.free cx)) = some X)
    (htr : TransferX ts.M cl (ctxOf_le_of_suffix hsuf) hx tt.M img himg cx hcx)
    (hlt : cl.length < ts.l.length) :
    Theory.IsMCS (realXStep ts tt x X cx cl img).M ∧ Grows tt (realXStep ts tt x X cx cl img) ∧
      ∃ (hsuf' : (nextTy ts.l cl :: cl) <:+ ts.l)
        (himg' : ImgOk (nextTy ts.l cl :: cl) (ctxOf (realXStep ts tt x X cx cl img).l)
          (extImg img cl.length tt.l.length))
        (hx' : (ctxOf (nextTy ts.l cl :: cl)).ref x = some (.VTypeDia X))
        (hcx' : (ctxOf (realXStep ts tt x X cx cl img).l).ref (.root (.free cx)) = some X),
        TransferX ts.M (nextTy ts.l cl :: cl) (ctxOf_le_of_suffix hsuf') hx'
          (realXStep ts tt x X cx cl img).M (extImg img cl.length tt.l.length) himg' cx hcx' := by
  have hsuf' := suffix_next hsuf hlt
  have hle := ctxOf_le_of_suffix hsuf'
  have hcons := realiseX_consistent hs hle ht himg hx hcx htr
  have hsub : WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
      realXSet ts tt x X cx cl img (nextTy ts.l cl) ⊆
        WFF.mono (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l) '' tt.M ∪
          {φ | ∃ ψ, WFF.mono hle (WFF.boxx x ⟨X, ref_old_of_ref hx⟩ ψ) ∈ ts.M ∧
            φ = extArrowX himg hx hcx ψ} := by
    rintro φ (h | ⟨_, _, _, _, ψ, h₁, h₂⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ψ, h₁, h₂⟩
  obtain ⟨hS, hmcs⟩ := complete_spec (hcons.mono hsub)
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hS (Or.inl ⟨φ, hφ, rfl⟩)⟩, hsuf', imgOk_ext himg,
    ref_old_of_ref hx, (ctxOf_le_append [(nextTy ts.l cl).bc] tt.l).ref hcx, ?_⟩
  intro ψ hψ
  exact hS (Or.inr ⟨hle, himg, hx, hcx, ψ, hψ, rfl⟩)

end BArrow

end V12M
