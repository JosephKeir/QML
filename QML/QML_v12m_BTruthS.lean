import QML.QML_v12m_BLimitW

/-!
# QML v12m — B's canonical model: the strong B cases of the truth lemma

The truth lemma (`BData.truth`) takes its `Back` and returning-possibility cases as a hypothesis
(`BData.StrongTruth`).  Here they are assembled from both directions of each case:

* `Back` (`mem_back_of_sat`, `sat_back_of_mem`), its carrier `□□A` or `◇□A` read as a body;
* `ret` and `retx` at necessary shapes (`mem_ret_of_sat_nec`, `mem_retx_of_sat`,
  `sat_retS_nec_of_memC`, `sat_retxS_nec_of_memC`) and at witnessed shapes
  (`mem_ret_of_sat_wit`, `mem_retx_of_sat_wit`, `sat_retS_wit_of_memC`,
  `sat_retxS_wit_of_memC`).

⭐`BData.strongTruth_of` does this from the fields a `BData` needs, and ⭐`bdataS_strongTruth`
supplies them for the limit of a strong chain.  Under rows 3–4 (`BStrongW`) the network makes only
doubly witnessed children, so ⭐`BData.strongTruth_ofW` reaches the other returning possibilities
through them: a necessary shape realises a possible part (`Proof.ret_realise`), a plain leg names
its route at the packed shape (`BData.Routes`, the derived `Proof.ret_route_node`), and all are
undone semantically (`Model.sat_ret_unrealise`, `Model.sat_retx_forget`, `Model.sat_ret_map`).
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

namespace BData

variable {B : BData σ}

/-- ⭐**The strong B cases of the truth lemma**, from the fields of the canonical data. -/
theorem strongTruth_of (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hInj : B.ImgInj) (hCx : B.CxFresh) (hRI : B.RetIn hS) (hRIX : B.RetInX hS)
    (hRW : B.RetInW hS) (hRWX : B.RetInWX hS) (hRO : B.RetOutC hS) (hROX : B.RetOutXC hS)
    (hROD : B.RetOutDC hS) (hROXD : B.RetOutXDC hS) : B.StrongTruth hS where
  back := by
    intro s i L A b a c t IH
    refine ⟨fun h => ?_, sat_back_of_mem hS c t⟩
    cases L with
    | nec =>
        match c with
        | .boxtm (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx .nec bd t (fun K φ hφ => IH s K φ hφ) h
    | pos =>
        match c with
        | .diatm y hy (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx (.pos y hy) bd t (fun K φ hφ => IH s K φ hφ) h
  retS := by
    intro s i S a t Φ IH
    cases S with
    | nec N => exact ⟨mem_ret_of_sat_nec hS hInj hRI t Φ IH, sat_retS_nec_of_memC hS hRO t Φ IH⟩
    | wit N Z =>
        exact ⟨mem_ret_of_sat_wit hS hInj hRW t Φ IH, sat_retS_wit_of_memC hS hROD t Φ IH⟩
  retxS := by
    intro s i y hy S a t Φ IH
    cases S with
    | nec N =>
        exact ⟨mem_retx_of_sat hS hInj hRIX hy t Φ IH, sat_retxS_nec_of_memC hS hROX hy t Φ IH⟩
    | wit N Z =>
        exact ⟨mem_retx_of_sat_wit hS hInj hRWX hy t Φ IH,
          sat_retxS_wit_of_memC hS hROXD hy t Φ fun s' K φ hφ => IH s' K φ (by
            change φ.size < Φ.size + _ + 1
            omega)⟩

/-! ## Rows 3–4: through named routes and realised parts -/

/-- ⭐Rows 3–4: **every returning possibility along `□` at a boxed shape names its route** at a
    later stage, a root `κ : ◇𝟙` along which it returns (`Proof.ret_route_node`).  The limit of a
    strong chain has it (`bdataS_routes`). -/
def Routes (B : BData σ) (hS : ModalSys.BStrong = true) : Prop :=
  ∀ {s : B.W} {i : ℕ} {S : RShape} {a : Ann S.flat} (t : Term σ ((B.w s).ctx i) S.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) S.ty) 1), S.boxed = true →
    WFF.retS hS S t Φ ∈ (B.w s).M i →
      ∃ (j : ℕ) (hij : i ≤ j) (κ : VarSymb)
        (hκ : ((B.w s).ctx j).ref κ = some (.VTypeDia .VTypeOne)),
        WFF.retxS hS κ ⟨_, hκ⟩ S (Term.mono ((B.w s).le hij) t)
          (WFF.mono ((Ctx.le_boxIn_diaIn _ κ).insert (.bnd 0) S.ty)
            (WFF.mono (((B.w s).le hij).boxIn.insert (.bnd 0) S.ty) Φ)) ∈ (B.w s).M j

/-- Rows 3–4: `ret` at a boxed witnessed shape, membership ⇒ truth (plain leg): the route named
    (`Routes`), the returning possibility along it true (`sat_retxS_wit_of_memC`), and the route
    forgotten (`Model.sat_retx_forget`). -/
theorem sat_retS_wit_of_memW_boxed (hS : ModalSys.BStrong = true) (hRt : B.Routes hS)
    (hRX : B.RetOutXDC hS) {s : B.W} {i : ℕ} {N : NShape} {Z : VarType}
    (hb : (RShape.wit N Z).boxed = true)
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < Φ.size + 1 → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  obtain ⟨j, hij, κ, hκ, hm⟩ := hRt t Φ hb h
  have hs := sat_retxS_wit_of_memC hS hRX ⟨_, hκ⟩ _ _ (fun s' K φ hφ => IH s' K φ (by
    rw [WFF.size_mono, WFF.size_mono] at hφ
    exact hφ)) hm
  have hf := Model.sat_retx_forget _ hS ⟨_, hκ⟩ (.wit N Z) _ _ hs
  exact (Model.sat_mono (B.canonEnv_le s hij) (WFF.retS hS (.wit N Z) t Φ)).mp hf

/-- ⭐**Rows 3–4: `ret` at a witnessed shape, membership ⇒ truth** (plain leg): pack the
    necessary part (`retS_packGW`), take the truth at the boxed shape
    (`sat_retS_wit_of_memW_boxed`), and map it back (`sat_ret_map` along `unpackG`). -/
theorem sat_retS_wit_of_memW (hS : ModalSys.BStrong = true) (hRt : B.Routes hS)
    (hRX : B.RetOutXDC hS) {s : B.W} {i : ℕ} {N : NShape} {Z : VarType}
    {a : Ann (RShape.wit N Z).flat} (t : Term σ ((B.w s).ctx i) (RShape.wit N Z).flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) (RShape.wit N Z).ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < Φ.size + 1 → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.wit N Z) t Φ : WFF σ _ 0) := by
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨retS_packGW hS .nec t Φ (Proof.lookup List.mem_cons_self)⟩
  have hsat := sat_retS_wit_of_memW_boxed hS hRt hRX (N := N.packed) rfl _ _
    (fun s' K φ hφ => IH s' K φ (by
      unfold WFF.bodyRepl at hφ
      rw [WFF.size_subst] at hφ
      exact hφ)) hp
  have hb := Model.sat_ret_map (B.canonEnv s i) (noProjLast s i) indCongr hS .nec
    (S := .wit N.packed Z) (unpackG N) _ Φ hsat
  refine (congrArg (B.model.sat _) (OutLeg.retS_congr hS .nec (.wit N Z) ?_ rfl)).mp hb
  rw [Term.holeRead_eq_holeAt, Term.holeRead_eq_holeAt]
  exact holeAt_packG_unpackGW_val N Z t

/-- ⭐**Rows 3–4: `ret` at a necessary shape, membership ⇒ truth** (plain leg): a possible part
    realised (`Proof.ret_realise`), the witnessed case, and the part dropped
    (`Model.sat_ret_unrealise`). -/
theorem sat_retS_nec_of_memW (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true)
    (hRt : B.Routes hS) (hRX : B.RetOutXDC hS) {s : B.W} {i : ℕ} {N : NShape}
    {a : Ann N.flat} (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ (((B.w s).ctx i).boxIn.insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < Φ.size + 1 → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) ∈ (B.w s).M i) :
    B.model.sat (B.canonEnv s i) (WFF.retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨Proof.ret_realise hS hW .nec N t Term.unit Φ (Proof.lookup List.mem_cons_self)⟩
  exact Model.sat_ret_unrealise _ hS .nec N t Term.unit Φ
    (sat_retS_wit_of_memW hS hRt hRX _ _ (fun s' K φ hφ => IH s' K φ (by
      unfold WFF.bodyRepl at hφ
      rw [WFF.size_subst] at hφ
      exact hφ)) hp)

/-- ⭐**Rows 3–4: `ret` along a witness at a necessary shape, membership ⇒ truth**: as
    `sat_retS_nec_of_memW`, along `y`. -/
theorem sat_retxS_nec_of_memW (hS : ModalSys.BStrong = true) (hW : ModalSys.BStrongW = true)
    (hRX : B.RetOutXDC hS) {s : B.W} {i : ℕ} {y : VarSymb}
    (hy : ∃ Y, ((B.w s).ctx i).ref y = some (.VTypeDia Y)) {N : NShape} {a : Ann N.flat}
    (t : Term σ ((B.w s).ctx i) N.flat a)
    (Φ : WFF σ ((((B.w s).ctx i).diaIn y).insert (.bnd 0) N.ty) 1)
    (IH : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0),
      φ.size < Φ.size + 1 → (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K))
    (h : ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) ∈
      (B.w s).M i) :
    B.model.sat (B.canonEnv s i)
      ((OutLeg.pos y hy : OutLeg ((B.w s).ctx i)).retS hS (.nec N) t Φ : WFF σ _ 0) := by
  have hp := BWorld.mem_of_provable (Δ := [_]) (fun ψ hψ => by
    rw [List.mem_singleton.mp hψ]; exact h)
    ⟨Proof.ret_realise hS hW (.pos y hy) N t Term.unit Φ (Proof.lookup List.mem_cons_self)⟩
  exact Model.sat_ret_unrealise _ hS (.pos y hy) N t Term.unit Φ
    (sat_retxS_wit_of_memC hS hRX hy _ _ (fun s' K φ hφ => IH s' K φ (by
      unfold WFF.bodyRepl at hφ
      rw [WFF.size_subst] at hφ
      exact hφ)) hp)

/-- ⭐**The strong B cases of the truth lemma under rows 3–4**: as `strongTruth_of`, the
    returning possibilities through named routes and realised parts, so only the doubly
    witnessed children are needed (`RetOutXDC`). -/
theorem strongTruth_ofW (hS : ModalSys.BStrong = true) (hB : ModalSys.B = true)
    (hW : ModalSys.BStrongW = true) (hInj : B.ImgInj) (hCx : B.CxFresh) (hRI : B.RetIn hS)
    (hRIX : B.RetInX hS) (hRW : B.RetInW hS) (hRWX : B.RetInWX hS) (hRt : B.Routes hS)
    (hROXD : B.RetOutXDC hS) : B.StrongTruth hS where
  back := by
    intro s i L A b a c t IH
    refine ⟨fun h => ?_, sat_back_of_mem hS c t⟩
    cases L with
    | nec =>
        match c with
        | .boxtm (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx .nec bd t (fun K φ hφ => IH s K φ hφ) h
    | pos =>
        match c with
        | .diatm y hy (.boxtm bd) =>
            exact mem_back_of_sat hS hB hInj hCx (.pos y hy) bd t (fun K φ hφ => IH s K φ hφ) h
  retS := by
    intro s i S a t Φ IH
    have IHb : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K) := fun s' K φ hφ =>
      IH s' K φ (by
        change φ.size < Φ.size + _ + 1
        omega)
    cases S with
    | nec N =>
        exact ⟨mem_ret_of_sat_nec hS hInj hRI t Φ IH,
          sat_retS_nec_of_memW hS hW hRt hROXD t Φ IHb⟩
    | wit N Z =>
        exact ⟨mem_ret_of_sat_wit hS hInj hRW t Φ IH, sat_retS_wit_of_memW hS hRt hROXD t Φ IHb⟩
  retxS := by
    intro s i y hy S a t Φ IH
    have IHb : ∀ (s' : B.W) (K : ℕ) (φ : WFF σ ((B.w s').ctx K) 0), φ.size < Φ.size + 1 →
        (B.model.sat (B.canonEnv s' K) φ ↔ φ ∈ (B.w s').M K) := fun s' K φ hφ =>
      IH s' K φ (by
        change φ.size < Φ.size + _ + 1
        omega)
    cases S with
    | nec N =>
        exact ⟨mem_retx_of_sat hS hInj hRIX hy t Φ IH,
          sat_retxS_nec_of_memW hS hW hROXD hy t Φ IHb⟩
    | wit N Z =>
        exact ⟨mem_retx_of_sat_wit hS hInj hRWX hy t Φ IH,
          sat_retxS_wit_of_memC hS hROXD hy t Φ IHb⟩

end BData

variable {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)} {hS : ModalSys.BStrong = true}
  (C : StrongChain hS M₀) (E : LimitEx C.toFairChain)

/-- ⭐Rows 3–4: the limit of a strong chain names routes (`lroute`). -/
theorem bdataS_routes (hW : ModalSys.BStrongW = true) : (bdataS C E).Routes hS := by
  intro s i S a t Φ hb h
  obtain ⟨i₁, hii₁, l, hl, hsuf, hmr⟩ := lroute C hW s i hb t Φ h
  refine ⟨i₁, hii₁, .root (.free l.length), (ctxOf_le_of_suffix hsuf).ref (ctxOf_ref_new _ l), ?_⟩
  unfold routeFormula at hmr
  simp only [WFF.mono, WFF.mono_mono, Term.weaken, Term.mono_mono] at hmr ⊢
  exact hmr

/-- ⭐⭐**The limit of a strong chain has the strong B cases of the truth lemma**: from its
    returning children of every kind (rows 1–2), or through its doubly witnessed ones (rows
    3–4). -/
theorem bdataS_strongTruth (hB : ModalSys.B = true) :
    ∀ hS' : ModalSys.BStrong = true, (bdataS C E).StrongTruth hS' := fun _ => by
  cases hW : ModalSys.BStrongW with
  | false =>
      exact BData.strongTruth_of hS hB (bdataS_imgInj C E) (bdataS_cxFresh C E)
        (bdataS_retIn C E) (bdataS_retInX C E) (bdataS_retInW C E) (bdataS_retInWX C E)
        (bdataS_retOutC C E hW) (bdataS_retOutXC C E hW) (bdataS_retOutDC C E hW)
        (bdataS_retOutXDC C E)
  | true =>
      exact BData.strongTruth_ofW hS hB hW (bdataS_imgInj C E) (bdataS_cxFresh C E)
        (bdataS_retIn C E) (bdataS_retInX C E) (bdataS_retInW C E) (bdataS_retInWX C E)
        (bdataS_routes C E hW) (bdataS_retOutXDC C E)

end BArrow

end V12M
