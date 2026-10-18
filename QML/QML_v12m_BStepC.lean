import QML.QML_v12m_BRetChildXDC

/-!
# QML v12m — strong B with T: committing a root with its companions (stage 4)

Committing the source's root `r : R` along an arrow under T needs the new tuple component's
companions to come back as projections of the root's one image (docs §11.21, "Stage 4").  The
existence goes through `r`'s **flat contents** (`flatB`: the contents of its top-level `□`
components, of type `R.bcB false`), bound as one necessary object, packed with the old tuple
(`packCC`), its companions named (`ret_compS`), and mapped to the tuple shape by `tupCG`.

* `tupCRT`, `tupCG`: `tupC` for a root of any type, and under a prefix; compositions of `tupC`
  with the companion-aware structural maps (`fstC`, `sndC`, `packCC`), so sound with no new case.
* ⭐`holeAt_tupCG_obj`: read at the flat object, `tupCG`'s object is the tuple object
  `□⟨T, tup r⟩`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

/-! ## A root's flat contents -/

omit [ModalSys.NoFour] in
/-- A root's flat contents: the contents of each top-level `□` component, paired along
    products (`R.bcB false`). -/
def flatB {Γ : Ctx} (u : VarSymb) : (R : VarType) → Γ.ref u = some R →
    Σ a, Term σ Γ.boxIn (R.bcB false) a
  | .Var, _ => ⟨_, .unit⟩
  | .VTypeOne, _ => ⟨_, .unit⟩
  | .VTypeProd X Y, h => ⟨_, .pair (flatB (.step u .fst) X (Ctx.ref_fst_of h)).2
      (flatB (.step u .snd) Y (Ctx.ref_snd_of h)).2⟩
  | .VTypeBox A, h => ⟨_, Term.eta u.inner A (Ctx.ref_inner h)⟩
  | .VTypeDia _, _ => ⟨_, .unit⟩

/-! ## The tuple of a root of any type, as a map of shapes -/

/-- Under T, a root's tuple from its flat contents with all their companions: `tupC` at each
    top-level `□` component, then its `()` dropped; pairs along products. -/
def tupCRT (hT : ModalSys.T = true) : (R : VarType) →
    ShapeMap σ (.boxC (R.bcB false) (R.bcB false).hereChains (VarType.compOk_compsAllB true hT _))
      (.boxC (R.bcB true) (R.bcB true).hereChains (VarType.compOk_compsAllB true hT _))
  | .VTypeBox A => .comp (.tupC A true hT)
      (.sndC .VTypeOne ((VarType.VTypeBox A).bcB true) [] _ (Or.inl rfl)
        (VarType.compOk_compsAllB true hT _))
  | .VTypeProd X Y => .comp
      (.pair
        (.fstC (X.bcB false) (Y.bcB false) _ _ (VarType.compOk_compsAllB true hT _)
          (VarType.compOk_compsAllB true hT _))
        (.sndC (X.bcB false) (Y.bcB false) _ _ (VarType.compOk_compsAllB true hT _)
          (VarType.compOk_compsAllB true hT _)))
      (.comp (.pair (.comp (.fst _ _) (tupCRT hT X)) (.comp (.snd _ _) (tupCRT hT Y)))
        (.packCC (X.bcB true) (Y.bcB true) _ _ (VarType.compOk_compsAllB true hT _)
          (VarType.compOk_compsAllB true hT _)))
  | .Var => .id _
  | .VTypeOne => .id _
  | .VTypeDia _ => .id _

/-- ⭐`tupC` under a prefix `Y`, for a root of any type: from `⟨y, flat contents⟩` with all
    companions to `⟨y, tuple⟩` with all companions.  With T off it is the identity. -/
def tupCG (Y R : VarType) : (b : Bool) → (hb : ModalSys.T = b) →
    ShapeMap σ (.boxC (.VTypeProd Y (R.bcB false))
        ((VarType.VTypeProd Y (R.bcB false)).compsAllB b) (VarType.compOk_compsAllB b hb _))
      (.boxC (.VTypeProd Y (R.bcB b)) ((VarType.VTypeProd Y (R.bcB b)).compsAllB b)
        (VarType.compOk_compsAllB b hb _))
  | false, _ => .id _
  | true, hb => .comp
      (.pair
        (.fstC Y (R.bcB false) _ _ (VarType.compOk_compsAllB true hb _)
          (VarType.compOk_compsAllB true hb _))
        (.comp (.sndC Y (R.bcB false) _ _ (VarType.compOk_compsAllB true hb _)
          (VarType.compOk_compsAllB true hb _)) (tupCRT hb R)))
      (.packCC Y (R.bcB true) _ _ (VarType.compOk_compsAllB true hb _)
        (VarType.compOk_compsAllB true hb _))

/-! ## The maps' objects at concrete necessary objects -/

/-- The first half with its companions, at `□⟨a, b⟩`: `□a`. -/
theorem holeAt_fstC_obj {Γ : Ctx} {X Y : VarType} {csX csY : List (List Step)}
    {hX : X.CompOk csX} {hY : Y.CompOk csY} {a₀ : Ann X} {b₀ : Ann Y} (a : Term σ Γ.boxIn X a₀)
    (b : Term σ Γ.boxIn Y b₀) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair a b))
        (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).obj.2⟩ : Σ e, Term σ Γ (.VTypeBox X) e) =
      ⟨_, Term.boxtm a⟩ := by
  unfold Term.holeAt
  dsimp only [ShapeMap.obj]
  exact sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ a (by
    rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _)]
    rfl))

/-- The second half with its companions, at `□⟨a, b⟩`: `□b`. -/
theorem holeAt_sndC_obj {Γ : Ctx} {X Y : VarType} {csX csY : List (List Step)}
    {hX : X.CompOk csX} {hY : Y.CompOk csY} {a₀ : Ann X} {b₀ : Ann Y} (a : Term σ Γ.boxIn X a₀)
    (b : Term σ Γ.boxIn Y b₀) :
    (⟨_, Term.holeAt (Term.boxtm (Term.pair a b))
        (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).obj.2⟩ : Σ e, Term σ Γ (.VTypeBox Y) e) =
      ⟨_, Term.boxtm b⟩ := by
  unfold Term.holeAt
  dsimp only [ShapeMap.obj]
  exact sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ b (by
    rw [Subst.at_proj _ _ rfl, Subst.box_at_inner_boxtm _ (Subst.at_single_root _ _)]
    rfl))

/-- Packing with companions, at `⟨□a, □b⟩`: `□⟨a, b⟩`. -/
theorem holeAt_packCC_obj {Γ : Ctx} {X Y : VarType} {csX csY : List (List Step)}
    {hX : X.CompOk csX} {hY : Y.CompOk csY} {a₀ : Ann X} {b₀ : Ann Y} (a : Term σ Γ.boxIn X a₀)
    (b : Term σ Γ.boxIn Y b₀) :
    (⟨_, Term.holeAt (Term.pair (Term.boxtm a) (Term.boxtm b))
        (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).obj.2⟩ :
        Σ e, Term σ Γ (.VTypeBox (.VTypeProd X Y)) e) = ⟨_, Term.boxtm (Term.pair a b)⟩ :=
  Term.holeAt_pack a b

/-- ⭐Under T, `tupCRT` read at a root's flat object is the root's tuple object. -/
theorem holeAt_tupCRT_obj (hT : ModalSys.T = true) : ∀ (R : VarType) {Γ : Ctx} (u : VarSymb)
    (hu : Γ.ref u = some R),
    (⟨_, Term.holeAt (Term.boxtm (flatB (σ := σ) u R hu).2) (tupCRT (σ := σ) hT R).obj.2⟩ :
      Σ e, Term σ Γ (.VTypeBox (R.bcB true)) e) = ⟨_, Term.boxtm (tupB u R true hT hu)⟩
  | .VTypeBox A, _, u, hu => by
    dsimp only [tupCRT]
    refine (Term.holeAt_holeAt_sig (Term.eta u (.VTypeBox A) hu) _ _).trans ?_
    refine (sig_holeAt (holeAt_eta_tupC_obj A hu true hT) _).trans ?_
    exact holeAt_sndC_obj _ _
  | .VTypeProd X Y, _, u, hu => by
    dsimp only [tupCRT]
    refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
    refine (sig_holeAt (sig_pair (holeAt_fstC_obj _ _) (holeAt_sndC_obj _ _)) _).trans ?_
    refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
    refine Eq.trans ?_ (holeAt_packCC_obj (csX := (X.bcB true).hereChains)
      (csY := (Y.bcB true).hereChains) (hX := VarType.compOk_compsAllB true hT _)
      (hY := VarType.compOk_compsAllB true hT _) _ _)
    refine sig_holeAt (sig_pair ?_ ?_) _
    · refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_fst _ _) _).trans ?_)
      exact holeAt_tupCRT_obj hT X (.step u .fst) (Ctx.ref_fst_of hu)
    · refine (Term.holeAt_holeAt_sig _ _ _).trans
        ((sig_holeAt (Term.holeAt_pair_snd _ _) _).trans ?_)
      exact holeAt_tupCRT_obj hT Y (.step u .snd) (Ctx.ref_snd_of hu)
  | .Var, _, _, _ => Term.holeAt_eta_root _
  | .VTypeOne, _, _, _ => Term.holeAt_eta_root _
  | .VTypeDia _, _, _, _ => Term.holeAt_eta_root _

/-- With T off, a root's flat contents are its tuple. -/
theorem flatB_tupB_false (hb : ModalSys.T = false) : ∀ (R : VarType) {Γ : Ctx} (u : VarSymb)
    (hu : Γ.ref u = some R),
    (⟨_, tupB (σ := σ) u R false hb hu⟩ : Σ a, Term σ Γ.boxIn (R.bcB false) a) = flatB u R hu
  | .VTypeBox _, _, _, _ => eta_addr_congr (VarSymb.inner_box ModalSys.NoFour.keepOnly).symm _ _
  | .VTypeProd X Y, _, _, hu => sig_pair (flatB_tupB_false hb X _ (Ctx.ref_fst_of hu))
      (flatB_tupB_false hb Y _ (Ctx.ref_snd_of hu))
  | .Var, _, _, _ => rfl
  | .VTypeOne, _, _, _ => rfl
  | .VTypeDia _, _, _, _ => rfl

/-- ⭐**The object identity of a step**: `tupCG` read at `□⟨T, flat contents of u⟩` is
    `□⟨T, tup u⟩`, for either value of the flag. -/
theorem holeAt_tupCG_obj (Y R : VarType) {Γ : Ctx} {y₀ : Ann Y} (T : Term σ Γ.boxIn Y y₀)
    (u : VarSymb) (hu : Γ.ref u = some R) : ∀ (b : Bool) (hb : ModalSys.T = b),
    (⟨_, Term.holeAt (Term.boxtm (Term.pair T (flatB (σ := σ) u R hu).2))
        (tupCG (σ := σ) Y R b hb).obj.2⟩ :
      Σ e, Term σ Γ (.VTypeBox (.VTypeProd Y (R.bcB b))) e) =
      ⟨_, Term.boxtm (Term.pair T (tupB u R b hb hu))⟩
  | false, hb => by
      refine (Term.holeAt_eta_root _).trans (sig_boxtm (sig_pair rfl ?_))
      exact (flatB_tupB_false hb R u hu).symm
  | true, hb => by
    dsimp only [tupCG]
    refine (Term.holeAt_holeAt_sig _ _ _).trans ?_
    refine Eq.trans ?_ (holeAt_packCC_obj (csX := Y.hereChains)
      (csY := (R.bcB true).hereChains) (hX := VarType.compOk_compsAllB true hb _)
      (hY := VarType.compOk_compsAllB true hb _) _ _)
    refine sig_holeAt (sig_pair (holeAt_fstC_obj _ _) ?_) _
    refine (Term.holeAt_holeAt_sig _ _ _).trans ((sig_holeAt (holeAt_sndC_obj _ _) _).trans ?_)
    exact holeAt_tupCRT_obj hb R u hu


/-! ## Existence keeps a theory consistent -/

omit [ModalSys.NoFour] in
/-- Adding a derivable formula keeps a theory consistent. -/
theorem consistent_union_derives {Γ : Ctx} {M : Set (WFF σ Γ 0)} (hM : Theory.Consistent M)
    {φ : WFF σ Γ 0} (hφ : Theory.Derives M φ) : Theory.Consistent (M ∪ {φ}) := fun hd =>
  hM (Derives.trans (fun x hx => hx.elim Theory.Derives.of_mem
    (fun h => by rw [Set.mem_singleton_iff.mp h]; exact hφ)) hd)

omit [ModalSys.NoFour] in
/-- A theory's consistency passes to a subset. -/
theorem consistent_mono {Γ : Ctx} {M M' : Set (WFF σ Γ 0)} (hM : Theory.Consistent M)
    (h : M' ⊆ M) : Theory.Consistent M' := fun ⟨L, hL, p⟩ => hM ⟨L, fun x hx => h (hL x hx), p⟩

omit [ModalSys.NoFour] in
/-- ⭐**A returning possibility's new necessary part is witnessed by a fresh variable**, at any
    shape and leg (`ret_extS`), as `retExt_consistent`. -/
theorem retExtS_consistent {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.Consistent M) (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape)
    {B : VarType} {a : Ann S.flat} (t : Term σ Γ S.flat a)
    (Φ : WFF σ ((O.view.insert (.bnd 0) S.ty).insert (.bnd 1) (.VTypeBox B)) 2)
    (hex : Theory.Derives M (O.retS hS S t (WFF.ex (.VTypeBox B) Φ))) {u : ℕ}
    (hu : Γ.RootFresh (.free u)) :
    Theory.Consistent (WFF.mono (Ctx.le_insert hu.root B) '' M ∪
      {(O.mono (Ctx.le_insert hu.root B)).retS hS (S.ext B)
        (S.extTm (Term.weaken hu.root B t)
          (Term.eta (.root (.free u)) B (Ctx.ref_insert_root Γ (.free u) B))).2
        (WFF.mono ((O.le_view_mono (Ctx.le_insert hu.root B)).insert (.bnd 0) _)
          (WFF.bodySplit (S.extL O.view B).2 (S.extR O.view B).2 Φ))}) := by
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (Ctx.le_insert hu.root B) x) _ Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := hex
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ret_extS hS O t Φ u hu (φ := .bot)
    (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pex)
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hy))

omit [ModalSys.NoFour] in
/-- ⭐**A companion's return is witnessed by a fresh variable** (`ret_compS`). -/
theorem compS_consistent {Γ : Ctx} [Γ.Presented] {M : Set (WFF σ Γ 0)}
    (hM : Theory.Consistent M) (hS : ModalSys.BStrong = true) (O : OutLeg Γ) (S : RShape)
    {A : VarType} {cs : List (List Step)} {h : A.CompOk cs} (p : List Step)
    (h' : A.CompOk (p :: cs)) {a : Ann (S.withNec (.boxC A cs h)).flat}
    (t : Term σ Γ (S.withNec (.boxC A cs h)).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (S.withNec (.boxC A cs h)).ty) 1)
    (hex : Theory.Derives M (O.retS hS (S.withNec (.boxC A cs h)) t Φ)) {u : ℕ}
    (hu : Γ.RootFresh (.free u)) :
    Theory.Consistent (WFF.mono (Ctx.le_insert hu.root ((A.compAt p).getD .VTypeOne)) '' M ∪
      {(O.mono (Ctx.le_insert hu.root _)).retS hS (S.withNec (.boxC A (p :: cs) h'))
        (RShape.compTm A cs h p h' S (Term.weaken hu.root _ t)
          (Term.eta (.root (.free u)) _ (Ctx.ref_insert_root Γ (.free u) _))).2
        (WFF.mono ((O.le_view_mono (Ctx.le_insert hu.root _)).insert (.bnd 0) _)
          (WFF.bodyRepl (RShape.compL O.view A cs h p h' S).2 Φ))}) := by
  rintro ⟨Δ, hΔ, p'⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (Ctx.le_insert hu.root ((A.compAt p).getD .VTypeOne)) x) _ Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p'
  obtain ⟨Δ₁, hΔ₁, ⟨pex⟩⟩ := hex
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ret_compS hS O S p h' t Φ u hu (φ := .bot)
    (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pex)
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hy))

/-! ## Naming a list of companions -/

section Names

variable (hS : ModalSys.BStrong = true) (S : RShape) (A : VarType) (cs : List (List Step))
  (h : A.CompOk cs)

/-- The types of the returns of a list of companions, newest first. -/
def compsTys (A : VarType) : List (List Step) → List VarType
  | [] => []
  | q :: Q => ((A.compAt q).getD .VTypeOne) :: compsTys A Q

/-- The leg after naming a list of companions. -/
def legQ {l : List VarType} (O : OutLeg (ctxOf l)) :
    (Q : List (List Step)) → OutLeg (ctxOf (compsTys A Q ++ l))
  | [] => O
  | q :: Q => (legQ O Q).mono (ctxOf_le_append [((A.compAt q).getD .VTypeOne)] _)

omit [ModalSys] [ModalSys.NoFour] in
theorem legQ_le {l : List VarType} : ∀ (Q : List (List Step)),
    (ctxOf l).Le (ctxOf (compsTys A Q ++ l))
  | [] => Ctx.Le.refl _
  | q :: Q => (legQ_le Q).trans (ctxOf_le_append [((A.compAt q).getD .VTypeOne)] _)

/-- The value after naming a list of companions: each new return a fresh root. -/
def valQ {l : List VarType} {a : Ann (S.withNec (.boxC A cs h)).flat}
    (t : Term σ (ctxOf l) (S.withNec (.boxC A cs h)).flat a) :
    (Q : List (List Step)) → (hQ : A.CompOk (Q ++ cs)) →
    Σ c, Term σ (ctxOf (compsTys A Q ++ l)) (S.withNec (.boxC A (Q ++ cs) hQ)).flat c
  | [], _ => ⟨_, t⟩
  | q :: Q, hQ => RShape.compTm A (Q ++ cs) hQ.tail q hQ S
      (Term.mono (ctxOf_le_append [((A.compAt q).getD .VTypeOne)] _) (valQ t Q hQ.tail).2)
      (Term.eta (.root (.free (compsTys A Q ++ l).length)) _ (ctxOf_ref_new _ _))

/-- The body after naming a list of companions. -/
def bodyQ {l : List VarType} (O : OutLeg (ctxOf l))
    (Φ : WFF σ (O.view.insert (.bnd 0) (S.withNec (.boxC A cs h)).ty) 1) :
    (Q : List (List Step)) → (hQ : A.CompOk (Q ++ cs)) →
    WFF σ ((legQ A O Q).view.insert (.bnd 0) (S.withNec (.boxC A (Q ++ cs) hQ)).ty) 1
  | [], _ => Φ
  | q :: Q, hQ => WFF.mono
      (((legQ A O Q).le_view_mono (ctxOf_le_append [((A.compAt q).getD .VTypeOne)] _)).insert
        (.bnd 0) _)
      (WFF.bodyRepl (RShape.compL (legQ A O Q).view A (Q ++ cs) hQ.tail q hQ S).2
        (bodyQ O Φ Q hQ.tail))

omit [ModalSys.NoFour] in
/-- ⭐**Naming a list of companions keeps a theory consistent**: each by `compS_consistent`. -/
theorem compsS_consistent {l : List VarType} (O : OutLeg (ctxOf l))
    {a : Ann (S.withNec (.boxC A cs h)).flat}
    (t : Term σ (ctxOf l) (S.withNec (.boxC A cs h)).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (S.withNec (.boxC A cs h)).ty) 1)
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.Consistent M)
    (hex : Theory.Derives M (O.retS hS (S.withNec (.boxC A cs h)) t Φ)) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)),
      Theory.Consistent (WFF.mono (legQ_le A Q) '' M ∪
        {(legQ A O Q).retS hS (S.withNec (.boxC A (Q ++ cs) hQ)) (valQ S A cs h t Q hQ).2
          (bodyQ S A cs h O Φ Q hQ)})
  | [], _ => by
      rw [show WFF.mono (legQ_le A (l := l) []) '' M = M from by
        ext x
        simp only [Set.mem_image]
        exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, WFF.mono_refl]; exact hy,
          fun hx => ⟨x, hx, WFF.mono_refl _ _⟩⟩]
      exact consistent_union_derives hM hex
  | q :: Q, hQ => by
      have ih := compsS_consistent O t Φ hM hex Q hQ.tail
      have hc := compS_consistent ih hS (legQ A O Q) S q hQ (valQ S A cs h t Q hQ.tail).2
        (bodyQ S A cs h O Φ Q hQ.tail) (Theory.Derives.of_mem (Or.inr rfl))
        (ctxOf_fresh (l := compsTys A Q ++ l) le_rfl)
      refine consistent_mono hc (Set.union_subset_union ?_ subset_rfl)
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨WFF.mono (legQ_le A Q) x, Or.inl ⟨x, hx, rfl⟩, ?_⟩
      rw [WFF.mono_mono]

end Names

/-! ## The source's `∃`-introduction for a root's flat contents -/

/-- A body read at the far end `v` with its bound object any necessary term `X` of `v`. -/
def liftBodyAt {lv clt : List VarType} {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt)
    {Z : VarType} {x : Ann Z} (X : Term σ (ctxOf lv) Z x)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) Z) 1) : WFF σ (ctxOf lv) 0 :=
  WFF.subst (Subst.setIdx (arrowIdx imgt) (.bnd 0) (.tm X))
    ((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (.tm X))
    (Subst.ok_set (ok_arrowS himgt) rfl)
    (Subst.coh_set (ok_arrowS himgt) (coh_arrowS himgt)
      ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _) Ctx.NoSlots.slots Φ

theorem liftBody_eq_liftBodyAt {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx cls clt) 1) :
    liftBody hs himgt Φ = liftBodyAt himgt
      (Term.boxtm (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2)) Φ :=
  rfl

omit [ModalSys.NoFour] in
/-- ⭐**A body read at a re-read slot**, for any substitution of the view: re-reading the slot
    through a hole term `O`, then setting the slot to `X`, is setting it to `O(X)`. -/
theorem subst_set_bodyRepl {V Δ : Ctx} [V.NoSlots] {ι : VarSymb → VarSymb} (α : Subst σ Δ)
    (hα : Subst.Ok V α) (hcα : Subst.Coh ι V α) (hΔ : Δ.SlotsFrom 0) {Z Z' : VarType}
    {x : Ann Z} (X : Term σ Δ Z x) {o : Ann Z'}
    (O : Term σ (Ctx.empty.insert (.bnd 0) Z) Z' o)
    (Φ : WFF σ (V.insert (.bnd 0) Z') 1) :
    WFF.subst (Subst.setIdx ι (.bnd 0) (.tm X)) (α.set (.bnd 0) (.tm X)) (Subst.ok_set hα rfl)
        (Subst.coh_set hα hcα ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) hΔ
        (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) O) Φ) =
      WFF.subst (Subst.setIdx ι (.bnd 0) (.tm (Term.holeAt X O)))
        (α.set (.bnd 0) (.tm (Term.holeAt X O))) (Subst.ok_set hα rfl)
        (Subst.coh_set hα hcα ((Ctx.NoSlots.slots (Γ := V)).rootFresh (le_refl 0)) rfl)
        ((Ctx.NoSlots.slots (Γ := V)).insert _) hΔ Φ := by
  unfold WFF.bodyRepl
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Φ
  refine Subst.sim_of fun v T hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : T = Z' := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.comp]
    refine SubE.sim_tm_sigma ?_
    rw [Term.subst_mono]
    unfold Term.holeAt
    refine Term.subst_congr _ _ _ _ _ _ (Subst.sim_of fun w U _ hw => ?_) O
    by_cases hwr : w = .root (.bnd 0)
    · subst hwr
      rw [Subst.set_root]
      rw [show Subst.single (σ := σ) (Δ := Δ) (.bnd 0) (.tm X) (.root (.bnd 0)) = .tm X
        from if_pos rfl]
      exact .refl _
    · change (if w = VarSymb.root (.bnd 0) then _ else Ctx.empty w) = _ at hw
      rw [if_neg hwr] at hw
      cases hw
  · dsimp only [Subst.comp]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr, show (Subst.idS σ _ v) = .ren v from rfl,
      SubE.comp_ren, Subst.at_nonproj _ hlp, Subst.set_ne _ _ hvr]
    exact .refl _

/-- A body read at a re-read slot, at the far end of an arrow. -/
theorem liftBodyAt_bodyRepl {lv clt : List VarType} {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {Z Z' : VarType} {x : Ann Z}
    (X : Term σ (ctxOf lv) Z x) {o : Ann Z'}
    (O : Term σ (Ctx.empty.insert (.bnd 0) Z) Z' o)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) Z') 1) :
    liftBodyAt himgt X (WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _) O) Φ) =
      liftBodyAt himgt (Term.holeAt X O) Φ :=
  subst_set_bodyRepl _ (ok_arrowS himgt) (coh_arrowS himgt) _ X O Φ

section FlatRoot

variable {lv cls clt : List VarType} {B : VarType}

/-- The pair of the older roots' necessary object and a new slot of type `□B`, in the view of
    the `∃` it is bound by. -/
def midTermB (hs : cls <:+ lv) (B : VarType) :
    Σ a, Term σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox B)) (.VTypeBox (.VTypeProd (bcT cls) B))
      a :=
  ⟨_, .boxtm (.pair
    (Term.mono ((Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _).boxIn)
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))
    (Term.eta (VarSymb.root (.bnd 0)).inner B
      (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))))⟩

/-- The middle substitution for a new slot of type `□B`. -/
abbrev midSB (hs : cls <:+ lv) (B : VarType) (imgt : ℕ → ℕ) :
    Subst σ ((ctxOf lv).insert (.bnd 0) (.VTypeBox B)) :=
  ((arrowS σ (ctxOf lv) imgt).mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := ctxOf lv)).root _)).set
    (.bnd 0) (.tm (midTermB hs B).2)

theorem ok_midSB (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Ok ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B)))
      (midSB (σ := σ) hs B imgt) :=
  Subst.ok_set (Subst.ok_mono (ok_arrowS himgt) _) rfl

theorem coh_midSB (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) :
    Subst.Coh (Subst.setIdx (arrowIdx imgt) (.bnd 0) (.tm (midTermB (σ := σ) hs B).2))
      ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B)))
      (midSB (σ := σ) hs B imgt) :=
  Subst.coh_set (Subst.ok_mono (ok_arrowS himgt) _) (Subst.coh_mono (coh_arrowS himgt) _)
    ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl

/-- ⭐**A new component's body is an `∃`-introduction of the older roots' body**, for any new
    component: read at the source, the split body `∃e. pairUp Ψ` over the older roots, at the
    necessary object `□w`, is `Ψ` read at `□⟨tupT cls, w⟩`. -/
theorem liftBody_ex_pairUp_memB {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M)
    (hs : cls <:+ lv) {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) {w₀ : Ann B}
    (w : Term σ (ctxOf lv).boxIn B w₀)
    (Ψ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B))) 1)
    (h : liftBodyAt himgt (Term.boxtm (Term.pair
      (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT (σ := σ) cls).2) w)) Ψ ∈ M) :
    liftBody hs himgt (WFF.ex (.VTypeBox B) (WFF.pairUp Ψ)) ∈ M := by
  refine hM.closed ⟨[_], fun x hx => by rw [List.mem_singleton.mp hx]; exact h, ⟨?_⟩⟩
  refine Proof.ex_intro _ (Term.boxtm w) (Proof.conv ?_ (Proof.lookup List.mem_cons_self))
  refine Eq.symm ?_
  unfold WFF.instantiate WFF.substRoot WFF.pairUp
  have hfr : (ctxOf lv) (.root (.bnd 0)) = none := (Ctx.NoSlots.slots (Γ := ctxOf lv)).root
  have simA : Subst.Sim ((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cls) B)))
      (midSB (σ := σ) hs B imgt)
      (((Subst.idS σ (((ctxOf clt).boxIn.insert (.bnd 0) (.VTypeBox (bcT cls))).insert
          (.bnd 1) (.VTypeBox B))).set (.bnd 0) (.tm (pairItem (bcT cls) B))).comp
        (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox B) hfr)
        (Subst.ok_under (Subst.ok_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs)
          (ok_arrowS himgt) rfl) _ hfr)
        (Subst.coh_under (Subst.ok_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs)
            (ok_arrowS himgt) rfl)
          (Subst.coh_set (T := .VTypeBox (bcT cls)) (e := liftEntry hs) (ok_arrowS himgt)
            (coh_arrowS himgt)
            ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).rootFresh (le_refl 0)) rfl)
          ((Ctx.NoSlots.slots (Γ := (ctxOf clt).boxIn)).insert _) _ hfr)) := by
    refine Subst.sim_of fun v U hlp hv => ?_
    by_cases hvr : v = .root (.bnd 0)
    · subst hvr
      obtain rfl : U = .VTypeBox (.VTypeProd (bcT cls) B) := by
        change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
        rw [if_pos rfl] at hv
        exact (Option.some.inj hv).symm
      dsimp only [Subst.comp]
      rw [show midSB (σ := σ) hs B imgt (.root (.bnd 0)) = .tm (midTermB hs B).2 from
        Subst.set_root _ _ _]
      have h0 : (((arrowS σ (ctxOf lv) imgt).set (.bnd 0) (liftEntry hs)).under (0 + 1) 0
          (.VTypeBox B) hfr).at (.root (.bnd 0)) =
          .tm (Term.boxtm (Term.mono ((Ctx.le_insert hfr _).boxIn)
            (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2))) := by
        rw [Subst.at_under_ne _ _ _ (fun h => by cases h)]
        change SubE.mono _ (Subst.set _ _ _ (.root (.bnd 0))) = _
        rw [Subst.set_root]
        rfl
      dsimp only [SubE.comp]
      exact SubE.sim_tm_sigma (sig_boxtm (sig_pair
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0))
        (Term.subst_eta_renAt _ _ _ _ _ _ _ (Ctx.ref_inner (Ctx.ref_insert_root _ (.bnd 0) _))
          (Subst.box_at_inner_ren _ (Subst.under_at_slot _ (0 + 1) 0 _ hfr))))).symm
    · obtain ⟨u, rfl, hu⟩ := body_itemT hv hvr
      dsimp only [Subst.comp]
      rw [show midSB (σ := σ) hs B imgt (.step u .box) =
        SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
        Subst.set_ne _ _ hvr]
      dsimp only [Subst.idS, SubE.comp]
      rw [Subst.at_nonproj _ hlp]
      dsimp only [Subst.under]
      rw [if_neg (fun h => by cases h), Subst.set_ne _ _ hvr]
      exact .refl _
  rw [WFF.subst_comp _ _ (midSB hs B imgt) _ _ _ _ (ok_midSB hs himgt) (coh_midSB hs himgt)
    _ _ _ simA]
  unfold liftBodyAt
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (.VTypeProd (bcT cls) B) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp]
    rw [show midSB (σ := σ) hs B imgt (.root (.bnd 0)) = .tm (midTermB hs B).2 from
      Subst.set_root _ _ _]
    dsimp only [SubE.comp]
    have hsg : (Subst.single (σ := σ) (.bnd 0) (.tm (Term.boxtm w))).at (.root (.bnd 0)) =
        .tm (Term.boxtm w) := by
      change Subst.single (.bnd 0) _ (.root (.bnd 0)) = _
      exact if_pos rfl
    have hsim : Subst.Sim (ctxOf cls).boxIn
        (Subst.single (σ := σ) (Δ := ctxOf lv) (.bnd 0) (.tm (Term.boxtm w))).box
        (Subst.idS σ (ctxOf lv).boxIn) := by
      refine Subst.sim_of fun v U _ hv => ?_
      obtain ⟨u, rfl, hu⟩ := boxIn_item hv
      obtain ⟨r, hr, _, _⟩ := ref_rt hu
      change SubE.Sim U ((Subst.single _ _).at u).unbox (.ren (.step u .box))
      rw [Subst.single_at_ne (by rw [hr]; exact fun h => by cases h)]
      change SubE.Sim U (.ren u.inner) _
      rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
      exact .refl _
    refine SubE.sim_tm_sigma (sig_boxtm (sig_pair ?_
      (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ hsg)))).symm
    try rw [Term.mono_mono]
    rw [Term.subst_mono]
    exact (Term.subst_congr _ _ _ (Subst.ok_idS_le (ctxOf_le_of_suffix hs).boxIn) _
      (Subst.coh_idS_le (ctxOf_le_of_suffix hs).boxIn) hsim _).trans
      (Term.subst_idS_mono (ctxOf_le_of_suffix hs).boxIn _ _ _)
  · obtain ⟨u, rfl, hu⟩ := body_itemT hv hvr
    obtain ⟨r, hr, _, _⟩ := ref_rt hu
    dsimp only [Subst.comp]
    rw [show midSB (σ := σ) hs B imgt (.step u .box) =
      SubE.mono _ (arrowS σ (ctxOf lv) imgt (.step u .box)) from Subst.set_ne _ _ hvr,
      Subst.set_ne _ _ hvr]
    change SubE.Sim U (.ren (itemImg imgt u)) ((Subst.single _ _).at (itemImg imgt u))
    rw [Subst.single_at_ne (by rw [itemAt_rt, hr]; exact fun h => by cases h)]
    exact .refl _

end FlatRoot

/-- `liftBodyAt` depends on its object only as a dependent pair. -/
theorem liftBodyAt_congr {lv clt : List VarType} {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) {Z : VarType} {x x' : Ann Z}
    {X : Term σ (ctxOf lv) Z x} {X' : Term σ (ctxOf lv) Z x'}
    (h : (⟨x, X⟩ : Σ c, Term σ (ctxOf lv) Z c) = ⟨x', X'⟩)
    (Φ : WFF σ ((ctxOf clt).boxIn.insert (.bnd 0) Z) 1) :
    liftBodyAt himgt X Φ = liftBodyAt himgt X' Φ := by
  cases h
  rfl

/-- The source's next root's tuple, from its flat contents (`tupCG`'s object). -/
abbrev flatBody {V : Ctx} [V.NoSlots] {cl : List VarType} (A : VarType)
    (Φ : WFF σ (V.insert (.bnd 0) (.VTypeBox (bcT (A :: cl)))) 1) :
    WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd (bcT cl) (A.bcB false)))) 1 :=
  WFF.bodyRepl (Term.mono ((Ctx.empty_le _).insert (.bnd 0) _)
    (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl).obj.2) Φ

/-- The source's tuple with the next root is the old tuple paired with the root's items. -/
theorem tupT_cons_mono {lv cl : List VarType} {A : VarType} (hs' : (A :: cl) <:+ lv) :
    (⟨_, Term.boxtm (Term.mono (ctxOf_le_of_suffix hs').boxIn (tupT (σ := σ) (A :: cl)).2)⟩ :
      Σ c, Term σ (ctxOf lv) (.VTypeBox (bcT (A :: cl))) c) =
      ⟨_, Term.boxtm (Term.pair
        (Term.mono (ctxOf_le_of_suffix ((List.suffix_cons A cl).trans hs')).boxIn
          (tupT (σ := σ) cl).2)
        (tupB (.root (.free cl.length)) A ModalSys.T rfl
          ((ctxOf_le_of_suffix hs').ref (ctxOf_ref_new A cl))))⟩ := by
  refine sig_boxtm (sig_pair ?_ ?_)
  · exact congrArg (Sigma.mk _) (Term.mono_mono _ _ _)
  · exact congrArg (Sigma.mk _) (mono_tupB (ctxOf_le_of_suffix hs') _ _ _ _ _)

/-- ⭐**The source's `∃`-introduction for its next root, under T**: a body over the roots with the
    next one, true at the source, gives `∃e. pairUp (flatBody Φ)` over the older roots, witnessed
    by the next root's flat object (`holeAt_tupCG_obj`). -/
theorem liftBody_ex_flat_mem {lv cl clt : List VarType} {A : VarType}
    {M : Set (WFF σ (ctxOf lv) 0)} (hM : Theory.IsMCS M) (hs' : (A :: cl) <:+ lv)
    {imgt : ℕ → ℕ} (himgt : ImgOk clt (ctxOf lv) imgt) (Φ : WFF σ (bodyCtx (A :: cl) clt) 1)
    (h : liftBody hs' himgt Φ ∈ M) :
    liftBody ((List.suffix_cons A cl).trans hs') himgt
      (WFF.ex (.VTypeBox (A.bcB false)) (WFF.pairUp (flatBody A Φ))) ∈ M := by
  have hr := (ctxOf_le_of_suffix hs').ref (ctxOf_ref_new A cl)
  refine liftBody_ex_pairUp_memB hM ((List.suffix_cons A cl).trans hs') himgt
    (flatB (σ := σ) (.root (.free cl.length)) A hr).2 (flatBody A Φ) ?_
  rw [liftBodyAt_bodyRepl, liftBodyAt_congr himgt (holeAt_tupCG_obj (bcT cl) A _ _ hr _ rfl),
    ← liftBodyAt_congr himgt (tupT_cons_mono hs')]
  exact h

/-- ⭐Splitting a weakened paired body along a product slot is re-reading the weakened body
    through `packCC`'s object: both put `□⟨d₀.inner, d₁.inner⟩` in the slot. -/
theorem WFF.bodySplit_mono_pairUp_packCC {V V' : Ctx} [V.NoSlots] [V'.NoSlots] (h : V.Le V')
    {X Y : VarType} {csX : List (List Step)} {hX : X.CompOk csX}
    (Ψ : WFF σ (V.insert (.bnd 0) (.VTypeBox (.VTypeProd X Y))) 1) :
    WFF.bodySplit
      (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) (Ctx.ref_fst_of
        (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y)))))
      (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) (Ctx.ref_snd_of
        (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y)))))
      (WFF.mono ((h.insert (.bnd 0) _).insert (.bnd 1) _) (WFF.pairUp Ψ)) =
      WFF.bodyRepl (Term.mono ((Ctx.empty_le V').insert (.bnd 0) _)
        (ShapeMap.packCC (σ := σ) X Y csX [] hX (Or.inl rfl)).obj.2)
        (WFF.mono (h.insert (.bnd 0) _) Ψ) := by
  unfold WFF.bodySplit WFF.pairUp WFF.bodyRepl
  rw [WFF.mono_subst _ _ _ _ _ _ (((Ctx.NoSlots.slots (Γ := V')).insert _).insert _),
    WFF.subst_mono]
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ Ψ
  refine Subst.sim_of fun v U hlp hv => ?_
  by_cases hvr : v = .root (.bnd 0)
  · subst hvr
    obtain rfl : U = .VTypeBox (.VTypeProd X Y) := by
      change (if VarSymb.root (.bnd 0) = .root (.bnd 0) then _ else V _) = _ at hv
      rw [if_pos rfl] at hv
      exact (Option.some.inj hv).symm
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_root, Subst.set_root]
    dsimp only [SubE.mono, SubE.comp]
    rw [Term.subst_mono]
    have h0 : (((Subst.idS σ (V'.insert (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y)))).set
        (.bnd 0) (.tm (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) (Ctx.ref_fst_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))))).set
        (.bnd 1) (.tm (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) (Ctx.ref_snd_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))))).at
        (.root (.bnd 0)) = .tm (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) (Ctx.ref_fst_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))) := by
      rw [Subst.at_nonproj _ rfl, Subst.set_ne _ _ (fun h => by cases h), Subst.set_root]
    have h1 : (((Subst.idS σ (V'.insert (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y)))).set
        (.bnd 0) (.tm (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) (Ctx.ref_fst_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))))).set
        (.bnd 1) (.tm (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) (Ctx.ref_snd_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))))).at
        (.root (.bnd 1)) = .tm (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) (Ctx.ref_snd_of
          (Ctx.ref_insert_root V' (.bnd 0) (.VTypeProd (.VTypeBox X) (.VTypeBox Y))))) := by
      rw [Subst.at_nonproj _ rfl, Subst.set_root]
    refine SubE.sim_tm_sigma (sig_boxtm (sig_pair
      ((congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)).trans
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h0)).symm)
      ((congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _)).trans
        (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm _ h1)).symm)))
  · have hv' : V v = some U := by
      change (if v = VarSymb.root (.bnd 0) then _ else V v) = _ at hv
      rwa [if_neg hvr] at hv
    have hv1 : v ≠ .root (.bnd 1) := fun h => by
      subst h
      rw [((Ctx.NoSlots.slots (Γ := V)).rootFresh (Nat.zero_le 1)).root] at hv'
      cases hv'
    dsimp only [Subst.comp, Subst.mono]
    rw [Subst.set_ne _ _ hvr, Subst.set_ne _ _ hvr]
    dsimp only [Subst.idS, SubE.mono, SubE.comp]
    rw [Subst.at_nonproj _ hlp, Subst.set_ne _ _ hv1, Subst.set_ne _ _ hvr]
    exact .refl _

/-! ## Bodies after naming companions, at a necessary shape -/

omit [ModalSys.NoFour] in
/-- Re-reading the slot through its own η-expansion is no change. -/
theorem WFF.bodyRepl_eta' {V : Ctx} [V.NoSlots] {T : VarType} (Φ : WFF σ (V.insert (.bnd 0) T) 1) :
    WFF.bodyRepl (Term.eta (.root (.bnd 0)) T (Ctx.ref_insert_root V (.bnd 0) T)) Φ = Φ := by
  have e := Term.mono_eta (σ := σ) ((Ctx.empty_le V).insert (.bnd 0) T) (.root (.bnd 0)) T
    (Ctx.ref_insert_root _ _ _)
  rw [← e]
  exact WFF.bodyRepl_eta Φ

omit [ModalSys.NoFour] in
theorem legQ_view_le (A : VarType) {l : List VarType} (O : OutLeg (ctxOf l)) :
    ∀ (Q : List (List Step)), O.view.Le (legQ A O Q).view
  | [] => Ctx.Le.refl _
  | _ :: Q => (legQ_view_le A O Q).trans ((legQ A O Q).le_view_mono _)

omit [ModalSys.NoFour] in
/-- At a necessary shape naming companions leaves the body as it was, weakened. -/
theorem bodyQ_nec (N : NShape) (A : VarType) (cs : List (List Step)) (h : A.CompOk cs)
    {l : List VarType} (O : OutLeg (ctxOf l))
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)),
      bodyQ (.nec N) A cs h O Φ Q hQ = WFF.mono ((legQ_view_le A O Q).insert (.bnd 0) _) Φ
  | [], _ => (WFF.mono_refl _ _).symm
  | q :: Q, hQ => by
      change WFF.mono _ (WFF.bodyRepl (Term.eta (.root (.bnd 0)) (.VTypeBox A)
        (Ctx.ref_insert_root _ (.bnd 0) _)) (bodyQ (.nec N) A cs h O Φ Q hQ.tail)) = _
      rw [WFF.bodyRepl_eta', bodyQ_nec N A cs h O Φ Q hQ.tail, WFF.mono_mono]

omit [ModalSys.NoFour] in
/-- Substituting a fresh root's value leaves a formula from before it was weakened. -/
theorem subst_single_mono {lt bigl : List VarType} (hle : (ctxOf lt).Le (ctxOf bigl))
    {B : VarType} {e : SubE σ (ctxOf bigl)}
    (hθ : Subst.Ok (ctxOf (B :: lt)) (Subst.single (.free lt.length) e))
    (hc : Subst.Coh (Subst.singleIdx (.free lt.length) e) (ctxOf (B :: lt))
      (Subst.single (.free lt.length) e))
    (x : WFF σ (ctxOf lt) 0) :
    WFF.subst (Subst.singleIdx (.free lt.length) e) (Subst.single (.free lt.length) e) hθ hc
        Ctx.NoSlots.slots Ctx.NoSlots.slots (WFF.mono (ctxOf_le_append [B] lt) x) =
      WFF.mono hle x := by
  rw [WFF.subst_mono _ _ _ _ Ctx.NoSlots.slots]
  refine WFF.subst_ren hle _ _ _ _ _ (fun v T hv => Subst.single_at_ne ?_) x
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hv
  rw [hr]
  exact fun h => absurd (Root.free.inj h) (Nat.ne_of_lt hlt)

/-! ## The chain of a step: its values -/

section ChainVals

variable {lt cl : List VarType} {img : ℕ → ℕ} (A : VarType) (himg : ImgOk cl (ctxOf lt) img)

/-- The companions of the flat contents to be named, under `snd`. -/
abbrev stepQ (A : VarType) : List (List Step) :=
  ((A.bcB false).compsAllB ModalSys.T).map (Step.snd :: ·)

omit [ModalSys.NoFour] in
theorem stepQ_ok (cl : List VarType) (A : VarType) :
    (VarType.VTypeProd (bcT cl) (A.bcB false)).CompOk
      (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) []) := by
  cases hT : ModalSys.T with
  | false =>
      left
      simp [stepQ, VarType.compsAllB, pairComps, hT]
  | true =>
      refine Or.inr ⟨hT, fun p hp => ?_, List.Nodup.append
        ((compsAllB_nodup _ _).map (fun _ _ h => (List.cons.inj h).2))
        (pairComps_nodup (compsAllB_nodup _ _) List.nodup_nil) (by simp [List.Disjoint])⟩
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rw [hT] at hq
        exact VarType.compAt_hereChains _ q hq
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact VarType.compAt_hereChains _ q hq
        · simp at hp

omit [ModalSys.NoFour] in
theorem stepQ_sub (cl : List VarType) (A : VarType) :
    ∀ p ∈ (VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T,
      p ∈ stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) [] := by
  unfold stepQ
  generalize ModalSys.T = b
  cases b with
  | false => intro p hp; cases hp
  | true =>
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact List.mem_append_right _ (List.mem_append_left _ hp)
      · exact List.mem_append_left _ hp

/-- The value after `ret_extS`: the old tuple's value and the flat contents' fresh return. -/
def stepV₁ : Σ c, Term σ (ctxOf (A.bcB false :: lt))
    ((RShape.nec (tupShape ModalSys.T rfl cl)).ext (A.bcB false)).flat c :=
  (RShape.nec (tupShape ModalSys.T rfl cl)).extTm
    (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false)
      (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2)
    (Term.eta (.root (.free lt.length)) (A.bcB false) (ctxOf_ref_new _ _))

/-- The value after packing. -/
def stepV₂ : Σ c, Term σ (ctxOf (A.bcB false :: lt))
    ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsFlat
      (pairComps ((bcT cl).compsAllB ModalSys.T) [])) c :=
  ⟨_, Term.holeRead (stepV₁ A himg).2
    (ShapeMap.packCC (σ := σ) (bcT cl) (A.bcB false) _ []
      (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl)).val.2⟩

/-- The value after naming the flat contents' companions. -/
def stepV₃ :=
  valQ (.nec (tupShape ModalSys.T rfl cl)) (VarType.VTypeProd (bcT cl) (A.bcB false))
    (pairComps ((bcT cl).compsAllB ModalSys.T) [])
    (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))
    (stepV₂ (σ := σ) A himg).2 (stepQ A) (stepQ_ok cl A)

/-- ⭐The value of a step's chain, at the tuple shape. -/
def stepV₅ : Σ c, Term σ (ctxOf (compsTys (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A) ++
    A.bcB false :: lt)) ((bcT (A :: cl)).compsFlat ((bcT (A :: cl)).compsAllB ModalSys.T)) c :=
  ⟨_, Term.holeRead (Term.holeRead (stepV₃ (σ := σ) A himg).2
    (ShapeMap.subC (σ := σ) (VarType.VTypeProd (bcT cl) (A.bcB false)) _
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T) (stepQ_ok cl A)
      (VarType.compOk_compsAllB _ rfl _) (stepQ_sub cl A)).val.2)
    (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl).val.2⟩

end ChainVals

/-! ## Consistency bookkeeping -/

omit [ModalSys.NoFour] in
/-- Adding what the last added formula proves keeps a theory consistent. -/
theorem consistent_step {Γ : Ctx} {M : Set (WFF σ Γ 0)} {φ ψ : WFF σ Γ 0}
    (hM : Theory.Consistent (M ∪ {φ})) (p : Proof σ Γ [φ] ψ) :
    Theory.Consistent ((M ∪ {φ}) ∪ {ψ}) :=
  consistent_union_derives hM
    ⟨[φ], fun x hx => by rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩

omit [ModalSys.NoFour] in
/-- ⭐A theory is consistent if a substitution sends it into a consistent one. -/
theorem consistent_of_subst {Γ Γ' : Ctx} [Γ'.Presented] {M : Set (WFF σ Γ 0)}
    {M' : Set (WFF σ Γ' 0)} (hM' : Theory.Consistent M') {ι : VarSymb → VarSymb}
    (θ : Subst σ Γ') (hθ : Subst.Ok Γ θ) (hc : Subst.Coh ι Γ θ) (hΓ : Γ.SlotsFrom 0)
    (hsub : ∀ x ∈ M, WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots x ∈ M') :
    Theory.Consistent M := by
  rintro ⟨L, hL, ⟨p⟩⟩
  exact hM' ⟨L.map (WFF.subst ι θ hθ hc hΓ Ctx.NoSlots.slots), fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hsub y (hL y hy), ⟨Proof.subst p θ hθ hc hΓ⟩⟩

omit [ModalSys.NoFour] in
/-- ⭐**Naming a list of companions along a leg keeps a theory consistent**, at a necessary shape
    the body only weakened (`compL` is the slot's η there). -/
theorem compsS_consistent_leg (hS : ModalSys.BStrong = true) (N : NShape) (A : VarType)
    (cs : List (List Step)) (h : A.CompOk cs) {l : List VarType} (O : OutLeg (ctxOf l))
    {a : Ann ((RShape.nec N).withNec (.boxC A cs h)).flat}
    (t : Term σ (ctxOf l) ((RShape.nec N).withNec (.boxC A cs h)).flat a)
    (Φ : WFF σ (O.view.insert (.bnd 0) (.VTypeBox A)) 1)
    {M : Set (WFF σ (ctxOf l) 0)} (hM : Theory.Consistent M)
    (hex : Theory.Derives M (O.retS hS (.nec (.boxC A cs h)) t Φ)) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)),
      Theory.Consistent (WFF.mono (legQ_le A Q) '' M ∪
        {(O.mono (legQ_le A Q)).retS hS (.nec (.boxC A (Q ++ cs) hQ))
          (valQ (.nec N) A cs h t Q hQ).2
          (WFF.mono ((O.le_view_mono (legQ_le A Q)).insert (.bnd 0) _) Φ)})
  | [], hQ => by
      rw [show WFF.mono (legQ_le A (l := l) []) '' M = M from by
        ext x
        simp only [Set.mem_image]
        exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, WFF.mono_refl]; exact hy,
          fun hx => ⟨x, hx, WFF.mono_refl _ _⟩⟩]
      have e : (O.mono (legQ_le A (l := l) [])).retS hS (.nec (.boxC A ([] ++ cs) hQ))
          (valQ (.nec N) A cs h t [] hQ).2
          (WFF.mono ((O.le_view_mono (legQ_le A (l := l) [])).insert (.bnd 0) _) Φ) =
          O.retS hS (.nec (.boxC A cs h)) t Φ := by
        cases O <;> exact congrArg _ (WFF.mono_refl _ _)
      rw [e]
      exact consistent_union_derives hM hex
  | q :: Q, hQ => by
      have ih := compsS_consistent_leg hS N A cs h O t Φ hM hex Q hQ.tail
      have hc := compS_consistent ih hS (O.mono (legQ_le A Q)) (.nec N) q hQ
        (valQ (.nec N) A cs h t Q hQ.tail).2
        (WFF.mono ((O.le_view_mono (legQ_le A Q)).insert (.bnd 0) _) Φ)
        (Theory.Derives.of_mem (Or.inr rfl)) (ctxOf_fresh (l := compsTys A Q ++ l) le_rfl)
      refine consistent_mono hc (Set.union_subset_union ?_ ?_)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨WFF.mono (legQ_le A Q) x, Or.inl ⟨x, hx, rfl⟩, ?_⟩
        rw [WFF.mono_mono]
      · intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        refine Set.mem_singleton_iff.mpr ?_
        cases O with
        | nec =>
            change WFF.retS hS _ _ _ = WFF.retS hS _ _ (WFF.mono _ (WFF.bodyRepl
              (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _))
              (WFF.mono _ Φ)))
            rw [WFF.bodyRepl_eta', WFF.mono_mono]
            rfl
        | pos y hy =>
            change WFF.retxS hS _ _ _ _ _ = WFF.retxS hS _ _ _ _ (WFF.mono _ (WFF.bodyRepl
              (Term.eta (.root (.bnd 0)) (.VTypeBox A) (Ctx.ref_insert_root _ (.bnd 0) _))
              (WFF.mono _ Φ)))
            rw [WFF.bodyRepl_eta', WFF.mono_mono]
            rfl

/-- A fresh root's value, substituted into a body over older roots' `□` view, renames every
    variable of the body to itself. -/
theorem single_box_under_ren {l lt : List VarType} {Δ : Ctx} (hl : l.length ≤ lt.length)
    {e : SubE σ Δ} {T : VarType} (h : Δ.boxIn (.root (.bnd 0)) = none) :
    ∀ (v : VarSymb) (U : VarType), ((ctxOf l).boxIn.insert (.bnd 0) T).ref v = some U →
      (((Subst.single (.free lt.length) e).box).under 0 0 T h).at v = .ren v
  | .root r, U, hv => by
      by_cases hr : r = .bnd 0
      · subst hr
        exact Subst.under_at_slot _ 0 0 T h
      · exfalso
        change (if VarSymb.root r = .root (.bnd 0) then _ else (ctxOf l).boxIn (.root r)) = _
          at hv
        rw [if_neg (fun he => hr (by cases he; rfl))] at hv
        cases hv
  | .step w s, U, hv => by
      by_cases hs : s.isProj = true
      · have hv' := hv
        simp only [Ctx.ref, if_pos hs] at hv'
        cases hw : ((ctxOf l).boxIn.insert (.bnd 0) T).ref w with
        | none =>
            change (if s.isProj then (Ctx.ref _ w).bind (·.step s) else _) = _ at hv
            rw [if_pos hs, hw] at hv
            cases hv
        | some U' =>
            rw [Subst.at_proj _ w hs, single_box_under_ren hl h w U' hw]
            rfl
      · have hv' : ((ctxOf l).boxIn.insert (.bnd 0) T) (.step w s) = some U := by
          change (if s.isProj then _ else _) = _ at hv
          rwa [if_neg hs] at hv
        change (if VarSymb.step w s = VarSymb.root (.bnd 0) then _ else _) = _ at hv'
        rw [if_neg (fun he => by cases he)] at hv'
        obtain ⟨u, he, hu⟩ := boxIn_item hv'
        injection he with hwu hsb
        subst hwu
        subst hsb
        obtain ⟨r, hr, hlt, -⟩ := ref_rt hu
        rw [Subst.at_under_ne _ _ _ (by
          change w.rt ≠ _
          rw [hr]
          exact fun h => by cases h)]
        change SubE.mono _ (((Subst.single (.free lt.length) e).at w).unbox) = _
        rw [Subst.single_at_ne (by
          rw [hr]
          exact fun h => absurd (Root.free.inj h) (by omega))]
        change SubE.mono _ (SubE.ren w.inner) = _
        rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
        rfl

/-- A fresh root's value, substituted into a body over older roots' `◇_y` view, renames every
    variable of the body to itself. -/
theorem single_dia_under_ren {l lt : List VarType} (hl : l.length ≤ lt.length) {Δ : Ctx}
    {e : SubE σ Δ} {T : VarType} {y : VarSymb} (h : (Δ.diaIn y) (.root (.bnd 0)) = none) :
    ∀ (v : VarSymb) (U : VarType), (((ctxOf l).diaIn y).insert (.bnd 0) T).ref v = some U →
      (((Subst.single (.free lt.length) e).dia y y).under 0 0 T h).at v = .ren v
  | .root r, U, hv => by
      by_cases hr : r = .bnd 0
      · subst hr
        exact Subst.under_at_slot _ 0 0 T h
      · exfalso
        change (if VarSymb.root r = .root (.bnd 0) then _ else (ctxOf l).diaIn y (.root r)) = _
          at hv
        rw [if_neg (fun he => hr (by cases he; rfl))] at hv
        cases hv
  | .step w s, U, hv => by
      by_cases hs : s.isProj = true
      · cases hw : (((ctxOf l).diaIn y).insert (.bnd 0) T).ref w with
        | none =>
            change (if s.isProj then (Ctx.ref _ w).bind (·.step s) else _) = _ at hv
            rw [if_pos hs, hw] at hv
            cases hv
        | some U' =>
            rw [Subst.at_proj _ w hs, single_dia_under_ren hl h w U' hw]
            rfl
      · have hv' : (((ctxOf l).diaIn y).insert (.bnd 0) T) (.step w s) = some U := by
          change (if s.isProj then _ else _) = _ at hv
          rwa [if_neg hs] at hv
        change (if VarSymb.step w s = VarSymb.root (.bnd 0) then _ else _) = _ at hv'
        rw [if_neg (fun he => by cases he)] at hv'
        rcases diaIn_item hv' with ⟨u, he, hu⟩ | ⟨he, hyr⟩
        · cases he
          obtain ⟨r, hr, hlt, -⟩ := ref_rt hu
          rw [Subst.at_under_ne _ _ _ (by
            change w.rt ≠ _
            rw [hr]
            exact fun h => by cases h)]
          change SubE.mono _ ((((Subst.single (.free lt.length) e).at w).unbox).mono _) = _
          rw [Subst.single_at_ne (by
            rw [hr]
            exact fun h => absurd (Root.free.inj h) (by omega))]
          change SubE.mono _ (SubE.mono _ (SubE.ren w.inner)) = _
          rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
          rfl
        · cases he
          obtain ⟨r, hr, hlt, -⟩ := ref_rt hyr
          rw [Subst.at_under_ne _ _ _ (by
            change y.rt ≠ _
            rw [hr]
            exact fun h => by cases h)]
          change SubE.mono _ (if y = y then ((Subst.single (.free lt.length) e).at y).diaBody y
            else .hide) = _
          rw [if_pos rfl, Subst.single_at_ne (by
            rw [hr]
            exact fun h => absurd (Root.free.inj h) (by omega))]
          rfl

/-! ## Reading a term along `fst`/`snd` steps

Every term of a product type is a pair, so a value with companions can be read component by
component.  `Term.getP` descends pairs; a substitution holding a term at `v` holds its parts at
`v`'s extensions (`Subst.at_ext_getP`), so a hole term reading the slot along a path reads the part
(`holeAt_getP`). -/

omit [ModalSys.NoFour] in
/-- A term read along `fst`/`snd` steps, descending pairs. -/
def _root_.V12M.Term.getP {Γ : Ctx} : {T : VarType} → {a : Ann T} → Term σ Γ T a →
    List Step → Option (Σ T', Σ a', Term σ Γ T' a')
  | _, _, t, π => match π, t with
    | [], t => some ⟨_, _, t⟩
    | .fst :: π, .pair s _ => s.getP π
    | .snd :: π, .pair _ t => t.getP π
    | _ :: _, _ => none

omit [ModalSys.NoFour] in
theorem getP_nil {Γ : Ctx} {T : VarType} {a : Ann T} (t : Term σ Γ T a) :
    t.getP [] = some ⟨T, a, t⟩ := by
  unfold Term.getP
  rfl

omit [ModalSys.NoFour] in
theorem getP_pair_fst {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} (s : Term σ Γ A a)
    (t : Term σ Γ B b) (π : List Step) : (Term.pair s t).getP (.fst :: π) = s.getP π := by
  conv_lhs => unfold Term.getP

omit [ModalSys.NoFour] in
theorem getP_pair_snd {Γ : Ctx} {A B : VarType} {a : Ann A} {b : Ann B} (s : Term σ Γ A a)
    (t : Term σ Γ B b) (π : List Step) : (Term.pair s t).getP (.snd :: π) = t.getP π := by
  conv_lhs => unfold Term.getP

omit [ModalSys.NoFour] in
/-- A substitution holding `t` at `w` holds `t`'s part at `w`'s extension. -/
theorem Subst.at_ext_getP {Δ : Ctx} (θ : Subst σ Δ) : ∀ (π : List Step) {w : VarSymb}
    {T : VarType} {a : Ann T} {t : Term σ Δ T a} {T' : VarType} {a' : Ann T'}
    {s : Term σ Δ T' a'}, θ.at w = .tm t → t.getP π = some ⟨T', a', s⟩ →
      θ.at (w.ext π) = .tm s
  | [], w, _, _, t, _, _, s, hw, hg => by
      rw [getP_nil] at hg
      cases Option.some.inj hg
      exact hw
  | st :: π, w, _, _, t, _, _, s, hw, hg => by
      cases t with
      | pair t₁ t₂ =>
          cases st with
          | fst =>
              rw [getP_pair_fst] at hg
              exact Subst.at_ext_getP θ π (w := .step w .fst)
                (by rw [Subst.at_proj θ w rfl, hw]; rfl) hg
          | snd =>
              rw [getP_pair_snd] at hg
              exact Subst.at_ext_getP θ π (w := .step w .snd)
                (by rw [Subst.at_proj θ w rfl, hw]; rfl) hg
          | _ => simp [Term.getP] at hg
      | _ => simp [Term.getP] at hg

omit [ModalSys.NoFour] in
/-- ⭐A hole term reading its slot along a path reads the part there. -/
theorem holeAt_getP {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) (π : List Step)
    {T : VarType} {b : Ann T} {s : Term σ Γ T b} (hg : t.getP π = some ⟨T, b, s⟩)
    (h : (Ctx.empty.insert (.bnd 0) A).ref ((VarSymb.root (.bnd 0)).ext π) = some T) :
    (⟨_, Term.holeAt t (Term.eta ((VarSymb.root (.bnd 0)).ext π) T h)⟩ : Σ c, Term σ Γ T c) =
      ⟨b, s⟩ :=
  Term.subst_eta_tm _ _ _ _ _ _ s (Subst.at_ext_getP _ π (Subst.at_single_root _ _) hg)

omit [ModalSys.NoFour] in
theorem getP_append {Γ : Ctx} : ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a) (π π' : List Step)
    {T' : VarType} {a' : Ann T'} {s : Term σ Γ T' a'}, t.getP π = some ⟨T', a', s⟩ →
      t.getP (π ++ π') = s.getP π'
  | _, _, t, [], _, _, _, _, hg => by
      rw [getP_nil] at hg
      cases Option.some.inj hg
      rfl
  | _, _, t, st :: π, π', _, _, _, hg => by
      cases t with
      | pair t₁ t₂ =>
          cases st with
          | fst =>
              rw [getP_pair_fst] at hg
              rw [List.cons_append, getP_pair_fst]
              exact getP_append t₁ π π' hg
          | snd =>
              rw [getP_pair_snd] at hg
              rw [List.cons_append, getP_pair_snd]
              exact getP_append t₂ π π' hg
          | _ => simp [Term.getP] at hg
      | _ => simp [Term.getP] at hg

omit [ModalSys.NoFour] in
/-- A built value with companions read at its own value's place. -/
theorem getP_compsBuild_fst {Γ : Ctx} (A : VarType) (main : Σ a, Term σ Γ A a) :
    ∀ (cs : List (List Step)) (get : ∀ p ∈ cs, Σ c, Term σ Γ ((A.compAt p).getD .VTypeOne) c),
      (compsBuild A main cs get).2.getP (compsFst cs) = some ⟨A, main.1, main.2⟩
  | [], _ => getP_nil _
  | p :: ps, get => by
      change (Term.pair _ _).getP (.fst :: compsFst ps) = _
      rw [getP_pair_fst]
      exact getP_compsBuild_fst A main ps _

omit [ModalSys.NoFour] in
/-- A built value with companions read at a companion's place. -/
theorem getP_compsBuild_idx {Γ : Ctx} (A : VarType) (main : Σ a, Term σ Γ A a) :
    ∀ (cs : List (List Step)) (get : ∀ p ∈ cs, Σ c, Term σ Γ ((A.compAt p).getD .VTypeOne) c)
      (q : List Step) (hq : q ∈ cs),
      (compsBuild A main cs get).2.getP (compsIdx cs q) =
        some ⟨_, (get q hq).1, (get q hq).2⟩
  | [], _, _, hq => absurd hq List.not_mem_nil
  | p :: ps, get, q, hq => by
      by_cases hqp : q = p
      · subst hqp
        change (Term.pair _ _).getP (if q = q then [.snd] else _) = _
        rw [if_pos rfl, getP_pair_snd, getP_nil]
      · have hq' : q ∈ ps := (List.mem_cons.mp hq).resolve_left hqp
        change (Term.pair _ _).getP (if q = p then [.snd] else .fst :: compsIdx ps q) = _
        rw [if_neg hqp, getP_pair_fst]
        exact getP_compsBuild_idx A main ps _ q hq'

/-! ## Extensionality for values with companions -/

omit [ModalSys.NoFour] in
/-- ⭐**Two values with companions agree** when their own values and each companion's do. -/
theorem compsFlat_ext {Γ : Ctx} (A : VarType) :
    ∀ (cs : List (List Step)), cs.Nodup → ∀ {a a' : Ann (A.compsFlat cs)}
      (t : Term σ Γ (A.compsFlat cs) a) (t' : Term σ Γ (A.compsFlat cs) a'),
      t.getP (compsFst cs) = t'.getP (compsFst cs) →
      (∀ p ∈ cs, t.getP (compsIdx cs p) = t'.getP (compsIdx cs p)) →
      (⟨a, t⟩ : Σ c, Term σ Γ (A.compsFlat cs) c) = ⟨a', t'⟩
  | [], _, _, _, t, t', hm, _ => by
      change t.getP [] = t'.getP [] at hm
      rw [getP_nil, getP_nil] at hm
      cases Option.some.inj hm
      rfl
  | p :: ps, hnd, _, _, .pair t₁ t₂, .pair t₁' t₂', hm, hc => by
      have hp' : p ∉ ps := (List.nodup_cons.mp hnd).1
      change (Term.pair _ _).getP (.fst :: compsFst ps) =
        (Term.pair _ _).getP (.fst :: compsFst ps) at hm
      rw [getP_pair_fst, getP_pair_fst] at hm
      refine sig_pair (compsFlat_ext A ps (List.nodup_cons.mp hnd).2 t₁ t₁' hm fun q hq => ?_) ?_
      · have hqp : q ≠ p := fun e => hp' (e ▸ hq)
        have := hc q (List.mem_cons_of_mem _ hq)
        change (Term.pair _ _).getP (if q = p then [.snd] else .fst :: compsIdx ps q) =
          (Term.pair _ _).getP (if q = p then [.snd] else .fst :: compsIdx ps q) at this
        rw [if_neg hqp, getP_pair_fst, getP_pair_fst] at this
        exact this
      · have := hc p List.mem_cons_self
        change (Term.pair _ _).getP (if p = p then [.snd] else _) =
          (Term.pair _ _).getP (if p = p then [.snd] else _) at this
        rw [if_pos rfl, getP_pair_snd, getP_pair_snd, getP_nil, getP_nil] at this
        cases Option.some.inj this
        rfl

/-! ## Reading the maps' values -/

omit [ModalSys.NoFour] in
theorem getP_congr {Γ : Ctx} {T : VarType} {a a' : Ann T} {t : Term σ Γ T a} {t' : Term σ Γ T a'}
    (h : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩) (π : List Step) : t.getP π = t'.getP π := by
  cases h
  rfl

omit [ModalSys.NoFour] in
theorem getP_mono {Γ Γ' : Ctx} (h : Γ.Le Γ') : ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (π : List Step) {T' : VarType} {a' : Ann T'} {s : Term σ Γ T' a'},
    t.getP π = some ⟨T', a', s⟩ → (Term.mono h t).getP π = some ⟨T', a', Term.mono h s⟩
  | _, _, t, [], _, _, _, hg => by
      rw [getP_nil] at hg
      cases Option.some.inj hg
      exact getP_nil _
  | _, _, t, st :: π, _, _, _, hg => by
      cases t with
      | pair t₁ t₂ =>
          cases st with
          | fst =>
              rw [getP_pair_fst] at hg
              exact (getP_pair_fst _ _ _).trans (getP_mono h t₁ π hg)
          | snd =>
              rw [getP_pair_snd] at hg
              exact (getP_pair_snd _ _ _).trans (getP_mono h t₂ π hg)
          | _ => simp [Term.getP] at hg
      | _ => simp [Term.getP] at hg

omit [ModalSys.NoFour] in
/-- A hole term at an address that is the slot's extension reads the part there. -/
theorem holeAt_eta_getP {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) {w : VarSymb}
    (π : List Step) (hw : w = (VarSymb.root (.bnd 0)).ext π) {T : VarType} {b : Ann T}
    {s : Term σ Γ T b} (hg : t.getP π = some ⟨T, b, s⟩)
    (h : (Ctx.empty.insert (.bnd 0) A).ref w = some T) :
    (⟨_, Term.holeAt t (Term.eta w T h)⟩ : Σ c, Term σ Γ T c) = ⟨b, s⟩ := by
  subst hw
  exact holeAt_getP t π hg h

omit [ModalSys.NoFour] in
theorem some_of_sig {Γ : Ctx} {T : VarType} {a a' : Ann T} {t : Term σ Γ T a}
    {t' : Term σ Γ T a'} (h : (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩) :
    (some ⟨T, a, t⟩ : Option (Σ T', Σ a', Term σ Γ T' a')) = some ⟨T, a', t'⟩ := by
  cases h
  rfl

omit [ModalSys.NoFour] in
/-- A hole term read into a built value with companions builds the read parts. -/
theorem holeAt_compsBuild {Γ : Ctx} {B : VarType} {b : Ann B} (t : Term σ Γ B b)
    (A : VarType) (main : Σ a, Term σ (Ctx.empty.insert (.bnd 0) B) A a) :
    ∀ (cs : List (List Step))
      (get : ∀ p ∈ cs, Σ c, Term σ (Ctx.empty.insert (.bnd 0) B) ((A.compAt p).getD .VTypeOne) c),
      (⟨_, Term.holeAt t (compsBuild A main cs get).2⟩ : Σ c, Term σ Γ (A.compsFlat cs) c) =
        compsBuild A ⟨_, Term.holeAt t main.2⟩ cs (fun p hp => ⟨_, Term.holeAt t (get p hp).2⟩)
  | [], _ => rfl
  | _ :: ps, _ => sig_pair (holeAt_compsBuild t A main ps _) rfl

omit [ModalSys.NoFour] in
theorem getP_compsFst_some {Γ : Ctx} (A : VarType) :
    ∀ (cs : List (List Step)) {a : Ann (A.compsFlat cs)}
    (t : Term σ Γ (A.compsFlat cs) a), ∃ b s, t.getP (compsFst cs) = some ⟨A, b, s⟩
  | [], _, t => ⟨_, t, getP_nil t⟩
  | _ :: ps, _, .pair t₁ _ => by
      obtain ⟨b, s, h⟩ := getP_compsFst_some A ps t₁
      exact ⟨b, s, (getP_pair_fst _ _ _).trans h⟩

omit [ModalSys.NoFour] in
theorem getP_compsIdx_some {Γ : Ctx} (A : VarType) : ∀ (cs : List (List Step))
    {a : Ann (A.compsFlat cs)} (t : Term σ Γ (A.compsFlat cs) a) (q : List Step), q ∈ cs →
    ∃ b s, t.getP (compsIdx cs q) = some ⟨(A.compAt q).getD .VTypeOne, b, s⟩
  | [], _, _, _, hq => absurd hq List.not_mem_nil
  | p :: ps, _, .pair t₁ t₂, q, hq => by
      by_cases hqp : q = p
      · subst hqp
        exact ⟨_, t₂, by simp [compsIdx, Term.getP]⟩
      · obtain ⟨b, s, h⟩ := getP_compsIdx_some A ps t₁ q
          ((List.mem_cons.mp hq).resolve_left hqp)
        exact ⟨b, s, by simp only [compsIdx, if_neg hqp]; exact (getP_pair_fst _ _ _).trans h⟩

omit [ModalSys.NoFour] in
theorem getP_prod_some {Γ : Ctx} {X Y : VarType} {a : Ann (.VTypeProd X Y)}
    (t : Term σ Γ (.VTypeProd X Y) a) :
    ∃ (a₁ : Ann X) (t₁ : Term σ Γ X a₁) (a₂ : Ann Y) (t₂ : Term σ Γ Y a₂),
      (⟨a, t⟩ : Σ c, Term σ Γ (.VTypeProd X Y) c) = ⟨_, Term.pair t₁ t₂⟩ := by
  cases t with
  | pair t₁ t₂ => exact ⟨_, t₁, _, t₂, rfl⟩

omit [ModalSys.NoFour] in
theorem getP_append_bind {Γ : Ctx} : ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a)
    (π ρ : List Step), t.getP (π ++ ρ) = (t.getP π).bind fun x => x.2.2.getP ρ
  | _, _, t, [], ρ => by rw [getP_nil]; rfl
  | _, _, t, st :: π, ρ => by
      cases t with
      | pair t₁ t₂ =>
          cases st with
          | fst =>
              rw [List.cons_append, getP_pair_fst, getP_pair_fst]
              exact getP_append_bind t₁ π ρ
          | snd =>
              rw [List.cons_append, getP_pair_snd, getP_pair_snd]
              exact getP_append_bind t₂ π ρ
          | _ => simp [Term.getP]
      | _ => simp [Term.getP]

omit [ModalSys.NoFour] in
theorem getP_append_congr {Γ : Ctx} {T T' : VarType} {a : Ann T} {a' : Ann T'}
    {t : Term σ Γ T a} {t' : Term σ Γ T' a'} {π π' : List Step} (h : t.getP π = t'.getP π')
    (ρ : List Step) : t.getP (π ++ ρ) = t'.getP (π' ++ ρ) := by
  rw [getP_append_bind, getP_append_bind, h]

omit [ModalSys.NoFour] in
theorem getP_subst {ι : VarSymb → VarSymb} {Γ Δ : Ctx} (θ : Subst σ Δ) (hθ : Subst.Ok Γ θ)
    (hc : Subst.Coh ι Γ θ) : ∀ {T : VarType} {a : Ann T} (t : Term σ Γ T a) (π : List Step)
    {T' : VarType} {a' : Ann T'} {s : Term σ Γ T' a'}, t.getP π = some ⟨T', a', s⟩ →
    (Term.subst ι θ hθ hc t).getP π = some ⟨T', _, Term.subst ι θ hθ hc s⟩
  | _, _, t, [], _, _, _, hg => by
      rw [getP_nil] at hg
      cases Option.some.inj hg
      exact getP_nil _
  | _, _, t, st :: π, _, _, _, hg => by
      cases t with
      | pair t₁ t₂ =>
          cases st with
          | fst =>
              rw [getP_pair_fst] at hg
              exact (getP_pair_fst _ _ _).trans (getP_subst θ hθ hc t₁ π hg)
          | snd =>
              rw [getP_pair_snd] at hg
              exact (getP_pair_snd _ _ _).trans (getP_subst θ hθ hc t₂ π hg)
          | _ => simp [Term.getP] at hg
      | _ => simp [Term.getP] at hg

omit [ModalSys.NoFour] in
theorem sig_of_some {Γ : Ctx} {T : VarType} {a a' : Ann T} {t : Term σ Γ T a}
    {t' : Term σ Γ T a'}
    (h : (some ⟨T, a, t⟩ : Option (Σ T', Σ a', Term σ Γ T' a')) = some ⟨T, a', t'⟩) :
    (⟨a, t⟩ : Σ c, Term σ Γ T c) = ⟨a', t'⟩ :=
  eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2

/-! ## Paths of projections out of pairs -/

/-- A path of `fst` and `snd` steps only. -/
abbrev FS (π : List Step) : Prop := ∀ s ∈ π, s = .fst ∨ s = .snd

omit [ModalSys] [ModalSys.NoFour] in
theorem FS_nil : FS [] := fun _ h => absurd h List.not_mem_nil

omit [ModalSys] [ModalSys.NoFour] in
theorem FS_cons {s : Step} {π : List Step} (hs : s = .fst ∨ s = .snd) (h : FS π) :
    FS (s :: π) := fun s' hs' => (List.mem_cons.mp hs').elim (fun e => e ▸ hs) (h s')

omit [ModalSys] [ModalSys.NoFour] in
theorem FS_append {π ρ : List Step} (h : FS π) (h' : FS ρ) : FS (π ++ ρ) :=
  fun s hs => (List.mem_append.mp hs).elim (h s) (h' s)

omit [ModalSys] [ModalSys.NoFour] in
theorem FS_compsFst : ∀ cs : List (List Step), FS (compsFst cs)
  | [] => FS_nil
  | _ :: ps => FS_cons (Or.inl rfl) (FS_compsFst ps)

omit [ModalSys] [ModalSys.NoFour] in
theorem FS_compsIdx : ∀ (cs : List (List Step)) (q : List Step), FS (compsIdx cs q)
  | [], _ => FS_nil
  | p :: ps, q => by
      unfold compsIdx
      split_ifs
      · exact FS_cons (Or.inr rfl) FS_nil
      · exact FS_cons (Or.inl rfl) (FS_compsIdx ps q)

omit [ModalSys.NoFour] in
theorem ref_ext_some {Δ : Ctx} : ∀ (π : List Step), FS π → ∀ {v : VarSymb} {C : VarType},
    Δ.ref (v.ext π) = some C → ∃ T, Δ.ref v = some T
  | [], _, _, C, h => ⟨C, h⟩
  | s :: π, hπ, v, C, h => by
      obtain ⟨T', hT'⟩ := ref_ext_some π (fun s' hs' => hπ s' (List.mem_cons_of_mem _ hs')) h
      have hs : s.isProj = true := by rcases hπ s List.mem_cons_self with rfl | rfl <;> rfl
      rw [Ctx.ref_step_proj _ _ hs] at hT'
      cases hv : Δ.ref v with
      | none =>
          rw [hv] at hT'
          cases hT'
      | some T => exact ⟨T, rfl⟩

omit [ModalSys.NoFour] in
/-- A term read along a declared path of `fst`/`snd` steps reads a part of the declared type. -/
theorem getP_some_of_ref {Γ Δ : Ctx} : ∀ (π : List Step), FS π →
    ∀ {v : VarSymb} {T C : VarType}, Δ.ref v = some T → Δ.ref (v.ext π) = some C →
    ∀ {a : Ann T} (t : Term σ Γ T a), ∃ b s, t.getP π = some ⟨C, b, s⟩
  | [], _, _, T, C, hv, h, _, t => by
      obtain rfl : T = C := Option.some.inj (hv.symm.trans h)
      exact ⟨_, t, getP_nil t⟩
  | st :: π, hπ, v, T, C, hv, h, _, t => by
      have hπ' : FS π := fun s hs => hπ s (List.mem_cons_of_mem _ hs)
      rcases hπ st List.mem_cons_self with rfl | rfl
      · obtain ⟨T', hT'⟩ := ref_ext_some π hπ' h
        rw [Ctx.ref_step_proj _ _ rfl, hv] at hT'
        cases T with
        | VTypeProd X Y =>
            cases t with
            | pair t₁ t₂ =>
                obtain ⟨b, s, hs⟩ := getP_some_of_ref π hπ' (Ctx.ref_fst_of hv) h t₁
                exact ⟨b, s, (getP_pair_fst _ _ _).trans hs⟩
        | _ => simp [VarType.step] at hT'
      · obtain ⟨T', hT'⟩ := ref_ext_some π hπ' h
        rw [Ctx.ref_step_proj _ _ rfl, hv] at hT'
        cases T with
        | VTypeProd X Y =>
            cases t with
            | pair t₁ t₂ =>
                obtain ⟨b, s, hs⟩ := getP_some_of_ref π hπ' (Ctx.ref_snd_of hv) h t₂
                exact ⟨b, s, (getP_pair_snd _ _ _).trans hs⟩
        | _ => simp [VarType.step] at hT'

omit [ModalSys.NoFour] in
/-- ⭐A hole term at an address along `fst`/`snd` steps reads its slot there. -/
theorem getP_holeAt_eta {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a) (π : List Step)
    (hπ : FS π) {w : VarSymb} (hw : w = (VarSymb.root (.bnd 0)).ext π) {T : VarType}
    (h : (Ctx.empty.insert (.bnd 0) A).ref w = some T) (ρ : List Step) :
    (Term.holeAt t (Term.eta w T h)).getP ρ = t.getP (π ++ ρ) := by
  subst hw
  obtain ⟨b, s, hs⟩ := getP_some_of_ref π hπ (Ctx.ref_insert_root _ _ _) h t
  rw [getP_congr (holeAt_getP t π hs h), getP_append t π ρ hs]

omit [ModalSys.NoFour] in
theorem getP_holeAt_comp {Γ : Ctx} {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b)
    {C : VarType} {c : Ann C} (u : Term σ (Ctx.empty.insert (.bnd 0) B) C c) (π : List Step) :
    (Term.holeAt t (Term.holeAt s u)).getP π = (Term.holeAt (Term.holeAt t s) u).getP π :=
  getP_congr (Term.holeAt_holeAt_sig t s u) π

/-! ## The structural maps with companions, read -/

section MapReads

variable {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step)) (hX : X.CompOk csX)
  (hY : Y.CompOk csY)

omit [ModalSys.NoFour] in
theorem packCC_read_fst {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsFst (pairComps csX csY) ++ .fst :: ρ) = w.getP (.fst :: compsFst csX ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_fst _ _ _ _)]
  refine (getP_pair_fst _ _ ρ).trans ?_
  exact getP_holeAt_eta w _ (FS_cons (Or.inl rfl) (FS_compsFst csX)) rfl _ ρ

omit [ModalSys.NoFour] in
theorem packCC_read_snd {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsFst (pairComps csX csY) ++ .snd :: ρ) = w.getP (.snd :: compsFst csY ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_fst _ _ _ _)]
  refine (getP_pair_snd _ _ ρ).trans ?_
  exact getP_holeAt_eta w _ (FS_cons (Or.inr rfl) (FS_compsFst csY)) rfl _ ρ

omit [ModalSys.NoFour] in
theorem packCC_read_idx_fst {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (q : List Step)
    (hq : q ∈ csX) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx (pairComps csX csY) (.fst :: q) ++ ρ) =
      w.getP (.fst :: compsIdx csX q ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_idx _ _ _ _
    (.fst :: q) (List.mem_append_left _ (List.mem_map_of_mem hq)))]
  exact getP_holeAt_eta w _ (FS_cons (Or.inl rfl) (FS_compsIdx csX q)) (if_pos rfl) _ ρ

omit [ModalSys.NoFour] in
theorem packCC_read_idx_snd {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (q : List Step)
    (hq : q ∈ csY) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx (pairComps csX csY) (.snd :: q) ++ ρ) =
      w.getP (.snd :: compsIdx csY q ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_idx _ _ _ _
    (.snd :: q) (List.mem_append_right _ (List.mem_map_of_mem hq)))]
  exact getP_holeAt_eta w _ (FS_cons (Or.inr rfl) (FS_compsIdx csY q))
    (if_neg (by simp)) _ ρ

omit [ModalSys.NoFour] in
theorem fstC_read_main {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).val.2).getP (compsFst csX ++ ρ) =
      w.getP (compsFst (pairComps csX csY) ++ .fst :: ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_fst _ _ _ _),
    getP_holeAt_eta w _ (FS_append (FS_compsFst _) (FS_cons (Or.inl rfl) FS_nil))
      (VarSymb.ext_step _ _ _).symm _ ρ, List.append_assoc, List.singleton_append]

omit [ModalSys.NoFour] in
theorem fstC_read_idx {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (q : List Step)
    (hq : q ∈ csX) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx csX q ++ ρ) = w.getP (compsIdx (pairComps csX csY) (.fst :: q) ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_idx _ _ _ _
    q hq)]
  exact getP_holeAt_eta w _ (FS_compsIdx _ _) rfl _ ρ

omit [ModalSys.NoFour] in
theorem sndC_read_main {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).val.2).getP (compsFst csY ++ ρ) =
      w.getP (compsFst (pairComps csX csY) ++ .snd :: ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_fst _ _ _ _),
    getP_holeAt_eta w _ (FS_append (FS_compsFst _) (FS_cons (Or.inr rfl) FS_nil))
      (VarSymb.ext_step _ _ _).symm _ ρ, List.append_assoc, List.singleton_append]

omit [ModalSys.NoFour] in
theorem sndC_read_idx {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (q : List Step)
    (hq : q ∈ csY) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx csY q ++ ρ) = w.getP (compsIdx (pairComps csX csY) (.snd :: q) ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_idx _ _ _ _
    q hq)]
  exact getP_holeAt_eta w _ (FS_compsIdx _ _) rfl _ ρ

end MapReads

omit [ModalSys.NoFour] in
/-- `subC` keeps the object's own value. -/
theorem subC_read_main {Γ : Ctx} (A : VarType) (cs cs' : List (List Step)) (h : A.CompOk cs)
    (h' : A.CompOk cs') (hsub : ∀ p ∈ cs', p ∈ cs) {a : Ann (A.compsFlat cs)}
    (w : Term σ Γ (A.compsFlat cs) a) (ρ : List Step) :
    (Term.holeAt w (ShapeMap.subC (σ := σ) A cs cs' h h' hsub).val.2).getP
      (compsFst cs' ++ ρ) = w.getP (compsFst cs ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_fst _ _ _ _)]
  exact getP_holeAt_eta w _ (FS_compsFst _) rfl _ ρ

omit [ModalSys.NoFour] in
/-- `subC` keeps each selected companion's value. -/
theorem subC_read_idx {Γ : Ctx} (A : VarType) (cs cs' : List (List Step)) (h : A.CompOk cs)
    (h' : A.CompOk cs') (hsub : ∀ p ∈ cs', p ∈ cs) {a : Ann (A.compsFlat cs)}
    (w : Term σ Γ (A.compsFlat cs) a) (q : List Step) (hq : q ∈ cs') (ρ : List Step) :
    (Term.holeAt w (ShapeMap.subC (σ := σ) A cs cs' h h' hsub).val.2).getP
      (compsIdx cs' q ++ ρ) = w.getP (compsIdx cs q ++ ρ) := by
  dsimp only [ShapeMap.val]
  rw [getP_congr (holeAt_compsBuild w _ _ _ _), getP_append _ _ _ (getP_compsBuild_idx _ _ _ _
    q hq)]
  exact getP_holeAt_eta w _ (FS_compsIdx _ _) rfl _ ρ

omit [ModalSys.NoFour] in
theorem packCC_read_idx_fst' {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY)
    {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (q : List Step)
    (hq : q ∈ csX) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx (pairComps csX csY) (.fst :: q)) = w.getP (.fst :: compsIdx csX q) := by
  have h := packCC_read_idx_fst X Y csX csY hX hY w q hq []
  rwa [List.append_nil, List.append_nil] at h

omit [ModalSys.NoFour] in
theorem packCC_read_idx_snd' {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY)
    {a : Ann (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY))}
    (w : Term σ Γ (.VTypeProd (X.compsFlat csX) (Y.compsFlat csY)) a) (q : List Step)
    (hq : q ∈ csY) :
    (Term.holeAt w (ShapeMap.packCC (σ := σ) X Y csX csY hX hY).val.2).getP
      (compsIdx (pairComps csX csY) (.snd :: q)) = w.getP (.snd :: compsIdx csY q) := by
  have h := packCC_read_idx_snd X Y csX csY hX hY w q hq []
  rwa [List.append_nil, List.append_nil] at h

omit [ModalSys.NoFour] in
theorem fstC_read_idx' {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY)
    {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (q : List Step)
    (hq : q ∈ csX) :
    (Term.holeAt w (ShapeMap.fstC (σ := σ) X Y csX csY hX hY).val.2).getP (compsIdx csX q) =
      w.getP (compsIdx (pairComps csX csY) (.fst :: q)) := by
  have h := fstC_read_idx X Y csX csY hX hY w q hq []
  rwa [List.append_nil, List.append_nil] at h

omit [ModalSys.NoFour] in
theorem sndC_read_idx' {Γ : Ctx} (X Y : VarType) (csX csY : List (List Step))
    (hX : X.CompOk csX) (hY : Y.CompOk csY)
    {a : Ann ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY))}
    (w : Term σ Γ ((VarType.VTypeProd X Y).compsFlat (pairComps csX csY)) a) (q : List Step)
    (hq : q ∈ csY) :
    (Term.holeAt w (ShapeMap.sndC (σ := σ) X Y csX csY hX hY).val.2).getP (compsIdx csY q) =
      w.getP (compsIdx (pairComps csX csY) (.snd :: q)) := by
  have h := sndC_read_idx X Y csX csY hX hY w q hq []
  rwa [List.append_nil, List.append_nil] at h

omit [ModalSys.NoFour] in
theorem subC_read_idx' {Γ : Ctx} (A : VarType) (cs cs' : List (List Step)) (h : A.CompOk cs)
    (h' : A.CompOk cs') (hsub : ∀ p ∈ cs', p ∈ cs) {a : Ann (A.compsFlat cs)}
    (w : Term σ Γ (A.compsFlat cs) a) (q : List Step) (hq : q ∈ cs') :
    (Term.holeAt w (ShapeMap.subC (σ := σ) A cs cs' h h' hsub).val.2).getP (compsIdx cs' q) =
      w.getP (compsIdx cs q) := by
  have e := subC_read_idx A cs cs' h h' hsub w q hq []
  rwa [List.append_nil, List.append_nil] at e

/-! ## Tuples read: a companion sits in the tree of items -/

omit [ModalSys] [ModalSys.NoFour] in
theorem mem_pairComps_fst {csX csY : List (List Step)} {q : List Step}
    (h : .fst :: q ∈ pairComps csX csY) : q ∈ csX := by
  rcases pairComps_mem h with ⟨-, hq⟩ | ⟨e, -⟩
  · exact hq
  · cases e

omit [ModalSys] [ModalSys.NoFour] in
theorem mem_pairComps_snd {csX csY : List (List Step)} {q : List Step}
    (h : .snd :: q ∈ pairComps csX csY) : q ∈ csY := by
  rcases pairComps_mem h with ⟨e, -⟩ | ⟨-, hq⟩
  · cases e
  · exact hq

omit [ModalSys.NoFour] in
theorem itemTail_T (hT : ModalSys.T = true) : itemTail = [.fst] := by
  simp [itemTail, hT]

omit [ModalSys.NoFour] in
/-- ⭐Under T, the tree of items holds each companion's leaf at the companion's encoded path. -/
theorem bcTree_read (hT : ModalSys.T = true) {Γ : Ctx} : ∀ (Z : VarType)
    (get : ∀ q, q ∈ Z.hereChains → Σ c, Term σ Γ ((Z.compAt q).getD .VTypeOne) c)
    (q : List Step) (hq : q ∈ Z.hereChains),
    (bcTree Z get).2.getP (encPath q ++ itemTail) = some ⟨_, _, (get q hq).2⟩
  | .VTypeBox C, get, q, hq => by
      dsimp only [bcTree]
      rcases List.mem_cons.mp hq with rfl | hq'
      · rw [itemTail_T hT]
        exact (getP_pair_fst _ _ _).trans (getP_nil _)
      · obtain ⟨q', hq₀, rfl⟩ := List.mem_map.mp hq'
        simp only [encPath, List.map_cons, List.cons_append]
        rw [encStep_here hT]
        exact (getP_pair_snd _ _ _).trans
          (bcTree_read hT C (fun q hq => get (.here :: q) _) q' hq₀)
  | .VTypeProd X Y, get, q, hq => by
      dsimp only [bcTree]
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨q', hq₀, rfl⟩ := List.mem_map.mp hq'
        simp only [encPath, List.map_cons, List.cons_append]
        rw [encStep_fst]
        exact (getP_pair_fst _ _ _).trans
          (bcTree_read hT X (fun q hq => get (.fst :: q) _) q' hq₀)
      · obtain ⟨q', hq₀, rfl⟩ := List.mem_map.mp hq'
        simp only [encPath, List.map_cons, List.cons_append]
        rw [encStep_snd]
        exact (getP_pair_snd _ _ _).trans
          (bcTree_read hT Y (fun q hq => get (.snd :: q) _) q' hq₀)
  | .Var, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeOne, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeDia _, _, _, hq => absurd hq List.not_mem_nil

omit [ModalSys.NoFour] in
theorem tupCVal_ref (A : VarType) {p : List Step} (hp : p ∈ (tupOneTy A true).hereChains) :
    (Ctx.empty.insert (.bnd 0) (A.compsFlat A.hereChains)).ref
      ((VarSymb.root (.bnd 0)).ext (compsIdx A.hereChains (tupCompOf A p))) =
      some (((tupOneTy A true).compAt p).getD .VTypeOne) := by
  rw [(tupCompOf_spec A p hp).2]
  exact Ctx.ref_compsIdx _ _ (tupCompOf_spec A p hp).1 (Ctx.ref_insert_root _ _ _)

omit [ModalSys.NoFour] in
theorem tupCVal_eq_build (A : VarType) (hT : ModalSys.T = true) :
    ∀ (cs : List (List Step)) (hcs : ∀ p ∈ cs, p ∈ (tupOneTy A true).hereChains),
      tupCVal (σ := σ) A hT cs hcs = compsBuild (tupOneTy A true)
        (tupCVal A hT [] fun _ h => absurd h List.not_mem_nil) cs
        (fun p hp => ⟨_, Term.eta ((VarSymb.root (.bnd 0)).ext
          (compsIdx A.hereChains (tupCompOf A p))) _ (tupCVal_ref A (hcs p hp))⟩)
  | [], _ => rfl
  | _ :: ps, _ => sig_pair (tupCVal_eq_build A hT ps _) rfl

section TupRead

variable (A : VarType) (hT : ModalSys.T = true) {Γ : Ctx} {a : Ann (A.compsFlat A.hereChains)}
  (w : Term σ Γ (A.compsFlat A.hereChains) a)

omit [ModalSys.NoFour] in
/-- The tuple's tree of items, read at a companion's encoded path: the companion's value. -/
theorem tupC_read_tree (q : List Step) (hq : q ∈ A.hereChains) :
    (Term.holeAt w (ShapeMap.tupC (σ := σ) A true hT).val.2).getP
      (compsFst (tupOneTy A true).hereChains ++ .snd :: .snd :: (encPath q ++ itemTail)) =
      w.getP (compsIdx A.hereChains q) := by
  dsimp only [ShapeMap.val]
  rw [tupCVal_eq_build A hT, getP_congr (holeAt_compsBuild w _ _ _ _)]
  refine (getP_append _ _ _ (getP_compsBuild_fst _ _ _ _)).trans ?_
  dsimp only [tupCVal]
  refine (getP_subst _ _ _ _ _ ((getP_pair_snd _ _ _).trans
    ((getP_pair_snd _ _ _).trans (bcTree_read hT A _ q hq)))).trans ?_
  exact (getP_nil _).symm.trans ((getP_holeAt_eta w _ (FS_compsIdx _ _) rfl _ []).trans
    (congrArg _ (List.append_nil _)))

omit [ModalSys.NoFour] in
/-- The tuple's companion: the born root's companion it is. -/
theorem tupC_read_idx (p : List Step) (hp : p ∈ (tupOneTy A true).hereChains) :
    (Term.holeAt w (ShapeMap.tupC (σ := σ) A true hT).val.2).getP
      (compsIdx (tupOneTy A true).hereChains p) =
      w.getP (compsIdx A.hereChains (tupCompOf A p)) := by
  dsimp only [ShapeMap.val]
  rw [tupCVal_eq_build A hT, getP_congr (holeAt_compsBuild w _ _ _ _)]
  refine (getP_compsBuild_idx _ _ _ _ p hp).trans ?_
  exact (getP_nil _).symm.trans ((getP_holeAt_eta w _ (FS_compsIdx _ _) rfl _ []).trans
    (congrArg _ (List.append_nil _)))

omit [ModalSys.NoFour] in
/-- ⭐**The tuple is coherent**: its companion `snd :: p` sits in its value, at the encoded
    path of the root's companion it decodes to. -/
theorem tupC_coh (p : List Step) (hp : p ∈ ((VarType.VTypeBox A).bcB true).hereChains) :
    (Term.holeAt w (ShapeMap.tupC (σ := σ) A true hT).val.2).getP
      (compsIdx (tupOneTy A true).hereChains (.snd :: p)) =
    (Term.holeAt w (ShapeMap.tupC (σ := σ) A true hT).val.2).getP
      (compsFst (tupOneTy A true).hereChains ++
        .snd :: (encPath ((VarType.VTypeBox A).bcDec p) ++ itemTail)) := by
  have hp' : .snd :: p ∈ (tupOneTy A true).hereChains :=
    List.mem_append_right _ (List.mem_map_of_mem hp)
  obtain ⟨r, hr⟩ : ∃ r, (VarType.VTypeBox A).bcDec p = .here :: r :=
    ⟨_, VarType.bcDec_box A p hp⟩
  have hrc : tupCompOf A (.snd :: p) = r := by simp [tupCompOf, hr]
  rw [tupC_read_idx A hT w _ hp', hr]
  simp only [encPath, List.map_cons, List.cons_append]
  rw [encStep_here hT]
  have h1 := tupC_read_tree A hT w r (hrc ▸ (tupCompOf_spec A _ hp').1)
  simp only [encPath] at h1
  rw [h1, hrc]

end TupRead

omit [ModalSys.NoFour] in
/-- ⭐**A root's tuple is coherent**, for a root of any type: each companion of `tupCRT`'s output
    sits in its value, at the encoded path of the root's companion it decodes to. -/
theorem tupCRT_coh (hT : ModalSys.T = true) : ∀ (R : VarType) {Γ : Ctx}
    {a : Ann ((R.bcB false).compsFlat (R.bcB false).hereChains)}
    (w : Term σ Γ ((R.bcB false).compsFlat (R.bcB false).hereChains) a)
    (q : List Step), q ∈ (R.bcB true).hereChains →
    (Term.holeAt w (tupCRT (σ := σ) hT R).val.2).getP (compsIdx (R.bcB true).hereChains q) =
    (Term.holeAt w (tupCRT (σ := σ) hT R).val.2).getP
      (compsFst (R.bcB true).hereChains ++ (encPath (R.bcDec q) ++ itemTail))
  | .VTypeBox A, _, _, w, q, hq => by
      dsimp only [tupCRT, ShapeMap.val]
      refine (getP_holeAt_comp _ _ _ _).trans (Eq.trans ?_ (getP_holeAt_comp _ _ _ _).symm)
      exact (sndC_read_idx' (σ := σ) .VTypeOne ((VarType.VTypeBox A).bcB true) []
        ((VarType.VTypeBox A).bcB true).hereChains (Or.inl rfl)
        (VarType.compOk_compsAllB true hT _) _ q hq).trans ((tupC_coh A hT w q hq).trans
        (sndC_read_main (σ := σ) .VTypeOne _ [] _ (Or.inl rfl)
          (VarType.compOk_compsAllB true hT _) _ _).symm)
  | .VTypeProd X Y, _, _, w, q, hq => by
      dsimp only [tupCRT, ShapeMap.val]
      refine (getP_holeAt_comp _ _ _ _).trans ((getP_holeAt_comp _ _ _ _).trans
        (Eq.trans ?_ ((getP_holeAt_comp _ _ _ _).trans (getP_holeAt_comp _ _ _ _)).symm))
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨q', hq₀, rfl⟩ := List.mem_map.mp hq'
        have hpath : encPath ((VarType.VTypeProd X Y).bcDec (.fst :: q')) ++ itemTail =
            .fst :: (encPath (X.bcDec q') ++ itemTail) := by
          simp only [VarType.bcDec, encPath, List.map_cons, List.cons_append, encStep_fst]
        rw [hpath]
        refine (packCC_read_idx_fst' (σ := σ) (X.bcB true) (Y.bcB true) _ _
          (VarType.compOk_compsAllB true hT _) (VarType.compOk_compsAllB true hT _) _ q'
          hq₀).trans (Eq.trans ?_ (packCC_read_fst (σ := σ) (X.bcB true) (Y.bcB true) _ _
          (VarType.compOk_compsAllB true hT _) (VarType.compOk_compsAllB true hT _) _ _).symm)
        refine (getP_pair_fst _ _ _).trans (Eq.trans ?_ (getP_pair_fst _ _ _).symm)
        refine (getP_holeAt_comp _ _ _ _).trans (Eq.trans ?_ (getP_holeAt_comp _ _ _ _).symm)
        refine (getP_congr (sig_holeAt (Term.holeAt_pair_fst _ _) _) _).trans
          (Eq.trans ?_ (getP_congr (sig_holeAt (Term.holeAt_pair_fst _ _) _) _).symm)
        exact tupCRT_coh hT X _ q' hq₀
      · obtain ⟨q', hq₀, rfl⟩ := List.mem_map.mp hq'
        have hpath : encPath ((VarType.VTypeProd X Y).bcDec (.snd :: q')) ++ itemTail =
            .snd :: (encPath (Y.bcDec q') ++ itemTail) := by
          simp only [VarType.bcDec, encPath, List.map_cons, List.cons_append, encStep_snd]
        rw [hpath]
        refine (packCC_read_idx_snd' (σ := σ) (X.bcB true) (Y.bcB true) _ _
          (VarType.compOk_compsAllB true hT _) (VarType.compOk_compsAllB true hT _) _ q'
          hq₀).trans (Eq.trans ?_ (packCC_read_snd (σ := σ) (X.bcB true) (Y.bcB true) _ _
          (VarType.compOk_compsAllB true hT _) (VarType.compOk_compsAllB true hT _) _ _).symm)
        refine (getP_pair_snd _ _ _).trans (Eq.trans ?_ (getP_pair_snd _ _ _).symm)
        refine (getP_holeAt_comp _ _ _ _).trans (Eq.trans ?_ (getP_holeAt_comp _ _ _ _).symm)
        refine (getP_congr (sig_holeAt (Term.holeAt_pair_snd _ _) _) _).trans
          (Eq.trans ?_ (getP_congr (sig_holeAt (Term.holeAt_pair_snd _ _) _) _).symm)
        exact tupCRT_coh hT Y _ q' hq₀
  | .Var, _, _, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeOne, _, _, _, _, hq => absurd hq List.not_mem_nil
  | .VTypeDia _, _, _, _, _, hq => absurd hq List.not_mem_nil

/-! ## The step's tuple map, read -/

section TupCGRead

variable (Y R : VarType) {Γ : Ctx}

omit [ModalSys.NoFour] in
/-- `tupCG` keeps the prefix. -/
theorem tupCG_read_main : ∀ (b : Bool) (hb : ModalSys.T = b)
    {a : Ann ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b))}
    (w : Term σ Γ ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b)) a),
    (Term.holeAt w (tupCG (σ := σ) Y R b hb).val.2).getP
      (compsFst ((VarType.VTypeProd Y (R.bcB b)).compsAllB b) ++ [.fst]) =
      w.getP (compsFst ((VarType.VTypeProd Y (R.bcB false)).compsAllB b) ++ [.fst])
  | false, _, _, w => getP_congr (Term.holeAt_eta_root w) _
  | true, hb, _, w => by
      dsimp only [tupCG, ShapeMap.val]
      refine (getP_holeAt_comp _ _ _ _).trans ?_
      refine (packCC_read_fst (σ := σ) Y (R.bcB true) _ _ (VarType.compOk_compsAllB true hb _)
        (VarType.compOk_compsAllB true hb _) _ []).trans ?_
      refine (getP_pair_fst _ _ _).trans ?_
      exact fstC_read_main (σ := σ) Y (R.bcB false) _ _ (VarType.compOk_compsAllB true hb _)
        (VarType.compOk_compsAllB true hb _) w []

omit [ModalSys.NoFour] in
/-- `tupCG` keeps the prefix's companions. -/
theorem tupCG_read_fst : ∀ (b : Bool) (hb : ModalSys.T = b)
    {a : Ann ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b))}
    (w : Term σ Γ ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b)) a) (q : List Step),
    .fst :: q ∈ (VarType.VTypeProd Y (R.bcB b)).compsAllB b →
    (Term.holeAt w (tupCG (σ := σ) Y R b hb).val.2).getP
      (compsIdx ((VarType.VTypeProd Y (R.bcB b)).compsAllB b) (.fst :: q)) =
      w.getP (compsIdx ((VarType.VTypeProd Y (R.bcB false)).compsAllB b) (.fst :: q))
  | false, _, _, _, _, hq => absurd hq List.not_mem_nil
  | true, hb, _, w, q, hq => by
      have hq' := mem_pairComps_fst hq
      dsimp only [tupCG, ShapeMap.val]
      refine (getP_holeAt_comp _ _ _ _).trans ?_
      refine (packCC_read_idx_fst' (σ := σ) Y (R.bcB true) _ _
        (VarType.compOk_compsAllB true hb _) (VarType.compOk_compsAllB true hb _) _ q
        hq').trans ((getP_pair_fst _ _ _).trans ?_)
      exact fstC_read_idx' (σ := σ) Y (R.bcB false) _ _ (VarType.compOk_compsAllB true hb _)
        (VarType.compOk_compsAllB true hb _) w q hq'

omit [ModalSys.NoFour] in
/-- ⭐**`tupCG`'s output is coherent**: its companion `snd :: q` sits in its value, at the
    encoded path of the root's companion `q` decodes to. -/
theorem tupCG_coh : ∀ (b : Bool) (hb : ModalSys.T = b)
    {a : Ann ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b))}
    (w : Term σ Γ ((VarType.VTypeProd Y (R.bcB false)).compsFlat
      ((VarType.VTypeProd Y (R.bcB false)).compsAllB b)) a) (q : List Step),
    .snd :: q ∈ (VarType.VTypeProd Y (R.bcB b)).compsAllB b →
    (Term.holeAt w (tupCG (σ := σ) Y R b hb).val.2).getP
      (compsIdx ((VarType.VTypeProd Y (R.bcB b)).compsAllB b) (.snd :: q)) =
    (Term.holeAt w (tupCG (σ := σ) Y R b hb).val.2).getP
      (compsFst ((VarType.VTypeProd Y (R.bcB b)).compsAllB b) ++
        .snd :: (encPath (R.bcDec q) ++ itemTail))
  | false, _, _, _, _, hq => absurd hq List.not_mem_nil
  | true, hb, _, w, q, hq => by
      have hq' := mem_pairComps_snd hq
      dsimp only [tupCG, ShapeMap.val]
      refine (getP_holeAt_comp _ _ _ _).trans (Eq.trans ?_ (getP_holeAt_comp _ _ _ _).symm)
      refine (packCC_read_idx_snd' (σ := σ) Y (R.bcB true) _ _
        (VarType.compOk_compsAllB true hb _) (VarType.compOk_compsAllB true hb _) _ q
        hq').trans ((getP_pair_snd _ _ _).trans ((getP_holeAt_comp _ _ _ _).trans ?_))
      refine (tupCRT_coh hb R _ q hq').trans ?_
      refine (getP_holeAt_comp _ _ _ _).symm.trans ?_
      refine Eq.trans ?_ (packCC_read_snd (σ := σ) Y (R.bcB true) _ _
        (VarType.compOk_compsAllB true hb _) (VarType.compOk_compsAllB true hb _) _ _).symm
      exact (getP_pair_snd _ _ _).symm

end TupCGRead

/-! ## The chain's other links, read -/

omit [ModalSys] [ModalSys.NoFour] in
theorem compsAllB_prod (b : Bool) (X Y : VarType) :
    (VarType.VTypeProd X Y).compsAllB b = pairComps (X.compsAllB b) (Y.compsAllB b) := by
  cases b <;> rfl

omit [ModalSys.NoFour] in
theorem getP_holeRead {Γ : Ctx} [Γ.NoSlots] {A : VarType} {a : Ann A} (t : Term σ Γ A a)
    {B : VarType} {b : Ann B} (s : Term σ (Ctx.empty.insert (.bnd 0) A) B b) (π : List Step) :
    (Term.holeRead t s).getP π = (Term.holeAt t s).getP π := by
  rw [Term.holeRead_eq_holeAt]

omit [ModalSys.NoFour] in
/-- Naming companions keeps the value's own value, weakened. -/
theorem valQ_read_main (N : NShape) (A : VarType) (cs : List (List Step)) (h : A.CompOk cs)
    {l : List VarType} {a : Ann ((RShape.nec N).withNec (.boxC A cs h)).flat}
    (t : Term σ (ctxOf l) ((RShape.nec N).withNec (.boxC A cs h)).flat a) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)) (ρ : List Step) {T : VarType}
      {b : Ann T} {s : Term σ (ctxOf l) T b}, t.getP (compsFst cs ++ ρ) = some ⟨T, b, s⟩ →
      (valQ (σ := σ) (.nec N) A cs h t Q hQ).2.getP (compsFst (Q ++ cs) ++ ρ) =
        some ⟨T, b, Term.mono (legQ_le A Q) s⟩
  | [], _, ρ, _, _, s, hs => by
      rw [show Term.mono (legQ_le A (l := l) []) s = s from Term.mono_refl _ s]
      exact hs
  | q :: Q, hQ, ρ, _, _, s, hs => by
      have ih := valQ_read_main N A cs h t Q hQ.tail ρ hs
      refine (getP_pair_fst _ _ _).trans ((getP_mono _ _ _ ih).trans ?_)
      rw [Term.mono_mono]

omit [ModalSys.NoFour] in
/-- Naming companions keeps the older companions' values, weakened. -/
theorem valQ_read_idx (N : NShape) (A : VarType) (cs : List (List Step)) (h : A.CompOk cs)
    {l : List VarType} {a : Ann ((RShape.nec N).withNec (.boxC A cs h)).flat}
    (t : Term σ (ctxOf l) ((RShape.nec N).withNec (.boxC A cs h)).flat a) (p : List Step) :
    ∀ (Q : List (List Step)) (hQ : A.CompOk (Q ++ cs)), p ∉ Q → ∀ {T : VarType}
      {b : Ann T} {s : Term σ (ctxOf l) T b}, t.getP (compsIdx cs p) = some ⟨T, b, s⟩ →
      (valQ (σ := σ) (.nec N) A cs h t Q hQ).2.getP (compsIdx (Q ++ cs) p) =
        some ⟨T, b, Term.mono (legQ_le A Q) s⟩
  | [], _, _, _, _, s, hs => by
      rw [show Term.mono (legQ_le A (l := l) []) s = s from Term.mono_refl _ s]
      exact hs
  | q :: Q, hQ, hp, _, _, s, hs => by
      have hpq : p ≠ q := fun e => hp (e ▸ List.mem_cons_self)
      have ih := valQ_read_idx N A cs h t p Q hQ.tail
        (fun h' => hp (List.mem_cons_of_mem _ h')) hs
      rw [show compsIdx ((q :: Q) ++ cs) p = .fst :: compsIdx (Q ++ cs) p from if_neg hpq]
      refine (getP_pair_fst _ _ _).trans ((getP_mono _ _ _ ih).trans ?_)
      rw [Term.mono_mono]

/-- The images' tuple with companions, read at the tuple's place: the images' tuple. -/
theorem tupCompsImg_read_fst {Δ : Ctx} (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) : ∀ (cs : List (List Step)) (h : (bcT cls).CompOk cs),
      (tupCompsImg (σ := σ) cls img himg cs h).2.getP (compsFst cs) =
        some ⟨_, _, (tupImgT cls img himg).2⟩
  | [], _ => getP_nil _
  | _ :: ps, h => (getP_pair_fst _ _ _).trans (tupCompsImg_read_fst cls img himg ps h.tail)

/-- The images' tuple with companions, read at a companion's place: the companion's contents
    sent along the arrow. -/
theorem tupCompsImg_read_idx {Δ : Ctx} (cls : List VarType) (img : ℕ → ℕ)
    (himg : ImgOk cls Δ img) : ∀ (cs : List (List Step)) (h : (bcT cls).CompOk cs)
      (q : List Step), q ∈ cs → ∀ (h' : (bcT cls).CompOk [q]),
      (tupCompsImg (σ := σ) cls img himg cs h).2.getP (compsIdx cs q) =
        some ⟨_, _, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg)
          (coh_arrowS himg) (compVal (tupT cls).2 q h').2⟩
  | [], _, _, hq, _ => absurd hq List.not_mem_nil
  | p :: ps, h, q, hq, h' => by
      by_cases hqp : q = p
      · subst hqp
        rw [show compsIdx (q :: ps) q = [.snd] from if_pos rfl]
        exact (getP_pair_snd _ _ _).trans (getP_nil _)
      · rw [show compsIdx (p :: ps) q = .fst :: compsIdx ps q from if_neg hqp]
        exact (getP_pair_fst _ _ _).trans (tupCompsImg_read_idx cls img himg ps h.tail q
          ((List.mem_cons.mp hq).resolve_left hqp) h')

/-! ## Companions' contents of pairs and tuples -/

/-- Under T, a pair's companion `fst :: q` is its first component's companion `q`. -/
theorem compVal_pair_fst {Γ : Ctx} {X Y : VarType} {a₀ : Ann X} {b₀ : Ann Y}
    (s : Term σ Γ.boxIn X a₀) (t : Term σ Γ.boxIn Y b₀) (q : List Step)
    {ps ps' : List (List Step)} (h : (VarType.VTypeProd X Y).CompOk ((.fst :: q) :: ps))
    (hq : X.CompOk (q :: ps')) :
    compVal (σ := σ) (Term.pair s t) (.fst :: q) h = compVal s q hq := by
  obtain ⟨hT, hall, -⟩ := hq.resolve_left (List.cons_ne_nil _ _)
  have hC : X.compAt q = some ((X.compAt q).getD .VTypeOne) := by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall q List.mem_cons_self)
    rw [hC]
    rfl
  have hr := Ctx.ref_insert_root Ctx.empty (.bnd 0)
    (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))
  have hf : (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))).ref
      (.step (.root (.bnd 0)) .fst) = some (.VTypeBox X) := Ctx.ref_fst_of hr
  have h' := Ctx.ref_compAt hT q (Ctx.ref_here_of hT hf) hC
  let θ₁ := Subst.single (σ := σ)
    (Δ := Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))) (.bnd 0)
    (.tm (ShapeMap.pack (σ := σ) X Y).obj.2)
  have h0 : θ₁.at (.step (.step (.root (.bnd 0)) .here) .fst) =
      .tm (Term.eta (.step (.step (.root (.bnd 0)) .fst) .here) X (Ctx.ref_here_of hT hf)) := by
    rw [Subst.at_proj θ₁ _ rfl, Subst.at_proj θ₁ _ rfl, Subst.at_single_root]
    dsimp only [ShapeMap.obj]
    rw [SubE.proj_boxtm_here _ hT]
    change SubE.tm (Term.collapse _ (Term.eta (VarSymb.step (.root (.bnd 0)) .fst).inner X _)) = _
    exact SubE.tm_eq_of_sig ((Term.collapse_eta _ _ X _).trans
      (Term.eta_congr (VarSymb.inner_collapse_zero _) X _ _))
  have key1 : (⟨_, Term.holeAt (ShapeMap.pack (σ := σ) X Y).obj.2 (Term.boxtm (Term.eta
      ((VarSymb.step (.root (.bnd 0)) .here).ext (.fst :: q)).inner
      (((VarType.VTypeProd X Y).compAt (.fst :: q)).getD .VTypeOne)
      (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _)))))⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y)))
        (.VTypeBox ((X.compAt q).getD .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.eta ((VarSymb.step (.step (.root (.bnd 0)) .fst) .here).ext q).inner
        ((X.compAt q).getD .VTypeOne) (Ctx.ref_inner h'))⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ₁
      (Subst.at_ext_eta hT θ₁ q (Ctx.ref_here_of hT hf) hC h' h0)))
  let θ₂ := Subst.single (σ := σ)
    (Δ := Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))) (.bnd 0)
    (.tm (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) hf))
  have h0' : θ₂.at (.step (.root (.bnd 0)) .here) =
      .tm (Term.eta (.step (.step (.root (.bnd 0)) .fst) .here) X (Ctx.ref_here_of hT hf)) := by
    rw [Subst.at_proj θ₂ _ rfl, Subst.at_single_root]
    exact SubE.proj_here_eta hT hf
  have key2 : (⟨_, Term.holeAt (Term.eta (.step (.root (.bnd 0)) .fst) (.VTypeBox X) hf)
      (Term.boxtm (Term.eta ((VarSymb.step (.root (.bnd 0)) .here).ext q).inner
        ((X.compAt q).getD .VTypeOne) (Ctx.ref_inner (hq.ref_head (Ctx.ref_insert_root _ _ _)))))⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y)))
        (.VTypeBox ((X.compAt q).getD .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.eta ((VarSymb.step (.step (.root (.bnd 0)) .fst) .here).ext q).inner
        ((X.compAt q).getD .VTypeOne) (Ctx.ref_inner h'))⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ₂
      (Subst.at_ext_eta hT θ₂ q (Ctx.ref_here_of hT hf) hC h' h0')))
  unfold compVal
  exact sig_unboxtm ((sig_holeAt (Term.holeAt_pack s t).symm _).trans
    ((Term.holeAt_holeAt_sig _ _ _).symm.trans ((sig_holeAt_right _ key1).trans
      ((sig_holeAt_right _ key2.symm).trans ((Term.holeAt_holeAt_sig _ _ _).trans
        (sig_holeAt (Term.holeAt_pair_fst _ _) _))))))

/-- Under T, a pair's companion `snd :: q` is its second component's companion `q`. -/
theorem compVal_pair_snd {Γ : Ctx} {X Y : VarType} {a₀ : Ann X} {b₀ : Ann Y}
    (s : Term σ Γ.boxIn X a₀) (t : Term σ Γ.boxIn Y b₀) (q : List Step)
    {ps ps' : List (List Step)} (h : (VarType.VTypeProd X Y).CompOk ((.snd :: q) :: ps))
    (hq : Y.CompOk (q :: ps')) :
    compVal (σ := σ) (Term.pair s t) (.snd :: q) h = compVal t q hq := by
  obtain ⟨hT, hall, -⟩ := hq.resolve_left (List.cons_ne_nil _ _)
  have hC : Y.compAt q = some ((Y.compAt q).getD .VTypeOne) := by
    obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (hall q List.mem_cons_self)
    rw [hC]
    rfl
  have hr := Ctx.ref_insert_root Ctx.empty (.bnd 0)
    (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))
  have hf : (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))).ref
      (.step (.root (.bnd 0)) .snd) = some (.VTypeBox Y) := Ctx.ref_snd_of hr
  have h' := Ctx.ref_compAt hT q (Ctx.ref_here_of hT hf) hC
  let θ₁ := Subst.single (σ := σ)
    (Δ := Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))) (.bnd 0)
    (.tm (ShapeMap.pack (σ := σ) X Y).obj.2)
  have h0 : θ₁.at (.step (.step (.root (.bnd 0)) .here) .snd) =
      .tm (Term.eta (.step (.step (.root (.bnd 0)) .snd) .here) Y (Ctx.ref_here_of hT hf)) := by
    rw [Subst.at_proj θ₁ _ rfl, Subst.at_proj θ₁ _ rfl, Subst.at_single_root]
    dsimp only [ShapeMap.obj]
    rw [SubE.proj_boxtm_here _ hT]
    change SubE.tm (Term.collapse _ (Term.eta (VarSymb.step (.root (.bnd 0)) .snd).inner Y _)) = _
    exact SubE.tm_eq_of_sig ((Term.collapse_eta _ _ Y _).trans
      (Term.eta_congr (VarSymb.inner_collapse_zero _) Y _ _))
  have key1 : (⟨_, Term.holeAt (ShapeMap.pack (σ := σ) X Y).obj.2 (Term.boxtm (Term.eta
      ((VarSymb.step (.root (.bnd 0)) .here).ext (.snd :: q)).inner
      (((VarType.VTypeProd X Y).compAt (.snd :: q)).getD .VTypeOne)
      (Ctx.ref_inner (h.ref_head (Ctx.ref_insert_root _ _ _)))))⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y)))
        (.VTypeBox ((Y.compAt q).getD .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.eta ((VarSymb.step (.step (.root (.bnd 0)) .snd) .here).ext q).inner
        ((Y.compAt q).getD .VTypeOne) (Ctx.ref_inner h'))⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ₁
      (Subst.at_ext_eta hT θ₁ q (Ctx.ref_here_of hT hf) hC h' h0)))
  let θ₂ := Subst.single (σ := σ)
    (Δ := Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y))) (.bnd 0)
    (.tm (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) hf))
  have h0' : θ₂.at (.step (.root (.bnd 0)) .here) =
      .tm (Term.eta (.step (.step (.root (.bnd 0)) .snd) .here) Y (Ctx.ref_here_of hT hf)) := by
    rw [Subst.at_proj θ₂ _ rfl, Subst.at_single_root]
    exact SubE.proj_here_eta hT hf
  have key2 : (⟨_, Term.holeAt (Term.eta (.step (.root (.bnd 0)) .snd) (.VTypeBox Y) hf)
      (Term.boxtm (Term.eta ((VarSymb.step (.root (.bnd 0)) .here).ext q).inner
        ((Y.compAt q).getD .VTypeOne) (Ctx.ref_inner (hq.ref_head (Ctx.ref_insert_root _ _ _)))))⟩ :
      Σ c, Term σ (Ctx.empty.insert (.bnd 0) (VarType.VTypeProd (.VTypeBox X) (.VTypeBox Y)))
        (.VTypeBox ((Y.compAt q).getD .VTypeOne)) c) =
      ⟨_, Term.boxtm (Term.eta ((VarSymb.step (.step (.root (.bnd 0)) .snd) .here).ext q).inner
        ((Y.compAt q).getD .VTypeOne) (Ctx.ref_inner h'))⟩ :=
    sig_boxtm (Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ₂
      (Subst.at_ext_eta hT θ₂ q (Ctx.ref_here_of hT hf) hC h' h0')))
  unfold compVal
  exact sig_unboxtm ((sig_holeAt (Term.holeAt_pack s t).symm _).trans
    ((Term.holeAt_holeAt_sig _ _ _).symm.trans ((sig_holeAt_right _ key1).trans
      ((sig_holeAt_right _ key2.symm).trans ((Term.holeAt_holeAt_sig _ _ _).trans
        (sig_holeAt (Term.holeAt_pair_snd _ _) _))))))

omit [ModalSys.NoFour] in
/-- A root's tuple's companion's item, for either value of the flag. -/
theorem ref_tupB_comp {Γ : Ctx} {u : VarSymb} {R : VarType} (hu : Γ.ref u = some R) :
    ∀ (b : Bool), ModalSys.T = b → ∀ (q : List Step), q ∈ (R.bcB b).compsAllB b →
      Γ.boxIn.ref (u.ext (R.bcDec q)).inner = some (((R.bcB b).compAt q).getD .VTypeOne)
  | false, _, _, hq => absurd hq List.not_mem_nil
  | true, hT, q, hq => by
      obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains _ q hq)
      rw [hC]
      rw [VarType.compAt_bcDec R q hq] at hC
      exact Ctx.ref_inner (Ctx.ref_compAt hT _ hu hC)

/-- ⭐The contents of a root's tuple's companion `q`: the item of the root's companion `q`
    decodes to, for either value of the flag. -/
theorem compVal_tupB {Γ : Ctx} (u : VarSymb) (R : VarType) (hu : Γ.ref u = some R) :
    ∀ (b : Bool) (hb : ModalSys.T = b) (q : List Step) {ps : List (List Step)}
      (h : (R.bcB b).CompOk (q :: ps)) (hq : q ∈ (R.bcB b).compsAllB b),
      compVal (σ := σ) (tupB u R b hb hu) q h =
        ⟨_, Term.eta (u.ext (R.bcDec q)).inner _ (ref_tupB_comp hu b hb q hq)⟩
  | false, _, _, _, _, hq => absurd hq List.not_mem_nil
  | true, hT, q, _, h, hq => by
      obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp (VarType.compAt_hereChains _ q hq)
      have hC' : (R.bcB true).compAt q = some (((R.bcB true).compAt q).getD .VTypeOne) := by
        rw [hC]
        rfl
      have h' : Γ.ref (u.ext (R.bcDec q)) =
          some (.VTypeBox (((R.bcB true).compAt q).getD .VTypeOne)) := by
        have hC'' := hC
        rw [VarType.compAt_bcDec R q hq] at hC''
        rw [hC]
        exact Ctx.ref_compAt hT _ hu hC''
      let θ := Subst.single (σ := σ) (Δ := Γ) (.bnd 0) (.tm (Term.boxtm (tupB u R true hT hu)))
      have h0 : θ.at (.step (.root (.bnd 0)) .here) =
          .tm (Term.collapse (Ctx.collapses_boxIn_self hT Γ) (tupB u R true hT hu)) := by
        rw [Subst.at_proj θ _ rfl, Subst.at_single_root, SubE.proj_boxtm_here _ hT]
      have h2 := Subst.at_ext_collapse_tupB hT θ R u hu q hq _ _ hC' h' h0
      exact Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.box_at_inner_boxtm θ h2)

/-! ## Arrows and fresh roots on weakened terms -/

/-- An arrow into a larger target: the arrow, weakened. -/
theorem subst_arrow_tgt_mono {l : List VarType} {Δ Δ' : Ctx} (h : Δ.Le Δ') {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {T : VarType} {a : Ann T} (t : Term σ (ctxOf l).boxIn T a) :
    (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ' img) (ok_arrowS (himg.mono h))
        (coh_arrowS (himg.mono h)) t⟩ : Σ c, Term σ Δ' T c) =
      ⟨_, Term.mono h (Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg)
        (coh_arrowS himg) t)⟩ := by
  rw [Term.mono_subst]
  exact congrArg _ (Term.subst_congr_eq _ _ _ _ _ _ (Subst.sim_of fun v T _ _ => by
    rw [arrowS_mono]
    exact .refl _) t)

/-- An arrow on an item's η-expansion: the item's image. -/
theorem subst_arrow_eta_inner {l : List VarType} {Δ : Ctx} {img : ℕ → ℕ}
    (himg : ImgOk l Δ img) {x : VarSymb} {C : VarType}
    (hx : (ctxOf l).boxIn.ref x.inner = some C) :
    ∃ hw : Δ.ref (itemImg img x) = some C,
      (⟨_, Term.subst (arrowIdx img) (arrowS σ Δ img) (ok_arrowS himg) (coh_arrowS himg)
        (Term.eta x.inner C hx)⟩ : Σ c, Term σ Δ C c) = ⟨_, Term.eta (itemImg img x) C hw⟩ := by
  have he : (arrowS σ Δ img).at x.inner = .ren (itemImg img x) := by
    rw [VarSymb.inner_box ModalSys.NoFour.keepOnly]
    rfl
  have hw : Δ.ref (itemImg img x) = some C := by
    have := Subst.okRef_at (ok_arrowS (σ := σ) himg) hx
    rwa [he] at this
  exact ⟨hw, Term.subst_eta_renAt _ _ _ C x.inner _ hx hw he⟩

omit [ModalSys.NoFour] in
/-- Substituting a fresh root's value in a term from before it: the term, weakened. -/
theorem subst_single_free_mono_tm {lt bigl : List VarType} (hle : (ctxOf lt).Le (ctxOf bigl))
    {B : VarType} {e : SubE σ (ctxOf bigl)}
    (hθ : Subst.Ok (ctxOf (B :: lt)) (Subst.single (.free lt.length) e))
    (hc : Subst.Coh (Subst.singleIdx (.free lt.length) e) (ctxOf (B :: lt))
      (Subst.single (.free lt.length) e))
    (h : (ctxOf lt).Le (ctxOf (B :: lt))) {T : VarType} {a : Ann T} (x : Term σ (ctxOf lt) T a) :
    (⟨_, Term.subst (Subst.singleIdx (.free lt.length) e) (Subst.single (.free lt.length) e) hθ hc
        (Term.mono h x)⟩ : Σ c, Term σ (ctxOf bigl) T c) = ⟨_, Term.mono hle x⟩ := by
  rw [Term.subst_mono]
  refine Term.subst_ren hle _ _ _ (fun v T hv => Subst.single_at_ne ?_) x
  obtain ⟨r, hr, hlt, -⟩ := ref_rt hv
  rw [hr]
  exact fun h => absurd (Root.free.inj h) (Nat.ne_of_lt hlt)

/-! ## The plain step, assembled -/

section StepB

variable {lt cl : List VarType} {img : ℕ → ℕ} (A : VarType) (himg : ImgOk cl (ctxOf lt) img)

/-- The step's big context: the flat contents' return and its companions' returns. -/
abbrev stepCtxL (lt cl : List VarType) (A : VarType) : List VarType :=
  compsTys (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A) ++ A.bcB false :: lt

omit [ModalSys.NoFour] in
theorem stepLe (lt cl : List VarType) (A : VarType) : (ctxOf lt).Le (ctxOf (stepCtxL lt cl A)) :=
  (ctxOf_le_append [A.bcB false] lt).trans (legQ_le _ (stepQ A))

/-- ⭐The image root's value: the tuple component of the chain's value. -/
def stepARR : Σ c, Term σ (ctxOf (stepCtxL lt cl A)) A.bc c :=
  ⟨_, Term.holeRead (stepV₅ (σ := σ) A himg).2
    (Term.eta (((VarSymb.root (.bnd 0)).ext (compsFst ((bcT (A :: cl)).compsAllB ModalSys.T))).step
      .snd) A.bc (Ctx.ref_snd_of (Ctx.ref_compsFst _ (Ctx.ref_insert_root _ _ _))))⟩

/-- ⭐**The step's value identity** (P3): substituting the image root's value `stepARR` sends the
    grown target's tuple with companions to the chain's value.  Companion by companion
    (`compsFlat_ext`): the tuple's own value and the older roots' companions come down the chain
    from the old invariant's value; the new root's companions sit in the chain's value at their
    items' places (`tupCG_coh`), which is where the arrow sends their items. -/
theorem stepV₅_eq :
    (⟨_, Term.subst (Subst.singleIdx (.free lt.length) (.tm (stepARR A himg).2))
        (Subst.single (.free lt.length) (.tm (stepARR (σ := σ) A himg).2))
        (Subst.ok_single (stepLe lt cl A) rfl)
        (Subst.coh_single (ctxOf_fresh le_rfl) (stepLe lt cl A) rfl)
        (tupCompsImg (A :: cl) (extImg img cl.length lt.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2⟩ :
        Σ c, Term σ (ctxOf (stepCtxL lt cl A))
          ((bcT (A :: cl)).compsFlat ((bcT (A :: cl)).compsAllB ModalSys.T)) c) =
      stepV₅ A himg := by
  have hRM : (stepV₅ (σ := σ) A himg).2.getP
      (compsFst ((bcT (A :: cl)).compsAllB ModalSys.T) ++ [.fst]) =
      some ⟨_, _, Term.mono (legQ_le (l := A.bcB false :: lt)
        (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A))
        (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false)
          (tupImgT cl img himg).2)⟩ := by
    refine (getP_holeRead _ _ _).trans ?_
    refine (tupCG_read_main (σ := σ) (bcT cl) A ModalSys.T rfl _).trans ?_
    refine (getP_holeRead _ _ _).trans ?_
    refine (subC_read_main (σ := σ) _ _ _ _ _ _ _ _).trans ?_
    refine valQ_read_main (σ := σ) _ _ _ _ _ _ _ _ ?_
    refine (getP_holeRead _ _ _).trans ?_
    refine (packCC_read_fst (σ := σ) _ _ _ _ _ _ _ []).trans ?_
    rw [List.append_nil]
    exact (getP_pair_fst _ _ _).trans (getP_mono _ _ _ (tupCompsImg_read_fst _ _ _ _ _))
  obtain ⟨b₀, m, hm⟩ := getP_compsFst_some _ _ (stepV₅ (σ := σ) A himg).2
  obtain ⟨a₁, m₁, a₂, m₂, hmp⟩ := getP_prod_some m
  have hm' := hm.trans (some_of_sig hmp)
  have hm₁ : (stepV₅ (σ := σ) A himg).2.getP
      (compsFst ((bcT (A :: cl)).compsAllB ModalSys.T) ++ [.fst]) = some ⟨_, _, m₁⟩ :=
    (getP_append _ _ _ hm').trans ((getP_pair_fst _ _ _).trans (getP_nil _))
  have hA : (⟨_, (stepARR (σ := σ) A himg).2⟩ :
      Σ c, Term σ (ctxOf (stepCtxL lt cl A)) A.bc c) = ⟨a₂, m₂⟩ := by
    refine sig_of_some ((getP_nil _).symm.trans ((getP_holeRead _ _ _).trans
      ((getP_holeAt_eta _ (compsFst ((bcT (A :: cl)).compsAllB ModalSys.T) ++ [.snd])
        (FS_append (FS_compsFst _) (FS_cons (Or.inr rfl) FS_nil)) (VarSymb.ext_step _ _ _).symm
        _ []).trans ?_)))
    rw [List.append_nil]
    exact (getP_append _ _ _ hm').trans ((getP_pair_snd _ _ _).trans (getP_nil _))
  have e1 : (⟨_, Term.mono (stepLe lt cl A) (tupImgT (σ := σ) cl img himg).2⟩ :
      Σ c, Term σ (ctxOf (stepCtxL lt cl A)) (bcT cl) c) = ⟨a₁, m₁⟩ := by
    rw [← sig_of_some (hRM.symm.trans hm₁)]
    unfold Term.weaken
    rw [Term.mono_mono]
  refine compsFlat_ext _ _ (compsAllB_nodup _ _) _ _ ?_ ?_
  · refine Eq.trans ?_ hm'.symm
    refine (getP_subst _ _ _ _ _ (tupCompsImg_read_fst _ _ _ _ _)).trans (some_of_sig ?_)
    rw [tupImgT_ext himg (imgOk_ext himg)]
    exact sig_pair ((subst_single_free_mono_tm (stepLe lt cl A) _ _ _ _).trans e1)
      ((Term.subst_eta_tm _ _ _ _ _ _ _ (Subst.at_single_root _ _)).trans hA)
  · intro p hp
    have hT : ModalSys.T = true := by
      rcases Bool.eq_false_or_eq_true ModalSys.T with h | h
      · exact h
      · rw [h] at hp
        exact absurd hp List.not_mem_nil
    have hp' : p ∈ pairComps ((bcT cl).compsAllB ModalSys.T) ((A.bc).compsAllB ModalSys.T) := by
      rw [← compsAllB_prod]
      exact hp
    rcases pairComps_mem hp' with ⟨e, hq⟩ | ⟨e, hq⟩
    · generalize p.tail = q at e hq
      subst e
      have hc : (bcT cl).CompOk [q] := VarType.CompOk.single (VarType.compOk_compsAllB _ rfl _) hq
      have h₁ : (bcT (A :: cl)).CompOk [.fst :: q] :=
        VarType.CompOk.single (VarType.compOk_compsAllB _ rfl _) hp
      have hfq : .fst :: q ∈ (VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T := by
        rw [compsAllB_prod]
        exact List.mem_append_left _ (List.mem_map_of_mem hq)
      have hnq : .fst :: q ∉ stepQ A := fun h => by
        obtain ⟨_, _, e⟩ := List.mem_map.mp h
        cases e
      have hRC : (stepV₅ (σ := σ) A himg).2.getP
          (compsIdx ((bcT (A :: cl)).compsAllB ModalSys.T) (.fst :: q)) =
          some ⟨_, _, Term.mono (legQ_le (l := A.bcB false :: lt)
            (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A))
            (Term.weaken (ctxOf_fresh (l := lt) le_rfl).root (A.bcB false)
              (Term.subst (arrowIdx img) (arrowS σ (ctxOf lt) img) (ok_arrowS himg)
                (coh_arrowS himg) (compVal (tupT cl).2 q hc).2))⟩ := by
        refine (getP_holeRead _ _ _).trans ?_
        refine (tupCG_read_fst (σ := σ) (bcT cl) A ModalSys.T rfl _ q hp).trans ?_
        refine (getP_holeRead _ _ _).trans ?_
        refine (subC_read_idx' (σ := σ) _ _ _ _ _ _ _ _ hfq).trans ?_
        refine valQ_read_idx (σ := σ) _ _ _ _ _ _ _ _ hnq ?_
        refine (getP_holeRead _ _ _).trans ?_
        refine (packCC_read_idx_fst' (σ := σ) _ _ _ _ _ _ _ q hq).trans ?_
        exact (getP_pair_fst _ _ _).trans
          (getP_mono _ _ _ (tupCompsImg_read_idx _ _ _ _ _ q hq hc))
      refine Eq.trans ?_ hRC.symm
      refine (getP_subst _ _ _ _ _ (tupCompsImg_read_idx _ _ _ _ _ _ hp h₁)).trans
        (some_of_sig ?_)
      have e2 := (compVal_pair_fst (σ := σ)
        (Term.mono (ctxOf_le_append [A] cl).boxIn (tupT (σ := σ) cl).2)
        (tup (.root (.free cl.length)) A (ctxOf_ref_new A cl)) q h₁ hc).trans
        (mono_compVal (ctxOf_le_append [A] cl) (tupT (σ := σ) cl).2 q hc)
      refine (sig_subst _ _ _ ((sig_subst _ _ _ e2).trans
        ((subst_arrow_mono (ctxOf_le_append [A] cl) (himg.mono (ctxOf_le_append [A.bc] lt))
          (imgOk_ext himg) (fun r hr => if_neg (Nat.ne_of_lt hr)) _).trans
          (subst_arrow_tgt_mono (ctxOf_le_append [A.bc] lt) himg _)))).trans ?_
      refine (subst_single_free_mono_tm (stepLe lt cl A) _ _ _ _).trans ?_
      unfold Term.weaken
      rw [Term.mono_mono]
    · generalize p.tail = q at e hq
      subst e
      have hc' : (A.bc).CompOk [q] := VarType.CompOk.single (VarType.compOk_compsAllB _ rfl _) hq
      have h₁ : (bcT (A :: cl)).CompOk [.snd :: q] :=
        VarType.CompOk.single (VarType.compOk_compsAllB _ rfl _) hp
      obtain ⟨b, y, hy⟩ := getP_compsIdx_some _ _ (stepV₅ (σ := σ) A himg).2 (.snd :: q) hp
      have h3 : (stepV₅ (σ := σ) A himg).2.getP
          (compsIdx ((bcT (A :: cl)).compsAllB ModalSys.T) (.snd :: q)) =
          (stepV₅ (σ := σ) A himg).2.getP (compsFst ((bcT (A :: cl)).compsAllB ModalSys.T) ++
            .snd :: (encPath (A.bcDec q) ++ itemTail)) :=
        (getP_holeRead _ _ _).trans ((tupCG_coh (σ := σ) (bcT cl) A ModalSys.T rfl _ q hp).trans
          (getP_holeRead _ _ _).symm)
      have h4 : (stepARR (σ := σ) A himg).2.getP (encPath (A.bcDec q) ++ itemTail) =
          some ⟨_, b, y⟩ :=
        (getP_congr hA _).trans ((getP_pair_snd m₁ m₂ _).symm.trans
          ((getP_append _ _ _ hm').symm.trans (h3.symm.trans hy)))
      refine Eq.trans ?_ hy.symm
      refine (getP_subst _ _ _ _ _ (tupCompsImg_read_idx _ _ _ _ _ _ hp h₁)).trans
        (some_of_sig ?_)
      have e2 := (compVal_pair_snd (σ := σ)
        (Term.mono (ctxOf_le_append [A] cl).boxIn (tupT (σ := σ) cl).2)
        (tup (.root (.free cl.length)) A (ctxOf_ref_new A cl)) q h₁ hc').trans
        (compVal_tupB _ A (ctxOf_ref_new A cl) ModalSys.T rfl q hc' hq)
      obtain ⟨hw, e3⟩ := subst_arrow_eta_inner (σ := σ) (imgOk_ext (A := A) himg)
        (ref_tupB_comp (ctxOf_ref_new A cl) ModalSys.T rfl q hq)
      have hitem : itemImg (extImg img cl.length lt.length)
          ((VarSymb.root (.free cl.length)).ext (A.bcDec q)) =
          (VarSymb.root (.free lt.length)).ext (encPath (A.bcDec q) ++ itemTail) := by
        simp [itemImg, itemAt, VarSymb.ext_rt, VarSymb.ext_path, imgRoot, extImg, VarSymb.rt,
          VarSymb.path]
      refine (sig_subst _ _ _ ((sig_subst _ _ _ e2).trans
        (e3.trans (eta_addr_congr hitem hw (hitem ▸ hw))))).trans ?_
      exact Term.subst_eta_tm _ _ _ _ _ _ _
        (Subst.at_ext_getP _ _ (Subst.at_single_root _ _) h4)

end StepB

variable (hS : ModalSys.BStrong = true)

/-! ## The chain of a step, along any leg -/

/-- ⭐Substituting a fresh root's value in a returning possibility along a leg whose body is from
    before the root: the value substituted, the body weakened. -/
theorem subst_single_retS {lt bigl : List VarType} (hle : (ctxOf lt).Le (ctxOf bigl))
    (O : OutLeg (ctxOf lt)) {B : VarType} {e : SubE σ (ctxOf bigl)}
    (hθ : Subst.Ok (ctxOf (B :: lt)) (Subst.single (.free lt.length) e))
    (hc : Subst.Coh (Subst.singleIdx (.free lt.length) e) (ctxOf (B :: lt))
      (Subst.single (.free lt.length) e))
    (S : RShape) {a : Ann S.flat} (t : Term σ (ctxOf (B :: lt)) S.flat a) {V₀ : Ctx}
    [V₀.NoSlots] (hV : V₀.Le O.view) (Φ : WFF σ (V₀.insert (.bnd 0) S.ty) 1) :
    WFF.subst (Subst.singleIdx (.free lt.length) e) (Subst.single (.free lt.length) e) hθ hc
        Ctx.NoSlots.slots Ctx.NoSlots.slots
        ((O.mono (ctxOf_le_append [B] lt)).retS hS S t
          (WFF.mono ((hV.trans (O.le_view_mono (ctxOf_le_append [B] lt))).insert (.bnd 0) _) Φ)) =
      (O.mono hle).retS hS S (Term.subst _ _ hθ hc t)
        (WFF.mono ((hV.trans (O.le_view_mono hle)).insert (.bnd 0) _) Φ) := by
  cases O with
  | nec =>
      change WFF.retS hS S (Term.subst _ _ _ _ _) (WFF.subst _ _ _ _ _ _ _) = _
      refine WFF.retS_congr' hS S rfl ?_
      rw [WFF.subst_mono _ _ _ _ ((Ctx.NoSlots.slots (Γ := V₀)).insert _)]
      exact WFF.subst_ren _ _ _ _ _ _
        (fun v U hv => single_box_under_ren le_rfl _ v U ((hV.insert (.bnd 0) _).ref hv)) Φ
  | pos y hy =>
      have hyr : y.rt ≠ .free lt.length := by
        obtain ⟨Y, hY⟩ := hy
        obtain ⟨r, hr, hlt, -⟩ := ref_rt hY
        rw [hr]
        exact fun h => absurd (Root.free.inj h) (Nat.ne_of_lt hlt)
      have key : ∀ (z : VarSymb) (_hz : y = z)
          (P : ∃ Y, (ctxOf bigl).ref z = some (.VTypeDia Y))
          (hΔz : ((ctxOf bigl).diaIn z).SlotsFrom 0)
          (p : Subst.Ok (((ctxOf (B :: lt)).diaIn y).insert (.bnd 0) S.ty)
            (((Subst.single (.free lt.length) e).dia y z).under 0 0 _ hΔz.root))
          (q : Subst.Coh (VarSymb.shiftSlot (Subst.singleIdx (.free lt.length) e) 0 0)
            (((ctxOf (B :: lt)).diaIn y).insert (.bnd 0) S.ty)
            (((Subst.single (.free lt.length) e).dia y z).under 0 0 _ hΔz.root)),
          WFF.retxS hS z P S (Term.subst _ _ hθ hc t)
              (WFF.subst (VarSymb.shiftSlot (Subst.singleIdx (.free lt.length) e) 0 0)
                (((Subst.single (.free lt.length) e).dia y z).under 0 0 _ hΔz.root) p q
                (((Ctx.NoSlots.slots (Γ := ctxOf (B :: lt))).diaIn y).insert _) (hΔz.insert _)
                (WFF.mono ((hV.trans (OutLeg.le_view_mono (ctxOf_le_append [B] lt)
                  (.pos y hy))).insert (.bnd 0) _) Φ)) =
            ((OutLeg.pos y hy).mono hle).retS hS S (Term.subst _ _ hθ hc t)
              (WFF.mono ((hV.trans (OutLeg.le_view_mono hle (.pos y hy))).insert (.bnd 0) _)
                Φ) := by
        intro z hz P hΔz p q
        subst hz
        refine WFF.retxS_congr hS y _ S rfl ?_
        rw [WFF.subst_mono _ _ _ _ ((Ctx.NoSlots.slots (Γ := V₀)).insert _)]
        exact WFF.subst_ren _ _ _ _ _ _
          (fun v U hv => single_dia_under_ren le_rfl _ v U ((hV.insert (.bnd 0) _).ref hv)) Φ
      exact key (Subst.singleIdx (.free lt.length) e y) (if_neg hyr).symm _
        ((Ctx.NoSlots.slots (Γ := ctxOf bigl)).diaIn _) _ _

/-- ⭐**The chain of a step, along any leg**: a target with the old tuple's returning possibility
    of `∃e. pairUp (flatBody Φ)` along `O` stays consistent with the grown tuple's returning
    possibility of `Φ` at the image root.  Existence (`ret_extS`), packing (`packCC`), naming the
    companions (`ret_compS`), selecting them (`subC`) and `tupCG` give the atom at the chain's
    value; the substitution of `stepARR` for the image root sends the target atom there
    (`stepV₅_eq`, `subst_single_retS`). -/
theorem chainB_consistent {lt cl : List VarType} {img : ℕ → ℕ} (A : VarType)
    (himg : ImgOk cl (ctxOf lt) img) (O : OutLeg (ctxOf lt)) {V₀ : Ctx} [V₀.NoSlots]
    (hV : V₀.Le O.view) (Φ : WFF σ (V₀.insert (.bnd 0) (.VTypeBox (bcT (A :: cl)))) 1)
    {M : Set (WFF σ (ctxOf lt) 0)} (hM : Theory.Consistent M)
    (hex : Theory.Derives M (O.retS hS (.nec (tupShape ModalSys.T rfl cl))
      (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
      (WFF.mono (hV.insert (.bnd 0) _)
        (WFF.ex (.VTypeBox (A.bcB false)) (WFF.pairUp (flatBody A Φ)))))) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] lt) '' M ∪
      {(O.mono (ctxOf_le_append [A.bc] lt)).retS hS (.nec (tupShape ModalSys.T rfl (A :: cl)))
        (tupCompsImg (A :: cl) (extImg img cl.length lt.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2
        (WFF.mono ((hV.trans (O.le_view_mono (ctxOf_le_append [A.bc] lt))).insert (.bnd 0) _)
          Φ)}) := by
  have hu : (ctxOf lt).RootFresh (.free lt.length) := ctxOf_fresh le_rfl
  have hc₁ := retExtS_consistent hM hS O (.nec (tupShape ModalSys.T rfl cl)) _
    (WFF.mono ((hV.insert (.bnd 0) _).insert (.bnd 1) _) (WFF.pairUp (flatBody A Φ))) hex hu
  have hc₂ := consistent_step hc₁ (Proof.ret_map hS (O.mono (ctxOf_le_append [A.bcB false] lt))
    (S := (RShape.nec (tupShape ModalSys.T rfl cl)).ext (A.bcB false))
    (ShapeMap.packCC (σ := σ) (bcT cl) (A.bcB false) _ [] (VarType.compOk_compsAllB _ rfl _)
      (Or.inl rfl)) (stepV₁ A himg).2
    (WFF.mono ((O.le_view_mono (ctxOf_le_append [A.bcB false] lt)).insert (.bnd 0) _)
      (WFF.mono (hV.insert (.bnd 0) _) (flatBody A Φ)))
    (Proof.conv (by
      refine OutLeg.retS_congr hS _ _ rfl ?_
      dsimp only [RShape.extL, RShape.extR, ShapeMap.liftObj]
      erw [WFF.bodySplit_mono_pairUp_packCC (hX := VarType.compOk_compsAllB _ rfl _) hV
        (flatBody A Φ)]
      rw [WFF.mono_bodyRepl, Term.mono_mono]
      · try rw [WFF.mono_mono]
        rfl
      · exact O.le_view_mono _) (Proof.lookup List.mem_cons_self)))
  have hc₃ := compsS_consistent_leg hS (tupShape ModalSys.T rfl cl)
    (VarType.VTypeProd (bcT cl) (A.bcB false)) (pairComps ((bcT cl).compsAllB ModalSys.T) [])
    (VarType.compOk_pairComps (VarType.compOk_compsAllB _ rfl _) (Or.inl rfl))
    (O.mono (ctxOf_le_append [A.bcB false] lt)) (stepV₂ A himg).2
    (WFF.mono ((O.le_view_mono (ctxOf_le_append [A.bcB false] lt)).insert (.bnd 0) _)
      (WFF.mono (hV.insert (.bnd 0) _) (flatBody A Φ))) hc₂
    (Theory.Derives.of_mem (Or.inr rfl)) (stepQ A) (stepQ_ok cl A)
  have hc₄ := consistent_step hc₃ (Proof.ret_map hS
    ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono (legQ_le _ (stepQ A)))
    (S := .nec (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      (stepQ A ++ pairComps ((bcT cl).compsAllB ModalSys.T) []) (stepQ_ok cl A)))
    (ShapeMap.subC (σ := σ) (VarType.VTypeProd (bcT cl) (A.bcB false)) _
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T) (stepQ_ok cl A)
      (VarType.compOk_compsAllB _ rfl _) (stepQ_sub cl A)) _ _
    (Proof.conv (OutLeg.retS_congr hS _ _ rfl (WFF.bodyRepl_eta _).symm)
      (Proof.lookup List.mem_cons_self)))
  have hle₂ : V₀.Le ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono
      (legQ_le (VarType.VTypeProd (bcT cl) (A.bcB false)) (stepQ A))).view :=
    hV.trans ((O.le_view_mono _).trans ((O.mono _).le_view_mono _))
  have hc₅ := consistent_step hc₄ (Proof.ret_map hS
    ((O.mono (ctxOf_le_append [A.bcB false] lt)).mono (legQ_le _ (stepQ A)))
    (S := .nec (.boxC (VarType.VTypeProd (bcT cl) (A.bcB false))
      ((VarType.VTypeProd (bcT cl) (A.bcB false)).compsAllB ModalSys.T)
      (VarType.compOk_compsAllB _ rfl _)))
    (tupCG (σ := σ) (bcT cl) A ModalSys.T rfl) _
    (WFF.mono (hle₂.insert (.bnd 0) _) Φ)
    (Proof.conv (by
      refine OutLeg.retS_congr hS _ _ rfl ?_
      dsimp only [flatBody, ShapeMap.liftObj]
      rw [WFF.mono_mono, WFF.mono_mono, WFF.mono_bodyRepl, Term.mono_mono]
      exact hle₂) (Proof.lookup List.mem_cons_self)))
  refine consistent_of_subst hc₅ (Subst.single (.free lt.length) (.tm (stepARR A himg).2))
    (Subst.ok_single (stepLe lt cl A) rfl)
    (Subst.coh_single (ctxOf_fresh le_rfl) (stepLe lt cl A) rfl) Ctx.NoSlots.slots ?_
  rintro x (⟨y, hy, rfl⟩ | hx)
  · erw [subst_single_mono (stepLe lt cl A)]
    exact Or.inl (Or.inl (Or.inl ⟨_, Or.inl (Or.inl ⟨y, hy, rfl⟩), by rw [WFF.mono_mono]⟩))
  · rw [Set.mem_singleton_iff.mp hx]
    refine Or.inr (Set.mem_singleton_iff.mpr ?_)
    refine (subst_single_retS hS (stepLe lt cl A) O _ _
      (.nec (tupShape ModalSys.T rfl (A :: cl))) _ hV Φ).trans ?_
    clear hc₁ hc₂ hc₃ hc₄ hc₅ hex
    cases O with
    | nec => exact WFF.retS_congr hS _ (stepV₅_eq A himg) rfl
    | pos y hy => exact WFF.retxS_congr hS y _ _ (stepV₅_eq A himg) rfl

/-- The returning possibility a body over the roots committed so far with `A` becomes in the
    grown target, with companions. -/
def retAtomB {tt : NodeSt σ} {A : VarType} {cl clt : List VarType} {img : ℕ → ℕ}
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (Φ : WFF σ (bodyCtx (A :: cl) clt) 1) : WFF σ (ctxOf (A.bc :: tt.l)) 0 :=
  WFF.retS hS (.nec (tupShape ModalSys.T rfl (A :: cl)))
    (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
      (VarType.compOk_compsAllB _ rfl _)).2
    (WFF.mono ((ctxOf_le_of_suffix (ht.trans (List.suffix_cons _ _))).boxIn.insert (.bnd 0) _) Φ)

/-- ⭐**One body's atom is consistent with the grown target**: the source has
    `∃e. pairUp (flatBody Φ)` (`liftBody_ex_flat_mem`), so the target has it under the old
    invariant; existence (`ret_extS`), packing (`packCC`), naming the companions (`ret_compS`),
    selecting them (`subC`) and `tupCG` give the atom at the chain's value; and the substitution
    of `stepARR` for the image root sends the target atom there (`stepV₅_eq`). -/
theorem retAtomB_consistent {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtx cl clt) 1,
      liftBody ((List.suffix_cons A cl).trans hs') himgt Ψ ∈ ts.M →
        WFF.retS hS (.nec (tupShape ModalSys.T rfl cl))
          (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Ψ) ∈ tt.M)
    (Φ : WFF σ (bodyCtx (A :: cl) clt) 1) (hΦ : liftBody hs' himgt Φ ∈ ts.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      {retAtomB hS himg ht Φ}) :=
  chainB_consistent hS A himg .nec (ctxOf_le_of_suffix ht).boxIn Φ hw.1
    (Theory.Derives.of_mem (hinv _ (liftBody_ex_flat_mem hv hs' himgt Φ hΦ)))

/-! ## The plain step under T: the gained atoms and the grown target -/

section StepSet

variable {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType} {img imgt : ℕ → ℕ}

/-- What the target gains when the source's root `A` is committed, with companions. -/
def retSetB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) :
    Set (WFF σ (ctxOf (A.bc :: tt.l)) 0) :=
  {φ | ∃ Φ, liftBody hs' himgt Φ ∈ ts.M ∧ φ = retAtomB hS himg ht Φ}

/-- Finitely many of the gained atoms reduce to one, at the conjunction of their bodies. -/
theorem ret_listB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) (hv : Theory.IsMCS ts.M)
    (S : Set (WFF σ (ctxOf (A.bc :: tt.l)) 0)) :
    ∀ L : List (WFF σ (ctxOf (A.bc :: tt.l)) 0),
      (∀ δ ∈ L, δ ∈ S ∨ δ ∈ retSetB hS hs' himgt himg ht) →
      ∃ Φ, liftBody hs' himgt Φ ∈ ts.M ∧
        ∀ δ ∈ L, Theory.Derives (S ∪ {retAtomB hS himg ht Φ}) δ
  | [], _ => ⟨.top, hv.top_mem, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: L, h => by
      obtain ⟨Φ₀, hΦ₀, hL⟩ := ret_listB hs' himgt himg ht hv S L
        (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := ctxOf_fresh (l := A.bc :: tt.l) le_rfl
      rcases h δ List.mem_cons_self with hS' | ⟨Φ₁, hΦ₁, rfl⟩
      · refine ⟨Φ₀, hΦ₀, fun d hd => ?_⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Theory.Derives.of_mem (Or.inl hS')
        · exact hL d hd
      · have hand : ∀ Φ', Proof σ _ [retAtomB hS himg ht (Φ₀.and Φ₁)]
              (retAtomB hS himg ht Φ') →
            Theory.Derives (S ∪ {retAtomB hS himg ht (Φ₀.and Φ₁)}) (retAtomB hS himg ht Φ') :=
          fun Φ' p => ⟨[_], fun x hx => by
            rw [List.mem_singleton.mp hx]; exact Or.inr rfl, ⟨p⟩⟩
        have h₀ := hand Φ₀ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_left _ _ hu))
        have h₁ := hand Φ₁ (Proof.ret_monoS hS .nec _ _ _ (Proof.lookup List.mem_cons_self)
          (Proof.box_all_and_right _ _ hu))
        refine ⟨Φ₀.and Φ₁, hv.closed ⟨[_, _], fun x hx => ?_,
          ⟨Proof.and_intro (Proof.lookup List.mem_cons_self)
            (Proof.lookup (List.mem_cons_of_mem _ List.mem_cons_self))⟩⟩, fun d hd => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hΦ₀
          · rw [List.mem_singleton.mp hx]; exact hΦ₁
        rcases List.mem_cons.mp hd with rfl | hd
        · exact h₁
        · refine Derives.trans (fun x hx => ?_) (hL d hd)
          rcases hx with hx | hx
          · exact Theory.Derives.of_mem (Or.inl hx)
          · rw [Set.mem_singleton_iff.mp hx]; exact h₀

/-- ⭐**The gained atoms are consistent with the target**: finitely many reduce to one body
    (`ret_listB`), whose atom is consistent with it (`retAtomB_consistent`). -/
theorem retSetB_consistent (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : ∀ Ψ : WFF σ (bodyCtx cl clt) 1,
      liftBody ((List.suffix_cons A cl).trans hs') himgt Ψ ∈ ts.M →
        WFF.retS hS (.nec (tupShape ModalSys.T rfl cl))
          (tupCompsImg cl img himg _ (VarType.compOk_compsAllB _ rfl _)).2
          (WFF.mono ((ctxOf_le_of_suffix ht).boxIn.insert (.bnd 0) _) Ψ) ∈ tt.M) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
      retSetB hS hs' himgt himg ht) := by
  rintro ⟨L, hL, p⟩
  obtain ⟨Φ, hΦ, hder⟩ := ret_listB hS hs' himgt himg ht hv _ L hL
  exact retAtomB_consistent hS hs' himgt himg ht hv hw hinv Φ hΦ
    (Derives.trans (fun x hx => hder x hx) ⟨L, fun x hx => hx, p⟩)

/-- The target grown by the image of the source's root `A`, under strong B with companions:
    every body true at the source over the roots with `A` becomes a returning possibility at
    the tuple's shape with all its companions. -/
noncomputable def retStepB (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l) : NodeSt σ :=
  ⟨A.bc :: tt.l, complete (WFF.mono (ctxOf_le_append [A.bc] tt.l) '' tt.M ∪
    retSetB hS hs' himgt himg ht)⟩

/-- ⭐**One realisation step under strong B, with companions**: when the arrow's invariant with
    companions holds, the grown target is maximal consistent, extends the old one, and the
    invariant holds for one more root.  This is `retStep_ok` for every value of T. -/
theorem retStepB_ok (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvB hS ModalSys.T rfl ts tt cl img clt imgt) :
    Theory.IsMCS (retStepB hS hs' himgt himg ht).M ∧ Grows tt (retStepB hS hs' himgt himg ht) ∧
      RetInvB hS ModalSys.T rfl ts (retStepB hS hs' himgt himg ht) (A :: cl)
        (extImg img cl.length tt.l.length) clt imgt := by
  obtain ⟨_, _, _, _, h⟩ := hinv
  have hcons := retSetB_consistent hS hs' himgt himg ht hv hw h
  obtain ⟨hsub, hmcs⟩ := complete_spec hcons
  refine ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩,
    hs', imgOk_ext himg, ht.trans (List.suffix_cons _ _), himgt, fun Φ hΦ => ?_⟩
  exact hsub (Or.inr ⟨Φ, hΦ, rfl⟩)

end StepSet

/-! ## The reverse arrow under T: cross-arrow preservation with companions -/

omit [ModalSys.NoFour] in
/-- A slot's value with companions, read at its own value's place: the slot's contents. -/
theorem compsSlot_read_fst {Δ Δ' : Ctx} {u : VarSymb} {C : VarType}
    (hu : Δ.ref u = some (.VTypeBox C)) (hle : Δ.boxIn.Le Δ') :
    ∀ (cs : List (List Step)) (h : C.CompOk cs),
      (compsSlot (σ := σ) hu hle cs h).2.getP (compsFst cs) =
        some ⟨C, _, Term.eta u.inner C (hle.ref (Ctx.ref_inner hu))⟩
  | [], _ => getP_nil _
  | _ :: ps, h => (getP_pair_fst _ _ _).trans (compsSlot_read_fst hu hle ps h.tail)

/-- A body packed into a hole formula over the pair of the roots' tuple **with companions** and
    a slot: `pack2`, the tuple read off its value with companions. -/
def packC2 (cls : List VarType) (co : List (List Step)) (U : VarType)
    (Φ : WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) U) 1) :
    WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd ((bcT cls).compsFlat co) U)) 1 :=
  WFF.holeAt (Ctx.slotsFrom_empty.insert _)
    (Term.pair
      (Term.eta ((VarSymb.step (.root (.bnd 0)) .fst).ext (compsFst co)) (bcT cls)
        (Ctx.ref_compsFst co (Ctx.ref_fst_of (Ctx.ref_insert_root _ _ _))))
      (Term.eta (.step (.root (.bnd 0)) .snd) U (Ctx.ref_snd_of (Ctx.ref_insert_root _ _ _))))
    (pack2 cls U Φ)

/-- `packC2` read at a pair is `pack2` read at the pair with the first component's own value. -/
theorem WFF.holeAt_packC2 {Γ : Ctx} {d : ℕ} (hΓ : Γ.SlotsFrom d) {cls : List VarType}
    {co : List (List Step)} {U : VarType} {p : Ann ((bcT cls).compsFlat co)}
    (P : Term σ Γ ((bcT cls).compsFlat co) p) {q : Ann U} (Q : Term σ Γ U q) {p' : Ann (bcT cls)}
    {P' : Term σ Γ (bcT cls) p'} (hP : P.getP (compsFst co) = some ⟨_, p', P'⟩)
    (Φ : WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeAt hΓ (Term.pair P Q) (packC2 cls co U Φ) =
      WFF.holeAt hΓ (Term.pair P' Q) (pack2 cls U Φ) := by
  unfold packC2
  refine (WFF.subst_holeAt _ _ _ _ _ _ _).trans (WFF.holeAt_congr _ (sig_pair ?_
    (Term.holeAt_pair_snd _ _)) _)
  refine sig_of_some ((getP_nil _).symm.trans ((getP_holeAt_eta _ (.fst :: compsFst co)
    (FS_cons (Or.inl rfl) (FS_compsFst _)) rfl _ []).trans ?_))
  rw [List.append_nil]
  exact (getP_pair_fst _ _ _).trans hP

/-- `packC2` read at the images' tuple with companions: `pack2` read at the images' tuple. -/
theorem holeRead_packC2 {cls : List VarType} {Δ : Ctx} [Δ.NoSlots] {img : ℕ → ℕ}
    (himg : ImgOk cls Δ img) (co : List (List Step)) (hco : (bcT cls).CompOk co) {U : VarType}
    {x : Ann U} (X : Term σ Δ U x) (Φ : WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) U) 1) :
    WFF.holeRead (Term.pair (tupCompsImg cls img himg co hco).2 X) (packC2 cls co U Φ) =
      WFF.holeRead (Term.pair (tupImgT cls img himg).2 X) (pack2 cls U Φ) := by
  rw [WFF.holeRead_eq_holeAt, WFF.holeRead_eq_holeAt]
  exact WFF.holeAt_packC2 _ _ _ (tupCompsImg_read_fst _ _ _ _ _) Φ

omit [ModalSys.NoFour] in
/-- Weakening the companion unit's conjunct weakens its object. -/
theorem WFF.mono_unitBodyC {Γ Γ' : Ctx} [Γ.NoSlots] [Γ'.NoSlots] (h : Γ.Le Γ')
    (hS : ModalSys.BStrong = true) {C A : VarType} (co : List (List Step)) (ho : C.CompOk co)
    {a₀ : Ann A} (sb : Term σ Γ.boxIn A a₀) (cs : List (List Step)) (hcs : A.CompOk cs)
    (θ : WFF σ (Ctx.empty.insert (.bnd 0) (.VTypeProd (C.compsFlat co) (.VTypeBox A))) 1) :
    WFF.mono (h.boxIn.insert (.bnd 0) (.VTypeBox C)) (WFF.unitBodyC hS co ho sb cs hcs θ) =
      WFF.unitBodyC hS co ho (Term.mono h.boxIn sb) cs hcs θ := by
  unfold WFF.unitBodyC
  refine WFF.retS_congr hS _ ?_ ?_
  · rw [mono_compsVal h sb cs hcs]
    change (⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩ : Σ c, _) =
      ⟨_, Term.mono _ (Term.mono _ (compsVal sb cs hcs).2)⟩
    rw [Term.mono_mono, Term.mono_mono]
  · rw [WFF.mono_holeAt _ _ ((((Ctx.NoSlots.slots (Γ := Γ'.boxIn)).insert _).boxIn).insert _)]
    exact WFF.holeAt_congr _ (sig_pair ((mono_compsSlot _ _ _ co ho).trans
      (compsSlot_home _ _ _ _ co ho)) (congrArg (Sigma.mk _) (Term.mono_eta _ _ _ _))) θ

/-- ⭐The companion unit's conjunct at the reverse arrow's items, read at the forward arrow's
    source, is the reverse arrow's returning possibility with companions: its object is the
    reverse images' tuple with companions (`subst_arrow_compsVal`), and its body is `Φ`. -/
theorem liftBody_unitBodyC {lv cls clt : List VarType} (hs : cls <:+ lv) {imgt : ℕ → ℕ}
    (himgt : ImgOk clt (ctxOf lv) imgt) (hS : ModalSys.BStrong = true)
    (co : List (List Step)) (hco : (bcT cls).CompOk co) (cs : List (List Step))
    (hcs : (bcT clt).CompOk cs)
    (Φ : WFF σ ((ctxOf cls).boxIn.insert (.bnd 0) (.VTypeBox (bcT clt))) 1) :
    liftBody hs himgt (WFF.unitBodyC (Γ := ctxOf clt) hS co hco (tupT clt).2 cs hcs
        (packC2 cls co (.VTypeBox (bcT clt)) Φ)) =
      WFF.retS hS (.nec (.boxC (bcT clt) cs hcs)) (tupCompsImg clt imgt himgt cs hcs).2
        (WFF.mono ((ctxOf_le_of_suffix hs).boxIn.insert (.bnd 0) _) Φ) := by
  unfold liftBody WFF.unitBodyC
  refine WFF.retS_congr hS _ ?_ ?_
  · rw [Term.subst_mono]
    refine (Term.subst_congr _ (arrowS σ (ctxOf lv) imgt) _ (ok_arrowS himgt) _
      (coh_arrowS himgt) ?_ _).trans (subst_arrow_compsVal clt himgt cs hcs)
    refine Subst.sim_of fun v T _ hv => ?_
    obtain ⟨u, rfl, _⟩ := boxIn_item hv
    rw [Subst.set_ne _ _ (fun h => by cases h)]
    exact .refl _
  · rw [WFF.subst_holeAt]
    refine (WFF.holeAt_packC2 _ _ _ (P' := Term.mono (((ctxOf_le_of_suffix hs).boxIn).trans
      (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)) (tupT cls).2)
      ((getP_subst _ _ _ _ _ (compsSlot_read_fst _ _ _ _)).trans (some_of_sig ?_)) Φ).trans ?_
    · refine (Term.subst_eta_tm _ _ _ _ _ _
        (Term.mono (Ctx.le_insert (Ctx.NoSlots.slots (Γ := (ctxOf lv).boxIn)).root _)
          (Term.mono (ctxOf_le_of_suffix hs).boxIn (tupT cls).2)) ?_).trans ?_
      · rw [Subst.at_under_ne _ _ _ (by rw [VarSymb.inner_rt]; exact fun h => by cases h),
          Subst.box_at_inner_boxtm _ (by
            change Subst.set _ _ _ (.root (.bnd 0)) = _
            exact Subst.set_root _ _ _)]
        rfl
      · rw [Term.mono_mono]
    · refine (WFF.holeAt_congr _ (sig_pair rfl ?_) _).trans
        (holeAt_tupT_pack2 (ctxOf_le_of_suffix hs).boxIn Φ)
      exact Term.subst_eta_renAt _ _ _ _ _ _ _ _ (Subst.under_at_slot _ _ _ _ _)

/-- ⭐**Cross-arrow preservation under T**: committing the source's root `A` along the forward
    arrow keeps the reverse arrow's invariant with companions, over the extended list.  Were the
    reverse arrow's returning possibility for `Φ` to fail at the source, its negation would be a
    body over the forward arrow's roots (`liftBody_unitBodyC`), so the grown target would have
    `◇[d ↦ y] ¬U`; `Φ`, read there, is `θ(y, □sb)` (`holeRead_packC2`), and `ret_unitC` gives
    `◇[d ↦ y](¬U ∧ U)`, which is absurd (`Proof.ret_absurdS`). -/
theorem retStepB_rev {ts tt : NodeSt σ} {A : VarType} {cl clt : List VarType}
    {img imgt : ℕ → ℕ} (hs' : (A :: cl) <:+ ts.l) (himgt : ImgOk clt (ctxOf ts.l) imgt)
    (himg : ImgOk cl (ctxOf tt.l) img) (ht : clt <:+ tt.l)
    (hv : Theory.IsMCS ts.M) (hw : Theory.IsMCS tt.M)
    (hinv : RetInvB hS ModalSys.T rfl ts tt cl img clt imgt) :
    RetInvB hS ModalSys.T rfl (retStepB hS hs' himgt himg ht) ts clt imgt (A :: cl)
      (extImg img cl.length tt.l.length) := by
  obtain ⟨_, _, _, _, h⟩ := hinv
  obtain ⟨hsub, hmcs⟩ := complete_spec (retSetB_consistent hS hs' himgt himg ht hv hw h)
  have ht' : clt <:+ A.bc :: tt.l := ht.trans (List.suffix_cons _ _)
  refine ⟨ht', himgt, hs', imgOk_ext himg, fun Φ hΦ => ?_⟩
  by_contra hn
  have hneg := hv.neg_mem_iff.mpr hn
  have hΨ : liftBody hs' himgt (WFF.neg (WFF.unitBodyC (Γ := ctxOf clt) hS
      ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
      ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
      (packC2 (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) (.VTypeBox (bcT clt)) Φ))) ∈
      ts.M := by
    change WFF.neg (liftBody hs' himgt _) ∈ ts.M
    rw [liftBody_unitBodyC]
    exact hneg
  have hret := hsub (Or.inr ⟨_, hΨ, rfl⟩)
  have p₁ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomB hS himg ht (WFF.neg (WFF.unitBodyC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2 (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) (.VTypeBox (bcT clt)) Φ)))]
      (WFF.retS hS (.nec (tupShape ModalSys.T rfl (A :: cl)))
        (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length) (imgOk_ext himg) _
          (VarType.compOk_compsAllB _ rfl _)).2
        (WFF.neg (WFF.unitBodyC hS ((bcT (A :: cl)).compsAllB ModalSys.T)
          (VarType.compOk_compsAllB _ rfl _) (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)
          ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
          (packC2 (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) (.VTypeBox (bcT clt)) Φ)))) := by
    refine Proof.conv ?_ (Proof.lookup List.mem_cons_self)
    unfold retAtomB
    refine congrArg (WFF.retS hS _ _) ?_
    change WFF.imp (WFF.mono _ _) .bot = _
    rw [WFF.mono_unitBodyC (ctxOf_le_of_suffix ht')]
  have p₂ : Proof σ (ctxOf (A.bc :: tt.l)) [liftBody ht' (imgOk_ext himg) Φ]
      (WFF.holeRead (Term.pair (tupCompsImg (A :: cl) (extImg img cl.length tt.l.length)
          (imgOk_ext himg) _ (VarType.compOk_compsAllB _ rfl _)).2
        (Term.boxtm (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2)))
        (packC2 (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) (.VTypeBox (bcT clt)) Φ)) :=
    Proof.conv ((holeRead_packC2 (imgOk_ext himg) _ _ _ Φ).trans
      (holeRead_tupImgT_pack2 (imgOk_ext himg) _ Φ)).symm (Proof.lookup List.mem_cons_self)
  have p₃ : Proof σ (ctxOf (A.bc :: tt.l))
      [retAtomB hS himg ht (WFF.neg (WFF.unitBodyC (Γ := ctxOf clt) hS
        ((bcT (A :: cl)).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _) (tupT clt).2
        ((bcT clt).compsAllB ModalSys.T) (VarType.compOk_compsAllB _ rfl _)
        (packC2 (A :: cl) ((bcT (A :: cl)).compsAllB ModalSys.T) (.VTypeBox (bcT clt)) Φ))),
        liftBody ht' (imgOk_ext himg) Φ] .bot :=
    Proof.ret_absurdS hS _ _ _ (ctxOf_fresh (l := A.bc :: tt.l) le_rfl)
      (Proof.ret_unitC hS .nec _ _ _ _ (Term.mono (ctxOf_le_of_suffix ht').boxIn (tupT clt).2) _
        _ _
        (Proof.ofSubset (fun x hx => by
          rw [List.mem_singleton.mp hx]; exact List.mem_cons_self) p₁)
        (Proof.ofSubset (fun x hx => by
          rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ List.mem_cons_self) p₂))
  exact hmcs.1 ⟨[_, _], fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hret
    · rw [List.mem_singleton.mp hx]; exact hΦ, ⟨p₃⟩⟩

end BArrow

end V12M
