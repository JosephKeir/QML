import QML.QML_v12m_GCluInd
import QML.QML_v12m_GHubLimit
import QML.QML_v12m_ConeApex

/-!
# QML v12m — K45 and KD45 without lifts: truth at the world asked about

With the hub (`GNetSt.HubOn M₀`; docs, "K45 and KD45 without both lifts: the hub", step 5) the
world asked about, `gsrcWorld`, is put on top of the cluster model as the apex of a cone
(`Model.ConeData.cone`) over the tree's root.

* `hubV`: the apex's `□` view read at the hub along the edge, `hubV_sat`: what it satisfies is
  what the hub holds of the edge's image (`ctruth`).
* ⭐`apex_box_iff`, ⭐`apex_dia_iff`: at the apex of any cone keyed to `hubV`, `□ψ` and `◇_x ψ`
  hold exactly when the world asked about holds them — `four_box`, `five_box`, `five_dia` and
  `four_dia`, and the edge (`gltr_hub`).
-/

namespace V12M

variable [ModalSys]

namespace GArrow

open BArrow Model

variable {σ : Signature} [Countable σ.FuncSyms] [Countable σ.RelSyms]
  {hF : ModalSys.Four = true} {l₀ : List VarType} {M₀ : Set (WFF σ (ctxOf l₀) 0)}

/-! ## The flags -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hubOn_T (hh : GNetSt.HubOn M₀) : ModalSys.T = false := by
  have h := hh.1
  cases hT : ModalSys.T
  · rfl
  · simp [ModalSys.hubFlags, ModalSys.axNeed, hT] at h

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hubOn_B (hh : GNetSt.HubOn M₀) : ModalSys.B = false := by
  have h := hh.1
  cases hB : ModalSys.B
  · rfl
  · simp [ModalSys.hubFlags, hB] at h

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
theorem hubOn_BS (hX : CluFlags) (hh : GNetSt.HubOn M₀) : ModalSys.BStrong = false :=
  Bool.eq_false_iff.mpr fun hS => Bool.false_ne_true ((hubOn_B hh).symm.trans (hX.bS hS))

variable (hM₀ : Theory.IsMCS M₀) (hX : CluFlags) (hh : GNetSt.HubOn M₀)

include hh in
/-- With T off, the cluster model's `Ind` is equality. -/
theorem hub_ind : ∀ {A : VarType} {w : (cmodel hF hM₀ hX).frame.W}
    (o o' : (cmodel hF hM₀ hX).frame.Dom A w), (cmodel hF hM₀ hX).Ind o o' → o = o' :=
  fun _ _ h => h.2 (hubOn_T hh)

/-! ## The `□` view at the hub -/

variable (hF) in
/-- ⭐**The `□` view of the world asked about at a stage, read at the hub along the edge.** -/
noncomputable def hubV (i : ℕ) :
    (cmodel hF hM₀ hX).Env ((ctxOf (gnet hF M₀ i).src.l).kView none) (groot hF M₀) :=
  Model.substEnv (eS σ _ (fmapL hF M₀ [])) (ok_eS_kView (hubOk hM₀ hh i))
    (Ctx.noProjLast_boxIn _) (ccanonEnv hM₀ hX (groot hF M₀) (hstg hF M₀ i))

/-- A `□`-view formula of the world asked about, sent along the edge into the hub. -/
noncomputable abbrev hubW (i : ℕ) (φ : WFF σ ((ctxOf (gnet hF M₀ i).src.l).kView none) 0) :
    WFF σ (ctxOf (glat (groot hF M₀) (hstg hF M₀ i))) 0 :=
  WFF.subst (eIdx (fmapL hF M₀ [])) (eS σ _ (fmapL hF M₀ [])) (ok_eS_kView (hubOk hM₀ hh i))
    (coh_eS_kView (hubOk hM₀ hh i)) Ctx.NoSlots.slots Ctx.NoSlots.slots φ

/-- ⭐What the hub's reading satisfies is what the hub holds of the edge's image. -/
theorem hubV_sat (i : ℕ) (φ : WFF σ ((ctxOf (gnet hF M₀ i).src.l).kView none) 0) :
    (cmodel hF hM₀ hX).sat (hubV hF hM₀ hX hh i) φ ↔
      hubW hM₀ hh i φ ∈ ((gnet hF M₀ (hrnd hF M₀ i)).st []).M :=
  (Model.sat_subst _ _ (coh_eS_kView (hubOk hM₀ hh i)) Ctx.NoSlots.slots Ctx.NoSlots.slots
    (Ctx.noProjLast_boxIn _) _ φ).symm.trans (ctruth hX (groot hF M₀) (hstg hF M₀ i) _)

/-- Reading the hub's view at a later stage is reading it at the earlier one. -/
theorem hubV_mono {i j : ℕ} (hij : i ≤ j) {v : VarSymb} {T : VarType}
    (hv : ((ctxOf (gnet hF M₀ i).src.l).kView none).ref v = some T) :
    (hubV hF hM₀ hX hh j).ref v
        (((ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf).kView none).ref hv) =
      (hubV hF hM₀ hX hh i).ref v hv := by
  have key : ∀ k (hk : ((ctxOf (gnet hF M₀ k).src.l).kView none).ref v = some T),
      (hubV hF hM₀ hX hh k).ref v hk = interp (ccanonEnv hM₀ hX (groot hF M₀) (hstg hF M₀ k))
        (hubTm hM₀ hh k (Term.eta v T hk)).2 := by
    intro k hk
    rw [← interp_eta (hubV hF hM₀ hX hh k) v hk]
    exact (interp_subst _ _ (coh_eS_kView (hubOk hM₀ hh k)) (Ctx.noProjLast_boxIn _) _ _).symm
  rw [key, key,
    ← Term.mono_eta ((ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf).kView none) v T hv,
    ← hubTm_mono hM₀ hh hij]
  exact interp_mono (ccanonEnv_le hX (groot hF M₀) (hstg_monotone hM₀ hh hij)) _

/-! ## The first cone: all of the hub's objects -/

variable (hF) in
/-- ⭐**The first cone's data**: the hub with all of its objects, under the term model of the world
    asked about. -/
noncomputable def hubFull : (cmodel hF hM₀ hX).ConeData where
  ρ := groot hF M₀
  D := (gsrcWorld hF M₀ hM₀ hh).D
  funcInterp := (gsrcWorld hF M₀ hM₀ hh).canonFunc
  relInterp := (gsrcWorld hF M₀ hM₀ hh).canonRel
  DefN _ _ := True
  DefP _ _ := True
  necMap := by intros; trivial
  necPair := by intros; trivial
  necUnit := trivial
  posMap := by intros; trivial
  posStrength := by intros; trivial
  necDup := by intros; trivial
  posKeep := by intros; trivial
  posSide := by intros; trivial
  posSerial hD := by
    obtain ⟨p, hp⟩ := (cmodel hF hM₀ hX).posSerial hD (groot hF M₀)
    exact ⟨p, trivial, hp⟩
  keepLiftN hF' _ hl a o := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).keepLift hF' hl a o
    exact ⟨m, trivial, hm⟩
  keepLiftP hF' _ hl a o := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).keepLift hF' hl a o
    exact ⟨m, trivial, hm⟩
  necSide hV h5 _ a n := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).necSide_exists hV h5 a n
    exact ⟨m, trivial, fun b => hub_ind hM₀ hX hh _ _ (hm b)⟩

variable (hF) in
/-- The first cone. -/
noncomputable abbrev hubCone₀ : Model.{0, 0} σ :=
  (hubFull hF hM₀ hX hh).cone (hubOn_T hh) (hubOn_B hh) (hubOn_BS hX hh) (hub_ind hM₀ hX hh)

/-- The world asked about's base objects at a stage: its terms' classes. -/
noncomputable abbrev hubBase (i : ℕ) (v : VarSymb)
    (h : (ctxOf (gnet hF M₀ i).src.l).ref v = some .Var) : (gsrcWorld hF M₀ hM₀ hh).D :=
  (gsrcWorld hF M₀ hM₀ hh).cls i (.var v h)

theorem hubBase_mono {i j : ℕ} (hij : i ≤ j) (v : VarSymb)
    (h : (ctxOf (gnet hF M₀ i).src.l).ref v = some .Var) :
    hubBase hM₀ hh j v ((ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf).ref h) =
      hubBase hM₀ hh i v h :=
  (gsrcWorld hF M₀ hM₀ hh).cls_lift hij (.var v h)

variable (hF) in
/-- ⭐The first cone's environment at a stage. -/
noncomputable def hubE₀ (i : ℕ) :
    (hubCone₀ hF hM₀ hX hh).Env (ctxOf (gnet hF M₀ i).src.l) none :=
  ConeData.apexEnv _ _ _ _ _ hF (Ctx.Presented.noProjLast _) (hubBase hM₀ hh i)
    (hubV hF hM₀ hX hh i) (fun _ _ _ => trivial) (fun _ _ _ => trivial)

theorem hubE₀_agree {i j : ℕ} (hij : i ≤ j) :
    Env.Agree (ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf) (hubE₀ hF hM₀ hX hh i)
      (hubE₀ hF hM₀ hX hh j) :=
  ConeData.apexEnv_agree (hInd := hub_ind hM₀ hX hh) _ (hubBase_mono hM₀ hh hij)
    fun _ _ h => hubV_mono hM₀ hX hh hij h

theorem hubE₀_keyed (i : ℕ) : ConeData.Keyed hF (hubE₀ hF hM₀ hX hh i) (hubV hF hM₀ hX hh i) :=
  ConeData.apexEnv_keyed (hInd := hub_ind hM₀ hX hh)

/-! ## `□` and `◇` at the apex -/

section Apex

variable {hM₀ hX hh}

/-- ⭐⭐**`□` at the apex**: of a cone keyed to an environment satisfying what the hub holds of
    the edge's image, `□ψ` holds exactly when the world asked about holds it — `four_box` and the
    edge forward, `five_box` and the edge back. -/
theorem apex_box_iff {c : (cmodel hF hM₀ hX).ConeData} {hT : ModalSys.T = false}
    {hB : ModalSys.B = false} {hS : ModalSys.BStrong = false}
    {hInd : ∀ {A : VarType} {w : (cmodel hF hM₀ hX).frame.W}
      (o o' : (cmodel hF hM₀ hX).frame.Dom A w), (cmodel hF hM₀ hX).Ind o o' → o = o'}
    {i : ℕ} {E : (c.cone hT hB hS hInd).Env (ctxOf (gnet hF M₀ i).src.l) none}
    {V : (cmodel hF hM₀ hX).Env ((ctxOf (gnet hF M₀ i).src.l).kView none) c.ρ}
    (hK : ConeData.Keyed hF E V)
    (hV : ∀ φ, (cmodel hF hM₀ hX).sat V φ ↔
      hubW hM₀ hh i φ ∈ ((gnet hF M₀ (hrnd hF M₀ i)).st []).M)
    (ψ : WFF σ ((ctxOf (gnet hF M₀ i).src.l).kView none) 0) :
    (c.cone hT hB hS hInd).sat E (.box ψ) ↔ WFF.box ψ ∈ (gsrcWorld hF M₀ hM₀ hh).M i := by
  rw [ConeData.sat_apex_box hK ψ, hV]
  constructor
  · intro h
    by_contra hn
    have h1 : WFF.box (WFF.neg (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _)
        Ctx.NoSlots.slots ψ))) ∈ (gsrcWorld hF M₀ hM₀ hh).M i := by
      by_contra h2
      exact hn (BWorld.mem_of_provable (Δ := [_]) (fun χ hχ => by
          rw [List.mem_singleton.mp hχ]
          exact ((gsrcWorld hF M₀ hM₀ hh).mcs i).neg_mem_iff.mpr h2)
        ⟨Proof.five_box hF hX.five (Proof.lookup List.mem_cons_self)⟩)
    have h3 := gltr_hub hM₀ hh i _ h1
    exact ((gw hM₀ (groot hF M₀)).mcs (hstg hF M₀ i)).neg_mem_iff.mp h3 h
  · intro h
    have h1 : WFF.box (WFF.box (WFF.shift (Ctx.shifts_boxIn_boxIn hF _)
        Ctx.NoSlots.slots ψ)) ∈ (gsrcWorld hF M₀ hM₀ hh).M i :=
      BWorld.mem_of_provable (Δ := [_]) (fun χ hχ => by
          rw [List.mem_singleton.mp hχ]
          exact h)
        ⟨Proof.four_box hF (Proof.lookup List.mem_cons_self)⟩
    exact gltr_hub hM₀ hh i _ h1

/-- ⭐⭐**`◇_x` at the apex**: `five_dia` and the edge forward, `four_dia` and the edge back. -/
theorem apex_dia_iff {c : (cmodel hF hM₀ hX).ConeData} {hT : ModalSys.T = false}
    {hB : ModalSys.B = false} {hS : ModalSys.BStrong = false}
    {hInd : ∀ {A : VarType} {w : (cmodel hF hM₀ hX).frame.W}
      (o o' : (cmodel hF hM₀ hX).frame.Dom A w), (cmodel hF hM₀ hX).Ind o o' → o = o'}
    {i : ℕ} {E : (c.cone hT hB hS hInd).Env (ctxOf (gnet hF M₀ i).src.l) none}
    {V : (cmodel hF hM₀ hX).Env ((ctxOf (gnet hF M₀ i).src.l).kView none) c.ρ}
    (hK : ConeData.Keyed hF E V)
    (hV : ∀ φ, (cmodel hF hM₀ hX).sat V φ ↔
      hubW hM₀ hh i φ ∈ ((gnet hF M₀ (hrnd hF M₀ i)).st []).M)
    {x : VarSymb} (hx : ∃ X, (ctxOf (gnet hF M₀ i).src.l).ref x = some (.VTypeDia X))
    (ψ : WFF σ ((ctxOf (gnet hF M₀ i).src.l).diaIn x) 0) :
    (c.cone hT hB hS hInd).sat E (.dia x hx ψ) ↔
      WFF.dia x hx ψ ∈ (gsrcWorld hF M₀ hM₀ hh).M i := by
  rw [ConeData.sat_apex_dia hK hx ψ]
  constructor
  · intro h
    by_contra hn
    have hb : WFF.boxx x hx ψ.neg ∈ (gsrcWorld hF M₀ hM₀ hh).M i :=
      BWorld.mem_of_provable (Δ := [(WFF.dia x hx ψ).neg]) (fun χ hχ => by
          rw [List.mem_singleton.mp hχ]
          exact ((gsrcWorld hF M₀ hM₀ hh).mcs i).neg_mem_iff.mpr hn)
        ⟨Proof.boxx_neg_of_not_dia (Γ := (gsrcWorld hF M₀ hM₀ hh).ctx i) x hx ψ⟩
    have h1 : WFF.box (WFF.boxx (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots ψ.neg)) ∈
        (gsrcWorld hF M₀ hM₀ hh).M i :=
      BWorld.mem_of_provable (Δ := [_]) (fun χ hχ => by
          rw [List.mem_singleton.mp hχ]
          exact hb)
        ⟨Proof.four_dia hF hx (Proof.lookup List.mem_cons_self)⟩
    have h2 := (hV _).mpr (gltr_hub hM₀ hh i _ h1)
    obtain ⟨X, hX', a, ha⟩ := h
    exact h2 ⟨X, hX', a, fun hn' => hn' ha⟩
  · intro h
    have h1 : WFF.box (WFF.dia (.step x .keep) (Ctx.exists_keep_dia hF hx)
        (WFF.shift (Ctx.shifts_diaIn_keep hF _ x) Ctx.NoSlots.slots ψ)) ∈
        (gsrcWorld hF M₀ hM₀ hh).M i :=
      BWorld.mem_of_provable (Δ := [_]) (fun χ hχ => by
          rw [List.mem_singleton.mp hχ]
          exact h)
        ⟨Proof.five_dia hF hX.five hx (Proof.lookup List.mem_cons_self)⟩
    exact (hV _).mpr (gltr_hub hM₀ hh i _ h1)

end Apex

/-! ## The cone: the objects the world asked about names -/

omit [Countable σ.FuncSyms] [Countable σ.RelSyms] in
include hX hh in
theorem hubSh : ModalSys.shaped = false := shaped_false_of (hubOn_T hh) (hubOn_BS hX hh)

theorem hubNb_mono {i j : ℕ} (hij : i ≤ j) {A : VarType} {a : Ann (.VTypeBox A)}
    (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeBox A) a) :
    ConeData.nb (interp (hubE₀ hF hM₀ hX hh j)
      (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf) t)) =
      ConeData.nb (interp (hubE₀ hF hM₀ hX hh i) t) := by
  rw [interp_mono (hubE₀_agree hM₀ hX hh hij)]

theorem hubPb_mono {i j : ℕ} (hij : i ≤ j) {A : VarType} {a : Ann (.VTypeDia A)}
    (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeDia A) a) :
    ConeData.pb (interp (hubE₀ hF hM₀ hX hh j)
      (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf) t)) =
      ConeData.pb (interp (hubE₀ hF hM₀ hX hh i) t) := by
  rw [interp_mono (hubE₀_agree hM₀ hX hh hij)]

variable (hF) in
/-- A necessary object of the hub named at the apex: the first cone's value of a term of the
    world asked about. -/
def HubDefN (A : VarType) (n : (cmodel hF hM₀ hX).frame.Nec A (groot hF M₀)) : Prop :=
  ∃ (i : ℕ) (a : Ann (.VTypeBox A)) (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeBox A) a),
    ConeData.nb (interp (hubE₀ hF hM₀ hX hh i) t) = n

variable (hF) in
/-- A possible object of the hub named at the apex. -/
def HubDefP (A : VarType) (p : (cmodel hF hM₀ hX).frame.Pos A (groot hF M₀)) : Prop :=
  ∃ (i : ℕ) (a : Ann (.VTypeDia A)) (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeDia A) a),
    ConeData.pb (interp (hubE₀ hF hM₀ hX hh i) t) = p

/-- Under strong D the world asked about names a possible object of `𝟙` with a nonempty extent:
    its Henkin witness for the axiom, read at the hub (`apex_dia_iff`). -/
theorem hubDefP_serial (hD : ModalSys.DStrong = true) :
    ∃ p : (cmodel hF hM₀ hX).frame.Pos .VTypeOne (groot hF M₀),
      HubDefP hF hM₀ hX hh .VTypeOne p ∧ Nonempty ((cmodel hF hM₀ hX).posEval p).1 := by
  have hax : (WFF.somePoss : WFF σ ((gsrcWorld hF M₀ hM₀ hh).ctx 0) 0) ∈
      (gsrcWorld hF M₀ hM₀ hh).M 0 :=
    BWorld.mem_of_provable (Δ := []) (fun _ h => by simp at h) ⟨Proof.D_ex hD⟩
  obtain ⟨j, _, _, t, hmem⟩ := (gsrcWorld hF M₀ hM₀ hh).exW_term hax
  match t with
  | .diatm x hx u =>
      obtain ⟨X, hX'⟩ := id hx
      have hm : WFF.dia x ⟨X, hX'⟩ .top ∈ (gsrcWorld hF M₀ hM₀ hh).M j := by
        have e : (WFF.instantiate Ctx.NoSlots.slots (Term.diatm x hx u)
            (WFF.mono ((ctxOf_le_of_suffix ((gsrcWorld hF M₀ hM₀ hh).suf (Nat.zero_le j))).insert
              (.bnd 0) (.VTypeDia .VTypeOne))
              (.dia (.root (.bnd 0)) ⟨.VTypeOne, Ctx.ref_insert_root _ (.bnd 0) _⟩ .top))) =
            WFF.dia x ⟨X, hX'⟩ .top := rfl
        rw [← e]
        exact hmem
      obtain ⟨Y, hY, ⟨⟨_ | s, ⟨r⟩⟩, ha⟩, -⟩ := (apex_dia_iff (hubE₀_keyed hM₀ hX hh j)
        (hubV_sat hM₀ hX hh j) ⟨X, hX'⟩ .top).mpr hm
      · exact False.elim r
      obtain ⟨hE, -⟩ := posSec_of_eq (dia_beta (hubE₀ hF hM₀ hX hh j) hx hY u)
      exact ⟨_, ⟨j, _, Term.diatm x hx u, rfl⟩,
        ⟨⟨⟨s, ⟨r⟩⟩, (Set.ext_iff.mp hE ⟨some s, ⟨r⟩⟩).mpr ha⟩⟩⟩

/-- ⭐**With a lift flag, every hub object of the type is read at a kept address of the world asked
    about**: it is a hub term's value (`cdefinable_fromDom`), and the term is eventually lifted
    (`hub_lift_limit`). -/
theorem hub_lifted {T : VarType} (hl : T.liftableR = true)
    (o : (cmodel hF hM₀ hX).frame.Dom T (groot hF M₀)) :
    ∃ (j : ℕ) (v : VarSymb) (hr : (ctxOf (gnet hF M₀ j).src.l).ref v = some T),
      (hubV hF hM₀ hX hh j).ref (.step v .keep)
        (Ctx.ref_keep_of' hF hr (VarType.keepable_of_liftableR hl)) = o := by
  obtain ⟨i', a, t', ht'⟩ := cdefinable_fromDom hM₀ hX T (groot hF M₀) o
  obtain ⟨j, hj, r, hr, L, hL, he⟩ := hub_lift_limit (n := gbirth hF M₀ (groot hF M₀).2 + i')
    hM₀ hh t' hl
  have hi : i' ≤ hstg hF M₀ j := by
    have := (hstg_spec (hF := hF) hM₀ hh j).1
    omega
  refine ⟨j, .root (.free r), hr, ?_⟩
  have hok := hubOk hM₀ hh j (.step (.root (.free r)) .keep) T rfl
    (Ctx.boxIn_keep_of' hF hr (VarType.keepable_of_liftableR hl))
  rw [he] at hok
  have hLe : (ctxOf L).Le (ctxOf (glat (groot hF M₀) (hstg hF M₀ j))) := by
    by_contra hn
    rw [show entOf (ctxOf (glat (groot hF M₀) (hstg hF M₀ j))) (.inr ⟨L, T, a, _⟩) = .hide from
      dif_neg hn] at hok
    exact hok
  have hθ : (eS σ (ctxOf (glat (groot hF M₀) (hstg hF M₀ j))) (fmapL hF M₀ [])).at
      (.step (.root (.free r)) .keep) =
      .tm (Term.mono hLe (Term.mono (ctxOf_le_of_suffix hL) t')) := by
    rw [Subst.at_nonproj _ rfl, eS_item _ rfl, he, entOf_tm hLe]
  unfold hubV
  rw [substEnv_ref, entryVal_congr _ hθ _ rfl]
  change interp _ (Term.mono hLe (Term.mono _ t')) = o
  rw [Term.mono_mono]
  exact cinterp_lift hX ht' hi

/-- Every necessary hub object of a type lifted by flag is the apex's. -/
theorem hub_defN_of_lift {A : VarType} (hl : (VarType.VTypeBox A).liftableR = true)
    (n : (cmodel hF hM₀ hX).frame.Nec A (groot hF M₀)) : HubDefN hF hM₀ hX hh A n := by
  obtain ⟨j, v, hr, hval⟩ := hub_lifted hM₀ hX hh hl n
  exact ⟨j, _, Term.eta v _ hr, by
    rw [interp_eta]
    exact ((hubE₀_keyed hM₀ hX hh j).1 v A hr).trans hval⟩

/-- Every possible hub object of a type lifted by flag is the apex's. -/
theorem hub_defP_of_lift {A : VarType} (hl : (VarType.VTypeDia A).liftableR = true)
    (p : (cmodel hF hM₀ hX).frame.Pos A (groot hF M₀)) : HubDefP hF hM₀ hX hh A p := by
  obtain ⟨j, v, hr, hval⟩ := hub_lifted hM₀ hX hh hl p
  exact ⟨j, _, Term.eta v _ hr, by
    rw [interp_eta]
    exact ((hubE₀_keyed hM₀ hX hh j).2 v A hr).trans hval⟩

variable (hF) in
/-- ⭐**The cone's data**: the hub with the objects the world asked about names, under its term
    model.  With strong 5, strong 4 (docs, "the hub", 6). -/
noncomputable def hubData (hFS : ModalSys.FiveStrong = true → ModalSys.FourStrong = true) :
    (cmodel hF hM₀ hX).ConeData where
  ρ := groot hF M₀
  D := (gsrcWorld hF M₀ hM₀ hh).D
  funcInterp := (gsrcWorld hF M₀ hM₀ hh).canonFunc
  relInterp := (gsrcWorld hF M₀ hM₀ hh).canonRel
  DefN := HubDefN hF hM₀ hX hh
  DefP := HubDefP hF hM₀ hX hh
  necMap := by
    intro A B f n hn
    obtain ⟨i, _, t, rfl⟩ := hn
    exact ⟨i, _, (Canon.applyG (.boxMap f) t).2, by rw [interp_applyG (hubSh hX hh)]; rfl⟩
  necPair := by
    intro A B a b ha hb
    obtain ⟨i, _, t, rfl⟩ := ha
    obtain ⟨j, _, u, rfl⟩ := hb
    refine ⟨max i j, _, (Canon.applyG (.boxPair A B)
      (.pair (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_left i j)).suf) t)
        (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_right i j)).suf) u))).2, ?_⟩
    rw [interp_applyG (hubSh hX hh)]
    change (cmodel hF hM₀ hX).ops.necPair (ConeData.nb (interp (hubE₀ hF hM₀ hX hh _) _))
      (ConeData.nb (interp (hubE₀ hF hM₀ hX hh _) _)) = _
    rw [hubNb_mono _ _ _ (le_max_left i j), hubNb_mono _ _ _ (le_max_right i j)]
  necUnit := ⟨0, _, (Canon.applyG (Γ := ctxOf (gnet hF M₀ 0).src.l) .boxUnit .unit).2, by
    rw [interp_applyG (hubSh hX hh)]; rfl⟩
  posMap := by
    intro A B f p hp
    obtain ⟨i, _, t, rfl⟩ := hp
    exact ⟨i, _, (Canon.applyG (.diaMap f) t).2, by rw [interp_applyG (hubSh hX hh)]; rfl⟩
  posStrength := by
    intro A B n p hn hp
    obtain ⟨i, _, t, rfl⟩ := hn
    obtain ⟨j, _, u, rfl⟩ := hp
    refine ⟨max i j, _, (Canon.applyG (.strength A B)
      (.pair (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_left i j)).suf) t)
        (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_right i j)).suf) u))).2, ?_⟩
    rw [interp_applyG (hubSh hX hh)]
    change (cmodel hF hM₀ hX).ops.posStrength (ConeData.nb (interp (hubE₀ hF hM₀ hX hh _) _))
      (ConeData.pb (interp (hubE₀ hF hM₀ hX hh _) _)) = _
    rw [hubNb_mono _ _ _ (le_max_left i j), hubPb_mono _ _ _ (le_max_right i j)]
  necDup := by
    intro hF' A n hn
    obtain ⟨i, _, t, rfl⟩ := hn
    exact ⟨i, _, (Canon.applyG (.dup hF') t).2, by rw [interp_applyG (hubSh hX hh)]; rfl⟩
  posKeep := by
    intro hF' A p hp
    obtain ⟨i, _, t, rfl⟩ := hp
    exact ⟨i, _, (Canon.applyG (.dkeep hF') t).2, by rw [interp_applyG (hubSh hX hh)]; rfl⟩
  posSide := by
    intro hV A p hp
    obtain ⟨i, _, t, rfl⟩ := hp
    rw [posSide_eq_posKeep (hubSh hX hh) hF hV]
    exact ⟨i, _, (Canon.applyG (.dkeep hF) t).2, by rw [interp_applyG (hubSh hX hh)]; rfl⟩
  posSerial hD := hubDefP_serial hM₀ hX hh hD
  keepLiftN hF' _ hl a o := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).keepLift hF' hl a o
    exact ⟨m, hub_defN_of_lift hM₀ hX hh hl m, hm⟩
  keepLiftP hF' _ hl a o := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).keepLift hF' hl a o
    exact ⟨m, hub_defP_of_lift hM₀ hX hh hl m, hm⟩
  necSide hV h5 _ a n := by
    obtain ⟨m, hm⟩ := (cmodel hF hM₀ hX).necSide_exists hV h5 a n
    exact ⟨m, hub_defN_of_lift hM₀ hX hh (hFS h5) m, fun b => hub_ind hM₀ hX hh _ _ (hm b)⟩

variable (hFS : ModalSys.FiveStrong = true → ModalSys.FourStrong = true)

variable (hF) in
/-- ⭐**The cone over the cluster model with the world asked about at its apex.** -/
noncomputable abbrev hubCone : Model.{0, 0} σ :=
  (hubData hF hM₀ hX hh hFS).cone (hubOn_T hh) (hubOn_B hh) (hubOn_BS hX hh) (hub_ind hM₀ hX hh)

variable (hF) in
/-- ⭐**The apex's environment at a stage**: base addresses their classes, keepable ones the hub's
    reading of their kept address. -/
noncomputable def hubE (i : ℕ) :
    (hubCone hF hM₀ hX hh hFS).Env (ctxOf (gnet hF M₀ i).src.l) none :=
  ConeData.apexEnv _ _ _ _ _ hF (Ctx.Presented.noProjLast _) (hubBase hM₀ hh i)
    (hubV hF hM₀ hX hh i)
    (fun v _ h => ⟨i, _, Term.eta v _ h, by
      rw [interp_eta]
      exact (hubE₀_keyed hM₀ hX hh i).1 v _ h⟩)
    (fun v _ h => ⟨i, _, Term.eta v _ h, by
      rw [interp_eta]
      exact (hubE₀_keyed hM₀ hX hh i).2 v _ h⟩)

theorem hubE_agree {i j : ℕ} (hij : i ≤ j) :
    Env.Agree (ctxOf_le_of_suffix (src_grows hM₀ hh hij).suf) (hubE hF hM₀ hX hh hFS i)
      (hubE hF hM₀ hX hh hFS j) :=
  ConeData.apexEnv_agree (hInd := hub_ind hM₀ hX hh) _ (hubBase_mono hM₀ hh hij)
    fun _ _ h => hubV_mono hM₀ hX hh hij h

theorem hubE_keyed (i : ℕ) :
    ConeData.Keyed hF (hubE hF hM₀ hX hh hFS i) (hubV hF hM₀ hX hh i) :=
  ConeData.apexEnv_keyed (hInd := hub_ind hM₀ hX hh)

/-- A necessary term's object at the apex is the first cone's. -/
theorem hub_nb (i : ℕ) {A : VarType} {a : Ann (.VTypeBox A)}
    (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeBox A) a) :
    ConeData.nb (interp (hubE hF hM₀ hX hh hFS i) t) =
      ConeData.nb (interp (hubE₀ hF hM₀ hX hh i) t) := by
  cases t with
  | boxtm b =>
      rw [ConeData.interp_apex_box (hubE_keyed hM₀ hX hh hFS i) b,
        ConeData.interp_apex_box (hubE₀_keyed hM₀ hX hh i) b]

/-- A possible term's object at the apex is the first cone's. -/
theorem hub_pb (i : ℕ) {A : VarType} {a : Ann (.VTypeDia A)}
    (t : Term σ (ctxOf (gnet hF M₀ i).src.l) (.VTypeDia A) a) :
    ConeData.pb (interp (hubE hF hM₀ hX hh hFS i) t) =
      ConeData.pb (interp (hubE₀ hF hM₀ hX hh i) t) := by
  cases t with
  | diatm x hx c =>
      rw [ConeData.interp_apex_dia (hubE_keyed hM₀ hX hh hFS i) hx c,
        ConeData.interp_apex_dia (hubE₀_keyed hM₀ hX hh i) hx c]

/-! ## Base terms at the apex -/

mutual
  theorem hub_interpFunc (i : ℕ) : ∀ {n : ℕ} (g : Func σ (ctxOf (gnet hF M₀ i).src.l) n)
      (args : Fin n → (gsrcWorld hF M₀ hM₀ hh).D)
      (ts : Fin n → Term σ (ctxOf (gnet hF M₀ i).src.l) .Var .var),
      (∀ k, args k = (gsrcWorld hF M₀ hM₀ hh).cls i (ts k)) →
      interpFunc (hubE hF hM₀ hX hh hFS i) g args =
        (gsrcWorld hF M₀ hM₀ hh).cls i (.func ((Spine.ofFn ts).fill g))
    | _, .F ⟨f, rfl⟩, args, ts, hts => by
        change (gsrcWorld hF M₀ hM₀ hh).canonFunc f (fun k => args (Fin.cast rfl k)) = _
        rw [show (fun k => args (Fin.cast rfl k)) =
            fun k => (gsrcWorld hF M₀ hM₀ hh).cls i (ts k) from funext fun k => hts k,
          BWorld.canonFunc_cls]
    | _, .eval g t, args, ts, hts => by
        change interpFunc (hubE hF hM₀ hX hh hFS i) g
          (Fin.cons (interp (hubE hF hM₀ hX hh hFS i) t) args) = _
        have h0 := hub_interp_var i t
        rw [hub_interpFunc i g (Fin.cons (interp (hubE hF hM₀ hX hh hFS i) t) args) (Fin.cons t ts)
          (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
        rfl
  termination_by _ g => g.size
  decreasing_by
    all_goals simp only [Func.size]
    all_goals omega

  /-- ⭐A base term's value at the apex is its class. -/
  theorem hub_interp_var (i : ℕ) : ∀ t : Term σ (ctxOf (gnet hF M₀ i).src.l) .Var .var,
      interp (hubE hF hM₀ hX hh hFS i) t = (gsrcWorld hF M₀ hM₀ hh).cls i t
    | .var v hv => ConeData.apexEnv_ref (hInd := hub_ind hM₀ hX hh) v hv
    | .func f => hub_interpFunc i f Fin.elim0 Fin.elim0 (fun k => k.elim0)
  termination_by t => t.size
  decreasing_by
    all_goals simp only [Term.size]
    all_goals omega
end

theorem hub_relSat (i : ℕ) : ∀ {n : ℕ} (ρ : Rel σ (ctxOf (gnet hF M₀ i).src.l) n)
    (args : Fin n → (gsrcWorld hF M₀ hM₀ hh).D)
    (ts : Fin n → Term σ (ctxOf (gnet hF M₀ i).src.l) .Var .var),
    (∀ k, args k = (gsrcWorld hF M₀ hM₀ hh).cls i (ts k)) →
    (relSat (hubE hF hM₀ hX hh hFS i) ρ args ↔
      WFF.atom ((Spine.ofFn ts).fillR ρ) ∈ (gsrcWorld hF M₀ hM₀ hh).M i)
  | _, .R ⟨r, rfl⟩, args, ts, hts => by
      change (gsrcWorld hF M₀ hM₀ hh).canonRel r (fun k => args (Fin.cast rfl k)) ↔ _
      rw [show (fun k => args (Fin.cast rfl k)) =
          fun k => (gsrcWorld hF M₀ hM₀ hh).cls i (ts k) from funext fun k => hts k,
        BWorld.canonRel_cls]
  | _, .eval ρ t, args, ts, hts => by
      change relSat (hubE hF hM₀ hX hh hFS i) ρ
        (Fin.cons (interp (hubE hF hM₀ hX hh hFS i) t) args) ↔ _
      have h0 := hub_interp_var hM₀ hX hh hFS i t
      rw [hub_relSat i ρ (Fin.cons (interp (hubE hF hM₀ hX hh hFS i) t) args) (Fin.cons t ts)
        (fun k => by cases k using Fin.cases <;> simp [h0, hts]), Spine.ofFn_cons]
      rfl

/-! ## Every object of the apex is named -/

/-- ⭐**Every object at the apex is the value of a term of the world asked about.** -/
theorem hub_definable : ∀ (A : VarType) (o : (hubCone hF hM₀ hX hh hFS).frame.Dom A none),
    ∃ (i : ℕ) (a : Ann A) (t : Term σ (ctxOf (gnet hF M₀ i).src.l) A a),
      interp (hubE hF hM₀ hX hh hFS i) t = o
  | .Var, o => by
      obtain ⟨⟨i, t⟩, rfl⟩ := Quotient.exists_rep (o : (gsrcWorld hF M₀ hM₀ hh).D)
      exact ⟨i, _, t, hub_interp_var hM₀ hX hh hFS i t⟩
  | .VTypeOne, _ => ⟨0, _, .unit, rfl⟩
  | .VTypeProd A B, o => by
      obtain ⟨i, _, t, ht⟩ := hub_definable A (o : (hubCone hF hM₀ hX hh hFS).frame.Dom A none ×
        (hubCone hF hM₀ hX hh hFS).frame.Dom B none).1
      obtain ⟨j, _, u, hu⟩ := hub_definable B (o : (hubCone hF hM₀ hX hh hFS).frame.Dom A none ×
        (hubCone hF hM₀ hX hh hFS).frame.Dom B none).2
      refine ⟨max i j, _,
        .pair (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_left i j)).suf) t)
          (Term.mono (ctxOf_le_of_suffix (src_grows hM₀ hh (le_max_right i j)).suf) u), ?_⟩
      change (interp _ (Term.mono _ t), interp _ (Term.mono _ u)) = o
      rw [interp_mono (hubE_agree hM₀ hX hh hFS (le_max_left i j)),
        interp_mono (hubE_agree hM₀ hX hh hFS (le_max_right i j)), ht, hu]
      rfl
  | .VTypeBox A, o => by
      obtain ⟨n, i, a, t, rfl⟩ := o
      exact ⟨i, a, t, Subtype.ext (hub_nb hM₀ hX hh hFS i t)⟩
  | .VTypeDia A, o => by
      obtain ⟨p, i, a, t, rfl⟩ := o
      exact ⟨i, a, t, Subtype.ext (hub_pb hM₀ hX hh hFS i t)⟩

/-! ## The truth lemma at the apex -/

/-- ⭐**The truth lemma at the apex, below a size, at every stage.** -/
theorem hubTruth_lt : ∀ (n i : ℕ) (φ : WFF σ (ctxOf (gnet hF M₀ i).src.l) 0), φ.size < n →
    ((hubCone hF hM₀ hX hh hFS).sat (hubE hF hM₀ hX hh hFS i) φ ↔
      φ ∈ (gsrcWorld hF M₀ hM₀ hh).M i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, φ, hφ => by
      cases φ with
      | atom ρ =>
          change relSat (hubE hF hM₀ hX hh hFS i) ρ Fin.elim0 ↔ _
          rw [hub_relSat hM₀ hX hh hFS i ρ Fin.elim0 Fin.elim0 (fun k => k.elim0)]
          rfl
      | eq t u =>
          change interp (hubE hF hM₀ hX hh hFS i) t = interp (hubE hF hM₀ hX hh hFS i) u ↔ _
          rw [hub_interp_var hM₀ hX hh hFS i t, hub_interp_var hM₀ hX hh hFS i u,
            BWorld.cls_eq_iff (le_refl i) (le_refl i)]
          change WFF.eq (Term.mono ((gsrcWorld hF M₀ hM₀ hh).le (le_refl i)) t)
            (Term.mono ((gsrcWorld hF M₀ hM₀ hh).le (le_refl i)) u) ∈
              (gsrcWorld hF M₀ hM₀ hh).M i ↔ _
          rw [Term.mono_refl, Term.mono_refl]
      | top => exact ⟨fun _ => ((gsrcWorld hF M₀ hM₀ hh).mcs i).top_mem, fun _ => trivial⟩
      | bot => exact ⟨False.elim, fun h => ((gsrcWorld hF M₀ hM₀ hh).mcs i).bot_not_mem h⟩
      | here hT _ _ => exact flagElim (hubOn_T hh) hT
      | back hB _ _ _ => exact flagElim (hubOn_BS hX hh) hB
      | retS hB _ _ _ => exact flagElim (hubOn_BS hX hh) hB
      | retxS hB _ _ _ _ _ => exact flagElim (hubOn_BS hX hh) hB
      | link _ hN _ _ => exact flagElim hN hF
      | linkx _ hN _ _ _ _ => exact flagElim hN hF
      | and φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∧ _ ↔ _
          rw [hubTruth_lt n i φ h₁, hubTruth_lt n i ψ h₂,
            ((gsrcWorld hF M₀ hM₀ hh).mcs i).and_mem_iff]
      | or φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change _ ∨ _ ↔ _
          rw [hubTruth_lt n i φ h₁, hubTruth_lt n i ψ h₂,
            ((gsrcWorld hF M₀ hM₀ hh).mcs i).or_mem_iff]
      | imp φ ψ =>
          have h₁ : φ.size < n := by simp only [WFF.size] at hφ; omega
          have h₂ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (_ → _) ↔ _
          rw [hubTruth_lt n i φ h₁, hubTruth_lt n i ψ h₂,
            ((gsrcWorld hF M₀ hM₀ hh).mcs i).imp_mem_iff]
      | all A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∀ o : (hubCone hF hM₀ hX hh hFS).frame.Dom A none,
            (hubCone hF hM₀ hX hh hFS).sat ((hubE hF hM₀ hX hh hFS i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · intro hsat
            by_contra hnot
            obtain ⟨i', hi, a, t, hmem⟩ := (gsrcWorld hF M₀ hM₀ hh).allW
              (((gsrcWorld hF M₀ hM₀ hh).mcs i).neg_mem_iff.mpr hnot)
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (hubE_agree hM₀ hX hh hFS hi)
              (.bnd 0) (interp (hubE hF hM₀ hX hh hFS i') t)) ψ).mpr (hsat _)
            have hs₂ := (Model.sat_instantiate (hubE hF hM₀ hX hh hFS i')
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots t _).mpr hs₁
            have hs₃ := (hubTruth_lt n i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (((gsrcWorld hF M₀ hM₀ hh).mcs i').neg_mem_iff.mp hmem) hs₃
          · intro hmem o
            obtain ⟨i', a, t', ht'⟩ := hub_definable hM₀ hX hh hFS A o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hinst : WFF.instantiate Ctx.NoSlots.slots ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t')
                (WFF.mono (((gsrcWorld hF M₀ hM₀ hh).le hK).insert (.bnd 0) A) ψ) ∈
                (gsrcWorld hF M₀ hM₀ hh).M (i ⊔ i') :=
              BWorld.mem_of_provable
                (Δ := [WFF.all A (WFF.mono (((gsrcWorld hF M₀ hM₀ hh).le hK).insert (.bnd 0) A) ψ)])
                (fun χ hχ => by
                  rw [List.mem_singleton.mp hχ]
                  exact (BWorld.mem_lift hK).mp hmem)
                ⟨Proof.all_elim A ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t')
                  (Proof.lookup List.mem_cons_self)⟩
            have hs := (hubTruth_lt n (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hinst
            have hs₁ := (Model.sat_instantiate (hubE hF hM₀ hX hh hFS (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots
              ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t') _).mp hs
            rw [show interp (hubE hF hM₀ hX hh hFS (i ⊔ i'))
                ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t') = o from
              (interp_mono (hubE_agree hM₀ hX hh hFS hK') t').trans ht'] at hs₁
            exact (Model.sat_mono (Model.Env.extend_agree (hubE_agree hM₀ hX hh hFS hK) (.bnd 0) o)
              ψ).mp hs₁
      | ex A ψ =>
          have hψ : ψ.size < n := by simp only [WFF.size] at hφ; omega
          change (∃ o : (hubCone hF hM₀ hX hh hFS).frame.Dom A none,
            (hubCone hF hM₀ hX hh hFS).sat ((hubE hF hM₀ hX hh hFS i).extend (.bnd 0) o) ψ) ↔ _
          constructor
          · rintro ⟨o, hsat⟩
            obtain ⟨i', a, t', ht'⟩ := hub_definable hM₀ hX hh hFS A o
            have hK : i ≤ i ⊔ i' := le_sup_left
            have hK' : i' ≤ i ⊔ i' := le_sup_right
            have hs₁ := (Model.sat_mono (Model.Env.extend_agree (hubE_agree hM₀ hX hh hFS hK)
              (.bnd 0) o) ψ).mpr hsat
            rw [← show interp (hubE hF hM₀ hX hh hFS (i ⊔ i'))
                ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t') = o from
              (interp_mono (hubE_agree hM₀ hX hh hFS hK') t').trans ht'] at hs₁
            have hs₂ := (Model.sat_instantiate (hubE hF hM₀ hX hh hFS (i ⊔ i'))
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots
              ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t') _).mpr hs₁
            have hmemK := (hubTruth_lt n (i ⊔ i') _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mp hs₂
            exact (BWorld.mem_lift hK).mpr (BWorld.mem_of_provable
              (Δ := [WFF.instantiate Ctx.NoSlots.slots ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t')
                (WFF.mono (((gsrcWorld hF M₀ hM₀ hh).le hK).insert (.bnd 0) A) ψ)])
              (fun χ hχ => by
                rw [List.mem_singleton.mp hχ]
                exact hmemK)
              ⟨Proof.ex_intro A ((gsrcWorld hF M₀ hM₀ hh).liftT hK' t')
                (Proof.lookup List.mem_cons_self)⟩)
          · intro hmem
            obtain ⟨i', hi, a, t, hmem'⟩ := (gsrcWorld hF M₀ hM₀ hh).exW_term hmem
            refine ⟨interp (hubE hF hM₀ hX hh hFS i') t, ?_⟩
            have hs := (hubTruth_lt n i' _
              (by rw [WFF.size_instantiate, WFF.size_mono]; exact hψ)).mpr hmem'
            have hs₁ := (Model.sat_instantiate (hubE hF hM₀ hX hh hFS i')
              (Ctx.Presented.noProjLast _) Ctx.NoSlots.slots t _).mp hs
            exact (Model.sat_mono (Model.Env.extend_agree (hubE_agree hM₀ hX hh hFS hi) (.bnd 0) _)
              ψ).mp hs₁
      | box χ => exact apex_box_iff (hubE_keyed hM₀ hX hh hFS i) (hubV_sat hM₀ hX hh i) χ
      | dia x hx χ => exact apex_dia_iff (hubE_keyed hM₀ hX hh hFS i) (hubV_sat hM₀ hX hh i) hx χ

/-- ⭐⭐**The truth lemma at the apex**: the world asked about satisfies, at each stage, exactly its
    theory there. -/
theorem hubTruth (i : ℕ) (φ : WFF σ (ctxOf (gnet hF M₀ i).src.l) 0) :
    (hubCone hF hM₀ hX hh hFS).sat (hubE hF hM₀ hX hh hFS i) φ ↔
      φ ∈ (gsrcWorld hF M₀ hM₀ hh).M i :=
  hubTruth_lt hM₀ hX hh hFS (φ.size + 1) i φ (Nat.lt_succ_self _)

/-- ⭐⭐**The cone over a maximal consistent theory with the hub on**: its apex satisfies, at its
    first stage, exactly that theory. -/
theorem exists_canonHub (φ : WFF σ (ctxOf l₀) 0) :
    (hubCone hF hM₀ hX hh hFS).sat (hubE hF hM₀ hX hh hFS 0) φ ↔ φ ∈ M₀ :=
  hubTruth hM₀ hX hh hFS 0 φ

end GArrow

end V12M
