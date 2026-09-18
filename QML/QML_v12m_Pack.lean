import QML.QML_v12m_SubstId

/-!
# QML v12m — packing several roots into one parameter (strong T)

The rule `T_dia` gives its subproof, for each `□`-view formula with a hole, the hypothesis that
*for every value of one parameter* `y : B` what holds of `t` here holds of the witness content in
`◇_c` (`WFF.retHyp`).  One parameter serves all hypotheses, and its docstring says how several are
meant to be handled: they **pack into a product type**.

The canonical model needs exactly that.  A witness `c` is declared at one own stage of the Henkin
chain, with hypotheses whose hole formulas live in the context of that stage; but `RealDatum.spec`
must serve formulas of *every later* stage, which mention the constants declared after `c`.  Those
constants are packed into the parameter: the hole formula is taken with each of them replaced by a
component of `y`, and the hypothesis is then instantiated at the tuple of the constants themselves.

* `VarType.pack`: the right-nested product of a list of types, `[]` giving the unit;
* `VarSymb.comp`: the address of a component; `VarSymb.rebase`: replacing the root of an address;
* `Ctx.ref_comp`: a packed root's components are the listed types;
* `Term.tuple`: the tuple of the packed roots;
* `Subst.pack`: the renaming sending each packed root to its component of `y`;
* ⭐`Subst.sim_pack_single`: instantiating `y` at the tuple undoes the renaming.
-/

namespace V12M

variable [ModalSys]

/-! ## Packed types and their components -/

/-- The right-nested product of a list of types; the empty list gives the unit. -/
def VarType.pack : List VarType → VarType
  | [] => .VTypeOne
  | A :: l => .VTypeProd A (VarType.pack l)

namespace VarSymb

/-- The address of the `k`-th component of a packed address. -/
def comp (u : VarSymb) : ℕ → VarSymb
  | 0 => .step u .fst
  | k + 1 => comp (.step u .snd) k

/-- Replacing the root of an address by another address: `v.rebase u`. -/
def rebase : VarSymb → VarSymb → VarSymb
  | .root _, u => u
  | .step v s, u => .step (rebase v u) s

omit [ModalSys] in
theorem rebase_ext : ∀ (v : VarSymb) (p : List Step) (u : VarSymb),
    rebase (v.ext p) u = (rebase v u).ext p
  | _, [], _ => rfl
  | v, s :: p, u => rebase_ext (.step v s) p u

end VarSymb

namespace Ctx

/-- The components of a packed root are the types of the list, in order. -/
theorem ref_comp : ∀ (k : ℕ) (l : List VarType) {Γ : Ctx} {u : VarSymb} {T : VarType},
    Γ.ref u = some (VarType.pack l) → l[k]? = some T → Γ.ref (u.comp k) = some T
  | 0, A :: _, _, _, _, hu, hl => by
      have hA : A = _ := Option.some.inj hl
      subst hA
      exact Ctx.ref_fst_of hu
  | k + 1, _ :: l, _, _, _, hu, hl => ref_comp k l (Ctx.ref_snd_of hu) hl
  | 0, [], _, _, _, _, hl => by cases hl
  | _ + 1, [], _, _, _, _, hl => by cases hl

end Ctx

/-! ## The packed tuple -/

/-- The annotation of the tuple of η-expansions. -/
def Ann.packEta : (zs : List (VarType × ℕ)) → Ann (VarType.pack (zs.map Prod.fst))
  | [] => .one
  | z :: zs => .prod (Ann.eta (.root (.free z.2)) z.1) (Ann.packEta zs)

/-- The tuple of the packed roots, η-expanded. -/
def Term.tuple {σ : Signature} {Γ : Ctx} : (zs : List (VarType × ℕ)) →
    (∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) →
    Term σ Γ (VarType.pack (zs.map Prod.fst)) (Ann.packEta zs)
  | [], _ => .unit
  | z :: zs, h =>
      .pair (Term.eta (.root (.free z.2)) z.1 (h z List.mem_cons_self))
        (Term.tuple zs fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))

/-! ## The packing renaming -/

namespace Subst

variable {σ : Signature}

/-- The component index of a name among those packed. -/
def packOf : List (VarType × ℕ) → ℕ → Option ℕ
  | [], _ => none
  | z :: zs, n => if n = z.2 then some 0 else (packOf zs n).map (· + 1)

omit [ModalSys] in
/-- A packed name is the name of its component. -/
theorem packOf_spec : ∀ (zs : List (VarType × ℕ)) {n k : ℕ}, packOf zs n = some k →
    ∃ z, zs[k]? = some z ∧ z.2 = n
  | z :: zs, n, k, h => by
      by_cases hn : n = z.2
      · rw [show packOf (z :: zs) n = some 0 from if_pos hn] at h
        cases h
        exact ⟨z, rfl, hn.symm⟩
      · rw [show packOf (z :: zs) n = (packOf zs n).map (· + 1) from if_neg hn] at h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨z', hz', he⟩ := packOf_spec zs hk'
        exact ⟨z', hz', he⟩
  | [], _, _, h => by cases h

/-- The component index of a root among those packed. -/
def rootPack (zs : List (VarType × ℕ)) : Root → Option ℕ
  | .free n => packOf zs n
  | .bnd _ => none

/-- The address map of the packing: an address rooted at a packed name is rebased onto that
    component of `y`. -/
def packIdx (y : ℕ) (zs : List (VarType × ℕ)) (v : VarSymb) : VarSymb :=
  match rootPack zs v.rt with
  | some k => v.rebase ((VarSymb.root (.free y)).comp k)
  | none => v

/-- ⭐The packing: each packed root goes to its component of the parameter `y`. -/
def pack (σ : Signature) (Δ : Ctx) (y : ℕ) (zs : List (VarType × ℕ)) : Subst σ Δ :=
  fun v => .ren (packIdx y zs v)

omit [ModalSys] in
theorem packIdx_ext (y : ℕ) (zs : List (VarType × ℕ)) (v : VarSymb) (p : List Step) :
    packIdx y zs (v.ext p) = (packIdx y zs v).ext p := by
  unfold packIdx
  rw [VarSymb.ext_rt]
  cases hk : rootPack zs v.rt with
  | none => rfl
  | some k =>
      change (v.ext p).rebase ((VarSymb.root (.free y)).comp k) =
        ((v.rebase ((VarSymb.root (.free y)).comp k)).ext p)
      exact VarSymb.rebase_ext v p _

omit [ModalSys] in
/-- An address rooted at a packed name is rebased. -/
theorem packIdx_packed {y n k : ℕ} {zs : List (VarType × ℕ)} {v : VarSymb} (hrt : v.rt = .free n)
    (hk : packOf zs n = some k) :
    packIdx y zs v = v.rebase ((VarSymb.root (.free y)).comp k) := by
  unfold packIdx
  rw [show rootPack zs v.rt = some k by rw [hrt]; exact hk]

omit [ModalSys] in
/-- An address rooted elsewhere is untouched. -/
theorem packIdx_other {y : ℕ} {zs : List (VarType × ℕ)} {v : VarSymb}
    (h : ∀ n, v.rt = .free n → packOf zs n = none) : packIdx y zs v = v := by
  unfold packIdx
  rw [show rootPack zs v.rt = none by
    cases hrt : v.rt with
    | bnd _ => rfl
    | free n => exact h n hrt]

variable {Γ : Ctx} {y : ℕ} {zs : List (VarType × ℕ)}

/-- The type of the parameter that packs `zs`. -/
abbrev packType (zs : List (VarType × ℕ)) : VarType := VarType.pack (zs.map Prod.fst)

/-- A packed name is declared at the type of its component. -/
theorem type_of_packed (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) {n k : ℕ}
    (hk : packOf zs n = some k) {T : VarType} (hv : Γ.ref (.root (.free n)) = some T) :
    (zs.map Prod.fst)[k]? = some T := by
  obtain ⟨z, hz', rfl⟩ := packOf_spec zs hk
  have := hz z (List.mem_of_getElem? hz')
  rw [this] at hv
  rw [List.getElem?_map, hz']
  exact congrArg some (Option.some.inj hv)

/-- The packing lands in the context with the parameter declared. -/
theorem ok_pack (hy : Γ.RootFresh (.free y))
    (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → packOf zs n ≠ none →
      v ≠ .root (.free n) → Γ v = none) :
    Ok Γ (pack σ (Γ.insert (.free y) (packType zs)) y zs) := by
  intro v T hlp hv
  cases hrt : v.rt with
  | bnd _ =>
      have he : packIdx y zs v = v := packIdx_other (fun n hn => by rw [hrt] at hn; cases hn)
      change (Γ.insert (.free y) (packType zs)).ref (packIdx y zs v) = some T
      rw [he]
      exact (Ctx.ref_nonproj _ hlp).trans (Ctx.le_insert hy.root (packType zs) v T hv)
  | free n =>
      cases hk : packOf zs n with
      | none =>
          have he : packIdx y zs v = v := packIdx_other (fun n' hn' => by
            rw [hrt] at hn'
            cases hn'
            exact hk)
          change (Γ.insert (.free y) (packType zs)).ref (packIdx y zs v) = some T
          rw [he]
          exact (Ctx.ref_nonproj _ hlp).trans (Ctx.le_insert hy.root (packType zs) v T hv)
      | some k =>
          have hvr : v = .root (.free n) := by
            by_contra hne
            rw [honly v n hrt (by rw [hk]; exact fun h => by cases h) hne] at hv
            cases hv
          subst hvr
          change (Γ.insert (.free y) (packType zs)).ref (packIdx y zs (.root (.free n))) = some T
          rw [packIdx_packed (y := y) rfl hk]
          exact Ctx.ref_comp k (zs.map Prod.fst)
            (Ctx.ref_insert_root Γ (.free y) (packType zs))
            (type_of_packed hz hk hv)

theorem coh_pack (hy : Γ.RootFresh (.free y))
    (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → packOf zs n ≠ none →
      v ≠ .root (.free n) → Γ v = none) :
    Coh (packIdx y zs) Γ (pack σ (Γ.insert (.free y) (packType zs)) y zs) :=
  coh_of (ok_pack hy hz honly) (fun v _ _ _ p => (packIdx_ext y zs v p).symm)

/-! ## Instantiating the parameter at the tuple -/

/-- Reading a component of an entry that is the packed tuple. -/
theorem at_tuple_comp {Δ : Ctx} (θ : Subst σ Δ) :
    ∀ (k : ℕ) (zs : List (VarType × ℕ)) (u : VarSymb)
      (hz : ∀ z ∈ zs, Δ.ref (.root (.free z.2)) = some z.1),
      θ.at u = .tm (Term.tuple zs hz) → ∀ z, zs[k]? = some z →
      ∀ h : Δ.ref (.root (.free z.2)) = some z.1,
      θ.at (u.comp k) = .tm (Term.eta (.root (.free z.2)) z.1 h)
  | 0, z' :: zs, u, hz, hu, z, hzk, h => by
      have : θ.at (.step u .fst) = (θ.at u).proj .fst := by
        change (if Step.fst.isProj then (θ.at u).proj .fst else _) = _
        rw [if_pos (show Step.fst.isProj = true from rfl)]
      have hz' : z' = z := Option.some.inj hzk
      subst hz'
      rw [show u.comp 0 = .step u .fst from rfl, this, hu]
      rfl
  | k + 1, _ :: zs, u, hz, hu, z, hzk, h => by
      refine at_tuple_comp θ k zs (.step u .snd) (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz'))
        ?_ z hzk h
      have : θ.at (.step u .snd) = (θ.at u).proj .snd := by
        change (if Step.snd.isProj then (θ.at u).proj .snd else _) = _
        rw [if_pos (show Step.snd.isProj = true from rfl)]
      rw [this, hu]
      rfl
  | 0, [], _, _, _, _, hzk, _ => by cases hzk
  | _ + 1, [], _, _, _, _, hzk, _ => by cases hzk

/-- Away from the parameter, substituting for it changes nothing. -/
theorem at_single_of_rt_ne {Δ : Ctx} {r : Root} {e : SubE σ Δ} :
    ∀ {v : VarSymb}, v.rt ≠ r → (single r e).at v = .ren v
  | .root r', h => by
      change (if (VarSymb.root r') = .root r then e else SubE.ren (.root r')) = _
      exact if_neg (fun he => h (VarSymb.root.inj he))
  | .step v s, h => by
      change (if s.isProj then ((single r e).at v).proj s else single r e (.step v s)) = _
      by_cases hs : s.isProj = true
      · rw [if_pos hs, at_single_of_rt_ne (v := v) h]
        rfl
      · rw [if_neg hs]
        change (if (VarSymb.step v s) = .root r then e else SubE.ren (.step v s)) = _
        exact if_neg (fun he => by cases he)

/-- Substituting the tuple of the packed roots for the parameter. -/
def tupleS (y : ℕ) (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) : Subst σ Γ :=
  single (.free y) (.tm (Term.tuple zs hz))

theorem ok_tupleS (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) :
    Ok (Γ.insert (.free y) (packType zs)) (tupleS (σ := σ) y hz) :=
  ok_single (T := packType zs) (e := SubE.tm (Term.tuple zs hz)) (Ctx.Le.refl Γ) rfl

theorem coh_tupleS (hy : Γ.RootFresh (.free y))
    (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) :
    Coh (singleIdx (σ := σ) (.free y) (.tm (Term.tuple zs hz))) (Γ.insert (.free y) (packType zs))
      (tupleS (σ := σ) y hz) :=
  coh_single (T := packType zs) (e := SubE.tm (Term.tuple zs hz)) hy (Ctx.Le.refl Γ) rfl

theorem at_single_root {Δ : Ctx} (r : Root) (e : SubE σ Δ) : (single r e).at (.root r) = e := by
  change (if (VarSymb.root r) = .root r then e else SubE.ren (.root r)) = _
  exact if_pos rfl

theorem at_tupleS_of_rt_ne (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1) {v : VarSymb}
    (h : v.rt ≠ .free y) : (tupleS (σ := σ) y hz).at v = .ren v := at_single_of_rt_ne h

/-- ⭐The round trip: instantiating the parameter at the tuple of the packed roots undoes the
    packing. -/
theorem sim_pack_single (hy : Γ.RootFresh (.free y))
    (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → packOf zs n ≠ none →
      v ≠ .root (.free n) → Γ v = none) :
    Sim Γ (idS σ Γ)
      ((pack σ (Γ.insert (.free y) (packType zs)) y zs).comp
        (tupleS y hz) (ok_tupleS hz) (coh_tupleS hy hz)) := by
  refine sim_of ?_
  intro v T _ hv
  have hvy : v.rt ≠ .free y := fun he => by rw [hy v he] at hv; cases hv
  change SubE.Sim T (.ren v)
    ((SubE.ren (packIdx y zs v)).comp _ (ok_tupleS hz)
      (coh_tupleS hy hz))
  change SubE.Sim T (.ren v) ((tupleS y hz).at (packIdx y zs v))
  cases hrt : v.rt with
  | bnd _ =>
      rw [packIdx_other (fun n hn => by rw [hrt] at hn; cases hn),
        at_tupleS_of_rt_ne hz hvy]
      exact .refl _
  | free n =>
      cases hk : packOf zs n with
      | none =>
          rw [packIdx_other (fun n' hn' => by rw [hrt] at hn'; cases hn'; exact hk),
            at_tupleS_of_rt_ne hz hvy]
          exact .refl _
      | some k =>
          have hvr : v = .root (.free n) := by
            by_contra hne
            rw [honly v n hrt (by rw [hk]; exact fun h => by cases h) hne] at hv
            cases hv
          subst hvr
          obtain ⟨z, hzk, hzn⟩ := packOf_spec zs hk
          have hT : z.1 = T := by
            have h1 := hz z (List.mem_of_getElem? hzk)
            rw [hzn] at h1
            have h2 : Γ.ref (.root (.free n)) = some T := hv
            rw [h1] at h2
            exact Option.some.inj h2
          have hu : (tupleS (σ := σ) (Γ := Γ) y hz).at (.root (.free y)) =
              .tm (Term.tuple zs hz) := by
            change (if (VarSymb.root (.free y)) = .root (.free y) then _ else _) = _
            rw [if_pos rfl]
          rw [packIdx_packed (y := y) rfl hk,
            show (VarSymb.root (Root.free n)).rebase ((VarSymb.root (Root.free y)).comp k) =
              (VarSymb.root (Root.free y)).comp k from rfl,
            at_tuple_comp _ k zs (.root (.free y)) hz hu z hzk
              (hz z (List.mem_of_getElem? hzk))]
          subst hT
          rw [← hzn]
          exact .ren_eta _ _

end Subst

/-- ⭐The packing round trip one view in and under the hole — the form a `T_dia` hypothesis needs,
    since its hole formula lives in the `□` view with a slot for the object. -/
theorem WFF.subst_pack_single_view {σ : Signature} {Γ : Ctx} {y : ℕ} {zs : List (VarType × ℕ)}
    (hy : Γ.RootFresh (.free y)) (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → Subst.packOf zs n ≠ none →
      v ≠ .root (.free n) → Γ v = none)
    (hΓ : Γ.SlotsFrom 0) (hΔ : (Γ.insert (.free y) (Subst.packType zs)).SlotsFrom 0)
    (A : VarType) (φ : WFF σ (Γ.boxIn.insert (.bnd 0) A) 1) :
    WFF.subst (VarSymb.shiftSlot (Subst.singleIdx (.free y) (.tm (Term.tuple zs hz))) 0 0)
        ((Subst.tupleS y hz).box.under 0 0 A hΓ.boxIn.root)
        (Subst.ok_under (Subst.ok_box (Subst.ok_tupleS hz)) A hΓ.boxIn.root)
        (Subst.coh_under (Subst.ok_box (Subst.ok_tupleS hz))
          (Subst.coh_box (Subst.ok_tupleS hz) (Subst.coh_tupleS hy hz)) hΔ.boxIn A hΓ.boxIn.root)
        (hΔ.boxIn.insert A) (hΓ.boxIn.insert A)
      (WFF.subst (VarSymb.shiftSlot (Subst.packIdx y zs) 0 0)
        ((Subst.pack σ (Γ.insert (.free y) (Subst.packType zs)) y zs).box.under 0 0 A
          hΔ.boxIn.root)
        (Subst.ok_under (Subst.ok_box (Subst.ok_pack hy hz honly)) A hΔ.boxIn.root)
        (Subst.coh_under (Subst.ok_box (Subst.ok_pack hy hz honly))
          (Subst.coh_box (Subst.ok_pack hy hz honly) (Subst.coh_pack hy hz honly)) hΓ.boxIn A
          hΔ.boxIn.root)
        (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) φ) = φ := by
  refine (WFF.subst_comp _ _ ((Subst.idS σ Γ).box.under 0 0 A hΓ.boxIn.root) _ _ _ _
    (Subst.ok_under (Subst.ok_box Subst.ok_idS) A hΓ.boxIn.root)
    (Subst.coh_under (Subst.ok_box Subst.ok_idS)
      (Subst.coh_box Subst.ok_idS Subst.coh_idS) hΓ.boxIn A hΓ.boxIn.root)
    (hΓ.boxIn.insert A) (hΔ.boxIn.insert A) (hΓ.boxIn.insert A)
    (Subst.sim_under_comp (Subst.ok_box (Subst.ok_pack hy hz honly))
      (Subst.ok_box (Subst.ok_tupleS hz))
      (Subst.coh_box (Subst.ok_tupleS hz) (Subst.coh_tupleS hy hz))
      (Subst.sim_box_comp (Subst.ok_pack hy hz honly) (Subst.ok_tupleS hz)
        (Subst.coh_tupleS hy hz) (Subst.sim_pack_single hy hz honly))
      hΔ.boxIn A hΔ.boxIn.root hΓ.boxIn.root) φ).trans ?_
  refine (WFF.subst_congr _ ((Subst.idS σ Γ.boxIn).under 0 0 A hΓ.boxIn.root) _
    (Subst.ok_under Subst.ok_idS A hΓ.boxIn.root)
    _ (Subst.coh_under Subst.ok_idS Subst.coh_idS hΓ.boxIn A hΓ.boxIn.root)
    (hΓ.boxIn.insert A) (hΓ.boxIn.insert A)
    (Subst.sim_under Subst.sim_box_idS A hΓ.boxIn.root) φ).trans ?_
  refine (WFF.subst_congr _ (Subst.idS σ (Γ.boxIn.insert (.bnd 0) A)) _ Subst.ok_idS _
    Subst.coh_idS (hΓ.boxIn.insert A) (hΓ.boxIn.insert A)
    (Subst.sim_under_idS 0 A hΓ.boxIn.root) φ).trans ?_
  exact WFF.subst_id Subst.ok_idS Subst.coh_idS (hΓ.boxIn.insert A) φ

/-- ⭐Binding a free root, weakening to a larger context, and instantiating the bound slot at a
    term there is just substituting that term for the root.  This is how a `∀`-quantified
    hypothesis of an earlier stage is used at a later one: the parameter's name is gone once it is
    bound, so the later stage may well declare it, and the instance may be taken at a term the
    earlier stage could not write. -/
theorem WFF.instantiate_mono_bindFree {σ : Signature} {Γ Δ : Ctx} {T : VarType} {a : Ann T}
    (hle : Γ.Le Δ) (u : ℕ) (hu : Γ.RootFresh (.free u)) (hΓ : Γ.SlotsFrom 0) (hΔ : Δ.SlotsFrom 0)
    (s : Term σ Δ T a) (φ : WFF σ (Γ.insert (.free u) T) 0) :
    WFF.instantiate hΔ s (WFF.mono (hle.insert (.bnd 0) T) (WFF.bindFree u hu hΓ T φ)) =
      WFF.subst (Subst.singleIdx (.free u) (.tm s)) (Subst.single (.free u) (.tm s))
        (Subst.ok_single hle rfl) (Subst.coh_single hu hle rfl) (hΓ.insertFree u T) hΔ φ := by
  refine (WFF.subst_mono (hle.insert (.bnd 0) T) (Subst.single (.bnd 0) (.tm s))
    (Subst.ok_single (Ctx.Le.refl Δ) rfl)
    (Subst.coh_single (hΔ.rootFresh le_rfl) (Ctx.Le.refl Δ) rfl) (hΓ.insert T) (hΔ.insert T) hΔ
    (WFF.bindFree u hu hΓ T φ)).trans ?_
  refine WFF.subst_comp _ _ _ _ _ _ _ _ _ _ _ _ ?_ φ
  refine Subst.sim_of ?_
  intro v U _ hv
  by_cases hvu : v = .root (.free u)
  · subst hvu
    change SubE.Sim U (Subst.single (.free u) (SubE.tm s) (.root (.free u)))
      ((Subst.single (.free u) (SubE.ren (.root (.bnd 0))) (.root (.free u))).comp _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Δ) (.free u) (SubE.tm s) (.root (.free u)) = .tm s from
        if_pos rfl,
      show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (SubE.ren (.root (.bnd 0)))
          (.root (.free u)) = .ren (.root (.bnd 0)) from if_pos rfl]
    change SubE.Sim U (.tm s) ((Subst.single (.bnd 0) (SubE.tm s)).at (.root (.bnd 0)))
    rw [Subst.at_single_root (Δ := Δ) (.bnd 0) (SubE.tm s)]
    exact .refl _
  · have hv2 : Γ v = some U := by simpa [Ctx.insert, hvu] using hv
    have hvb : v.rt ≠ .bnd 0 := fun he => by
      rw [hΓ.rootFresh (le_refl 0) v he] at hv2
      cases hv2
    change SubE.Sim U (Subst.single (.free u) (SubE.tm s) v)
      ((Subst.single (.free u) (SubE.ren (.root (.bnd 0))) v).comp _ _ _)
    rw [show Subst.single (σ := σ) (Δ := Δ) (.free u) (SubE.tm s) v = .ren v from if_neg hvu,
      show Subst.single (σ := σ) (Δ := Γ.insert (.bnd 0) T) (.free u) (SubE.ren (.root (.bnd 0)))
        v = .ren v from if_neg hvu]
    change SubE.Sim U (.ren v) ((Subst.single (.bnd 0) (SubE.tm s)).at v)
    rw [Subst.at_single_of_rt_ne hvb]
    exact .refl _

/-- ⭐Packing the listed roots into a fresh parameter and then instantiating that parameter at the
    tuple of the roots themselves leaves a formula unchanged.  This is how a hypothesis of `T_dia`,
    whose hole formula may only mention the context of the stage where the witness was declared,
    serves a formula of a later stage. -/
theorem WFF.subst_pack_single {σ : Signature} {Γ : Ctx} {y : ℕ} {zs : List (VarType × ℕ)} {d : ℕ}
    (hy : Γ.RootFresh (.free y)) (hz : ∀ z ∈ zs, Γ.ref (.root (.free z.2)) = some z.1)
    (honly : ∀ (v : VarSymb) (n : ℕ), v.rt = .free n → Subst.packOf zs n ≠ none →
      v ≠ .root (.free n) → Γ v = none)
    (hΓ : Γ.SlotsFrom d) (hΔ : (Γ.insert (.free y) (Subst.packType zs)).SlotsFrom d)
    (φ : WFF σ Γ d) :
    WFF.subst (Subst.singleIdx (.free y) (.tm (Term.tuple zs hz))) (Subst.tupleS y hz)
        (Subst.ok_tupleS hz) (Subst.coh_tupleS hy hz) hΔ hΓ
      (WFF.subst (Subst.packIdx y zs) (Subst.pack σ (Γ.insert (.free y) (Subst.packType zs)) y zs)
        (Subst.ok_pack hy hz honly) (Subst.coh_pack hy hz honly) hΓ hΔ φ) = φ :=
  (WFF.subst_comp _ _ (Subst.idS σ Γ) (Subst.ok_pack hy hz honly) (Subst.coh_pack hy hz honly)
    (Subst.ok_tupleS hz) (Subst.coh_tupleS hy hz) Subst.ok_idS Subst.coh_idS hΓ hΔ hΓ
    (Subst.sim_pack_single hy hz honly) φ).trans (WFF.subst_id Subst.ok_idS Subst.coh_idS hΓ φ)

end V12M
