import QML.QML_v12m_BRetOpsC

/-!
# QML v12m — strong B on the network: naming the route (rows 3–4)

Under rows 3–4 (`BStrongW`) every edge is doubly witnessed (docs §11.23), so a returning
possibility along `□` gets its child along a witness: first the node names the route, a fresh
root `κ : ◇𝟙` with `◇_κ[d ↦ y] Φ` (paper check 3), consistent by `Proof.ret_route` as a Henkin
witness is by `ex_elim`.

* `routeFormula`, ⭐`route_consistent`, `routeStep`, `routeStep_ok`;
* the operation `NetSt.mkRoute`, ⭐`GoodS.mkRoute`, `Ext.mkRoute`.
-/

namespace V12M

variable [ModalSys]

namespace BArrow

variable {σ : Signature} [ModalSys.NoFour]

section Route

variable {l : List VarType} (hS : ModalSys.BStrong = true) {S : RShape} {a : Ann S.flat}

/-- The route's formula over `◇𝟙 :: l`: `◇_κ[d ↦ y] Φ` along the fresh root `κ = |l|`, the body
    read in `κ`'s view. -/
def routeFormula (y : Term σ (ctxOf l) S.flat a)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) S.ty) 1) :
    WFF σ (ctxOf (.VTypeDia .VTypeOne :: l)) 0 :=
  WFF.retxS hS (.root (.free l.length))
    ⟨.VTypeOne, Ctx.ref_insert_root (ctxOf l) (.free l.length) _⟩ S
    (Term.weaken (ctxOf_fresh (l := l) le_rfl).root _ y)
    (WFF.mono (((Ctx.le_insert (ctxOf_fresh (l := l) le_rfl).root _).boxIn.trans
      (Ctx.le_boxIn_diaIn _ (.root (.free l.length)))).insert (.bnd 0) S.ty) Φ)

omit [ModalSys.NoFour] in
/-- ⭐**Naming the route is consistent**: a refutation of the theory with the route formula is,
    by `Proof.ret_route`, one of the theory's returning possibility. -/
theorem route_consistent (hW : ModalSys.BStrongW = true) {M : Set (WFF σ (ctxOf l) 0)}
    (hM : Theory.Consistent M) (y : Term σ (ctxOf l) S.flat a)
    (Φ : WFF σ ((ctxOf l).boxIn.insert (.bnd 0) S.ty) 1)
    (hr : Theory.Derives M (WFF.retS hS S y Φ)) :
    Theory.Consistent (WFF.mono (ctxOf_le_append [.VTypeDia .VTypeOne] l) '' M ∪
      {routeFormula hS y Φ}) := by
  have hu : (ctxOf l).RootFresh (.free l.length) := ctxOf_fresh le_rfl
  rintro ⟨Δ, hΔ, p⟩
  obtain ⟨Δ₀, h₀, h₁⟩ := exists_hyps_cons_map (P := fun x => x ∈ M)
    (fun x => WFF.mono (ctxOf_le_append [.VTypeDia .VTypeOne] l) x) (routeFormula hS y Φ) Δ
    (fun δ hδ => by
      rcases hΔ δ hδ with ⟨x, hx, rfl⟩ | h
      · exact Or.inr ⟨x, hx, rfl⟩
      · exact Or.inl (Set.mem_singleton_iff.mp h))
  obtain ⟨q⟩ := Provable.mono h₁ p
  obtain ⟨Δ₁, hΔ₁, ⟨pr⟩⟩ := hr
  refine hM ⟨Δ₁ ++ Δ₀, fun x hx => (List.mem_append.mp hx).elim (hΔ₁ x) (h₀ x), ⟨?_⟩⟩
  refine Proof.ret_route hS hW y Φ l.length hu (Δ := Δ₁ ++ Δ₀) (φ := .bot)
    (Proof.ofSubset (fun x hx => List.mem_append_left _ hx) pr)
    (Proof.ofSubset (fun x hx => ?_) q)
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons_self
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_right _ hz))

/-- The node grown by naming the route of `◇[d ↦ y] Φ`. -/
noncomputable def routeStep (t : NodeSt σ) (y : Term σ (ctxOf t.l) S.flat a)
    (Φ : WFF σ ((ctxOf t.l).boxIn.insert (.bnd 0) S.ty) 1) : NodeSt σ :=
  ⟨.VTypeDia .VTypeOne :: t.l, complete
    (WFF.mono (ctxOf_le_append [.VTypeDia .VTypeOne] t.l) '' t.M ∪ {routeFormula hS y Φ})⟩

omit [ModalSys.NoFour] in
/-- ⭐The node with its route named is maximal consistent, extends the old one, and holds the
    route formula. -/
theorem routeStep_ok (hW : ModalSys.BStrongW = true) {t : NodeSt σ} (ht : Theory.IsMCS t.M)
    (y : Term σ (ctxOf t.l) S.flat a) (Φ : WFF σ ((ctxOf t.l).boxIn.insert (.bnd 0) S.ty) 1)
    (hr : WFF.retS hS S y Φ ∈ t.M) :
    Theory.IsMCS (routeStep hS t y Φ).M ∧ Grows t (routeStep hS t y Φ) ∧
      routeFormula hS y Φ ∈ (routeStep hS t y Φ).M := by
  obtain ⟨hsub, hmcs⟩ :=
    complete_spec (route_consistent hS hW ht.1 y Φ (Theory.Derives.of_mem hr))
  exact ⟨hmcs, ⟨⟨[_], rfl⟩, fun φ hφ => hsub (Or.inl ⟨φ, hφ, rfl⟩)⟩, hsub (Or.inr rfl)⟩

end Route

namespace NetSt

/-- A route obligation: a returning possibility along `□` over a list of a node's variables. -/
abbrev RouteObl (σ : Signature) :=
  Σ l : List VarType, Σ S : RShape, Σ a : Ann S.flat,
    Term σ (ctxOf l) S.flat a × WFF σ ((ctxOf l).boxIn.insert (.bnd 0) S.ty) 1

open Classical in
/-- ⭐Name the route of the node `s`'s returning possibility `◇[d ↦ y] Φ`, if it has it — over
    an earlier list of its variables. -/
noncomputable def mkRoute (hS : ModalSys.BStrong = true) (N : NetSt σ) (s : Node) :
    RouteObl σ → NetSt σ
  | ⟨l, S, _, y, Φ⟩ =>
      if h : l <:+ (N.st s).l then
        if WFF.retS hS S (Term.mono (ctxOf_le_of_suffix h) y)
            (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) S.ty) Φ) ∈ (N.st s).M then
          N.setSt s (routeStep hS (N.st s) (Term.mono (ctxOf_le_of_suffix h) y)
            (WFF.mono ((ctxOf_le_of_suffix h).boxIn.insert (.bnd 0) S.ty) Φ))
        else N
      else N

/-- ⭐Naming a route keeps strong B's invariants: the node only grows. -/
theorem GoodS.mkRoute {hS : ModalSys.BStrong = true} (hW : ModalSys.BStrongW = true)
    {N : NetSt σ} (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : RouteObl σ) :
    (N.mkRoute hS s o).GoodS hS := by
  obtain ⟨l, S, a, y, Φ⟩ := o
  simp only [NetSt.mkRoute]
  split_ifs with h hr
  · obtain ⟨h₁, h₂, -⟩ := routeStep_ok hS hW (hN.mcs s hs) _ _ hr
    exact hN.setSt hs h₂ h₁
  all_goals exact hN

theorem Ext.mkRoute {hS : ModalSys.BStrong = true} (hW : ModalSys.BStrongW = true)
    {N : NetSt σ} (hN : N.GoodS hS) {s : Node} (hs : N.Live s) (o : RouteObl σ) :
    Ext N (N.mkRoute hS s o) := by
  obtain ⟨l, S, a, y, Φ⟩ := o
  simp only [NetSt.mkRoute]
  split_ifs with h hr
  · exact Ext.setSt (routeStep_ok hS hW (hN.mcs s hs) _ _ hr).2.1
  all_goals exact Ext.refl N

end NetSt

end BArrow

end V12M
